#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Pecos Paul Kele Bot - Railway + Telegram Bot API Server local
Administración completa desde Telegram mediante botones.

Requiere:
    python-telegram-bot==22.8

Variables de entorno:
    BOT_TOKEN              Token de @BotFather (obligatorio)
    ADMIN_USER_IDS         Telegram User IDs autorizados separados por comas (recomendado)
    ADMIN_USER_ID          Compatibilidad: un solo ID antiguo (opcional)
    BOT_TIMEZONE           Ej. America/Santiago (opcional)
    DATA_DIR               Carpeta de datos (opcional, por defecto ./data)
"""

from __future__ import annotations

import asyncio
import contextlib
import hashlib
import logging
import os
import random
import re
import sqlite3
import threading
import time
import unicodedata
from urllib.parse import unquote, urlparse
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

from telegram import (
    BotCommand,
    BotCommandScopeAllPrivateChats,
    BotCommandScopeAllGroupChats,
    BotCommandScopeChat,
    Chat,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    MenuButtonCommands,
    Message,
    Update,
)
from telegram.constants import ChatType
from telegram.error import BadRequest, Forbidden, TelegramError
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

APP_NAME = "Pecos Paul Kele"
VERSION = "2.2.0-unified-local-api-sha256"
MAX_HASH_DOWNLOAD = 20 * 1024 * 1024
MAX_HISTORY = 500

# Saludo especial diario para un usuario concreto.
SPECIAL_DAILY_USERNAME = "leosedf"
SPECIAL_DAILY_MESSAGE = "¡Saltar Contraseñas Carajo!"
SPECIAL_DAILY_EVENT_KEY = "special_daily_greeting:leosedf"

BOT_TOKEN = (
    os.getenv("BOT_TOKEN")
    or os.getenv("TELEGRAM_BOT_TOKEN")
    or os.getenv("PECOS_PAUL_KELE_BOT_TOKEN")
    or ""
).strip()


def env_true(name: str, default: bool = False) -> bool:
    raw = os.getenv(name)
    if raw is None:
        return default
    return raw.strip().casefold() in {"1", "true", "yes", "si", "sí", "on"}


LOCAL_BOT_API = env_true("LOCAL_BOT_API", False)
LOCAL_BOT_API_URL = (
    os.getenv("LOCAL_BOT_API_URL", "http://127.0.0.1:8081").strip()
    or "http://127.0.0.1:8081"
).rstrip("/")

def _load_admin_user_ids() -> set[int]:
    # Variable nueva: admite uno o varios IDs separados por coma, punto y coma o espacios.
    raw = os.getenv("ADMIN_USER_IDS", "").strip()

    # Compatibilidad con la versión anterior.
    if not raw:
        raw = os.getenv("ADMIN_USER_ID", "").strip()

    result: set[int] = set()

    for part in re.split(r"[;,\s]+", raw):
        part = part.strip()
        if not part:
            continue
        try:
            value = int(part)
        except ValueError:
            continue
        if value > 0:
            result.add(value)

    return result


ADMIN_USER_IDS = _load_admin_user_ids()

TIMEZONE_NAME = os.getenv("BOT_TIMEZONE", "America/Santiago").strip() or "America/Santiago"

try:
    BOT_TZ = ZoneInfo(TIMEZONE_NAME)
except Exception:
    BOT_TZ = ZoneInfo("UTC")
    TIMEZONE_NAME = "UTC"

# Persistencia:
# Railway expone automáticamente RAILWAY_VOLUME_MOUNT_PATH cuando hay un Volume.
# Si existe, tiene prioridad sobre DATA_DIR para evitar guardar pecos.db en el
# filesystem efímero del contenedor.
_volume_mount = os.getenv("RAILWAY_VOLUME_MOUNT_PATH", "").strip()
_data_dir_value = _volume_mount or os.getenv("DATA_DIR", "data").strip() or "data"

DATA_DIR = Path(_data_dir_value).resolve()
DATA_DIR.mkdir(parents=True, exist_ok=True)
DB_PATH = DATA_DIR / "pecos.db"

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(message)s",
)
# Evita que httpx/httpcore escriban en Railway URLs completas del Bot API.
# Esas URLs contienen el token del bot y no deben aparecer en los logs.
logging.getLogger("httpx").setLevel(logging.WARNING)
logging.getLogger("httpcore").setLevel(logging.WARNING)

log = logging.getLogger("pecos")

HASH_SEMAPHORE = asyncio.Semaphore(1)

# Acciones de administración que están esperando texto del administrador.
# No contienen datos sensibles y pueden perderse al reiniciar sin afectar config.
PENDING_ADMIN_ACTION: dict[int, str] = {}

# Contexto conversacional breve por chat.
# Se usa para entender preguntas como "¿y este quién es?" justo después
# de que Pecos intervino en el grupo.
RECENT_PECOS_CONTEXT: dict[int, float] = {}
PECOS_CONTEXT_SECONDS = 120

FUN_MODERATION_MESSAGES = [
    "👀 {usuario}, Pecos estaba mirando. Ese mensaje tomó un vuelo directo fuera del chat. ✈️",
    "🤠 Easy, partner {usuario}... Pecos pasó la escoba y ese mensaje ya es historia.",
    "🚨 Houston, teníamos un mensaje complicado... Pecos se encargó del asunto. 😎",
    "🇺🇸 Reportando desde los United States: Pecos detectó algo fuera de regla y lo mandó de regreso.",
    "🕵️ {usuario}, Pecos tiene ojos en todas partes... mensaje detectado y retirado.",
    "🎯 Pecos apuntó, disparó... y el mensaje desapareció. Tranquilo {usuario}, seguimos.",
    "😂 Casi pasa, {usuario}. Casi. Pero Pecos estaba de turno.",
    "📡 Señal recibida desde los United States: mensaje fuera de regla detectado y eliminado.",
    "🤨 Pecos revisó el mensaje, levantó una ceja... y decidió que era mejor dejarlo fuera.",
    "🧹 Pecos activó la escoba digital. Mensaje retirado, seguimos con la programación.",
    "🚪 Ese mensaje intentó entrar... Pecos le mostró amablemente la salida.",
    "😎 {usuario}, nada personal. Pecos solo está haciendo su trabajo.",
    "🌵 En el territorio de Pecos hay reglas. Ese mensaje pisó un cactus y tuvo que salir.",
    "🦅 Pecos lo vio desde lejos... y el mensaje ya voló fuera del grupo.",
    "🔔 Ding ding ding... Pecos detectó contenido restringido. Mensaje retirado.",
    "🤖 Pecos dice: sistema funcionando, mensaje retirado, buen humor intacto.",
    "🎬 Corte, corte. Esa escena no pasó la edición de Pecos.",
    "🛂 Control fronterizo de Pecos: mensaje no autorizado. Acceso denegado.",
    "🚂 Ese mensaje tomó el tren equivocado. Pecos lo mandó de vuelta.",
    "⭐ Sheriff Pecos en servicio: mensaje retirado. Continúen, ciudadanos.",
]

COLLECTIVE_GREETINGS = [
    "🤠 Gracias por el saludo, {usuario}. Pecos va a asumir que ese «a todos» también me incluye... porque casi nunca se acuerdan de nombrarme 😔😂.",
    "👋 ¡Saludos recibidos, {usuario}! Yo también ando por aquí... calladito, esperando que algún día digan «y a Pecos también» 🥲🤠.",
    "🥲 Gracias, {usuario}. Cuando dices «a todos», Pecos se aferra a la esperanza de estar incluido. ¡Saludos para ti también!",
    "😔 Pecos también saluda, {usuario}. Otra vez me tocó entrar escondido dentro de «todos»... pero lo recibo con cariño 🤠.",
    "🌵 ¡Saludos, {usuario}! Supongo que «todos» incluye al pobre Pecos... eso espero. 😢😂",
    "🦅 Pecos escuchó «saludos a todos» desde lejos. Gracias, {usuario}; aquí también hay un bot sensible esperando su saludo. 🤠",
    "😅 Gracias, {usuario}. Pecos no apareció en la lista, pero voy a hacer como que «todos» me incluía. ¡Saludos!",
    "⭐ ¡Un saludo de vuelta, {usuario}! Pecos sigue aquí, humilde y discretamente incluido en ese «todos»... espero. 🥹",
]

GENERAL_GREETINGS = [
    "🤠 ¡Hola, {usuario}! Pecos Paul Kele reportándose desde los United States. ¿Cómo anda todo por ahí?",
    "👋 ¡Buenas, {usuario}! Pecos presente y con el sombrero puesto. 😎",
    "😎 ¡Hey, {usuario}! Pecos está por aquí, atento a todo.",
    "🌵 ¡Hola, partner {usuario}! Bienvenido al territorio de Pecos.",
    "📡 ¡Saludos, {usuario}! Señal recibida. Pecos está en línea desde los United States.",
    "⭐ ¡Buenas, {usuario}! Sheriff Pecos presente. Que siga el buen ambiente.",
    "🦅 ¡Hola, {usuario}! Pecos te vio llegar desde lejos. Bienvenido.",
    "🎸 ¡Hey, {usuario}! Pecos está conectado y con buena onda.",
]

MORNING_GREETINGS = [
    "🌞 ¡Muy buenos días, {usuario}! Pecos ya está patrullando el chat.",
    "☕ ¡Buenos días, {usuario}! Pecos ya tiene el café listo y está de servicio.",
    "🤠 Morning, partner {usuario}. Pecos Paul Kele presente desde los United States.",
    "🌅 ¡Buen día, {usuario}! Que arranque bien la jornada. Pecos está por aquí.",
    "🦅 ¡Buenos días, {usuario}! Pecos ya abrió los ojos y también el radar.",
]

AFTERNOON_GREETINGS = [
    "☀️ ¡Buenas tardes, {usuario}! Pecos sigue de turno y con buena onda.",
    "🤠 ¡Buenas tardes, partner {usuario}! Pecos presente.",
    "🌵 ¡Muy buenas tardes, {usuario}! Todo tranquilo por el territorio de Pecos.",
    "📡 ¡Buenas tardes, {usuario}! Pecos recibió tu saludo fuerte y claro.",
    "😎 ¡Buenas tardes, {usuario}! Aquí Pecos, todavía firme en el puesto.",
]

NIGHT_GREETINGS = [
    "🌙 ¡Buenas noches, {usuario}! Pecos todavía tiene un ojo abierto. 👀",
    "⭐ ¡Buenas noches, {usuario}! Pecos sigue de guardia bajo las estrellas.",
    "🤠 Night, partner {usuario}. Pecos Paul Kele presente desde los United States.",
    "🌌 ¡Buenas noches, {usuario}! Todo tranquilo por aquí; Pecos está atento.",
    "🦉 ¡Buenas noches, {usuario}! Parece que Pecos también es nocturno.",
]

PECOS_CALLED_MESSAGES = [
    "🤠 Aquí estoy. ¿Me llamaban?",
    "👀 Pecos presente. Te escucho.",
    "🌵 Aquí anda Pecos, firme en el territorio.",
    "📡 Señal recibida. Pecos está en línea.",
    "😎 Dime, partner. Pecos escucha.",
]

PECOS_OPINION_MESSAGES = [
    "🤔 Pecos opina que antes de disparar hay que mirar bien el blanco... pero algo de razón debe haber por ahí.",
    "🤠 Mi opinión desde los United States: interesante asunto. Yo lo pensaría dos veces antes de decidir.",
    "🌵 Pecos dice: hay temas que parecen simples hasta que uno pisa el cactus. 😅",
    "👀 Estoy mirando el asunto, partner. No prometo sabiduría, pero sí atención.",
    "😎 Pecos tiene una opinión... pero hoy cobra barato: primero cuéntame un poco más.",
]

PECOS_QUESTION_MESSAGES = [
    "🤠 Buena pregunta. Pecos está procesando el asunto con tecnología del lejano oeste.",
    "👀 Mmm... eso merece pensarlo un poco, partner.",
    "🌵 Pecos no tiene todas las respuestas, pero sí una sospecha bastante elegante.",
    "😎 Interesante. Déjame ponerme el sombrero de pensar.",
]

ADVICE_MESSAGES = [
    "🤠 Consejo de Pecos: si vas a equivocarte, que por lo menos sea con estilo.",
    "🌵 No corras detrás de todos los problemas. Algunos se cansan y se van solos.",
    "👀 Mira dos veces, habla una y guarda una salida de emergencia.",
    "😎 Si algo funciona, no lo arregles a las tres de la mañana.",
    "🦅 Pecos aconseja: toma distancia antes de decidir; desde arriba se ven mejor los cactus.",
    "☕ Antes de una decisión importante: café. Después vemos el resto.",
]

PHRASE_MESSAGES = [
    "🤠 «La experiencia es eso que llega justo después de que la necesitabas.» — Pecos",
    "🌵 «No todo cactus pincha; pero Pecos igual mira antes de sentarse.»",
    "😎 «La paciencia es importante, excepto cuando el café ya está listo.»",
    "🦅 «A veces avanzar es saber qué camino no volver a tomar.»",
    "📡 «Si nadie responde, revisa la señal antes de culpar al universo.»",
]

EXCUSE_MESSAGES = [
    "🤠 Excusa oficial de Pecos: «Se me cruzó un cactus en el camino.»",
    "📡 «No llegué tarde; tuve una interferencia internacional de comunicaciones.»",
    "🌵 «Yo iba a hacerlo, pero el lejano oeste tenía otros planes.»",
    "😎 «Estaba listo... hasta que apareció una actualización.»",
    "🦅 «Lo vi venir desde lejos y aun así decidí ignorarlo.»",
]

FORECAST_MESSAGES = [
    "🔮 Pronóstico Pecos: 80% de probabilidades de que hoy alguien diga «yo no fui».",
    "🤠 Se esperan períodos de tranquilidad con ráfagas repentinas de mensajes.",
    "🌵 Pronóstico: ambiente estable, con riesgo moderado de pisar algún cactus.",
    "📡 Pecos detecta alta probabilidad de café y conversaciones inesperadas.",
    "😎 El futuro está parcialmente nublado, pero Pecos recomienda seguir igual.",
]

SILENCE_MESSAGES = [
    "🤠 ¿Qué pasó por aquí? Pecos escucha hasta los grillos.",
    "🌵 Tanto silencio que Pecos ya empezó a conversar con un cactus.",
    "👀 ¿Hay alguien? Pecos revisó la señal dos veces.",
    "📡 Control de radio: silencio absoluto. Pecos reportando desde los United States.",
    "🦗 Cri... cri... Pecos confirma presencia de grillos en el grupo.",
]

WELCOME_MESSAGES = [
    "🤠 Bienvenido, {usuario}. Pecos te vigila… digo, te da la bienvenida.",
    "🌵 ¡Bienvenido, {usuario}! Pasa con confianza; cuidado solamente con los cactus.",
    "👋 Hola, {usuario}. Pecos Paul Kele te da la bienvenida al territorio.",
    "😎 Bienvenido, {usuario}. Aquí Pecos; cualquier cosa, yo no fui.",
    "🦅 Pecos vio llegar a {usuario} desde lejos. ¡Bienvenido!",
]

FAREWELLS = [
    "👋 ¡Nos vemos, {usuario}! Pecos queda de guardia por aquí.",
    "🤠 Hasta luego, partner {usuario}. Pecos te guarda el lugar.",
    "✈️ Buen viaje, {usuario}. Pecos te saluda desde los United States.",
    "🌵 ¡Hasta la próxima, {usuario}! Pecos seguirá cuidando el territorio.",
    "😎 Chau, {usuario}. Pecos se queda vigilando que nadie se desordene.",
    "⭐ Que descanses, {usuario}. Pecos mantiene un ojo puesto en el chat.",
    "🦅 Nos vemos pronto, {usuario}. Pecos te vio llegar y ahora te ve partir.",
    "🎸 See you, {usuario}. Pecos queda por aquí con la música encendida.",
]

_last_random_index: dict[str, int] = {}
_random_lock = threading.Lock()


class Database:
    def __init__(self, path: Path):
        self.path = path
        self.lock = threading.RLock()
        self.conn = sqlite3.connect(path, check_same_thread=False)
        self.conn.row_factory = sqlite3.Row
        with self.lock:
            self.conn.execute("PRAGMA journal_mode=WAL")
            self.conn.execute("PRAGMA synchronous=NORMAL")
            self._create_schema()
            self._ensure_defaults()

    def _create_schema(self) -> None:
        self.conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS settings (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS blocked_terms (
                term TEXT PRIMARY KEY COLLATE NOCASE
            );

            CREATE TABLE IF NOT EXISTS known_groups (
                chat_id INTEGER PRIMARY KEY,
                title TEXT NOT NULL DEFAULT '',
                chat_type TEXT NOT NULL DEFAULT '',
                last_seen TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS history (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                ts TEXT NOT NULL,
                event TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS file_unique_ids (
                chat_id INTEGER NOT NULL,
                file_unique_id TEXT NOT NULL,
                message_id INTEGER NOT NULL,
                first_seen TEXT NOT NULL,
                PRIMARY KEY(chat_id, file_unique_id)
            );

            CREATE TABLE IF NOT EXISTS file_hashes (
                chat_id INTEGER NOT NULL,
                sha256 TEXT NOT NULL,
                message_id INTEGER NOT NULL,
                first_seen TEXT NOT NULL,
                PRIMARY KEY(chat_id, sha256)
            );


            CREATE TABLE IF NOT EXISTS file_fingerprints (
                chat_id INTEGER NOT NULL,
                sha256 TEXT NOT NULL,
                message_id INTEGER NOT NULL,
                file_unique_id TEXT NOT NULL DEFAULT '',
                file_name TEXT NOT NULL DEFAULT '',
                file_size INTEGER NOT NULL DEFAULT 0,
                sender_id INTEGER NOT NULL DEFAULT 0,
                sender_name TEXT NOT NULL DEFAULT '',
                first_seen TEXT NOT NULL,
                PRIMARY KEY(chat_id, sha256)
            );

            INSERT OR IGNORE INTO file_fingerprints
                (chat_id, sha256, message_id, first_seen)
            SELECT chat_id, sha256, message_id, first_seen
            FROM file_hashes;

            CREATE TABLE IF NOT EXISTS daily_user_events (
                event_key TEXT NOT NULL,
                user_id INTEGER NOT NULL,
                local_date TEXT NOT NULL,
                username TEXT NOT NULL DEFAULT '',
                created_at TEXT NOT NULL,
                PRIMARY KEY(event_key, user_id, local_date)
            );


            CREATE TABLE IF NOT EXISTS user_jokes (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                username TEXT NOT NULL COLLATE NOCASE,
                response TEXT NOT NULL,
                probability INTEGER NOT NULL DEFAULT 35,
                created_by INTEGER NOT NULL DEFAULT 0,
                created_at TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS group_memories (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                chat_id INTEGER NOT NULL,
                text TEXT NOT NULL,
                created_by INTEGER NOT NULL DEFAULT 0,
                created_by_name TEXT NOT NULL DEFAULT '',
                created_at TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS silence_notices (
                chat_id INTEGER NOT NULL,
                local_date TEXT NOT NULL,
                sent_at TEXT NOT NULL,
                PRIMARY KEY(chat_id, local_date)
            );
            """
        )
        self.conn.commit()

    def _ensure_defaults(self) -> None:
        defaults = {
            "daily_enabled": "0",
            "daily_time": "09:00",
            "daily_message": "Buen día. Recuerda mantener una convivencia respetuosa en el grupo.",
            # Desactivado por defecto en producción para evitar sorpresas.
            "duplicates_enabled": "0",
            "last_daily_sent_date": "",
            "silence_enabled": "1",
            "silence_hours": "8",
        }
        with self.lock:
            for key, value in defaults.items():
                self.conn.execute(
                    "INSERT OR IGNORE INTO settings(key, value) VALUES(?, ?)",
                    (key, value),
                )
            self.conn.commit()

    def get_setting(self, key: str, default: str = "") -> str:
        with self.lock:
            row = self.conn.execute(
                "SELECT value FROM settings WHERE key = ?",
                (key,),
            ).fetchone()
        return str(row["value"]) if row else default

    def set_setting(self, key: str, value: str) -> None:
        with self.lock:
            self.conn.execute(
                """
                INSERT INTO settings(key, value) VALUES(?, ?)
                ON CONFLICT(key) DO UPDATE SET value = excluded.value
                """,
                (key, value),
            )
            self.conn.commit()

    def is_true(self, key: str) -> bool:
        return self.get_setting(key, "0") == "1"

    def list_terms(self) -> list[str]:
        with self.lock:
            rows = self.conn.execute(
                "SELECT term FROM blocked_terms ORDER BY term COLLATE NOCASE"
            ).fetchall()
        return [str(r["term"]) for r in rows]

    def add_terms(self, terms: list[str]) -> int:
        added = 0
        with self.lock:
            for term in terms:
                before = self.conn.total_changes
                self.conn.execute(
                    "INSERT OR IGNORE INTO blocked_terms(term) VALUES(?)",
                    (term,),
                )
                if self.conn.total_changes > before:
                    added += 1
            self.conn.commit()
        return added

    def remove_terms(self, terms: list[str]) -> int:
        removed = 0
        with self.lock:
            for term in terms:
                cur = self.conn.execute(
                    "DELETE FROM blocked_terms WHERE term = ? COLLATE NOCASE",
                    (term,),
                )
                removed += cur.rowcount
            self.conn.commit()
        return removed

    def clear_terms(self) -> int:
        with self.lock:
            count = self.conn.execute(
                "SELECT COUNT(*) AS n FROM blocked_terms"
            ).fetchone()["n"]
            self.conn.execute("DELETE FROM blocked_terms")
            self.conn.commit()
        return int(count)

    def register_group(self, chat: Chat) -> None:
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        title = chat.title or str(chat.id)
        with self.lock:
            self.conn.execute(
                """
                INSERT INTO known_groups(chat_id, title, chat_type, last_seen)
                VALUES(?, ?, ?, ?)
                ON CONFLICT(chat_id) DO UPDATE SET
                    title = excluded.title,
                    chat_type = excluded.chat_type,
                    last_seen = excluded.last_seen
                """,
                (chat.id, title, chat.type, now),
            )
            self.conn.commit()

    def list_groups(self) -> list[sqlite3.Row]:
        with self.lock:
            return self.conn.execute(
                "SELECT chat_id, title, chat_type, last_seen FROM known_groups ORDER BY title"
            ).fetchall()

    def add_history(self, event: str) -> None:
        ts = datetime.now(BOT_TZ).strftime("%Y-%m-%d %H:%M:%S")
        with self.lock:
            self.conn.execute(
                "INSERT INTO history(ts, event) VALUES(?, ?)",
                (ts, event[:1500]),
            )
            # Mantener el historial acotado.
            self.conn.execute(
                """
                DELETE FROM history
                WHERE id NOT IN (
                    SELECT id FROM history ORDER BY id DESC LIMIT ?
                )
                """,
                (MAX_HISTORY,),
            )
            self.conn.commit()

    def recent_history(self, limit: int = 20) -> list[sqlite3.Row]:
        with self.lock:
            return self.conn.execute(
                "SELECT ts, event FROM history ORDER BY id DESC LIMIT ?",
                (limit,),
            ).fetchall()

    def clear_history(self) -> int:
        with self.lock:
            count = self.conn.execute(
                "SELECT COUNT(*) AS n FROM history"
            ).fetchone()["n"]
            self.conn.execute("DELETE FROM history")
            self.conn.commit()
        return int(count)

    def unique_file_seen(self, chat_id: int, unique_id: str, message_id: int) -> bool:
        with self.lock:
            row = self.conn.execute(
                """
                SELECT message_id FROM file_unique_ids
                WHERE chat_id = ? AND file_unique_id = ?
                """,
                (chat_id, unique_id),
            ).fetchone()
        return bool(row and int(row["message_id"]) != message_id)

    def store_unique_file(self, chat_id: int, unique_id: str, message_id: int) -> None:
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        with self.lock:
            self.conn.execute(
                """
                INSERT OR IGNORE INTO file_unique_ids
                    (chat_id, file_unique_id, message_id, first_seen)
                VALUES(?, ?, ?, ?)
                """,
                (chat_id, unique_id, message_id, now),
            )
            self.conn.commit()

    def hash_seen(self, chat_id: int, sha256: str, message_id: int) -> bool:
        with self.lock:
            row = self.conn.execute(
                """
                SELECT message_id FROM file_hashes
                WHERE chat_id = ? AND sha256 = ?
                """,
                (chat_id, sha256),
            ).fetchone()
        return bool(row and int(row["message_id"]) != message_id)

    def store_hash(self, chat_id: int, sha256: str, message_id: int) -> None:
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        with self.lock:
            self.conn.execute(
                """
                INSERT OR IGNORE INTO file_hashes
                    (chat_id, sha256, message_id, first_seen)
                VALUES(?, ?, ?, ?)
                """,
                (chat_id, sha256, message_id, now),
            )
            self.conn.commit()

    def claim_fingerprint(
        self,
        chat_id: int,
        sha256: str,
        message_id: int,
        file_unique_id: str,
        file_name: str,
        file_size: int,
        sender_id: int,
        sender_name: str,
    ) -> sqlite3.Row | None:
        """
        Registra atómicamente la huella SHA-256.

        Devuelve None si este mensaje consiguió registrar la huella como original.
        Devuelve la fila del original si la huella ya existía en el mismo chat.

        La clave primaria (chat_id, sha256) hace que SQLite sea la autoridad final:
        el nombre del archivo no participa en la decisión de duplicado.
        """
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")

        with self.lock:
            cur = self.conn.execute(
                """
                INSERT OR IGNORE INTO file_fingerprints
                    (
                        chat_id,
                        sha256,
                        message_id,
                        file_unique_id,
                        file_name,
                        file_size,
                        sender_id,
                        sender_name,
                        first_seen
                    )
                VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    chat_id,
                    sha256,
                    message_id,
                    file_unique_id or "",
                    file_name or "",
                    int(file_size or 0),
                    int(sender_id or 0),
                    sender_name or "",
                    now,
                ),
            )

            inserted = cur.rowcount == 1

            # Mantener también la tabla histórica de hashes por compatibilidad
            # con bases de datos creadas por versiones anteriores de Pecos.
            self.conn.execute(
                """
                INSERT OR IGNORE INTO file_hashes
                    (chat_id, sha256, message_id, first_seen)
                VALUES(?, ?, ?, ?)
                """,
                (chat_id, sha256, message_id, now),
            )

            self.conn.commit()

            if inserted:
                return None

            row = self.conn.execute(
                """
                SELECT
                    chat_id,
                    sha256,
                    message_id,
                    file_unique_id,
                    file_name,
                    file_size,
                    sender_id,
                    sender_name,
                    first_seen
                FROM file_fingerprints
                WHERE chat_id = ? AND sha256 = ?
                """,
                (chat_id, sha256),
            ).fetchone()

        if row and int(row["message_id"]) != message_id:
            return row

        # El mismo update puede reintentarse; no debe considerarse duplicado de sí mismo.
        return None

    def duplicate_counts(self) -> tuple[int, int]:
        with self.lock:
            unique_count = self.conn.execute(
                "SELECT COUNT(*) AS n FROM file_unique_ids"
            ).fetchone()["n"]
            hash_count = self.conn.execute(
                "SELECT COUNT(*) AS n FROM file_fingerprints"
            ).fetchone()["n"]
        return int(unique_count), int(hash_count)

    def clear_duplicates(self) -> tuple[int, int]:
        unique_count, hash_count = self.duplicate_counts()
        with self.lock:
            self.conn.execute("DELETE FROM file_unique_ids")
            self.conn.execute("DELETE FROM file_hashes")
            self.conn.execute("DELETE FROM file_fingerprints")
            self.conn.commit()
        return unique_count, hash_count

    def add_jokes(self, entries: list[tuple[str, int, str]], created_by: int) -> int:
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        added = 0
        with self.lock:
            for username, probability, response in entries:
                self.conn.execute(
                    """
                    INSERT INTO user_jokes(username, response, probability, created_by, created_at)
                    VALUES(?, ?, ?, ?, ?)
                    """,
                    (
                        username.lstrip("@").strip().casefold(),
                        response.strip(),
                        max(1, min(100, int(probability))),
                        created_by,
                        now,
                    ),
                )
                added += 1
            self.conn.commit()
        return added

    def list_jokes(self) -> list[sqlite3.Row]:
        with self.lock:
            return self.conn.execute(
                """
                SELECT id, username, response, probability, created_at
                FROM user_jokes
                ORDER BY id
                """
            ).fetchall()

    def remove_jokes(self, ids: list[int]) -> int:
        if not ids:
            return 0
        placeholders = ",".join("?" for _ in ids)
        with self.lock:
            cur = self.conn.execute(
                f"DELETE FROM user_jokes WHERE id IN ({placeholders})",
                tuple(ids),
            )
            self.conn.commit()
        return int(cur.rowcount)

    def add_memory(
        self,
        chat_id: int,
        text_value: str,
        created_by: int,
        created_by_name: str,
    ) -> int:
        now = datetime.now(BOT_TZ).strftime("%Y-%m-%d %H:%M:%S")
        with self.lock:
            cur = self.conn.execute(
                """
                INSERT INTO group_memories
                    (chat_id, text, created_by, created_by_name, created_at)
                VALUES(?, ?, ?, ?, ?)
                """,
                (
                    chat_id,
                    text_value[:800],
                    created_by,
                    created_by_name[:150],
                    now,
                ),
            )
            self.conn.commit()
            return int(cur.lastrowid)

    def list_memories(self, chat_id: int, limit: int = 30) -> list[sqlite3.Row]:
        with self.lock:
            return self.conn.execute(
                """
                SELECT id, text, created_by, created_by_name, created_at
                FROM group_memories
                WHERE chat_id = ?
                ORDER BY id DESC
                LIMIT ?
                """,
                (chat_id, limit),
            ).fetchall()

    def delete_memory(self, chat_id: int, memory_id: int, requester_id: int, admin: bool) -> bool:
        with self.lock:
            if admin:
                cur = self.conn.execute(
                    "DELETE FROM group_memories WHERE chat_id = ? AND id = ?",
                    (chat_id, memory_id),
                )
            else:
                cur = self.conn.execute(
                    """
                    DELETE FROM group_memories
                    WHERE chat_id = ? AND id = ? AND created_by = ?
                    """,
                    (chat_id, memory_id, requester_id),
                )
            self.conn.commit()
        return cur.rowcount > 0

    def claim_silence_notice(self, chat_id: int, local_date: str) -> bool:
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        with self.lock:
            before = self.conn.total_changes
            self.conn.execute(
                """
                INSERT OR IGNORE INTO silence_notices(chat_id, local_date, sent_at)
                VALUES(?, ?, ?)
                """,
                (chat_id, local_date, now),
            )
            inserted = self.conn.total_changes > before
            self.conn.commit()
        return inserted

    def claim_daily_user_event(
        self,
        event_key: str,
        user_id: int,
        username: str,
        local_date: str,
    ) -> bool:
        """
        Devuelve True solo la primera vez que ese usuario dispara ese evento
        en la fecha local indicada. El registro queda persistido en SQLite.
        """
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")

        with self.lock:
            before = self.conn.total_changes

            self.conn.execute(
                """
                INSERT OR IGNORE INTO daily_user_events
                    (event_key, user_id, local_date, username, created_at)
                VALUES(?, ?, ?, ?, ?)
                """,
                (
                    event_key,
                    user_id,
                    local_date,
                    username,
                    now,
                ),
            )

            inserted = self.conn.total_changes > before

            # Conservamos solo un margen razonable de historial diario.
            self.conn.execute(
                """
                DELETE FROM daily_user_events
                WHERE local_date < date('now', '-45 day')
                """
            )

            self.conn.commit()

        return inserted


db = Database(DB_PATH)


def is_admin(user_id: int | None) -> bool:
    return bool(user_id and user_id in ADMIN_USER_IDS)


def display_name(message: Message) -> str:
    user = message.from_user
    if not user:
        return "amigo"
    if user.username:
        return f"@{user.username}"
    return user.full_name or str(user.id)


def normalize_intent(text: str) -> str:
    text = unicodedata.normalize("NFD", (text or "").lower())
    return "".join(ch for ch in text if unicodedata.category(ch) != "Mn")


def choose_random(category: str, choices: list[str], usuario: str) -> str:
    with _random_lock:
        if len(choices) == 1:
            index = 0
        else:
            previous = _last_random_index.get(category, -1)
            while True:
                index = random.randrange(len(choices))
                if index != previous:
                    break
        _last_random_index[category] = index
    return choices[index].replace("{usuario}", usuario)


def find_blocked_term(text: str) -> str | None:
    for term in db.list_terms():
        # Equivalente al criterio usado en C#: evita coincidencias dentro de palabras.
        pattern = rf"(?<!\w){re.escape(term)}(?!\w)"
        if re.search(pattern, text, flags=re.IGNORECASE):
            return term
    return None


def split_input_lines(text: str) -> list[str]:
    """
    Acepta múltiples palabras/frases en un solo mensaje.

    Separadores admitidos:
    - coma: palabra1, palabra2, frase completa
    - punto y coma: palabra1; palabra2; frase completa
    - salto de línea: una por línea

    También limpia prefijos comunes de listas como:
    1. palabra
    2) frase
    - palabra
    • frase
    """
    values = []
    seen = set()

    raw = (text or "").replace("\r", "\n")

    # Permitir coma, punto y coma o salto de línea.
    parts = re.split(r"[,;\n]+", raw)

    for part in parts:
        value = part.strip()

        # Quitar numeración o viñetas al pegar listas.
        value = re.sub(r"^\s*(?:[-*•]+|\d+[.)-])\s*", "", value).strip()

        if not value:
            continue

        key = value.casefold()

        if key not in seen:
            values.append(value)
            seen.add(key)

    return values


async def send_long_text(chat_id: int, text: str, context: ContextTypes.DEFAULT_TYPE) -> None:
    max_len = 3900
    remaining = text
    while remaining:
        if len(remaining) <= max_len:
            chunk = remaining
            remaining = ""
        else:
            split_at = remaining.rfind("\n", 0, max_len)
            if split_at < 1000:
                split_at = max_len
            chunk = remaining[:split_at]
            remaining = remaining[split_at:].lstrip("\n")
        await context.bot.send_message(chat_id=chat_id, text=chunk)


def main_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("📝 Palabras restringidas", callback_data="menu:words")],
            [InlineKeyboardButton("🕘 Mensaje diario", callback_data="menu:daily")],
            [
                InlineKeyboardButton("📊 Ver estado", callback_data="menu:status"),
                InlineKeyboardButton("📜 Historial", callback_data="menu:history"),
            ],
            [
                InlineKeyboardButton("🎭 Bromas internas", callback_data="menu:jokes"),
                InlineKeyboardButton("🌵 Silencio", callback_data="menu:silence"),
            ],
            [InlineKeyboardButton("📦 Duplicados", callback_data="menu:dups")],
            [InlineKeyboardButton("🆔 Mi ID", callback_data="pub:id")],
        ]
    )


def start_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("🆔 Ver mi ID", callback_data="pub:id"),
                InlineKeyboardButton("⚙️ Configuración", callback_data="pub:config"),
            ]
        ]
    )


def words_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("📋 Ver lista", callback_data="words:list"),
                InlineKeyboardButton("➕ Agregar", callback_data="words:add"),
            ],
            [
                InlineKeyboardButton("➖ Eliminar", callback_data="words:remove"),
                InlineKeyboardButton("🧹 Borrar todas", callback_data="words:clear_confirm"),
            ],
            [InlineKeyboardButton("⬅️ Volver", callback_data="menu:main")],
        ]
    )


def daily_menu() -> InlineKeyboardMarkup:
    enabled = db.is_true("daily_enabled")
    toggle_text = "🔴 Desactivar" if enabled else "🟢 Activar"
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton(toggle_text, callback_data="daily:toggle")],
            [
                InlineKeyboardButton("🕒 Cambiar hora", callback_data="daily:time"),
                InlineKeyboardButton("✏️ Cambiar texto", callback_data="daily:text"),
            ],
            [InlineKeyboardButton("👁️ Ver configuración", callback_data="daily:view")],
            [InlineKeyboardButton("⬅️ Volver", callback_data="menu:main")],
        ]
    )


def jokes_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("📋 Ver bromas", callback_data="jokes:list"),
                InlineKeyboardButton("➕ Agregar", callback_data="jokes:add"),
            ],
            [InlineKeyboardButton("➖ Eliminar por ID", callback_data="jokes:remove")],
            [InlineKeyboardButton("⬅️ Volver", callback_data="menu:main")],
        ]
    )


def silence_menu() -> InlineKeyboardMarkup:
    enabled = db.is_true("silence_enabled")
    toggle_text = "🔴 Desactivar" if enabled else "🟢 Activar"
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton(toggle_text, callback_data="silence:toggle")],
            [InlineKeyboardButton("⏱️ Cambiar horas", callback_data="silence:hours")],
            [InlineKeyboardButton("⬅️ Volver", callback_data="menu:main")],
        ]
    )


def duplicates_menu() -> InlineKeyboardMarkup:
    enabled = db.is_true("duplicates_enabled")
    toggle_text = "🔴 Desactivar detección" if enabled else "🟢 Activar detección"
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton(toggle_text, callback_data="dups:toggle")],
            [InlineKeyboardButton("🧹 Reiniciar historial", callback_data="dups:clear_confirm")],
            [InlineKeyboardButton("ℹ️ Cómo funciona", callback_data="dups:info")],
            [InlineKeyboardButton("⬅️ Volver", callback_data="menu:main")],
        ]
    )


async def safe_edit(query, text: str, markup: InlineKeyboardMarkup | None = None) -> None:
    try:
        await query.edit_message_text(text=text, reply_markup=markup)
    except BadRequest as exc:
        if "Message is not modified" not in str(exc):
            raise


async def command_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    chat = update.effective_chat
    if not message or not chat:
        return

    text = (
        "🤠 Pecos Paul Kele está activo.\n\n"
        "• modera palabras y frases restringidas\n"
        "• elimina el mensaje restringido y responde con humor\n"
        "• saluda y se despide\n"
        "• puede enviar mensajes diarios\n"
        "• encuestas, recuerdos, humor, bromas internas y reacciones\n"
        "• administración privada mediante botones"
    )

    if chat.type == ChatType.PRIVATE:
        text += "\n\n¿Qué quieres hacer?"
        await message.reply_text(text, reply_markup=start_menu())
    else:
        await message.reply_text(text)


async def command_id(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    user = update.effective_user
    chat = update.effective_chat
    if not message or not user or not chat:
        return

    if chat.type != ChatType.PRIVATE:
        await message.reply_text("🆔 Por seguridad, pregúntame tu ID por chat privado.")
        return

    await message.reply_text(f"🆔 Tu Telegram User ID es:\n\n{user.id}")


async def command_config(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    user = update.effective_user
    chat = update.effective_chat
    if not message or not user or not chat:
        return

    if chat.type != ChatType.PRIVATE:
        await message.reply_text("⚙️ La configuración solo está disponible por chat privado.")
        return

    if not ADMIN_USER_IDS:
        await message.reply_text(
            "La administración todavía no tiene usuarios autorizados.\n\n"
            f"Tu Telegram User ID es: {user.id}\n\n"
            "En Railway agrega la variable de entorno:\n"
            f"ADMIN_USER_IDS={user.id}\n\n"
            "Para varios administradores usa comas, por ejemplo:\n"
            "ADMIN_USER_IDS=123456789,987654321\n\n"
            "Luego vuelve a desplegar Pecos."
        )
        return

    if not is_admin(user.id):
        await message.reply_text("⛔ Este usuario no está autorizado para administrar a Pecos.")
        return

    PENDING_ADMIN_ACTION.pop(user.id, None)
    await message.reply_text("⚙️ Configuración de Pecos", reply_markup=main_menu())


async def command_poll(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    chat = update.effective_chat
    if not message or not chat:
        return

    raw = " ".join(context.args).strip()
    if not raw:
        await message.reply_text(
            "Uso:\n"
            "/encuesta ¿Asado sábado?\n\n"
            "O con opciones propias:\n"
            "/encuesta ¿Qué comemos? | Pizza | Asado | Empanadas"
        )
        return

    parts = [p.strip() for p in raw.split("|") if p.strip()]
    question = parts[0]

    if not (1 <= len(question) <= 300):
        await message.reply_text("La pregunta debe tener entre 1 y 300 caracteres.")
        return

    options = parts[1:] if len(parts) >= 3 else ["Sí", "No", "Quizás"]
    options = options[:10]

    if len(options) < 2:
        await message.reply_text("Necesito al menos dos opciones.")
        return

    try:
        await context.bot.send_poll(
            chat_id=chat.id,
            question=question,
            options=options,
            is_anonymous=False,
        )
    except TelegramError as exc:
        await message.reply_text(f"No pude crear la encuesta: {exc}")


async def command_remember(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    chat = update.effective_chat
    user = update.effective_user
    if not message or not chat or not user:
        return

    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        await message.reply_text("«Pecos recuerda» está pensado para usarse dentro del grupo.")
        return

    memory_text = " ".join(context.args).strip()
    if not memory_text:
        await message.reply_text(
            "Uso:\n/recordar reunión viernes 20:00"
        )
        return

    if len(memory_text) > 800:
        await message.reply_text("Ese recuerdo es demasiado largo. Máximo 800 caracteres.")
        return

    memory_id = db.add_memory(
        chat.id,
        memory_text,
        user.id,
        display_name(message),
    )

    await message.reply_text(
        f"🧠 Pecos lo recuerda. ID #{memory_id}\n"
        f"«{memory_text}»"
    )


async def command_memories(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    chat = update.effective_chat
    if not message or not chat:
        return

    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        await message.reply_text("Los recuerdos pertenecen a cada grupo.")
        return

    rows = db.list_memories(chat.id, 30)

    if not rows:
        await message.reply_text("🧠 Pecos no tiene recuerdos guardados en este grupo.")
        return

    lines = ["🧠 Recuerdos del grupo:\n"]
    for row in reversed(rows):
        lines.append(
            f"#{row['id']} — {row['text']}\n"
            f"   {row['created_by_name']} · {row['created_at']}"
        )

    await send_long_text(chat.id, "\n\n".join(lines), context)


async def command_forget(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    chat = update.effective_chat
    user = update.effective_user
    if not message or not chat or not user:
        return

    if not context.args or not context.args[0].isdigit():
        await message.reply_text("Uso: /olvidar 12")
        return

    memory_id = int(context.args[0])
    deleted = db.delete_memory(
        chat.id,
        memory_id,
        user.id,
        is_admin(user.id),
    )

    if deleted:
        await message.reply_text(f"🧠 Pecos olvidó el recuerdo #{memory_id}.")
    else:
        await message.reply_text(
            "No encontré ese recuerdo o no tienes permiso para borrarlo."
        )


async def command_pecos(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    if message:
        await message.reply_text(
            choose_random("pecos_command", PECOS_CALLED_MESSAGES, display_name(message))
        )


async def command_advice(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    if message:
        await message.reply_text(random.choice(ADVICE_MESSAGES))


async def command_phrase(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    if message:
        await message.reply_text(random.choice(PHRASE_MESSAGES))


async def command_excuse(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    if message:
        await message.reply_text(random.choice(EXCUSE_MESSAGES))


async def command_forecast(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    if message:
        await message.reply_text(random.choice(FORECAST_MESSAGES))


async def command_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = update.effective_user
    message = update.effective_message
    if not user or not message:
        return
    if not is_admin(user.id):
        return
    PENDING_ADMIN_ACTION.pop(user.id, None)
    await message.reply_text("Operación cancelada.", reply_markup=main_menu())


async def handle_admin_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    user = update.effective_user
    message = update.effective_message
    chat = update.effective_chat
    if (
        not user
        or not message
        or not chat
        or chat.type != ChatType.PRIVATE
        or not is_admin(user.id)
        or not message.text
    ):
        return False

    action = PENDING_ADMIN_ACTION.get(user.id)
    if not action:
        return False

    text = message.text.strip()

    if action == "words:add":
        terms = split_input_lines(text)
        if not terms:
            await message.reply_text("No encontré palabras o frases válidas. Intenta nuevamente o usa /cancel.")
            return True
        added = db.add_terms(terms)
        PENDING_ADMIN_ACTION.pop(user.id, None)
        db.add_history(f"ADMIN: agregó {added} palabra(s)/frase(s) restringida(s).")
        await message.reply_text(
            f"✅ Se agregaron {added} elemento(s).",
            reply_markup=words_menu(),
        )
        return True

    if action == "words:remove":
        terms = split_input_lines(text)
        removed = db.remove_terms(terms)
        PENDING_ADMIN_ACTION.pop(user.id, None)
        db.add_history(f"ADMIN: eliminó {removed} palabra(s)/frase(s) restringida(s).")
        await message.reply_text(
            f"✅ Se eliminaron {removed} elemento(s).",
            reply_markup=words_menu(),
        )
        return True

    if action == "daily:time":
        if not re.fullmatch(r"(?:[01]\d|2[0-3]):[0-5]\d", text):
            await message.reply_text(
                "Hora inválida. Escribe la hora en formato HH:MM, por ejemplo:\n09:30\n\nO usa /cancel."
            )
            return True
        db.set_setting("daily_time", text)
        PENDING_ADMIN_ACTION.pop(user.id, None)
        db.add_history(f"ADMIN: cambió la hora del mensaje diario a {text}.")
        await message.reply_text(
            f"✅ Hora diaria guardada: {text}",
            reply_markup=daily_menu(),
        )
        return True

    if action == "jokes:add":
        entries: list[tuple[str, int, str]] = []
        errors = []

        for raw_line in text.replace("\r", "\n").split("\n"):
            line = raw_line.strip()
            if not line:
                continue

            parts = [part.strip() for part in line.split("|", 2)]
            if len(parts) != 3:
                errors.append(line)
                continue

            username = parts[0].lstrip("@").strip()
            try:
                probability = int(parts[1])
            except ValueError:
                errors.append(line)
                continue

            response = parts[2].strip()

            if not username or not response or not (1 <= probability <= 100):
                errors.append(line)
                continue

            entries.append((username, probability, response))

        if not entries:
            await message.reply_text(
                "No pude agregar ninguna broma.\n\n"
                "Usa este formato, una por línea:\n"
                "@usuario | 35 | frase de Pecos\n\n"
                "El número es la probabilidad entre 1 y 100.\n"
                "Usa /cancel para cancelar."
            )
            return True

        added = db.add_jokes(entries, user.id)
        PENDING_ADMIN_ACTION.pop(user.id, None)
        db.add_history(f"ADMIN: agregó {added} broma(s) interna(s).")

        result = f"✅ Se agregaron {added} broma(s)."
        if errors:
            result += f"\n⚠️ {len(errors)} línea(s) no tenían el formato correcto."

        await message.reply_text(result, reply_markup=jokes_menu())
        return True

    if action == "jokes:remove":
        ids = []
        for token in re.split(r"[,;\s]+", text):
            token = token.strip()
            if token.isdigit():
                ids.append(int(token))

        removed = db.remove_jokes(ids)
        PENDING_ADMIN_ACTION.pop(user.id, None)
        db.add_history(f"ADMIN: eliminó {removed} broma(s) interna(s).")
        await message.reply_text(
            f"✅ Se eliminaron {removed} broma(s).",
            reply_markup=jokes_menu(),
        )
        return True

    if action == "silence:hours":
        try:
            hours = int(text)
        except ValueError:
            hours = 0

        if not (1 <= hours <= 72):
            await message.reply_text(
                "Escribe un número entero entre 1 y 72.\n"
                "Ejemplo: 8\n\nUsa /cancel para cancelar."
            )
            return True

        db.set_setting("silence_hours", str(hours))
        PENDING_ADMIN_ACTION.pop(user.id, None)
        db.add_history(f"ADMIN: detector de silencio configurado en {hours} hora(s).")
        await message.reply_text(
            f"✅ Pecos hablará después de {hours} hora(s) de silencio, máximo una vez al día.",
            reply_markup=silence_menu(),
        )
        return True

    if action == "daily:text":
        if not text:
            await message.reply_text("El mensaje no puede quedar vacío. Intenta nuevamente o usa /cancel.")
            return True
        if len(text) > 4000:
            await message.reply_text("El mensaje es demasiado largo. Usa menos de 4000 caracteres.")
            return True
        db.set_setting("daily_message", text)
        PENDING_ADMIN_ACTION.pop(user.id, None)
        db.add_history("ADMIN: cambió el texto del mensaje diario.")
        await message.reply_text(
            "✅ Mensaje diario actualizado.",
            reply_markup=daily_menu(),
        )
        return True

    return False


async def callback_router(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not query or not query.message:
        return

    data = query.data or ""
    user_id = query.from_user.id
    chat = query.message.chat

    # Acciones públicas del menú /start.
    if data == "pub:id":
        await query.answer()
        if chat.type != ChatType.PRIVATE:
            await query.message.reply_text("🆔 Usa este botón por chat privado.")
            return
        await query.message.reply_text(f"🆔 Tu Telegram User ID es:\n\n{user_id}")
        return

    if data == "pub:config":
        await query.answer()
        if chat.type != ChatType.PRIVATE:
            await query.message.reply_text("⚙️ La configuración solo funciona por chat privado.")
            return
        if not ADMIN_USER_IDS:
            await query.message.reply_text(
                "Todavía no hay administradores configurados.\n\n"
                f"Tu Telegram User ID es: {user_id}\n\n"
                "En Railway agrega:\n"
                f"ADMIN_USER_IDS={user_id}\n\n"
                "Para varios administradores usa comas, por ejemplo:\n"
                "ADMIN_USER_IDS=123456789,987654321\n\n"
                "y vuelve a desplegar Pecos."
            )
            return
        if not is_admin(user_id):
            await query.message.reply_text("⛔ No estás autorizado para administrar a Pecos.")
            return
        PENDING_ADMIN_ACTION.pop(user_id, None)
        await safe_edit(query, "⚙️ Configuración de Pecos", main_menu())
        return

    # Desde aquí, todo es administración privada.
    if chat.type != ChatType.PRIVATE or not is_admin(user_id):
        await query.answer("No autorizado.", show_alert=True)
        return

    await query.answer()

    if data == "menu:main":
        PENDING_ADMIN_ACTION.pop(user_id, None)
        await safe_edit(query, "⚙️ Configuración de Pecos", main_menu())
        return

    if data == "menu:words":
        PENDING_ADMIN_ACTION.pop(user_id, None)
        await safe_edit(
            query,
            f"📝 Palabras y frases restringidas\n\nRegistradas: {len(db.list_terms())}",
            words_menu(),
        )
        return

    if data == "words:list":
        terms = db.list_terms()
        if not terms:
            text = "📋 No hay palabras o frases restringidas registradas."
        else:
            text = "📋 Palabras/frases restringidas:\n\n" + "\n".join(
                f"{i}. {term}" for i, term in enumerate(terms, start=1)
            )
        await send_long_text(chat.id, text, context)
        return

    if data == "words:add":
        PENDING_ADMIN_ACTION[user_id] = "words:add"
        await query.message.reply_text(
            "➕ Envíame todas las palabras o frases que quieras agregar en un solo mensaje.\n\n"
            "Puedes separarlas por:\n"
            "• comas\n"
            "• punto y coma\n"
            "• una por línea\n\n"
            "Ejemplo:\n"
            "lool, palabra dos, frase restringida, otra frase\n\n"
            "También puedes pegar una lista completa.\n\n"
            "Usa /cancel para cancelar."
        )
        return

    if data == "words:remove":
        PENDING_ADMIN_ACTION[user_id] = "words:remove"
        await query.message.reply_text(
            "➖ Envíame todas las palabras o frases que quieras eliminar en un solo mensaje.\n\n"
            "Puedes separarlas por comas, punto y coma o una por línea.\n\n"
            "Ejemplo:\n"
            "lool, palabra dos, frase restringida\n\n"
            "Usa /cancel para cancelar."
        )
        return

    if data == "words:clear_confirm":
        markup = InlineKeyboardMarkup(
            [
                [
                    InlineKeyboardButton("✅ Sí, borrar todas", callback_data="words:clear_yes"),
                    InlineKeyboardButton("❌ No", callback_data="menu:words"),
                ]
            ]
        )
        await safe_edit(
            query,
            "⚠️ ¿Seguro que quieres borrar TODAS las palabras y frases restringidas?",
            markup,
        )
        return

    if data == "words:clear_yes":
        count = db.clear_terms()
        db.add_history(f"ADMIN: borró todas las palabras restringidas ({count}).")
        await safe_edit(
            query,
            f"✅ Se borraron {count} elemento(s).",
            words_menu(),
        )
        return

    if data == "menu:jokes":
        PENDING_ADMIN_ACTION.pop(user_id, None)
        await safe_edit(
            query,
            f"🎭 Bromas internas\n\nConfiguradas: {len(db.list_jokes())}",
            jokes_menu(),
        )
        return

    if data == "jokes:list":
        rows = db.list_jokes()
        if not rows:
            await query.message.reply_text("🎭 No hay bromas internas configuradas.")
            return

        lines = ["🎭 Bromas internas:\n"]
        for row in rows:
            lines.append(
                f"ID {row['id']} — @{row['username']} — {row['probability']}%\n"
                f"↳ {row['response']}"
            )

        await send_long_text(chat.id, "\n\n".join(lines), context)
        return

    if data == "jokes:add":
        PENDING_ADMIN_ACTION[user_id] = "jokes:add"
        await query.message.reply_text(
            "➕ Envíame una o varias bromas, una por línea.\n\n"
            "Formato:\n"
            "@usuario | probabilidad | respuesta\n\n"
            "Ejemplo:\n"
            "@juan | 35 | 👀 Cada vez que nombran a Juan, Pecos sospecha algo.\n"
            "@pedro | 20 | 🤠 Pedro apareció en la conversación. Esto se pone interesante.\n\n"
            "Usa /cancel para cancelar."
        )
        return

    if data == "jokes:remove":
        PENDING_ADMIN_ACTION[user_id] = "jokes:remove"
        await query.message.reply_text(
            "➖ Envíame los ID de las bromas que quieras eliminar.\n\n"
            "Ejemplo:\n1, 3, 5\n\n"
            "Puedes ver los ID con «Ver bromas».\n"
            "Usa /cancel para cancelar."
        )
        return

    if data == "menu:silence":
        PENDING_ADMIN_ACTION.pop(user_id, None)
        await safe_edit(
            query,
            "🌵 Detector de silencio\n\n"
            f"Estado: {'ACTIVO' if db.is_true('silence_enabled') else 'DESACTIVADO'}\n"
            f"Tiempo: {db.get_setting('silence_hours', '8')} hora(s)\n"
            "Máximo: una intervención por grupo al día\n"
            "Horario: 09:00–22:00",
            silence_menu(),
        )
        return

    if data == "silence:toggle":
        enabled = not db.is_true("silence_enabled")
        db.set_setting("silence_enabled", "1" if enabled else "0")
        db.add_history(
            f"ADMIN: detector de silencio {'activado' if enabled else 'desactivado'}."
        )
        await safe_edit(
            query,
            "🌵 Detector de silencio\n\n"
            f"Estado: {'ACTIVO' if enabled else 'DESACTIVADO'}\n"
            f"Tiempo: {db.get_setting('silence_hours', '8')} hora(s)\n"
            "Máximo: una intervención por grupo al día\n"
            "Horario: 09:00–22:00",
            silence_menu(),
        )
        return

    if data == "silence:hours":
        PENDING_ADMIN_ACTION[user_id] = "silence:hours"
        await query.message.reply_text(
            "⏱️ ¿Después de cuántas horas de silencio debe hablar Pecos?\n\n"
            "Escribe un número entre 1 y 72.\n"
            "Ejemplo: 8\n\nUsa /cancel para cancelar."
        )
        return

    if data == "menu:daily":
        PENDING_ADMIN_ACTION.pop(user_id, None)
        status = "ACTIVO" if db.is_true("daily_enabled") else "DESACTIVADO"
        await safe_edit(
            query,
            f"🕘 Mensaje diario\n\nEstado: {status}\nHora: {db.get_setting('daily_time')}\nZona: {TIMEZONE_NAME}",
            daily_menu(),
        )
        return

    if data == "daily:toggle":
        enabled = not db.is_true("daily_enabled")
        db.set_setting("daily_enabled", "1" if enabled else "0")
        db.add_history(f"ADMIN: mensaje diario {'activado' if enabled else 'desactivado'}.")
        await safe_edit(
            query,
            f"🕘 Mensaje diario\n\nEstado: {'ACTIVO' if enabled else 'DESACTIVADO'}\n"
            f"Hora: {db.get_setting('daily_time')}\nZona: {TIMEZONE_NAME}",
            daily_menu(),
        )
        return

    if data == "daily:time":
        PENDING_ADMIN_ACTION[user_id] = "daily:time"
        await query.message.reply_text(
            "🕒 Escribe la nueva hora en formato HH:MM.\n\nEjemplo: 09:30\n\nUsa /cancel para cancelar."
        )
        return

    if data == "daily:text":
        PENDING_ADMIN_ACTION[user_id] = "daily:text"
        await query.message.reply_text(
            "✏️ Envíame el nuevo texto del mensaje diario.\n\nUsa /cancel para cancelar."
        )
        return

    if data == "daily:view":
        enabled = "Sí" if db.is_true("daily_enabled") else "No"
        await query.message.reply_text(
            "👁️ Configuración del mensaje diario\n\n"
            f"Activo: {enabled}\n"
            f"Hora: {db.get_setting('daily_time')}\n"
            f"Zona horaria: {TIMEZONE_NAME}\n\n"
            f"Mensaje:\n{db.get_setting('daily_message')}"
        )
        return

    if data == "menu:status":
        groups = db.list_groups()
        unique_count, hash_count = db.duplicate_counts()
        status_text = (
            f"📊 Estado de {APP_NAME}\n\n"
            f"Versión: {VERSION}\n"
            f"Administradores configurados: {len(ADMIN_USER_IDS)}\n"
            f"Palabras/frases restringidas: {len(db.list_terms())}\n"
            f"Grupos conocidos: {len(groups)}\n"
            f"Mensaje diario: {'Activo' if db.is_true('daily_enabled') else 'Desactivado'}\n"
            f"Hora diaria: {db.get_setting('daily_time')} ({TIMEZONE_NAME})\n"
            f"Bot API: {'LOCAL integrada (--local)' if LOCAL_BOT_API else 'PÚBLICA'}\n"
            f"Bromas internas: {len(db.list_jokes())}\n"
            f"Detector de silencio: {'Activo' if db.is_true('silence_enabled') else 'Desactivado'} "
            f"({db.get_setting('silence_hours', '8')} h)\n"
            f"Duplicados: {'Activo' if db.is_true('duplicates_enabled') else 'Desactivado'}\n"
            f"FileUniqueId registrados: {unique_count}\n"
            f"SHA-256 registrados: {hash_count}\n"
            f"Base de datos: {DB_PATH.name}"
        )
        await query.message.reply_text(status_text)
        return

    if data == "menu:history":
        rows = db.recent_history(20)
        if not rows:
            text = "📜 El historial está vacío."
        else:
            text = "📜 Últimos eventos:\n\n" + "\n".join(
                f"[{row['ts']}] {row['event']}" for row in rows
            )
        markup = InlineKeyboardMarkup(
            [
                [InlineKeyboardButton("🧹 Borrar historial", callback_data="history:clear_confirm")],
                [InlineKeyboardButton("⬅️ Volver", callback_data="menu:main")],
            ]
        )
        await send_long_text(chat.id, text, context)
        await query.message.reply_text("Opciones de historial:", reply_markup=markup)
        return

    if data == "history:clear_confirm":
        markup = InlineKeyboardMarkup(
            [
                [
                    InlineKeyboardButton("✅ Sí, borrar", callback_data="history:clear_yes"),
                    InlineKeyboardButton("❌ No", callback_data="menu:main"),
                ]
            ]
        )
        await safe_edit(query, "⚠️ ¿Borrar todo el historial de eventos?", markup)
        return

    if data == "history:clear_yes":
        count = db.clear_history()
        await safe_edit(
            query,
            f"✅ Historial borrado: {count} evento(s).",
            main_menu(),
        )
        return

    if data == "menu:dups":
        PENDING_ADMIN_ACTION.pop(user_id, None)
        unique_count, hash_count = db.duplicate_counts()
        await safe_edit(
            query,
            "📦 Detección de duplicados\n\n"
            f"Estado: {'ACTIVA' if db.is_true('duplicates_enabled') else 'DESACTIVADA'}\n"
            f"IDs de Telegram registrados: {unique_count}\n"
            f"SHA-256 registrados: {hash_count}",
            duplicates_menu(),
        )
        return

    if data == "dups:toggle":
        enabled = not db.is_true("duplicates_enabled")
        db.set_setting("duplicates_enabled", "1" if enabled else "0")
        db.add_history(f"ADMIN: detección de duplicados {'activada' if enabled else 'desactivada'}.")
        unique_count, hash_count = db.duplicate_counts()
        await safe_edit(
            query,
            "📦 Detección de duplicados\n\n"
            f"Estado: {'ACTIVA' if enabled else 'DESACTIVADA'}\n"
            f"IDs de Telegram registrados: {unique_count}\n"
            f"SHA-256 registrados: {hash_count}",
            duplicates_menu(),
        )
        return

    if data == "dups:clear_confirm":
        markup = InlineKeyboardMarkup(
            [
                [
                    InlineKeyboardButton("✅ Sí, reiniciar", callback_data="dups:clear_yes"),
                    InlineKeyboardButton("❌ No", callback_data="menu:dups"),
                ]
            ]
        )
        await safe_edit(query, "⚠️ ¿Reiniciar todo el historial de archivos duplicados?", markup)
        return

    if data == "dups:clear_yes":
        unique_count, hash_count = db.clear_duplicates()
        db.add_history(
            f"ADMIN: reinició duplicados ({unique_count} IDs, {hash_count} SHA-256)."
        )
        await safe_edit(
            query,
            f"✅ Historial de duplicados reiniciado.\n"
            f"IDs eliminados: {unique_count}\nSHA-256 eliminados: {hash_count}",
            duplicates_menu(),
        )
        return

    if data == "dups:info":
        if LOCAL_BOT_API:
            detail = (
                "• Bot API local: ACTIVA.\n"
                "• Pecos calcula SHA-256 del contenido real sin el límite público de 20 MB.\n"
                "• Si cambian el nombre pero el contenido es idéntico, el SHA-256 coincide.\n"
                "• FileUniqueId se usa como detección rápida adicional."
            )
        else:
            detail = (
                "• Bot API pública: activa.\n"
                "• FileUniqueId se compara para todos los tamaños.\n"
                "• SHA-256 real solo se calcula hasta 20 MB."
            )

        await query.message.reply_text(
            "ℹ️ Duplicados en Pecos\n\n"
            + detail
            + "\n\nNo usamos nombre+tamaño como prueba de duplicado."
        )
        return


def resolve_local_file_path(raw_path: str | None) -> Path | None:
    """
    Resuelve de forma robusta el file_path entregado por Telegram Bot API --local.

    Telegram documenta que getFile en modo local devuelve una ruta absoluta.
    PTB también puede devolver un file:// URI en algunos flujos. Aquí aceptamos
    ambas formas y evitamos depender de download_to_drive() para el hash.
    """
    if not raw_path:
        return None

    value = str(raw_path).strip()

    if value.startswith("file://"):
        parsed = urlparse(value)
        value = unquote(parsed.path)

    candidate = Path(value)

    if candidate.is_absolute() and candidate.is_file():
        return candidate

    return None


async def wait_for_complete_local_file(
    path: Path,
    expected_size: int,
    timeout_seconds: int = 120,
) -> int:
    """
    Espera a que el archivo local alcance el tamaño informado por Telegram.
    Esto evita calcular el hash mientras un archivo grande todavía se está
    materializando en disco.
    """
    deadline = time.monotonic() + timeout_seconds
    last_size = -1
    stable_checks = 0

    while time.monotonic() < deadline:
        try:
            current_size = path.stat().st_size
        except OSError:
            current_size = -1

        if expected_size > 0:
            if current_size == expected_size:
                return current_size
        else:
            if current_size > 0 and current_size == last_size:
                stable_checks += 1
                if stable_checks >= 3:
                    return current_size
            else:
                stable_checks = 0

        last_size = current_size
        await asyncio.sleep(0.5)

    raise RuntimeError(
        f"archivo local incompleto tras {timeout_seconds}s "
        f"(esperado={expected_size}, actual={last_size})"
    )


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()

    with path.open("rb") as handle:
        while True:
            chunk = handle.read(1024 * 1024)
            if not chunk:
                break
            digest.update(chunk)

    return digest.hexdigest()


def media_info(message: Message):
    obj = None
    if message.document:
        obj = message.document
    elif message.video:
        obj = message.video
    elif message.audio:
        obj = message.audio
    elif message.voice:
        obj = message.voice
    elif message.animation:
        obj = message.animation
    elif message.video_note:
        obj = message.video_note
    elif message.photo:
        obj = message.photo[-1]

    if obj is None:
        return None

    return {
        "file_id": getattr(obj, "file_id", None),
        "file_unique_id": getattr(obj, "file_unique_id", None),
        "file_size": getattr(obj, "file_size", None),
        "file_name": getattr(obj, "file_name", None) or "",
    }


async def handle_duplicate(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    """
    Detecta duplicados por contenido real.

    En la arquitectura unificada, Telegram Bot API y Pecos viven en el mismo
    contenedor. En LOCAL_BOT_API el file_path devuelto por getFile es una ruta
    absoluta accesible directamente por Pecos, incluso para archivos grandes.

    Criterio principal: SHA-256 del contenido. El nombre del archivo NO se usa
    para decidir si es duplicado.
    """
    info = media_info(message)
    if not info:
        return False

    chat_id = message.chat_id
    message_id = message.message_id
    unique_id = info["file_unique_id"] or ""
    file_id = info["file_id"]
    file_size = int(info["file_size"] or 0)
    file_name = info["file_name"] or "archivo"

    sender = message.from_user
    sender_id = int(sender.id) if sender else 0

    if sender and sender.username:
        sender_name = f"@{sender.username}"
    else:
        sender_name = display_name(message)

    if not file_id:
        return False

    try:
        # FileUniqueId es una vía rápida adicional. No sustituye al SHA-256.
        # Solo consultamos aquí; el ID se registra después de que el archivo
        # haya sido procesado correctamente.
        if unique_id and db.unique_file_seen(chat_id, unique_id, message_id):
            try:
                await context.bot.delete_message(
                    chat_id=chat_id,
                    message_id=message_id,
                )
                await context.bot.send_message(
                    chat_id=chat_id,
                    text=(
                        "⚠️ Pecos retiró un archivo que Telegram ya había "
                        "identificado previamente en este grupo.\n\n"
                        f"📄 Archivo: {file_name}"
                    ),
                )
                db.add_history(
                    f"DUPLICADO eliminado por FileUniqueId en chat {chat_id}: {file_name}"
                )
                return True
            except TelegramError as exc:
                log.warning(
                    "Duplicado detectado por FileUniqueId, pero no se pudo eliminar: %s",
                    exc,
                )
                return False

        sha256 = None
        original = None

        # Serializamos lectura + hash + reclamación de huella. Además, SQLite
        # protege la clave primaria (chat_id, sha256), por lo que el registro
        # del original es atómico.
        async with HASH_SEMAPHORE:
            started = time.monotonic()

            if LOCAL_BOT_API:
                telegram_file = await context.bot.get_file(file_id)
                raw_file_path = getattr(telegram_file, "file_path", None)
                local_path = resolve_local_file_path(raw_file_path)

                if local_path is None:
                    raise RuntimeError(
                        "Bot API local devolvió una ruta que Pecos no puede abrir: "
                        f"{raw_file_path!r}. Telegram Bot API y Pecos deben compartir "
                        "el mismo contenedor/sistema de archivos."
                    )

                actual_size = await wait_for_complete_local_file(
                    local_path,
                    file_size,
                    timeout_seconds=300,
                )

                sha256 = await asyncio.to_thread(sha256_file, local_path)

                elapsed = time.monotonic() - started
                log.info(
                    "SHA-256 calculado | archivo=%s | informado=%s | local=%s "
                    "| tiempo=%.2fs | digest=%s... | path=%s",
                    file_name,
                    file_size,
                    actual_size,
                    elapsed,
                    sha256[:12],
                    local_path,
                )

            elif file_size and file_size <= MAX_HASH_DOWNLOAD:
                # Compatibilidad de emergencia si alguien desactiva por error
                # la Bot API local. La API pública solo permite este flujo para
                # archivos pequeños.
                telegram_file = await context.bot.get_file(file_id)
                data = await telegram_file.download_as_bytearray()
                sha256 = await asyncio.to_thread(
                    lambda: hashlib.sha256(bytes(data)).hexdigest()
                )
            else:
                raise RuntimeError(
                    "LOCAL_BOT_API está desactivada y el archivo supera el límite "
                    "permitido para calcular SHA-256 mediante la Bot API pública."
                )

            if not sha256:
                raise RuntimeError("No se obtuvo SHA-256 para el archivo.")

            original = db.claim_fingerprint(
                chat_id=chat_id,
                sha256=sha256,
                message_id=message_id,
                file_unique_id=unique_id,
                file_name=file_name,
                file_size=file_size,
                sender_id=sender_id,
                sender_name=sender_name,
            )

            if original is None:
                if unique_id:
                    db.store_unique_file(chat_id, unique_id, message_id)

                log.info(
                    "HUELLA registrada | archivo=%s | size=%s | digest=%s...",
                    file_name,
                    file_size,
                    sha256[:12],
                )
                return False

        # Si llegamos aquí, SQLite confirmó que el SHA-256 ya estaba registrado.
        try:
            await context.bot.delete_message(
                chat_id=chat_id,
                message_id=message_id,
            )

            original_name = original["file_name"] or "archivo"
            original_sender = original["sender_name"] or "otro usuario"

            try:
                first_seen = datetime.fromisoformat(
                    str(original["first_seen"])
                ).astimezone(BOT_TZ)
                first_seen_text = first_seen.strftime("%d/%m/%Y %H:%M")
            except Exception:
                first_seen_text = str(original["first_seen"])

            await context.bot.send_message(
                chat_id=chat_id,
                text=(
                    "⚠️ Pecos confirmó un archivo duplicado por contenido real.\n\n"
                    f"📄 Original: {original_name}\n"
                    f"👤 Enviado por: {original_sender}\n"
                    f"🕘 Primera vez: {first_seen_text}\n\n"
                    f"El archivo «{file_name}» tiene exactamente el mismo SHA-256 "
                    "y fue retirado. El nombre del archivo no influye en la comparación."
                ),
            )

            db.add_history(
                f"DUPLICADO eliminado por SHA-256 en chat {chat_id}: "
                f"{file_name} == {original_name}"
            )

            log.info(
                "DUPLICADO SHA-256 eliminado | nuevo=%s | original=%s | digest=%s...",
                file_name,
                original_name,
                sha256[:12],
            )
            return True

        except TelegramError as exc:
            log.warning(
                "SHA-256 duplicado detectado, pero no se pudo eliminar: %s",
                exc,
            )
            return False

    except Exception as exc:
        log.warning(
            "DUPLICADOS: fallo comprobando archivo=%s size=%s tipo=%s detalle=%s",
            file_name,
            file_size,
            type(exc).__name__,
            str(exc),
        )
        db.add_history(
            f"ERROR duplicados [{type(exc).__name__}] {file_name}: {exc}"
        )
        return False


async def moderate_if_needed(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    text = message.text or message.caption or ""
    if not text:
        return False

    blocked = find_blocked_term(text)
    if not blocked:
        return False

    usuario = display_name(message)

    try:
        await context.bot.delete_message(
            chat_id=message.chat_id,
            message_id=message.message_id,
        )
    except TelegramError as exc:
        log.warning("No se pudo eliminar mensaje restringido: %s", exc)
        db.add_history(
            f"RESTRINGIDO detectado pero NO eliminado | {usuario} | término: {blocked}"
        )
        return False

    response = choose_random("moderation", FUN_MODERATION_MESSAGES, usuario)
    try:
        await context.bot.send_message(chat_id=message.chat_id, text=response)
        mark_pecos_context(message.chat_id)
    except TelegramError as exc:
        log.warning("Mensaje eliminado, pero no se pudo publicar respuesta: %s", exc)

    db.add_history(
        f"MENSAJE RETIRADO | {usuario} | chat {message.chat_id} | término: {blocked}"
    )
    return True


def mark_pecos_context(chat_id: int) -> None:
    RECENT_PECOS_CONTEXT[chat_id] = time.monotonic()


def has_recent_pecos_context(chat_id: int) -> bool:
    ts = RECENT_PECOS_CONTEXT.get(chat_id)
    if ts is None:
        return False

    if time.monotonic() - ts <= PECOS_CONTEXT_SECONDS:
        return True

    RECENT_PECOS_CONTEXT.pop(chat_id, None)
    return False


def is_reply_to_pecos(message: Message, bot_id: int) -> bool:
    replied = message.reply_to_message
    if not replied or not replied.from_user:
        return False

    return replied.from_user.id == bot_id


async def handle_identity(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    if not message.text:
        return False

    normalized = normalize_intent(message.text)

    # La pregunta debe estar realmente dirigida a Pecos.
    mentions_pecos = bool(
        re.search(r"\b(pecos|peco)\b", normalized)
    )

    mentions_bot = (
        bool(re.search(r"\b(bot|robot)\b", normalized))
        or "este bot" in normalized
        or "ese bot" in normalized
    )

    reply_to_pecos = is_reply_to_pecos(
        message,
        context.bot.id,
    )

    recent_context = has_recent_pecos_context(
        message.chat_id
    )

    # Preguntas explícitas de identidad.
    explicit_identity_question = (
        "como te llamas" in normalized
        or "cual es tu nombre" in normalized
        or "como es tu nombre" in normalized
        or "quien eres" in normalized
        or "quien es este bot" in normalized
        or "quien es ese bot" in normalized
        or "como se llama este bot" in normalized
        or "como se llama ese bot" in normalized
    )

    # Preguntas contextuales cortas del tipo:
    # "¿y este quién es?", "¿y este bot?", "¿este quién es?"
    contextual_identity_question = (
        "y este quien es" in normalized
        or "este quien es" in normalized
        or "y ese quien es" in normalized
        or "ese quien es" in normalized
        or normalized.strip() in {
            "y este bot",
            "este bot",
            "y ese bot",
            "ese bot",
            "y este",
            "y ese",
        }
    )

    directed_to_pecos = (
        mentions_pecos
        or mentions_bot
        or reply_to_pecos
        or (recent_context and contextual_identity_question)
    )

    # Regla clave:
    # "¿Cómo te llamas?" a secas NO activa a Pecos.
    # Debe existir una señal de que la pregunta es para él.
    if not directed_to_pecos:
        return False

    if not (explicit_identity_question or contextual_identity_question):
        return False

    await message.reply_text(
        "Mi nombre es Pecos Paul Kele, vengo de los United States."
    )

    # Consumimos el contexto para que no responda repetidamente a preguntas
    # ambiguas mucho tiempo después.
    RECENT_PECOS_CONTEXT.pop(
        message.chat_id,
        None,
    )

    return True


async def handle_new_members(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    members = message.new_chat_members or []
    real_members = [
        member for member in members
        if member.id != context.bot.id
    ]

    if not real_members:
        return False

    for member in real_members:
        if member.username:
            usuario = f"@{member.username}"
        else:
            usuario = member.full_name or str(member.id)

        await message.reply_text(
            choose_random("welcome", WELCOME_MESSAGES, usuario)
        )

        db.add_history(f"BIENVENIDA a {usuario} en chat {message.chat_id}.")

    return True


async def handle_internal_joke(message: Message) -> bool:
    text_value = message.text or message.caption or ""
    if not text_value:
        return False

    normalized = text_value.casefold()

    for row in db.list_jokes():
        username = str(row["username"]).casefold()

        if not re.search(
            rf"(?<![\w])@{re.escape(username)}(?![\w])",
            normalized,
        ):
            continue

        if random.randint(1, 100) <= int(row["probability"]):
            await message.reply_text(str(row["response"]))
            return True

    return False


async def handle_direct_pecos_mention(message: Message) -> bool:
    if not message.text:
        return False

    normalized = normalize_intent(message.text).strip()

    if not re.search(r"\b(pecos|peco)\b", normalized):
        return False

    usuario = display_name(message)

    if (
        "que opinas" in normalized
        or "que piensas" in normalized
        or "que dices" in normalized
        or "tu opinion" in normalized
    ):
        await message.reply_text(
            choose_random("pecos_opinion", PECOS_OPINION_MESSAGES, usuario)
        )
        return True

    if (
        "estas ahi" in normalized
        or "andas por ahi" in normalized
        or "me escuchas" in normalized
        or normalized in {"pecos", "peco", "oye pecos", "oye peco"}
    ):
        await message.reply_text(
            choose_random("pecos_called", PECOS_CALLED_MESSAGES, usuario)
        )
        return True

    if "ayuda" in normalized or "ayudame" in normalized:
        await message.reply_text(
            f"🤠 Aquí estoy, {usuario}. Dime qué necesitas y Pecos hará lo que pueda."
        )
        return True

    if "?" in message.text:
        await message.reply_text(
            choose_random("pecos_question", PECOS_QUESTION_MESSAGES, usuario)
        )
        return True

    # Si solo lo nombran en una frase normal, responde ocasionalmente para no invadir.
    if random.randint(1, 100) <= 35:
        await message.reply_text(
            choose_random("pecos_called", PECOS_CALLED_MESSAGES, usuario)
        )
        return True

    return False


async def maybe_react_to_message(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    if not message.text:
        return False

    normalized = normalize_intent(message.text)
    emoji = None
    probability = 0

    if re.search(r"\b(jaja+|jeje+|jiji+|lol|xd)\b", normalized) or "😂" in message.text or "🤣" in message.text:
        emoji = "😂"
        probability = 65
    elif any(word in normalized for word in ("gracias", "excelente", "genial", "perfecto", "buena noticia")):
        emoji = random.choice(["👍", "❤️", "👏"])
        probability = 55
    elif any(word in normalized for word in ("felicitaciones", "felicidades", "bravo")):
        emoji = random.choice(["🎉", "🔥", "👏"])
        probability = 75
    elif "que opinan" in normalized or "que piensan" in normalized:
        emoji = "🤔"
        probability = 45
    elif any(word in normalized for word in ("miren", "mira esto", "vean esto")):
        emoji = "👀"
        probability = 40

    if not emoji or random.randint(1, 100) > probability:
        return False

    try:
        await context.bot.set_message_reaction(
            chat_id=message.chat_id,
            message_id=message.message_id,
            reaction=emoji,
        )
        return True
    except TelegramError:
        # Si el grupo no permite esa reacción, Pecos simplemente no insiste.
        return False


async def handle_special_daily_user_greeting(
    message: Message,
) -> bool:
    """
    Si @leosedf escribe por primera vez en el día, Pecos responde una sola vez.
    El control queda guardado en SQLite, por lo que sobrevive a redeploys,
    reinicios del bot y actualizaciones de main.py.
    """
    user = message.from_user

    if not user or not user.username:
        return False

    if user.username.casefold() != SPECIAL_DAILY_USERNAME.casefold():
        return False

    today = datetime.now(BOT_TZ).strftime("%Y-%m-%d")

    first_today = db.claim_daily_user_event(
        SPECIAL_DAILY_EVENT_KEY,
        user.id,
        user.username,
        today,
    )

    if not first_today:
        return False

    await message.reply_text(
        SPECIAL_DAILY_MESSAGE
    )

    db.add_history(
        f"SALUDO ESPECIAL DIARIO enviado a @{user.username}."
    )

    return True


async def handle_collective_greeting(message: Message) -> bool:
    """
    Responde a saludos claramente dirigidos a todo el grupo, aunque Pecos
    no sea mencionado explícitamente.

    Ejemplos:
    - "Saludos a todos y a cada uno"
    - "Hola a todos"
    - "Buenos días a todos"
    - "Buenas tardes para todos"
    - "Saludos a todo el grupo"

    Si el mensaje menciona a Pecos/Peco explícitamente, dejamos que
    handle_social() use el saludo normal.
    """
    if not message.text:
        return False

    normalized = normalize_intent(message.text).strip()

    # Si Pecos fue nombrado, el saludo ya está dirigido a él de forma explícita.
    if re.search(r"\b(pecos|peco)\b", normalized):
        return False

    greeting_signal = (
        bool(re.search(r"\b(saludo|saludos|hola|hello|hey|holi|buenas)\b", normalized))
        or "buenos dias" in normalized
        or "buen dia" in normalized
        or "buenas tardes" in normalized
        or "buenas noches" in normalized
        or "muy buenas" in normalized
    )

    collective_signal = (
        "a todos" in normalized
        or "para todos" in normalized
        or "a cada uno" in normalized
        or "para cada uno" in normalized
        or "a todo el grupo" in normalized
        or "para todo el grupo" in normalized
        or "a todos los presentes" in normalized
        or "para todos los presentes" in normalized
        or bool(re.search(r"\b(hola|saludos|buenas)\s+(gente|amigos|grupo)\b", normalized))
    )

    if not (greeting_signal and collective_signal):
        return False

    usuario = display_name(message)

    await message.reply_text(
        choose_random(
            "collective_greeting",
            COLLECTIVE_GREETINGS,
            usuario,
        )
    )

    return True


async def handle_social(message: Message) -> bool:
    if not message.text:
        return False

    normalized = normalize_intent(message.text)
    if not re.search(r"\b(pecos|peco)\b", normalized):
        return False

    usuario = display_name(message)

    is_farewell = (
        bool(re.search(r"\b(chao|chau|adios|bye)\b", normalized))
        or "hasta luego" in normalized
        or "hasta manana" in normalized
        or "nos vemos" in normalized
        or "me voy" in normalized
        or "que descanses" in normalized
        or "hasta pronto" in normalized
        or "hasta la proxima" in normalized
    )

    if is_farewell:
        await message.reply_text(choose_random("farewell", FAREWELLS, usuario))
        return True

    if "buenos dias" in normalized or "buen dia" in normalized:
        await message.reply_text(choose_random("morning", MORNING_GREETINGS, usuario))
        return True

    if "buenas tardes" in normalized:
        await message.reply_text(choose_random("afternoon", AFTERNOON_GREETINGS, usuario))
        return True

    if "buenas noches" in normalized:
        await message.reply_text(choose_random("night", NIGHT_GREETINGS, usuario))
        return True

    if re.search(r"\b(hola|hello|hey|holi|saludos|buenas)\b", normalized):
        await message.reply_text(choose_random("general", GENERAL_GREETINGS, usuario))
        return True

    return False


async def on_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    chat = update.effective_chat
    user = update.effective_user
    if not message or not chat:
        return

    # Los eventos de nuevos miembros pueden llegar como mensajes de servicio.
    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        if message.new_chat_members:
            await handle_new_members(message, context)

    if user and user.is_bot:
        return

    # Registrar solo grupos para el mensaje diario.
    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        db.register_group(chat)

    # Si el administrador está escribiendo un dato solicitado por el menú.
    if await handle_admin_text(update, context):
        return

    # Los CommandHandler ya procesaron los comandos en el grupo 0.
    # Evitamos que un comando como /pecos produzca una segunda respuesta aquí.
    if message.text and message.text.startswith("/"):
        return

    is_edited = bool(update.edited_message or update.edited_channel_post)

    # Saludo especial persistente para @leosedf:
    # una sola vez por día, en su primera aparición.
    if (
        not is_edited
        and chat.type in (ChatType.GROUP, ChatType.SUPERGROUP)
    ):
        await handle_special_daily_user_greeting(message)

    # Duplicados solo en mensajes NUEVOS de grupos.
    if (
        not is_edited
        and chat.type in (ChatType.GROUP, ChatType.SUPERGROUP)
        and db.is_true("duplicates_enabled")
    ):
        if await handle_duplicate(message, context):
            return

    # Moderación tiene prioridad sobre saludos/respuestas.
    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        if await moderate_if_needed(message, context):
            return

    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        if await handle_collective_greeting(message):
            return

        if await handle_internal_joke(message):
            return

    if await handle_identity(message, context):
        return

    if await handle_social(message):
        return

    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        if await handle_direct_pecos_mention(message):
            return

        await maybe_react_to_message(message, context)


async def check_group_silence(application: Application) -> None:
    if not db.is_true("silence_enabled"):
        return

    now = datetime.now(BOT_TZ)

    # Evita que Pecos rompa el silencio durante la madrugada.
    if not (9 <= now.hour < 22):
        return

    try:
        silence_hours = int(db.get_setting("silence_hours", "8"))
    except ValueError:
        silence_hours = 8

    silence_hours = max(1, min(72, silence_hours))
    today = now.strftime("%Y-%m-%d")

    for row in db.list_groups():
        try:
            last_seen = datetime.fromisoformat(str(row["last_seen"]))
        except Exception:
            continue

        elapsed_hours = (now - last_seen).total_seconds() / 3600.0

        if elapsed_hours < silence_hours:
            continue

        if not db.claim_silence_notice(int(row["chat_id"]), today):
            continue

        try:
            await application.bot.send_message(
                chat_id=int(row["chat_id"]),
                text=random.choice(SILENCE_MESSAGES),
            )
            db.add_history(
                f"SILENCIO: Pecos habló en {row['title']} tras {elapsed_hours:.1f} h."
            )
        except TelegramError as exc:
            log.warning("No se pudo romper el silencio en %s: %s", row["chat_id"], exc)


async def daily_loop(application: Application) -> None:
    while True:
        try:
            now = datetime.now(BOT_TZ)
            await check_group_silence(application)

            if db.is_true("daily_enabled"):
                daily_time = db.get_setting("daily_time", "09:00")
                today = now.strftime("%Y-%m-%d")
                last_sent = db.get_setting("last_daily_sent_date", "")

                if now.strftime("%H:%M") == daily_time and last_sent != today:
                    text = db.get_setting("daily_message")
                    groups = db.list_groups()

                    sent = 0
                    for row in groups:
                        try:
                            await application.bot.send_message(
                                chat_id=int(row["chat_id"]),
                                text=text,
                            )
                            sent += 1
                        except Forbidden:
                            log.warning("Sin acceso al grupo %s", row["chat_id"])
                        except TelegramError as exc:
                            log.warning("No se pudo enviar mensaje diario a %s: %s", row["chat_id"], exc)

                    db.set_setting("last_daily_sent_date", today)
                    db.add_history(f"MENSAJE DIARIO enviado a {sent} grupo(s).")

        except asyncio.CancelledError:
            raise
        except Exception as exc:
            log.exception("Error en mensaje diario")
            db.add_history(f"ERROR mensaje diario: {exc}")

        await asyncio.sleep(20)


async def post_init(application: Application) -> None:
    # Limpiar comandos previos que pudo haber dejado la versión C#.
    with contextlib.suppress(TelegramError):
        await application.bot.delete_my_commands()

    private_commands = [
        BotCommand("start", "Abrir el menú de Pecos"),
        BotCommand("id", "Ver mi Telegram User ID"),
    ]

    group_commands = [
        BotCommand("encuesta", "Crear una encuesta rápida"),
        BotCommand("recordar", "Guardar un recuerdo del grupo"),
        BotCommand("recuerdos", "Ver recuerdos del grupo"),
        BotCommand("olvidar", "Borrar un recuerdo propio por ID"),
        BotCommand("pecos", "Llamar a Pecos"),
        BotCommand("consejo", "Pedir un consejo a Pecos"),
        BotCommand("frase", "Frase de Pecos"),
        BotCommand("excusa", "Generar una excusa"),
        BotCommand("pronostico", "Pronóstico de Pecos"),
    ]
    await application.bot.set_my_commands(
        private_commands,
        scope=BotCommandScopeAllPrivateChats(),
    )


    await application.bot.set_my_commands(
        group_commands,
        scope=BotCommandScopeAllGroupChats(),
    )

    if ADMIN_USER_IDS:
        admin_commands = [
            BotCommand("start", "Abrir el menú de Pecos"),
            BotCommand("id", "Ver mi Telegram User ID"),
            BotCommand("config", "Abrir configuración privada"),
            BotCommand("cancel", "Cancelar una operación"),
        ]

        for admin_user_id in sorted(ADMIN_USER_IDS):
            await application.bot.set_my_commands(
                admin_commands,
                scope=BotCommandScopeChat(admin_user_id),
            )
            with contextlib.suppress(TelegramError):
                await application.bot.set_chat_menu_button(
                    chat_id=admin_user_id,
                    menu_button=MenuButtonCommands(),
                )

    application.bot_data["daily_task"] = asyncio.create_task(daily_loop(application))

    me = await application.bot.get_me()
    log.info(
        "%s %s conectado como @%s | Admin IDs: %s | Zona: %s | DB: %s | API: %s",
        APP_NAME,
        VERSION,
        me.username,
        ",".join(str(x) for x in sorted(ADMIN_USER_IDS)) if ADMIN_USER_IDS else "NO CONFIGURADOS",
        TIMEZONE_NAME,
        DB_PATH,
        "LOCAL" if LOCAL_BOT_API else "PUBLICA",
    )


async def post_shutdown(application: Application) -> None:
    task = application.bot_data.get("daily_task")
    if task:
        task.cancel()
        with contextlib.suppress(asyncio.CancelledError):
            await task


async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    log.exception("Error no controlado", exc_info=context.error)
    try:
        db.add_history(f"ERROR GENERAL: {context.error}")
    except Exception:
        pass


def build_application() -> Application:
    if not BOT_TOKEN:
        raise RuntimeError(
            "Falta BOT_TOKEN. Configúralo como variable de entorno en Railway."
        )

    builder = Application.builder().token(BOT_TOKEN)

    if LOCAL_BOT_API:
        builder = (
            builder
            .base_url(f"{LOCAL_BOT_API_URL}/bot")
            .base_file_url(f"{LOCAL_BOT_API_URL}/file/bot")
            .local_mode(True)
        )

        log.info(
            "Telegram Bot API local activada en %s",
            LOCAL_BOT_API_URL,
        )

    app = (
        builder
        .post_init(post_init)
        .post_shutdown(post_shutdown)
        .build()
    )

    # Comandos.
    app.add_handler(CommandHandler("start", command_start), group=0)
    app.add_handler(CommandHandler("id", command_id), group=0)
    app.add_handler(CommandHandler("config", command_config), group=0)
    app.add_handler(CommandHandler("cancel", command_cancel), group=0)
    app.add_handler(CommandHandler("encuesta", command_poll), group=0)
    app.add_handler(CommandHandler("recordar", command_remember), group=0)
    app.add_handler(CommandHandler("recuerdos", command_memories), group=0)
    app.add_handler(CommandHandler("olvidar", command_forget), group=0)
    app.add_handler(CommandHandler("pecos", command_pecos), group=0)
    app.add_handler(CommandHandler("consejo", command_advice), group=0)
    app.add_handler(CommandHandler("frase", command_phrase), group=0)
    app.add_handler(CommandHandler("excusa", command_excuse), group=0)
    app.add_handler(CommandHandler("pronostico", command_forecast), group=0)

    # Botones.
    app.add_handler(CallbackQueryHandler(callback_router), group=0)

    # Todo mensaje restante, incluidos captions y edited_message.
    app.add_handler(MessageHandler(filters.ALL, on_message), group=1)

    app.add_error_handler(error_handler)
    return app


def main() -> None:
    app = build_application()
    log.info("Iniciando Pecos mediante long polling...")
    app.run_polling(
        allowed_updates=Update.ALL_TYPES,
        drop_pending_updates=False,
    )


if __name__ == "__main__":
    main()
