#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Pecos Paul Kele Bot - versión Python para hosting 24/7 (Pella)
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
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

from telegram import (
    BotCommand,
    BotCommandScopeAllPrivateChats,
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
VERSION = "1.5.0-special-daily-persistent"
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
log = logging.getLogger("pecos")

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

            CREATE TABLE IF NOT EXISTS daily_user_events (
                event_key TEXT NOT NULL,
                user_id INTEGER NOT NULL,
                local_date TEXT NOT NULL,
                username TEXT NOT NULL DEFAULT '',
                created_at TEXT NOT NULL,
                PRIMARY KEY(event_key, user_id, local_date)
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

    def duplicate_counts(self) -> tuple[int, int]:
        with self.lock:
            unique_count = self.conn.execute(
                "SELECT COUNT(*) AS n FROM file_unique_ids"
            ).fetchone()["n"]
            hash_count = self.conn.execute(
                "SELECT COUNT(*) AS n FROM file_hashes"
            ).fetchone()["n"]
        return int(unique_count), int(hash_count)

    def clear_duplicates(self) -> tuple[int, int]:
        unique_count, hash_count = self.duplicate_counts()
        with self.lock:
            self.conn.execute("DELETE FROM file_unique_ids")
            self.conn.execute("DELETE FROM file_hashes")
            self.conn.commit()
        return unique_count, hash_count

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
        await query.message.reply_text(
            "ℹ️ Duplicados en Pella\n\n"
            "• Todos los tamaños: Pecos compara FileUniqueId de Telegram.\n"
            "• Hasta 20 MB: además descarga el archivo y calcula SHA-256 real.\n"
            "• Más de 20 MB: la Bot API pública no permite descargar el contenido completo; "
            "por eso un archivo grande re-subido con otro FileUniqueId puede no detectarse.\n\n"
            "No usamos solo nombre+tamaño para borrar, porque podría eliminar archivos distintos."
        )
        return


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
    info = media_info(message)
    if not info:
        return False

    chat_id = message.chat_id
    message_id = message.message_id
    unique_id = info["file_unique_id"]
    file_id = info["file_id"]
    file_size = info["file_size"]

    try:
        if unique_id:
            if db.unique_file_seen(chat_id, unique_id, message_id):
                try:
                    await context.bot.delete_message(chat_id=chat_id, message_id=message_id)
                    await context.bot.send_message(
                        chat_id=chat_id,
                        text="🤠 Easy, partner... ese archivo ya pasó por aquí. Pecos tiene buena memoria. 📂👀\n\nEl duplicado fue retirado.",
                    )
                    db.add_history(
                        f"DUPLICADO eliminado por FileUniqueId en chat {chat_id}: {info['file_name'] or 'archivo'}"
                    )
                    return True
                except TelegramError as exc:
                    log.warning("Duplicado detectado, pero no se pudo eliminar: %s", exc)
                    return False

            db.store_unique_file(chat_id, unique_id, message_id)

        # SHA-256 solo si Telegram permite descargarlo por la API pública.
        if file_id and file_size is not None and file_size <= MAX_HASH_DOWNLOAD:
            telegram_file = await context.bot.get_file(file_id)
            data = await telegram_file.download_as_bytearray()
            sha256 = await asyncio.to_thread(
                lambda: hashlib.sha256(bytes(data)).hexdigest()
            )

            if db.hash_seen(chat_id, sha256, message_id):
                try:
                    await context.bot.delete_message(chat_id=chat_id, message_id=message_id)
                    await context.bot.send_message(
                        chat_id=chat_id,
                        text="🤠 Pecos comparó el contenido y confirmó que ese archivo ya estaba aquí. 📂🔎\n\nEl duplicado fue retirado.",
                    )
                    db.add_history(
                        f"DUPLICADO eliminado por SHA-256 en chat {chat_id}: {info['file_name'] or 'archivo'}"
                    )
                    return True
                except TelegramError as exc:
                    log.warning("SHA-256 duplicado detectado, pero no se pudo eliminar: %s", exc)
                    return False

            db.store_hash(chat_id, sha256, message_id)

        return False

    except TelegramError as exc:
        log.warning("No se pudo comprobar duplicado: %s", exc)
        db.add_history(f"ERROR duplicados: {exc}")
        return False
    except Exception as exc:
        log.exception("Error inesperado comprobando duplicado")
        db.add_history(f"ERROR duplicados: {exc}")
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

    if user and user.is_bot:
        return

    # Registrar solo grupos para el mensaje diario.
    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        db.register_group(chat)

    # Si el administrador está escribiendo un dato solicitado por el menú.
    if await handle_admin_text(update, context):
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

    if await handle_identity(message, context):
        return

    await handle_social(message)


async def daily_loop(application: Application) -> None:
    while True:
        try:
            now = datetime.now(BOT_TZ)
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
    await application.bot.set_my_commands(
        private_commands,
        scope=BotCommandScopeAllPrivateChats(),
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
        "%s %s conectado como @%s | Admin IDs: %s | Zona: %s | DB: %s",
        APP_NAME,
        VERSION,
        me.username,
        ",".join(str(x) for x in sorted(ADMIN_USER_IDS)) if ADMIN_USER_IDS else "NO CONFIGURADOS",
        TIMEZONE_NAME,
        DB_PATH,
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
            "Falta BOT_TOKEN. Configura el token de BotFather como variable de entorno en Pella."
        )

    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .post_init(post_init)
        .post_shutdown(post_shutdown)
        .build()
    )

    # Comandos.
    app.add_handler(CommandHandler("start", command_start), group=0)
    app.add_handler(CommandHandler("id", command_id), group=0)
    app.add_handler(CommandHandler("config", command_config), group=0)
    app.add_handler(CommandHandler("cancel", command_cancel), group=0)

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
