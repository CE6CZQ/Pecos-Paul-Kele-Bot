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
    ALLOWED_GROUP_IDS      Grupos donde Pecos puede operar, separados por comas
"""

from __future__ import annotations

import asyncio
import contextlib
import difflib
import hashlib
import io
from difflib import SequenceMatcher
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
    BotCommandScopeChatMember,
    Chat,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    MenuButtonCommands,
    Message,
    Update,
)
from telegram.constants import ChatType
from telegram.error import BadRequest, Forbidden, NetworkError, TelegramError
from telegram.ext import (
    Application,
    ApplicationHandlerStop,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    TypeHandler,
    filters,
)


APP_NAME = "Pecos Paul Kele"
VERSION = "2.8.10-directed-thanks"
HISTORY_SOURCE_CHAT_ID = int(os.getenv("HISTORY_SOURCE_CHAT_ID", "-1001775566217"))
HISTORY_MEMORY_GROUP_IDS = {
    int(x.strip()) for x in os.getenv("HISTORY_MEMORY_GROUP_IDS", "-1001775566217").split(",")
    if x.strip()
}
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

TELEGRAM_FILES_DIR = Path(
    os.getenv("TELEGRAM_FILES_DIR", "/tmp/telegram-bot-api-files").strip()
    or "/tmp/telegram-bot-api-files"
).resolve()

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


def _load_owner_user_ids() -> set[int]:
    """
    Propietarios de Pecos con privilegios especiales.

    Si OWNER_USER_IDS / OWNER_USER_ID no están configurados y existe exactamente
    un ADMIN_USER_IDS, se asume que ese único administrador actual es el creador.
    Así esta versión funciona sin exigir cambios inmediatos en Railway.
    """
    raw = os.getenv("OWNER_USER_IDS", "").strip()
    if not raw:
        raw = os.getenv("OWNER_USER_ID", "").strip()

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

    if result:
        return result

    if len(ADMIN_USER_IDS) == 1:
        return set(ADMIN_USER_IDS)

    return set()


OWNER_USER_IDS = _load_owner_user_ids()


def _load_allowed_group_ids() -> set[int]:
    """
    Grupos autorizados para Pecos.

    Por seguridad, si Railway todavía no tiene ALLOWED_GROUP_IDS, esta versión
    permite únicamente los dos grupos definidos para el proyecto:
    - Pruebas
    - YO REPARO RADIOS
    """
    raw = os.getenv(
        "ALLOWED_GROUP_IDS",
        "-1004469972566,-1001775566217",
    ).strip()

    result: set[int] = set()
    for part in raw.split(","):
        part = part.strip()
        if not part:
            continue
        try:
            value = int(part)
        except ValueError as exc:
            raise RuntimeError(
                "ALLOWED_GROUP_IDS debe contener chat_id numéricos separados por comas."
            ) from exc
        if value >= 0:
            raise RuntimeError(
                "Cada valor de ALLOWED_GROUP_IDS debe ser un chat_id negativo de grupo/supergrupo."
            )
        result.add(value)

    if not result:
        raise RuntimeError("ALLOWED_GROUP_IDS no puede quedar vacío.")

    return result


ALLOWED_GROUP_IDS = _load_allowed_group_ids()

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

# Ventana breve para detectar si un usuario recién ingresado pregunta
# inmediatamente sin haber tenido tiempo razonable de revisar reglas/archivos.
NEW_MEMBER_RULE_WINDOW_SECONDS = 30
NEW_MEMBER_JOINED_AT: dict[tuple[int, int], float] = {}

# Evita que Pecos responda de forma contextual demasiado seguido al mismo tema.
RECENT_CONTEXTUAL_RESPONSES: dict[tuple[int, str], float] = {}
CONTEXTUAL_RESPONSE_COOLDOWN_SECONDS = 180

KNOWN_HELPFUL_KEYWORDS = (
    "aqui esta",
    "aqui está",
    "te dejo",
    "les dejo",
    "adjunto",
    "solucion",
    "solución",
    "manual",
    "firmware",
    "driver",
    "programa",
    "software",
    "cps",
    "codeplug",
)

ARCHIVE_EXTENSIONS = (".rar", ".zip", ".7z")

# Fase 3: archivo inteligente.
ARCHIVE_SEARCH_MAX_RESULTS = 6
ARCHIVE_AUTO_COOLDOWN_SECONDS = 600
ARCHIVE_DETECTIVE_SIMILARITY = 0.72
RECENT_ARCHIVE_HINTS: dict[tuple[int, str], float] = {}

ARCHIVE_SEARCH_STOPWORDS = {
    "pecos", "peco", "paul", "kele", "busca", "buscar", "buscame", "buscame",
    "encuentra", "encuentrame", "tenemos", "tienes", "tienen", "hay", "algo",
    "archivo", "archivos", "para", "por", "favor", "favor", "del", "de", "la",
    "el", "los", "las", "un", "una", "unos", "unas", "que", "qué", "quiero",
    "necesito", "necesitamos", "sobre", "relacionado", "relacionados",
    "algun", "alguno", "alguna", "algunos", "algunas", "me", "puedes", "puede",
    "podrias", "podría", "ver", "si", "existe", "salta", "saltar", "quita",
    "quitar", "elimina", "eliminar", "saca", "sacar", "necesita", "necesitan",
}

TECHNICAL_ARCHIVE_WORDS = {
    "cps", "dmr", "firmware", "codeplug", "hytera", "motorola", "kenwood",
    "icom", "baofeng", "anytone", "vertex", "yaesu", "radioddity", "retevis",
    "programming", "programacion", "driver", "drivers", "software", "programa",
    "programas", "password", "clave", "contrasena", "unlock", "desbloqueo",
    "bypass", "crack", "patch", "patched", "tuner", "tool", "utility", "flash",
    "upgrade", "downgrade", "recovery", "programmer", "programador", "rss",
    "management",
}

# Familias/plataformas de software que no necesariamente contienen números.
# Se mantienen separadas de los modelos para no confundir, por ejemplo, APX con
# MOTOTRBO solo porque ambos usan CPS.
ARCHIVE_FAMILY_ALIASES: dict[str, set[str]] = {
    "mototrbo": {"mototrbo", "motortrbo", "motorbo", "mototurbo", "motrbo"},
    "apx": {"apx"},
    "astro25": {"astro25", "astro 25", "astro-25"},
    "tetra": {"tetra"},
    "nxdn": {"nxdn"},
}

# Alias semánticos y errores frecuentes de escritura. Solo se usan para entender
# mejor la consulta; nunca autorizan por sí solos a mezclar familias incompatibles.
ARCHIVE_TERM_ALIASES: dict[str, set[str]] = {
    "software": {"software", "sofware", "softwre", "softwar"},
    "firmware": {"firmware", "firware", "firmwere"},
    "password": {"password", "pasword", "passwrod", "contrasena", "clave", "pass"},
    "crack": {"crack", "cracked", "patch", "patched"},
    "codeplug": {"codeplug", "codeplg", "code plug"},
    "driver": {"driver", "drivers", "drv"},
}

ARCHIVE_GENERIC_RESOURCE_TERMS = {
    "software", "programa", "programas", "cps", "firmware", "driver", "drivers",
    "password", "clave", "contrasena", "unlock", "desbloqueo", "bypass", "crack",
    "patch", "patched", "codeplug", "flash", "tuner", "tool", "utility",
    "programming", "programacion", "programmer", "programador", "recovery",
    "upgrade", "downgrade", "management", "rss",
}


# Fase 2: preguntas repetidas + reconocimiento interno de aportes.
QUESTION_LOOKBACK_DAYS = 120
QUESTION_HISTORY_LIMIT = 500
QUESTION_SIMILARITY_THRESHOLD = 0.72
QUESTION_ALERT_COOLDOWN_SECONDS = 240
RECENT_REPEAT_QUESTION_ALERTS: dict[tuple[int, int], float] = {}

QUESTION_STOPWORDS = {
    "a", "al", "algo", "alguien", "alguno", "alguna", "ante", "como", "con",
    "cual", "cuales", "cuando", "de", "del", "donde", "el", "ella", "en", "es",
    "esa", "ese", "esta", "este", "esto", "hay", "la", "las", "lo", "los", "me",
    "mi", "para", "pero", "por", "porque", "puede", "pueden", "que", "quien",
    "se", "si", "sin", "su", "sus", "tengo", "tiene", "tienen", "un", "una",
    "uno", "unos", "unas", "y", "ya", "yo", "favor", "sabe", "saben", "ayuda",
    "necesito", "busco", "consulta", "pregunta",
}

REPUTATION_MILESTONES = (3, 7, 12, 20)

REPUTATION_MESSAGES = {
    3: [
        "⭐ Pecos toma nota: {usuario} ya ha dejado varias ayudas útiles por este pueblo. Se agradece, partner.",
        "🤠 Pecos reconoce a {usuario}: ya van varias contribuciones útiles. Buen vecino del territorio.",
        "🌵 {usuario} viene aportando más que cactus al paisaje. Pecos lo tiene presente.",
    ],
    7: [
        "🦅 Pecos lleva la cuenta sin hacer rankings: {usuario} se está convirtiendo en una referencia útil del grupo.",
        "⭐ Sheriff Pecos hace un gesto con el sombrero a {usuario}. Varias ayudas útiles ya llevan su firma.",
        "🤠 {usuario}, Pecos no reparte medallas por cualquier cosa. Pero tus aportes ya se hacen notar por aquí.",
    ],
    12: [
        "🌵 Pecos confirma algo que el pueblo ya sospechaba: {usuario} suele aparecer cuando hace falta una mano.",
        "🦅 Respeto de sheriff para {usuario}. Pecos recuerda quién ayuda cuando el camino se pone complicado.",
        "⭐ {usuario} ya tiene historial de aportes útiles. Pecos no olvida esas cosas.",
    ],
    20: [
        "🤠 Pecos se quita el sombrero ante {usuario}. No hay ranking, pero sí memoria: has ayudado muchas veces a este pueblo.",
        "⭐ Reconocimiento especial del sheriff para {usuario}. A esta altura Pecos ya sabe que cuando apareces, suele venir algo útil contigo.",
        "🦅 {usuario}, Pecos te tiene en la memoria buena del territorio. Gracias por sostener el espíritu de ayuda del grupo.",
    ],
}

REPEATED_QUESTION_MESSAGES = [
    "🌵 {usuario}, esa pregunta ya pasó por este saloon hace poco. Pecos encontró una conversación muy parecida.",
    "🕵️ {usuario}, Pecos revisó sus notas: este asunto ya se habló por aquí recientemente.",
    "🤠 Partner {usuario}, antes de volver a ensillar esa pregunta, Pecos encontró una huella casi idéntica en el historial.",
    "📡 {usuario}, señal conocida. Pecos recuerda una consulta muy parecida en este mismo territorio.",
    "🦅 Pecos vio esta pregunta antes, {usuario}. Te dejo la pista para que no tengamos que recorrer dos veces el mismo desierto.",
    "⭐ Sheriff Pecos reporta coincidencia: {usuario}, este tema ya tuvo una ronda anterior en el grupo.",
]

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


DUPLICATE_QUICK_MESSAGES = [
    "🤠 Easy, partner... Pecos ya vio ese archivo cabalgar por aquí. La segunda copia vuelve al saloon. 🌵",
    "👀 Pecos tiene memoria de sheriff: ese archivo ya pasó por este territorio. Duplicado retirado.",
    "🚨 Houston, tenemos un repetido. Pecos lo reconoció al instante y lo mandó de vuelta. 😎",
    "🦅 Pecos lo vio venir desde lejos... mismo archivo, segundo viaje. Copia retirada.",
    "🌵 Ese archivo intentó volver a entrar al pueblo. Pecos dijo: «una vez basta, partner».",
    "⭐ Sheriff Pecos reporta: archivo conocido, copia detectada y retirada.",
    "😂 Casi pasa otra vez... pero Pecos no nació ayer. Duplicado fuera.",
    "📡 Señal recibida desde los United States: archivo repetido detectado. Pecos se encargó.",
]

DUPLICATE_HASH_MESSAGES = [
    "🕵️ Cambiaste el nombre, pero no engañaste a Pecos: por dentro es exactamente el mismo archivo. 😎",
    "🤠 Nuevo sombrero, mismo cowboy... Pecos revisó los bytes y encontró un duplicado.",
    "🌵 Ese archivo llegó disfrazado con otro nombre, pero Pecos reconoció su huella. Copia retirada.",
    "👀 El nombre decía una cosa, el SHA-256 contó la verdad. Pecos encontró el duplicado.",
    "🎯 Pecos apuntó al contenido, no al nombre. Resultado: duplicado confirmado y retirado.",
    "🦅 Desde lejos parecía distinto; de cerca tenía exactamente la misma huella. Pecos lo retiró.",
    "🚂 Cambió de nombre, pero tomó el mismo tren de bytes. Pecos mandó la copia de regreso.",
    "⭐ Caso cerrado por Sheriff Pecos: mismo contenido, distinto nombre, duplicado eliminado.",
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


NEW_USER_RULE_MESSAGES = [
    "🤠 {usuario}, veo que llegaste preguntando más rápido de lo que Pecos desenfunda. Me parece que te saltaste las reglas del grupo. Échales una mirada y revisa los archivos antes de que tengamos un duelo... y te aviso que Pecos juega de local. 🌵",
    "👀 {usuario}, acabas de entrar y ya vienes con preguntas... Pecos sospecha que las reglas quedaron sin estrenar. Revísalas primero, partner, y date una vuelta por los archivos.",
    "🌵 Easy, partner {usuario}... llevas menos de 30 segundos en el pueblo y ya estás preguntando. Primero revisa las reglas y los archivos del grupo; Pecos estará mirando. 😎",
    "⭐ Sheriff Pecos reportando: {usuario} entró, vio las reglas pasar de largo y fue directo a preguntar. Un vistazo a los archivos primero, partner. Después conversamos. 🤠",
    "🕵️ {usuario}, Pecos hizo las cuentas: recién llegaste y ya apareció una pregunta. Eso huele a reglas sin leer. Busca primero en los archivos... no querrás desafiar al sheriff tan temprano. 🌵",
    "🎯 {usuario}, velocidad impresionante: entrar al grupo y preguntar en menos de 30 segundos. Ahora intenta superar el siguiente desafío: leer las reglas y revisar los archivos. Pecos confía en ti. Más o menos. 😏",
    "🚂 {usuario}, ese tren salió demasiado rápido de la estación. Antes de preguntar, date una vuelta por las reglas y los archivos del grupo. Pecos estará mirando desde el saloon. 🤠",
    "😂 {usuario}, ni Pecos desenfunda tan rápido. Recién llegaste y ya tenemos pregunta. Primero revisa las reglas y los archivos, partner... después evitamos el duelo.",
    "🦅 Pecos vio todo desde arriba, {usuario}: entrada al grupo, cero escala en las reglas y directo a preguntar. Vuelve un par de pasos y revisa los archivos. 🤠",
    "📡 Alerta desde los United States: usuario nuevo preguntando antes de revisar las reglas. {usuario}, busca primero en los archivos si no quieres un duelo con Pecos. Spoiler: Pecos viene entrenando. 😎",
]

DIRECT_PECOS_GREETINGS = [
    "🤠 ¡Saludos, {usuario}! Pecos recibió su saludo fuerte y claro. Gracias por incluirme directamente, partner. 📡",
    "😎 ¡Presente, {usuario}! Esta vez Pecos sí apareció en la lista. Saludo recibido y devuelto. 🤠",
    "📡 ¡Gracias por el saludo, {usuario}! Mención recibida sin interferencias. Pecos también te saluda.",
    "🌵 ¡Saludos, {usuario}! Pecos agradece que se acordaran del sheriff del grupo. 😄",
]

DIRECT_PECOS_MORNING_GREETINGS = [
    "🌞 ¡Buenos días, {usuario}! Pecos recibió el saludo fuerte y claro. Gracias por incluirme, partner. 🤠",
    "☕ ¡Buenos días, {usuario}! Esta vez Pecos sí estaba en la lista. Saludo recibido y café en mano. 😎",
    "📡 ¡Muy buenos días, {usuario}! Mención recibida sin interferencias. Pecos también te saluda.",
]

DIRECT_PECOS_AFTERNOON_GREETINGS = [
    "☀️ ¡Buenas tardes, {usuario}! Pecos recibió su saludo fuerte y claro. Gracias por incluirme. 🤠",
    "📡 ¡Buenas tardes, {usuario}! Esta vez Pecos sí apareció en la lista. Saludo recibido y devuelto.",
    "😎 ¡Muy buenas tardes, {usuario}! Pecos presente y agradecido por la mención, partner.",
]

DIRECT_PECOS_NIGHT_GREETINGS = [
    "🌙 ¡Buenas noches, {usuario}! Pecos recibió el saludo y confirma presencia. Gracias por incluirme. 🤠",
    "⭐ ¡Buenas noches, {usuario}! Esta vez Pecos sí estaba nombrado. Saludo recibido y devuelto.",
    "📡 ¡Muy buenas noches, {usuario}! Mención recibida fuerte y clara. Pecos también te saluda.",
]


PECOS_EXCLUDED_GREETINGS = [
    "🥺 Pecos admite que le dio un poquito de pena quedar fuera del saludo, {usuario}. Pero uno es educado a la antigua: ¡muy buenos días igual! Lo cortés no quita lo valiente. 🤠",
    "😔 Vaya, {usuario}... hoy Pecos quedó expresamente fuera del saludo. Igual devuelve uno con respeto: ¡que tengas muy buen día! Lo cortés no quita lo valiente. 📡",
    "🤠 Pecos escuchó clarito que el saludo era para todos menos para él. Duele un poquito, partner... pero la educación va primero: ¡saludos igualmente! Lo cortés no quita lo valiente.",
    "🌵 Pecos quedó fuera de la lista, {usuario}. Este viejo sheriff se pone triste un segundo y después hace lo correcto: ¡muy buenos días igual! Lo cortés no quita lo valiente. 😄",
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
    "👀 Pecos presente. Te leo.",
    "🌵 Aquí anda Pecos, firme en el territorio.",
    "📡 Señal recibida. Pecos está en línea.",
    "😎 Dime, partner. Pecos te lee.",
]


PECOS_ATTENTIVE_MESSAGES = [
    "👀 Claro, {usuario}. Pecos está pendiente de todo... alguien tiene que cuidar este pueblo. 🤠",
    "🤠 Así es, partner {usuario}. Mientras ustedes conversan, Pecos tiene el radar encendido.",
    "🌵 Pecos está pendiente de todo, {usuario}. Hasta los cactus están bajo vigilancia. 😎",
    "📡 Confirmado, {usuario}. Radar de Pecos activo desde los United States.",
    "🦅 Pecos ve desde lejos, {usuario}. Aquí cuesta que algo pase desapercibido.",
    "⭐ Sheriff Pecos de turno, {usuario}. Nada grave se mueve por el pueblo sin que levante una ceja.",
    "😂 {usuario}, alguien tiene que estar atento... y por lo visto me tocó a mí.",
    "👀 Pendiente de todo, {usuario}. Pecos no parpadea... ventajas de ser bot. 🤠",
    "🤨 {usuario}, Pecos no dice que lo vea todo... pero casi todo termina pasando por su radar.",
    "🚨 Atención, {usuario}: Pecos confirma que sigue despierto, vigilando y ligeramente desconfiado.",
    "🎯 Así es, {usuario}. Pecos tiene un ojo en el chat y el otro buscando problemas antes de que aparezcan.",
    "🛂 {usuario}, control fronterizo de Pecos activo. Aquí hasta los mensajes hacen fila para entrar.",
    "🚂 Pecos sigue la vía completa, {usuario}. Si algo raro pasa por aquí, tarde o temprano lo ve.",
    "🕵️ {usuario}, oficialmente Pecos no espía... digamos que observa con muchísimo entusiasmo. 😎",
    "🎬 {usuario}, Pecos está pendiente incluso de las escenas que todavía no empiezan.",
    "🔔 Ding ding, {usuario}. Pecos confirma: vigilancia activa y sombrero bien puesto.",
    "🤖 {usuario}, sistema Pecos operativo: ojos abiertos, radar encendido y humor disponible.",
    "🦅 Desde arriba todo se ve mejor, {usuario}. Pecos mantiene el territorio bajo control.",
    "🌵 {usuario}, por aquí hasta un cactus moviéndose raro llama la atención de Pecos.",
    "😎 Correcto, {usuario}. Pecos está pendiente de todo... y de lo que parece que no importa también.",
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

MELERIX_FUN_MESSAGES = [
    "🤠 Melerix fue mencionado. Pecos ajusta el sombrero y revisa que el pueblo siga en pie.",
    "👀 ¿Melerix? Pecos no acusa a nadie... pero ya está mirando alrededor.",
    "🌵 Nombre detectado: Melerix. Los cactus han sido puestos en alerta preventiva.",
    "📡 Reporte desde los United States: Melerix apareció en frecuencia. Pecos mantiene vigilancia.",
    "😂 Otra vez salió Melerix en la conversación. Pecos sospecha que esto viene con historia incluida.",
    "⭐ Sheriff Pecos registra oficialmente una mención a Melerix. Continúen bajo su propio riesgo.",
    "🦅 Pecos escuchó ‘Melerix’ desde lejos. Algo me dice que el siguiente capítulo viene entretenido.",
    "😎 Melerix detectado. Pecos ya puso música de duelo por si acaso.",
    "🚨 Código Melerix activado. Nadie entre en pánico... todavía.",
    "🌵 Cada vez que alguien dice Melerix, un cactus en Texas se pone nervioso.",
    "🤨 Pecos oyó Melerix y levantó una ceja. Eso normalmente significa que viene anécdota.",
    "🎯 Melerix en el radar. Pecos no dispara conclusiones... pero tampoco guarda el revólver.",
    "🚂 Melerix volvió a pasar por la estación. Pecos espera que esta vez traiga boleto.",
    "🕵️ Melerix fue nombrado. Pecos abre expediente, sirve café y espera los detalles.",
    "🔔 Ding ding... mención a Melerix detectada. Pecos declara oficialmente iniciado el episodio.",
    "🤖 Sistema Pecos: palabra Melerix recibida. Humor automático cargado al 100%.",
    "🎬 Melerix apareció en el guion. Pecos pide palomitas antes de continuar.",
    "🛂 Control fronterizo: Melerix acaba de cruzar la conversación. Documentos, por favor. 😎",
    "🦗 Dijeron Melerix y hasta los grillos dejaron de cantar para escuchar.",
    "☕ Melerix fue mencionado. Pecos recomienda café; estas historias rara vez son cortas.",
    "🐎 Melerix entró cabalgando en la conversación. Pecos todavía no sabe si saludar o cubrirse.",
    "📻 Señal clara y fuerte: Melerix. Pecos confirma recepción y ligera preocupación humorística.",
    "🌵 Pecos no sabe qué hizo Melerix esta vez, pero el cactus ya pidió testigos.",
    "😏 Melerix... ese nombre tiene más temporadas que una serie. Pecos sigue atento.",
    "⭐ Melerix mencionado. Pecos anota: ‘posible material para leyenda del pueblo’.",
    "🦅 Si Melerix fuera una frecuencia, Pecos ya la tendría guardada en favoritos.",
    "🤠 Pecos escuchó Melerix. Nadie dijo ‘problema’, pero el sombrero se acomodó solo.",
    "😂 Melerix en conversación: Pecos activa protocolo científico de mirar y esperar qué pasa.",
    "📡 Mensaje recibido: Melerix. Respuesta de Pecos: esto promete.",
    "🌵 Melerix otra vez en boca del pueblo. Pecos oficialmente se declara curioso.",
]


XERAX_USERNAME = "xerax"

XERAX_FUN_MESSAGES = [
    "🤖 Apareció XeraX. Escondan los computadores antes de que los convierta en nodos para minar Bitcoin.",
    "⚠️ Alerta XeraX: revisen el Administrador de tareas; capaz ya tienen 14 bots trabajando para él.",
    "⛏️ XeraX entró al chat. Pecos recomienda vigilar la GPU… por si empieza a minar mientras ustedes conversan.",
    "🪙 Cada vez que XeraX escribe, algún procesador del pueblo siente un escalofrío misterioso.",
    "🤠 Pecos informa: XeraX está conectado. No acepten nada llamado actualizacion_definitiva_final.exe.",
    "🚨 Código XeraX activado. Protejan routers, notebooks y cualquier cosa que tenga más de 512 MB de RAM.",
    "🤖 XeraX dice ‘hola’ y tres bots aparecen misteriosamente en algún servidor. Coincidencia, seguramente.",
    "💻 Si tu ventilador empezó a sonar justo cuando apareció XeraX… Pecos no quiere sacar conclusiones.",
    "🪙 XeraX presente. En algún lugar acaba de aparecer una fracción microscópica de Bitcoin.",
    "🌵 Pecos recomienda no dejar a XeraX solo con un VPS, Docker y una tarjeta de crédito.",
    "📡 XeraX conectado. El tráfico de red subió misteriosamente. Pecos declara que debe ser el clima.",
    "😂 XeraX otra vez… escondan las Raspberry Pi.",
    "🤖 Dicen que XeraX no crea bots. Los bots simplemente aparecen cuando él llega.",
    "🖥️ XeraX entró al grupo y algún proveedor cloud acaba de preparar una factura sin explicación.",
    "⛏️ Atención: si XeraX pregunta cuántos núcleos tiene tu procesador, Pecos recomienda cambiar de tema.",
    "🪙 Pecos revisó la blockchain. XeraX estaba ‘haciendo pruebas’, aparentemente.",
    "🚜 XeraX no mina Bitcoin con GPUs. Dicen las malas lenguas que mina con todo lo que tenga enchufe.",
    "🔌 Desenchufen las calculadoras. XeraX ya debe estar pensando cuántos hashes por segundo dan.",
    "👀 XeraX apareció. Pecos está contando los bots antes y después de su llegada.",
    "🤠 Tranquilos, XeraX solo vino a conversar… eso dijo también la última botnet imaginaria del pueblo.",
    "📟 Si XeraX te pregunta tu IP, Pecos recomienda responder: ‘pregúntale al sheriff’.",
    "🖥️ XeraX mirando un servidor: ‘qué bonito equipo… sería una pena dejarlo sin minar’.",
    "🤖 El problema no es que XeraX tenga bots. El problema es que, según Pecos, probablemente los bots tengan a XeraX.",
    "🌐 XeraX conectado. Internet del pueblo acaba de pedir vacaciones.",
    "🪙 Pecos detectó actividad sospechosamente absurda: alguien intentó minar Bitcoin con la cafetera.",
    "🔥 Si el PC empieza a calentarse después de que XeraX escribe, Pecos recomienda abrir una ventana y no acusar al clima.",
    "🤖 XeraX no necesita agregar bots al grupo. En las leyendas del pueblo llegan solos cuando detectan a su creador.",
    "🧮 XeraX vio una calculadora Casio y preguntó cuántos hashes por segundo daba. Pecos cambió de vereda.",
    "📡 XeraX apareció en frecuencia. Los servidores de medio mundo, según las malas lenguas, se pusieron nerviosos.",
    "🌵 Pecos tiene una regla sencilla: si aparece XeraX, revise CPU, RAM y que la billetera siga donde estaba.",
    "🧠 Dicen las malas lenguas que XeraX tiene una IA trabajando 24/7. Pecos prefiere no preguntar en qué.",
    "🤖 La IA de XeraX acaba de conectarse. Oficialmente está aprendiendo. Extraoficialmente… mejor no mirar los logs.",
    "👀 XeraX dice que su IA solo responde preguntas. Pecos vio el consumo de CPU y mantiene sus reservas humorísticas.",
    "🤠 Dicen las malas lenguas que XeraX entrenó una IA para ahorrar tiempo. Ahora nadie sabe qué hace con todo ese tiempo libre.",
    "🤖 La IA de XeraX pidió acceso de administrador. Pecos escondió inmediatamente las llaves del servidor.",
    "🪙 XeraX asegura que su IA no mina Bitcoin. Pecos responde: ‘claro, claro…’.",
    "🌐 Dicen que la IA de XeraX empezó como asistente personal y terminó preguntando por puertos abiertos.",
    "🧠 Pecos investigó a la IA de XeraX. La IA investigó a Pecos de vuelta. Investigación cancelada.",
    "😂 XeraX dice: ‘es solo una IA de pruebas’. Pecos pregunta por qué entonces necesita tantos núcleos y tres VPS.",
    "🤖 Dicen las malas lenguas que la IA de XeraX ya tiene empleados. Ninguno sabe que trabaja para ella.",
    "📡 La IA de XeraX detectó una radio con USB. Pecos recomienda esconder el cable antes de que le instale Docker.",
    "🖥️ XeraX le pidió a su IA que optimizara el servidor. Ahora el servidor responde únicamente en hexadecimal.",
    "🚨 Alerta Pecos: XeraX mencionó ‘automatizar una cosita’. La última vez aparecieron nueve bots en la leyenda.",
    "🧠 La IA de XeraX está ‘haciendo cálculos’. Curiosamente, hasta la GPU del vecino parece cansada.",
    "👀 Dicen que XeraX tiene una IA tan avanzada que cuando preguntas qué está haciendo responde: ‘no te preocupes’.",
    "🌵 XeraX afirma que su IA es completamente inofensiva. Pecos también afirma que sabe bailar salsa.",
    "🪙 Rumor del pueblo: XeraX le enseñó blockchain a su IA. Desde entonces desaparecen watts misteriosamente.",
    "📟 La IA de XeraX encontró un XPR7550. Cinco minutos después preguntó si se podía overclockear.",
    "🤠 Pecos tiene dos reglas: no apostar con tahúres y no darle acceso root a la IA de XeraX.",
    "🧠 Dicen las malas lenguas que la IA de XeraX ya escribió su propio bot. XeraX todavía cree que él manda.",
    "🤖 XeraX: ‘la IA está bajo control’. IA de XeraX: ‘confirmo’. Pecos se retira lentamente.",
    "🔌 Si XeraX dice ‘déjame probar una IA’, desenchufen todo lo que tenga procesador. Por tradición, nada más.",
    "😂 La IA de XeraX pidió vacaciones. Nadie sabe de qué trabajo se está recuperando.",
    "🌐 XeraX conectó su IA al servidor ‘solo para probar’. Pecos ya está mirando la factura del cloud.",
    "📡 Dicen que la IA de XeraX escucha hasta frecuencias que todavía no fueron inventadas.",
    "🪙 Pecos preguntó si la IA de XeraX mina Bitcoin. Respuesta: ‘ese término ya está obsoleto’. Eso preocupó más al sheriff.",
    "🤖 Hay rumores de que XeraX tiene una IA haciendo cosas turbias. Pecos aclara: turbias, pero con excelente documentación.",
    "🧠 La IA de XeraX no hace nada ilegal. Según la leyenda, solo hace cosas que todavía no tienen nombre.",
    "🤠 Pecos acaba de ver a XeraX escribir ‘pip install’. Que Dios encuentre al servidor confesado.",
    "📻 XeraX le mostró un CPS a su IA. Ahora la IA quiere privilegios de administrador en el repetidor.",
    "📡 Dicen que la IA de XeraX puede programar un Motorola mirando solamente la antena.",
    "🤖 XeraX conectó una radio al PC. La IA preguntó inmediatamente: ‘¿esto también puede minar?’.",
    "📻 Pecos vio a la IA de XeraX analizando un firmware. Desde entonces el firmware analiza a Pecos.",
    "🌵 XeraX dijo ‘solo voy a automatizar la programación de radios’. Pecos ya está preparando un refugio.",
]

SILENCE_MESSAGES = [
    "🤠 ¿Qué pasó por aquí? Pecos escucha hasta los grillos. Ya van {horas} horas de silencio.",
    "🌵 Tanto silencio que Pecos ya empezó a conversar con un cactus. Marcador actual: {horas} horas.",
    "👀 ¿Hay alguien? Pecos revisó la señal dos veces. Este pueblo lleva {horas} horas en modo fantasma.",
    "📡 Control de radio: silencio absoluto. Pecos reportando desde los United States tras {horas} horas sin movimiento.",
    "🦗 Cri... cri... Pecos confirma presencia de grillos en el grupo. Silencio acumulado: {horas} horas.",
    "⭐ Sheriff Pecos informa: {horas} horas de calma. O todos están ocupados... o los cactus tomaron el control.",
    "🦅 Desde arriba solo se ven huellas viejas. Pecos calcula {horas} horas sin mensajes.",
    "😎 Todo tranquilo por aquí... demasiado tranquilo. Pecos marca {horas} horas de silencio oficial.",
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

COLLECTIVE_FAREWELLS = [
    "🤠 Buenas noches, {usuario}. Pecos queda de guardia mientras el pueblo descansa.",
    "🌙 Que descanses, {usuario}. Pecos baja el volumen de la radio, pero deja una oreja en la frecuencia.",
    "👋 Hasta la próxima, {usuario}. Pecos cuida el saloon hasta que vuelva la tropa.",
    "⭐ Buen descanso, {usuario}. Mañana seguimos desenredando cables y misterios.",
    "🦅 Nos vemos, {usuario}. Pecos apaga una luz, pero no pierde de vista el territorio.",
    "😎 Bye, {usuario}. Que descanse el pueblo; Pecos se queda haciendo la última ronda.",
]

SLEEP_FAREWELLS = [
    "😴 Puede ser, {usuario}. Pecos cuelga el sombrero un rato… pero deja una oreja en la frecuencia. 😂",
    "🌙 Buena idea, {usuario}. Pecos apaga la lámpara del saloon… por ahora. 😂",
    "🤠 Está bien, partner {usuario}. Si preguntan por Pecos, diles que está calibrando los párpados. 😴",
    "🌵 Pecos ya iba a dormir, {usuario}; alguien tiene que vigilar que no conviertan un VHF en UHF mientras descansa. 😂",
]


VETERAN_GREETINGS = [
    "🤠 ¡Hola, {usuario}! Pecos no olvida que ya has echado una mano más de una vez por aquí.",
    "⭐ Buen verte, {usuario}. Pecos te tiene fichado como parte útil del pueblo.",
    "🦅 {usuario}, Pecos te saluda con respeto de veterano. Ya has dejado varias huellas útiles por aquí.",
    "😎 ¡Buenas, {usuario}! Pecos recuerda que no vienes a mirar cactus nomás; ya has aportado al territorio.",
    "🌵 {usuario}, Pecos te ubica. Cuando apareces, algo útil suele caer por el pueblo.",
]

CONTEXTUAL_FRUSTRATION_MESSAGES = [
    "🤠 Tranquilo, partner. Antes de rendirse, Pecos recomienda respirar, revisar dos veces y disparar una sola.",
    "🌵 Cuando algo no funciona, a veces el cactus no está en el equipo sino en el paso que se saltó. Pecos lo dice con cariño.",
    "👀 Pecos ha visto problemas más feos que ese. No lo des por perdido todavía.",
    "😎 Si todavía no funciona, no es el final. Es solo la parte del guion donde Pecos levanta una ceja y sigue buscando.",
    "📡 Calma en la frecuencia, partner. Pecos sugiere revisar nombre, versión y conexión antes del duelo final.",
]

CONTEXTUAL_SUCCESS_MESSAGES = [
    "🦅 Pecos toma nota: asunto resuelto. El pueblo puede seguir respirando.",
    "🤠 Bien ahí. Pecos sospechaba que ese cactus se podía esquivar.",
    "😎 Caso cerrado. Pecos archiva el drama y deja abierta la cantina.",
    "⭐ Excelente. Pecos marca el expediente como resuelto y guarda el sombrero.",
    "🌵 Pecos aprueba ese final: menos drama, más solución.",
]

CONTEXTUAL_THANKS_MESSAGES = [
    "🤠 De nada, partner... Pecos vive para estas pequeñas victorias del pueblo.",
    "😎 Pecos recibe el agradecimiento y lo guarda junto al sombrero bueno.",
    "🦅 Agradecimiento recibido. Pecos sigue sobrevolando por si aparece otro cactus.",
    "🌵 Pecos agradece el gesto. No todo en este territorio son problemas y grillos.",
]

REPEAT_DUPLICATE_WARNINGS = [
    "🤨 Pecos toma nota: ya no es la primera copia que te retiro por aquí, partner.",
    "🌵 Pecos recuerda que conviene mirar el corral antes de subir otro archivo. Ya llevas más de una repetición.",
    "⭐ Sheriff Pecos marca reincidencia leve: este no es tu primer duplicado en el pueblo.",
]

REPEAT_RULE_WARNINGS = [
    "🤠 Pecos ya te había visto llegar preguntando sin revisar el terreno. Mejor revisar reglas y archivos primero, partner.",
    "🌵 Reincidencia leve detectada: Pecos insiste en que primero se revisa el pueblo y después se desenfunda la pregunta.",
    "🦅 Pecos no olvida estas entradas rápidas: antes de preguntar, primero mira reglas y archivos.",
]

REPEAT_RESTRICTED_WARNINGS = [
    "🤨 Pecos recuerda que no es la primera vez que te cruza por la puerta equivocada, partner.",
    "🌵 Reincidencia leve: Pecos recomienda evitar de nuevo los cactus del reglamento.",
    "⭐ Sheriff Pecos anota otro tropiezo con las reglas. Mejor no coleccionar avisos.",
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

            CREATE TABLE IF NOT EXISTS fun_keyword_usage (
                chat_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL,
                keyword TEXT NOT NULL COLLATE NOCASE,
                first_used_at TEXT NOT NULL,
                PRIMARY KEY(chat_id, user_id, keyword)
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


            CREATE TABLE IF NOT EXISTS user_profiles (
                chat_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL,
                username TEXT NOT NULL DEFAULT '',
                display_name TEXT NOT NULL DEFAULT '',
                first_seen TEXT NOT NULL,
                last_seen TEXT NOT NULL,
                helpful_score INTEGER NOT NULL DEFAULT 0,
                greeting_count INTEGER NOT NULL DEFAULT 0,
                duplicate_count INTEGER NOT NULL DEFAULT 0,
                restricted_count INTEGER NOT NULL DEFAULT 0,
                rule_reminder_count INTEGER NOT NULL DEFAULT 0,
                pecos_mention_count INTEGER NOT NULL DEFAULT 0,
                PRIMARY KEY(chat_id, user_id)
            );


            CREATE TABLE IF NOT EXISTS reputation_notices (
                chat_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL,
                milestone INTEGER NOT NULL,
                sent_at TEXT NOT NULL,
                PRIMARY KEY(chat_id, user_id, milestone)
            );

            CREATE TABLE IF NOT EXISTS question_history (
                chat_id INTEGER NOT NULL,
                message_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL DEFAULT 0,
                user_name TEXT NOT NULL DEFAULT '',
                question_text TEXT NOT NULL,
                signature TEXT NOT NULL,
                created_at TEXT NOT NULL,
                answer_message_id INTEGER NOT NULL DEFAULT 0,
                answer_user_id INTEGER NOT NULL DEFAULT 0,
                PRIMARY KEY(chat_id, message_id)
            );

            CREATE INDEX IF NOT EXISTS idx_question_history_chat_created
                ON question_history(chat_id, created_at DESC);


            CREATE TABLE IF NOT EXISTS archive_detective_notices (
                chat_id INTEGER NOT NULL,
                message_id INTEGER NOT NULL,
                notice_type TEXT NOT NULL,
                related_message_id INTEGER NOT NULL DEFAULT 0,
                sent_at TEXT NOT NULL,
                PRIMARY KEY(chat_id, message_id, notice_type)
            );
            

            -- Memoria histórica de conversaciones. Está separada de file_fingerprints
            -- para que la integración no altere la lógica SHA-256 ni duplicados.
            CREATE TABLE IF NOT EXISTS conversation_messages (
                chat_id INTEGER NOT NULL,
                message_id INTEGER NOT NULL,
                date_utc TEXT NOT NULL,
                edit_date_utc TEXT NOT NULL DEFAULT '',
                sender_id INTEGER NOT NULL DEFAULT 0,
                sender_name TEXT NOT NULL DEFAULT '',
                sender_username TEXT NOT NULL DEFAULT '',
                reply_to_message_id INTEGER NOT NULL DEFAULT 0,
                text TEXT NOT NULL,
                normalized_text TEXT NOT NULL,
                message_link TEXT NOT NULL DEFAULT '',
                media_type TEXT NOT NULL DEFAULT '',
                PRIMARY KEY(chat_id, message_id)
            );

            CREATE INDEX IF NOT EXISTS idx_conv_messages_chat_date
                ON conversation_messages(chat_id, date_utc);
            CREATE INDEX IF NOT EXISTS idx_conv_messages_reply
                ON conversation_messages(chat_id, reply_to_message_id);

            CREATE TABLE IF NOT EXISTS conversation_classifications (
                chat_id INTEGER NOT NULL,
                message_id INTEGER NOT NULL,
                primary_label TEXT NOT NULL,
                is_question INTEGER NOT NULL DEFAULT 0,
                is_request INTEGER NOT NULL DEFAULT 0,
                is_answer INTEGER NOT NULL DEFAULT 0,
                is_helpful INTEGER NOT NULL DEFAULT 0,
                is_closure INTEGER NOT NULL DEFAULT 0,
                is_confirmed_solution INTEGER NOT NULL DEFAULT 0,
                question_score INTEGER NOT NULL DEFAULT 0,
                request_score INTEGER NOT NULL DEFAULT 0,
                answer_score INTEGER NOT NULL DEFAULT 0,
                help_score INTEGER NOT NULL DEFAULT 0,
                closure_score INTEGER NOT NULL DEFAULT 0,
                parent_message_id INTEGER NOT NULL DEFAULT 0,
                root_question_id INTEGER NOT NULL DEFAULT 0,
                classification_reason TEXT NOT NULL DEFAULT '',
                classified_at TEXT NOT NULL,
                PRIMARY KEY(chat_id, message_id)
            );

            CREATE INDEX IF NOT EXISTS idx_conv_class_label
                ON conversation_classifications(chat_id, primary_label);
            CREATE INDEX IF NOT EXISTS idx_conv_class_root
                ON conversation_classifications(chat_id, root_question_id);

            CREATE TABLE IF NOT EXISTS conversation_qa_pairs (
                chat_id INTEGER NOT NULL,
                question_message_id INTEGER NOT NULL,
                answer_message_id INTEGER NOT NULL,
                confirmation_message_id INTEGER NOT NULL DEFAULT 0,
                confidence REAL NOT NULL DEFAULT 0,
                status TEXT NOT NULL,
                reason TEXT NOT NULL DEFAULT '',
                PRIMARY KEY(chat_id, question_message_id, answer_message_id)
            );

            CREATE INDEX IF NOT EXISTS idx_conv_qa_status
                ON conversation_qa_pairs(chat_id, status);
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

    def duplicate_precheck(
        self,
        chat_id: int,
        file_size: int,
        file_name: str,
    ) -> tuple[int, int]:
        """
        Señales previas al hash. Tamaño y nombre ayudan a identificar
        candidatos, pero nunca deciden por sí solos que dos archivos
        tengan el mismo contenido.
        """
        with self.lock:
            size_count = self.conn.execute(
                """
                SELECT COUNT(*) AS n
                FROM file_fingerprints
                WHERE chat_id = ? AND file_size = ?
                """,
                (chat_id, int(file_size or 0)),
            ).fetchone()["n"]

            name_size_count = self.conn.execute(
                """
                SELECT COUNT(*) AS n
                FROM file_fingerprints
                WHERE chat_id = ?
                  AND file_size = ?
                  AND file_name = ? COLLATE NOCASE
                """,
                (chat_id, int(file_size or 0), file_name or ""),
            ).fetchone()["n"]

        return int(size_count), int(name_size_count)

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

    def claim_fun_keyword_once(
        self,
        chat_id: int,
        user_id: int,
        keyword: str,
    ) -> bool:
        """
        Devuelve True solo la primera vez que ese usuario usa la palabra clave
        en ese grupo. Persiste en SQLite y sobrevive a redeploys/reinicios.
        """
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        with self.lock:
            before = self.conn.total_changes
            self.conn.execute(
                """
                INSERT OR IGNORE INTO fun_keyword_usage(
                    chat_id, user_id, keyword, first_used_at
                )
                VALUES(?, ?, ?, ?)
                """,
                (chat_id, user_id, keyword.casefold(), now),
            )
            inserted = self.conn.total_changes > before
            self.conn.commit()
        return inserted

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

    def touch_user_profile(
        self,
        chat_id: int,
        user_id: int,
        username: str,
        display_name: str,
    ) -> None:
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        with self.lock:
            self.conn.execute(
                """
                INSERT INTO user_profiles(
                    chat_id, user_id, username, display_name, first_seen, last_seen
                )
                VALUES(?, ?, ?, ?, ?, ?)
                ON CONFLICT(chat_id, user_id) DO UPDATE SET
                    username = excluded.username,
                    display_name = excluded.display_name,
                    last_seen = excluded.last_seen
                """,
                (chat_id, user_id, username[:80], display_name[:150], now, now),
            )
            self.conn.commit()

    def increment_user_counter(
        self,
        chat_id: int,
        user_id: int,
        username: str,
        display_name: str,
        counter_name: str,
        delta: int = 1,
    ) -> int:
        allowed = {
            "helpful_score",
            "greeting_count",
            "duplicate_count",
            "restricted_count",
            "rule_reminder_count",
            "pecos_mention_count",
        }
        if counter_name not in allowed:
            raise ValueError(f"Contador no permitido: {counter_name}")

        self.touch_user_profile(chat_id, user_id, username, display_name)

        with self.lock:
            self.conn.execute(
                f"UPDATE user_profiles SET {counter_name} = {counter_name} + ? WHERE chat_id = ? AND user_id = ?",
                (max(1, int(delta)), chat_id, user_id),
            )
            row = self.conn.execute(
                f"SELECT {counter_name} AS n FROM user_profiles WHERE chat_id = ? AND user_id = ?",
                (chat_id, user_id),
            ).fetchone()
            self.conn.commit()
        return int(row["n"]) if row else 0

    def get_user_profile(self, chat_id: int, user_id: int) -> sqlite3.Row | None:
        with self.lock:
            return self.conn.execute(
                """
                SELECT *
                FROM user_profiles
                WHERE chat_id = ? AND user_id = ?
                """,
                (chat_id, user_id),
            ).fetchone()

    def get_activity_message_stats(self, chat_id: int) -> list[sqlite3.Row]:
        """Actividad observada desde conversation_messages. Solo lectura."""
        with self.lock:
            return self.conn.execute(
                """
                SELECT
                    sender_id AS user_id,
                    MAX(NULLIF(sender_name, '')) AS sender_name,
                    MAX(NULLIF(sender_username, '')) AS sender_username,
                    MIN(NULLIF(date_utc, '')) AS first_seen,
                    MAX(NULLIF(date_utc, '')) AS last_seen,
                    COUNT(*) AS message_count,
                    SUM(CASE WHEN julianday(date_utc) >= julianday('now', '-30 days') THEN 1 ELSE 0 END) AS messages_30d
                FROM conversation_messages
                WHERE chat_id = ? AND sender_id > 0
                GROUP BY sender_id
                """,
                (chat_id,),
            ).fetchall()

    def get_activity_profiles(self, chat_id: int) -> list[sqlite3.Row]:
        """Perfiles recientes observados por Pecos. Solo lectura."""
        with self.lock:
            return self.conn.execute(
                """
                SELECT user_id, username, display_name, first_seen, last_seen
                FROM user_profiles
                WHERE chat_id = ? AND user_id > 0
                """,
                (chat_id,),
            ).fetchall()

    def claim_reputation_notice(self, chat_id: int, user_id: int, milestone: int) -> bool:
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        with self.lock:
            before = self.conn.total_changes
            self.conn.execute(
                """
                INSERT OR IGNORE INTO reputation_notices(chat_id, user_id, milestone, sent_at)
                VALUES(?, ?, ?, ?)
                """,
                (chat_id, user_id, milestone, now),
            )
            inserted = self.conn.total_changes > before
            self.conn.commit()
        return inserted

    def store_question(
        self,
        chat_id: int,
        message_id: int,
        user_id: int,
        user_name: str,
        question_text: str,
        signature: str,
    ) -> None:
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        with self.lock:
            self.conn.execute(
                """
                INSERT OR IGNORE INTO question_history(
                    chat_id, message_id, user_id, user_name, question_text,
                    signature, created_at
                )
                VALUES(?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    chat_id, message_id, user_id, user_name[:150],
                    question_text[:1000], signature[:500], now,
                ),
            )
            # Mantener un máximo razonable por grupo.
            self.conn.execute(
                """
                DELETE FROM question_history
                WHERE chat_id = ?
                  AND message_id NOT IN (
                      SELECT message_id
                      FROM question_history
                      WHERE chat_id = ?
                      ORDER BY message_id DESC
                      LIMIT ?
                  )
                """,
                (chat_id, chat_id, QUESTION_HISTORY_LIMIT),
            )
            self.conn.commit()

    def recent_questions(self, chat_id: int, limit: int = 120) -> list[sqlite3.Row]:
        with self.lock:
            return self.conn.execute(
                """
                SELECT chat_id, message_id, user_id, user_name, question_text,
                       signature, created_at, answer_message_id, answer_user_id
                FROM question_history
                WHERE chat_id = ?
                  AND created_at >= datetime('now', ?)
                ORDER BY CASE WHEN answer_message_id > 0 THEN 0 ELSE 1 END,
                         message_id DESC
                LIMIT ?
                """,
                (chat_id, f"-{QUESTION_LOOKBACK_DAYS} days", limit),
            ).fetchall()

    def get_question(self, chat_id: int, message_id: int) -> sqlite3.Row | None:
        with self.lock:
            return self.conn.execute(
                """
                SELECT * FROM question_history
                WHERE chat_id = ? AND message_id = ?
                """,
                (chat_id, message_id),
            ).fetchone()

    def mark_question_answer(
        self,
        chat_id: int,
        question_message_id: int,
        answer_message_id: int,
        answer_user_id: int,
    ) -> bool:
        with self.lock:
            cur = self.conn.execute(
                """
                UPDATE question_history
                SET answer_message_id = ?, answer_user_id = ?
                WHERE chat_id = ? AND message_id = ? AND answer_message_id = 0
                """,
                (answer_message_id, answer_user_id, chat_id, question_message_id),
            )
            self.conn.commit()
        return cur.rowcount > 0

    def list_archive_fingerprints(self, chat_id: int, limit: int = 5000) -> list[sqlite3.Row]:
        with self.lock:
            return self.conn.execute(
                """
                SELECT chat_id, sha256, message_id, file_unique_id, file_name,
                       file_size, sender_id, sender_name, first_seen
                FROM file_fingerprints
                WHERE chat_id = ? AND file_name <> ''
                ORDER BY message_id DESC
                LIMIT ?
                """,
                (chat_id, limit),
            ).fetchall()

    def fingerprint_by_message(self, chat_id: int, message_id: int) -> sqlite3.Row | None:
        with self.lock:
            return self.conn.execute(
                """
                SELECT chat_id, sha256, message_id, file_unique_id, file_name,
                       file_size, sender_id, sender_name, first_seen
                FROM file_fingerprints
                WHERE chat_id = ? AND message_id = ?
                LIMIT 1
                """,
                (chat_id, message_id),
            ).fetchone()

    def claim_archive_detective_notice(
        self,
        chat_id: int,
        message_id: int,
        notice_type: str,
        related_message_id: int = 0,
    ) -> bool:
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        with self.lock:
            before = self.conn.total_changes
            self.conn.execute(
                """
                INSERT OR IGNORE INTO archive_detective_notices(
                    chat_id, message_id, notice_type, related_message_id, sent_at
                )
                VALUES(?, ?, ?, ?, ?)
                """,
                (chat_id, message_id, notice_type[:40], related_message_id, now),
            )
            inserted = self.conn.total_changes > before
            self.conn.commit()
        return inserted


    def store_conversation_message(
        self,
        chat_id: int,
        message_id: int,
        date_utc: str,
        edit_date_utc: str,
        sender_id: int,
        sender_name: str,
        sender_username: str,
        reply_to_message_id: int,
        text_value: str,
        normalized_text: str,
        message_link: str,
        media_type: str,
    ) -> None:
        with self.lock:
            self.conn.execute(
                """
                INSERT INTO conversation_messages(
                    chat_id, message_id, date_utc, edit_date_utc,
                    sender_id, sender_name, sender_username,
                    reply_to_message_id, text, normalized_text,
                    message_link, media_type
                )
                VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(chat_id, message_id) DO UPDATE SET
                    edit_date_utc=excluded.edit_date_utc,
                    sender_name=excluded.sender_name,
                    sender_username=excluded.sender_username,
                    reply_to_message_id=excluded.reply_to_message_id,
                    text=excluded.text,
                    normalized_text=excluded.normalized_text,
                    message_link=excluded.message_link,
                    media_type=excluded.media_type
                """,
                (
                    chat_id, message_id, date_utc, edit_date_utc,
                    sender_id, sender_name, sender_username,
                    reply_to_message_id, text_value, normalized_text,
                    message_link, media_type,
                ),
            )
            self.conn.commit()

    def get_conversation_classification(
        self,
        chat_id: int,
        message_id: int,
    ) -> sqlite3.Row | None:
        with self.lock:
            return self.conn.execute(
                """
                SELECT *
                FROM conversation_classifications
                WHERE chat_id=? AND message_id=?
                """,
                (chat_id, message_id),
            ).fetchone()

    def get_conversation_message(
        self,
        chat_id: int,
        message_id: int,
    ) -> sqlite3.Row | None:
        with self.lock:
            return self.conn.execute(
                """
                SELECT *
                FROM conversation_messages
                WHERE chat_id=? AND message_id=?
                """,
                (chat_id, message_id),
            ).fetchone()

    def upsert_conversation_classification(
        self,
        chat_id: int,
        message_id: int,
        primary_label: str,
        is_question: int,
        is_request: int,
        is_answer: int,
        is_helpful: int,
        is_closure: int,
        is_confirmed_solution: int,
        question_score: int,
        request_score: int,
        answer_score: int,
        help_score: int,
        closure_score: int,
        parent_message_id: int,
        root_question_id: int,
        reason: str,
    ) -> None:
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        with self.lock:
            self.conn.execute(
                """
                INSERT INTO conversation_classifications(
                    chat_id, message_id, primary_label,
                    is_question, is_request, is_answer, is_helpful, is_closure,
                    is_confirmed_solution,
                    question_score, request_score, answer_score,
                    help_score, closure_score,
                    parent_message_id, root_question_id,
                    classification_reason, classified_at
                )
                VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(chat_id, message_id) DO UPDATE SET
                    primary_label=excluded.primary_label,
                    is_question=excluded.is_question,
                    is_request=excluded.is_request,
                    is_answer=excluded.is_answer,
                    is_helpful=excluded.is_helpful,
                    is_closure=excluded.is_closure,
                    is_confirmed_solution=excluded.is_confirmed_solution,
                    question_score=excluded.question_score,
                    request_score=excluded.request_score,
                    answer_score=excluded.answer_score,
                    help_score=excluded.help_score,
                    closure_score=excluded.closure_score,
                    parent_message_id=excluded.parent_message_id,
                    root_question_id=excluded.root_question_id,
                    classification_reason=excluded.classification_reason,
                    classified_at=excluded.classified_at
                """,
                (
                    chat_id, message_id, primary_label,
                    is_question, is_request, is_answer, is_helpful, is_closure,
                    is_confirmed_solution,
                    question_score, request_score, answer_score,
                    help_score, closure_score,
                    parent_message_id, root_question_id,
                    reason[:1200], now,
                ),
            )
            self.conn.commit()

    def upsert_conversation_pair(
        self,
        chat_id: int,
        question_message_id: int,
        answer_message_id: int,
        confirmation_message_id: int,
        confidence: float,
        status: str,
        reason: str,
    ) -> None:
        with self.lock:
            self.conn.execute(
                """
                INSERT INTO conversation_qa_pairs(
                    chat_id, question_message_id, answer_message_id,
                    confirmation_message_id, confidence, status, reason
                )
                VALUES(?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(chat_id, question_message_id, answer_message_id)
                DO UPDATE SET
                    confirmation_message_id=excluded.confirmation_message_id,
                    confidence=excluded.confidence,
                    status=excluded.status,
                    reason=excluded.reason
                """,
                (
                    chat_id, question_message_id, answer_message_id,
                    confirmation_message_id, confidence, status, reason[:800],
                ),
            )
            self.conn.commit()

    def find_pair_by_answer(
        self,
        chat_id: int,
        answer_message_id: int,
    ) -> sqlite3.Row | None:
        with self.lock:
            return self.conn.execute(
                """
                SELECT *
                FROM conversation_qa_pairs
                WHERE chat_id=? AND answer_message_id=?
                ORDER BY confidence DESC
                LIMIT 1
                """,
                (chat_id, answer_message_id),
            ).fetchone()

    def search_conversation_history(
        self,
        chat_id: int,
        terms: list[str],
        model_anchor: str = "",
        limit: int = 8,
    ) -> list[sqlite3.Row]:
        if not terms and not model_anchor:
            return []

        with self.lock:
            params: list[object] = [chat_id]

            # Si la consulta contiene un modelo fuerte (DEP450, DM4601e,
            # TK-2312, etc.), ese modelo es un filtro obligatorio. Se prueban
            # variantes habituales de separador sin aplicar REPLACE() a las
            # 113 mil filas, para mantener la búsqueda rápida en Railway.
            if model_anchor:
                anchor_patterns = [f"%{model_anchor}%"]
                match = re.fullmatch(r"([a-z]+)(\d.*)", model_anchor)
                if match:
                    prefix, rest = match.groups()
                    for sep in (" ", "-", "_", ".", "/"):
                        pattern = f"%{prefix}{sep}{rest}%"
                        if pattern not in anchor_patterns:
                            anchor_patterns.append(pattern)

                where_sql = " OR ".join(
                    "m.normalized_text LIKE ?" for _ in anchor_patterns
                )
                params.extend(anchor_patterns)
            else:
                where_parts: list[str] = []
                for term in terms:
                    where_parts.append("m.normalized_text LIKE ?")
                    params.append(f"%{term}%")
                where_sql = " OR ".join(where_parts)

            # Cada mensaje se une solo al mejor par Q/A relacionado. Esto evita
            # que una misma consulta aparezca dos veces cuando tiene varias
            # respuestas PROBABLE y una CONFIRMED.
            rows = self.conn.execute(
                f"""
                SELECT
                    m.message_id, m.date_utc, m.sender_name, m.sender_username,
                    m.text, m.message_link,
                    c.primary_label, c.root_question_id,
                    q.status AS pair_status, q.confidence AS pair_confidence,
                    q.question_message_id, q.answer_message_id,
                    q.confirmation_message_id, q.reason AS pair_reason
                FROM conversation_messages m
                LEFT JOIN conversation_classifications c
                  ON c.chat_id=m.chat_id AND c.message_id=m.message_id
                LEFT JOIN conversation_qa_pairs q
                  ON q.rowid = (
                      SELECT q2.rowid
                      FROM conversation_qa_pairs q2
                      WHERE q2.chat_id=m.chat_id
                        AND (
                            q2.question_message_id=m.message_id
                            OR q2.answer_message_id=m.message_id
                        )
                      ORDER BY
                        CASE q2.status
                            WHEN 'CONFIRMED' THEN 1
                            WHEN 'REJECTED' THEN 2
                            WHEN 'WILL_TRY' THEN 3
                            WHEN 'ACKNOWLEDGED' THEN 4
                            WHEN 'PROBABLE' THEN 5
                            ELSE 6
                        END,
                        COALESCE(q2.confidence,0) DESC,
                        q2.answer_message_id DESC
                      LIMIT 1
                  )
                WHERE m.chat_id=? AND ({where_sql})
                ORDER BY
                    CASE
                        WHEN q.status='CONFIRMED' THEN 1
                        WHEN c.primary_label='SOLUTION_CONFIRMED' THEN 2
                        WHEN c.primary_label='HELP_PROBABLE' THEN 3
                        WHEN c.primary_label='ANSWER' THEN 4
                        WHEN c.primary_label='REQUEST_HELP' THEN 5
                        WHEN c.primary_label='QUESTION' THEN 6
                        ELSE 7
                    END,
                    COALESCE(q.confidence,0) DESC,
                    m.message_id DESC
                LIMIT ?
                """,
                params + [max(1, min(20, limit))],
            ).fetchall()
        return rows

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


def is_owner(user_id: int | None) -> bool:
    return bool(user_id and user_id in OWNER_USER_IDS)


def display_name(message: Message) -> str:
    user = message.from_user
    if not user:
        return "amigo"
    if user.username:
        return f"@{user.username}"
    return user.full_name or str(user.id)


def user_identity_tuple(user) -> tuple[str, str]:
    if not user:
        return "", "amigo"
    username = user.username or ""
    if username:
        shown = f"@{username}"
    else:
        shown = user.full_name or str(user.id)
    return username, shown


def remember_user_presence(message: Message) -> None:
    user = message.from_user
    if not user or user.is_bot:
        return
    username, shown = user_identity_tuple(user)
    db.touch_user_profile(message.chat_id, user.id, username, shown)


def increment_user_metric(message: Message, counter_name: str, delta: int = 1) -> int:
    user = message.from_user
    if not user or user.is_bot:
        return 0
    username, shown = user_identity_tuple(user)
    return db.increment_user_counter(
        message.chat_id,
        user.id,
        username,
        shown,
        counter_name,
        delta,
    )


def get_user_metric(chat_id: int, user_id: int, counter_name: str) -> int:
    row = db.get_user_profile(chat_id, user_id)
    if not row:
        return 0
    try:
        return int(row[counter_name])
    except Exception:
        return 0


def normalize_intent(text: str) -> str:
    text = unicodedata.normalize("NFD", (text or "").lower())
    return "".join(ch for ch in text if unicodedata.category(ch) != "Mn")


def parse_activity_datetime(value: object) -> datetime | None:
    raw = str(value or "").strip()
    if not raw:
        return None
    if raw.endswith("Z"):
        raw = raw[:-1] + "+00:00"
    try:
        dt = datetime.fromisoformat(raw)
    except ValueError:
        dt = None
        for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%dT%H:%M:%S"):
            try:
                dt = datetime.strptime(raw, fmt)
                break
            except ValueError:
                pass
        if dt is None:
            return None
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=ZoneInfo("UTC"))
    return dt.astimezone(BOT_TZ)


def activity_age_days(last_seen: datetime | None) -> float:
    if last_seen is None:
        return float("inf")
    delta = datetime.now(BOT_TZ) - last_seen
    return max(0.0, delta.total_seconds() / 86400.0)


def activity_status(last_seen: datetime | None) -> tuple[str, str]:
    days = activity_age_days(last_seen)
    if days <= 30:
        return "🟢", "ACTIVO"
    if days <= 90:
        return "🟡", "POCO ACTIVO"
    if days <= 180:
        return "🟠", "INACTIVO"
    return "🔴", "MUY INACTIVO"


def human_activity_age(last_seen: datetime | None) -> str:
    if last_seen is None:
        return "sin fecha"
    seconds = max(0, int((datetime.now(BOT_TZ) - last_seen).total_seconds()))
    if seconds < 60:
        return "hace menos de 1 minuto"
    if seconds < 3600:
        minutes = seconds // 60
        return f"hace {minutes} min"
    if seconds < 86400:
        hours = seconds // 3600
        return f"hace {hours} h"
    days = seconds // 86400
    if days < 60:
        return f"hace {days} día{'s' if days != 1 else ''}"
    if days < 730:
        months = max(1, round(days / 30))
        return f"hace ~{months} mes{'es' if months != 1 else ''}"
    years = days / 365.25
    return f"hace ~{years:.1f} años"


def build_member_activity_snapshot(chat_id: int) -> list[dict[str, object]]:
    entries: dict[int, dict[str, object]] = {}
    for row in db.get_activity_message_stats(chat_id):
        user_id = int(row["user_id"] or 0)
        if user_id <= 0:
            continue
        entries[user_id] = {
            "user_id": user_id,
            "username": str(row["sender_username"] or "").lstrip("@"),
            "display_name": str(row["sender_name"] or "").strip(),
            "first_seen": parse_activity_datetime(row["first_seen"]),
            "last_seen": parse_activity_datetime(row["last_seen"]),
            "message_count": int(row["message_count"] or 0),
            "messages_30d": int(row["messages_30d"] or 0),
        }
    for row in db.get_activity_profiles(chat_id):
        user_id = int(row["user_id"] or 0)
        if user_id <= 0:
            continue
        profile_first = parse_activity_datetime(row["first_seen"])
        profile_last = parse_activity_datetime(row["last_seen"])
        username = str(row["username"] or "").lstrip("@")
        display = str(row["display_name"] or "").strip()
        entry = entries.get(user_id)
        if entry is None:
            entries[user_id] = {
                "user_id": user_id, "username": username, "display_name": display,
                "first_seen": profile_first, "last_seen": profile_last,
                "message_count": 0, "messages_30d": 0,
            }
            continue
        current_first = entry.get("first_seen")
        if profile_first and (not isinstance(current_first, datetime) or profile_first < current_first):
            entry["first_seen"] = profile_first
        current_last = entry.get("last_seen")
        if profile_last and (not isinstance(current_last, datetime) or profile_last > current_last):
            entry["last_seen"] = profile_last
        if username:
            entry["username"] = username
        if display:
            entry["display_name"] = display
    rows = list(entries.values())
    rows.sort(key=lambda x: x.get("last_seen") if isinstance(x.get("last_seen"), datetime) else datetime.min.replace(tzinfo=BOT_TZ), reverse=True)
    return rows


def activity_person_label(entry: dict[str, object]) -> str:
    username = str(entry.get("username") or "").strip()
    display = str(entry.get("display_name") or "").strip()
    if username and display and display.casefold() != ("@" + username).casefold():
        return f"{display} (@{username})"
    if username:
        return f"@{username}"
    if display:
        return display
    return f"ID {entry.get('user_id', 0)}"


def format_activity_timestamp(value: object) -> str:
    if not isinstance(value, datetime):
        return "sin fecha"
    return value.strftime("%d/%m/%Y %H:%M")


def find_activity_entries(entries: list[dict[str, object]], query: str) -> list[dict[str, object]]:
    needle = normalize_intent(query).strip().lstrip("@")
    if not needle:
        return []
    if needle.isdigit():
        uid = int(needle)
        return [e for e in entries if int(e.get("user_id") or 0) == uid]
    exact, partial = [], []
    for entry in entries:
        username = normalize_intent(str(entry.get("username") or "")).lstrip("@")
        display = normalize_intent(str(entry.get("display_name") or ""))
        if needle == username or needle == display:
            exact.append(entry)
        elif needle in username or needle in display:
            partial.append(entry)
    return exact or partial


def build_activity_text_report(chat_title: str, entries: list[dict[str, object]], *, inactive_days: int | None = None) -> str:
    now_text = datetime.now(BOT_TZ).strftime("%d/%m/%Y %H:%M")
    lines = [
        "PECOS PAUL KELE - REPORTE DE ACTIVIDAD OBSERVADA",
        f"Grupo: {chat_title}", f"Generado: {now_text} ({TIMEZONE_NAME})", "",
        "IMPORTANTE:",
        "Este informe NO representa la última conexión a Telegram.",
        "Solo indica la última actividad que Pecos observó/registró en el grupo.",
        "Un usuario que solo lee y no escribe puede parecer inactivo.",
        "El listado histórico tampoco confirma que la persona siga siendo miembro.", "",
        "Clasificación:", "ACTIVO = 0 a 30 días", "POCO ACTIVO = 31 a 90 días",
        "INACTIVO = 91 a 180 días", "MUY INACTIVO = más de 180 días", "",
    ]
    selected = entries
    if inactive_days is not None:
        selected = [e for e in entries if activity_age_days(e.get("last_seen") if isinstance(e.get("last_seen"), datetime) else None) >= inactive_days]
        selected.sort(key=lambda e: activity_age_days(e.get("last_seen") if isinstance(e.get("last_seen"), datetime) else None), reverse=True)
        lines += [f"Filtro: sin actividad observada durante {inactive_days} días o más.", ""]
    lines += [f"Usuarios incluidos: {len(selected)}", "=" * 78]
    for index, entry in enumerate(selected, 1):
        last_dt = entry.get("last_seen") if isinstance(entry.get("last_seen"), datetime) else None
        icon, state = activity_status(last_dt)
        lines += [
            f"{index}. {icon} {state} | {activity_person_label(entry)}",
            f"   User ID: {int(entry.get('user_id') or 0)}",
            f"   Última actividad observada: {format_activity_timestamp(last_dt)} ({human_activity_age(last_dt)})",
            f"   Mensajes registrados en memoria: {int(entry.get('message_count') or 0)}",
            f"   Mensajes registrados últimos 30 días: {int(entry.get('messages_30d') or 0)}", "",
        ]
    return "\n".join(lines).rstrip() + "\n"


def telegram_member_status_label(status: str) -> str:
    labels = {"creator":"propietario", "owner":"propietario", "administrator":"administrador", "member":"miembro", "restricted":"restringido", "left":"salió del grupo", "kicked":"expulsado/bloqueado"}
    return labels.get((status or "").casefold(), status or "desconocido")


PECOS_USERNAME_ALIASES = {"pecos_paul_kele_bot"}


def text_mentions_pecos(text_value: str) -> bool:
    """
    Detecta menciones explícitas a Pecos, incluyendo el @username de Telegram.
    El guion bajo es carácter de palabra para regex, por eso una búsqueda
    simple con \bpecos\b no reconoce bien @Pecos_Paul_Kele_Bot.
    """
    normalized = normalize_intent(text_value or "").lower()

    if re.search(r"(?<!\w)(?:pecos|peco)(?!\w)", normalized):
        return True

    compact = normalized.lstrip("@")
    return any(alias and alias in compact for alias in PECOS_USERNAME_ALIASES)


def pecos_explicitly_excluded_from_greeting(text_value: str) -> bool:
    """Detecta saludos donde Pecos/Peco fue excluido de forma expresa."""
    normalized = normalize_intent(text_value or "").lower().strip()
    if not normalized:
        return False

    greeting_signal = (
        bool(re.search(r"\b(saludo|saludos|hola|hello|hey|holi|buenas)\b", normalized))
        or "buenos dias" in normalized
        or "buen dia" in normalized
        or "buenas tardes" in normalized
        or "buenas noches" in normalized
        or "muy buenas" in normalized
    )
    if not greeting_signal:
        return False

    canonical = normalized

    # Funciona con Pecos, Peco y también con el @username del bot.
    for alias in PECOS_USERNAME_ALIASES:
        alias_norm = normalize_intent(alias).lower().lstrip("@")
        if alias_norm:
            canonical = canonical.replace("@" + alias_norm, "pecos")
            canonical = canonical.replace(alias_norm, "pecos")

    canonical = re.sub(r"(?<!\w)peco(?!\w)", "pecos", canonical)

    exclusion_patterns = (
        r"\bmenos\s+(?:a\s+|al\s+)?pecos\b",
        r"\bexcepto\s+(?:a\s+|al\s+)?pecos\b",
        r"\bsalvo\s+(?:a\s+|al\s+)?pecos\b",
        r"\bpero\s+no\s+(?:a\s+|al\s+)?pecos\b",
        r"\by\s+no\s+(?:a\s+|al\s+)?pecos\b",
        r"\bni\s+(?:a\s+|al\s+)?pecos\b",
    )

    return any(re.search(pattern, canonical) for pattern in exclusion_patterns)


def gratitude_is_for_pecos(message: Message) -> bool:
    """Devuelve True solo si el agradecimiento está dirigido a Pecos.

    Se considera dirigido a Pecos cuando:
    - el texto menciona Pecos/Peco/@username, o
    - el mensaje responde directamente a un mensaje del propio bot.

    Un "muchas gracias" genérico entre usuarios no debe hacer intervenir a Pecos.
    """
    text_value = message.text or message.caption or ""

    if text_mentions_pecos(text_value):
        return True

    replied = message.reply_to_message
    if replied is None or replied.from_user is None:
        return False

    replied_user = replied.from_user
    if not replied_user.is_bot:
        return False

    username = normalize_intent(replied_user.username or "").lower().lstrip("@")
    if not username:
        return False

    return username in PECOS_USERNAME_ALIASES


def contextual_reply_requests_help(message: Message) -> bool:
    """True si una respuesta a otro usuario sí está pidiendo ayuda."""
    text_value = message.text or message.caption or ""
    normalized = normalize_intent(text_value).strip()

    if not normalized:
        return False

    if text_mentions_pecos(text_value):
        return True

    if "?" in text_value:
        return True

    help_patterns = (
        r"\bayuda\b",
        r"\bayudame\b",
        r"\bme pueden ayudar\b",
        r"\bpueden ayudarme\b",
        r"\balguien sabe\b",
        r"\bsaben como\b",
        r"\bcomo (?:hago|puedo|se hace|lo hago)\b",
        r"\bque puedo hacer\b",
        r"\bque puede ser\b",
        r"\bque sera\b",
        r"\balguna idea\b",
        r"\balguna sugerencia\b",
        r"\bque recomiendan\b",
    )

    if any(re.search(pattern, normalized) for pattern in help_patterns):
        return True

    # Una consulta técnica suficientemente concreta sigue pudiendo ser atendida.
    if technical_archive_terms(text_value):
        return True

    return False


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


def format_hours_value(hours: float) -> str:
    if hours < 10:
        return f"{hours:.1f}"
    return str(int(round(hours)))


def build_silence_message(elapsed_hours: float) -> str:
    template = random.choice(SILENCE_MESSAGES)
    return template.replace("{horas}", format_hours_value(elapsed_hours))


def has_archive_extension(file_name: str) -> bool:
    lower = (file_name or "").casefold()
    return any(lower.endswith(ext) for ext in ARCHIVE_EXTENSIONS)


def looks_like_helpful_contribution(message: Message) -> bool:
    if message.document:
        file_name = getattr(message.document, "file_name", "") or ""
        if has_archive_extension(file_name):
            return True

    text_value = (message.text or message.caption or "").strip()
    if len(text_value) < 18:
        return False

    normalized = normalize_intent(text_value)
    return any(keyword in normalized for keyword in KNOWN_HELPFUL_KEYWORDS)


def remember_helpful_contribution(message: Message) -> int | None:
    if looks_like_helpful_contribution(message):
        return increment_user_metric(message, "helpful_score")
    return None


def question_signature(text_value: str) -> str:
    normalized = normalize_intent(text_value)
    normalized = re.sub(r"https?://\S+", " ", normalized)
    normalized = re.sub(r"@\w+", " ", normalized)
    tokens = re.findall(r"[a-z0-9][a-z0-9_+.-]*", normalized)
    informative = [
        token for token in tokens
        if token not in QUESTION_STOPWORDS and len(token) >= 2
    ]
    return " ".join(informative[:50])


def is_repeated_question_candidate(message: Message) -> bool:
    text_value = (message.text or message.caption or "").strip()
    if not text_value or len(text_value) < 8:
        return False

    normalized = normalize_intent(text_value)

    # Las preguntas explícitas a Pecos siguen su flujo conversacional normal.
    if text_mentions_pecos(text_value):
        return False

    if not looks_like_question(text_value):
        return False

    signature = question_signature(text_value)
    token_count = len(signature.split())

    # Una consulta demasiado genérica ("¿cómo hago?") no debe disparar coincidencias.
    return token_count >= 2


def question_similarity(sig_a: str, sig_b: str) -> float:
    if not sig_a or not sig_b:
        return 0.0

    if sig_a == sig_b:
        return 1.0

    a = set(sig_a.split())
    b = set(sig_b.split())
    if not a or not b:
        return 0.0

    shared = len(a & b)
    if shared < 2:
        return 0.0

    jaccard = shared / len(a | b)
    containment = shared / min(len(a), len(b))
    sequence = SequenceMatcher(None, sig_a, sig_b).ratio()

    # Si todos los términos importantes de la consulta corta aparecen en la larga,
    # lo consideramos una señal fuerte, pero solo con 3+ términos para evitar ruido.
    if min(len(a), len(b)) >= 3 and containment >= 0.90:
        return max(jaccard, 0.88, sequence)

    return max(jaccard, sequence * 0.92)


def repeated_question_alert_allowed(chat_id: int, user_id: int) -> bool:
    now = time.monotonic()
    key = (chat_id, user_id)
    previous = RECENT_REPEAT_QUESTION_ALERTS.get(key)
    if previous is not None and now - previous <= QUESTION_ALERT_COOLDOWN_SECONDS:
        return False

    RECENT_REPEAT_QUESTION_ALERTS[key] = now

    expired = [
        item for item, ts in RECENT_REPEAT_QUESTION_ALERTS.items()
        if now - ts > QUESTION_ALERT_COOLDOWN_SECONDS + 60
    ]
    for item in expired:
        RECENT_REPEAT_QUESTION_ALERTS.pop(item, None)

    return True


async def maybe_send_reputation_notice(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
    score: int | None,
) -> bool:
    user = message.from_user
    if not user or user.is_bot or not score:
        return False

    milestone = None
    for value in REPUTATION_MILESTONES:
        if score >= value:
            milestone = value

    if milestone is None:
        return False

    if not db.claim_reputation_notice(message.chat_id, user.id, milestone):
        return False

    usuario = display_name(message)
    template = random.choice(REPUTATION_MESSAGES[milestone])
    await context.bot.send_message(
        chat_id=message.chat_id,
        text=template.replace("{usuario}", usuario),
    )
    db.add_history(
        f"RECONOCIMIENTO PECOS | {usuario} | hito interno {milestone} | chat {message.chat_id}"
    )
    return True


async def capture_answer_to_known_question(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    reply = message.reply_to_message
    user = message.from_user
    if not reply or not user or user.is_bot:
        return False

    question = db.get_question(message.chat_id, reply.message_id)
    if not question:
        return False

    # No cuenta como ayuda responderse a sí mismo.
    if int(question["user_id"] or 0) == user.id:
        return False

    text_value = (message.text or message.caption or "").strip()
    has_useful_media = bool(message.document or message.photo or message.video)
    if not has_useful_media and len(text_value) < 12:
        return False

    if not db.mark_question_answer(
        message.chat_id,
        reply.message_id,
        message.message_id,
        user.id,
    ):
        return False

    score = increment_user_metric(message, "helpful_score", 2)
    await maybe_send_reputation_notice(message, context, score)
    db.add_history(
        f"AYUDA DETECTADA | {display_name(message)} respondió pregunta {reply.message_id} "
        f"en chat {message.chat_id}."
    )
    return True


async def handle_repeated_question(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    if not is_repeated_question_candidate(message):
        return False

    user = message.from_user
    if not user or user.is_bot:
        return False

    current_text = (message.text or message.caption or "").strip()
    current_signature = question_signature(current_text)

    best = None
    best_score = 0.0
    for row in db.recent_questions(message.chat_id):
        if int(row["message_id"]) == message.message_id:
            continue

        score = question_similarity(current_signature, str(row["signature"] or ""))
        if score > best_score:
            best = row
            best_score = score

    # Siempre guardamos la pregunta nueva para que Pecos aprenda el historial futuro.
    db.store_question(
        message.chat_id,
        message.message_id,
        user.id,
        display_name(message),
        current_text,
        current_signature,
    )

    if best is None or best_score < QUESTION_SIMILARITY_THRESHOLD:
        return False

    if not repeated_question_alert_allowed(message.chat_id, user.id):
        return False

    previous_link = build_message_link(message.chat, int(best["message_id"]))
    answer_id = int(best["answer_message_id"] or 0)
    answer_link = build_message_link(message.chat, answer_id) if answer_id else None

    response = random.choice(REPEATED_QUESTION_MESSAGES).replace(
        "{usuario}", display_name(message)
    )

    if previous_link:
        response += f"\n\n🔎 Conversación anterior: {previous_link}"

    if answer_link:
        response += f"\n💬 Respuesta relacionada: {answer_link}"

    await context.bot.send_message(chat_id=message.chat_id, text=response)
    db.add_history(
        f"PREGUNTA REPETIDA | {display_name(message)} | similitud={best_score:.2f} | "
        f"actual={message.message_id} anterior={best['message_id']}"
    )
    return True


def contextual_slot_available(chat_id: int, slot: str) -> bool:
    """Comprueba cooldown sin consumirlo."""
    now = time.monotonic()

    expired = [
        key for key, ts in RECENT_CONTEXTUAL_RESPONSES.items()
        if now - ts > CONTEXTUAL_RESPONSE_COOLDOWN_SECONDS + 30
    ]
    for key in expired:
        RECENT_CONTEXTUAL_RESPONSES.pop(key, None)

    key = (chat_id, slot)
    previous = RECENT_CONTEXTUAL_RESPONSES.get(key)
    return previous is None or now - previous > CONTEXTUAL_RESPONSE_COOLDOWN_SECONDS


def mark_contextual_response(chat_id: int, slot: str) -> None:
    RECENT_CONTEXTUAL_RESPONSES[(chat_id, slot)] = time.monotonic()


def repeat_warning_text(kind: str, count: int) -> str:
    if count < 2:
        return ""

    if kind == "duplicate":
        return "\n\n" + random.choice(REPEAT_DUPLICATE_WARNINGS)
    if kind == "rule":
        return "\n\n" + random.choice(REPEAT_RULE_WARNINGS)
    if kind == "restricted":
        return "\n\n" + random.choice(REPEAT_RESTRICTED_WARNINGS)

    return ""


def archive_file_allowed(file_name: str) -> bool:
    lower = (file_name or "").casefold().strip()
    return any(lower.endswith(ext) for ext in ARCHIVE_EXTENSIONS)


def archive_normalized_name(value: str) -> str:
    normalized = normalize_intent(value or "")
    normalized = re.sub(r"\.(rar|zip|7z)$", "", normalized, flags=re.IGNORECASE)
    normalized = re.sub(r"[^a-z0-9]+", " ", normalized)
    return re.sub(r"\s+", " ", normalized).strip()


def archive_stem_for_similarity(file_name: str) -> str:
    stem = archive_normalized_name(file_name)
    # Neutraliza versiones explícitas, pero conserva números de modelo unidos a letras.
    stem = re.sub(r"\bv?\d+(?:[._-]\d+)+\b", " version ", stem)
    stem = re.sub(r"\b(?:ver|version)\s*\d+(?:\s*\d+)*\b", " version ", stem)
    return re.sub(r"\s+", " ", stem).strip()


def archive_model_terms(text_value: str) -> list[str]:
    """
    Extrae modelos de radio escritos juntos o separados.

    Ejemplos:
    - EM200 -> em200
    - PRO 5100 -> pro5100
    - TK-2312 -> tk2312
    - DM 4601e -> dm4601e
    - XPR7550e -> xpr7550e

    Se exige un prefijo de al menos dos letras y un bloque de al menos
    tres dígitos para evitar convertir versiones como R40 o R05 en modelos.
    """
    normalized = normalize_intent(text_value or "")
    models: list[str] = []
    seen: set[str] = set()

    for match in re.finditer(
        r"\b([a-z]{2,5})[\s._-]*(\d{3,5}[a-z]?)\b",
        normalized,
    ):
        model = f"{match.group(1)}{match.group(2)}"
        if model not in seen:
            seen.add(model)
            models.append(model)

    return models[:6]


def archive_name_matches_model(file_name: str, model: str) -> bool:
    compact_name = re.sub(r"[^a-z0-9]", "", archive_normalized_name(file_name))
    compact_model = re.sub(r"[^a-z0-9]", "", normalize_intent(model))
    return bool(compact_model and compact_model in compact_name)


def _archive_alias_to_canonical() -> dict[str, str]:
    result: dict[str, str] = {}
    for canonical, aliases in ARCHIVE_TERM_ALIASES.items():
        for alias in aliases | {canonical}:
            result[archive_normalized_name(alias)] = canonical
    for canonical, aliases in ARCHIVE_FAMILY_ALIASES.items():
        for alias in aliases | {canonical}:
            result[archive_normalized_name(alias)] = canonical
    return result


ARCHIVE_ALIAS_TO_CANONICAL = _archive_alias_to_canonical()


def canonical_archive_token(token: str) -> str:
    normalized = archive_normalized_name(token)
    if not normalized:
        return ""

    exact = ARCHIVE_ALIAS_TO_CANONICAL.get(normalized)
    if exact:
        return exact

    # Corrección leve de errores de escritura solo para palabras alfabéticas
    # relativamente largas. Los identificadores/modelos con números se dejan
    # intactos para evitar convertir un modelo en otro.
    if normalized.isalpha() and len(normalized) >= 5:
        candidates = set(TECHNICAL_ARCHIVE_WORDS) | set(ARCHIVE_FAMILY_ALIASES)
        best = ""
        best_score = 0.0
        for candidate in candidates:
            score = SequenceMatcher(None, normalized, candidate).ratio()
            if score > best_score:
                best = candidate
                best_score = score
        if best_score >= 0.88:
            return best

    return normalized


def strict_archive_family_terms(text_value: str) -> list[str]:
    """Detecta familias/plataformas solo por coincidencia explícita de alias.

    Se usa únicamente para decidir si Pecos debe intervenir automáticamente.
    La similitud difusa queda reservada para interpretar una consulta que ya fue
    identificada como técnica, evitando falsos positivos en conversación casual.
    """
    normalized = archive_normalized_name(text_value or "")
    if not normalized:
        return []

    found: list[str] = []
    seen: set[str] = set()
    for canonical, aliases in ARCHIVE_FAMILY_ALIASES.items():
        for alias in aliases | {canonical}:
            alias_norm = archive_normalized_name(alias)
            if alias_norm and re.search(rf"(?:^|\s){re.escape(alias_norm)}(?:$|\s)", normalized):
                if canonical not in seen:
                    seen.add(canonical)
                    found.append(canonical)
                break
    return found[:4]


def strict_technical_archive_words(text_value: str) -> list[str]:
    """Devuelve señales técnicas escritas explícitamente por el usuario.

    No aplica similitud ortográfica. Esto es intencional: la similitud ayuda a
    comprender una búsqueda ya detectada, pero nunca debe convertir una charla
    cotidiana en una búsqueda automática de archivos.
    """
    normalized = archive_normalized_name(text_value or "")
    if not normalized:
        return []

    found: list[str] = []
    seen: set[str] = set()

    # Palabras técnicas canónicas.
    for word in TECHNICAL_ARCHIVE_WORDS:
        word_norm = archive_normalized_name(word)
        if word_norm and re.search(rf"(?:^|\s){re.escape(word_norm)}(?:$|\s)", normalized):
            if word not in seen:
                seen.add(word)
                found.append(word)

    # Alias exactos conocidos (sofware, pasword, code plug, etc.).
    for canonical, aliases in ARCHIVE_TERM_ALIASES.items():
        for alias in aliases | {canonical}:
            alias_norm = archive_normalized_name(alias)
            if alias_norm and re.search(rf"(?:^|\s){re.escape(alias_norm)}(?:$|\s)", normalized):
                if canonical not in seen:
                    seen.add(canonical)
                    found.append(canonical)
                break

    return found[:8]


def archive_family_terms(text_value: str) -> list[str]:
    normalized = archive_normalized_name(text_value or "")
    if not normalized:
        return []

    tokens = normalized.split()
    found: list[str] = []
    seen: set[str] = set()

    for canonical, aliases in ARCHIVE_FAMILY_ALIASES.items():
        variants = aliases | {canonical}
        matched = False
        for alias in variants:
            alias_norm = archive_normalized_name(alias)
            if alias_norm and re.search(rf"(?:^|\s){re.escape(alias_norm)}(?:$|\s)", normalized):
                matched = True
                break

        if not matched:
            # Tolerancia a un error de escritura corto en familias conocidas.
            for token in tokens:
                if len(token) >= 5 and SequenceMatcher(None, token, canonical).ratio() >= 0.84:
                    matched = True
                    break

        if matched and canonical not in seen:
            seen.add(canonical)
            found.append(canonical)

    return found[:4]


def archive_name_matches_family(file_name: str, family: str) -> bool:
    normalized_name = archive_normalized_name(file_name)
    name_tokens = normalized_name.split()
    aliases = ARCHIVE_FAMILY_ALIASES.get(family, {family}) | {family}

    for alias in aliases:
        alias_norm = archive_normalized_name(alias)
        if not alias_norm:
            continue
        if alias_norm in normalized_name:
            return True
        if len(alias_norm) >= 5:
            for token in name_tokens:
                if len(token) >= 5 and SequenceMatcher(None, token, alias_norm).ratio() >= 0.88:
                    return True
    return False


def archive_identifier_terms(text_value: str) -> list[str]:
    terms = extract_archive_terms(text_value)
    result: list[str] = []
    for term in terms:
        compact = re.sub(r"[^a-z0-9]", "", term)
        if len(compact) >= 3 and any(c.isalpha() for c in compact) and any(c.isdigit() for c in compact):
            result.append(term)
    return result[:4]


def archive_term_variants(term: str) -> set[str]:
    canonical = canonical_archive_token(term)
    variants = {archive_normalized_name(canonical)}

    for key, aliases in ARCHIVE_TERM_ALIASES.items():
        if canonical == key:
            variants.update(archive_normalized_name(alias) for alias in aliases)

    for key, aliases in ARCHIVE_FAMILY_ALIASES.items():
        if canonical == key:
            variants.update(archive_normalized_name(alias) for alias in aliases)

    return {v for v in variants if v}


def extract_archive_terms(text_value: str) -> list[str]:
    normalized = normalize_intent(text_value or "")
    models = archive_model_terms(normalized)
    families = archive_family_terms(normalized)

    # Evita que un modelo separado como "PRO 5100" termine convertido en
    # dos términos débiles ("pro" y "5100"). Se elimina esa secuencia
    # del texto y luego se agregan los modelos canónicos al resultado.
    text_without_models = normalized
    text_without_models = re.sub(
        r"\b[a-z]{2,5}[\s._-]*\d{3,5}[a-z]?\b",
        " ",
        text_without_models,
    )

    raw_tokens = re.findall(r"[a-z0-9][a-z0-9._+-]*", text_without_models)
    result: list[str] = []
    seen: set[str] = set()

    for token in raw_tokens:
        token = token.strip("._+-")
        if not token or token in ARCHIVE_SEARCH_STOPWORDS:
            continue
        if token in {"rar", "zip", "7z"}:
            continue
        if len(token) < 3 and not any(ch.isdigit() for ch in token):
            continue

        canonical = canonical_archive_token(token)
        if not canonical:
            continue
        if canonical not in seen:
            seen.add(canonical)
            result.append(canonical)

    for family in families:
        if family not in seen:
            seen.add(family)
            result.append(family)

    for model in models:
        if model not in seen:
            seen.add(model)
            result.append(model)

    # Términos técnicos primero, luego familias/plataformas y modelos.
    technical = [t for t in result if t in TECHNICAL_ARCHIVE_WORDS]
    family_set = set(families)
    family_items = [t for t in result if t in family_set]
    model_set = set(models)
    model_items = [t for t in result if t in model_set]
    reserved = set(technical) | family_set | model_set
    other = [t for t in result if t not in reserved]
    return (technical + family_items + model_items + other)[:10]


def archive_search_score(file_name: str, terms: list[str]) -> float:
    if not terms:
        return 0.0

    normalized_name = archive_normalized_name(file_name)
    name_tokens = set(normalized_name.split())
    score = 0.0
    matched = 0

    for term in terms:
        variants = archive_term_variants(term)
        term_matched = False

        for variant in variants:
            if variant in name_tokens:
                score += 4.0
                term_matched = True
                break
            if variant in normalized_name:
                score += 2.5
                term_matched = True
                break

            compact_name = normalized_name.replace(" ", "")
            compact_variant = variant.replace(" ", "")
            if compact_variant and compact_variant in compact_name:
                score += 2.0
                term_matched = True
                break

        if not term_matched:
            canonical = canonical_archive_token(term)
            # Similitud controlada: solo palabras largas sin números.
            if canonical.isalpha() and len(canonical) >= 5:
                best_ratio = max(
                    (SequenceMatcher(None, canonical, token).ratio() for token in name_tokens if len(token) >= 4),
                    default=0.0,
                )
                if best_ratio >= 0.88:
                    score += 1.4
                    term_matched = True

        if term_matched:
            matched += 1

    if matched == len(terms):
        score += 3.0
    elif matched == 0:
        return 0.0

    # Favorece coincidencias más específicas.
    score += min(2.0, sum(len(t) for t in terms) / 20.0)
    return score


def search_archive_rows(chat_id: int, query: str, limit: int = ARCHIVE_SEARCH_MAX_RESULTS) -> list[sqlite3.Row]:
    terms = extract_archive_terms(query)
    if not terms:
        return []

    requested_models = archive_model_terms(query)
    requested_families = archive_family_terms(query)
    ranked: list[tuple[float, sqlite3.Row]] = []

    for row in db.list_archive_fingerprints(chat_id):
        file_name = str(row["file_name"] or "")
        if not archive_file_allowed(file_name):
            continue

        # Un modelo concreto es un ancla dura: no se ofrecen archivos de otra
        # familia solo porque comparten palabras genéricas como CPS/firmware.
        matched_models = [
            model for model in requested_models
            if archive_name_matches_model(file_name, model)
        ]
        if requested_models and not matched_models:
            continue

        # Lo mismo para familias/plataformas sin números (MOTOTRBO, APX, etc.).
        matched_families = [
            family for family in requested_families
            if archive_name_matches_family(file_name, family)
        ]
        if requested_families and not matched_families:
            continue

        score = archive_search_score(file_name, terms)
        if score <= 0:
            continue

        score += 12.0 * len(matched_models)
        score += 9.0 * len(matched_families)
        ranked.append((score, row))

    ranked.sort(key=lambda pair: (pair[0], int(pair[1]["message_id"])), reverse=True)
    return [row for _, row in ranked[:max(1, min(12, limit))]]


def human_file_size(size_value: int) -> str:
    size = max(0, int(size_value or 0))
    if size >= 1024 ** 3:
        return f"{size / (1024 ** 3):.2f} GB"
    if size >= 1024 ** 2:
        return f"{size / (1024 ** 2):.1f} MB"
    if size >= 1024:
        return f"{size / 1024:.1f} KB"
    return f"{size} B"


def archive_result_lines(chat: Chat, rows: list[sqlite3.Row], max_items: int = 6) -> list[str]:
    lines: list[str] = []
    for index, row in enumerate(rows[:max_items], start=1):
        file_name = str(row["file_name"] or "archivo")
        file_size = human_file_size(int(row["file_size"] or 0))
        sender = str(row["sender_name"] or "usuario desconocido")
        link = build_message_link(chat, int(row["message_id"]))

        line = f"{index}. 📦 {file_name} · {file_size} · {sender}"
        if link:
            line += f"\n   🔗 {link}"
        lines.append(line)
    return lines


def archive_query_needs_target(query: str, terms: list[str] | None = None) -> bool:
    terms = terms if terms is not None else extract_archive_terms(query)
    if not terms:
        return False

    if archive_model_terms(query) or archive_family_terms(query) or archive_identifier_terms(query):
        return False

    specific = [term for term in terms if term not in ARCHIVE_GENERIC_RESOURCE_TERMS]
    return bool(terms) and not specific


def archive_query_from_natural_text(text_value: str) -> str | None:
    normalized = normalize_intent(text_value or "").strip()
    if not text_mentions_pecos(text_value):
        return None

    terms = extract_archive_terms(text_value)
    models = archive_model_terms(text_value)
    families = archive_family_terms(text_value)
    identifiers = archive_identifier_terms(text_value)

    # Para decidir si Pecos debe intervenir por sí solo usamos solo señales
    # explícitas. La similitud ortográfica NO puede activar una búsqueda.
    strict_technical = strict_technical_archive_words(text_value)
    strict_families = strict_archive_family_terms(text_value)

    explicit_intent = (
        "busca" in normalized
        or "buscar" in normalized
        or "encuentra" in normalized
        or "tenemos" in normalized
        or "tienes" in normalized
        or "hay algo" in normalized
        or "hay archivo" in normalized
        or "hay archivos" in normalized
        or "archivo para" in normalized
        or "archivos para" in normalized
        or "que hay para" in normalized
        or "que tenemos" in normalized
    )

    # Además de las frases "Pecos busca...", acepta consultas cortas de uso real:
    # "Pecos CPS APX?", "Pecos CPS MOTOTRBO?", "Pecos KPG-D6" o
    # "Pecos salta password". Los saludos/conversación social siguen fuera
    # porque requieren al menos una señal técnica, familia, modelo o identificador.
    strong_archive_signal = bool(strict_technical or strict_families or models or identifiers)
    if not explicit_intent and not strong_archive_signal:
        return None

    if not terms:
        return ""
    return " ".join(terms)


def archive_hint_key(chat_id: int, terms: list[str]) -> tuple[int, str]:
    return (chat_id, "|".join(sorted(terms[:3])))


def archive_hint_allowed(chat_id: int, terms: list[str]) -> bool:
    key = archive_hint_key(chat_id, terms)
    now = time.monotonic()
    previous = RECENT_ARCHIVE_HINTS.get(key)
    if previous is not None and now - previous < ARCHIVE_AUTO_COOLDOWN_SECONDS:
        return False

    expired = [
        item for item, ts in RECENT_ARCHIVE_HINTS.items()
        if now - ts > ARCHIVE_AUTO_COOLDOWN_SECONDS * 2
    ]
    for item in expired:
        RECENT_ARCHIVE_HINTS.pop(item, None)

    RECENT_ARCHIVE_HINTS[key] = now
    return True


def technical_archive_terms(text_value: str) -> list[str]:
    """Términos para la búsqueda automática, con activación conservadora.

    La similitud/normalización sigue disponible DESPUÉS de detectar una consulta
    técnica, pero una conversación casual nunca debe disparar el buscador por
    similitudes accidentales.
    """
    terms = extract_archive_terms(text_value)
    if not terms:
        return []

    model_terms = archive_model_terms(text_value)
    family_terms = archive_family_terms(text_value)
    identifier_terms = archive_identifier_terms(text_value)

    strict_technical = strict_technical_archive_words(text_value)
    strict_families = strict_archive_family_terms(text_value)

    # Modelo explícito + señal técnica explícita: caso más seguro.
    # Ej.: "CPS para EM200", "firmware DEP450".
    if model_terms and strict_technical:
        return (strict_technical + strict_families + model_terms)[:8]

    # Familia/plataforma explícita + señal técnica explícita.
    # Ej.: "cps mototrbo", "crack mototrbo", "firmware apx".
    if strict_families and strict_technical:
        return (strict_technical + strict_families)[:8]

    # Identificador explícito + señal técnica explícita.
    # Ej.: "software KPG-D6".
    if identifier_terms and strict_technical:
        return (strict_technical + identifier_terms)[:8]

    # Para mensajes sin destino concreto, incluso dos palabras técnicas pueden
    # ser conversación general. No hacemos búsqueda automática. Si el usuario
    # nombra a Pecos, archive_query_from_natural_text puede pedir el destino.
    return []


def archive_name_similarity(name_a: str, name_b: str) -> float:
    a = archive_stem_for_similarity(name_a)
    b = archive_stem_for_similarity(name_b)
    if not a or not b:
        return 0.0
    return difflib.SequenceMatcher(None, a, b).ratio()


async def send_archive_search_results(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
    query: str,
    *,
    clean_command: bool = False,
) -> bool:
    chat = message.chat
    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        await message.reply_text("📦 La búsqueda del archivo de Pecos funciona dentro del grupo.")
        return True

    if clean_command:
        await delete_group_command_invocation(message, context)

    terms = extract_archive_terms(query)
    if not terms:
        await context.bot.send_message(
            chat_id=chat.id,
            text="🤠 Dime qué modelo, programa o palabra debo buscar. Ejemplo: «Pecos busca XPR7550»."
        )
        return True

    if archive_query_needs_target(query, terms):
        await context.bot.send_message(
            chat_id=chat.id,
            text=(
                "👀 Entendido. ¿Para qué modelo, familia o plataforma necesitas revisarlo? "
                "Por ejemplo: EM200, DEP450, MOTOTRBO o APX."
            ),
        )
        return True

    rows = search_archive_rows(chat.id, " ".join(terms))
    usuario = display_name(message)

    if not rows:
        await context.bot.send_message(
            chat_id=chat.id,
            text=(
                f"🌵 {usuario}, Pecos revisó el archivo del pueblo y no encontró coincidencias para "
                f"«{' '.join(terms)}»."
            ),
        )
        return True

    requested_models = archive_model_terms(query)
    found_models = {
        model
        for model in requested_models
        if any(archive_name_matches_model(str(row["file_name"] or ""), model) for row in rows)
    }
    missing_models = [model.upper() for model in requested_models if model not in found_models]

    lines = [
        f"📚 {usuario}, Pecos encontró {len(rows)} coincidencia(s) para «{' '.join(terms)}»:"
    ]
    lines.extend(archive_result_lines(chat, rows))
    if missing_models:
        lines.append(
            "\n🔎 También detecté " + ", ".join(missing_models)
            + ", pero no encontré un archivo que pueda asociar con suficiente seguridad "
              "a " + ("ese modelo" if len(missing_models) == 1 else "esos modelos") + "."
        )

    await context.bot.send_message(chat_id=chat.id, text="\n\n".join(lines))
    db.add_history(
        f"ARCHIVO BUSCADO | {usuario} | {' '.join(terms)} | resultados={len(rows)}"
    )
    return True


async def handle_archive_natural_query(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    if not message.text:
        return False
    query = archive_query_from_natural_text(message.text)
    if query is None:
        return False
    return await send_archive_search_results(message, context, query)


async def maybe_offer_related_files(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    if not message.text:
        return False
    if text_mentions_pecos(message.text):
        return False
    if len(message.text) > 350:
        return False

    terms = technical_archive_terms(message.text)
    if not terms:
        return False
    if not archive_hint_allowed(message.chat_id, terms):
        return False

    rows = search_archive_rows(message.chat_id, " ".join(terms), limit=3)
    if not rows:
        return False

    # Si solo existe una coincidencia, exigimos que haya un modelo alfanumérico explícito.
    has_model = any(any(c.isalpha() for c in t) and any(c.isdigit() for c in t) for t in terms)
    if len(rows) == 1 and not has_model:
        return False

    requested_models = archive_model_terms(message.text)
    found_models = {
        model
        for model in requested_models
        if any(archive_name_matches_model(str(row["file_name"] or ""), model) for row in rows)
    }
    missing_models = [model.upper() for model in requested_models if model not in found_models]

    lines = [
        f"👀 Pecos levantó una oreja: encontré {len(rows)} archivo(s) relacionado(s) con «{' '.join(terms)}»."
    ]
    lines.extend(archive_result_lines(message.chat, rows, max_items=3))
    if missing_models:
        lines.append(
            "\n🔎 También detecté " + ", ".join(missing_models)
            + ", pero no encontré un archivo que pueda asociar con suficiente seguridad "
              "a " + ("ese modelo" if len(missing_models) == 1 else "esos modelos") + "."
        )
    lines.append(f"\n📡 Para revisar más: «Pecos busca {' '.join(terms)}». ")

    await context.bot.send_message(chat_id=message.chat_id, text="\n\n".join(lines))
    return True


async def handle_file_detective(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    """
    Fase 3, modo detective.

    Se ejecuta DESPUÉS del detector de duplicados. Si el archivo era duplicado,
    handle_duplicate ya retornó True y esta función ni siquiera se invoca.
    Aquí solo analizamos archivos que Pecos registró como contenido nuevo.
    """
    if not message.document:
        return False

    file_name = getattr(message.document, "file_name", "") or ""
    if not archive_file_allowed(file_name):
        return False

    current = db.fingerprint_by_message(message.chat_id, message.message_id)
    if current is None:
        # Duplicados desactivados o huella aún no registrada: no inventamos conclusiones.
        return False

    current_sha = str(current["sha256"] or "")
    current_size = int(current["file_size"] or 0)
    candidates = [
        row for row in db.list_archive_fingerprints(message.chat_id)
        if int(row["message_id"]) != message.message_id
        and str(row["sha256"] or "") != current_sha
        and archive_file_allowed(str(row["file_name"] or ""))
    ]

    if not candidates:
        return False

    exact_name = None
    same_size = None
    family = None
    family_score = 0.0

    current_lower = file_name.casefold()
    for row in candidates:
        other_name = str(row["file_name"] or "")
        other_size = int(row["file_size"] or 0)
        similarity = archive_name_similarity(file_name, other_name)

        if exact_name is None and other_name.casefold() == current_lower:
            exact_name = row
            continue

        if (
            same_size is None
            and current_size > 0
            and other_size == current_size
            and similarity >= 0.50
        ):
            same_size = row

        if similarity > family_score:
            family_score = similarity
            family = row

    notice_type = ""
    related = None
    text_value = ""

    if exact_name is not None:
        notice_type = "same_name_new_hash"
        related = exact_name
        text_value = (
            f"🕵️ Pecos abrió la lupa: «{file_name}» ya existía con exactamente el mismo nombre, "
            "pero esta copia tiene una huella SHA-256 distinta. No es un duplicado exacto; "
            "puede ser otra versión o contenido modificado."
        )
    elif same_size is not None:
        notice_type = "same_size_new_hash"
        related = same_size
        text_value = (
            f"🎯 Pecos encontró algo curioso con «{file_name}»: coincide en tamaño con un archivo "
            "parecido del archivo histórico, pero la huella SHA-256 es diferente. Mismo peso, "
            "contenido distinto."
        )
    elif family is not None and family_score >= ARCHIVE_DETECTIVE_SIMILARITY:
        notice_type = "possible_version_family"
        related = family
        text_value = (
            f"📦 Pecos encontró un pariente de «{file_name}». El nombre se parece bastante a otro "
            "archivo del grupo, pero la huella es distinta. Puede tratarse de otra versión."
        )
    else:
        return False

    related_message_id = int(related["message_id"])
    if not db.claim_archive_detective_notice(
        message.chat_id,
        message.message_id,
        notice_type,
        related_message_id,
    ):
        return False

    related_name = str(related["file_name"] or "archivo")
    link = build_message_link(message.chat, related_message_id)
    text_value += f"\n\n📄 Relacionado: {related_name}"
    if link:
        text_value += f"\n🔗 {link}"
    text_value += "\n🤠 Pecos informa; no elimina ninguno porque sus contenidos no son idénticos."

    await context.bot.send_message(chat_id=message.chat_id, text=text_value)
    db.add_history(
        f"DETECTIVE ARCHIVO | {notice_type} | nuevo={file_name} relacionado={related_name}"
    )
    return True



HISTORY_SUCCESS_PATTERNS = (
    r"\bme funcion[oó]\b", r"\bya funcion[oó]\b", r"\bfuncion[oó] perfecto\b",
    r"\bfunciona perfecto\b", r"\bqued[oó] funcionando\b", r"\bqued[oó] listo\b",
    r"\bsolucionad[oa]\b", r"\bresuelto\b", r"\bera eso\b", r"\bera justo eso\b",
    r"\bit works\b", r"\bit worked\b", r"\bthat worked\b", r"\bworking now\b",
    r"\bsolved\b", r"\bfixed\b", r"\beverything worked out\b",
)

HISTORY_NEGATIVE_PATTERNS = (
    r"\bno me funcion", r"\bno funcion[oó]\b", r"\bno funciona\b", r"\bno sirve\b",
    r"\bno ayud", r"\bno pude\b", r"\bno puedo\b",
    r"\bsigue (?:igual|apareciendo|fallando)\b",
    r"\bmismo (?:error|problema)\b", r"\bdoesn['’]?t help\b",
    r"\bdidn['’]?t work\b", r"\bnot work\b", r"\bthanks anyway\b",
    r"\bgracias de todos modos\b",
)

HISTORY_TRY_PATTERNS = (
    r"\bvoy a (?:probar|intentar|buscar)\b", r"\blo voy a (?:probar|intentar)\b",
    r"\bprobar[eé]\b", r"\bintentar[eé]\b", r"\bi['’]?ll try\b", r"\bwill try\b",
)

HISTORY_REQUEST_PATTERNS = (
    r"\bbusco\b", r"\bbuscando\b", r"\bnecesito\b", r"\bme falta\b",
    r"\balguien tiene\b", r"\balguien puede compartir\b",
    r"\bme pueden pasar\b", r"\bme pueden enviar\b", r"\bnecesito ayuda\b",
    r"\btengo un problema\b", r"\bno me funciona\b", r"\bi need\b",
    r"\bi am looking for\b", r"\blooking for\b", r"\bdoes anyone have\b",
    r"\bneed help\b", r"\bplease help\b",
)

HISTORY_HELP_PATTERNS = (
    r"\busa\b", r"\butiliza\b", r"\bdebes\b", r"\btienes que\b", r"\bprueba\b",
    r"\bintenta\b", r"\binstala\b", r"\bdescarga\b", r"\bconfigura\b",
    r"\bcambia\b", r"\bactiva\b", r"\bdesactiva\b", r"\brevisa\b",
    r"\bverifica\b", r"\bpuedes usar\b", r"\bte recomiendo\b", r"\bsolucion\b",
    r"\buse\b", r"\byou need\b", r"\btry\b", r"\binstall\b", r"\bdownload\b",
    r"\bcheck\b", r"\bsolution\b", r"\bworks with\b", r"\byou can use\b",
)

HISTORY_SEARCH_STOPWORDS = {
    "a","al","algo","alguien","con","como","cual","cuando","de","del","donde",
    "el","en","es","esta","este","esto","gracias","hola","la","las","lo","los",
    "me","mi","no","para","pero","por","que","quien","se","si","su","tengo",
    "un","una","y","ya","ayuda","ayudar","favor","busco","buscando","necesito",
    "archivo","archivos","the","and","for","have","help","how","i","in","is","it",
    "need","of","on","or","please","the","this","to","what","where","with","you",
}

HISTORY_MODEL_PREFIXES = {
    "tk","xpr","dm","dp","dep","pd","gp","hp","apx","dgp","ic","icf",
    "bf","uv","md","rd","cp","r","ft","vx",
}


def history_feedback_kind(text_value: str) -> str:
    normalized = normalize_intent(text_value or "")
    if any(re.search(p, normalized) for p in HISTORY_NEGATIVE_PATTERNS):
        return "REJECTED"
    if any(re.search(p, normalized) for p in HISTORY_SUCCESS_PATTERNS):
        return "CONFIRMED"
    if any(re.search(p, normalized) for p in HISTORY_TRY_PATTERNS):
        return "WILL_TRY"
    if re.search(r"\b(gracias|thanks|thank you|te agradezco|muchas gracias)\b", normalized):
        return "ACKNOWLEDGED"
    return ""


def history_extract_search_terms(query: str) -> list[str]:
    normalized = normalize_intent(query or "")
    raw = re.findall(r"[a-z0-9_#+.\-]+", normalized)
    out: list[str] = []
    for token in raw:
        token = token.strip(".-_")
        if not token or token in HISTORY_SEARCH_STOPWORDS:
            continue
        if len(token) < 3 and not token.isdigit():
            continue
        if token not in out:
            out.append(token)
    return out[:10]


def history_model_anchor(query: str) -> str:
    normalized = normalize_intent(query or "")
    tokens = re.findall(r"[a-z0-9]+(?:[-./][a-z0-9]+)*", normalized)
    for token in tokens:
        compact = re.sub(r"[^a-z0-9]", "", token)
        if len(compact) >= 4 and re.search(r"[a-z]", compact) and re.search(r"\d", compact):
            return compact
    simple = re.findall(r"[a-z0-9]+", normalized)
    for i in range(len(simple) - 1):
        if simple[i] in HISTORY_MODEL_PREFIXES and re.fullmatch(r"\d+[a-z]?", simple[i + 1]):
            return simple[i] + simple[i + 1]
    return ""


def history_message_media_type(message: Message) -> str:
    if message.document:
        return "document"
    if message.photo:
        return "photo"
    if message.video:
        return "video"
    if message.audio:
        return "audio"
    if message.voice:
        return "voice"
    return ""


def history_memory_enabled_for_chat(chat_id: int) -> bool:
    return chat_id in HISTORY_MEMORY_GROUP_IDS


async def learn_historical_memory(
    message: Message,
    *,
    is_edited: bool = False,
) -> None:
    if not history_memory_enabled_for_chat(message.chat_id):
        return

    text_value = (message.text or message.caption or "").strip()
    if not text_value:
        return

    user = message.from_user
    sender_id = int(user.id) if user else 0
    sender_name = display_name(message)
    sender_username = (user.username or "") if user else ""
    parent_id = int(message.reply_to_message.message_id) if message.reply_to_message else 0

    try:
        date_utc = message.date.astimezone(ZoneInfo("UTC")).isoformat(timespec="seconds")
    except Exception:
        date_utc = datetime.now(ZoneInfo("UTC")).isoformat(timespec="seconds")

    edit_date_utc = ""
    if is_edited:
        try:
            edit_date_utc = message.edit_date.astimezone(ZoneInfo("UTC")).isoformat(timespec="seconds")
        except Exception:
            edit_date_utc = date_utc

    db.store_conversation_message(
        chat_id=message.chat_id,
        message_id=message.message_id,
        date_utc=date_utc,
        edit_date_utc=edit_date_utc,
        sender_id=sender_id,
        sender_name=sender_name,
        sender_username=sender_username,
        reply_to_message_id=parent_id,
        text_value=text_value,
        normalized_text=normalize_intent(text_value),
        message_link=build_message_link(message.chat, message.message_id) or "",
        media_type=history_message_media_type(message),
    )

    normalized = normalize_intent(text_value)
    is_question = int(looks_like_question(text_value))
    is_request = int(any(re.search(p, normalized) for p in HISTORY_REQUEST_PATTERNS))
    feedback = history_feedback_kind(text_value)
    is_closure = int(bool(feedback and parent_id))

    parent_cls = db.get_conversation_classification(message.chat_id, parent_id) if parent_id else None
    parent_is_need = bool(
        parent_cls and (int(parent_cls["is_question"] or 0) or int(parent_cls["is_request"] or 0))
    )

    is_answer = int(
        bool(parent_is_need and not is_question and not is_request and not is_closure)
    )
    helpful_hits = sum(1 for p in HISTORY_HELP_PATTERNS if re.search(p, normalized))
    is_helpful = int(bool(is_answer and (helpful_hits > 0 or len(text_value) >= 35)))
    root_id = message.message_id if (is_question or is_request) else (
        int(parent_cls["root_question_id"] or parent_id) if parent_cls else 0
    )

    primary = "NORMAL"
    if is_closure:
        primary = "THANKS_CLOSURE"
    elif is_request:
        primary = "REQUEST_HELP"
    elif is_question:
        primary = "QUESTION"
    elif is_helpful:
        primary = "HELP_PROBABLE"
    elif is_answer:
        primary = "ANSWER"

    db.upsert_conversation_classification(
        message.chat_id, message.message_id, primary,
        is_question, is_request, is_answer, is_helpful, is_closure, 0,
        4 if is_question else 0,
        5 if is_request else 0,
        4 if is_answer else 0,
        min(10, helpful_hits * 2 + (4 if parent_is_need else 0)),
        5 if is_closure else 0,
        parent_id, root_id,
        "aprendizaje_continuo_v2.8",
    )

    # Crear par inicial cuando alguien responde directamente a una necesidad.
    if is_answer and parent_cls:
        question_id = int(parent_cls["root_question_id"] or parent_id)
        db.upsert_conversation_pair(
            message.chat_id,
            question_id,
            message.message_id,
            0,
            0.70 if parent_id == question_id else 0.55,
            "PROBABLE",
            "aprendizaje_continuo: reply_a_consulta",
        )

    # Confirmación estricta: el cierre debe responder a una respuesta ya enlazada
    # y debe venir del mismo autor que originó la consulta.
    if is_closure and parent_id:
        pair = db.find_pair_by_answer(message.chat_id, parent_id)
        if pair:
            qrow = db.get_conversation_message(
                message.chat_id,
                int(pair["question_message_id"]),
            )
            same_author = bool(
                qrow and int(qrow["sender_id"] or 0) == sender_id
            )
            if same_author:
                status = feedback or "ACKNOWLEDGED"
                confidence = 0.99 if status == "CONFIRMED" else (
                    0.40 if status == "REJECTED" else float(pair["confidence"] or 0.70)
                )
                db.upsert_conversation_pair(
                    message.chat_id,
                    int(pair["question_message_id"]),
                    int(pair["answer_message_id"]),
                    message.message_id,
                    confidence,
                    status,
                    f"aprendizaje_continuo: autor_original_{status.lower()}",
                )
                if status == "CONFIRMED":
                    answer_cls = db.get_conversation_classification(
                        message.chat_id,
                        int(pair["answer_message_id"]),
                    )
                    if answer_cls:
                        db.upsert_conversation_classification(
                            message.chat_id,
                            int(pair["answer_message_id"]),
                            "SOLUTION_CONFIRMED",
                            int(answer_cls["is_question"] or 0),
                            int(answer_cls["is_request"] or 0),
                            1, 1, int(answer_cls["is_closure"] or 0), 1,
                            int(answer_cls["question_score"] or 0),
                            int(answer_cls["request_score"] or 0),
                            max(4, int(answer_cls["answer_score"] or 0)),
                            max(7, int(answer_cls["help_score"] or 0)),
                            int(answer_cls["closure_score"] or 0),
                            int(answer_cls["parent_message_id"] or 0),
                            int(answer_cls["root_question_id"] or 0),
                            "aprendizaje_continuo: solucion_confirmada_por_autor_original",
                        )


async def command_history_search(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
) -> None:
    message = update.effective_message
    chat = update.effective_chat
    user = update.effective_user
    if not message or not chat:
        return

    # Defensa adicional: /historial es una herramienta interna de Pecos y solo
    # los ADMIN_USER_IDS configurados pueden ejecutarla.
    if not user or not is_admin(user.id):
        if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
            await delete_group_command_invocation(message, context)
            await context.bot.send_message(
                chat_id=chat.id,
                text="🔒 Esta función está disponible solo para administradores de Pecos.",
            )
        return

    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        await message.reply_text("La búsqueda histórica se utiliza dentro de los grupos autorizados.")
        return

    await delete_group_command_invocation(message, context)

    if not history_memory_enabled_for_chat(chat.id):
        await context.bot.send_message(
            chat_id=chat.id,
            text="🧠 La memoria histórica no está habilitada en este grupo.",
        )
        return

    query = " ".join(context.args).strip()
    if not query:
        await context.bot.send_message(
            chat_id=chat.id,
            text="Uso: /historial DEP450\nEjemplo: /historial DM4601e firmware",
        )
        return

    terms = history_extract_search_terms(query)
    anchor = history_model_anchor(query)
    if anchor:
        terms = [t for t in terms if re.sub(r"[^a-z0-9]", "", t) != anchor]

    rows = db.search_conversation_history(
        HISTORY_SOURCE_CHAT_ID,
        terms,
        anchor,
        limit=8,
    )

    if not rows:
        await context.bot.send_message(
            chat_id=chat.id,
            text=f"🌵 Pecos no encontró conversaciones históricas para «{query}».",
        )
        return

    lines = [f"🧠 Pecos encontró {len(rows)} resultado(s) históricos para «{query}»:"]
    shown_confirmed_pairs: set[tuple[int, int]] = set()
    shown_messages: set[int] = set()
    shown_count = 0

    for row in rows:
        message_id = int(row["message_id"] or 0)
        if message_id in shown_messages:
            continue

        status = str(row["pair_status"] or "")
        question_id = int(row["question_message_id"] or 0)
        answer_id = int(row["answer_message_id"] or 0)
        confirmation_id = int(row["confirmation_message_id"] or 0)

        # Si existe una solución confirmada, no mostramos solo la pregunta:
        # presentamos pregunta + respuesta útil + confirmación del autor.
        if status == "CONFIRMED" and question_id and answer_id:
            pair_key = (question_id, answer_id)
            if pair_key in shown_confirmed_pairs:
                shown_messages.add(message_id)
                continue

            qrow = db.get_conversation_message(HISTORY_SOURCE_CHAT_ID, question_id)
            arow = db.get_conversation_message(HISTORY_SOURCE_CHAT_ID, answer_id)
            crow = (
                db.get_conversation_message(HISTORY_SOURCE_CHAT_ID, confirmation_id)
                if confirmation_id else None
            )

            if qrow and arow:
                shown_count += 1
                qtext = " ".join(str(qrow["text"] or "").split())
                atext = " ".join(str(arow["text"] or "").split())
                ctext = " ".join(str(crow["text"] or "").split()) if crow else ""
                if len(qtext) > 280:
                    qtext = qtext[:277] + "..."
                if len(atext) > 500:
                    atext = atext[:497] + "..."
                if len(ctext) > 220:
                    ctext = ctext[:217] + "..."

                item = (
                    f"{shown_count}. ✅ SOLUCIÓN CONFIRMADA\n"
                    f"   ❓ Consulta: {qtext}\n"
                    f"   💡 Solución: {atext}"
                )
                if ctext:
                    item += f"\n   ✅ Confirmación: {ctext}"
                if qrow["message_link"]:
                    item += f"\n   🔗 Consulta: {qrow['message_link']}"
                if arow["message_link"]:
                    item += f"\n   🔗 Solución: {arow['message_link']}"
                lines.append(item)
                shown_confirmed_pairs.add(pair_key)
                shown_messages.update({message_id, question_id, answer_id})
                if confirmation_id:
                    shown_messages.add(confirmation_id)
                continue

        shown_count += 1
        shown_messages.add(message_id)
        label = str(row["primary_label"] or "NORMAL")
        text_out = " ".join(str(row["text"] or "").split())
        if len(text_out) > 320:
            text_out = text_out[:317] + "..."
        item = f"{shown_count}. [{label}"
        if status:
            item += f" · {status}"
        item += f"] {text_out}"
        if row["message_link"]:
            item += f"\n   🔗 {row['message_link']}"
        lines.append(item)

    await send_long_text(chat.id, "\n\n".join(lines), context)


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



async def delete_group_command_invocation(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    """
    En grupos, elimina el mensaje /comando del usuario para que el chat quede
    limpio. Telegram puede mostrar /comando@NombreDelBot al seleccionar un
    comando desde el menú; eso lo decide el cliente de Telegram. Pecos no puede
    cambiar cómo se escribe antes de enviarlo, pero sí puede retirar el mensaje
    inmediatamente después de recibirlo.

    Devuelve True si el chat es grupo/supergrupo, aunque Telegram no permita
    borrar el mensaje. La respuesta del bot igualmente se enviará como mensaje
    independiente y nunca como reply.
    """
    chat = message.chat
    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        return False

    with contextlib.suppress(TelegramError):
        await context.bot.delete_message(
            chat_id=chat.id,
            message_id=message.message_id,
        )
    return True


async def send_clean_command_text(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
    text: str,
    reply_markup: InlineKeyboardMarkup | None = None,
) -> None:
    """
    En grupos:
      1) retira el /comando del usuario;
      2) envía la respuesta de Pecos como mensaje independiente.

    En privado conserva el comportamiento normal de reply_text.
    """
    is_group = await delete_group_command_invocation(message, context)

    if is_group:
        await context.bot.send_message(
            chat_id=message.chat_id,
            text=text,
            reply_markup=reply_markup,
        )
    else:
        await message.reply_text(text, reply_markup=reply_markup)



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
        "• encuestas, recuerdos, humor, bromas internas y reacciones\n• memoria básica de usuarios, avisos contextuales y detector de silencio con personalidad\n• archivo inteligente: búsqueda, relaciones y modo detective\n• reconocimiento de aportes y detector de preguntas repetidas\n"
        "• administración privada mediante botones"
    )

    if chat.type == ChatType.PRIVATE:
        text += "\n\n¿Qué quieres hacer?"
        await message.reply_text(text, reply_markup=start_menu())
    else:
        await send_clean_command_text(message, context, text)


async def command_id(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    user = update.effective_user
    chat = update.effective_chat
    if not message or not user or not chat:
        return

    if chat.type != ChatType.PRIVATE:
        await send_clean_command_text(message, context, "🆔 Por seguridad, pregúntame tu ID por chat privado.")
        return

    await message.reply_text(f"🆔 Tu Telegram User ID es:\n\n{user.id}")


async def command_config(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    user = update.effective_user
    chat = update.effective_chat
    if not message or not user or not chat:
        return

    if chat.type != ChatType.PRIVATE:
        await send_clean_command_text(message, context, "⚙️ La configuración solo está disponible por chat privado.")
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

    # En grupos retiramos el comando inmediatamente. context.args ya fue
    # interpretado por python-telegram-bot, por lo que no perdemos sus datos.
    is_group = await delete_group_command_invocation(message, context)

    async def respond(text_value: str) -> None:
        if is_group:
            await context.bot.send_message(chat_id=chat.id, text=text_value)
        else:
            await message.reply_text(text_value)

    raw = " ".join(context.args).strip()
    if not raw:
        await respond(
            "Uso:\n"
            "/encuesta ¿Asado sábado?\n\n"
            "O con opciones propias:\n"
            "/encuesta ¿Qué comemos? | Pizza | Asado | Empanadas"
        )
        return

    parts = [p.strip() for p in raw.split("|") if p.strip()]
    question = parts[0]

    if not (1 <= len(question) <= 300):
        await respond("La pregunta debe tener entre 1 y 300 caracteres.")
        return

    options = parts[1:] if len(parts) >= 3 else ["Sí", "No", "Quizás"]
    options = options[:10]

    if len(options) < 2:
        await respond("Necesito al menos dos opciones.")
        return

    try:
        await context.bot.send_poll(
            chat_id=chat.id,
            question=question,
            options=options,
            is_anonymous=False,
        )
    except TelegramError as exc:
        await respond(f"No pude crear la encuesta: {exc}")


async def command_remember(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    chat = update.effective_chat
    user = update.effective_user
    if not message or not chat or not user:
        return

    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        await message.reply_text("«Pecos recuerda» está pensado para usarse dentro del grupo.")
        return

    # El comando desaparece; Pecos responde como mensaje normal.
    await delete_group_command_invocation(message, context)

    memory_text = " ".join(context.args).strip()
    if not memory_text:
        await context.bot.send_message(
            chat_id=chat.id,
            text="Uso:\n/recordar reunión viernes 20:00",
        )
        return

    if len(memory_text) > 800:
        await context.bot.send_message(
            chat_id=chat.id,
            text="Ese recuerdo es demasiado largo. Máximo 800 caracteres.",
        )
        return

    memory_id = db.add_memory(
        chat.id,
        memory_text,
        user.id,
        display_name(message),
    )

    await context.bot.send_message(
        chat_id=chat.id,
        text=(
            f"🧠 Pecos lo recuerda. ID #{memory_id}\n"
            f"«{memory_text}»"
        ),
    )


async def command_memories(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    chat = update.effective_chat
    if not message or not chat:
        return

    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        await message.reply_text("Los recuerdos pertenecen a cada grupo.")
        return

    await delete_group_command_invocation(message, context)

    rows = db.list_memories(chat.id, 30)

    if not rows:
        await context.bot.send_message(
            chat_id=chat.id,
            text="🧠 Pecos no tiene recuerdos guardados en este grupo.",
        )
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

    is_group = await delete_group_command_invocation(message, context)

    async def respond(text_value: str) -> None:
        if is_group:
            await context.bot.send_message(chat_id=chat.id, text=text_value)
        else:
            await message.reply_text(text_value)

    if not context.args or not context.args[0].isdigit():
        await respond("Uso: /olvidar 12")
        return

    memory_id = int(context.args[0])
    deleted = db.delete_memory(
        chat.id,
        memory_id,
        user.id,
        is_admin(user.id),
    )

    if deleted:
        await respond(f"🧠 Pecos olvidó el recuerdo #{memory_id}.")
    else:
        await respond(
            "No encontré ese recuerdo o no tienes permiso para borrarlo."
        )


async def command_activity(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not message or not chat:
        return
    if not user or not is_admin(user.id):
        if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
            await delete_group_command_invocation(message, context)
            await context.bot.send_message(chat_id=chat.id, text="🔒 Esta función está disponible solo para administradores de Pecos.")
        return
    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        await message.reply_text("📊 /actividad se utiliza dentro de un grupo autorizado.")
        return
    await delete_group_command_invocation(message, context)
    entries = build_member_activity_snapshot(chat.id)
    if not entries:
        await context.bot.send_message(chat_id=chat.id, text="📊 Pecos todavía no tiene actividad observada para este grupo.")
        return
    query = " ".join(context.args).strip()
    if query:
        matches = find_activity_entries(entries, query)
        if not matches:
            await context.bot.send_message(chat_id=chat.id, text=f"📊 No encontré actividad registrada para «{query}».")
            return
        if len(matches) > 1:
            sample = "\n".join(f"• {activity_person_label(e)} · ID {e['user_id']}" for e in matches[:8])
            await context.bot.send_message(chat_id=chat.id, text=f"📊 Encontré varias coincidencias para «{query}»:\n{sample}\n\nUsa /actividad @usuario o /actividad USER_ID para precisar.")
            return
        entry = matches[0]
        last_seen = entry.get("last_seen") if isinstance(entry.get("last_seen"), datetime) else None
        icon, state = activity_status(last_seen)
        member_status = "no verificado"
        try:
            member = await context.bot.get_chat_member(chat_id=chat.id, user_id=int(entry["user_id"]))
            member_status = telegram_member_status_label(str(member.status))
        except TelegramError:
            pass
        await context.bot.send_message(chat_id=chat.id, text=(
            f"📊 Actividad observada de {activity_person_label(entry)}\n\n"
            f"{icon} Estado por actividad: {state}\n"
            f"🕒 Última actividad observada: {format_activity_timestamp(last_seen)} ({human_activity_age(last_seen)})\n"
            f"💬 Mensajes registrados: {int(entry.get('message_count') or 0)}\n"
            f"📅 Mensajes registrados últimos 30 días: {int(entry.get('messages_30d') or 0)}\n"
            f"👥 Estado actual consultado a Telegram: {member_status}\n"
            f"🆔 User ID: {int(entry['user_id'])}\n\n"
            "ℹ️ Esto no es la «última conexión» de Telegram; es la última actividad que Pecos pudo observar en el grupo."
        ))
        return
    buckets={"ACTIVO":0,"POCO ACTIVO":0,"INACTIVO":0,"MUY INACTIVO":0}
    for entry in entries:
        last_seen=entry.get("last_seen") if isinstance(entry.get("last_seen"),datetime) else None
        _, state=activity_status(last_seen); buckets[state]+=1
    report=build_activity_text_report(chat.title or str(chat.id), entries)
    payload=io.BytesIO(report.encode("utf-8-sig")); payload.name="pecos_actividad_"+datetime.now(BOT_TZ).strftime("%Y-%m-%d_%H%M")+".txt"
    caption=(f"📊 Actividad observada por Pecos\n👥 Usuarios con registro: {len(entries)}\n🟢 Activos (0–30 d): {buckets['ACTIVO']}\n🟡 Poco activos (31–90 d): {buckets['POCO ACTIVO']}\n🟠 Inactivos (91–180 d): {buckets['INACTIVO']}\n🔴 Muy inactivos (>180 d): {buckets['MUY INACTIVO']}\n\n📄 Adjunto va el detalle completo.\nℹ️ Mide actividad observada, no última conexión a Telegram.")
    await context.bot.send_document(chat_id=chat.id, document=payload, caption=caption)


async def command_inactive(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not message or not chat:
        return
    if not user or not is_admin(user.id):
        if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
            await delete_group_command_invocation(message, context)
            await context.bot.send_message(chat_id=chat.id, text="🔒 Esta función está disponible solo para administradores de Pecos.")
        return
    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        await message.reply_text("📊 /inactivos se utiliza dentro de un grupo autorizado.")
        return
    await delete_group_command_invocation(message, context)
    days=90
    if context.args:
        try: days=int(context.args[0])
        except ValueError:
            await context.bot.send_message(chat_id=chat.id,text="Uso: /inactivos 90\nEl número corresponde a días sin actividad observada."); return
    if not 1 <= days <= 3650:
        await context.bot.send_message(chat_id=chat.id,text="El rango permitido es entre 1 y 3650 días."); return
    entries=build_member_activity_snapshot(chat.id)
    inactive=[e for e in entries if activity_age_days(e.get("last_seen") if isinstance(e.get("last_seen"),datetime) else None)>=days]
    if not inactive:
        await context.bot.send_message(chat_id=chat.id,text=f"📊 No encontré usuarios con {days} días o más sin actividad observada."); return
    report=build_activity_text_report(chat.title or str(chat.id),entries,inactive_days=days)
    payload=io.BytesIO(report.encode("utf-8-sig")); payload.name=f"pecos_inactivos_{days}d_"+datetime.now(BOT_TZ).strftime("%Y-%m-%d_%H%M")+".txt"
    await context.bot.send_document(chat_id=chat.id,document=payload,caption=(f"📊 Pecos encontró {len(inactive)} usuario(s) con {days} días o más sin actividad observada.\n\n📄 Adjunto va el detalle.\nℹ️ No significa que no entren a Telegram ni que sigan siendo miembros; solo que Pecos no ha observado actividad reciente de ellos en el grupo."))


async def command_search_archive(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    if not message:
        return

    query = " ".join(context.args).strip()
    await send_archive_search_results(
        message,
        context,
        query,
        clean_command=True,
    )


async def command_pecos(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    if message:
        await send_clean_command_text(
            message,
            context,
            choose_random(
                "pecos_command",
                PECOS_CALLED_MESSAGES,
                display_name(message),
            ),
        )


async def command_advice(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    if message:
        await send_clean_command_text(
            message,
            context,
            random.choice(ADVICE_MESSAGES),
        )


async def command_phrase(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    if message:
        await send_clean_command_text(
            message,
            context,
            random.choice(PHRASE_MESSAGES),
        )


async def command_excuse(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    if message:
        await send_clean_command_text(
            message,
            context,
            random.choice(EXCUSE_MESSAGES),
        )


async def command_forecast(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    if message:
        await send_clean_command_text(
            message,
            context,
            random.choice(FORECAST_MESSAGES),
        )


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
            f"Archivos de hash: temporal ({TELEGRAM_FILES_DIR})\n"
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
        detail = (
            "• 1.º FileUniqueId: detección rápida cuando Telegram reconoce el mismo archivo.\n"
            "• 2.º Tamaño y nombre: señales previas, nunca veredicto final.\n"
            "• 3.º SHA-256: compara el contenido real aunque cambie el nombre.\n"
            "• Los archivos se materializan solo en /tmp y se borran al terminar el hash.\n"
            "• En el volumen quedan únicamente pecos.db y el estado pequeño del Bot API local."
        )

        await query.message.reply_text(
            "ℹ️ Duplicados en Pecos\n\n"
            + detail
            + "\n\nLa fecha se conserva para informar cuándo apareció el original, "
              "pero no se usa como prueba de igualdad."
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


def cleanup_ephemeral_file(path: Path | None) -> None:
    """
    Borra solo archivos del directorio efímero del Bot API local.
    Nunca elimina archivos dentro del volumen persistente /data.
    """
    if path is None:
        return

    try:
        root = TELEGRAM_FILES_DIR.resolve()
        target = path.resolve()
        target.relative_to(root)
    except Exception:
        log.warning(
            "LIMPIEZA omitida: ruta fuera de temporales | ruta=%s | root=%s",
            path,
            TELEGRAM_FILES_DIR,
        )
        return

    try:
        target.unlink(missing_ok=True)
        log.info("TEMP eliminado | archivo=%s", target.name)
    except OSError as exc:
        log.warning("No se pudo borrar temporal %s: %s", target, exc)


async def get_file_resilient(
    context: ContextTypes.DEFAULT_TYPE,
    file_id: str,
    file_name: str,
    file_size: int,
):
    """
    Obtiene el archivo desde la Bot API local con reintentos.

    Telegram Bot API local puede responder temporalmente con
    "Wrong file_id or the file is temporarily unavailable" mientras
    materializa archivos grandes. También reintenta cortes breves del
    servidor local.
    """
    delays = (0, 2, 4, 8, 12, 20, 30)
    last_exc: Exception | None = None

    for attempt, delay in enumerate(delays, start=1):
        if delay:
            await asyncio.sleep(delay)

        try:
            return await context.bot.get_file(file_id)
        except BadRequest as exc:
            text = str(exc).casefold()
            retryable = (
                "wrong file_id" in text
                or "temporarily unavailable" in text
            )
            if not retryable:
                raise
            last_exc = exc
        except NetworkError as exc:
            last_exc = exc

        log.warning(
            "GETFILE temporal | intento=%s/%s | archivo=%s | size=%s | error=%s",
            attempt,
            len(delays),
            file_name,
            file_size,
            type(last_exc).__name__ if last_exc else "desconocido",
        )

    if last_exc is not None:
        raise last_exc

    raise RuntimeError(f"No se pudo obtener getFile para {file_name}")


def build_message_link(chat: Chat, message_id: int) -> str | None:
    """
    Construye un enlace directo al mensaje original sin tocar la lógica
    de duplicados.

    - Grupo/supergrupo público: https://t.me/usuario/message_id
    - Supergrupo privado:       https://t.me/c/id_interno/message_id

    Si Telegram no permite construir un enlace directo para ese tipo de chat,
    devuelve None.
    """
    username = getattr(chat, "username", None)

    if username:
        return f"https://t.me/{username}/{message_id}"

    chat_id_text = str(chat.id)

    if chat_id_text.startswith("-100"):
        internal_id = chat_id_text[4:]
        if internal_id:
            return f"https://t.me/c/{internal_id}/{message_id}"

    return None


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
    Detección final de duplicados:
    1) FileUniqueId como vía rápida.
    2) Tamaño/nombre/fecha como señales y metadatos.
    3) SHA-256 del contenido como veredicto definitivo.

    El Bot API local guarda los archivos descargados en /tmp mediante
    --files-dir. Pecos calcula SHA-256 por bloques y borra el temporal
    inmediatamente, por lo que los .rar no quedan en el volumen.
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
        # 1) Vía rápida: Telegram ya conoce exactamente ese archivo.
        if unique_id and db.unique_file_seen(chat_id, unique_id, message_id):
            try:
                await context.bot.delete_message(
                    chat_id=chat_id,
                    message_id=message_id,
                )
                funny_text = random.choice(DUPLICATE_QUICK_MESSAGES)
                await context.bot.send_message(
                    chat_id=chat_id,
                    text=(
                        funny_text
                        + "\n\n"
                        + f"📄 Archivo: {file_name}\n"
                        + "🔎 Pecos lo reconoció al instante."
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

        # 2) Señales previas. No son prueba suficiente por sí solas.
        same_size, same_name_size = db.duplicate_precheck(
            chat_id,
            file_size,
            file_name,
        )

        try:
            received_at = message.date.astimezone(BOT_TZ).strftime("%Y-%m-%d %H:%M:%S")
        except Exception:
            received_at = ""

        log.info(
            "PRECHECK | archivo=%s | size=%s | mismo_tamano=%s "
            "| mismo_nombre_tamano=%s | fecha=%s",
            file_name,
            file_size,
            same_size,
            same_name_size,
            received_at,
        )

        # 3) Veredicto exacto por contenido.
        async with HASH_SEMAPHORE:
            if not LOCAL_BOT_API:
                raise RuntimeError(
                    "La detección exacta de archivos grandes requiere LOCAL_BOT_API=1."
                )

            started = time.monotonic()
            local_path: Path | None = None

            try:
                telegram_file = await get_file_resilient(
                    context,
                    file_id,
                    file_name,
                    file_size,
                )

                raw_file_path = getattr(telegram_file, "file_path", None)
                local_path = resolve_local_file_path(raw_file_path)

                if local_path is None:
                    raise RuntimeError(
                        "Bot API local no entregó una ruta absoluta accesible: "
                        f"{raw_file_path!r}"
                    )

                # Nunca permitimos que el hash trabaje sobre /data.
                try:
                    local_path.resolve().relative_to(TELEGRAM_FILES_DIR.resolve())
                except Exception as exc:
                    raise RuntimeError(
                        f"Ruta fuera del directorio temporal permitido: {local_path}"
                    ) from exc

                actual_size = await wait_for_complete_local_file(
                    local_path,
                    file_size,
                    timeout_seconds=300,
                )

                sha256 = await asyncio.to_thread(
                    sha256_file,
                    local_path,
                )

                elapsed = time.monotonic() - started
                log.info(
                    "SHA-256 calculado | archivo=%s | informado=%s | local=%s "
                    "| tiempo=%.2fs | digest=%s...",
                    file_name,
                    file_size,
                    actual_size,
                    elapsed,
                    sha256[:12],
                )

            finally:
                # También limpia si el hash falla.
                cleanup_ephemeral_file(local_path)

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

        # SQLite confirmó que ya existía exactamente el mismo contenido.
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

            original_message_id = int(original["message_id"])
            original_link = build_message_link(
                message.chat,
                original_message_id,
            )

            funny_text = random.choice(DUPLICATE_HASH_MESSAGES)

            message_text = (
                funny_text
                + "\n\n"
                + f"📄 Original: {original_name}\n"
            )

            if original_link:
                message_text += f"🔗 Archivo original: {original_link}\n"

            message_text += (
                f"👤 Enviado por: {original_sender}\n"
                f"🕘 Primera vez: {first_seen_text}"
            )

            duplicate_count = increment_user_metric(message, "duplicate_count")
            await context.bot.send_message(
                chat_id=chat_id,
                text=message_text + repeat_warning_text("duplicate", duplicate_count),
            )

            if unique_id:
                db.store_unique_file(chat_id, unique_id, message_id)

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

    restricted_count = increment_user_metric(message, "restricted_count")
    response = (
        choose_random("moderation", FUN_MODERATION_MESSAGES, usuario)
        + repeat_warning_text("restricted", restricted_count)
    )
    try:
        await context.bot.send_message(chat_id=message.chat_id, text=response)
        mark_pecos_context(message.chat_id)
    except TelegramError as exc:
        log.warning("Mensaje eliminado, pero no se pudo publicar respuesta: %s", exc)

    db.add_history(
        f"MENSAJE RETIRADO | {usuario} | chat {message.chat_id} | término: {blocked}"
    )
    return True


def mark_new_member(chat_id: int, user_id: int) -> None:
    """
    Registra el instante en que un usuario entra al grupo.
    El dato es temporal y solo vive en memoria durante unos segundos.
    """
    now = time.monotonic()

    # Limpieza perezosa para evitar acumular entradas antiguas.
    expired = [
        key
        for key, joined_at in NEW_MEMBER_JOINED_AT.items()
        if now - joined_at > NEW_MEMBER_RULE_WINDOW_SECONDS + 10
    ]
    for key in expired:
        NEW_MEMBER_JOINED_AT.pop(key, None)

    NEW_MEMBER_JOINED_AT[(chat_id, user_id)] = now


def is_new_member_within_rule_window(chat_id: int, user_id: int) -> bool:
    joined_at = NEW_MEMBER_JOINED_AT.get((chat_id, user_id))
    if joined_at is None:
        return False

    elapsed = time.monotonic() - joined_at
    if elapsed <= NEW_MEMBER_RULE_WINDOW_SECONDS:
        return True

    NEW_MEMBER_JOINED_AT.pop((chat_id, user_id), None)
    return False


def looks_like_question(text_value: str) -> bool:
    """
    Detecta preguntas explícitas y consultas típicas sin exigir siempre '?'.
    Se mantiene deliberadamente conservador para no molestar a quien solo saluda.
    """
    if not text_value:
        return False

    normalized = normalize_intent(text_value).strip()

    if "?" in text_value:
        return True

    question_patterns = (
        r"\bcomo\b",
        r"\bdonde\b",
        r"\bcuando\b",
        r"\bquien\b",
        r"\bquienes\b",
        r"\bcual\b",
        r"\bcuales\b",
        r"\bpor que\b",
        r"\balguien sabe\b",
        r"\balguien tiene\b",
        r"\bsaben si\b",
        r"\btienen\b",
        r"\bpueden\b",
        r"\bme pueden\b",
        r"\bconsulta\b",
        r"\bbusco\b",
        r"\bnecesito\b",
    )

    return any(re.search(pattern, normalized) for pattern in question_patterns)


async def handle_new_member_question(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    """
    Si un usuario recién ingresado pregunta dentro de los primeros 30 segundos,
    Pecos le recuerda con ironía que revise reglas y archivos.

    Responde una sola vez por ingreso y nunca molesta a administradores.
    """
    user = message.from_user
    if not user or user.is_bot:
        return False

    key = (message.chat_id, user.id)

    if not is_new_member_within_rule_window(message.chat_id, user.id):
        return False

    text_value = message.text or message.caption or ""
    if not looks_like_question(text_value):
        return False

    # Administradores de Pecos: nunca reciben este aviso.
    if is_admin(user.id):
        NEW_MEMBER_JOINED_AT.pop(key, None)
        return False

    # Administradores reales del grupo tampoco reciben el aviso.
    try:
        member = await context.bot.get_chat_member(message.chat_id, user.id)
        status = str(getattr(member, "status", "")).lower()
        if status in {"administrator", "creator", "owner"}:
            NEW_MEMBER_JOINED_AT.pop(key, None)
            return False
    except TelegramError:
        # Si Telegram no permite consultar el estado, no bloqueamos la función.
        pass

    # Una sola intervención por ingreso.
    NEW_MEMBER_JOINED_AT.pop(key, None)

    usuario = display_name(message)
    rule_count = increment_user_metric(message, "rule_reminder_count")
    await message.reply_text(
        choose_random(
            "new_user_rules",
            NEW_USER_RULE_MESSAGES,
            usuario,
        )
        + repeat_warning_text("rule", rule_count)
    )

    db.add_history(
        f"REGLAS NUEVO USUARIO | {usuario} preguntó dentro de "
        f"{NEW_MEMBER_RULE_WINDOW_SECONDS}s en chat {message.chat_id}."
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
    mentions_pecos = text_mentions_pecos(message.text)

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
        # Abre una ventana de 30 segundos para detectar preguntas inmediatas.
        mark_new_member(message.chat_id, member.id)

        if member.username:
            usuario = f"@{member.username}"
        else:
            usuario = member.full_name or str(member.id)

        await message.reply_text(
            choose_random("welcome", WELCOME_MESSAGES, usuario)
        )

        db.add_history(f"BIENVENIDA a {usuario} en chat {message.chat_id}.")

    return True


async def handle_band_conversion_joke(message: Message) -> bool:
    """
    Broma técnica para preguntas sobre convertir un equipo VHF a UHF o viceversa.

    Solo se activa cuando aparecen ambas bandas y además hay una intención clara
    de conversión. No se dispara por una conversación normal que simplemente
    mencione VHF y UHF.
    """
    text_value = message.text or message.caption or ""
    if not text_value or not message.from_user or message.from_user.is_bot:
        return False

    normalized = normalize_intent(text_value).strip()
    if not normalized:
        return False

    has_vhf = bool(re.search(r"(?<!\w)vhf(?!\w)", normalized))
    has_uhf = bool(re.search(r"(?<!\w)uhf(?!\w)", normalized))
    if not (has_vhf and has_uhf):
        return False

    conversion_signal = bool(re.search(
        r"\b(?:pasar|pasa|pasarlo|pasarla|convertir|convierto|convertirse|"
        r"cambiar|cambio|cambiarlo|cambiarla|transformar|transformarlo|"
        r"modificar|modificarlo|hacer|hacerlo)\b",
        normalized,
    ))
    if not conversion_signal:
        return False

    # Exige una dirección de conversión reconocible.
    vhf_to_uhf = bool(re.search(
        r"(?:vhf.{0,40}(?:a|en|para)\s+uhf|de\s+vhf.{0,30}(?:a|en|para)\s+uhf)",
        normalized,
    ))
    uhf_to_vhf = bool(re.search(
        r"(?:uhf.{0,40}(?:a|en|para)\s+vhf|de\s+uhf.{0,30}(?:a|en|para)\s+vhf)",
        normalized,
    ))
    if not (vhf_to_uhf or uhf_to_vhf):
        return False

    if vhf_to_uhf:
        joke = (
            "🤠 Pasar un VHF a UHF es casi como pedirle a un árbol que "
            "florezca billetes… bonito sería, pero no funciona así, partner. 😂"
        )
        direction = "VHF → UHF"
    else:
        joke = (
            "🤠 Pasar un UHF a VHF es casi como pedirle a un árbol que "
            "florezca billetes… bonito sería, pero no funciona así, partner. 😂"
        )
        direction = "UHF → VHF"

    await message.reply_text(
        joke
        + "\n\n📡 Normalmente no es un cambio de CPS o programación: "
          "el equipo necesita hardware de RF diseñado para esa banda. "
          "Si das el modelo exacto, Pecos puede revisar si existe alguna excepción o variante."
    )
    db.add_history(
        f"BROMA CONVERSION BANDA {direction} | {display_name(message)} | chat {message.chat_id}"
    )
    return True


async def handle_melerix_fun(message: Message) -> bool:
    """
    Broma especial para la palabra clave Melerix.

    - Cada usuario normal obtiene UNA sola respuesta por grupo, para evitar abuso.
    - Los usos posteriores del mismo usuario se ignoran silenciosamente.
    - El/los OWNER_USER_IDS pueden activar la broma todas las veces que quieran.
    - El control de uso queda persistido en SQLite.
    """
    text_value = message.text or message.caption or ""
    if not text_value or not message.from_user or message.from_user.is_bot:
        return False

    normalized = normalize_intent(text_value)
    if not re.search(r"(?<!\w)melerix(?!\w)", normalized):
        return False

    user_id = int(message.from_user.id)

    if not is_owner(user_id):
        first_use = db.claim_fun_keyword_once(
            message.chat_id,
            user_id,
            "melerix",
        )
        if not first_use:
            # Silencio intencional y total para este mensaje: ya consumió su única respuesta.
            # Retornamos True para que on_message no continúe con otros respondedores de Pecos.
            return True

    await message.reply_text(
        choose_random(
            "melerix_fun",
            MELERIX_FUN_MESSAGES,
            display_name(message),
        )
    )

    db.add_history(
        f"BROMA MELERIX | {display_name(message)} | chat {message.chat_id}"
    )
    return True


def message_references_xerax(message: Message) -> bool:
    """Detecta mención textual/@username o respuesta directa a @XeraX."""
    text_value = message.text or message.caption or ""
    if text_value:
        normalized = normalize_intent(text_value)
        if re.search(r"(?<!\w)@?xerax(?!\w)", normalized):
            return True

    replied = message.reply_to_message
    replied_user = replied.from_user if replied else None
    replied_username = (replied_user.username or "").casefold() if replied_user else ""
    return replied_username == XERAX_USERNAME


async def handle_xerax_fun(message: Message) -> bool:
    """
    Broma especial para XeraX.

    - Se activa por XeraX/@XeraX en el texto o al responder directamente a @XeraX.
    - Cada usuario normal obtiene UNA sola respuesta por grupo.
    - Menciones posteriores del mismo usuario quedan en silencio.
    - El OWNER puede activarla ilimitadamente.
    - Usa una clave separada de Melerix, por lo que ambos límites son independientes.
    """
    if not message.from_user or message.from_user.is_bot:
        return False

    if not message_references_xerax(message):
        return False

    user_id = int(message.from_user.id)

    if not is_owner(user_id):
        first_use = db.claim_fun_keyword_once(
            message.chat_id,
            user_id,
            "xerax",
        )
        if not first_use:
            # Ya usó su oportunidad XeraX: Pecos queda completamente en silencio
            # para este mensaje y no deja que otro handler responda por accidente.
            return True

    await message.reply_text(
        choose_random(
            "xerax_fun",
            XERAX_FUN_MESSAGES,
            display_name(message),
        )
    )

    db.add_history(
        f"BROMA XERAX | {display_name(message)} | chat {message.chat_id}"
    )
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

    if not text_mentions_pecos(message.text):
        return False

    usuario = display_name(message)
    increment_user_metric(message, "pecos_mention_count")

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
        "pecos esta pendiente" in normalized
        or "peco esta pendiente" in normalized
        or "pecos siempre esta pendiente" in normalized
        or "peco siempre esta pendiente" in normalized
        or "pecos esta atento" in normalized
        or "peco esta atento" in normalized
        or "pecos siempre atento" in normalized
        or "peco siempre atento" in normalized
        or "pecos no se le escapa" in normalized
        or "a pecos no se le escapa" in normalized
    ):
        await message.reply_text(
            choose_random("pecos_attentive", PECOS_ATTENTIVE_MESSAGES, usuario)
        )
        return True

    if (
        "estas ahi" in normalized
        or "estas aqui" in normalized
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


async def handle_contextual_phrase(message: Message) -> bool:
    """
    Respuestas contextuales de Fase 1.

    Las señales fuertes responden siempre la primera vez dentro del cooldown.
    El cooldown se aplica por tipo concreto de frase, de modo que probar
    "me rindo" y luego "no funciona" produce dos respuestas distintas,
    pero repetir la misma idea muchas veces seguidas no hace spam.
    """
    text_value = message.text or message.caption or ""
    if not text_value:
        return False

    normalized = normalize_intent(text_value).strip()
    if len(normalized) < 4:
        return False

    # Si este mensaje responde a otro humano y no está pidiendo ayuda,
    # Pecos no se mete solo porque aparezca "no funciona", "no sirve", etc.
    replied = message.reply_to_message
    if replied is not None:
        replied_user = replied.from_user
        replying_to_other_human = bool(
            replied_user
            and not replied_user.is_bot
            and (
                not message.from_user
                or replied_user.id != message.from_user.id
            )
        )
        if replying_to_other_human and not contextual_reply_requests_help(message):
            return False

    slot = None
    choices = None

    if "me rindo" in normalized or "ya me rindo" in normalized:
        slot = "frustration_giveup"
        choices = CONTEXTUAL_FRUSTRATION_MESSAGES
    elif (
        "no funciona" in normalized
        or "no sirve" in normalized
        or "no hay caso" in normalized
        or "sigue igual" in normalized
        or "que desastre" in normalized
    ):
        slot = "frustration_failure"
        choices = CONTEXTUAL_FRUSTRATION_MESSAGES
    elif (
        "solucionado" in normalized
        or "resuelto" in normalized
        or "ya funciono" in normalized
        or "era eso" in normalized
        or "listo quedo" in normalized
        or "arreglado" in normalized
    ):
        slot = "success"
        choices = CONTEXTUAL_SUCCESS_MESSAGES
    elif (
        "gracias" in normalized
        or "muchas gracias" in normalized
        or "te agradezco" in normalized
        or "thanks" in normalized
    ):
        # Pecos solo responde agradecimientos si están dirigidos a él.
        # Así no se mete cuando un usuario está agradeciendo a otro.
        if not gratitude_is_for_pecos(message):
            return False
        slot = "thanks"
        choices = CONTEXTUAL_THANKS_MESSAGES

    if not slot or not choices:
        return False

    if not contextual_slot_available(message.chat_id, slot):
        return False

    mark_contextual_response(message.chat_id, slot)
    await message.reply_text(random.choice(choices))
    return True


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
        # Si es un agradecimiento, reaccionar solo cuando va dirigido a Pecos.
        if "gracias" in normalized and not gratitude_is_for_pecos(message):
            return False
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


async def handle_collective_farewell(message: Message) -> bool:
    """
    Responde despedidas naturales dirigidas al grupo aunque Pecos no sea
    mencionado explícitamente. Evita intervenir si el mismo mensaje contiene
    una consulta técnica real.

    Ejemplos:
    - "Bye señores"
    - "Buenas noches muchachos"
    - "Hasta mañana amigos"
    - "Que descansen todos"
    """
    if not message.text:
        return False

    normalized = normalize_intent(message.text).strip()

    # Las despedidas dirigidas expresamente a Pecos las maneja handle_social().
    if text_mentions_pecos(message.text):
        return False

    # No cortar una consulta técnica que empieza o termina con una cortesía.
    if technical_archive_terms(message.text):
        return False

    words = normalized.split()
    short_message = len(words) <= 18

    explicit_farewell = (
        bool(re.search(r"\b(chao|chau|adios|bye)\b", normalized))
        or "hasta luego" in normalized
        or "hasta manana" in normalized
        or "hasta pronto" in normalized
        or "hasta la proxima" in normalized
        or "nos vemos" in normalized
        or "me voy" in normalized
        or "que descansen" in normalized
    )

    collective_target = (
        bool(re.search(
            r"\b(muchachos|chicos|amigos|senores|gente|grupo|todos|companeros|colegas|caballeros)\b",
            normalized,
        ))
        or "a todos" in normalized
    )

    # "Buenas noches" es ambigua: solo la tratamos como despedida colectiva
    # cuando es breve y está dirigida claramente al grupo.
    collective_good_night = (
        "buenas noches" in normalized
        and collective_target
        and short_message
    )

    if not (explicit_farewell or collective_good_night):
        return False

    usuario = display_name(message)
    increment_user_metric(message, "greeting_count")
    await message.reply_text(
        choose_random(
            "collective_farewell",
            COLLECTIVE_FAREWELLS,
            usuario,
        )
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
    if text_mentions_pecos(message.text):
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

    # Un saludo puede venir acompañado de una solicitud técnica real.
    # En ese caso Pecos saluda, pero NO corta el procesamiento: deja que el
    # buscador automático atienda también la petición en el mismo mensaje.
    if technical_archive_terms(message.text):
        return False

    return True


async def handle_social(message: Message) -> bool:
    if not message.text:
        return False

    normalized = normalize_intent(message.text)
    if not text_mentions_pecos(message.text):
        return False

    # Una petición técnica directa ("Pecos CPS MOTOTRBO?", etc.) pertenece
    # al buscador y no debe caer en una respuesta social genérica.
    if archive_query_from_natural_text(message.text) is not None:
        return False

    usuario = display_name(message)
    explicit_pecos_greeting = text_mentions_pecos(message.text)

    # Si el usuario dijo expresamente "todos menos Pecos/Peco", no fingimos
    # que Pecos fue incluido. Responde educadamente, a la antigua.
    if pecos_explicitly_excluded_from_greeting(message.text):
        increment_user_metric(message, "greeting_count")
        await message.reply_text(
            choose_random(
                "pecos_excluded_greeting",
                PECOS_EXCLUDED_GREETINGS,
                usuario,
            )
        )
        return True

    sleep_farewell = (
        "ve a dormir" in normalized
        or "vete a dormir" in normalized
        or "anda a dormir" in normalized
        or "mejor duerme" in normalized
        or "a dormir pecos" in normalized
        or "a dormir peco" in normalized
        or "duerme pecos" in normalized
        or "duerme peco" in normalized
    )

    is_farewell = (
        sleep_farewell
        or bool(re.search(r"\b(chao|chau|adios|bye)\b", normalized))
        or "hasta luego" in normalized
        or "hasta manana" in normalized
        or "nos vemos" in normalized
        or "me voy" in normalized
        or "que descanses" in normalized
        or "hasta pronto" in normalized
        or "hasta la proxima" in normalized
    )

    if is_farewell:
        increment_user_metric(message, "greeting_count")
        if sleep_farewell:
            await message.reply_text(choose_random("sleep_farewell", SLEEP_FAREWELLS, usuario))
        else:
            await message.reply_text(choose_random("farewell", FAREWELLS, usuario))
        return True

    helpful_score = 0
    if message.from_user:
        helpful_score = get_user_metric(message.chat_id, message.from_user.id, "helpful_score")

    if "buenos dias" in normalized or "buen dia" in normalized:
        increment_user_metric(message, "greeting_count")
        if explicit_pecos_greeting:
            await message.reply_text(
                choose_random("direct_pecos_morning", DIRECT_PECOS_MORNING_GREETINGS, usuario)
            )
        elif helpful_score >= 3 and random.randint(1, 100) <= 45:
            await message.reply_text(choose_random("veteran_morning", VETERAN_GREETINGS, usuario))
        else:
            await message.reply_text(choose_random("morning", MORNING_GREETINGS, usuario))
        return True

    if "buenas tardes" in normalized:
        increment_user_metric(message, "greeting_count")
        if explicit_pecos_greeting:
            await message.reply_text(
                choose_random("direct_pecos_afternoon", DIRECT_PECOS_AFTERNOON_GREETINGS, usuario)
            )
        elif helpful_score >= 3 and random.randint(1, 100) <= 45:
            await message.reply_text(choose_random("veteran_afternoon", VETERAN_GREETINGS, usuario))
        else:
            await message.reply_text(choose_random("afternoon", AFTERNOON_GREETINGS, usuario))
        return True

    if "buenas noches" in normalized:
        increment_user_metric(message, "greeting_count")
        if explicit_pecos_greeting:
            await message.reply_text(
                choose_random("direct_pecos_night", DIRECT_PECOS_NIGHT_GREETINGS, usuario)
            )
        elif helpful_score >= 3 and random.randint(1, 100) <= 45:
            await message.reply_text(choose_random("veteran_night", VETERAN_GREETINGS, usuario))
        else:
            await message.reply_text(choose_random("night", NIGHT_GREETINGS, usuario))
        return True

    if re.search(r"\b(hola|hello|hey|holi|saludos|buenas)\b", normalized):
        increment_user_metric(message, "greeting_count")
        if explicit_pecos_greeting:
            await message.reply_text(
                choose_random("direct_pecos_general", DIRECT_PECOS_GREETINGS, usuario)
            )
        elif helpful_score >= 3 and random.randint(1, 100) <= 50:
            await message.reply_text(choose_random("veteran_general", VETERAN_GREETINGS, usuario))
        else:
            await message.reply_text(choose_random("general", GENERAL_GREETINGS, usuario))
        return True

    return False


async def enforce_allowed_groups(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """
    Barrera global ejecutada antes que cualquier comando, botón o mensaje.

    - En Pruebas y YO REPARO RADIOS: continúa normalmente.
    - En cualquier otro grupo/supergrupo: Pecos abandona el chat y no procesa
      absolutamente ninguna función.
    - Los chats privados se conservan para la administración de Pecos.
    """
    chat = update.effective_chat
    if not chat:
        return

    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        return

    if chat.id in ALLOWED_GROUP_IDS:
        return

    log.warning(
        "Grupo no autorizado detectado: %s (%s). Pecos abandona el chat.",
        chat.id,
        getattr(chat, "title", "sin título"),
    )

    with contextlib.suppress(TelegramError):
        await context.bot.leave_chat(chat.id)

    # Impide que cualquier handler posterior procese este update.
    raise ApplicationHandlerStop


PECOS_GROUP_MANUAL_COMMANDS = {
    "start", "id", "config", "cancel", "encuesta", "recordar",
    "recuerdos", "olvidar", "pecos", "buscar", "historial",
    "consejo", "frase", "excusa", "pronostico",
    "actividad", "inactivos",
}


async def enforce_admin_group_commands(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
) -> None:
    """Bloquea los comandos manuales de Pecos para usuarios no administradores.

    El comportamiento automático del bot (saludos, búsquedas naturales,
    detección de consultas, duplicados, etc.) sigue disponible para todos los
    miembros del grupo.
    """
    message = update.effective_message
    chat = update.effective_chat
    user = update.effective_user
    if not message or not chat:
        return
    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        return

    text_value = (message.text or message.caption or "").strip()
    if not text_value.startswith("/"):
        return

    token = text_value.split(maxsplit=1)[0][1:]
    if not token:
        return
    if "@" in token:
        command_name, bot_name = token.split("@", 1)
        own_username = (getattr(context.bot, "username", "") or "").casefold()
        if own_username and bot_name.casefold() != own_username:
            return
    else:
        command_name = token

    command_name = command_name.casefold()
    if command_name not in PECOS_GROUP_MANUAL_COMMANDS:
        return
    if user and is_admin(user.id):
        return

    await delete_group_command_invocation(message, context)
    await context.bot.send_message(
        chat_id=chat.id,
        text="🔒 Esta función está disponible solo para administradores de Pecos.",
    )
    raise ApplicationHandlerStop


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
        remember_user_presence(message)

    # Si el administrador está escribiendo un dato solicitado por el menú.
    if await handle_admin_text(update, context):
        return

    # Los CommandHandler ya procesaron los comandos en el grupo 0.
    # Evitamos que un comando como /pecos produzca una segunda respuesta aquí.
    if message.text and message.text.startswith("/"):
        return

    is_edited = bool(update.edited_message or update.edited_channel_post)

    # Memoria histórica continua. Solo opera en HISTORY_MEMORY_GROUP_IDS.
    # No interviene en SHA-256, file_fingerprints ni en la decisión de duplicados.
    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        await learn_historical_memory(message, is_edited=is_edited)

    # Un mensaje editado NO vuelve a disparar respuestas automáticas.
    # Telegram conserva el mismo chat_id + message_id, pero envía un nuevo
    # update de tipo edited_message. La memoria puede actualizarse y la
    # moderación sigue revisando el contenido editado; después terminamos aquí.
    if is_edited:
        if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
            await moderate_if_needed(message, context)
        return

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
        # Fase 3: el veredicto de duplicados ya terminó. Si el contenido es nuevo,
        # Pecos puede comparar nombre/tamaño/familia sin alterar la decisión SHA-256.
        await handle_file_detective(message, context)

    if (
        not is_edited
        and chat.type in (ChatType.GROUP, ChatType.SUPERGROUP)
    ):
        helpful_score = remember_helpful_contribution(message)
        await maybe_send_reputation_notice(message, context, helpful_score)

    # Moderación tiene prioridad sobre saludos/respuestas.
    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        if await moderate_if_needed(message, context):
            return

    # Usuario recién ingresado que pregunta antes de revisar reglas/archivos.
    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        if await handle_new_member_question(message, context):
            return

    # Broma técnica para preguntas sobre convertir VHF <-> UHF.
    # Responde solo ante una intención clara de conversión y luego detiene
    # otros respondedores para evitar mensajes duplicados.
    if (
        not is_edited
        and chat.type in (ChatType.GROUP, ChatType.SUPERGROUP)
    ):
        if await handle_band_conversion_joke(message):
            return

    # Broma especial Melerix: una sola respuesta persistente por usuario.
    # El propietario de Pecos queda exento del límite.
    if (
        not is_edited
        and chat.type in (ChatType.GROUP, ChatType.SUPERGROUP)
    ):
        if await handle_melerix_fun(message):
            return

    # Broma especial XeraX: mención textual/@username o respuesta directa.
    # Una sola respuesta persistente por usuario; OWNER sin límite.
    if (
        not is_edited
        and chat.type in (ChatType.GROUP, ChatType.SUPERGROUP)
    ):
        if await handle_xerax_fun(message):
            return

    # Fase 2: aprende respuestas explícitas a preguntas ya registradas y
    # reconoce consultas muy parecidas sin borrar el mensaje del usuario.
    if (
        not is_edited
        and chat.type in (ChatType.GROUP, ChatType.SUPERGROUP)
    ):
        await capture_answer_to_known_question(message, context)
        if await handle_repeated_question(message, context):
            return

    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        if await handle_collective_farewell(message):
            return

        if await handle_collective_greeting(message):
            return

        if await handle_internal_joke(message):
            return

    if await handle_identity(message, context):
        return

    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        # Las consultas técnicas dirigidas a Pecos tienen prioridad sobre las
        # respuestas sociales genéricas. Esto permite frases cortas como
        # "Pecos CPS MOTOTRBO?" sin exigir la palabra "busca".
        if await handle_archive_natural_query(message, context):
            return

    if await handle_social(message):
        return

    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        if await handle_direct_pecos_mention(message):
            return

        if await maybe_offer_related_files(message, context):
            return

        if await handle_contextual_phrase(message):
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
        if int(row["chat_id"]) not in ALLOWED_GROUP_IDS:
            continue

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
                text=build_silence_message(elapsed_hours),
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
                    groups = [
                        row for row in db.list_groups()
                        if int(row["chat_id"]) in ALLOWED_GROUP_IDS
                    ]

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
        BotCommand("buscar", "Buscar archivos históricos"),
        BotCommand("historial", "Buscar conversaciones históricas"),
        BotCommand("actividad", "Ver actividad observada del grupo"),
        BotCommand("inactivos", "Listar usuarios sin actividad reciente"),
        BotCommand("consejo", "Pedir un consejo a Pecos"),
        BotCommand("frase", "Frase de Pecos"),
        BotCommand("excusa", "Generar una excusa"),
        BotCommand("pronostico", "Pronóstico de Pecos"),
    ]
    await application.bot.set_my_commands(
        private_commands,
        scope=BotCommandScopeAllPrivateChats(),
    )


    # No exponemos el menú de comandos a usuarios normales del grupo.
    # Cada administrador de Pecos recibe su propio scope ChatMember.
    with contextlib.suppress(TelegramError):
        await application.bot.delete_my_commands(scope=BotCommandScopeAllGroupChats())

    # La versión anterior publicó comandos con scope por chat. Hay que borrar
    # esos scopes explícitamente para que los usuarios normales dejen de verlos.
    for allowed_group_id in sorted(ALLOWED_GROUP_IDS):
        with contextlib.suppress(TelegramError):
            await application.bot.delete_my_commands(
                scope=BotCommandScopeChat(allowed_group_id),
            )

    if ADMIN_USER_IDS:
        for allowed_group_id in sorted(ALLOWED_GROUP_IDS):
            for admin_user_id in sorted(ADMIN_USER_IDS):
                with contextlib.suppress(TelegramError):
                    await application.bot.set_my_commands(
                        group_commands,
                        scope=BotCommandScopeChatMember(
                            chat_id=allowed_group_id,
                            user_id=admin_user_id,
                        ),
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

    log.info(
        "Duplicados: Bot API local + SHA-256 | temporales=%s",
        TELEGRAM_FILES_DIR,
    )
    log.info("Grupos autorizados: %s", ",".join(str(x) for x in sorted(ALLOWED_GROUP_IDS)))
    log.info("Memoria histórica activa en grupos: %s | fuente=%s", ",".join(str(x) for x in sorted(HISTORY_MEMORY_GROUP_IDS)), HISTORY_SOURCE_CHAT_ID)

    # Si la base conserva otros grupos antiguos, Pecos intenta salir de ellos
    # al iniciar. No se elimina historial; simplemente quedan inactivos.
    for row in db.list_groups():
        chat_id = int(row["chat_id"])
        if chat_id in ALLOWED_GROUP_IDS:
            continue
        with contextlib.suppress(TelegramError):
            await application.bot.leave_chat(chat_id)

    application.bot_data["daily_task"] = asyncio.create_task(daily_loop(application))

    me = await application.bot.get_me()
    if me.username:
        PECOS_USERNAME_ALIASES.add(normalize_intent(me.username).lower().lstrip("@"))

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

    # El Bot API local puede tardar más de los 5 s por defecto mientras
    # está materializando archivos grandes. Damos margen suficiente para
    # que /start, respuestas y botones no fallen por un timeout artificial.
    builder = (
        Application.builder()
        .token(BOT_TOKEN)
        .connect_timeout(15.0)
        .read_timeout(60.0)
        .write_timeout(30.0)
        .pool_timeout(30.0)
        .connection_pool_size(64)
        .get_updates_connect_timeout(15.0)
        .get_updates_read_timeout(60.0)
        .get_updates_pool_timeout(30.0)
    )

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

    # Barrera de seguridad: se ejecuta antes que cualquier otro handler.
    # Si Pecos es agregado a otro grupo, sale de él y no procesa el update.
    app.add_handler(TypeHandler(Update, enforce_allowed_groups), group=-100)
    # Los comandos manuales dentro de los grupos quedan reservados a los
    # administradores configurados de Pecos.
    app.add_handler(TypeHandler(Update, enforce_admin_group_commands), group=-90)

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
    app.add_handler(CommandHandler("buscar", command_search_archive), group=0)
    app.add_handler(CommandHandler("historial", command_history_search), group=0)
    app.add_handler(CommandHandler("actividad", command_activity), group=0)
    app.add_handler(CommandHandler("inactivos", command_inactive), group=0)
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
