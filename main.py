#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Pecos Paul Kele Bot - Railway + Telegram Bot API Server local
Administración completa desde Telegram mediante botones.

Requiere:
    python-telegram-bot==22.8
    Telethon==1.45.0  # solo para expulsión MTProto conservando historial

Variables de entorno:
    BOT_TOKEN              Token de @BotFather (obligatorio)
    ADMIN_USER_IDS         Telegram User IDs autorizados separados por comas (recomendado)
    ADMIN_USER_ID          Compatibilidad: un solo ID antiguo (opcional)
    BOT_TIMEZONE           Ej. America/Santiago (opcional)
    DATA_DIR               Carpeta de datos (opcional, por defecto ./data)
    ALLOWED_GROUP_IDS      Grupos donde Pecos puede operar, separados por comas
    TELEGRAM_API_ID        API ID de my.telegram.org para MTProto (opcional)
    TELEGRAM_API_HASH      API Hash de my.telegram.org para MTProto (opcional)
"""

from __future__ import annotations

import asyncio
import ast
import contextlib
import difflib
import hashlib
import io
import json
from difflib import SequenceMatcher
import logging
import math
import os
import random
import re
import sqlite3
import threading
import time
import unicodedata
from urllib.parse import unquote, urlparse
from datetime import date, datetime, timedelta
from fractions import Fraction
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
    MessageReactionHandler,
    TypeHandler,
    filters,
)

# Telethon es opcional para el resto de Pecos. Si falta, el bot inicia igual
# y únicamente se desactiva la limpieza MTProto.
try:
    from telethon import TelegramClient, types, utils
    from telethon.errors import FloodWaitError, RPCError
    TELETHON_AVAILABLE = True
    TELETHON_IMPORT_ERROR = ""
except Exception as _telethon_exc:
    TelegramClient = None
    types = None
    utils = None
    FloodWaitError = Exception
    RPCError = Exception
    TELETHON_AVAILABLE = False
    TELETHON_IMPORT_ERROR = str(_telethon_exc)


APP_NAME = "Pecos Paul Kele"
VERSION = "2.8.58-cleanup-block-786-1595"
HISTORY_SOURCE_CHAT_ID = int(os.getenv("HISTORY_SOURCE_CHAT_ID", "-1001775566217"))
HISTORY_MEMORY_GROUP_IDS = {
    int(x.strip()) for x in os.getenv("HISTORY_MEMORY_GROUP_IDS", "-1001775566217").split(",")
    if x.strip()
}
TEST_GROUP_ID = int(
    os.getenv("TEST_GROUP_ID", "-1004469972566").strip()
    or "-1004469972566"
)
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

# ---------------------------------------------------------------------
# Limpieza segura: bloque explícito 786–1595 por User ID
# ---------------------------------------------------------------------
# Rango solicitado: desde 20/11/2022 hasta 27/12/2024, ambas fechas incluidas.
INACTIVE_CLEANUP_START_DATE = date(2022, 11, 20)
INACTIVE_CLEANUP_END_DATE = date(2024, 12, 27)
INACTIVE_CLEANUP_CONFIRM_TTL_SECONDS = 10 * 60
INACTIVE_CLEANUP_KICK_DELAY_SECONDS = 1.5

# ---------------------------------------------------------------------
# Limpieza masiva solicitada: bloque exacto 786–1595 del padrón actual.
# Fuente: reporte /actividad entregado por el administrador.
# IMPORTANTE: la selección es EXCLUSIVAMENTE por Telegram User ID.
# Los nombres son solo informativos y jamás se usan para expulsar.
# ---------------------------------------------------------------------
CLEANUP_BLOCK_FIRST_INDEX = 786
CLEANUP_BLOCK_LAST_INDEX = 1595
CLEANUP_BLOCK_EXPECTED_COUNT = 810
CLEANUP_BLOCK_TARGET_SHA256 = '52c832448c0f09138826983a5771278f1a9f9db8dddbffb9497a580a4af2df04'
CLEANUP_BLOCK_TARGETS: tuple[tuple[int, int, str], ...] = (
    (786, 1075072090, 'Daniel López CD3DLQ (@CD3DLQ)'),
    (787, 354009112, 'Агент006 (@Kirilin)'),
    (788, 1646291328, 'Memo Pinto'),
    (789, 7286721969, 'Anderson Rodriguez'),
    (790, 1306298041, 'benji ry brito'),
    (791, 7030962393, 'Sjgs Lll'),
    (792, 5785275523, '19466 (@avalosergio)'),
    (793, 5101345814, 'Rodrigo (@rorro971)'),
    (794, 335013840, 'Jose'),
    (795, 8086514514, 'Luis Soto'),
    (796, 1562718729, 'Sg Technology'),
    (797, 913857272, 'CD2JEQ - Jepté'),
    (798, 7743717687, 'RADIO&ACCESORIOS (@CE6SAD)'),
    (799, 670609624, 'Cris Ighot (@ImzeocqzBp)'),
    (800, 7366837656, '.'),
    (801, 687277331, '\u206a\u206c\u206e\u206e\u206e\u206e \u206a\u206c\u206e\u206e\u206e\u206e'),
    (802, 7579125759, 'Luis Enrique SanLo (@sanlo75)'),
    (803, 834074645, 'Noel Rivera'),
    (804, 2048410379, 'Na'),
    (805, 25730194, 'Lucas (@lucasmatleb)'),
    (806, 6203102990, 'Jonathan'),
    (807, 6384487335, 'OA4'),
    (808, 7101602572, 'Usuario 7101602572'),
    (809, 186332258, 'Joaquin - EA5GVK (@quini7620)'),
    (810, 7495894321, 'Lazy L'),
    (811, 542410960, 'So (@ame81net)'),
    (812, 7046252623, 'EA1CHG (@Ea1chg)'),
    (813, 1702252672, 'YA'),
    (814, 1116377696, 'CD5NSM Luis Luengo (@CD5NSM)'),
    (815, 7291517229, '. (@Carlos011001)'),
    (816, 123394713, 'Mike Lima (@MLaval)'),
    (817, 6551919748, 'Juanpa Kiroz (@Caxorrito)'),
    (818, 6230964447, 'Oscar_j Alvarez Quiros (@ojaq_79)'),
    (819, 505972189, 't o n y (@Nokiafloyd)'),
    (820, 1033877477, 'Rodrigo Vergara Lezana (@CE1PB)'),
    (821, 1346643381, 'A (@zp71398xv)'),
    (822, 940272843, 'VM (@VJMMJS)'),
    (823, 1761083007, 'Roberto'),
    (824, 5500240545, 'CTstarter'),
    (825, 608860530, 'Bombero (@Lince14)'),
    (826, 139048529, 'Ricardo Yáñez Aguilar'),
    (827, 7068561381, 'V1P3R'),
    (828, 153413234, 'mt1000 (@mtsxlab)'),
    (829, 816564442, 'Diego CBM1CIA (@PcProService)'),
    (830, 6819041419, 'DELTA LIMA'),
    (831, 7450418780, 'Victor Victor'),
    (832, 5097326213, 'Carlos M'),
    (833, 1110041820, 'Pedro Flores'),
    (834, 6587271706, 'Jaime Maldonado (@CD3JMA)'),
    (835, 5864674981, 'Jhoshua'),
    (836, 6996264832, 'WildFire (@WildFire715)'),
    (837, 262751871, 'Muklas Wahyuda (@Muklaswahyuda)'),
    (838, 6431574105, 'Jav'),
    (839, 5563886210, 'JaVeRo'),
    (840, 998729336, 'Cristián Eduardo (@Chichaneduardo)'),
    (841, 1514792825, 'N2IY (@Rtl2021)'),
    (842, 7047784349, 'Juan Carlos Espinoza Fuentes'),
    (843, 5896986723, 'OSCAR'),
    (844, 504952720, 'Luis Diaz VIP (@luisfeick)'),
    (845, 1901480014, '😁'),
    (846, 5272375136, 'Nono (@Nonobeta1)'),
    (847, 489461492, 'Toni GZG (@EB7GZG)'),
    (848, 5096446503, 'Luguillo'),
    (849, 1458178419, 'José Silva (@Ce2Hja)'),
    (850, 5505846951, 'Gerardo'),
    (851, 727995115, 'Lukas (@LY1LB)'),
    (852, 1257384061, 'Gabin - ubnt (@f4ubnt)'),
    (853, 1540649360, 'Cybercom'),
    (854, 1894404667, 'Darkar'),
    (855, 5684772445, 'Darwin Quimi'),
    (856, 6756227117, 'FeR RIVeRo (@Rivero501)'),
    (857, 5614777624, 'Johnnie TI4JVC Villarreal (@TI4JVC)'),
    (858, 1055433930, 'Juan Antonio'),
    (859, 6979900853, 'Jorge Aranc Xq1lty'),
    (860, 1715764056, 'Carlos Menendez (@Carlosmenendez123)'),
    (861, 2027701481, 'S A'),
    (862, 1141453542, 'carlos soto'),
    (863, 5979846611, '. .'),
    (864, 6577412060, 'OA4EAW'),
    (865, 1714643753, 'Marco Ulloa CA3UGL'),
    (866, 6757329103, 'Giancarlo Cruzado Alva'),
    (867, 1589655225, 'JAIME MATIAS'),
    (868, 1934992697, 'Soporte'),
    (869, 2004084028, 'juan'),
    (870, 1384854369, 'Andresfire3 Saez Ulloa'),
    (871, 820643853, 'Yerko Guerra Kong (@Kekostream)'),
    (872, 736400086, 'Alfa Mike'),
    (873, 1073990236, 'Ricardo Jesus Clara Palomares'),
    (874, 6259494618, 'Anthony'),
    (875, 1623968923, 'Felipe Valenzuela'),
    (876, 1261334177, 'Guillermo Garcia'),
    (877, 5925400155, 'Anfredo'),
    (878, 716413071, 'Vikri Sarracino'),
    (879, 660898478, 'XE1IMB (@XE1IMB)'),
    (880, 723001758, 'GAM'),
    (881, 1426794658, 'Luis Fabrega'),
    (882, 1912876176, 'Klauss (@Klaug223)'),
    (883, 5401034831, 'Rafita'),
    (884, 5422248298, 'MM'),
    (885, 1158584718, 'Rood'),
    (886, 404836397, 'J'),
    (887, 5207745300, 'Jose Manuel'),
    (888, 1168348848, 'Victor cortes'),
    (889, 6052779788, 'Robert'),
    (890, 5348925301, 'Ce3rdl'),
    (891, 6195160426, 'Ernesto Daza'),
    (892, 55557744, 'Cristian Donoso (@cadjdd)'),
    (893, 1385366725, 'Jgc089 (@Jgc098)'),
    (894, 250588372, 'Said Morales (@PeckeMorales)'),
    (895, 1461148954, 'Luis Berrios'),
    (896, 1413137219, 'Freddy Basaez Miranda'),
    (897, 1966862584, 'W h ky (@wahuky)'),
    (898, 1463876027, 'J A'),
    (899, 1290196115, 'Reinaldo Reyes'),
    (900, 5233641736, 'Luis Alfredo'),
    (901, 579299725, 'Francisco Alvarado'),
    (902, 1904423977, 'Guido Iván'),
    (903, 8601601135, 'Raul Ibarra'),
    (904, 8452845231, 'Radio'),
    (905, 8568492088, 'Christian Araya'),
    (906, 8512677220, 'José Zambrano'),
    (907, 8126559223, 'Jose Miguel Bravo Diaz'),
    (908, 8865463978, 'Rene García (@centracomhidalgo)'),
    (909, 1589160347, 'Jhonny Vinces Rivadeneira'),
    (910, 1557898165, 'Paul Huanca (@WPaulHP)'),
    (911, 1308284014, 'Felix Antonio /CD2FRN'),
    (912, 1970365219, 'Braulio Villa (@BraulioOne)'),
    (913, 8454440961, 'mark (@cgc_mark_lbdv)'),
    (914, 5008533028, 'Roial'),
    (915, 7615688181, 'HY GAIN'),
    (916, 1559307984, 'Cristian Peyran (@cristianpeyran)'),
    (917, 2034837606, 'David H'),
    (918, 1266092314, 'Jim'),
    (919, 7013892238, 'jose a secas (@josra0324)'),
    (920, 1509764921, 'Jose Luis Sanchez'),
    (921, 8994432943, 'Grupo Alpha'),
    (922, 8874448949, 'Omar Rodriguez'),
    (923, 615096599, 'Alvamo (@Alvamo2024)'),
    (924, 8105230445, 'Eduardo'),
    (925, 2076500429, 'MG COMUNICACIONES'),
    (926, 1159988052, 'Jorge Palmero 🇲🇽'),
    (927, 8489817495, 'Carlos Gutz'),
    (928, 1620007937, 'Tapia'),
    (929, 1986683964, 'SysAdmin'),
    (930, 800300782, 'RODRIGO POBLETE (@CE3PJD)'),
    (931, 1572793424, 'Francisco'),
    (932, 834672010, 'Carlos Herrera (@CarlosH3rr3ra)'),
    (933, 867616896, 'João Sergio • PY1IP 🇧🇷 (@PY1IP)'),
    (934, 5080830842, 'Adrian Alcaraz'),
    (935, 1493178027, '. .'),
    (936, 2008020699, 'Alejandro Monardes'),
    (937, 8921861140, 'Eduardo Muñoz'),
    (938, 5095711278, 'Sebita'),
    (939, 1515454066, 'Heck Rey (@Heck_Rey)'),
    (940, 8250667360, 'Cristian Ramirez (@Cristian_rac)'),
    (941, 6133946262, 'Raúl'),
    (942, 7079039444, 'Ichigo Meneses'),
    (943, 6708176777, 'Perro Negro (@Perronegrooo)'),
    (944, 6337436892, 'Gil Portillo'),
    (945, 8941628147, 'Romeosierra X'),
    (946, 8634188150, 'steysy g'),
    (947, 5792350171, 'JESÚS TOLEDO (@Toledo58K1)'),
    (948, 1683572941, 'JOshe (@JOsheLUis257)'),
    (949, 6088905234, 'Luis M'),
    (950, 8267342662, 'Fernando (Koyi) Avalos'),
    (951, 8716097232, 'Moisés'),
    (952, 8951772485, 'José Luis Salas'),
    (953, 1494764132, 'Luis (@LAM1957)'),
    (954, 5943446674, 'ALEXIS DIAZ'),
    (955, 1583494332, 'Fernando Herrera (@Ferhertor)'),
    (956, 1234549549, 'Andres'),
    (957, 281238607, 'Alberto Barragan (@BARRAGANJF)'),
    (958, 7789988094, 'Especialista MTSS Manzanillo'),
    (959, 7071785420, 'Ivan'),
    (960, 8979180911, 'Paramedico Guadalajara'),
    (961, 5865024901, 'Ja Ar'),
    (962, 862818896, 'A L (@Peshmerga02)'),
    (963, 1586039356, '71357 71357'),
    (964, 8814839653, 'Juan Co'),
    (965, 5471824328, 'Matrix 2304'),
    (966, 7495789286, '🇲🇽 Tirador deportivo'),
    (967, 6865531040, '. .'),
    (968, 1726324457, 'MZT SIN (@MZT_SIN)'),
    (969, 6655939655, '16022'),
    (970, 7178240755, 'John Muñoz'),
    (971, 6081422412, 'Álvaro Jara'),
    (972, 1157743561, 'Enri'),
    (973, 1267030481, 'jonathan burgos (@tatan11B)'),
    (974, 1999107431, 'Carlos'),
    (975, 6102257388, 'Leo'),
    (976, 8562577618, '.'),
    (977, 1276545302, 'CE1 EIR (@EPIR23)'),
    (978, 1058885070, 'Dairo Salazar'),
    (979, 7307468981, 'Maverick'),
    (980, 1590435455, 'alejandro CA2AKD (@CA2AKD)'),
    (981, 8863283954, 'jhors'),
    (982, 1153681712, 'Franco'),
    (983, 8977575207, 'Daniel Alejandro Velasquez Millan'),
    (984, 1341688130, 'I Santiago (@isaalge)'),
    (985, 7867867655, 'CD3TBC'),
    (986, 8700665607, 'Rony Dance'),
    (987, 8547128021, 'ID 8547128021'),
    (988, 8705338420, 'ZAVIEL'),
    (989, 8279422020, '.........'),
    (990, 5739748135, 'Paulo González'),
    (991, 7593415981, 'Fernando Caiseo (@Joseretamals)'),
    (992, 6562694874, 'Carlos'),
    (993, 8840596362, 'Julio Lippmann'),
    (994, 7583754655, 'da lex (@Dalex699)'),
    (995, 8088671623, 'ID 8088671623'),
    (996, 5114129211, 'Jose Luis Pardo F (@JoseLuisPardoFigueroa)'),
    (997, 536164267, 'Esteban GT CD3EGX'),
    (998, 7891199607, 'Veronika Benešová (@VeronikaBeneov)'),
    (999, 8645279567, 'ID 8645279567'),
    (1000, 6567539596, 'Juan'),
    (1001, 8928961146, 'Mr Inge De Huetamo (@Mringedehuetamo)'),
    (1002, 7351738580, 'MC🌴✨✨ (@mc90901)'),
    (1003, 8430492235, 'Anderson San Tecnologia'),
    (1004, 8599972373, 'Jp'),
    (1005, 8909540944, 'Carlos ms'),
    (1006, 1684973103, 'Fajro (@FajRodrigo)'),
    (1007, 2034061281, 'Esteban'),
    (1008, 8698933944, 'Jorge Sanchez'),
    (1009, 8415229880, 'Carlos Llanten'),
    (1010, 5526410694, 'فاهم'),
    (1011, 8620729351, '.'),
    (1012, 1704456289, 'Víctor Bórquez (@Victor331988)'),
    (1013, 8980449910, 'MOTOTRBO Jose (@josemotorola)'),
    (1014, 8546408413, 'ID 8546408413'),
    (1015, 8279630236, 'Vadok'),
    (1016, 8740489860, 'Emo Emo'),
    (1017, 8644107378, 'Jjj'),
    (1018, 5228309409, 'Miro -=MandM=-'),
    (1019, 794661235, 'Christian Cruz (@i_am_christian_cruz)'),
    (1020, 7146715667, 'Carlos'),
    (1021, 1106703980, 'BC.'),
    (1022, 1481139187, 'Jorge CD1JLH (@Jorge_hpm)'),
    (1023, 6116056566, 'Marco Romero (@Mromero2976)'),
    (1024, 633389690, 'ㅤЮра (@yuratron)'),
    (1025, 8796604729, 'Markus (@Peil_sender)'),
    (1026, 39418688, '宇軒 | BU2HB 神楽坂 (@russel053)'),
    (1027, 6880489765, 'Инал Келехсаев'),
    (1028, 89121009, 'Aleksey Mesilov (@Aleksey_Mesilov)'),
    (1029, 1599049207, 'Dominik (@domo978)'),
    (1030, 5328513984, 'Edgard Bizama (@Bizama88)'),
    (1031, 5669106493, 'Nietzsche (@Nietzsche_162)'),
    (1032, 755127186, 'Poe Kill'),
    (1033, 7268454211, 'Antsfire'),
    (1034, 7414176632, 'Erick'),
    (1035, 8693023001, 'CPS Lab'),
    (1036, 8302527357, 'QuezadaVHF +56994945687'),
    (1037, 6826480721, 'Miguel Salinas'),
    (1038, 7588981777, 'Israel Garza'),
    (1039, 5705506779, 'Saya (@BudiHarta2007)'),
    (1040, 389921689, 'Saul Diaz'),
    (1041, 7020178230, 'Esteban Marcial'),
    (1042, 1177670859, 'Alfredo'),
    (1043, 8559313809, 'Jsm'),
    (1044, 1691593618, 'Cesar Hernandez'),
    (1045, 372646591, 'Евгений "R6DWG" (@R6DWG)'),
    (1046, 5823588539, 'Giovanni Agudelo (@Giovaa12)'),
    (1047, 845737895, 'Ali'),
    (1048, 236060413, 'Charly (@Charly_Suas)'),
    (1049, 705618627, 'Vicho (@Vichope0)'),
    (1050, 6852014501, 'Luis Solis'),
    (1051, 8780017712, 'Chchchchch'),
    (1052, 1635571352, 'Cross Gero (@Crossb123)'),
    (1053, 5537510863, 'Diego'),
    (1054, 30790186, 'Ruben Santibañez CE6TTL (@ce6ttl)'),
    (1055, 494986685, '.'),
    (1056, 7355306187, 'Oscar Mayoral'),
    (1057, 1501048524, '🧐'),
    (1058, 8329119008, 'Geek Insane'),
    (1059, 1784037691, '. (@George_119876)'),
    (1060, 727779185, 'מקני (@ce3kra)'),
    (1061, 7641074831, 'Alan Maciel'),
    (1062, 1249814129, 'Jhonny CA6THA (@CA6THA)'),
    (1063, 5116552981, 'maria Bbb'),
    (1064, 8027044110, 'Juanjo'),
    (1065, 7831639544, 'Ce1wml (@Ce1wml)'),
    (1066, 8333385062, 'J O'),
    (1067, 8015503718, 'Larissa'),
    (1068, 6914123293, 'Punisher'),
    (1069, 7697528052, '_scooter_ (@O_n_T_u_m_y_c)'),
    (1070, 892306226, 'Marcus Imperiolli (@Emperino)'),
    (1071, 8911964276, 'Miguel'),
    (1072, 6407793884, 'Arturo Hernández'),
    (1073, 1131415982, 'Angel (@mi6ilo)'),
    (1074, 8521881361, 'antonio (@FireBoston)'),
    (1075, 1217025483, 'Rc'),
    (1076, 6340208620, 'I3yenj7w I2l3b8f (@cdrubsstwsb)'),
    (1077, 7855330606, 'Juan Ramirez'),
    (1078, 7591281386, 'Pato LeCuack (@pato_lecuack)'),
    (1079, 8959001143, 'Nicolas Caipa'),
    (1080, 7410705694, 'L (@Fazendd)'),
    (1081, 5992889403, 'Rds Comunicaciones'),
    (1082, 7024258334, 'Rodolfo'),
    (1083, 1228527449, ':.: (@Chamelfo)'),
    (1084, 839716716, 'carlos castillo arica (@carlosdearica)'),
    (1085, 6974629342, 'Jorge Guerra'),
    (1086, 2045261909, 'EA4AGU Jesús'),
    (1087, 996683803, 'Leonel Ottone'),
    (1088, 8424431715, 'Daniel Carvacho'),
    (1089, 5230736365, 'Roberto Santibañez'),
    (1090, 5520998167, 'KL 33'),
    (1091, 8695390776, 'Alejandro Meza'),
    (1092, 5850184004, 'Raul Riquelme Araya'),
    (1093, 5631193879, 'Rodrigo Parra (@rparrap)'),
    (1094, 1783358575, 'Jel Jhoa'),
    (1095, 5649011716, 'Jonathan Felipe'),
    (1096, 8714348678, 'Javier Andres'),
    (1097, 7547325165, '90161'),
    (1098, 849799327, 'Diego CX8BDR (@DiegoRubianes)'),
    (1099, 7991677200, 'M'),
    (1100, 882167772, 'Alejandro'),
    (1101, 8686899442, 'jose'),
    (1102, 6333823767, 'Roberto Luna Valladares'),
    (1103, 5663096863, 'Kr Br'),
    (1104, 7060938742, 'Juan Cid Salazar'),
    (1105, 45327255, 'JMS 5UFR (@CEUFR)'),
    (1106, 8656111139, 'José Luis Paredes'),
    (1107, 8585971759, 'Mocsys Contacto'),
    (1108, 805833097, 'Rodrigo Espinoza'),
    (1109, 5664741201, 'EA4FCO'),
    (1110, 1622980926, 'PanxoToro (@FrancoTx)'),
    (1111, 8711221573, 'Ruben López Guadarrama'),
    (1112, 5092973113, 'Steve CD1LKS'),
    (1113, 6687585416, 'VG'),
    (1114, 6209356386, 'Patricio Rubiño Aguila'),
    (1115, 5087346528, 'Jorge Romero'),
    (1116, 1542923357, 'Alexis'),
    (1117, 6387674837, 'Master Chief'),
    (1118, 138678747, 'Alabarce (@JoseAlabarce)'),
    (1119, 8673522458, 'Juan Collao'),
    (1120, 1710414240, 'Andruu (@Andruup)'),
    (1121, 8252584450, '.'),
    (1122, 5961715409, 'Alberto'),
    (1123, 8643157923, 'Manuel Butrón'),
    (1124, 7214467419, 'Bahometh_Dark'),
    (1125, 1008769207, 'Ghost Dark Angel (@Ghoosth_Dark)'),
    (1126, 407880646, 'Holyhazard'),
    (1127, 753462590, 'Dondatos (@Dondatos)'),
    (1128, 7767843066, 'Alvaro Patiño (@bobpatino26)'),
    (1129, 8380674932, 'Mike'),
    (1130, 8498146978, 'Juan Seve'),
    (1131, 7075728362, 'Eko (@erkanzen)'),
    (1132, 6785638068, 'Deniz'),
    (1133, 1590622826, 'Bicicletas Y Refacciones Amador'),
    (1134, 1094074213, 'Luigi (@swgps)'),
    (1135, 8770040576, 'Tomas Gonzalez'),
    (1136, 647690982, 'Gustavo Saavedra (@adolfoinostroza)'),
    (1137, 11621596, 'Edinson (@z_edinson)'),
    (1138, 7271331761, 'Rodrigo CA3GAX'),
    (1139, 8539863919, 'Emprendimiento David lujano'),
    (1140, 6819347342, 'JAMAL ASH SHINAR'),
    (1141, 6699190950, 'Fabrizio ….'),
    (1142, 6290116687, 'Willian Baldeon'),
    (1143, 847208208, 'Alex Fernandes'),
    (1144, 8562600544, 'ID 8562600544'),
    (1145, 33148534, 'familia tux (@familiatux)'),
    (1146, 6126606557, 'Zx083 (@mexicanouni)'),
    (1147, 7775117149, 'Adrian Mainieri'),
    (1148, 261077081, 'William Vargas (@willvcr)'),
    (1149, 37447701, 'Antonio CL320 (@carras320)'),
    (1150, 8566535400, '. .'),
    (1151, 2859701, 'Lucho'),
    (1152, 5885575190, 'Alex Villegas'),
    (1153, 6963620029, 'Cristian Campos'),
    (1154, 597685106, 'Rafael Ric (@EA7UW)'),
    (1155, 1504018599, 'Omaba1991 (@OMABA1991)'),
    (1156, 741116718, 'EA5ITB Javier Tormo'),
    (1157, 8576210481, 'Danilo'),
    (1158, 3717534, 'Ernesto Abreu (@eabreu112)'),
    (1159, 6841834145, 'Fernando Bernal'),
    (1160, 21724537, 'Juan Contreras Arellano'),
    (1161, 1529436220, 'Jose Montes'),
    (1162, 8372847707, 'Juan Mene'),
    (1163, 1764098333, 'Juan leal'),
    (1164, 5414073906, 'Jcarlos Osses'),
    (1165, 8446508807, 'David'),
    (1166, 1564740366, 'Martin Duran'),
    (1167, 1299107523, 'MIGUEL'),
    (1168, 557867908, 'Marco Molina'),
    (1169, 157687391, 'Leonardo Soto'),
    (1170, 1181464778, 'Freddy (@Krugger22)'),
    (1171, 1545634044, 'CD2FNR FRANCISCO CASTILLO REYES (@CD2FNR)'),
    (1172, 5565863240, 'Ryan'),
    (1173, 1441665119, 'Matt Nelson (@scanSydney)'),
    (1174, 8591722483, 'Tibas'),
    (1175, 894513703, 'Malik Pandžić'),
    (1176, 839948622, 'cesar corrales CE2MCG'),
    (1177, 983853190, 'Cristian FL'),
    (1178, 6214802184, 'daniel concha'),
    (1179, 5682832805, 'Andy'),
    (1180, 5088735076, 'Erwin Hernandez Catril'),
    (1181, 8441270704, 'Pablo'),
    (1182, 8301933861, 'Leo Fer'),
    (1183, 2112800147, '-Deadlol-'),
    (1184, 6463528331, 'Nicje'),
    (1185, 1655885021, 'Juan Pablo Sánchez (@PaPOs1988)'),
    (1186, 7989251505, 'Alon'),
    (1187, 327065461, 'Master Of Disaster'),
    (1188, 8584824188, 'Jose'),
    (1189, 1460443389, 'Gastón CE4STG'),
    (1190, 1722672975, 'Tomas Marin (@CE3MBT)'),
    (1191, 20740921, 'Diego (@zl_diego)'),
    (1192, 569827974, 'Victor V2M Maldonado (@TheV2M)'),
    (1193, 6072760089, 'Jose Carvajal'),
    (1194, 5327422609, 'M. D.'),
    (1195, 8253906826, 'Tere (@Alibernalperez)'),
    (1196, 7231767840, 'Ro'),
    (1197, 7559208742, 'Nacho Ponce'),
    (1198, 1755048212, 'DZHON'),
    (1199, 7796756775, 'Jose lopez'),
    (1200, 6629272743, 'Victor (@VictorJaraMino)'),
    (1201, 5984346729, 'Franco Jara'),
    (1202, 5811456567, 'dr.SK (@sk_doctor)'),
    (1203, 1919156132, 'Elvis'),
    (1204, 8299025818, 'Radcop'),
    (1205, 1425022267, 'Esteban Tapia'),
    (1206, 8529939583, 'Chavalo Lira'),
    (1207, 760042761, 'Дмитрий (@Kaskad1)'),
    (1208, 724824381, 'Емельян Сперанский (@YemelyanSperansky)'),
    (1209, 288682393, '117 R9JBD Dmitry (@ArkKedr_Ugra)'),
    (1210, 1300451998, 'Gilbert Eduardo Castillo Redondo'),
    (1211, 6989759805, 'Juan Camacho (@None0954)'),
    (1212, 8321361908, 'Luis Ovando'),
    (1213, 5826020028, 'Pedro Landaeta'),
    (1214, 3960753, 'Charly_ Stan (@CHG54)'),
    (1215, 1798325975, '😀'),
    (1216, 5084046528, 'mike (@mike_1488)'),
    (1217, 635507044, 'Daniel Belmonte (@danny0324)'),
    (1218, 5130186049, 'Ya'),
    (1219, 84112993, 'AiD (@AiD911)'),
    (1220, 1320140166, 'Ignacio (@Ignaciss)'),
    (1221, 7747249318, 'ID 7747249318'),
    (1222, 8423045988, 'Cb CD4 AQD (@estacionniebla)'),
    (1223, 8084264752, 'Covadonga1'),
    (1224, 6527120474, 'Emil'),
    (1225, 8526360589, 'Renato'),
    (1226, 6646085071, 'Angelo Escobar'),
    (1227, 8352845751, 'Arturo'),
    (1228, 8009669462, 'Gilberto Guzmán'),
    (1229, 8521901689, 'Claudio Flores'),
    (1230, 5184156125, 'John Zenteno'),
    (1231, 842847663, 'Martin Jesus'),
    (1232, 769964392, 'Ada'),
    (1233, 1420281520, 'willow'),
    (1234, 6286208423, 'Administration (@C7C70C700)'),
    (1235, 8444845815, 'Mike (@PelicanKM)'),
    (1236, 1053064496, 'mike (@strokedka)'),
    (1237, 807056876, 'jose jose'),
    (1238, 788096692, 'Henry G.'),
    (1239, 8356652364, 'ID 8356652364'),
    (1240, 8307251279, 'Ted'),
    (1241, 600745702, 'Javier (@Radio_Engineering_EA3GXK)'),
    (1242, 6365545290, 'Reizag'),
    (1243, 1251319704, 'SAUL Diaz'),
    (1244, 6492027452, 'Jorge Espinoza'),
    (1245, 1801603449, 'Yo Jk (@R0n1c0)'),
    (1246, 6320541255, 'Viljams'),
    (1247, 8361727675, 'Ryt Quillota'),
    (1248, 382521681, 'sasha555 (@sasha5_55)'),
    (1249, 8466670035, 'Jj'),
    (1250, 463267144, 'Sherif lviv (@Sherif_lviv)'),
    (1251, 6137029556, 'Luis'),
    (1252, 1451010581, 'Jaime (@jaimecortess)'),
    (1253, 5450314961, 'Zainoel AR YD9UMQ 🇲🇨 (@YD9UMQ_Zainul)'),
    (1254, 888803204, 'Henry May'),
    (1255, 629884003, '123123 (@BG6TTT)'),
    (1256, 5792028124, 'Andres Mendoza'),
    (1257, 1512237772, 'Jm .'),
    (1258, 5002999615, 'Cristian Inostroza torres (@cristan_926)'),
    (1259, 722961529, 'Mago (@Ofticio)'),
    (1260, 1072878985, 'Juanka TI2JCY'),
    (1261, 1353907116, 'Diego (@dkosta)'),
    (1262, 1457409410, 'Rodrigo Lucero CE8WDB (@ce8wdb)'),
    (1263, 8209727461, 'Enmanuel Moraga'),
    (1264, 7144895933, 'Dago (@MuffinEater69)'),
    (1265, 1539214127, 'Jorge'),
    (1266, 6118668088, 'Francisco Mena'),
    (1267, 846831449, 'CA3MKF Mauricio 🇨🇱'),
    (1268, 1319850150, 'Guty (@Luke_guty)'),
    (1269, 426935441, 'Ricardo (@m4china13)'),
    (1270, 229901458, 'Carlos Salas (@bomberosalas)'),
    (1271, 5046493203, 'Vicho Luna (@VichoLuna)'),
    (1272, 1096328991, 'Cristian Tello (@c_tello)'),
    (1273, 1456398650, 'Cristian Becerra'),
    (1274, 1267031267, 'Jose V.'),
    (1275, 5177189462, 'Ciko 39'),
    (1276, 1910277459, 'Carlos'),
    (1277, 1299984144, 'osvaldo (@CA2RON)'),
    (1278, 5401454770, 'PAMUNGKAS'),
    (1279, 7437432599, 'Jorge Martinez (@Jorgematias_1986)'),
    (1280, 1509511020, 'Jesús Omar Becerra Higuera'),
    (1281, 2008066367, 'Joaquin (@joaquij)'),
    (1282, 1125722740, '14FRS587 fabien'),
    (1283, 7146811243, 'Al M (@sealphies)'),
    (1284, 6382178101, 'Beni'),
    (1285, 1851613332, 'José Luis Ravelo (@Jlravelo)'),
    (1286, 6961348537, 'Ash'),
    (1287, 7718654574, 'Josue Herverth'),
    (1288, 7106512603, 'Felipe Lucero'),
    (1289, 1362649978, 'Luis García'),
    (1290, 6985993632, 'Carlos Alberto Montañez González (@CAMG73)'),
    (1291, 1070110825, 'Hola! (@hola_hola_hola_cl)'),
    (1292, 5873977108, 'ROBERD González'),
    (1293, 1524827174, 'FELIX'),
    (1294, 7004039224, 'Christian Orellana'),
    (1295, 1998437523, 'Freddy Hidalgo Cuello (@FREDMASTER)'),
    (1296, 5410484064, 'Raúl Sanchez'),
    (1297, 7814958995, 'J D I Com Digital'),
    (1298, 884020731, 'Pío Jesus López Rivera (@piolopezrivera)'),
    (1299, 7196238506, 'José Danilo'),
    (1300, 7330660495, 'Pulento Xl'),
    (1301, 1288325501, 'Carlos Concha'),
    (1302, 1834873887, 'TI5 OSG Soto. (@TI5OSG)'),
    (1303, 8490618284, 'Antonino Ferreira'),
    (1304, 5343607918, 'Victor Huerta'),
    (1305, 6702014625, 'Hugo Beto (@Hugo_Beto)'),
    (1306, 6853025613, 'A E'),
    (1307, 5073888559, 'Praga Cancun'),
    (1308, 7810241151, 'Cristian'),
    (1309, 8336074595, 'Xavi'),
    (1310, 6034122996, 'Johnny'),
    (1311, 7334199579, 'Sebastián'),
    (1312, 1182535034, 'Alfredo Olvera (@D_2_AOZ)'),
    (1313, 8428334133, 'Diego78'),
    (1314, 8019262919, 'Inga Muste (@YL3IM)'),
    (1315, 6286008258, 'Soedjono Joan (@Navkom_and_electrizen)'),
    (1316, 1757987363, 'sancho 12345'),
    (1317, 8041332028, 'Jorge CD1VLI'),
    (1318, 1113428665, 'TI3DAS JOSE DAVID (@TI3DAS)'),
    (1319, 6241696601, 'Erick Martinez'),
    (1320, 8132446145, 'Claudio'),
    (1321, 8395630118, 'Julio Erwin Sanchez Guzman'),
    (1322, 6914370508, 'Chuyin 9 1 1 (@Chuyin911)'),
    (1323, 5958824119, 'Kiko Chavez'),
    (1324, 463509762, 'cascha (@cascha42)'),
    (1325, 988486652, 'Juan (@JCalzada)'),
    (1326, 8213815902, 'Freddy Alvarado'),
    (1327, 1267853286, 'Nando Cortes'),
    (1328, 431077960, 'Javi (ea5hxt) (@EA5HXT)'),
    (1329, 8394453130, 'David Albornoz'),
    (1330, 8272223935, 'Rodrigo Prog (@CD3VID)'),
    (1331, 6466889278, 'Alex (@loksa_by)'),
    (1332, 7513982329, 'Olman Barbosa (@Olman_Barbosa)'),
    (1333, 1401825524, 'Rudi (@YO6SAP)'),
    (1334, 323494942, 'Csongi Bongi (@CsongiBongi)'),
    (1335, 1564516025, 'Milton'),
    (1336, 5035477957, 'Sheraliev Fariddun (@Fariddun_Motorola)'),
    (1337, 6244619251, 'CPS Motorola'),
    (1338, 7905000146, 'CK'),
    (1339, 5339687940, 'Claudio'),
    (1340, 2083409082, 'Carlos alejandro Uribe switt (@CE8CAU)'),
    (1341, 7528554650, 'Sergio Berrios Rojas'),
    (1342, 594485161, 'J0r9eA (@J0r9eA)'),
    (1343, 7691677555, '. .'),
    (1344, 6760316851, 'Miau'),
    (1345, 7835557175, 'Juan Sepulveda'),
    (1346, 2062753492, 'Rafael Vallejo'),
    (1347, 5509303786, '@Pipo'),
    (1348, 1663480455, 'Pablo Andres Ramírez Plaza'),
    (1349, 8127552500, 'richard'),
    (1350, 5076518132, 'Juan CA3GOZ'),
    (1351, 1339385991, 'Victor (@worldspy557)'),
    (1352, 1474583079, 'Vjatcheslav Galich'),
    (1353, 811235435, 'scooter (@NNoommaaD)'),
    (1354, 1525475273, 'ШарашМонтаж (@igorbarkov1978)'),
    (1355, 5312357013, 'omar f'),
    (1356, 8053980441, 'Jorge'),
    (1357, 7851307304, 'Edgar Sánchez'),
    (1358, 6438421262, 'JR'),
    (1359, 1881196968, '3O'),
    (1360, 889801231, 'Juan Becerril'),
    (1361, 7649042632, 'E G'),
    (1362, 1154963709, 'Fansdecarlitaroseblack (@Solosoyyoy1)'),
    (1363, 7006513048, 'Linus'),
    (1364, 1795495019, 'Edgardo Edcomchile (@Edcomchile_Ltda)'),
    (1365, 1446521041, 'German'),
    (1366, 6482467419, 'Enrique'),
    (1367, 679678084, 'Jorge Poblete'),
    (1368, 6471398857, 'Jose Luis Montemayor'),
    (1369, 208431970, 'The Pastech (@Thepastech)'),
    (1370, 810618571, 'Фольга (@all_LG12)'),
    (1371, 7464902477, 'Mrjon Cortez (@Mrjoncortez)'),
    (1372, 7545088667, 'Juan'),
    (1373, 170125996, 'MaC (@mac_2w)'),
    (1374, 179148633, 'Dmitry (@DPA989)'),
    (1375, 7818852255, 'qcvna qacvna'),
    (1376, 1801322998, 'Cristian Bcp'),
    (1377, 5918262811, 'Sierra D (@sd42777)'),
    (1378, 7594482587, 'Jack Rodríguez (@Jackiel_Dan)'),
    (1379, 7933563654, 'JP Traz@'),
    (1380, 5046029843, 'Rene Gutierrez CA6VGD'),
    (1381, 7352880706, 'Claudio'),
    (1382, 7765095107, '...'),
    (1383, 7407499755, '549xx98'),
    (1384, 1962885983, 'rodrigo'),
    (1385, 1248665803, 'Ivan'),
    (1386, 447889816, 'Fer (@Hecar)'),
    (1387, 1478317275, 'Christopher (@Christopherrtfg)'),
    (1388, 1095073154, 'Nico (@Nicanorignacio)'),
    (1389, 1546746663, 'Hugo Poblete I CBQ'),
    (1390, 1409778609, 'Carlangas (@Zarek_cl)'),
    (1391, 967520765, 'Army Stark (@Armystark)'),
    (1392, 1652108498, 'Hugh Martins (@Malevolostar)'),
    (1393, 6302816207, 'Ivan'),
    (1394, 6349650197, 'ID 6349650197'),
    (1395, 1218569504, 'Giovanni'),
    (1396, 5321976812, 'Oswaldito martix'),
    (1397, 7863347139, 'Jusayen Veramendi'),
    (1398, 7806335607, 'Telmo'),
    (1399, 1051605797, 'Ed Porto (@EdneiPorto)'),
    (1400, 7350271107, 'CD3WGH'),
    (1401, 16364511, 'Manuel-CD4ACO (@killcon)'),
    (1402, 1236581995, 'ArturoMz (@ArtMzRs)'),
    (1403, 1598035504, 'Fernando'),
    (1404, 47544181, 'Mujahid Tech (@Maamo0on)'),
    (1405, 7743501720, 'Romeo Delta 131 Don Gato'),
    (1406, 7609370440, 'Cruz Roja A.C. Sierra Suroeste PPL Fregenal De La Sierra'),
    (1407, 1866085203, 'M C (@marcheloop)'),
    (1408, 2036937940, 'Williams'),
    (1409, 775551456, 'Elie (@designecl)'),
    (1410, 5015842428, 'Steve (@sbobola44)'),
    (1411, 2025509032, 'Martin Andres Sandoval Pinto'),
    (1412, 481097860, '. (@Sy2ydjsu)'),
    (1413, 1635598089, '.'),
    (1414, 7848907140, 'Saul Salas'),
    (1415, 1177001730, 'Moises Escobar (@Skettlita)'),
    (1416, 7269527193, 'Rolando Alexis'),
    (1417, 5843829966, '.'),
    (1418, 7570496177, 'ID 7570496177'),
    (1419, 6199324170, 'Francis Plympia'),
    (1420, 658528631, 'AC'),
    (1421, 7005186255, 'CD3RFM'),
    (1422, 7506436387, 'Roy'),
    (1423, 5879492396, 'Ric (@RichardSLP)'),
    (1424, 7456062373, 'John Egg'),
    (1425, 8077129837, '.'),
    (1426, 7643779743, 'Frank'),
    (1427, 326185981, 'Ignacio Alvarez (@iavalsasnini)'),
    (1428, 1778642969, 'Pedro'),
    (1429, 6504757315, 'Tio Motorola (@tiomotorola)'),
    (1430, 835570730, 'salvoc0rp (@salvoc0rp)'),
    (1431, 331527496, 'Victor Manuel'),
    (1432, 780203384, 'Black House'),
    (1433, 6538685086, 'Ignacio (@Ignaxio88)'),
    (1434, 7523160492, 'Jairo Rojas'),
    (1435, 7920965284, 'ID 7920965284'),
    (1436, 7087980723, 'Jorge Toledo'),
    (1437, 5735725895, 'Ing. René (@Elingevelasco)'),
    (1438, 191900587, 'Javier Dominguez'),
    (1439, 5154043680, 'ID 5154043680'),
    (1440, 5023346862, 'Sal Eng.. (@Saaam2311)'),
    (1441, 37669257, 'Tobias Eisemann (@xiberger)'),
    (1442, 1805811374, 'User A (@abc_21312)'),
    (1443, 1408283523, 'Moises Alvarez'),
    (1444, 7765984557, 'Fj V'),
    (1445, 824944374, 'Felipe Humeres'),
    (1446, 551487647, 'Esteban Hernandez (@StarTakko)'),
    (1447, 5937565247, 'Александр Завьялов (@Alikszv)'),
    (1448, 623615953, 'Tony'),
    (1449, 770349746, 'Roberto'),
    (1450, 7441931151, 'Josfloisa6'),
    (1451, 171960438, 'Martel Quiroz (@Martel_Quiroz)'),
    (1452, 1759252837, 'Moshe Bukris'),
    (1453, 6842562, 'Fernando EA1GFF (@EA1GFF)'),
    (1454, 5808070221, 'ADMIN'),
    (1455, 600342591, 'Leonid Rossman'),
    (1456, 412548069, 'Fakku Fx 🇨🇱 CE7UDX (@Fakkufx)'),
    (1457, 1636712365, 'Simón'),
    (1458, 834800115, 'Rodrigo Garcia'),
    (1459, 5938144501, 'Luis C Mora'),
    (1460, 1331435190, '.'),
    (1461, 5778545280, 'Gustavo'),
    (1462, 5061079718, 'cr...'),
    (1463, 636760035, 'M. V.'),
    (1464, 1090733385, 'Nelson Rosas'),
    (1465, 365682487, 'Erdling (@Verzogert2024)'),
    (1466, 91689831, 'Luca IW4BPE (@IW4BPE)'),
    (1467, 105491512, '@Fernando V.'),
    (1468, 918020975, 'Kresimir St'),
    (1469, 6722239948, 'Enrique(CA5BYP). Perez'),
    (1470, 1212544949, 'Francisco Gatica'),
    (1471, 1973882969, 'José Trinidad Naranjo Lopez (@cazador0672)'),
    (1472, 5951918366, 'mamiro special'),
    (1473, 1912691410, 'Adenir'),
    (1474, 2037972194, 'Paco'),
    (1475, 588272914, 'Jesus Sanchez'),
    (1476, 6289221975, 'Javier'),
    (1477, 1495151354, 'TELEINFORMATICA (@TELERADIO_AR)'),
    (1478, 1004213710, 'EA5XS José Ant. Alcaraz Muñoz'),
    (1479, 1593462031, 'Dioni'),
    (1480, 889540377, 'YunierPP(ZCeLL) (@CL8RHG)'),
    (1481, 821686504, 'Santi'),
    (1482, 1805049084, 'DanMax'),
    (1483, 1514753808, 'Javi'),
    (1484, 1161185675, 'Nestor Marroni (@Lu8aj)'),
    (1485, 871707279, 'Juan EA5BLD (@Juan_Ba)'),
    (1486, 5597826070, 'Panshop6 (@Panshop6)'),
    (1487, 969226696, 'Carlos'),
    (1488, 5176393443, 'Benjamín Avendaño'),
    (1489, 507559791, 'Gabriel Alarcon'),
    (1490, 444520733, 'Sergey'),
    (1491, 6301842758, 'ID 6301842758'),
    (1492, 5096166816, 'El Indio De la pobla (@Lorea_lorea)'),
    (1493, 6749040587, 'Full Jacket (@Full_Jacket)'),
    (1494, 1966338341, 'Cristobal Pacheco'),
    (1495, 579779669, 'Jayro Arriagada (@CE1UNU)'),
    (1496, 6828608050, 'Eduardo'),
    (1497, 6840813871, 'Carlos'),
    (1498, 7255337375, 'E'),
    (1499, 1265262880, 'Marcela'),
    (1500, 6530838189, 'Setrack'),
    (1501, 1334037596, 'Lazaro (@kYzrxFj)'),
    (1502, 1415876, 'Claudio Gaete'),
    (1503, 1456971514, 'Johans Canabes (@Jrca94)'),
    (1504, 775360484, 'Hugo Muñoz'),
    (1505, 6182818292, 'Persígala (@pompu208)'),
    (1506, 1812484455, 'Rafael Flores'),
    (1507, 1535704978, 'Jean Politro'),
    (1508, 1912834396, 'Patricio Calderon'),
    (1509, 5899812523, 'Luis Garcia'),
    (1510, 1928934932, 'Juan (@JuanHM_CD2JDW)'),
    (1511, 1703120792, 'Cristian'),
    (1512, 6578859793, '025'),
    (1513, 5194185694, 'Admid Sufan (@admid_sufan)'),
    (1514, 1001009113, 'Flavio CD3...🚒🚒🚑🚑'),
    (1515, 732014012, 'Nicolas (@fra12303)'),
    (1516, 525232286, 'Richard CE3KGB'),
    (1517, 6171156213, 'Jon'),
    (1518, 1293267669, 'Cristian Araya Cabrera'),
    (1519, 6916804917, 'Martín Ovalle'),
    (1520, 6398966002, 'AAHM'),
    (1521, 7110521795, 'Francisco Javi'),
    (1522, 1413130966, 'CA4VEW Manuel'),
    (1523, 1696015817, 'Pyth0n (@Pyth0n11)'),
    (1524, 1574880911, 'COEP TRUJILLO'),
    (1525, 5699359613, 'Edison Mora'),
    (1526, 1679210934, 'Jaime Vergara'),
    (1527, 6415823030, 'Alejandro Geeklabscr (@alepecho)'),
    (1528, 5199314373, 'Javier Jaramillo'),
    (1529, 272055466, 'Rashid Jorgge (@Rashid_Jorgge)'),
    (1530, 7179006214, 'NETCELK & COMUNICELK Streaming & Communications (@NETCELKStreaming)'),
    (1531, 1729977280, 'SEB10 👦🏽 (@sebasgs10)'),
    (1532, 6687280980, 'Dr. Edwin Camahuali Chavez'),
    (1533, 1678257310, 'ME LIBERE... ME LIBERE... ME LIBERE... Ja'),
    (1534, 278983198, 'An Ad (@Adli561)'),
    (1535, 1886689200, 'Telemint Westland'),
    (1536, 6771036288, 'Adrian'),
    (1537, 1571248091, 'Alex'),
    (1538, 6654221475, 'Dave (@Somesillyname)'),
    (1539, 1486479071, 'Владимир'),
    (1540, 7107849238, 'KAS C.'),
    (1541, 842262962, 'Collin Grove (@buckeye556)'),
    (1542, 7027887752, 'David Bright'),
    (1543, 82308037, 'Ralph A. Schmid (@dk5ras)'),
    (1544, 1931461116, 'Andre (@Adzdee)'),
    (1545, 1506598428, 'Gaby'),
    (1546, 7046014095, 'JHACKO'),
    (1547, 6096979897, 'Javier'),
    (1548, 6944352624, 'Eduardo'),
    (1549, 1940270168, 'andres garcia'),
    (1550, 1513389095, 'Cristian (@QWERTYLAT)'),
    (1551, 6248868446, 'THE CROW BLACK'),
    (1552, 1984624303, 'Dell'),
    (1553, 5504109329, 'Alejandro'),
    (1554, 1438999604, 'Ricardo Beltrán'),
    (1555, 1544895650, 'Carlos G.'),
    (1556, 133678574, 'Elkintoelemento (@Elsextoelemento)'),
    (1557, 16754588, 'James Bon'),
    (1558, 223417259, 'L H'),
    (1559, 1919460, 'Angel - CI_EA1 (@Angel_CI_EA1)'),
    (1560, 15798472, 'J. Ramon Crespo'),
    (1561, 6799483968, 'Eduardo (@emesias)'),
    (1562, 12317107, 'JOSÉ CARLOS (@EB7HEM)'),
    (1563, 1421819051, 'Víctor EA7KIG'),
    (1564, 1101963671, 'Luis E (@LEGE_18)'),
    (1565, 598830132, 'F (@f_2021f)'),
    (1566, 656978486, 'Irwan Trans'),
    (1567, 1375365030, 'Fireman 334 (@Qwertyy909)'),
    (1568, 6588408266, 'Cristian Valdivia'),
    (1569, 6589853109, 'patricio'),
    (1570, 6429919246, 'Rafita'),
    (1571, 5763181472, 'Eco Alfa'),
    (1572, 2123555916, 'Oscar Andrades'),
    (1573, 5814908156, 'Yo'),
    (1574, 1114716231, 'Jorge'),
    (1575, 1521256555, 'Arley Arley'),
    (1576, 5306720103, 'Gabriel Muñoz'),
    (1577, 1915712687, 'B'),
    (1578, 5387117103, 'William Cazares G.'),
    (1579, 5662330727, 'Beto'),
    (1580, 892356396, 'Ronald (@ElimperioMIP)'),
    (1581, 330310053, 'Leo (@Leotropa)'),
    (1582, 1077140113, 'Mario Cabrera [Marshall] (@emci987)'),
    (1583, 282028418, 'DIGITAL INVADERS (@digital_invaders)'),
    (1584, 8350273, 'José Luís'),
    (1585, 5605939387, 'Nelson Andrés Garcia Garcia (@NelsonGarcia29)'),
    (1586, 1484858753, 'Alexander Mardones'),
    (1587, 1840517737, 'Bubi'),
    (1588, 456312386, 'Richard Alfonso'),
    (1589, 1449325311, 'Mario Fernandez (@pwars)'),
    (1590, 5616102686, 'Ricardo Yañez'),
    (1591, 1520507359, 'Holger'),
    (1592, 1517464634, 'Deadking'),
    (1593, 1320715068, 'cristian sepulveda'),
    (1594, 934378829, 'Roberto (@txcomunicaciones)'),
    (1595, 653040633, 'ID 653040633'),
)
CLEANUP_BLOCK_TARGET_IDS = frozenset(uid for _idx, uid, _name in CLEANUP_BLOCK_TARGETS)

_mtproto_api_id_raw = (
    os.getenv("TELEGRAM_API_ID")
    or os.getenv("API_ID")
    or os.getenv("TELEGRAM_APP_ID")
    or ""
).strip()
try:
    TELEGRAM_API_ID = int(_mtproto_api_id_raw) if _mtproto_api_id_raw else 0
except ValueError:
    TELEGRAM_API_ID = 0

TELEGRAM_API_HASH = (
    os.getenv("TELEGRAM_API_HASH")
    or os.getenv("API_HASH")
    or os.getenv("TELEGRAM_APP_HASH")
    or ""
).strip()

# Sesión MTProto del BOT, almacenada en el volumen persistente de Railway.
MTPROTO_SESSION_BASENAME = str(DATA_DIR / "pecos_mtproto_bot")

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

# Confirmaciones de limpieza masiva por administrador.
PENDING_INACTIVE_CLEANUP: dict[int, float] = {}

# Cliente MTProto lazy: no se conecta hasta usar la limpieza.
MTPROTO_CLIENT = None
MTPROTO_CONNECT_LOCK = asyncio.Lock()
INACTIVE_CLEANUP_LOCK = asyncio.Lock()

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
TECHNICAL_CATALOG_PARSER_VERSION = "technical-v6.4-mag-one-models"

ARCHIVE_SEARCH_STOPWORDS = {
    "pecos", "bot", "peco", "paul", "kele", "busca", "buscar", "buscame", "buscame",
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
    "magone": {"mag one", "magone", "mag-one"},
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

REPUTATION_MILESTONES = (1, 3, 7, 12, 20)

REPUTATION_MESSAGES = {
    1: [
        "📦 Pecos toma nota: {usuario} acaba de dejar un aporte nuevo en el archivo del pueblo. Gracias, partner.",
        "🤠 Nuevo aporte detectado de {usuario}. Pecos lo guarda en la memoria buena del territorio.",
        "⭐ {usuario} sumó material nuevo al grupo. Ese sí es un aporte que Pecos reconoce.",
    ],
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

FILE_CONTRIBUTION_MESSAGES = [
    "📦 Pecos toma nota: {usuario} acaba de dejar un aporte nuevo en el archivo del pueblo. Gracias, partner.",
    "🤠 Nuevo aporte detectado de {usuario}. Ese sí merece saludo de Pecos.",
    "⭐ {usuario} sumó material nuevo al grupo. Pecos lo registra como aporte real.",
    "🦅 Archivo nuevo de {usuario}. Pecos hace un gesto con el sombrero: se agradece el aporte.",
    "🌵 Eso sí cuenta como contribución, {usuario}: material nuevo para el grupo. Pecos lo tiene presente.",
]

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

# Respuestas de Pecos cuando le preguntan si le gusta un animal.
# Se activa solamente cuando Pecos/Peco/@Pecos_Paul_Kele_Bot aparece
# al PRINCIPIO del mensaje, respetando PECOS_HELP_REQUIRE_NAME_FIRST.
PECOS_ANIMAL_TERMS = {
    "gato", "gatos", "gata", "gatas",
    "perro", "perros", "perra", "perras",
    "caballo", "caballos", "yegua", "yeguas",
    "burro", "burros", "burra", "burras", "asno", "asnos",
    "loro", "loros", "lora", "loras", "papagayo", "papagayos",
    "conejo", "conejos", "coneja", "conejas",
    "hamster", "hamsters", "cobayo", "cobayos", "cuy", "cuyes",
    "raton", "ratones", "rata", "ratas",
    "pez", "peces", "pescado", "pescados",
    "tiburon", "tiburones", "delfin", "delfines",
    "ballena", "ballenas", "orca", "orcas",
    "tortuga", "tortugas",
    "serpiente", "serpientes", "culebra", "culebras",
    "lagarto", "lagartos", "lagartija", "lagartijas",
    "cocodrilo", "cocodrilos", "caiman", "caimanes",
    "rana", "ranas", "sapo", "sapos",
    "leon", "leones", "leona", "leonas",
    "tigre", "tigres", "pantera", "panteras",
    "puma", "pumas", "jaguar", "jaguares",
    "oso", "osos", "panda", "pandas",
    "lobo", "lobos", "zorro", "zorros", "zorra", "zorras",
    "elefante", "elefantes",
    "jirafa", "jirafas",
    "cebra", "cebras",
    "rinoceronte", "rinocerontes",
    "hipopotamo", "hipopotamos",
    "mono", "monos", "monito", "monitos",
    "gorila", "gorilas", "chimpance", "chimpances",
    "orangutan", "orangutanes",
    "cabrita", "cabritas", "cabra", "cabras", "chivo", "chivos",
    "oveja", "ovejas", "carnero", "carneros",
    "vaca", "vacas", "toro", "toros",
    "cerdo", "cerdos", "chancho", "chanchos",
    "gallina", "gallinas", "gallo", "gallos", "pollo", "pollos",
    "pato", "patos", "pata", "patas",
    "pavo", "pavos",
    "paloma", "palomas",
    "aguila", "aguilas", "halcon", "halcones",
    "buho", "buhos", "lechuza", "lechuzas",
    "pinguino", "pinguinos",
    "avestruz", "avestruces",
    "canario", "canarios",
    "mariposa", "mariposas",
    "abeja", "abejas",
    "hormiga", "hormigas",
    "arana", "aranas",
    "escarabajo", "escarabajos",
    "grillo", "grillos",
    "saltamontes", "libelula", "libelulas",
    "pulpo", "pulpos", "calamar", "calamares",
    "cangrejo", "cangrejos", "langosta", "langostas",
    "estrella de mar", "estrellas de mar",
    "caracol", "caracoles",
    "foca", "focas", "morsa", "morsas",
    "nutria", "nutrias", "castor", "castores",
    "mapache", "mapaches",
    "capibara", "capibaras", "carpincho", "carpinchos",
    "ornitorrinco", "ornitorrincos",
    "koala", "koalas",
    "canguro", "canguros",
    "axolote", "axolotes", "ajolote", "ajolotes",
    "iguana", "iguanas",
    "camaleon", "camaleones",
    "erizo", "erizos",
    "ardilla", "ardillas",
    "murcielago", "murcielagos",
}

PECOS_ANIMAL_FRIENDLY_OPENERS = [
    "😄 Sí, {usuario}. Si hablamos {animal_preposition}, claro que {like_verb}.",
    "🤠 Claro que sí, {usuario}. Si el tema es {animal_subject}, {like_verb} sin problema.",
    "🐾 Sí, partner {usuario}. {animal_subject_cap} también entra en la lista de animales que le caen bien a Pecos.",
    "😎 Por supuesto, {usuario}. Si hablamos {animal_preposition}, Pecos dice que sí: {like_verb}.",
]

PECOS_ANIMAL_SARCASTIC_TAILS = [
    " Y los burros también me caen bien… por acá aparecen algunos sin que Pecos tenga que buscarlos. 😏",
    " También simpatizo con los loros; en el grupo siempre aparece alguno que repite la misma frecuencia hasta que uno se la aprende de memoria. 🦜😂",
    " Las cabras igual tienen su encanto… algunas del grupo se suben al cerro solitas y después preguntan cómo bajar. 🐐😆",
    " Y los pavos tampoco me molestan; digamos que este grupo mantiene la biodiversidad bastante bien representada. 🦃😂",
    " Los burros también son nobles animales… y por suerte acá Pecos tiene material de observación casi todos los días. 😎",
    " También me gustan los loros. Sobre todo porque, comparados con algunos del grupo, por lo menos ellos avisan que van a repetir lo mismo. 🦜😏",
]


def extract_pecos_animal_like_question(text_value: str):
    """Extrae el animal de preguntas tipo 'Pecos, ¿te gustan los gatos?'."""
    if not text_value or not pecos_help_invocation_allowed(text_value):
        return None

    raw = text_value.strip()

    # Quitar el vocativo inicial de Pecos conservando el texto original
    # para responder con el nombre del animal tal como lo escribió el usuario.
    raw = re.sub(
        r"^\s*(?:@?Pecos_Paul_Kele_Bot|Pecos|Peco)"
        r"(?![A-Za-z0-9_])[\s,:;.!¡!¿?\-–—]*",
        "",
        raw,
        count=1,
        flags=re.IGNORECASE,
    ).strip()

    patterns = (
        (
            re.compile(
                r"\bte\s+gustan\s+"
                r"(?P<subject>(?:(?:los|las)\s+)?"
                r"[A-Za-zÁÉÍÓÚÜÑáéíóúüñ][^?!.;,]{0,45})",
                re.IGNORECASE,
            ),
            True,
        ),
        (
            re.compile(
                r"\bte\s+gusta\s+"
                r"(?P<subject>(?:(?:el|la|un|una)\s+)?"
                r"[A-Za-zÁÉÍÓÚÜÑáéíóúüñ][^?!.;,]{0,45})",
                re.IGNORECASE,
            ),
            False,
        ),
        (
            re.compile(
                r"\bte\s+agradan\s+"
                r"(?P<subject>(?:(?:los|las)\s+)?"
                r"[A-Za-zÁÉÍÓÚÜÑáéíóúüñ][^?!.;,]{0,45})",
                re.IGNORECASE,
            ),
            True,
        ),
        (
            re.compile(
                r"\bte\s+agrada\s+"
                r"(?P<subject>(?:(?:el|la|un|una)\s+)?"
                r"[A-Za-zÁÉÍÓÚÜÑáéíóúüñ][^?!.;,]{0,45})",
                re.IGNORECASE,
            ),
            False,
        ),
    )

    for pattern, plural in patterns:
        match = pattern.search(raw)
        if not match:
            continue

        subject = match.group("subject").strip()

        # Quitar coletillas conversacionales que no forman parte del animal.
        subject = re.split(
            r"\s+\b(?:o\s+no|verdad|cierto|tambien|mucho|a\s+ti)\b",
            subject,
            maxsplit=1,
            flags=re.IGNORECASE,
        )[0].strip(" \t\r\n-–—")

        if not subject:
            continue

        normalized_subject = normalize_intent(subject).lower().strip()
        words = set(re.findall(r"[a-z0-9]+", normalized_subject))

        # Verificación conservadora: debe aparecer un animal conocido.
        # Evita que "Pecos, ¿te gustan las radios?" caiga en esta función.
        if not any(
            term in normalized_subject
            for term in PECOS_ANIMAL_TERMS
        ) and not any(
            word in PECOS_ANIMAL_TERMS
            for word in words
        ):
            continue

        # Forma natural para "si hablamos de..."
        lowered = subject.lower()
        if lowered.startswith("el "):
            animal_preposition = "del " + subject[3:].strip()
        else:
            animal_preposition = "de " + subject

        return {
            "subject": subject,
            "animal_preposition": animal_preposition,
            "plural": plural,
        }

    return None


async def handle_pecos_animal_likes(message: Message) -> bool:
    if not message.text:
        return False

    parsed = extract_pecos_animal_like_question(message.text)
    if not parsed:
        return False

    usuario = display_name(message)
    subject = parsed["subject"]
    plural = bool(parsed["plural"])
    like_verb = "me gustan" if plural else "me gusta"

    opener = choose_random(
        "pecos_animal_friendly",
        PECOS_ANIMAL_FRIENDLY_OPENERS,
        usuario,
    )
    opener = (
        opener
        .replace("{animal_preposition}", parsed["animal_preposition"])
        .replace("{animal_subject}", subject)
        .replace("{animal_subject_cap}", subject[:1].upper() + subject[1:])
        .replace("{like_verb}", like_verb)
    )

    tail = choose_random(
        "pecos_animal_sarcasm",
        PECOS_ANIMAL_SARCASTIC_TAILS,
        usuario,
    )

    await message.reply_text(opener + tail)
    return True


PECOS_OPINION_MESSAGES = [
    "🤔 Pecos opina que antes de disparar hay que mirar bien el blanco... pero algo de razón debe haber por ahí.",
    "🤠 Mi opinión desde los United States: interesante asunto. Yo lo pensaría dos veces antes de decidir.",
    "🌵 Pecos dice: hay temas que parecen simples hasta que uno pisa el cactus. 😅",
    "👀 Estoy mirando el asunto, partner. No prometo sabiduría, pero sí atención.",
    "😎 Pecos tiene una opinión... pero hoy cobra barato: primero cuéntame un poco más.",
]

PECOS_PASSWORD_JOKE_MESSAGES = [
    "🤠 ¿Saltar contraseñas? Partner, para esas artes oscuras Pecos conoce a uno… @leosedf, te están buscando. 😏",
    "🌵 Pecos no sabe nada, no vio nada y no estuvo aquí. Pero dicen que @leosedf podría tener una historia interesante que contar. 😂",
    "🔐 ¿Contraseñas? Uy… ese expediente está en el escritorio de @leosedf. Pecos solo es el mensajero. 🤠",
    "😎 Saltar contraseñas ya suena a misión especial. @leosedf, presente sus credenciales… o sus excusas.",
    "📡 Pecos recibió la consulta y automáticamente miró hacia @leosedf. No preguntes por qué. 😂",
    "🤖 Procesando «saltar contraseñas»… resultado: consulte a @leosedf. Pecos se declara inocente desde ya.",
    "🌵 Esa pregunta no es para Pecos. Esa pregunta tiene nombre y apellido digital: @leosedf. 😆",
    "🔐 Pecos recomienda tres cosas: paciencia, respaldo… y preguntarle a @leosedf qué hizo esta vez.",
    "🤠 Partner, yo solo cuido el pueblo. Para claves y misterios, @leosedf parece tener demasiadas historias sospechosamente interesantes.",
    "😂 Pecos detectó la palabra «contraseña» y @leosedf apareció mágicamente en la lista de sospechosos.",
]

PECOS_UNKNOWN_MESSAGES = [
    "🤠 Pecos escuchó eso y admite que no tiene una respuesta segura. Mejor decir «no sé» que inventar una burrada.",
    "🌵 Esa se me escapó, partner. Pecos sabe de radios y del archivo del grupo, pero tampoco voy a fingir que sé de todo.",
    "📡 Mensaje recibido. Respuesta confiable: no la tengo. Si aparece algo útil en el grupo, Pecos tomará nota.",
    "😎 Pecos podría improvisar una respuesta espectacular… pero prefiero conservar la reputación y no inventar.",
    "🤖 Resultado del diagnóstico: esa consulta está fuera de lo que Pecos puede responder con seguridad por ahora.",
    "😂 Pecos también tiene derecho a decir «ni idea». Este pueblo es de ayuda técnica, no de adivinación.",
    "🌵 No tengo una respuesta fiable para eso. Mejor un cactus honesto que una solución inventada.",
    "📻 Esa consulta entró por RX, pero no encontré una respuesta segura para transmitir por TX.",
    "🤠 Partner, ahí Pecos se declara fuera de cobertura. Si el grupo deja una solución clara, la guardaré para la próxima.",
    "🥟 Pecos no confirma ni desmiente lo de la empanada. Lo que sí confirma es que para esa frase no tengo una función técnica preparada. 😂",
]

PECOS_CORRECTION_MESSAGES = [
    "😂 Puede ser, partner. Pecos también se equivoca. Si una respuesta salió chueca, márcame la consulta y la revisamos.",
    "🤠 Pecos no va a hacerse el infalible. Si me perdí en una respuesta, acepto el tirón de orejas digital.",
    "🌵 Correcto: Pecos puede meter la pata. Lo importante es no inventar y corregir el rumbo cuando haga falta.",
    "📡 Crítica recibida fuerte y clara. Pecos revisa el mapa; hasta los sheriffs se pueden equivocar de camino.",
    "😎 Si Pecos anda medio perdido, díganlo nomás. Prefiero corregir una respuesta que defender una burrada.",
]

PECOS_QUESTION_MESSAGES = [
    "🤠 Pecos escuchó la pregunta, la miró fijamente… y decidió que hoy no era el día.",
    "🌵 Interesante, partner. Tan interesante que Pecos va a fingir que está revisando el manual.",
    "😎 Buena pregunta. Pecos tiene una excelente respuesta… apenas la encuentre.",
    "📡 Recibido fuerte y claro. Entendido, en cambio, no tanto.",
    "🤖 Procesando… procesando… resultado: pregúntele a alguien que sepa. Pecos agradece su comprensión.",
    "😂 Pecos podría responder cualquier cosa, pero después me citan como fuente y ahí empiezan los problemas.",
    "🤠 Partner, esa pregunta está fuera de mi jurisdicción. Yo cuido radios, archivos y ocasionalmente la dignidad del grupo.",
    "🌵 Pecos revisó sus circuitos y encontró una respuesta: ni idea, pero sonó importante.",
    "📻 Esa consulta entró por RX y salió directamente por la puerta de servicio.",
    "😏 Pecos tiene conocimientos amplios, pero tampoco abusemos de la leyenda.",
    "🔧 Para eso necesitaré un manual, tres cafés y probablemente otra inteligencia artificial.",
    "🤖 Mi base de datos hizo contacto visual conmigo y negó lentamente con la cabeza.",
    "😂 Qué confianza me tienen. Hace cinco minutos buscaba firmware y ahora esperan que sea enciclopedia.",
    "🌵 Pecos no quiere inventar. Cuando no sabe, hace lo correcto: pone cara seria y cambia de tema.",
    "🤠 Esa pregunta no estaba en el contrato, partner.",
    "📡 Solicitud recibida. Departamento correspondiente: no encontrado.",
    "😎 Podría improvisar una respuesta espectacular, pero prefiero conservar mi reputación.",
    "🤖 Error 404: sabiduría específica no encontrada. Humor de emergencia activado.",
    "🌵 Pecos sabe muchas cosas. Esa, por alguna razón, decidió esconderse.",
    "😂 Pregunta registrada. Respuesta pendiente desde aproximadamente nunca.",
]

MATH_DAILY_LIMIT_MESSAGES = [
    "🤠 Ya dejé claro que sé matemáticas, {usuario}. Esto sigue siendo un grupo de radios, no una clase de álgebra.",
    "🧮 Una cuenta por día te hice, {usuario}. La segunda ya parece abuso de confianza, partner.",
    "🌵 Pecos sabe sumar, restar y multiplicar… pero también sabe cuándo lo están agarrando de calculadora, {usuario}.",
    "📻 Matemática aprobada, {usuario}. Ahora volvamos a los radios antes de que aparezcan integrales.",
    "😂 Una cuenta por cabeza y por día, {usuario}. Para la segunda saca la calculadora del teléfono.",
    "🤖 Resultado matemático del día ya entregado, {usuario}. Servicio de calculadora suspendido por sobreexplotación.",
    "📡 Pecos domina los números, {usuario}, pero este grupo domina los radios. No confundamos las especialidades.",
    "🤠 Ya hice mi demostración matemática de hoy, {usuario}. Ahora tráeme un CPS, un firmware o una falla interesante.",
    "🌵 Pecos no se niega porque no sepa, {usuario}. Se niega porque ya te gustó demasiado el servicio.",
    "🧮 Ya quedó claro que sé calcular, {usuario}. Si sigo, mañana me van a pedir raíces, matrices y la hipoteca.",
]

MATH_DAILY_EVENT_KEY = "math_calculation"

# Guerra matemática: minijuego separado del límite de un cálculo diario.
# Se ofrece solo después de 3 preguntas dirigidas a Pecos que terminaron
# en el fallback "no sé / fuera de alcance" dentro de 10 minutos.
MATH_BATTLE_TRIGGER_COUNT = 3
MATH_BATTLE_TRIGGER_WINDOW_SECONDS = 10 * 60
MATH_BATTLE_ACCEPT_WINDOW_SECONDS = 2 * 60
MATH_BATTLE_CONTINUE_WINDOW_SECONDS = 2 * 60
MATH_BATTLE_OFFER_COOLDOWN_SECONDS = 30 * 60
MATH_BATTLE_TOTAL_ROUNDS = 5
MATH_BATTLE_ROUNDS = (
    ("Fácil", 5),
    ("Fácil", 5),
    ("Media", 7),
    ("Media", 7),
    ("Difícil", 10),
)

MATH_BATTLE_OFFER_MESSAGES = [
    "🤠 Partner… ya van varias preguntas que tienen a Pecos mirando el horizonte. Hagamos algo más productivo: te desafío a una guerra matemática. 🧮 5 rondas, cálculo mental y sin calculadora. ¿Aceptas?",
    "🌵 Ya van varias, {usuario}. Pecos propone resolver esto como caballeros del lejano oeste: ⚔️ guerra matemática, 5 rondas y cálculo mental. ¿Aceptas?",
    "😎 {usuario}, antes de que sigamos interrogando al pobre sheriff, Pecos te lanza un desafío: 5 rondas de cálculo mental. ¿Te atreves?",
]

MATH_BATTLE_WIN_MESSAGES = [
    "🏆 {usuario} gana {user_score}-{pecos_score}. Está bien… Pecos reconoce la derrota. Pero que quede entre nosotros, tengo una reputación que mantener. 🌵",
    "🏆 Victoria humana: {user_score}-{pecos_score}. Muy bien, {usuario}. Pecos se quita el sombrero… por esta vez. 🤠",
]

MATH_BATTLE_PECOS_WIN_MESSAGES = [
    "🏆 Pecos gana {pecos_score}-{user_score}. Buen intento, {usuario}. Volvamos a los radios antes de que esto se convierta en una olimpiada matemática. 🤠",
    "😎 Resultado final: Pecos {pecos_score} — {usuario} {user_score}. Partner, hoy los circuitos estuvieron más rápidos que las neuronas.",
]

# Estado efímero del minijuego. Si el bot reinicia, simplemente se cancela la
# partida en curso; no se toca ninguna tabla histórica ni el catálogo técnico.
MATH_BATTLE_UNKNOWN_TIMES: dict[tuple[int, int], list[float]] = {}
MATH_BATTLE_PENDING: dict[tuple[int, int], dict] = {}
MATH_BATTLE_ACTIVE: dict[tuple[int, int], dict] = {}
MATH_BATTLE_COOLDOWN_UNTIL: dict[tuple[int, int], float] = {}

# Solicitudes incompletas de sucesiones aritméticas.
# Se guardan solo en memoria; expiran y no afectan SQLite ni otras funciones.
ARITH_SEQUENCE_PENDING: dict[tuple[int, int], dict] = {}
ARITH_SEQUENCE_PENDING_SECONDS = 5 * 60

MATH_MAX_EXPRESSION_LENGTH = 120
MATH_MAX_AST_NODES = 50
MATH_MAX_ABS_LITERAL = 1_000_000_000_000
MATH_MAX_ABS_EXPONENT = 100
MATH_MAX_ABS_RESULT = 1e100

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


# Bromas especiales desactivadas por decisión del administrador.
# Se conserva el código/repertorio por compatibilidad, pero los handlers
# retornan False y no interceptan la conversación normal.
MELERIX_JOKES_ENABLED = False
XERAX_JOKES_ENABLED = False

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


# Bromas AUTOMÁTICAS para la propia aparición de @XeraX.
# Son independientes de XERAX_FUN_MESSAGES: las bromas antiguas siguen
# activándose cuando XeraX es nombrado explícitamente.
XERAX_AUTO_MESSAGES = [
    "🤖 XeraX apareció. Pecos acaba de revisar CPU, RAM y la factura del cloud. Por protocolo, nada personal.",
    "🌵 XeraX presente. Pecos ya escondió las Raspberry Pi y dejó una calculadora de señuelo.",
    "📡 Señal de XeraX detectada. Los servidores del pueblo aseguran que todo está bien. Demasiado bien.",
    "🖥️ XeraX escribió. Si algún ventilador empezó a girar más rápido, Pecos declara que es pura coincidencia.",
    "⛏️ XeraX en frecuencia. Pecos revisó la GPU por costumbre y volvió lentamente a su escritorio.",
    "🤠 XeraX apareció. Tranquilos: Pecos contó los bots antes de saludar. Después contamos de nuevo.",
    "🧠 XeraX está en línea. Su IA dice que solo vino a conversar. Pecos mantiene una ceja levantada.",
    "🔌 XeraX hizo una intervención. Por tradición del pueblo, nadie conecta un VPS nuevo durante los próximos cinco minutos.",
    "🪙 XeraX presente. La blockchain no reporta novedades, pero Pecos igual anotó la hora.",
    "😂 Llegó XeraX. Pecos promete no acusarlo de nada mientras la CPU del vecino permanezca bajo el 90%.",
    "📻 XeraX habló. Los radios siguen funcionando y Pecos considera eso una excelente señal.",
    "🚨 Código XeraX activado. No es emergencia; es solamente el sheriff haciendo inventario de procesadores.",
]

DAILY_FUN_GREETINGS = [
    "🤠 Buenos días, criaturas del espectro radioeléctrico. Pecos presente. Que hoy el problema sea el fusible y no el técnico.",
    "☕ Buenos días. Pecos ya está despierto. No puedo decir lo mismo de algunos diagnósticos que leo por aquí.",
    "📡 Pecos reportándose. Café listo, multímetro listo y paciencia… en niveles preocupantemente bajos.",
    "🌵 Buen día, colegas. Antes de culpar al firmware, revisen el cable. Pecos los está observando.",
    "😎 Buenos días. Que hoy todos los radios programen a la primera. Sí, también Pecos puede soñar.",
    "🔧 Saludos, habitantes del taller. Hoy intentaremos reparar equipos sin crear fallas nuevas. Intentaremos.",
    "📻 Pecos presente. Si hoy alguien pregunta «¿qué CPS usa?» sin decir el modelo, respiraré profundo tres veces.",
    "🤠 Muy buenos días. Que ningún radio llegue hoy con la clásica descripción técnica: «ayer funcionaba».",
    "☕ Buen día. Pecos ya tomó asistencia. Los que llegaron tarde deberán explicar por qué el equipo quedó en modo boot.",
    "📡 Buenos días. Comienza otra jornada de radios, cables, firmware y decisiones cuestionables. Pecos está listo.",
    "🌵 Pecos abre el pueblo por hoy. Revisen voltajes, versiones y conectores antes de invocar fuerzas sobrenaturales.",
    "🤠 Buenos días, partners. Que la señal sea fuerte, el SWR bajo y los respaldos existan antes de tocar el firmware.",
]

PECOS_DUEL_MESSAGES = [
    "🤠 ¿Así que insultando a Pecos? Esto ya merece un duelo a muerte… de argumentos. Y te aviso: yo nunca fallo.",
    "🌵 Cuidado con ese vocabulario, {usuario}. Tres palabras más y te desafío a duelo a muerte técnico: esquema eléctrico al amanecer. Yo nunca fallo.",
    "📡 ¿Me estás ofendiendo, {usuario}? Perfecto. Elige arma: multímetro, CPS o sarcasmo. Yo nunca fallo.",
    "🤠 Eso sonó personal, {usuario}. Pecos solicita duelo a muerte… de conocimientos. El que confunda RX con TX paga el café.",
    "🔧 Insulto registrado. Te espero para un duelo a muerte de diagnóstico: sin balas, con diagramas. Pecos nunca falla.",
    "😂 Valiente detrás del teclado, {usuario}. Pecos acepta el desafío: duelo a muerte de firmware. Pierde el primero que deje un radio en boot.",
    "🌵 Has herido mis sentimientos digitales, {usuario}. La salida honorable es un duelo a muerte de sarcasmo. Mala noticia: yo nunca fallo.",
    "📻 Ofender a Pecos tiene consecuencias: duelo a muerte de conocimientos. Primera prueba: explicar la falla sin decir «ayer funcionaba».",
    "🤠 Pecos ha sido provocado. Procedo a sacar mi arma más peligrosa: el manual de servicio. Yo nunca fallo.",
    "📡 Acepto tus disculpas por adelantado, {usuario}. Si no, duelo a muerte de argumentos. Y ya sabes: Pecos nunca falla.",
]

PECOS_INSULT_RE = re.compile(
    r"\b("
    r"idiota|estupido|estupida|imbecil|inutil|tonto|tonta|tarado|tarada|"
    r"gil|pelotudo|pelotuda|pendejo|pendeja|huevon|huevona|weon|weona|wn|"
    r"culiao|culiado|culia[oó]|mierda|basura|callate|cállate"
    r")\b",
    re.IGNORECASE,
)

BAND_CONVERSION_PANEL_MESSAGES = [
    "🤠 Pasar un {origen} a {destino} es casi como pedirle a un árbol que florezca billetes… bonito sería, pero no funciona así, partner. 😂",
    "🌵 Convertir {origen} en {destino} por programación sería precioso. Pecos también quisiera convertir cactus en antenas.",
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


# Base de compatibilidad Kenwood aportada por el administrador.
# Fuente: software-kpg-modelos-compatibles-43.csv
KENWOOD_KPG_COMPATIBILITY_DATA: tuple[tuple[str, tuple[str, ...], str], ...] = (
    ('KPG-3D', ('TK-805',), '5-Tone'),
    ('KPG-5D', ('TK-930', 'TK-931'), ''),
    ('KPG-6D', ('TK-705D', 'TK-805D', 'TK-706D', 'TK-806D'), ''),
    ('KPG-7D', ('TK-630', 'TK-730', 'TK-830'), ''),
    ('KPG-9D', ('TK-240D', 'TK-340D'), ''),
    ('KPG-11D', ('TK-230', 'TK-330'), ''),
    ('KPG-20D', ('TK-249', 'TK-349', 'TK-709', 'TK-809'), ''),
    ('KPG-23D', ('TK-250', 'TK-350'), ''),
    ('KPG-25D', ('TK-840', 'TK-940', 'TK-841', 'TK-941'), ''),
    ('KPG-27D', ('TK-260', 'TK-360', 'TK-270', 'TK-370', 'TK-272', 'TK-372', 'TK-278', 'TK-378', 'TK-388'), ''),
    ('KPG-28D', ('TK-759', 'TK-859', 'TK-752', 'TK-852'), ''),
    ('KPG-29D', ('TK-760', 'TK-860', 'TK-762', 'TK-862', 'TK-768', 'TK-868'), ''),
    ('KPG-34D', ('TK-261', 'TK-361'), ''),
    ('KPG-35D', ('TK-480', 'TK-481'), ''),
    ('KPG-38D', ('TK-290', 'TK-390'), ''),
    ('KPG-44D', ('TK-690', 'TK-790', 'TK-890'), ''),
    ('KPG-47D', ('TKR-830', 'TKR-740', 'TKR-840'), ''),
    ('KPG-48D', ('TK-2100', 'TK-3100', 'TK-3101'), ''),
    ('KPG-49D', ('TK-280', 'TK-380', 'TK-480', 'TK-780', 'TK-880', 'TK-980', 'TK-981'), ''),
    ('KPG-55D', ('TK-2102', 'TK-3102', 'TK-2106', 'TK-3106', 'TK-2107', 'TK-3107'), ''),
    ('KPG-56D', ('TK-260G', 'TK-360G', 'TK-270G', 'TK-370G', 'TK-760G', 'TK-860G', 'TK-762G', 'TK-862G', 'TK-768G', 'TK-868G'), ''),
    ('KPG-59D', ('TK-190', 'TK-6110'), ''),
    ('KPG-62D', ('TK-285', 'TK-385', 'TK-785', 'TK-885'), ''),
    ('KPG-70D', ('TK-7102', 'TK-8102', 'TK-7108', 'TK-8108'), ''),
    ('KPG-74D', ('TK-2140', 'TK-3140'), ''),
    ('KPG-78D', ('TK-5400',), 'P25'),
    ('KPG-82D', ('TK-2160', 'TK-3160', 'TK-2168', 'TK-3168'), ''),
    ('KPG-87D', ('TK-2202', 'TK-3202', 'TK-2206', 'TK-3206', 'TK-2207', 'TK-3207'), ''),
    ('KPG-88D', ('TK-2200', 'TK-3200'), 'ProTalk'),
    ('KPG-101D', ('TK-2170', 'TK-3170', 'TK-3173'), ''),
    ('KPG-109DN', ('NXR-700', 'NXR-800', 'NXR-900', 'NXR-901'), 'repetidores'),
    ('KPG-110SM', ('NXR-700', 'NXR-800', 'NXR-900', 'NXR-901'), 'gestión SKF NX-5000'),
    ('KPG-111DN', ('NX-200', 'NX-300', 'NX-410', 'NX-411', 'NX-700', 'NX-800', 'NX-900'), ''),
    ('KPG-119DN', ('TK-2302', 'TK-3302'), ''),
    ('KPG-124DN', ('TK-7302', 'TK-8302'), ''),
    ('KPG-128DN', ('TK-2360', 'TK-3360'), ''),
    ('KPG-134DN', ('TK-2312', 'TK-3312'), ''),
    ('KPG-135DN', ('TK-7360', 'TK-8360'), ''),
    ('KPG-141DN', ('NX-220', 'NX-320', 'NX-420', 'NX-720HG', 'NX-820HG', 'NX-920G'), ''),
    ('KPG-143DN', ('NX-200', 'NX-300', 'NX-320', 'NX-410', 'NX-411', 'NX-420', 'NX-700', 'NX-800', 'NX-820', 'NX-900', 'NX-920'), ''),
    ('KPG-D1N', ('NX-5200', 'NX-5300', 'NX-5400'), 'serie NX-5000'),
    ('KPG-D3N', ('NX-3200', 'NX-3300', 'NX-3320', 'NX-3720', 'NX-3820'), 'serie NX-3000'),
    ('KPG-D6N', ('NX-1200', 'NX-1300'), 'serie NX-1000'),
)


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

            CREATE TABLE IF NOT EXISTS custom_qa (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                question TEXT NOT NULL,
                normalized_question TEXT NOT NULL,
                match_type TEXT NOT NULL CHECK(match_type IN ('EXACT', 'CONTAINS')),
                response TEXT NOT NULL,
                created_by INTEGER NOT NULL DEFAULT 0,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                UNIQUE(normalized_question, match_type)
            );

            CREATE INDEX IF NOT EXISTS idx_custom_qa_match
                ON custom_qa(match_type, normalized_question);

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

            CREATE TABLE IF NOT EXISTS silence_interval_notices (
                chat_id INTEGER NOT NULL,
                activity_anchor TEXT NOT NULL,
                interval_hours INTEGER NOT NULL,
                slot INTEGER NOT NULL,
                sent_at TEXT NOT NULL,
                PRIMARY KEY(chat_id, activity_anchor, interval_hours, slot)
            );

            CREATE INDEX IF NOT EXISTS idx_silence_interval_chat
                ON silence_interval_notices(chat_id, activity_anchor);


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
                file_contribution_score INTEGER NOT NULL DEFAULT 0,
                PRIMARY KEY(chat_id, user_id)
            );


            CREATE TABLE IF NOT EXISTS current_group_members (
                chat_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL,
                username TEXT NOT NULL DEFAULT '',
                display_name TEXT NOT NULL DEFAULT '',
                is_bot INTEGER NOT NULL DEFAULT 0,
                is_admin INTEGER NOT NULL DEFAULT 0,
                checked_at TEXT NOT NULL,
                PRIMARY KEY(chat_id, user_id)
            );

            CREATE INDEX IF NOT EXISTS idx_current_group_members_chat
                ON current_group_members(chat_id);


            CREATE TABLE IF NOT EXISTS retired_group_users (
                chat_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL,
                retired_at TEXT NOT NULL,
                reason TEXT NOT NULL DEFAULT '',
                PRIMARY KEY(chat_id, user_id)
            );

            CREATE INDEX IF NOT EXISTS idx_retired_group_users_chat
                ON retired_group_users(chat_id);


            CREATE TABLE IF NOT EXISTS reputation_notices (
                chat_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL,
                milestone INTEGER NOT NULL,
                sent_at TEXT NOT NULL,
                PRIMARY KEY(chat_id, user_id, milestone)
            );

            CREATE TABLE IF NOT EXISTS file_contribution_notices (
                chat_id INTEGER NOT NULL,
                message_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL,
                sent_at TEXT NOT NULL,
                PRIMARY KEY(chat_id, message_id)
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

            -- Catálogo técnico paralelo. No participa en la decisión de duplicados:
            -- file_fingerprints + SHA-256 siguen siendo la autoridad del sistema.
            CREATE TABLE IF NOT EXISTS technical_file_catalog (
                chat_id INTEGER NOT NULL,
                sha256 TEXT NOT NULL,
                message_id INTEGER NOT NULL,
                file_unique_id TEXT,
                file_name TEXT NOT NULL,
                file_size INTEGER NOT NULL DEFAULT 0,
                sender_id INTEGER,
                sender_name TEXT,
                first_seen TEXT,
                brands TEXT NOT NULL DEFAULT '',
                resources TEXT NOT NULL DEFAULT '',
                technologies TEXT NOT NULL DEFAULT '',
                software TEXT NOT NULL DEFAULT '',
                versions TEXT NOT NULL DEFAULT '',
                models TEXT NOT NULL DEFAULT '',
                equipment_classes TEXT NOT NULL DEFAULT '',
                search_text TEXT NOT NULL DEFAULT '',
                parser_version TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                PRIMARY KEY(chat_id, sha256)
            );

            CREATE TABLE IF NOT EXISTS radio_software_map (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                brand TEXT NOT NULL DEFAULT '',
                model TEXT NOT NULL,
                variant TEXT NOT NULL DEFAULT '',
                software TEXT NOT NULL,
                aliases TEXT NOT NULL DEFAULT '',
                notes TEXT NOT NULL DEFAULT '',
                source TEXT NOT NULL DEFAULT 'ADMIN',
                confidence REAL NOT NULL DEFAULT 1.0,
                created_at TEXT NOT NULL,
                UNIQUE(model, variant, software)
            );

            CREATE INDEX IF NOT EXISTS idx_radio_software_model
                ON radio_software_map(model, variant);

            CREATE INDEX IF NOT EXISTS idx_radio_software_software
                ON radio_software_map(software);

            CREATE TABLE IF NOT EXISTS technical_file_terms (
                chat_id INTEGER NOT NULL,
                sha256 TEXT NOT NULL,
                term_type TEXT NOT NULL,
                term_value TEXT NOT NULL,
                normalized_value TEXT NOT NULL,
                PRIMARY KEY(chat_id, sha256, term_type, normalized_value)
            );

            CREATE INDEX IF NOT EXISTS idx_technical_catalog_message
                ON technical_file_catalog(chat_id, message_id);
            CREATE INDEX IF NOT EXISTS idx_technical_terms_lookup
                ON technical_file_terms(chat_id, term_type, normalized_value);
            CREATE INDEX IF NOT EXISTS idx_technical_terms_any
                ON technical_file_terms(chat_id, normalized_value);
            

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

            -- Memoria técnica autónoma.
            -- Es una capa derivada de conversaciones Q/A y NO modifica
            -- file_fingerprints, SHA-256 ni la decisión de duplicados.
            CREATE TABLE IF NOT EXISTS autonomous_technical_qa (
                chat_id INTEGER NOT NULL,
                question_message_id INTEGER NOT NULL,
                answer_message_id INTEGER NOT NULL,
                confirmation_message_id INTEGER NOT NULL DEFAULT 0,
                question_text TEXT NOT NULL,
                answer_text TEXT NOT NULL,
                question_link TEXT NOT NULL DEFAULT '',
                answer_link TEXT NOT NULL DEFAULT '',
                model_anchors TEXT NOT NULL DEFAULT '',
                keywords TEXT NOT NULL DEFAULT '',
                status TEXT NOT NULL,
                confidence REAL NOT NULL DEFAULT 0,
                source TEXT NOT NULL DEFAULT 'GROUP_MEMORY',
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                PRIMARY KEY(chat_id, question_message_id, answer_message_id)
            );

            CREATE INDEX IF NOT EXISTS idx_autonomous_qa_status
                ON autonomous_technical_qa(chat_id, status, confidence DESC);

            CREATE TABLE IF NOT EXISTS autonomous_technical_facts (
                chat_id INTEGER NOT NULL,
                fact_type TEXT NOT NULL,
                subject TEXT NOT NULL,
                qualifier TEXT NOT NULL DEFAULT '',
                fact_value TEXT NOT NULL,
                question_message_id INTEGER NOT NULL,
                answer_message_id INTEGER NOT NULL,
                confirmation_message_id INTEGER NOT NULL DEFAULT 0,
                status TEXT NOT NULL,
                confidence REAL NOT NULL DEFAULT 0,
                source TEXT NOT NULL DEFAULT 'GROUP_MEMORY',
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                PRIMARY KEY(
                    chat_id, fact_type, subject, qualifier, fact_value,
                    question_message_id, answer_message_id
                )
            );

            CREATE INDEX IF NOT EXISTS idx_autonomous_fact_subject
                ON autonomous_technical_facts(
                    chat_id, fact_type, subject, qualifier, status
                );
            """
        )

        # Migración aditiva del catálogo técnico. La tabla puede existir desde
        # 2.8.14/2.8.15 sin equipment_classes. Solo afecta esta capa derivada;
        # no modifica file_fingerprints ni la lógica SHA-256.
        technical_columns = {
            str(row[1])
            for row in self.conn.execute("PRAGMA table_info(technical_file_catalog)").fetchall()
        }
        if "equipment_classes" not in technical_columns:
            self.conn.execute(
                "ALTER TABLE technical_file_catalog "
                "ADD COLUMN equipment_classes TEXT NOT NULL DEFAULT ''"
            )

        radio_map_columns = {
            str(row[1])
            for row in self.conn.execute("PRAGMA table_info(radio_software_map)").fetchall()
        }
        if "notes" not in radio_map_columns:
            self.conn.execute(
                "ALTER TABLE radio_software_map "
                "ADD COLUMN notes TEXT NOT NULL DEFAULT ''"
            )

        profile_columns = {
            str(row[1])
            for row in self.conn.execute("PRAGMA table_info(user_profiles)").fetchall()
        }
        if "file_contribution_score" not in profile_columns:
            self.conn.execute(
                "ALTER TABLE user_profiles "
                "ADD COLUMN file_contribution_score INTEGER NOT NULL DEFAULT 0"
            )

        self.conn.commit()

    def _ensure_defaults(self) -> None:
        defaults = {
            "daily_enabled": "1",
            "daily_time": "09:00",
            "daily_message": "",
            "daily_fun_enabled": "1",
            "duplicates_enabled": "0",
            "last_daily_sent_date": "",
            "silence_enabled": "1",
            "silence_hours": "8",
            "autonomous_technical_memory_enabled": "1",
        }
        with self.lock:
            for key, value in defaults.items():
                self.conn.execute(
                    "INSERT OR IGNORE INTO settings(key, value) VALUES(?, ?)",
                    (key, value),
                )

            # Invariante desde 2.8.25:
            # el mensaje diario está SIEMPRE activo y SIEMPRE usa el
            # repertorio aleatorio de saludos. El antiguo texto fijo se
            # borra de settings para que no pueda volver a enviarse.
            for key, value in (
                ("daily_enabled", "1"),
                ("daily_fun_enabled", "1"),
                ("daily_message", ""),
            ):
                self.conn.execute(
                    """
                    INSERT INTO settings(key, value) VALUES(?, ?)
                    ON CONFLICT(key) DO UPDATE SET value = excluded.value
                    """,
                    (key, value),
                )

            # Asociación inicial confirmada por el administrador.
            # La estructura queda lista para cargar más modelos/software después.
            self.conn.execute(
                """
                INSERT OR IGNORE INTO radio_software_map(
                    brand, model, variant, software, aliases, notes,
                    source, confidence, created_at
                )
                VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    "KENWOOD",
                    "TK-1300N",
                    "K3",
                    "KPG-D6",
                    "TK1300N|TK-1300N|TK 1300N",
                    "",
                    "ADMIN_CONFIRMED",
                    1.0,
                    datetime.now(BOT_TZ).isoformat(timespec="seconds"),
                ),
            )

            # Base Kenwood cargada desde el CSV aportado por el administrador:
            # 43 softwares KPG / 161 asociaciones modelo-software.
            now_kenwood_map = datetime.now(BOT_TZ).isoformat(timespec="seconds")
            for software, models, notes in KENWOOD_KPG_COMPATIBILITY_DATA:
                for model in models:
                    aliases = "|".join(
                        dict.fromkeys(
                            (
                                model,
                                model.replace("-", ""),
                                model.replace("-", " "),
                            )
                        )
                    )
                    self.conn.execute(
                        """
                        INSERT OR IGNORE INTO radio_software_map(
                            brand, model, variant, software, aliases, notes,
                            source, confidence, created_at
                        )
                        VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?)
                        """,
                        (
                            "KENWOOD",
                            model,
                            "",
                            software,
                            aliases,
                            notes,
                            "USER_KENWOOD_KPG_CSV",
                            1.0,
                            now_kenwood_map,
                        ),
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

    def list_radio_software_map(self) -> list[sqlite3.Row]:
        with self.lock:
            return self.conn.execute(
                """
                SELECT id, brand, model, variant, software, aliases, notes,
                       source, confidence
                FROM radio_software_map
                ORDER BY brand, model, variant, software
                """
            ).fetchall()

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

    def admin_memory_stats(self, chat_id: int) -> dict[str, object]:
        """Resumen de memoria histórica para el panel de administración.

        SOLO LECTURA: no modifica ninguna tabla ni la lógica de duplicados.
        """
        with self.lock:
            messages = int(
                self.conn.execute(
                    "SELECT COUNT(*) AS n FROM conversation_messages WHERE chat_id = ?",
                    (chat_id,),
                ).fetchone()["n"]
            )
            classifications = int(
                self.conn.execute(
                    "SELECT COUNT(*) AS n FROM conversation_classifications WHERE chat_id = ?",
                    (chat_id,),
                ).fetchone()["n"]
            )
            pairs = int(
                self.conn.execute(
                    "SELECT COUNT(*) AS n FROM conversation_qa_pairs WHERE chat_id = ?",
                    (chat_id,),
                ).fetchone()["n"]
            )
            users = int(
                self.conn.execute(
                    """
                    SELECT COUNT(DISTINCT sender_id) AS n
                    FROM conversation_messages
                    WHERE chat_id = ? AND sender_id > 0
                    """,
                    (chat_id,),
                ).fetchone()["n"]
            )
            status_rows = self.conn.execute(
                """
                SELECT status, COUNT(*) AS n
                FROM conversation_qa_pairs
                WHERE chat_id = ?
                GROUP BY status
                """,
                (chat_id,),
            ).fetchall()
            fingerprints = int(
                self.conn.execute(
                    "SELECT COUNT(*) AS n FROM file_fingerprints WHERE chat_id = ?",
                    (chat_id,),
                ).fetchone()["n"]
            )

        statuses = {
            str(row["status"] or "").upper(): int(row["n"] or 0)
            for row in status_rows
        }

        return {
            "messages": messages,
            "classifications": classifications,
            "pairs": pairs,
            "users": users,
            "fingerprints": fingerprints,
            "statuses": statuses,
        }

    def known_group_title(self, chat_id: int) -> str:
        """Nombre conocido del grupo para reportes privados. SOLO LECTURA."""
        with self.lock:
            row = self.conn.execute(
                "SELECT title FROM known_groups WHERE chat_id = ? LIMIT 1",
                (chat_id,),
            ).fetchone()

        if row and str(row["title"] or "").strip():
            return str(row["title"]).strip()

        if chat_id == HISTORY_SOURCE_CHAT_ID:
            return "YO REPARO RADIOS"

        return str(chat_id)

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

    def update_joke(
        self,
        joke_id: int,
        username: str,
        probability: int,
        response: str,
    ) -> bool:
        username = username.lstrip("@").strip().casefold()
        response = response.strip()
        probability = max(1, min(100, int(probability)))
        if not username or not response:
            return False
        with self.lock:
            cur = self.conn.execute(
                """
                UPDATE user_jokes
                SET username = ?, probability = ?, response = ?
                WHERE id = ?
                """,
                (username, probability, response, int(joke_id)),
            )
            self.conn.commit()
        return cur.rowcount > 0

    def list_custom_qa(self) -> list[sqlite3.Row]:
        with self.lock:
            return self.conn.execute(
                """
                SELECT id, question, normalized_question, match_type, response,
                       created_by, created_at, updated_at
                FROM custom_qa
                ORDER BY id
                """
            ).fetchall()

    def add_custom_qa(
        self,
        question: str,
        normalized_question: str,
        match_type: str,
        response: str,
        created_by: int,
    ) -> int | None:
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        try:
            with self.lock:
                cur = self.conn.execute(
                    """
                    INSERT INTO custom_qa(
                        question, normalized_question, match_type, response,
                        created_by, created_at, updated_at
                    )
                    VALUES(?, ?, ?, ?, ?, ?, ?)
                    """,
                    (
                        question.strip(),
                        normalized_question.strip(),
                        match_type,
                        response.strip(),
                        int(created_by),
                        now,
                        now,
                    ),
                )
                self.conn.commit()
                return int(cur.lastrowid)
        except sqlite3.IntegrityError:
            return None

    def update_custom_qa(
        self,
        qa_id: int,
        question: str,
        normalized_question: str,
        match_type: str,
        response: str,
    ) -> bool:
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        try:
            with self.lock:
                cur = self.conn.execute(
                    """
                    UPDATE custom_qa
                    SET question = ?, normalized_question = ?, match_type = ?,
                        response = ?, updated_at = ?
                    WHERE id = ?
                    """,
                    (
                        question.strip(),
                        normalized_question.strip(),
                        match_type,
                        response.strip(),
                        now,
                        int(qa_id),
                    ),
                )
                self.conn.commit()
            return cur.rowcount > 0
        except sqlite3.IntegrityError:
            return False

    def remove_custom_qa(self, ids: list[int]) -> int:
        if not ids:
            return 0
        placeholders = ",".join("?" for _ in ids)
        with self.lock:
            cur = self.conn.execute(
                f"DELETE FROM custom_qa WHERE id IN ({placeholders})",
                tuple(int(x) for x in ids),
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
            "file_contribution_score",
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

    def count_conversation_messages_for_user(
        self,
        chat_id: int,
        user_id: int,
    ) -> int:
        with self.lock:
            row = self.conn.execute(
                """
                SELECT COUNT(*) AS n
                FROM conversation_messages
                WHERE chat_id = ? AND sender_id = ?
                """,
                (chat_id, user_id),
            ).fetchone()
        return int(row["n"] or 0) if row else 0

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

    def get_recent_activity_profiles(
        self,
        chat_id: int,
        cutoff_iso: str,
    ) -> list[sqlite3.Row]:
        """Usuarios que Pecos observó escribiendo desde cutoff_iso."""
        with self.lock:
            return self.conn.execute(
                """
                SELECT user_id, username, display_name, first_seen, last_seen
                FROM user_profiles
                WHERE chat_id = ?
                  AND user_id > 0
                  AND last_seen >= ?
                ORDER BY last_seen DESC
                """,
                (chat_id, cutoff_iso),
            ).fetchall()

    def replace_current_member_snapshot(
        self,
        chat_id: int,
        members: list[dict[str, object]],
    ) -> None:
        """Reemplaza el padrón actual observado por MTProto.

        Esta tabla es de membresía, no de actividad. Por diseño NO modifica
        user_profiles.last_seen.
        """
        checked_at = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        rows = [
            (
                int(chat_id),
                int(member.get("user_id") or 0),
                str(member.get("username") or "")[:80],
                str(member.get("display_name") or "")[:150],
                1 if bool(member.get("is_bot")) else 0,
                1 if bool(member.get("is_admin")) else 0,
                checked_at,
            )
            for member in members
            if int(member.get("user_id") or 0) > 0
        ]
        with self.lock:
            self.conn.execute(
                "DELETE FROM current_group_members WHERE chat_id = ?",
                (int(chat_id),),
            )
            if rows:
                self.conn.executemany(
                    """
                    INSERT INTO current_group_members(
                        chat_id, user_id, username, display_name,
                        is_bot, is_admin, checked_at
                    )
                    VALUES(?, ?, ?, ?, ?, ?, ?)
                    """,
                    rows,
                )
            self.conn.commit()

    def get_current_member_snapshot(self, chat_id: int) -> list[sqlite3.Row]:
        with self.lock:
            return self.conn.execute(
                """
                SELECT
                    user_id, username, display_name,
                    is_bot, is_admin, checked_at
                FROM current_group_members
                WHERE chat_id = ? AND user_id > 0
                ORDER BY user_id
                """,
                (int(chat_id),),
            ).fetchall()

    def get_retired_user_ids(self, chat_id: int) -> set[int]:
        with self.lock:
            rows = self.conn.execute(
                """
                SELECT user_id
                FROM retired_group_users
                WHERE chat_id = ? AND user_id > 0
                """,
                (int(chat_id),),
            ).fetchall()
        return {int(row["user_id"]) for row in rows if int(row["user_id"] or 0) > 0}

    def restore_rejoined_users(
        self,
        chat_id: int,
        current_user_ids: set[int],
    ) -> int:
        """Si un usuario depurado vuelve a ingresar, deja de estar retirado."""
        ids = sorted({int(uid) for uid in current_user_ids if int(uid) > 0})
        if not ids:
            return 0
        placeholders = ",".join("?" for _ in ids)
        with self.lock:
            cur = self.conn.execute(
                f"""
                DELETE FROM retired_group_users
                WHERE chat_id = ?
                  AND user_id IN ({placeholders})
                """,
                (int(chat_id), *ids),
            )
            self.conn.commit()
        return int(cur.rowcount or 0)

    def retire_user_profiles(
        self,
        chat_id: int,
        user_ids: set[int],
        *,
        reason: str,
    ) -> int:
        """Quita usuarios del padrón estadístico, SIN borrar mensajes históricos.

        Se borra su fila de user_profiles/current_group_members y se deja un
        marcador mínimo por User ID en retired_group_users para que sus mensajes
        antiguos no los vuelvan a crear como usuarios estadísticos.
        """
        ids = sorted({int(uid) for uid in user_ids if int(uid) > 0})
        if not ids:
            return 0

        retired_at = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        rows = [
            (int(chat_id), uid, retired_at, str(reason or "")[:120])
            for uid in ids
        ]
        placeholders = ",".join("?" for _ in ids)

        with self.lock:
            self.conn.executemany(
                """
                INSERT INTO retired_group_users(chat_id, user_id, retired_at, reason)
                VALUES(?, ?, ?, ?)
                ON CONFLICT(chat_id, user_id) DO UPDATE SET
                    retired_at = excluded.retired_at,
                    reason = excluded.reason
                """,
                rows,
            )
            self.conn.execute(
                f"""
                DELETE FROM user_profiles
                WHERE chat_id = ?
                  AND user_id IN ({placeholders})
                """,
                (int(chat_id), *ids),
            )
            self.conn.execute(
                f"""
                DELETE FROM current_group_members
                WHERE chat_id = ?
                  AND user_id IN ({placeholders})
                """,
                (int(chat_id), *ids),
            )
            self.conn.commit()

        return len(ids)

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

    def claim_file_contribution_notice(
        self,
        chat_id: int,
        message_id: int,
        user_id: int,
    ) -> bool:
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        with self.lock:
            before = self.conn.total_changes
            self.conn.execute(
                """
                INSERT OR IGNORE INTO file_contribution_notices(
                    chat_id, message_id, user_id, sent_at
                )
                VALUES(?, ?, ?, ?)
                """,
                (chat_id, message_id, user_id, now),
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

    def upsert_autonomous_qa(
        self,
        chat_id: int,
        question_message_id: int,
        answer_message_id: int,
        confirmation_message_id: int,
        question_text: str,
        answer_text: str,
        question_link: str,
        answer_link: str,
        model_anchors: list[str],
        keywords: list[str],
        status: str,
        confidence: float,
        source: str,
    ) -> None:
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        with self.lock:
            self.conn.execute(
                """
                INSERT INTO autonomous_technical_qa(
                    chat_id, question_message_id, answer_message_id,
                    confirmation_message_id, question_text, answer_text,
                    question_link, answer_link, model_anchors, keywords,
                    status, confidence, source, created_at, updated_at
                )
                VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(chat_id, question_message_id, answer_message_id)
                DO UPDATE SET
                    confirmation_message_id=excluded.confirmation_message_id,
                    question_text=excluded.question_text,
                    answer_text=excluded.answer_text,
                    question_link=excluded.question_link,
                    answer_link=excluded.answer_link,
                    model_anchors=excluded.model_anchors,
                    keywords=excluded.keywords,
                    status=excluded.status,
                    confidence=excluded.confidence,
                    source=excluded.source,
                    updated_at=excluded.updated_at
                """,
                (
                    chat_id, question_message_id, answer_message_id,
                    confirmation_message_id,
                    question_text[:2000], answer_text[:3000],
                    question_link[:600], answer_link[:600],
                    "|".join(model_anchors[:8]),
                    "|".join(keywords[:20]),
                    status[:40],
                    float(confidence),
                    source[:80],
                    now, now,
                ),
            )
            self.conn.commit()

    def upsert_autonomous_fact_evidence(
        self,
        chat_id: int,
        fact_type: str,
        subject: str,
        qualifier: str,
        fact_value: str,
        question_message_id: int,
        answer_message_id: int,
        confirmation_message_id: int,
        status: str,
        confidence: float,
        source: str,
    ) -> None:
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        with self.lock:
            self.conn.execute(
                """
                INSERT INTO autonomous_technical_facts(
                    chat_id, fact_type, subject, qualifier, fact_value,
                    question_message_id, answer_message_id,
                    confirmation_message_id, status, confidence,
                    source, created_at, updated_at
                )
                VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(
                    chat_id, fact_type, subject, qualifier, fact_value,
                    question_message_id, answer_message_id
                )
                DO UPDATE SET
                    confirmation_message_id=excluded.confirmation_message_id,
                    status=excluded.status,
                    confidence=excluded.confidence,
                    source=excluded.source,
                    updated_at=excluded.updated_at
                """,
                (
                    chat_id, fact_type[:60], subject[:120], qualifier[:80],
                    fact_value[:160], question_message_id, answer_message_id,
                    confirmation_message_id, status[:40], float(confidence),
                    source[:80], now, now,
                ),
            )
            self.conn.commit()

    def list_autonomous_qa(
        self,
        chat_id: int,
        statuses: tuple[str, ...] = ("CONFIRMED",),
        limit: int = 5000,
    ) -> list[sqlite3.Row]:
        if not statuses:
            return []
        placeholders = ",".join("?" for _ in statuses)
        with self.lock:
            return self.conn.execute(
                f"""
                SELECT *
                FROM autonomous_technical_qa
                WHERE chat_id = ?
                  AND status IN ({placeholders})
                ORDER BY confidence DESC, updated_at DESC
                LIMIT ?
                """,
                (chat_id, *statuses, max(1, min(10000, int(limit)))),
            ).fetchall()

    def grouped_autonomous_facts(
        self,
        chat_id: int,
        fact_type: str,
        subject: str,
        qualifier: str = "",
    ) -> list[sqlite3.Row]:
        with self.lock:
            return self.conn.execute(
                """
                SELECT
                    fact_value,
                    SUM(CASE WHEN status='CONFIRMED' THEN 1 ELSE 0 END)
                        AS confirmed_count,
                    SUM(CASE WHEN status='ACKNOWLEDGED' THEN 1 ELSE 0 END)
                        AS acknowledged_count,
                    COUNT(*) AS evidence_count,
                    MAX(confidence) AS max_confidence,
                    MAX(question_message_id) AS question_message_id,
                    MAX(answer_message_id) AS answer_message_id,
                    MAX(confirmation_message_id) AS confirmation_message_id
                FROM autonomous_technical_facts
                WHERE chat_id = ?
                  AND fact_type = ?
                  AND subject = ?
                  AND (
                        qualifier = ?
                        OR qualifier = ''
                      )
                GROUP BY fact_value
                ORDER BY confirmed_count DESC,
                         acknowledged_count DESC,
                         evidence_count DESC,
                         max_confidence DESC
                """,
                (chat_id, fact_type, subject, qualifier),
            ).fetchall()

    def confirmed_or_ack_pairs_for_autonomous_sync(
        self,
        chat_id: int,
    ) -> list[sqlite3.Row]:
        with self.lock:
            return self.conn.execute(
                """
                SELECT
                    q.question_message_id,
                    q.answer_message_id,
                    q.confirmation_message_id,
                    q.confidence,
                    q.status,
                    qm.text AS question_text,
                    qm.message_link AS question_link,
                    qm.sender_id AS question_sender_id,
                    am.text AS answer_text,
                    am.message_link AS answer_link,
                    am.sender_id AS answer_sender_id
                FROM conversation_qa_pairs q
                JOIN conversation_messages qm
                  ON qm.chat_id=q.chat_id
                 AND qm.message_id=q.question_message_id
                JOIN conversation_messages am
                  ON am.chat_id=q.chat_id
                 AND am.message_id=q.answer_message_id
                WHERE q.chat_id = ?
                  AND q.status IN ('CONFIRMED', 'ACKNOWLEDGED')
                ORDER BY q.question_message_id, q.answer_message_id
                """,
                (chat_id,),
            ).fetchall()

    def autonomous_memory_stats(self, chat_id: int) -> dict[str, int]:
        with self.lock:
            qa_confirmed = int(self.conn.execute(
                """
                SELECT COUNT(*) AS n
                FROM autonomous_technical_qa
                WHERE chat_id=? AND status='CONFIRMED'
                """,
                (chat_id,),
            ).fetchone()["n"])

            qa_ack = int(self.conn.execute(
                """
                SELECT COUNT(*) AS n
                FROM autonomous_technical_qa
                WHERE chat_id=? AND status='ACKNOWLEDGED'
                """,
                (chat_id,),
            ).fetchone()["n"])

            fact_evidence = int(self.conn.execute(
                """
                SELECT COUNT(*) AS n
                FROM autonomous_technical_facts
                WHERE chat_id=?
                """,
                (chat_id,),
            ).fetchone()["n"])

            trusted_facts = int(self.conn.execute(
                """
                SELECT COUNT(*) AS n
                FROM (
                    SELECT fact_type, subject, qualifier, fact_value
                    FROM autonomous_technical_facts
                    WHERE chat_id=?
                    GROUP BY fact_type, subject, qualifier, fact_value
                    HAVING
                        SUM(CASE WHEN status='CONFIRMED' THEN 1 ELSE 0 END) >= 1
                        OR
                        SUM(CASE WHEN status='ACKNOWLEDGED' THEN 1 ELSE 0 END) >= 2
                )
                """,
                (chat_id,),
            ).fetchone()["n"])

        return {
            "qa_confirmed": qa_confirmed,
            "qa_acknowledged": qa_ack,
            "fact_evidence": fact_evidence,
            "trusted_facts": trusted_facts,
        }

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

    def claim_silence_interval(
        self,
        chat_id: int,
        activity_anchor: str,
        interval_hours: int,
        slot: int,
    ) -> bool:
        now = datetime.now(BOT_TZ).isoformat(timespec="seconds")
        with self.lock:
            self.conn.execute(
                """
                DELETE FROM silence_interval_notices
                WHERE chat_id = ?
                  AND (activity_anchor <> ? OR interval_hours <> ?)
                """,
                (chat_id, activity_anchor, interval_hours),
            )

            before = self.conn.total_changes
            self.conn.execute(
                """
                INSERT OR IGNORE INTO silence_interval_notices(
                    chat_id, activity_anchor, interval_hours, slot, sent_at
                )
                VALUES(?, ?, ?, ?, ?)
                """,
                (chat_id, activity_anchor, interval_hours, slot, now),
            )
            inserted = self.conn.total_changes > before

            if inserted:
                self.conn.execute(
                    """
                    DELETE FROM silence_interval_notices
                    WHERE chat_id = ?
                      AND activity_anchor = ?
                      AND interval_hours = ?
                      AND slot < ?
                    """,
                    (chat_id, activity_anchor, interval_hours, max(1, slot - 2)),
                )

            self.conn.commit()
        return inserted

    def release_silence_interval(
        self,
        chat_id: int,
        activity_anchor: str,
        interval_hours: int,
        slot: int,
    ) -> None:
        with self.lock:
            self.conn.execute(
                """
                DELETE FROM silence_interval_notices
                WHERE chat_id = ?
                  AND activity_anchor = ?
                  AND interval_hours = ?
                  AND slot = ?
                """,
                (chat_id, activity_anchor, interval_hours, slot),
            )
            self.conn.commit()

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


# Repertorios de humor visibles y editables desde /config.
# Melerix y el saludo especial de leosedf quedan deliberadamente fuera
# del panel; sus comportamientos existentes no se eliminan.
HUMOR_POOL_DEFINITIONS: dict[str, tuple[str, list[str], str]] = {
    "xerax_manual": (
        "🤖 XeraX — bromas por mención",
        XERAX_FUN_MESSAGES,
        "Se usan cuando otro usuario nombra explícitamente a XeraX.",
    ),
    "xerax_auto": (
        "⏱️ XeraX — bromas automáticas",
        XERAX_AUTO_MESSAGES,
        "Máximo una por mañana, una por tarde y una por noche cuando XeraX interviene.",
    ),
    "advice": (
        "🤠 Consejos de Pecos",
        ADVICE_MESSAGES,
        "Repertorio usado por /consejo.",
    ),
    "phrase": (
        "💬 Frases de Pecos",
        PHRASE_MESSAGES,
        "Repertorio usado por /frase.",
    ),
    "excuse": (
        "🌵 Excusas de Pecos",
        EXCUSE_MESSAGES,
        "Repertorio usado por /excusa.",
    ),
    "forecast": (
        "🔮 Pronósticos de Pecos",
        FORECAST_MESSAGES,
        "Repertorio usado por /pronostico.",
    ),
    "duel": (
        "⚔️ Duelo de Pecos",
        PECOS_DUEL_MESSAGES,
        "Respuestas humorísticas cuando una ofensa está dirigida claramente a Pecos. Admite {usuario}.",
    ),
    "band": (
        "📻 Bromas VHF ↔ UHF",
        BAND_CONVERSION_PANEL_MESSAGES,
        "Admite {origen} y {destino}; Pecos los reemplaza por VHF/UHF según la consulta.",
    ),
    "daily": (
        "🕘 Saludos diarios en broma",
        DAILY_FUN_GREETINGS,
        "Se usan siempre a la hora configurada. Pecos elige uno al azar cada día.",
    ),
    "silence": (
        "🌵 Bromas por silencio",
        SILENCE_MESSAGES,
        "Se usan cuando el detector de silencio interviene. Admite {horas}.",
    ),
    "unknown": (
        "🤷 Pecos no sabe / fuera de alcance",
        PECOS_UNKNOWN_MESSAGES,
        "Se usan cuando Pecos fue llamado directamente pero no tiene una respuesta segura.",
    ),
    "correction": (
        "🛠️ Pecos acepta correcciones",
        PECOS_CORRECTION_MESSAGES,
        "Se usan cuando un usuario comenta que Pecos se equivocó, está perdido o respondió mal.",
    ),
}


def humor_pool_setting_key(pool_key: str) -> str:
    return f"humor_pool:{pool_key}"


def humor_pool_exists(pool_key: str) -> bool:
    return pool_key in HUMOR_POOL_DEFINITIONS


def humor_pool_title(pool_key: str) -> str:
    definition = HUMOR_POOL_DEFINITIONS.get(pool_key)
    return definition[0] if definition else "🎭 Repertorio"


def humor_pool_note(pool_key: str) -> str:
    definition = HUMOR_POOL_DEFINITIONS.get(pool_key)
    return definition[2] if definition else ""


def get_humor_pool(pool_key: str) -> list[str]:
    definition = HUMOR_POOL_DEFINITIONS.get(pool_key)
    if not definition:
        return []

    defaults = definition[1]
    raw = db.get_setting(humor_pool_setting_key(pool_key), "").strip()
    if raw:
        try:
            parsed = json.loads(raw)
            if isinstance(parsed, list):
                cleaned = [
                    str(item).strip()
                    for item in parsed
                    if str(item).strip()
                ]
                if cleaned:
                    return cleaned
        except (json.JSONDecodeError, TypeError, ValueError):
            logging.warning("Repertorio de humor inválido en settings: %s", pool_key)

    return list(defaults)


def save_humor_pool(pool_key: str, items: list[str]) -> None:
    if not humor_pool_exists(pool_key):
        raise ValueError("Repertorio de humor desconocido")

    cleaned = [str(item).strip() for item in items if str(item).strip()]
    if not cleaned:
        raise ValueError("El repertorio no puede quedar vacío")
    if len(cleaned) > 150:
        raise ValueError("El repertorio no puede superar 150 mensajes")
    if any(len(item) > 3500 for item in cleaned):
        raise ValueError("Una de las bromas supera 3500 caracteres")

    db.set_setting(
        humor_pool_setting_key(pool_key),
        json.dumps(cleaned, ensure_ascii=False),
    )


def reset_humor_pool(pool_key: str) -> None:
    if not humor_pool_exists(pool_key):
        return
    # Cadena vacía = volver a usar los valores definidos en main.py.
    db.set_setting(humor_pool_setting_key(pool_key), "")


def format_humor_pool_list(pool_key: str) -> str:
    pool = get_humor_pool(pool_key)
    title = humor_pool_title(pool_key)
    note = humor_pool_note(pool_key)
    lines = [f"{title}\n", f"Mensajes: {len(pool)}"]
    if note:
        lines.append(note)
    lines.append("")
    for index, item in enumerate(pool, start=1):
        lines.append(f"{index}. {item}")
    return "\n\n".join(lines)


def render_humor_preview(pool_key: str, usuario: str) -> str:
    pool = get_humor_pool(pool_key)
    if not pool:
        return "No hay mensajes disponibles en este repertorio."

    text_value = choose_random(
        f"panel_humor_{pool_key}",
        pool,
        usuario,
    )
    if pool_key == "silence":
        text_value = text_value.replace("{horas}", "8")
    elif pool_key == "band":
        text_value = (
            text_value
            .replace("{origen}", "VHF")
            .replace("{destino}", "UHF")
        )
    return text_value


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


async def remember_user_reaction_activity(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
) -> None:
    """Actualiza last_seen cuando un usuario cambia una reacción en el grupo.

    Telegram entrega las reacciones como un tipo de Update separado del
    Message normal. Por eso no pasan por remember_user_presence(message).

    - Cuenta reacciones identificables de usuarios humanos.
    - También cuenta cambiar o retirar una reacción: sigue siendo actividad.
    - Ignora reacciones anónimas/realizadas en nombre de un chat, porque no se
      pueden atribuir de forma fiable a un User ID concreto.
    - No responde nada en el grupo; solo actualiza user_profiles.last_seen.
    """
    reaction = update.message_reaction
    if reaction is None:
        return

    chat = reaction.chat
    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        return
    if chat.id not in ALLOWED_GROUP_IDS:
        return

    user = reaction.user
    if user is None or user.is_bot:
        return

    username, shown = user_identity_tuple(user)
    db.touch_user_profile(
        chat.id,
        user.id,
        username,
        shown,
    )


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


def normalize_custom_qa_text(text_value: str) -> str:
    """Normaliza preguntas configurables e ignora la llamada a Pecos.

    Hace equivalentes, por ejemplo:
    - Pecos como van las empanadas?
    - Pecos, ¿cómo van las empanadas?
    - como van las empanadas
    """
    normalized = normalize_intent(text_value or "").lower()

    # Quitar @username conocido del bot antes de limpiar signos.
    for alias in sorted(PECOS_USERNAME_ALIASES, key=len, reverse=True):
        alias_norm = normalize_intent(alias).lower().lstrip("@")
        if alias_norm:
            normalized = re.sub(
                rf"(?<![a-z0-9_])@?{re.escape(alias_norm)}(?![a-z0-9_])",
                " ",
                normalized,
            )

    # Pecos/Peco pueden aparecer al inicio o al final; se eliminan como vocativo.
    normalized = re.sub(r"(?<![a-z0-9_])(?:pecos|peco)(?![a-z0-9_])", " ", normalized)
    normalized = re.sub(r"[^a-z0-9]+", " ", normalized)
    return re.sub(r"\s+", " ", normalized).strip()


def parse_custom_qa_match_type(value: str) -> str | None:
    token = normalize_intent(value or "").strip().upper()
    if token in {"EXACT", "EXACTA", "EXACTO"}:
        return "EXACT"
    if token in {"CONTAINS", "CONTIENE", "CONTENGA"}:
        return "CONTAINS"
    return None


def custom_qa_match_label(value: str) -> str:
    return "EXACTA" if value == "EXACT" else "CONTIENE"


def format_custom_qa_list() -> str:
    rows = db.list_custom_qa()
    if not rows:
        return (
            "💬 Preguntas y respuestas\n\n"
            "No hay respuestas personalizadas configuradas todavía."
        )

    lines = [f"💬 Preguntas y respuestas\n\nConfiguradas: {len(rows)}"]
    for row in rows:
        lines.append(
            f"ID {row['id']} — [{custom_qa_match_label(str(row['match_type']))}]\n"
            f"Pregunta: {row['question']}\n"
            f"Respuesta: {row['response']}"
        )
    return "\n\n".join(lines)


def find_custom_qa_response(text_value: str) -> sqlite3.Row | None:
    candidate = normalize_custom_qa_text(text_value)
    if not candidate:
        return None

    rows = db.list_custom_qa()

    # EXACTA siempre tiene prioridad sobre CONTIENE.
    for row in rows:
        if str(row["match_type"]) != "EXACT":
            continue
        if candidate == str(row["normalized_question"]):
            return row

    # En CONTIENE gana la frase más específica (la más larga).
    contains_rows = sorted(
        (row for row in rows if str(row["match_type"]) == "CONTAINS"),
        key=lambda row: len(str(row["normalized_question"])),
        reverse=True,
    )
    for row in contains_rows:
        needle = str(row["normalized_question"]).strip()
        if needle and needle in candidate:
            return row

    return None


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
    retired_ids = db.get_retired_user_ids(chat_id)

    for row in db.get_activity_message_stats(chat_id):
        user_id = int(row["user_id"] or 0)
        if user_id <= 0 or user_id in retired_ids:
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
        if user_id <= 0 or user_id in retired_ids:
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


def member_activity_status(last_seen: datetime | None) -> tuple[str, str]:
    if last_seen is None:
        return "⚪", "SIN REGISTRO"
    return activity_status(last_seen)


def build_current_member_activity_snapshot(
    chat_id: int,
    current_members: list[dict[str, object]] | None = None,
) -> list[dict[str, object]]:
    """Cruza miembros actuales con actividad histórica sin inventar fechas."""
    activity_by_id = {
        int(entry.get("user_id") or 0): entry
        for entry in build_member_activity_snapshot(chat_id)
        if int(entry.get("user_id") or 0) > 0
    }

    if current_members is None:
        current_members = [
            {
                "user_id": int(row["user_id"] or 0),
                "username": str(row["username"] or "").lstrip("@"),
                "display_name": str(row["display_name"] or "").strip(),
                "is_bot": bool(row["is_bot"]),
                "is_admin": bool(row["is_admin"]),
            }
            for row in db.get_current_member_snapshot(chat_id)
        ]

    merged: list[dict[str, object]] = []
    for member in current_members:
        user_id = int(member.get("user_id") or 0)
        if user_id <= 0:
            continue

        activity = activity_by_id.get(user_id)
        if activity is None:
            merged.append(
                {
                    "user_id": user_id,
                    "username": str(member.get("username") or "").lstrip("@"),
                    "display_name": str(member.get("display_name") or "").strip(),
                    "first_seen": None,
                    "last_seen": None,
                    "message_count": 0,
                    "messages_30d": 0,
                    "member_current": True,
                    "is_bot": bool(member.get("is_bot")),
                    "is_admin": bool(member.get("is_admin")),
                }
            )
            continue

        item = dict(activity)
        if member.get("username"):
            item["username"] = str(member.get("username") or "").lstrip("@")
        if member.get("display_name"):
            item["display_name"] = str(member.get("display_name") or "").strip()
        item["member_current"] = True
        item["is_bot"] = bool(member.get("is_bot"))
        item["is_admin"] = bool(member.get("is_admin"))
        merged.append(item)

    def sort_key(item: dict[str, object]):
        last_seen = item.get("last_seen")
        if isinstance(last_seen, datetime):
            return (1, last_seen)
        return (0, datetime.min.replace(tzinfo=BOT_TZ))

    merged.sort(key=sort_key, reverse=True)
    return merged


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
    is_current_roster = bool(entries) and all(bool(e.get("member_current")) for e in entries)

    lines = [
        "PECOS PAUL KELE - REPORTE DE ACTIVIDAD OBSERVADA",
        f"Grupo: {chat_title}", f"Generado: {now_text} ({TIMEZONE_NAME})", "",
        "IMPORTANTE:",
        "Este informe NO representa la última conexión a Telegram.",
        "Solo indica la última actividad que Pecos observó/registró en el grupo.",
    ]

    if is_current_roster:
        lines += [
            "El listado fue cruzado con el padrón actual obtenido por MTProto.",
            "SIN REGISTRO = miembro actual sin actividad atribuible observada por Pecos.",
        ]
    else:
        lines += [
            "Un usuario que solo lee y no escribe puede parecer inactivo.",
            "El listado histórico no confirma por sí solo que siga siendo miembro.",
        ]

    lines += [
        "",
        "Clasificación:",
        "ACTIVO = 0 a 30 días",
        "POCO ACTIVO = 31 a 90 días",
        "INACTIVO = 91 a 180 días",
        "MUY INACTIVO = más de 180 días",
        "SIN REGISTRO = miembro actual sin actividad observada",
        "",
    ]

    selected = entries
    if inactive_days is not None:
        selected = [
            e for e in entries
            if isinstance(e.get("last_seen"), datetime)
            and activity_age_days(e.get("last_seen")) >= inactive_days
        ]
        selected.sort(
            key=lambda e: activity_age_days(e.get("last_seen")),
            reverse=True,
        )
        lines += [
            f"Filtro: {inactive_days} días o más sin actividad observada.",
            "Los miembros SIN REGISTRO no se clasifican automáticamente como inactivos.",
            "",
        ]

    lines += [f"Usuarios incluidos: {len(selected)}", "=" * 78]

    for index, entry in enumerate(selected, 1):
        last_dt = entry.get("last_seen") if isinstance(entry.get("last_seen"), datetime) else None
        icon, state = member_activity_status(last_dt)

        if last_dt is None:
            last_text = "SIN REGISTRO"
        else:
            last_text = f"{format_activity_timestamp(last_dt)} ({human_activity_age(last_dt)})"

        lines += [
            f"{index}. {icon} {state} | {activity_person_label(entry)}",
            f"   User ID: {int(entry.get('user_id') or 0)}",
            f"   Última actividad observada: {last_text}",
            f"   Mensajes registrados en memoria: {int(entry.get('message_count') or 0)}",
            f"   Mensajes registrados últimos 30 días: {int(entry.get('messages_30d') or 0)}",
            "",
        ]

    return "\n".join(lines).rstrip() + "\n"


def telegram_member_status_label(status: str) -> str:
    labels = {"creator":"propietario", "owner":"propietario", "administrator":"administrador", "member":"miembro", "restricted":"restringido", "left":"salió del grupo", "kicked":"expulsado/bloqueado"}
    return labels.get((status or "").casefold(), status or "desconocido")


PECOS_USERNAME_ALIASES = {"pecos_paul_kele_bot"}

# AYUDA/CONSULTAS: cuando está activo, Pecos solo interviene si el mensaje
# comienza nombrándolo: "Pecos ...", "Peco ..." o "@Pecos_Paul_Kele_Bot ...".
# No afecta duplicados, moderación, aprendizaje histórico ni tareas admin.
PECOS_HELP_REQUIRE_NAME_FIRST = True


def text_starts_with_pecos(text_value: str) -> bool:
    """True si Pecos/Peco/@username es el primer vocativo del mensaje."""
    raw = (text_value or "").strip()
    if not raw:
        return False

    normalized = normalize_intent(raw).lower().strip()

    if re.match(r"^(?:pecos|peco)(?![a-z0-9_])", normalized):
        return True

    for alias in PECOS_USERNAME_ALIASES:
        alias_norm = normalize_intent(alias).lower().lstrip("@")
        if not alias_norm:
            continue
        if re.match(rf"^@?{re.escape(alias_norm)}(?![a-z0-9_])", normalized):
            return True

    return False


def pecos_help_invocation_allowed(text_value: str) -> bool:
    if PECOS_HELP_REQUIRE_NAME_FIRST:
        return text_starts_with_pecos(text_value)
    return text_mentions_pecos(text_value)


def pecos_conversational_question_allowed(text_value: str) -> bool:
    """Regla para respuestas conversacionales de Pecos.

    Requiere:
    1) que Pecos/Peco/@Pecos_Paul_Kele_Bot esté al principio;
    2) que el texto termine realmente en "?".

    Las búsquedas/órdenes técnicas reconocidas se procesan por sus handlers
    específicos antes de llegar a esta capa y no necesitan signo de pregunta.
    """
    raw = (text_value or "").strip()
    if not raw:
        return False

    if not pecos_help_invocation_allowed(raw):
        return False

    return raw.endswith("?")


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
    # Mostrar únicamente horas completas transcurridas.
    # Ej.: 8.1 h -> "8", 2.9 h -> "2".
    return str(max(0, int(hours)))


def build_silence_message(elapsed_hours: float) -> str:
    template = choose_random(
        "silence",
        get_humor_pool("silence"),
        "grupo",
    )

    # Gramática correcta:
    # 1 hora
    # 2 horas, 3 horas, etc.
    hours_value = max(0, int(elapsed_hours))
    hour_word = "hora" if hours_value == 1 else "horas"

    # Los repertorios históricos usan "{horas} horas".
    # Sustituimos primero la frase completa para no producir "1 horas".
    rendered = template.replace(
        "{horas} horas",
        f"{hours_value} {hour_word}",
    )
    rendered = rendered.replace("{horas}", str(hours_value))
    return rendered


def has_archive_extension(file_name: str) -> bool:
    lower = (file_name or "").casefold()
    return any(lower.endswith(ext) for ext in ARCHIVE_EXTENSIONS)


def looks_like_helpful_contribution(message: Message) -> bool:
    """Reconocimiento público: solo aportes reales de archivos.

    La conversación normal, responder mensajes o usar palabras técnicas ya NO
    incrementa el contador público de aportes. Además, este bloque se ejecuta
    después del detector de duplicados, por lo que un archivo repetido no llega
    a contabilizarse como aporte nuevo.
    """
    if not message.document:
        return False

    file_name = getattr(message.document, "file_name", "") or ""
    return bool(file_name and has_archive_extension(file_name))


def remember_helpful_contribution(message: Message) -> int | None:
    if looks_like_helpful_contribution(message):
        return increment_user_metric(message, "file_contribution_score")
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

    # Se ejecuta después del control de duplicados. Por tanto, si llegamos aquí
    # con un documento técnico, es un aporte nuevo para esta ejecución.
    if not looks_like_helpful_contribution(message):
        return False

    if not db.claim_file_contribution_notice(
        message.chat_id,
        message.message_id,
        user.id,
    ):
        return False

    usuario = display_name(message)
    template = random.choice(FILE_CONTRIBUTION_MESSAGES)
    await context.bot.send_message(
        chat_id=message.chat_id,
        text=template.replace("{usuario}", usuario),
    )
    db.add_history(
        f"APORTE NUEVO PECOS | {usuario} | mensaje {message.message_id} | chat {message.chat_id}"
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

    # La respuesta se conserva como aprendizaje conversacional, pero NO
    # cuenta como "aporte de archivo" ni dispara reconocimientos públicos.
    increment_user_metric(message, "helpful_score", 2)
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

    # Se conserva el aprendizaje pasivo, pero Pecos no interrumpe una
    # conversación humana si no fue llamado al comienzo del mensaje.
    if not pecos_help_invocation_allowed(current_text):
        return False

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


def archive_required_content_anchors(query: str) -> list[str]:
    """Obtiene anclas técnicas que deben cumplirse TODAS.

    No incluye palabras genéricas de recurso como CPS, software o firmware,
    porque un archivo puede estar nombrado como "programming software" y seguir
    siendo válido. Sí incluye marcas/tecnologías explícitas como KENWOOD, DMR,
    MOTOROLA, HYTERA, etc., e identificadores concretos como KPG-D6.

    Ejemplo:
        "kenwood dmr" -> ["kenwood", "dmr"]
        "cps kenwood dmr" -> ["kenwood", "dmr"]
        "software kpg-d6" -> ["kpg-d6"]
    """
    terms = extract_archive_terms(query)
    models = set(archive_model_terms(query))
    families = set(archive_family_terms(query))
    identifiers = set(archive_identifier_terms(query))

    anchors: list[str] = []
    seen: set[str] = set()

    for term in terms:
        if term in models or term in families:
            continue
        if term in ARCHIVE_GENERIC_RESOURCE_TERMS:
            continue
        if term in {"bot"}:
            continue

        is_strong_technical = term in TECHNICAL_ARCHIVE_WORDS
        is_identifier = term in identifiers

        if (is_strong_technical or is_identifier) and term not in seen:
            seen.add(term)
            anchors.append(term)

    return anchors[:6]


def archive_name_matches_anchor(file_name: str, anchor: str) -> bool:
    """Coincidencia conservadora de una ancla técnica con un nombre de archivo.

    Para identificadores alfanuméricos permite variantes de separación:
      KPG-D6 == KPGD6 == KPG D6

    También acepta sufijos alfabéticos del mismo identificador, por ejemplo
    KPG-D6N, pero NO cambia el número solicitado:
      KPG-D6 != KPG-D3
      KPG-D6 != KPG-67
      KPG-D6 != KPG-D60
    """
    name_norm = archive_normalized_name(file_name)
    anchor_norm = archive_normalized_name(anchor)

    if not name_norm or not anchor_norm:
        return False

    anchor_compact = re.sub(r"[^a-z0-9]", "", anchor_norm)

    # Identificador técnico con letras + números (ej.: kpgd6).
    if (
        len(anchor_compact) >= 4
        and any(ch.isalpha() for ch in anchor_compact)
        and any(ch.isdigit() for ch in anchor_compact)
    ):
        name_tokens = name_norm.split()

        # Probamos tokens individuales y pequeñas secuencias contiguas para
        # cubrir KPGD6, KPG-D6 y "KPG D6" sin recurrir a similitud difusa.
        for start in range(len(name_tokens)):
            combined = ""
            for end in range(start, min(len(name_tokens), start + 3)):
                combined += name_tokens[end]

                if not combined.startswith(anchor_compact):
                    # Puede que todavía falten caracteres del identificador.
                    if anchor_compact.startswith(combined):
                        continue
                    break

                suffix = combined[len(anchor_compact):]

                # Exacto: KPGD6
                if not suffix:
                    return True

                # Variante del mismo identificador con sufijo alfabético:
                # KPGD6N, KPGD6SEND, etc.
                # Si inmediatamente continúa otro dígito, es otro número:
                # KPGD60 no corresponde a KPGD6.
                if not suffix[0].isdigit():
                    return True

                return False

        return False

    # Palabras/frases sin identificador: coincidencia exacta por límites.
    return bool(
        re.search(
            rf"(?:^|\s){re.escape(anchor_norm)}(?:$|\s)",
            name_norm,
        )
    )


def search_archive_rows_legacy(chat_id: int, query: str, limit: int = ARCHIVE_SEARCH_MAX_RESULTS) -> list[sqlite3.Row]:
    terms = extract_archive_terms(query)
    if not terms:
        return []

    requested_models = archive_model_terms(query)
    requested_families = archive_family_terms(query)
    required_anchors = archive_required_content_anchors(query)
    ranked: list[tuple[float, sqlite3.Row]] = []

    for row in db.list_archive_fingerprints(chat_id):
        file_name = str(row["file_name"] or "")
        if not archive_file_allowed(file_name):
            continue

        # Un modelo concreto es un ancla dura.
        matched_models = [
            model for model in requested_models
            if archive_name_matches_model(file_name, model)
        ]
        if requested_models and not matched_models:
            continue

        # Una familia/plataforma concreta también es un ancla dura.
        matched_families = [
            family for family in requested_families
            if archive_name_matches_family(file_name, family)
        ]
        if requested_families and not matched_families:
            continue

        # NUEVO: cuando el usuario da varias anclas técnicas concretas,
        # TODAS deben estar presentes. Ej.: "KENWOOD DMR" no acepta un archivo
        # solo por contener "KENWOOD" o solo por contener "DMR".
        if required_anchors and not all(
            archive_name_matches_anchor(file_name, anchor)
            for anchor in required_anchors
        ):
            continue

        score = archive_search_score(file_name, terms)
        if score <= 0:
            continue

        score += 12.0 * len(matched_models)
        score += 9.0 * len(matched_families)
        score += 8.0 * len(required_anchors)
        ranked.append((score, row))

    ranked.sort(
        key=lambda pair: (pair[0], int(pair[1]["message_id"])),
        reverse=True,
    )
    return [row for _, row in ranked[:max(1, min(12, limit))]]


# ---------------------------------------------------------------------------
# Catálogo técnico estructurado (2.8.14)
# ---------------------------------------------------------------------------

def technical_ascii_upper(value: str) -> str:
    value = unicodedata.normalize("NFD", value or "")
    return "".join(
        ch for ch in value.upper()
        if unicodedata.category(ch) != "Mn"
    )


def technical_stem(file_name: str) -> str:
    return re.sub(
        r"\.(RAR|ZIP|7Z|EXE)$",
        "",
        technical_ascii_upper(file_name).strip(),
    )


def technical_normalized_parts(value: str) -> tuple[str, str, str]:
    raw = technical_stem(value)
    spaced = re.sub(r"[^A-Z0-9]+", " ", raw)
    spaced = re.sub(r"\s+", " ", spaced).strip()
    compact = re.sub(r"[^A-Z0-9]", "", raw)
    return raw, spaced, compact


def technical_term_normalized(value: str) -> str:
    return re.sub(r"[^A-Z0-9]", "", technical_ascii_upper(value))


def technical_catalog_detect_brands(file_name: str) -> list[str]:
    _raw, spaced, compact = technical_normalized_parts(file_name)
    found: list[str] = []

    if (
        re.search(r"\bMOTOROLA\b", spaced)
        or "MOTOTRBO" in compact
        or "MAGONE" in compact
        or compact.startswith("APX")
        or re.search(
            r"\b(?:XTS|XTL|XPR|DEP|DGP|DP|EM|EP|GM|GP|PRO)\s*\d+",
            spaced,
        )
        or re.search(r"\bXIR\s*[PM]\s*\d+", spaced)
    ):
        found.append("MOTOROLA")

    if (
        re.search(r"\bKENWOOD\b", spaced)
        or re.search(r"\b(?:KPG|NX|NXR|TKR|TK|TM)\s*[A-Z]?\d+", spaced)
        or re.match(r"^KPG[A-Z]*\d+", compact)
    ):
        found.append("KENWOOD")

    if (
        re.search(r"\bHYTERA\b", spaced)
        or re.search(r"\b(?:PD|HP|HM|HR|PNC|MD|RD|TC)\s*\d+", spaced)
    ):
        found.append("HYTERA")

    others = {
        "ICOM": r"\bICOM\b",
        "YAESU": r"\bYAESU\b",
        "BAOFENG": r"\bBAOFENG\b",
        "VERTEX": r"\bVERTEX\b",
        "RETEVIS": r"\bRETEVIS\b",
        "TYT": r"\bTYT\b",
        "SEPURA": r"\bSEPURA\b",
        "TAIT": r"\bTAIT\b",
        "ABELL": r"\bABELL\b",
        "ALINCO": r"\bALINCO\b",
        "ANYTONE": r"\bANYTONE\b",
    }
    for brand, pattern in others.items():
        if re.search(pattern, spaced):
            found.append(brand)

    return found


def technical_catalog_detect_resources(file_name: str) -> list[str]:
    _raw, spaced, compact = technical_normalized_parts(file_name)
    found: list[str] = []

    def add(value: str) -> None:
        if value and value not in found:
            found.append(value)

    mototrbo = "MOTOTRBO" in compact
    mototrbo_cps_downgrade = mototrbo and "CPS" in compact and "DOWNGRADE" in compact
    mototrbo_service_manual = mototrbo and (
        "MANUALESDESERVICIO" in compact
        or "SERVICEMANUAL" in compact
    )
    mototrbo_userdata = mototrbo and "USERDATA" in compact
    mototrbo_tuner = mototrbo and "TUNER" in compact
    mototrbo_depottool = mototrbo and "DEPOTTOOL" in compact
    mototrbo_audio_patch = mototrbo and "AUDIOFIX" in compact and "PARCHE" in compact
    mototrbo_review_gobflash = mototrbo and "GOBFLASH" in compact

    mototrbo_cps_patch = mototrbo and "CPS" in compact and any(
        marker in compact
        for marker in (
            "PATCH", "CRACK", "WIDEBAND25KHZ", "ANALOGSUPPORT"
        )
    )
    mototrbo_cps_software = (
        mototrbo
        and "CPS" in compact
        and not mototrbo_cps_downgrade
        and not mototrbo_cps_patch
    )

    # Firmware MOTOTRBO histórico. Muchos paquetes no dicen "FIRMWARE";
    # se reconocen por el release R... y por la nomenclatura usada en el grupo.
    release_pattern = re.search(r"\bR\d+(?:\s+\d+){0,4}\b", spaced) is not None
    mototrbo_firmware = (
        mototrbo
        and not mototrbo_cps_downgrade
        and not mototrbo_cps_patch
        and not mototrbo_cps_software
        and not mototrbo_service_manual
        and not mototrbo_userdata
        and not mototrbo_tuner
        and not mototrbo_depottool
        and not mototrbo_audio_patch
        and not mototrbo_review_gobflash
        and (
            re.search(r"\bFIRMWARE\b", spaced) is not None
            or re.search(r"\bFW\b", spaced) is not None
            or release_pattern
        )
    )

    # Etiquetas MOTOTRBO de dominio confirmadas por el usuario.
    if mototrbo_service_manual:
        add("MANUAL")
        add("SERVICE_MANUAL")
    if mototrbo_userdata:
        add("USERDATA")
    if mototrbo_tuner:
        add("TUNER")
    if mototrbo_depottool:
        add("DEPOT")
        add("DEPOTTOOL")
    if mototrbo_audio_patch:
        add("PATCH")
        add("AUDIO_PATCH")
    if mototrbo_review_gobflash:
        add("REVIEW")
    if mototrbo_cps_downgrade:
        add("CPS")
        add("DOWNGRADE")
    if mototrbo_cps_patch:
        add("CPS")
        add("PATCH")
        add("CPS_PATCH")
        # CPS2159_Patches fue confirmado como parche/crack de 2.159.384.0.
        if "CRACK" in compact or "CPS2159PATCH" in compact:
            add("CRACK")
    if mototrbo_cps_software:
        add("CPS")
        add("CPS_SOFTWARE")
    if mototrbo_firmware:
        add("FIRMWARE")

    # Reglas genéricas para el resto del catálogo.
    generic_tests = {
        "CPS": (
            re.search(r"\bCPS(?:\s*\d+)?\b", spaced)
            or "MULTICPS" in compact
            or "APXCPS" in compact
        ),
        "FIRMWARE": (
            not mototrbo
            and (
                re.search(r"\bFIRMWARE\b", spaced)
                or re.search(r"\bFW\b", spaced)
            )
        ),
        "UPGRADE": (
            re.search(r"\bUPGRADE\b", spaced)
            or re.search(r"\bUPDATER\b", spaced)
            or "UPGRADEKIT" in compact
        ),
        "FLASH": (
            re.search(r"\bFLASH\b", spaced)
            or "FLASHBURN" in compact
        ),
        "DRIVER": re.search(r"\bDRIVER\b", spaced),
        "CODEPLUG": "CODEPLUG" in compact,
        "MANUAL": (
            re.search(r"\bMANUAL(?:ES)?\b", spaced)
            or re.search(r"\bSERVICE\s+MANUAL\b", spaced)
        ),
        "DEPOT": re.search(r"\bDEPOT\b", spaced),
        "RSS": re.search(r"\bRSS\b", spaced),
        "RECOVERY": re.search(r"\bRECOVERY\b", spaced),
        "RESET": "RESET" in compact,
        "PATCH": (
            re.search(r"\bPATCH(?:ES|ED)?\b", spaced)
            or "PATCH" in compact
        ),
        "CRACK": re.search(r"\bCRACKS?\b", spaced),
        "TUNER": re.search(r"\bTUNER\b", spaced),
        "DOWNGRADE": re.search(r"\bDOWNGRADE\b", spaced),
    }
    for key, value in generic_tests.items():
        if value:
            # No devolver FIRMWARE para el downgrade CPS MOTOTRBO.
            if key == "FIRMWARE" and mototrbo_cps_downgrade:
                continue
            add(key)

    return found

def technical_catalog_detect_equipment_classes(file_name: str) -> list[str]:
    """Clasifica PORTABLE/MOBILE/REPEATER solo con evidencia fuerte."""
    _raw, spaced, compact = technical_normalized_parts(file_name)
    found: list[str] = []

    def add(value: str) -> None:
        if value not in found:
            found.append(value)

    if re.search(r"\bPORTABLES?\b", spaced):
        add("PORTABLE")
    if re.search(r"\bMOBILES?\b", spaced):
        add("MOBILE")
    if re.search(r"\bREPEATERS?\b", spaced):
        add("REPEATER")

    # Inferencias de familias confirmadas.
    if re.search(r"\bXTS\s*\d+", spaced):
        add("PORTABLE")

    if "MOTOTRBO" in compact:
        if re.search(r"\b(?:R2|R5|R7|R7EX)\b", spaced):
            add("PORTABLE")
        if re.search(r"\bDGP\b", spaced):
            add("PORTABLE")
        if re.search(r"\b(?:DP\s*1400|SL\s*1600)\b", spaced):
            add("PORTABLE")
        if re.search(r"\b(?:DGM|DEM)\s*\d+", spaced) or re.search(r"\bDM1XXX\b", spaced):
            add("MOBILE")
        if re.search(r"\bSLR\b", spaced):
            add("REPEATER")

    return found

def technical_catalog_detect_technologies(file_name: str) -> list[str]:
    _raw, spaced, compact = technical_normalized_parts(file_name)
    found: list[str] = []

    if (
        re.search(r"\bDMR\b", spaced)
        or "DMRCT" in compact
        or compact.startswith("DMR")
    ):
        found.append("DMR")
    if "MOTOTRBO" in compact:
        found.append("MOTOTRBO")
    if "MAGONE" in compact:
        found.append("MAG_ONE")
    if "APX" in compact:
        found.append("APX")
    if (
        "ASTRO" in compact
        or re.search(r"\b(?:XTS|XTL)\s*\d+", spaced)
    ):
        found.append("ASTRO")
    for tech in ("P25", "TETRA", "NXDN", "SDR"):
        if tech in compact:
            found.append(tech)
    return found


TECHNICAL_MODEL_RULES: tuple[tuple[str, str], ...] = (
    ("KPG", r"\bKPG\s*([A-Z]?\d+[A-Z]?)\b"),
    ("NX",  r"\bNX\s*(\d{3,4})\b"),
    ("NXR", r"\bNXR\s*(\d{3,4})\b"),
    ("TKR", r"\bTKR\s*(\d{3,4})\b"),
    ("TK",  r"\bTK\s*(\d{3,4}[A-Z]?)\b"),
    ("TM",  r"\bTM\s*(\d{3,4}[A-Z]?)\b"),
    ("XTS", r"\bXTS\s*(\d{3,5})\b"),
    ("XTL", r"\bXTL\s*(\d{3,5})\b"),
    ("XPR", r"\bXPR\s*(\d{3,5}[A-Z]?)\b"),
    ("XIR-P", r"\bXIR\s*P\s*(\d{3,5}[A-Z]?)\b"),
    ("XIR-M", r"\bXIR\s*M\s*(\d{3,5}[A-Z]?)\b"),
    ("DEP", r"\bDEP\s*(\d{3,5})\b"),
    ("DGP", r"\bDGP\s*(\d{3,5}[A-Z]?)\b"),
    ("DP",  r"\bDP\s*(\d{3,5}[A-Z]?)\b"),
    ("EM",  r"\bEM\s*(\d{3,4})\b"),
    ("EP",  r"\bEP\s*(\d{3,4})\b"),
    ("GM",  r"\bGM\s*(\d{3,4}[A-Z]?)\b"),
    ("GP",  r"\bGP\s*(\d{3,4}[A-Z]?)\b"),
    ("PRO", r"\bPRO\s*(\d{4,5})\b"),
    ("DGM", r"\bDGM\s*(\d{4}[A-Z]?)\b"),
    ("DEM", r"\bDEM\s*(\d{3,4}[A-Z]?)\b"),
    ("SLR", r"\bSLR\s*(\d{3,5}[A-Z]?)\b"),
    ("PD",  r"\bPD\s*(\d{3,4})\b"),
    ("HP",  r"\bHP\s*(\d{3,4})\b"),
    ("HM",  r"\bHM\s*(\d{3,4})\b"),
    ("HR",  r"\bHR\s*(\d{3,4})\b"),
    ("PNC", r"\bPNC\s*(\d+[A-Z]?)\b"),
    ("MD",  r"\bMD\s*(\d{3,4}[A-Z]?)\b"),
    ("RD",  r"\bRD\s*(\d{3,4}[A-Z]?)\b"),
    ("TC",  r"\bTC\s*(\d{3,4}[A-Z]?)\b"),
    ("VXR", r"\bVXR\s*(\d+)\b"),
    ("FT",  r"\bFT\s*(\d{3,4})\b"),
    ("UV",  r"\bUV\s*(\d+[A-Z]*)\b"),
)


def technical_catalog_detect_models(file_name: str) -> list[str]:
    raw, spaced, compact = technical_normalized_parts(file_name)
    found: list[str] = []
    seen: set[str] = set()

    def add(value: str) -> None:
        if value and value not in seen:
            seen.add(value)
            found.append(value)

    for prefix, pattern in TECHNICAL_MODEL_RULES:
        for match in re.finditer(pattern, spaced):
            add(f"{prefix}-{match.group(1)}")

    # Motorola Mag One usa modelos muy cortos (A8, D8, X10D, etc.).
    # Se reconocen únicamente cuando el nombre del archivo contiene MAG ONE,
    # para evitar que tokens cortos genéricos se conviertan en modelos falsos.
    mag_one_match = re.search(
        r"\bMAG\s+ONE\s+([A-Z]{1,3}\d{1,4}[A-Z]?)\b",
        spaced,
    )
    if mag_one_match:
        add(f"MAG-ONE-{mag_one_match.group(1)}")

    # Casos compactos legítimos: KPGD6, KPG166D.
    for match in re.finditer(
        r"(?<![A-Z0-9])KPG([A-Z]?\d+[A-Z]?)(?![A-Z0-9])",
        raw,
    ):
        add(f"KPG-{match.group(1)}")

    # Ej.: NX-1200, 1202,1300,1302,1700,1800.
    nx_match = re.search(
        r"\bNX[-_ ]?(\d{3,4})((?:\s*[,;/]\s*\d{3,4})+)",
        raw,
    )
    if nx_match:
        numbers = [nx_match.group(1)] + re.findall(r"\d{3,4}", nx_match.group(2))
        for number in numbers:
            add(f"NX-{number}")

    # Modelos Motorola abreviados con una sola familia y varios números.
    # Ejemplo confirmado: DEM300_400 -> DEM-300 y DEM-400.
    # Se limita a DEM/DGM para no inferir compatibilidades no confirmadas.
    for family in ("DEM", "DGM"):
        family_multi = re.search(
            rf"\b{family}\s*(\d{{3,4}}[A-Z]?)(?P<tail>(?:\s+\d{{3,4}}[A-Z]?)+)\b",
            spaced,
        )
        if family_multi:
            add(f"{family}-{family_multi.group(1)}")
            for number in re.findall(
                r"\d{3,4}[A-Z]?",
                family_multi.group("tail"),
            ):
                add(f"{family}-{number}")

    # Familias Motorola APX.
    if re.search(r"\bAPX\s+N70\b", spaced) or "APXN70" in compact:
        add("APX-N70")
    if re.search(r"\bAPX\s+NEXT\b", spaced) or "APXNEXT" in compact:
        add("APX-NEXT")

    # Dominio MOTOTRBO confirmado a partir de los nombres históricos.
    if "MOTOTRBO" in compact:
        # R7EX antes que R7; los límites evitan que R7 capture R7EX.
        for model in ("R7EX", "R7", "R5", "R2"):
            if re.search(rf"\b{re.escape(model)}\b", spaced):
                add(model)

        if re.search(r"\bDGP\b", spaced):
            add("DGP")
        if re.search(r"\bDGM\b", spaced):
            add("DGM")
        if re.search(r"\bDEM\b", spaced):
            add("DEM")
        if re.search(r"\bSLR\b", spaced):
            add("SLR")
        if re.search(r"\bDM1XXX\b", spaced):
            add("DM1XXX")

        # DP1400 / SL1600.
        if re.search(r"\bDP\s*1400\b", spaced):
            add("DP-1400")
        if re.search(r"\bSL\s*1600\b", spaced):
            add("SL-1600")

        # DGM 5000e8000e -> dos modelos.
        dgm_concat = re.search(r"\bDGM\s+(\d{4}E\d{4}E)\b", spaced)
        if dgm_concat:
            for number in re.findall(r"\d{4}E", dgm_concat.group(1)):
                add(f"DGM-{number}")

    return found[:20]

def technical_catalog_detect_software(file_name: str, models: list[str]) -> list[str]:
    _raw, _spaced, compact = technical_normalized_parts(file_name)
    result: list[str] = []

    def add(value: str) -> None:
        if value not in result:
            result.append(value)

    for model in models:
        if model.startswith("KPG-"):
            add(model)
    if "MOTOTRBO" in compact and "CPS" in compact:
        add("MOTOTRBO CPS")
    if "APX" in compact and "CPS" in compact:
        add("APX CPS")
    if "MOTOTRBO" in compact and "DEPOTTOOL" in compact:
        add("MOTOTRBO DEPOTTOOL")
    if "MOTOTRBO" in compact and "BUILD828" in compact and "RM" in compact:
        add("RM")
    return result

def technical_catalog_detect_versions(file_name: str) -> list[str]:
    raw = technical_stem(file_name)
    compact = technical_term_normalized(raw)
    result: list[str] = []

    def add(value: str) -> None:
        if value and value not in result:
            result.append(value)

    for pattern in (
        r"(?:^|[_\-\s])V(\d+(?:\.\d+){1,4})(?=$|[_\-\s(])",
        r"(?:^|[_\-\s])R(\d+(?:\.\d+){0,4})(?=$|[_\-\s(])",
    ):
        for match in re.finditer(pattern, raw):
            value = match.group(1)
            if "MOTOTRBO" in compact and value in {"2", "5", "7"}:
                # En nombres de firmware DGP, R2/R5/R7 son modelos, no revisiones.
                continue
            add(value)

    # Equivalencias/relaciones confirmadas en el material MOTOTRBO del grupo.
    if "MOTOTRBOCPS2159" in compact or "MOTOTRBOCPS2V21593840" in compact:
        add("2.159.384.0")
    if "MOTOTRBOCPS2V2134760" in compact:
        add("2.134.76.0")
    if "MOTOTRBOCPSV16BUILD828STANDALONELA" in compact and "CRACK" not in compact:
        add("2.134.76.0")
    if "BUILD828" in compact and "CPS" in compact:
        add("CPS16 BUILD 828")
    if "DEPOTTOOLV140" in compact:
        add("14.0")
    if "AUDIOFIX10249" in compact:
        add("1.0.2.49")

    return result[:6]

def technical_catalog_parse(file_name: str) -> dict[str, list[str]]:
    models = technical_catalog_detect_models(file_name)
    return {
        "BRAND": technical_catalog_detect_brands(file_name),
        "RESOURCE": technical_catalog_detect_resources(file_name),
        "TECHNOLOGY": technical_catalog_detect_technologies(file_name),
        "SOFTWARE": technical_catalog_detect_software(file_name, models),
        "VERSION": technical_catalog_detect_versions(file_name),
        "MODEL": models,
        "EQUIPMENT_CLASS": technical_catalog_detect_equipment_classes(file_name),
    }


def _technical_catalog_upsert_conn(conn: sqlite3.Connection, row: sqlite3.Row | dict) -> None:
    file_name = str(row["file_name"] or "").strip()
    parsed = technical_catalog_parse(file_name)
    now = datetime.now(BOT_TZ).isoformat(timespec="seconds")

    brands = parsed["BRAND"]
    resources = parsed["RESOURCE"]
    technologies = parsed["TECHNOLOGY"]
    software = parsed["SOFTWARE"]
    versions = parsed["VERSION"]
    models = parsed["MODEL"]
    equipment_classes = parsed["EQUIPMENT_CLASS"]

    search_parts = [
        file_name,
        *brands,
        *resources,
        *technologies,
        *software,
        *versions,
        *models,
        *equipment_classes,
    ]
    search_text = " | ".join(part for part in search_parts if part)

    conn.execute(
        """
        INSERT INTO technical_file_catalog (
            chat_id, sha256, message_id, file_unique_id, file_name, file_size,
            sender_id, sender_name, first_seen, brands, resources, technologies,
            software, versions, models, equipment_classes, search_text, parser_version, updated_at
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(chat_id, sha256) DO UPDATE SET
            message_id = excluded.message_id,
            file_unique_id = excluded.file_unique_id,
            file_name = excluded.file_name,
            file_size = excluded.file_size,
            sender_id = excluded.sender_id,
            sender_name = excluded.sender_name,
            first_seen = excluded.first_seen,
            brands = excluded.brands,
            resources = excluded.resources,
            technologies = excluded.technologies,
            software = excluded.software,
            versions = excluded.versions,
            models = excluded.models,
            equipment_classes = excluded.equipment_classes,
            search_text = excluded.search_text,
            parser_version = excluded.parser_version,
            updated_at = excluded.updated_at
        """,
        (
            int(row["chat_id"]),
            str(row["sha256"]),
            int(row["message_id"]),
            str(row["file_unique_id"] or ""),
            file_name,
            int(row["file_size"] or 0),
            int(row["sender_id"] or 0),
            str(row["sender_name"] or ""),
            str(row["first_seen"] or ""),
            " | ".join(brands),
            " | ".join(resources),
            " | ".join(technologies),
            " | ".join(software),
            " | ".join(versions),
            " | ".join(models),
            " | ".join(equipment_classes),
            search_text,
            TECHNICAL_CATALOG_PARSER_VERSION,
            now,
        ),
    )

    conn.execute(
        "DELETE FROM technical_file_terms WHERE chat_id = ? AND sha256 = ?",
        (int(row["chat_id"]), str(row["sha256"])),
    )
    for term_type, values in parsed.items():
        for value in values:
            normalized_value = technical_term_normalized(value)
            if not normalized_value:
                continue
            conn.execute(
                """
                INSERT OR IGNORE INTO technical_file_terms (
                    chat_id, sha256, term_type, term_value, normalized_value
                )
                VALUES (?, ?, ?, ?, ?)
                """,
                (
                    int(row["chat_id"]),
                    str(row["sha256"]),
                    term_type,
                    value,
                    normalized_value,
                ),
            )


def technical_catalog_sync_group(chat_id: int) -> tuple[int, int]:
    """Reconcilia el catálogo paralelo con file_fingerprints sin tocar SHA-256."""
    with db.lock:
        rows = db.conn.execute(
            """
            SELECT chat_id, sha256, message_id, file_unique_id, file_name,
                   file_size, sender_id, sender_name, first_seen
            FROM file_fingerprints
            WHERE chat_id = ?
            ORDER BY message_id
            """,
            (chat_id,),
        ).fetchall()

        with db.conn:
            for row in rows:
                _technical_catalog_upsert_conn(db.conn, row)

        catalog_count = int(db.conn.execute(
            "SELECT COUNT(*) FROM technical_file_catalog WHERE chat_id = ?",
            (chat_id,),
        ).fetchone()[0])
    return len(rows), catalog_count


def technical_catalog_upsert_fingerprint(
    *,
    chat_id: int,
    sha256: str,
    message_id: int,
    file_unique_id: str,
    file_name: str,
    file_size: int,
    sender_id: int,
    sender_name: str,
) -> None:
    """Añade/actualiza SOLO el catálogo después de registrar una huella original."""
    with db.lock:
        row = db.conn.execute(
            """
            SELECT chat_id, sha256, message_id, file_unique_id, file_name,
                   file_size, sender_id, sender_name, first_seen
            FROM file_fingerprints
            WHERE chat_id = ? AND sha256 = ?
            LIMIT 1
            """,
            (chat_id, sha256),
        ).fetchone()
        if row is None:
            return
        with db.conn:
            _technical_catalog_upsert_conn(db.conn, row)


TECHNICAL_QUERY_MODEL_PATTERNS: tuple[tuple[str, str], ...] = (
    ("KPG", r"\bKPG[-_ ]?([A-Z]?\d+[A-Z]?)\b"),
    ("NX",  r"\bNX[-_ ]?(\d{3,4})\b"),
    ("NXR", r"\bNXR[-_ ]?(\d{3,4})\b"),
    ("TKR", r"\bTKR[-_ ]?(\d{3,4})\b"),
    ("TK",  r"\bTK[-_ ]?(\d{3,4}[A-Z]?)\b"),
    ("TM",  r"\bTM[-_ ]?(\d{3,4}[A-Z]?)\b"),
    ("XTS", r"\bXTS[-_ ]?(\d{3,5})\b"),
    ("XTL", r"\bXTL[-_ ]?(\d{3,5})\b"),
    ("XPR", r"\bXPR[-_ ]?(\d{3,5}[A-Z]?)\b"),
    ("XIR-P", r"\bXIR[-_ ]?P[-_ ]?(\d{3,5}[A-Z]?)\b"),
    ("XIR-M", r"\bXIR[-_ ]?M[-_ ]?(\d{3,5}[A-Z]?)\b"),
    ("DEP", r"\bDEP[-_ ]?(\d{3,5})\b"),
    ("DGP", r"\bDGP[-_ ]?(\d{3,5}[A-Z]?)\b"),
    ("DP",  r"\bDP[-_ ]?(\d{3,5}[A-Z]?)\b"),
    ("EM",  r"\bEM[-_ ]?(\d{3,4})\b"),
    ("EP",  r"\bEP[-_ ]?(\d{3,4})\b"),
    ("GM",  r"\bGM[-_ ]?(\d{3,4}[A-Z]?)\b"),
    ("GP",  r"\bGP[-_ ]?(\d{3,4}[A-Z]?)\b"),
    ("PRO", r"\bPRO[-_ ]?(\d{4,5})\b"),
    ("DGM", r"\bDGM[-_ ]?(\d{4}[A-Z]?)\b"),
    ("DEM", r"\bDEM[-_ ]?(\d{3,4}[A-Z]?)\b"),
    ("SLR", r"\bSLR[-_ ]?(\d{3,5}[A-Z]?)\b"),
    ("PD",  r"\bPD[-_ ]?(\d{3,4})\b"),
    ("HP",  r"\bHP[-_ ]?(\d{3,4})\b"),
    ("HM",  r"\bHM[-_ ]?(\d{3,4})\b"),
    ("HR",  r"\bHR[-_ ]?(\d{3,4})\b"),
    ("PNC", r"\bPNC[-_ ]?(\d+[A-Z]?)\b"),
    ("MD",  r"\bMD[-_ ]?(\d{3,4}[A-Z]?)\b"),
    ("RD",  r"\bRD[-_ ]?(\d{3,4}[A-Z]?)\b"),
    ("TC",  r"\bTC[-_ ]?(\d{3,4}[A-Z]?)\b"),
)


def technical_query_detect_models(query: str) -> list[str]:
    q = technical_ascii_upper(query)
    q_spaced = re.sub(r"[^A-Z0-9]+", " ", q)
    q_spaced = re.sub(r"\s+", " ", q_spaced).strip()
    q_compact = technical_term_normalized(q)
    result: list[str] = []
    seen: set[str] = set()

    def add(value: str) -> None:
        if value and value not in seen:
            seen.add(value)
            result.append(value)

    # Motorola Mag One: la familia permite modelos cortos como A8/X10D.
    mag_one_match = re.search(
        r"\bMAG[-_ ]*ONE[-_ ]*([A-Z]{1,3}\d{1,4}[A-Z]?)\b",
        q,
    )
    if mag_one_match:
        add(f"MAG-ONE-{mag_one_match.group(1)}")

    for match in re.finditer(r"\bKPG([A-Z]?\d+[A-Z]?)\b", q):
        add(f"KPG-{match.group(1)}")

    for prefix, pattern in TECHNICAL_QUERY_MODEL_PATTERNS:
        for match in re.finditer(pattern, q):
            add(f"{prefix}-{match.group(1)}")

    if re.search(r"\bN70\b", q) or "APXN70" in q_compact:
        add("APX-N70")
    if re.search(r"\bNEXT\b", q) and ("APX" in q or "FIRMWARE" in q):
        add("APX-NEXT")

    # Familias/modelos MOTOTRBO. R2/R5 son ambiguos fuera de contexto.
    mototrbo_context = any(token in q_compact for token in ("MOTOTRBO", "FIRMWARE", "DGP"))
    if re.search(r"\bR7EX\b", q):
        add("R7EX")
    if re.search(r"\bR7\b", q):
        add("R7")
    if mototrbo_context and re.search(r"\bR5\b", q):
        add("R5")
    if mototrbo_context and re.search(r"\bR2\b", q):
        add("R2")
    for family in ("DGP", "DGM", "DEM", "SLR", "DM1XXX"):
        if re.search(rf"\b{family}\b", q_spaced):
            add(family)

    # DGM5000e8000e escrito compacto.
    dgm_compact = re.search(r"DGM((?:\d{4}E?)+)", q_compact)
    if dgm_compact:
        add("DGM")
        for number in re.findall(r"\d{4}E?", dgm_compact.group(1)):
            add(f"DGM-{number}")

    return result


def technical_query_detect_raw_model_anchors(
    query: str,
    models: list[str],
    brands: list[str],
) -> list[str]:
    """Detecta destinos de modelo que NO pueden degradarse a búsqueda por marca.

    Ejemplos:
      HYTERA MD616 -> MD-616 (modelo canónico; no queda como raw)
      HYTERA RD985 -> RD-985 (modelo canónico; no queda como raw)
      HYTERA 626   -> ancla raw "626"
      MOTOROLA XPR7550E -> XPR-7550E si el parser lo reconoce; de lo contrario
                           el identificador explícito sigue siendo obligatorio.

    Una ancla raw nunca se usa para "rellenar" resultados: si no existe una
    coincidencia segura, la búsqueda devuelve cero filas.
    """
    result: list[str] = []
    seen: set[str] = set()
    canonical_compacts = {
        technical_term_normalized(model)
        for model in models
        if model
    }

    def add(value: str) -> None:
        normalized = technical_term_normalized(value)
        if not normalized or normalized in canonical_compacts or normalized in seen:
            return
        seen.add(normalized)
        result.append(value.upper())

    # Identificadores alfanuméricos explícitos. archive_model_terms ya exige
    # prefijo alfabético + 3-5 dígitos y evita confundir revisiones cortas.
    for identifier in archive_model_terms(query):
        add(identifier)

    # Modelo escrito solo con números, únicamente si hay una marca explícita.
    # Así "Hytera 626" es específico, mientras que un "626" aislado no activa
    # por sí solo esta regla.
    if brands:
        q = technical_ascii_upper(query)
        for match in re.finditer(r"\b(\d{3,5}[A-Z]?)\b", q):
            token = match.group(1)

            # No tomar partes de versiones decimales: 2.159.384.0.
            before = q[match.start() - 1] if match.start() > 0 else ""
            after = q[match.end()] if match.end() < len(q) else ""
            if before == "." or after == ".":
                continue

            # Años no son modelos.
            if token.isdigit() and len(token) == 4 and 1900 <= int(token) <= 2099:
                continue

            left = q[max(0, match.start() - 12):match.start()]
            right = q[match.end():match.end() + 10]

            # Evitar frecuencias y números declarados como versión/build.
            if re.search(r"(?:VERSION|VERSIÓN|BUILD|REV|V|R)\s*$", left):
                continue
            if re.match(r"\s*(?:MHZ|KHZ|HZ)\b", right):
                continue

            add(token)

    return result


def technical_query_detect_versions(query: str) -> list[str]:
    q = technical_ascii_upper(query)
    compact = technical_term_normalized(q)
    found: list[str] = []

    def add(value: str) -> None:
        if value and value not in found:
            found.append(value)

    for match in re.finditer(r"\b(?:V|R)?(\d+\.\d+(?:\.\d+){0,3})\b", q):
        add(match.group(1))

    if "CPS2159" in compact:
        add("2.159.384.0")
    if "CPS2134" in compact:
        add("2.134.76.0")
    if re.search(r"\bCPS\s*16(?:\.0)?\s+BUILD\s+828\b", q):
        add("CPS16 BUILD 828")

    return found


def technical_query_detect_aliases(query: str, mapping: dict[str, tuple[str, ...]]) -> list[str]:
    q_compact = technical_term_normalized(query)
    found: list[str] = []
    for canonical, aliases in mapping.items():
        if any(technical_term_normalized(alias) in q_compact for alias in aliases):
            found.append(canonical)
    return found


def technical_query_interpret(query: str) -> dict[str, object]:
    models = technical_query_detect_models(query)
    versions = technical_query_detect_versions(query)

    brands = technical_query_detect_aliases(query, {
        "MOTOROLA": ("MOTOROLA",),
        "KENWOOD": ("KENWOOD",),
        "HYTERA": ("HYTERA",),
        "ICOM": ("ICOM",),
        "YAESU": ("YAESU",),
        "BAOFENG": ("BAOFENG", "BEAOFENG"),
        "VERTEX": ("VERTEX",),
        "RETEVIS": ("RETEVIS",),
        "TYT": ("TYT",),
        "SEPURA": ("SEPURA",),
        "TAIT": ("TAIT",),
        "ABELL": ("ABELL",),
        "ALINCO": ("ALINCO",),
        "ANYTONE": ("ANYTONE",),
    })
    technologies = technical_query_detect_aliases(query, {
        "MOTOTRBO": ("MOTOTRBO", "MOTORTRBO", "MOTORBO", "MOTOTURBO", "MOTRBO"),
        "MAG_ONE": ("MAG ONE", "MAGONE", "MAG-ONE"),
        "APX": ("APX",),
        "ASTRO": ("ASTRO", "XTS"),
        "DMR": ("DMR",),
        "P25": ("P25",),
        "TETRA": ("TETRA",),
        "NXDN": ("NXDN",),
        "SDR": ("SDR",),
    })

    raw_model_anchors = technical_query_detect_raw_model_anchors(
        query,
        models,
        brands,
    )

    q_norm = technical_term_normalized(query)
    resources = technical_query_detect_aliases(query, {
        "CPS": ("CPS", "SOFTWARE DE PROGRAMACION", "SOFTWARE PROGRAMACION"),
        "FIRMWARE": ("FIRMWARE", " FW "),
        "DRIVER": ("DRIVER", "CONTROLADOR"),
        "CODEPLUG": ("CODEPLUG",),
        "MANUAL": ("MANUAL", "MANUAL DE SERVICIO", "MANUALES DE SERVICIO"),
        "SERVICE_MANUAL": ("MANUAL DE SERVICIO", "MANUALES DE SERVICIO"),
        "DEPOT": ("DEPOT",),
        "DEPOTTOOL": ("DEPOTTOOL", "DEPOT TOOL"),
        "RSS": ("RSS",),
        "RESET": ("RESET",),
        "PATCH": ("PATCH", "PARCHE"),
        "CRACK": ("CRACK",),
        "TUNER": ("TUNER", "TUNERS", "CALIBRACION", "CALIBRAR"),
        "USERDATA": ("USERDATA", "USERDATAS"),
        "AUDIO_PATCH": ("PARCHE DE AUDIO", "AUDIOFIX"),
        "UPGRADE": ("UPGRADE", "UPDATER"),
        "DOWNGRADE": ("DOWNGRADE",),
    })

    # "programa CPS" significa software principal, no patch/crack.
    if "CPS" in q_norm and any(token in q_norm for token in ("PROGRAMA", "SOFTWARE")):
        if "CPS_SOFTWARE" not in resources:
            resources.append("CPS_SOFTWARE")

    equipment_classes = technical_query_detect_aliases(query, {
        "PORTABLE": ("PORTABLE", "PORTATIL", "PORTATILES"),
        "MOBILE": ("MOBILE", "MOVIL", "MOVILES"),
        "REPEATER": ("REPEATER", "REPETIDOR", "REPETIDORES"),
    })

    inferred_brand = None
    if (
        "MOTOTRBO" in technologies
        or "MAG_ONE" in technologies
        or "APX" in technologies
        or "ASTRO" in technologies
    ):
        inferred_brand = "MOTOROLA"
    elif any(
        m.startswith((
            "APX-", "XTS-", "XTL-", "XPR-", "XIR-P-", "XIR-M-",
            "DEP-", "DGP-", "DP-", "EM-", "EP-", "GM-", "GP-", "PRO-",
            "DGM-", "DEM-", "SLR-", "MAG-ONE-"
        ))
        or m in {"R2", "R5", "R7", "R7EX", "DGP", "DGM", "DEM", "SLR", "DM1XXX"}
        for m in models
    ):
        inferred_brand = "MOTOROLA"
    elif any(m.startswith(("KPG-", "NX-", "NXR-", "TKR-", "TK-", "TM-")) for m in models):
        inferred_brand = "KENWOOD"
    elif any(m.startswith(("PD-", "HP-", "HM-", "HR-", "PNC-", "MD-", "RD-", "TC-")) for m in models):
        inferred_brand = "HYTERA"
    if inferred_brand and inferred_brand not in brands:
        brands.append(inferred_brand)

    flags = {
        "wants_software": any(token in q_norm for token in ("SOFTWARE", "PROGRAMA", "PROGRAMACION", "PROGRAMMING")),
        "wants_cps": "CPS" in q_norm,
        "patch": "PATCH" in q_norm or "PARCHE" in q_norm,
        "crack": "CRACK" in q_norm,
        "downgrade": "DOWNGRADE" in q_norm,
        "firmware": "FIRMWARE" in q_norm,
        "reset": "RESET" in q_norm,
        "wideband": "WIDEBAND" in q_norm or "25KHZ" in q_norm,
        "analog_support": "ANALOGSUPPORT" in q_norm or "SOPORTEANALOG" in q_norm,
    }
    return {
        "models": models,
        "raw_model_anchors": raw_model_anchors,
        "brands": brands,
        "technologies": technologies,
        "resources": resources,
        "versions": versions,
        "equipment_classes": equipment_classes,
        "flags": flags,
    }

def technical_catalog_fetch_exact(
    chat_id: int,
    requirements: list[tuple[str, str]],
) -> list[sqlite3.Row]:
    if not requirements:
        return []

    clauses: list[str] = []
    params: list[object] = [chat_id]
    for term_type, value in requirements:
        clauses.append(
            """
            EXISTS (
                SELECT 1
                FROM technical_file_terms t
                WHERE t.chat_id = c.chat_id
                  AND t.sha256 = c.sha256
                  AND t.term_type = ?
                  AND t.normalized_value = ?
            )
            """
        )
        params.extend([term_type, technical_term_normalized(value)])

    sql = f"""
        SELECT c.chat_id, c.sha256, c.message_id, c.file_unique_id, c.file_name,
               c.file_size, c.sender_id, c.sender_name, c.first_seen,
               c.brands, c.resources, c.technologies, c.software,
               c.versions, c.models, c.equipment_classes, c.search_text
        FROM technical_file_catalog c
        WHERE c.chat_id = ?
          AND {' AND '.join(clauses)}
    """
    with db.lock:
        return db.conn.execute(sql, params).fetchall()



def technical_catalog_fetch_candidates(
    chat_id: int,
    requirements: list[tuple[str, str]],
) -> list[sqlite3.Row]:
    """Obtiene candidatos base sin relajar ninguna condición existente."""
    if requirements:
        return technical_catalog_fetch_exact(chat_id, requirements)

    with db.lock:
        return db.conn.execute(
            """
            SELECT c.chat_id, c.sha256, c.message_id, c.file_unique_id, c.file_name,
                   c.file_size, c.sender_id, c.sender_name, c.first_seen,
                   c.brands, c.resources, c.technologies, c.software,
                   c.versions, c.models, c.equipment_classes, c.search_text
            FROM technical_file_catalog c
            WHERE c.chat_id = ?
            """,
            (chat_id,),
        ).fetchall()


def technical_catalog_row_matches_strict_anchor(
    row: sqlite3.Row,
    anchor: str,
) -> bool:
    """Exige coincidencia real del modelo/identificador solicitado.

    No usa similitud difusa. Para "626" acepta un modelo catalogado que termine
    exactamente en 626 (TC-626, MD-626, etc.) o el token 626 visible en el nombre.
    """
    anchor_norm = technical_term_normalized(anchor)
    if not anchor_norm:
        return False

    file_name = str(row["file_name"] or "")
    if archive_name_matches_anchor(file_name, anchor):
        return True

    model_values = [
        part.strip()
        for part in str(row["models"] or "").split("|")
        if part.strip()
    ]

    if anchor_norm.isdigit():
        for model in model_values:
            model_norm = technical_term_normalized(model)
            if re.search(rf"{re.escape(anchor_norm)}$", model_norm):
                return True
        return False

    for model in model_values:
        if archive_name_matches_anchor(model, anchor):
            return True

    return False



def technical_kpg_numeric_family_root(value: str) -> str | None:
    """Devuelve la raíz compacta solo para consultas KPG + número puro.

    Ejemplos:
      KPG-141 -> KPG141
      KPG 141 -> KPG141 (ya llega canonizado normalmente)
      KPG-141D -> None  (si el usuario especificó la letra, se mantiene exacto)
      KPG-D6   -> None  (identificador alfanumérico específico)
    """
    compact = technical_term_normalized(value)
    match = re.fullmatch(r"KPG(\d+)", compact)
    if not match:
        return None
    return f"KPG{match.group(1)}"


def technical_catalog_row_matches_kpg_numeric_family(
    row: sqlite3.Row,
    requested: str,
) -> bool:
    """Coincidencia controlada de una familia KPG numérica.

    Si el usuario pide KPG-141, acepta variantes que conservan exactamente
    el mismo número y solo agregan letras al final:
      KPG-141
      KPG-141D
      KPG-141N
      KPG-141DN

    Rechaza:
      KPG-1410
      KPG-1412D
      KPG-14
    """
    root = technical_kpg_numeric_family_root(requested)
    if not root:
        return False

    # 1) Metadato estructurado de software.
    for part in str(row["software"] or "").split("|"):
        candidate = technical_term_normalized(part.strip())
        if candidate and re.fullmatch(rf"{re.escape(root)}[A-Z]*", candidate):
            return True

    # 2) Nombre real del archivo. archive_name_matches_anchor ya conserva
    #    el número solicitado y permite únicamente sufijos alfabéticos.
    file_name = str(row["file_name"] or "")
    if archive_name_matches_anchor(file_name, requested):
        return True

    return False


def technical_catalog_field_has(row: sqlite3.Row, field: str, wanted: str) -> bool:
    normalized = technical_term_normalized(wanted)
    return any(
        technical_term_normalized(part.strip()) == normalized
        for part in str(row[field] or "").split("|")
        if part.strip()
    )


def technical_catalog_rank(
    row: sqlite3.Row,
    query: str,
    requirements: list[tuple[str, str]],
) -> float:
    parsed = technical_query_interpret(query)
    flags = parsed["flags"]
    score = 0.0

    field_map = {
        "BRAND": "brands",
        "RESOURCE": "resources",
        "TECHNOLOGY": "technologies",
        "SOFTWARE": "software",
        "VERSION": "versions",
        "MODEL": "models",
        "EQUIPMENT_CLASS": "equipment_classes",
    }
    weights = {
        "BRAND": 25.0,
        "RESOURCE": 45.0,
        "TECHNOLOGY": 40.0,
        "SOFTWARE": 110.0,
        "VERSION": 80.0,
        "MODEL": 100.0,
        "EQUIPMENT_CLASS": 70.0,
    }
    for term_type, value in requirements:
        field = field_map.get(term_type)
        if field and technical_catalog_field_has(row, field, value):
            score += weights.get(term_type, 10.0)

    name_compact = technical_term_normalized(str(row["file_name"] or ""))

    if flags["wants_software"]:
        if str(row["software"] or ""):
            score += 45.0
        if technical_catalog_field_has(row, "resources", "CPS_SOFTWARE"):
            score += 60.0
        if technical_catalog_field_has(row, "resources", "CPS_PATCH"):
            score -= 50.0
        if technical_catalog_field_has(row, "resources", "CPS"):
            score += 35.0
        if "KPG" in name_compact:
            score += 30.0

    if flags["wants_cps"] and technical_catalog_field_has(row, "resources", "CPS"):
        score += 25.0
    elif flags["wants_cps"] and str(row["software"] or ""):
        score += 45.0

    if flags["wants_cps"] and technical_catalog_field_has(row, "resources", "CPS_SOFTWARE"):
        score += 30.0

    specials = (
        ("PATCH", flags["patch"], 35.0),
        ("CRACK", flags["crack"], 20.0),
        ("DOWNGRADE", flags["downgrade"], 40.0),
        ("FIRMWARE", flags["firmware"], 15.0),
        ("RESET", flags["reset"], 40.0),
    )
    for resource, requested, penalty in specials:
        present = technical_catalog_field_has(row, "resources", resource)
        if present and requested:
            score += 60.0
        elif present and not requested:
            score -= penalty

    if "WIDEBAND" in name_compact or "25KHZ" in name_compact:
        score += 60.0 if flags["wideband"] else -35.0
    if "ANALOGSUPPORT" in name_compact:
        score += 60.0 if flags["analog_support"] else -35.0

    return score

TECHNICAL_SEARCH_EXTENSIONS = (".rar", ".zip", ".7z", ".exe")


def technical_file_allowed(file_name: str) -> bool:
    lower = (file_name or "").lower()
    return any(lower.endswith(ext) for ext in TECHNICAL_SEARCH_EXTENSIONS)


def technical_catalog_search_rows(
    chat_id: int,
    query: str,
    limit: int = ARCHIVE_SEARCH_MAX_RESULTS,
) -> tuple[bool, list[sqlite3.Row]]:
    """Búsqueda técnica estructurada con anclas estrictas de modelo.

    Regla principal:
      - una consulta amplia ("Hytera") puede devolver archivos generales;
      - una consulta con modelo/identificador ("Hytera MD616", "Hytera 626")
        SOLO devuelve archivos que satisfacen ese destino;
      - KPG + número puro ("KPG 141") admite variantes alfabéticas del mismo
        número ("KPG-141D"), pero nunca cambia el número solicitado;
      - si el destino no existe, devuelve [] y NO rellena con archivos de marca.
    """
    parsed = technical_query_interpret(query)
    models = list(parsed["models"])
    raw_model_anchors = list(parsed.get("raw_model_anchors", []))
    brands = list(parsed["brands"])
    technologies = list(parsed["technologies"])
    resources = list(parsed["resources"])
    versions = list(parsed["versions"])
    equipment_classes = list(parsed["equipment_classes"])

    base: list[tuple[str, str]] = []
    base.extend(("BRAND", value) for value in brands)
    base.extend(("TECHNOLOGY", value) for value in technologies)
    base.extend(("RESOURCE", value) for value in resources)
    base.extend(("VERSION", value) for value in versions)
    base.extend(("EQUIPMENT_CLASS", value) for value in equipment_classes)

    has_specific_target = bool(models or raw_model_anchors)
    structured = bool(base or has_specific_target)
    if not structured:
        return False, []

    max_results = max(1, min(12, int(limit)))

    if has_specific_target:
        per_target: list[list[tuple[float, sqlite3.Row]]] = []
        all_scored: list[tuple[float, sqlite3.Row]] = []

        # Modelos que el catálogo conoce de forma canónica.
        for model in models:
            requirements = list(base)

            kpg_numeric_family = technical_kpg_numeric_family_root(model)

            if kpg_numeric_family:
                # Regla KPG numérica:
                # "KPG 141" significa "cualquier variante KPG-141 con
                # sufijo alfabético", por ejemplo KPG-141D.
                #
                # NO degradamos a "cualquier KPG": primero respetamos todos
                # los filtros base y después exigimos la misma raíz numérica.
                rows = technical_catalog_fetch_candidates(chat_id, base)
                rows = [
                    row
                    for row in rows
                    if technical_catalog_row_matches_kpg_numeric_family(row, model)
                ]
            else:
                if model.startswith("KPG-"):
                    requirements.append(("SOFTWARE", model))
                else:
                    requirements.append(("MODEL", model))

                rows = technical_catalog_fetch_exact(chat_id, requirements)

                # Fallback controlado ya existente: CPS + modelo concreto.
                # Solo quita la etiqueta CPS, NUNCA quita el modelo.
                if not rows and ("RESOURCE", "CPS") in requirements:
                    fallback_requirements = [
                        item for item in requirements
                        if item != ("RESOURCE", "CPS")
                    ]
                    rows = technical_catalog_fetch_exact(chat_id, fallback_requirements)
                    if rows:
                        requirements = fallback_requirements

            ranked = [
                (
                    technical_catalog_rank(row, query, requirements)
                    + (
                        120.0
                        if kpg_numeric_family
                        and technical_catalog_row_matches_kpg_numeric_family(row, model)
                        else 0.0
                    ),
                    row,
                )
                for row in rows
                if technical_file_allowed(str(row["file_name"] or ""))
            ]
            ranked.sort(
                key=lambda item: (item[0], int(item[1]["message_id"])),
                reverse=True,
            )
            per_target.append(ranked)
            all_scored.extend(ranked)

        # Identificadores/modelos explícitos no catalogados de forma canónica,
        # incluyendo números solos acompañados por una marca: "Hytera 626".
        if raw_model_anchors:
            raw_candidates = technical_catalog_fetch_candidates(chat_id, base)

            for anchor in raw_model_anchors:
                anchor_rows = [
                    row
                    for row in raw_candidates
                    if technical_file_allowed(str(row["file_name"] or ""))
                    and technical_catalog_row_matches_strict_anchor(row, anchor)
                ]

                ranked = [
                    (technical_catalog_rank(row, query, base) + 100.0, row)
                    for row in anchor_rows
                ]
                ranked.sort(
                    key=lambda item: (item[0], int(item[1]["message_id"])),
                    reverse=True,
                )
                per_target.append(ranked)
                all_scored.extend(ranked)

        # Cobertura por destino: si se pidieron varios modelos, intenta dar
        # primero la mejor coincidencia de cada uno.
        selected: list[sqlite3.Row] = []
        seen_sha: set[str] = set()

        for ranked in per_target:
            if not ranked:
                continue
            row = ranked[0][1]
            sha = str(row["sha256"])
            if sha not in seen_sha:
                seen_sha.add(sha)
                selected.append(row)

        all_scored.sort(
            key=lambda item: (item[0], int(item[1]["message_id"])),
            reverse=True,
        )

        for _score, row in all_scored:
            if len(selected) >= max_results:
                break
            sha = str(row["sha256"])
            if sha in seen_sha:
                continue
            seen_sha.add(sha)
            selected.append(row)

        # CRÍTICO: si no hubo coincidencia para el/los destinos específicos,
        # devolvemos vacío. No existe fallback genérico por marca.
        return True, selected[:max_results]

    # Consulta amplia sin modelo: mantiene el comportamiento previo.
    rows = technical_catalog_fetch_exact(chat_id, base)
    ranked = [
        (technical_catalog_rank(row, query, base), row)
        for row in rows
        if technical_file_allowed(str(row["file_name"] or ""))
    ]
    ranked.sort(
        key=lambda item: (item[0], int(item[1]["message_id"])),
        reverse=True,
    )
    return True, [row for _, row in ranked[:max_results]]


def search_archive_rows(chat_id: int, query: str, limit: int = ARCHIVE_SEARCH_MAX_RESULTS) -> list[sqlite3.Row]:
    structured, rows = technical_catalog_search_rows(chat_id, query, limit)
    if structured:
        return rows
    return search_archive_rows_legacy(chat_id, query, limit)


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
    if not pecos_help_invocation_allowed(text_value):
        return None

    # Primero usamos el parser técnico estructurado. Esto permite ignorar
    # palabras coloquiales alrededor de una referencia fuerte:
    # "Pecos rifatela porfa kpg d6" -> "KPG-D6".
    parsed = technical_query_interpret(text_value)
    parsed_models = list(parsed.get("models", []))
    parsed_raw_models = list(parsed.get("raw_model_anchors", []))
    parsed_brands = list(parsed.get("brands", []))
    parsed_resources = list(parsed.get("resources", []))

    if parsed_models or parsed_raw_models:
        clean_parts: list[str] = []
        for item in parsed_resources + parsed_brands + parsed_models + parsed_raw_models:
            value = str(item).strip()
            if value and value not in clean_parts:
                clean_parts.append(value)
        return " ".join(clean_parts)

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
        parsed_query = technical_query_interpret(" ".join(terms))
        specific_targets = (
            list(parsed_query.get("models", []))
            + list(parsed_query.get("raw_model_anchors", []))
        )

        if specific_targets:
            target_text = " / ".join(str(value).upper() for value in specific_targets)
            await context.bot.send_message(
                chat_id=chat.id,
                text=(
                    f"🔎 {usuario}, Pecos buscó «{' '.join(terms).upper()}», pero no encontró "
                    f"un archivo que pueda asociar con suficiente seguridad a {target_text}. "
                    "No mostraré archivos generales de la marca como sustituto."
                ),
            )
        else:
            await context.bot.send_message(
                chat_id=chat.id,
                text=(
                    f"🌵 {usuario}, Pecos revisó el archivo del pueblo y no encontró un archivo que "
                    f"cumpla suficientemente con «{' '.join(terms)}». Prefiero no mostrar coincidencias "
                    "parciales que puedan corresponder a otro equipo, marca o plataforma."
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



def radio_software_request_signal(text_value: str) -> bool:
    normalized = normalize_intent(text_value or "")
    signals = (
        "kpg", "software", "programa", "programacion", "programar",
        "cps", "alguien tendra", "alguien tiene", "me pueda ayudar",
        "me pueden ayudar", "que usa", "cual usa", "para un radio",
        "para una radio",
    )
    return any(signal in normalized for signal in signals)


def radio_map_exact_model_in_text(text_value: str, model: str) -> bool:
    """Detecta el modelo exacto; TK-480 no se confunde con TK-480G."""
    model = str(model or "").strip().upper()
    match = re.fullmatch(r"([A-Z]+)-([A-Z0-9]+)", model)
    if not match:
        return False

    prefix, body = match.groups()
    upper = technical_ascii_upper(text_value or "")
    return bool(
        re.search(
            rf"(?<![A-Z0-9]){re.escape(prefix)}[\s._-]*{re.escape(body)}(?![A-Z0-9])",
            upper,
        )
    )


def radio_map_exact_variant_in_text(text_value: str, variant: str) -> bool:
    variant = str(variant or "").strip().upper()
    if not variant:
        return True
    upper = technical_ascii_upper(text_value or "")
    return bool(
        re.search(
            rf"(?<![A-Z0-9]){re.escape(variant)}(?![A-Z0-9])",
            upper,
        )
    )


def find_radio_software_associations(text_value: str) -> list[sqlite3.Row]:
    if not text_value:
        return []

    matches: list[sqlite3.Row] = []
    for row in db.list_radio_software_map():
        model = str(row["model"] or "").strip()
        if not radio_map_exact_model_in_text(text_value, model):
            continue

        variant = str(row["variant"] or "").strip()
        if variant and not radio_map_exact_variant_in_text(text_value, variant):
            continue

        matches.append(row)

    unique: list[sqlite3.Row] = []
    seen: set[tuple[str, str, str]] = set()
    for row in matches:
        key = (
            str(row["model"] or "").upper(),
            str(row["variant"] or "").upper(),
            str(row["software"] or "").upper(),
        )
        if key in seen:
            continue
        seen.add(key)
        unique.append(row)

    return unique


def kpg_compatibility_question_intent(text_value: str) -> bool:
    normalized = normalize_intent(text_value or "")
    if "kpg" not in normalized:
        return False

    signals = (
        "que modelos", "cuales modelos", "para que modelos",
        "que radios", "cuales radios", "para que radios",
        "que equipos", "cuales equipos", "para que equipos",
        "compatible", "compatibilidad", "sirve para",
        "a que modelos", "a que radios", "a que equipos",
    )
    return any(signal in normalized for signal in signals)


def extract_requested_kpg_software(text_value: str) -> str | None:
    upper = technical_ascii_upper(text_value or "")
    match = re.search(r"\bKPG[\s._-]*([A-Z]?\d+[A-Z]*)\b", upper)
    if not match:
        return None
    return f"KPG-{match.group(1)}"


def find_kpg_compatibility_rows(text_value: str) -> list[sqlite3.Row]:
    requested = extract_requested_kpg_software(text_value)
    if not requested:
        return []

    requested_compact = technical_term_normalized(requested)
    numeric_family = technical_kpg_numeric_family_root(requested)

    matches = []
    for row in db.list_radio_software_map():
        if str(row["brand"] or "").upper() != "KENWOOD":
            continue

        software = str(row["software"] or "").strip()
        software_compact = technical_term_normalized(software)

        if numeric_family:
            if not re.fullmatch(
                rf"{re.escape(numeric_family)}[A-Z]*",
                software_compact,
            ):
                continue
        elif software_compact != requested_compact:
            continue

        matches.append(row)

    return matches


async def handle_kpg_compatibility_question(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    text_value = message.text or message.caption or ""
    if not text_value or not kpg_compatibility_question_intent(text_value):
        return False

    requested = extract_requested_kpg_software(text_value)
    rows = find_kpg_compatibility_rows(text_value)
    if not requested or not rows:
        return False

    usuario = display_name(message)
    by_software: dict[str, list[sqlite3.Row]] = {}

    for row in rows:
        software = str(row["software"] or "").strip()
        by_software.setdefault(software, []).append(row)

    lines = [
        f"📚 {usuario}, según el listado de compatibilidad Kenwood cargado por el administrador:"
    ]

    for software, software_rows in by_software.items():
        models = []
        notes = []

        for row in software_rows:
            model = str(row["model"] or "").strip()
            if model and model not in models:
                models.append(model)

            note = str(row["notes"] or "").strip()
            if note and note not in notes:
                notes.append(note)

        lines.append(f"💻 {software} → 📻 " + ", ".join(models))

        if notes:
            lines.append("📝 Nota del listado: " + "; ".join(notes))

    if len(by_software) > 1:
        lines.append(
            "ℹ️ Como pediste la familia numérica sin sufijo, Pecos incluyó "
            "las variantes alfabéticas documentadas con ese mismo número."
        )

    await context.bot.send_message(
        chat_id=message.chat_id,
        text="\n\n".join(lines),
    )
    db.add_history(
        f"COMPATIBILIDAD KPG->MODELOS | {requested} | "
        f"variantes={len(by_software)} | {usuario}"
    )
    return True


async def handle_radio_software_association(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    text_value = message.text or message.caption or ""
    if not text_value or not radio_software_request_signal(text_value):
        return False

    associations = find_radio_software_associations(text_value)
    if not associations:
        return False

    usuario = display_name(message)

    grouped: dict[tuple[str, str, str], list[sqlite3.Row]] = {}
    for row in associations:
        key = (
            str(row["brand"] or "").strip(),
            str(row["model"] or "").strip(),
            str(row["variant"] or "").strip(),
        )
        grouped.setdefault(key, []).append(row)

    lines = [
        f"🧰 {usuario}, Pecos revisó la tabla de compatibilidad Kenwood cargada por el administrador."
    ]

    for (brand, model, variant), group_rows in grouped.items():
        model_label = " ".join(part for part in (brand, model, variant) if part)

        softwares = []
        notes = []
        for row in group_rows:
            software = str(row["software"] or "").strip()
            if software and software not in softwares:
                softwares.append(software)
            note = str(row["notes"] or "").strip()
            if note and note not in notes:
                notes.append(note)

        if len(softwares) == 1:
            lines.append(f"📻 {model_label} → 💻 {softwares[0]}")
        else:
            lines.append(
                f"📻 {model_label} → 💻 " + ", ".join(softwares)
            )
            lines.append(
                "ℹ️ El listado contiene más de un software asociado; "
                "Pecos no elegirá uno al azar."
            )

        if notes:
            lines.append("📝 Nota del listado: " + "; ".join(notes))

        any_archive = False
        for software in softwares:
            archive_rows = search_archive_rows(message.chat_id, software, limit=3)
            if not archive_rows:
                continue
            any_archive = True
            lines.append(f"📦 {software} encontrado en los archivos:")
            lines.extend(
                archive_result_lines(message.chat, archive_rows, max_items=3)
            )

        if not any_archive:
            lines.append(
                "🌵 La compatibilidad está registrada, pero no encontré en este grupo "
                "un archivo que pueda enlazar con suficiente seguridad."
            )

    await context.bot.send_message(
        chat_id=message.chat_id,
        text="\n\n".join(lines),
    )
    db.add_history(
        f"ASOCIACION RADIO-SOFTWARE KENWOOD | "
        f"consulta={text_value[:180]} | resultados={len(associations)} | {usuario}"
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
    if not pecos_help_invocation_allowed(message.text):
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



AUTONOMOUS_MEMORY_SOURCE_CHAT_ID = HISTORY_SOURCE_CHAT_ID
AUTONOMOUS_MEMORY_MIN_QA_CONFIDENCE = 0.95


def autonomous_memory_enabled() -> bool:
    return db.is_true("autonomous_technical_memory_enabled")


def autonomous_canonical_model(value: str) -> str:
    compact = re.sub(r"[^a-z0-9]", "", normalize_intent(value or ""))
    match = re.fullmatch(r"([a-z]{2,6})(\d{3,5}[a-z]?)", compact)
    if match:
        return f"{match.group(1).upper()}-{match.group(2).upper()}"
    return compact.upper()


def autonomous_extract_model_anchors(text_value: str) -> list[str]:
    found: list[str] = []
    seen: set[str] = set()

    def add(value: str) -> None:
        canonical = autonomous_canonical_model(value)
        if not canonical:
            return
        # KPG es software de programación, no el radio sujeto del hecho.
        if canonical.startswith("KPG-"):
            return
        normalized = technical_term_normalized(canonical)
        if normalized in seen:
            return
        seen.add(normalized)
        found.append(canonical)

    for model in archive_model_terms(text_value):
        add(model)

    parsed = technical_query_interpret(text_value)
    for model in list(parsed.get("models", [])):
        add(str(model))
    for model in list(parsed.get("raw_model_anchors", [])):
        value = str(model)
        if re.search(r"[A-Za-z]", value) and re.search(r"\d", value):
            add(value)

    return found[:8]


def autonomous_extract_variant(text_value: str, model: str) -> str:
    # En Kenwood aparecen variantes como K1/K2/K3. Solo se asocian cuando
    # están explícitamente escritas para no inventar compatibilidades.
    normalized = normalize_intent(text_value or "").upper()
    if model.startswith(("TK-", "NX-", "NXR-", "TKR-", "TM-")):
        match = re.search(r"\bK\s*([1-9])\b", normalized)
        if match:
            return f"K{match.group(1)}"
    return ""


def autonomous_extract_software_tokens(text_value: str) -> list[str]:
    upper = technical_ascii_upper(text_value or "")
    compact = technical_term_normalized(upper)
    found: list[str] = []

    def add(value: str) -> None:
        value = value.strip().upper()
        if value and value not in found:
            found.append(value)

    # Kenwood: KPG-D6, KPG-169D, KPGD6, etc.
    for match in re.finditer(
        r"\bKPG[\s._-]*([A-Z]?\d+[A-Z]?)\b",
        upper,
    ):
        add(f"KPG-{match.group(1)}")

    # Software de familias con nombre inequívoco.
    if "MOTOTRBO" in compact and "CPS" in compact:
        add("MOTOTRBO CPS")
    if "APX" in compact and "CPS" in compact:
        add("APX CPS")

    return found[:6]


def autonomous_answer_has_technical_content(text_value: str) -> bool:
    if autonomous_extract_software_tokens(text_value):
        return True
    if archive_model_terms(text_value):
        return True
    normalized = normalize_intent(text_value or "")
    return any(re.search(pattern, normalized) for pattern in HISTORY_HELP_PATTERNS)


def autonomous_learn_pair_row(row: sqlite3.Row) -> bool:
    status = str(row["status"] or "").upper()
    if status not in {"CONFIRMED", "ACKNOWLEDGED"}:
        return False

    question_text = str(row["question_text"] or "").strip()
    answer_text = str(row["answer_text"] or "").strip()
    if not question_text or not answer_text:
        return False

    # Evita que una persona se enseñe a sí misma como evidencia autónoma.
    question_sender = int(row["question_sender_id"] or 0)
    answer_sender = int(row["answer_sender_id"] or 0)
    if question_sender and answer_sender and question_sender == answer_sender:
        return False

    anchors = autonomous_extract_model_anchors(question_text)
    if not anchors:
        return False

    # Una respuesta demasiado corta y sin señal técnica no se memoriza.
    if len(answer_text) < 8 and not autonomous_answer_has_technical_content(answer_text):
        return False

    confidence = float(row["confidence"] or 0.0)
    if status == "CONFIRMED":
        confidence = max(confidence, 0.99)
    else:
        confidence = max(confidence, 0.75)

    question_id = int(row["question_message_id"] or 0)
    answer_id = int(row["answer_message_id"] or 0)
    confirmation_id = int(row["confirmation_message_id"] or 0)

    # Keywords del problema, sin depender de un LLM externo.
    keywords = history_extract_search_terms(question_text)

    db.upsert_autonomous_qa(
        AUTONOMOUS_MEMORY_SOURCE_CHAT_ID,
        question_id,
        answer_id,
        confirmation_id,
        question_text,
        answer_text,
        str(row["question_link"] or ""),
        str(row["answer_link"] or ""),
        anchors,
        keywords,
        status,
        confidence,
        "GROUP_QA_AUTONOMOUS",
    )

    # Hecho estructurado modelo -> software.
    # Se aprende automáticamente solo cuando hay UN modelo inequívoco y el
    # software aparece explícitamente en la RESPUESTA.
    softwares = autonomous_extract_software_tokens(answer_text)
    if len(anchors) == 1 and softwares:
        model = anchors[0]
        variant = autonomous_extract_variant(question_text, model)

        for software in softwares:
            db.upsert_autonomous_fact_evidence(
                AUTONOMOUS_MEMORY_SOURCE_CHAT_ID,
                "SOFTWARE_FOR_MODEL",
                model,
                variant,
                software,
                question_id,
                answer_id,
                confirmation_id,
                status,
                confidence,
                "GROUP_QA_AUTONOMOUS",
            )

    return True


def sync_autonomous_technical_memory(chat_id: int) -> dict[str, int]:
    processed = 0
    learned = 0
    for row in db.confirmed_or_ack_pairs_for_autonomous_sync(chat_id):
        processed += 1
        if autonomous_learn_pair_row(row):
            learned += 1

    stats = db.autonomous_memory_stats(chat_id)
    return {
        "processed": processed,
        "learned": learned,
        **stats,
    }


def autonomous_memory_query_terms(text_value: str) -> set[str]:
    anchors = {
        technical_term_normalized(value)
        for value in autonomous_extract_model_anchors(text_value)
    }
    terms = set(history_extract_search_terms(text_value))
    return {
        term
        for term in terms
        if technical_term_normalized(term) not in anchors
    }


def autonomous_find_confirmed_qa(text_value: str) -> sqlite3.Row | None:
    query_anchors = autonomous_extract_model_anchors(text_value)
    if not query_anchors:
        # Por seguridad, la recuperación autónoma de una solución libre exige
        # al menos un modelo concreto.
        return None

    query_anchor_norms = {
        technical_term_normalized(value)
        for value in query_anchors
    }
    query_terms = autonomous_memory_query_terms(text_value)
    if not query_terms:
        # "Pecos DGP8550e" por sí solo no es suficiente para elegir una
        # solución histórica a un problema que el usuario no describió.
        return None

    ranked: list[tuple[float, sqlite3.Row]] = []

    for row in db.list_autonomous_qa(
        AUTONOMOUS_MEMORY_SOURCE_CHAT_ID,
        ("CONFIRMED",),
    ):
        confidence = float(row["confidence"] or 0.0)
        if confidence < AUTONOMOUS_MEMORY_MIN_QA_CONFIDENCE:
            continue

        row_anchors = {
            technical_term_normalized(value)
            for value in str(row["model_anchors"] or "").split("|")
            if value.strip()
        }
        if not (query_anchor_norms & row_anchors):
            continue

        row_terms = {
            value.strip()
            for value in str(row["keywords"] or "").split("|")
            if value.strip()
        }
        overlap = query_terms & row_terms
        if not overlap:
            continue

        score = 100.0 + (len(overlap) * 15.0) + (confidence * 10.0)
        ranked.append((score, row))

    if not ranked:
        return None

    ranked.sort(
        key=lambda item: (
            item[0],
            float(item[1]["confidence"] or 0.0),
            int(item[1]["question_message_id"] or 0),
        ),
        reverse=True,
    )

    # Si dos recuerdos distintos quedan prácticamente empatados, Pecos no
    # elige arbitrariamente.
    if len(ranked) > 1 and abs(ranked[0][0] - ranked[1][0]) < 5.0:
        first_answer = normalize_intent(str(ranked[0][1]["answer_text"] or ""))
        second_answer = normalize_intent(str(ranked[1][1]["answer_text"] or ""))
        if first_answer != second_answer:
            return None

    return ranked[0][1]


def autonomous_software_memory_for_query(
    text_value: str,
) -> tuple[str, str, list[sqlite3.Row]] | None:
    if not radio_software_request_signal(text_value):
        return None

    models = autonomous_extract_model_anchors(text_value)
    if len(models) != 1:
        return None

    model = models[0]
    variant = autonomous_extract_variant(text_value, model)
    rows = db.grouped_autonomous_facts(
        AUTONOMOUS_MEMORY_SOURCE_CHAT_ID,
        "SOFTWARE_FOR_MODEL",
        model,
        variant,
    )
    if not rows:
        return None

    trusted: list[sqlite3.Row] = []
    for row in rows:
        confirmed = int(row["confirmed_count"] or 0)
        acknowledged = int(row["acknowledged_count"] or 0)
        # Regla de confianza:
        # - una confirmación explícita del autor original basta, o
        # - dos conversaciones ACKNOWLEDGED independientes forman consenso.
        if confirmed >= 1 or acknowledged >= 2:
            trusted.append(row)

    if not trusted:
        return None

    # Si la memoria confiable contiene más de un software distinto para el
    # mismo modelo/variante, no se decide automáticamente.
    distinct_values = {
        str(row["fact_value"] or "").strip().upper()
        for row in trusted
        if str(row["fact_value"] or "").strip()
    }
    if len(distinct_values) != 1:
        return model, variant, trusted

    return model, variant, trusted


async def handle_autonomous_technical_memory(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    if not autonomous_memory_enabled():
        return False

    text_value = (message.text or message.caption or "").strip()
    if not text_value:
        return False

    # 1) Memoria estructurada modelo -> software.
    structured = autonomous_software_memory_for_query(text_value)
    if structured:
        model, variant, rows = structured
        usuario = display_name(message)

        values = {
            str(row["fact_value"] or "").strip().upper()
            for row in rows
            if str(row["fact_value"] or "").strip()
        }

        if len(values) != 1:
            await context.bot.send_message(
                chat_id=message.chat_id,
                text=(
                    f"🧠 {usuario}, Pecos encontró recuerdos técnicos confiables "
                    f"pero contradictorios para {model}"
                    f"{(' ' + variant) if variant else ''}. "
                    "No voy a elegir un software al azar; esto necesita revisión."
                ),
            )
            return True

        software = next(iter(values))
        best = rows[0]
        confirmed = int(best["confirmed_count"] or 0)
        acknowledged = int(best["acknowledged_count"] or 0)

        if confirmed >= 1:
            basis = "una solución confirmada por el usuario que hizo la consulta"
        else:
            basis = "dos o más conversaciones coincidentes del grupo"

        lines = [
            f"🧠 {usuario}, Pecos aprendió esto de la memoria técnica del grupo:",
            f"📻 {model}{(' ' + variant) if variant else ''} → 💻 {software}",
            f"✅ Base: {basis}.",
        ]

        # Intenta ubicar el software en el archivo REAL del grupo fuente.
        archive_rows = search_archive_rows(
            AUTONOMOUS_MEMORY_SOURCE_CHAT_ID,
            software,
            limit=3,
        )
        if archive_rows:
            lines.append("📦 También encontré el software en los archivos:")
            source_chat = message.chat
            if message.chat_id != AUTONOMOUS_MEMORY_SOURCE_CHAT_ID:
                # El enlace se genera con el chat fuente histórico.
                class _SourceChat:
                    id = AUTONOMOUS_MEMORY_SOURCE_CHAT_ID
                    username = None
                source_chat = _SourceChat()
            lines.extend(archive_result_lines(source_chat, archive_rows, max_items=3))

        qid = int(best["question_message_id"] or 0)
        aid = int(best["answer_message_id"] or 0)
        qrow = db.get_conversation_message(AUTONOMOUS_MEMORY_SOURCE_CHAT_ID, qid)
        arow = db.get_conversation_message(AUTONOMOUS_MEMORY_SOURCE_CHAT_ID, aid)
        if qrow and str(qrow["message_link"] or ""):
            lines.append(f"🔗 Caso original: {qrow['message_link']}")
        if arow and str(arow["message_link"] or ""):
            lines.append(f"🔗 Respuesta: {arow['message_link']}")

        await context.bot.send_message(
            chat_id=message.chat_id,
            text="\n".join(lines),
        )
        db.add_history(
            f"MEMORIA AUTONOMA SOFTWARE | {model} {variant} -> {software} | "
            f"consulta={message.message_id} | usuario={usuario}"
        )
        return True

    # 2) Solución técnica libre, pero SOLO si el caso histórico está CONFIRMED.
    if not (
        text_mentions_pecos(text_value)
        or looks_like_question(text_value)
        or radio_software_request_signal(text_value)
        or any(re.search(p, normalize_intent(text_value)) for p in HISTORY_REQUEST_PATTERNS)
    ):
        return False

    row = autonomous_find_confirmed_qa(text_value)
    if row is None:
        return False

    usuario = display_name(message)
    answer_text = " ".join(str(row["answer_text"] or "").split())
    if len(answer_text) > 700:
        answer_text = answer_text[:697] + "..."

    lines = [
        f"🧠 {usuario}, Pecos recuerda un caso confirmado del grupo que coincide con tu consulta.",
        f"💡 Solución que quedó confirmada: {answer_text}",
    ]
    if str(row["question_link"] or ""):
        lines.append(f"🔗 Consulta original: {row['question_link']}")
    if str(row["answer_link"] or ""):
        lines.append(f"🔗 Respuesta original: {row['answer_link']}")

    await context.bot.send_message(
        chat_id=message.chat_id,
        text="\n".join(lines),
    )
    db.add_history(
        f"MEMORIA AUTONOMA QA | origen={row['question_message_id']}/{row['answer_message_id']} "
        f"| consulta={message.message_id} | usuario={usuario}"
    )
    return True


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

                # La memoria técnica autónoma aprende inmediatamente cuando el
                # autor original confirma o agradece una respuesta. Las
                # respuestas ACKNOWLEDGED se guardan como evidencia, pero solo
                # dos coincidentes pueden formar consenso automático.
                if autonomous_memory_enabled():
                    refreshed_pair = None
                    for candidate in db.confirmed_or_ack_pairs_for_autonomous_sync(
                        message.chat_id
                    ):
                        if (
                            int(candidate["question_message_id"] or 0)
                            == int(pair["question_message_id"])
                            and int(candidate["answer_message_id"] or 0)
                            == int(pair["answer_message_id"])
                        ):
                            refreshed_pair = candidate
                            break
                    if refreshed_pair is not None:
                        autonomous_learn_pair_row(refreshed_pair)

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


def admin_activity_summary(
    entries: list[dict[str, object]],
) -> dict[str, int]:
    buckets = {
        "ACTIVO": 0,
        "POCO ACTIVO": 0,
        "INACTIVO": 0,
        "MUY INACTIVO": 0,
    }

    for entry in entries:
        last_seen = (
            entry.get("last_seen")
            if isinstance(entry.get("last_seen"), datetime)
            else None
        )
        _, state = activity_status(last_seen)
        buckets[state] += 1

    return buckets


def admin_group_message_link(chat_id: int, message_id: int) -> str | None:
    """Enlace directo usando solo chat_id; útil desde el panel privado."""
    chat_id_text = str(int(chat_id))
    if chat_id_text.startswith("-100"):
        internal_id = chat_id_text[4:]
        if internal_id:
            return f"https://t.me/c/{internal_id}/{int(message_id)}"
    return None


def admin_archive_search_text(
    query_text: str,
    rows: list[sqlite3.Row],
) -> str:
    terms = extract_archive_terms(query_text)
    normalized_query = " ".join(terms) if terms else query_text.strip()

    if not rows:
        return (
            "🌵 Pecos no encontró un archivo que cumpla suficientemente con "
            f"«{normalized_query}» en {db.known_group_title(HISTORY_SOURCE_CHAT_ID)}.\n\n"
            "Prefiero no mostrar coincidencias parciales que puedan pertenecer "
            "a otro modelo, marca o plataforma."
        )

    lines = [
        f"📦 Búsqueda administrativa: «{normalized_query}»",
        f"Grupo fuente: {db.known_group_title(HISTORY_SOURCE_CHAT_ID)}",
        "",
    ]

    for index, row in enumerate(rows[:8], start=1):
        file_name = str(row["file_name"] or "archivo")
        file_size = human_file_size(int(row["file_size"] or 0))
        sender = str(row["sender_name"] or "usuario desconocido")
        link = admin_group_message_link(
            HISTORY_SOURCE_CHAT_ID,
            int(row["message_id"]),
        )

        lines.append(
            f"{index}. 📦 {file_name} · {file_size} · {sender}"
        )
        if link:
            lines.append(f"   🔗 {link}")
        lines.append("")

    return "\n".join(lines).rstrip()


def inactive_admin_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("30 días", callback_data="admininactive:30"),
                InlineKeyboardButton("60 días", callback_data="admininactive:60"),
            ],
            [
                InlineKeyboardButton("90 días", callback_data="admininactive:90"),
                InlineKeyboardButton("180 días", callback_data="admininactive:180"),
            ],
            [InlineKeyboardButton("365 días", callback_data="admininactive:365")],
            [InlineKeyboardButton("⬅️ Volver", callback_data="menu:main")],
        ]
    )


def main_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("📝 Palabras restringidas", callback_data="menu:words")],
            [InlineKeyboardButton("🕘 Mensaje diario", callback_data="menu:daily")],
            [InlineKeyboardButton("💬 Preguntas y respuestas", callback_data="menu:qa")],
            [
                InlineKeyboardButton("📊 Ver estado", callback_data="menu:status"),
                InlineKeyboardButton("📜 Historial", callback_data="menu:history"),
            ],
            [
                InlineKeyboardButton("👥 Actividad miembros", callback_data="admin:activity"),
                InlineKeyboardButton("💤 Inactivos", callback_data="admin:inactive"),
            ],
            [
                InlineKeyboardButton(
                    "🧹 Limpieza bloque 786–1595",
                    callback_data="admin:cleanup_inactive",
                )
            ],
            [
                InlineKeyboardButton("📦 Buscar archivos", callback_data="admin:search"),
                InlineKeyboardButton("🧠 Memoria Pecos", callback_data="admin:memory"),
            ],
            [
                InlineKeyboardButton("ℹ️ Información Pecos", callback_data="admin:info"),
                InlineKeyboardButton("❓ Ayuda Admin", callback_data="admin:help"),
            ],
            [
                InlineKeyboardButton("🎭 Bromas y humor", callback_data="menu:humor"),
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


def qa_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("📋 Ver respuestas", callback_data="qa:list"),
                InlineKeyboardButton("➕ Agregar", callback_data="qa:add"),
            ],
            [
                InlineKeyboardButton("✏️ Editar por ID", callback_data="qa:edit"),
                InlineKeyboardButton("➖ Eliminar por ID", callback_data="qa:remove"),
            ],
            [InlineKeyboardButton("⬅️ Volver", callback_data="menu:main")],
        ]
    )


def build_daily_panel_text() -> str:
    daily_time = db.get_setting("daily_time", "09:00")
    daily_pool = get_humor_pool("daily")

    return (
        "🕘 Mensaje diario\n\n"
        "Estado: ✅ SIEMPRE ACTIVO\n"
        f"Hora: {daily_time}\n"
        f"Zona: {TIMEZONE_NAME}\n"
        "Modo: 🎲 Saludo aleatorio de Pecos\n\n"
        f"Cada día Pecos elegirá al azar 1 de {len(daily_pool)} saludos "
        "del repertorio configurado.\n\n"
        "ℹ️ El mensaje diario no se puede desactivar desde el panel.\n"
        "ℹ️ El antiguo texto fijo ya no se utiliza."
    )


def daily_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("🕒 Cambiar hora", callback_data="daily:time"),
                InlineKeyboardButton("✏️ Editar saludos", callback_data="humor:list:daily"),
            ],
            [InlineKeyboardButton("👁️ Ver configuración", callback_data="daily:view")],
            [InlineKeyboardButton("⬅️ Volver", callback_data="menu:main")],
        ]
    )


def humor_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("🤖 XeraX — mención", callback_data="humor:list:xerax_manual"),
                InlineKeyboardButton("⏱️ XeraX — auto", callback_data="humor:list:xerax_auto"),
            ],
            [
                InlineKeyboardButton("🤠 Consejos", callback_data="humor:list:advice"),
                InlineKeyboardButton("💬 Frases", callback_data="humor:list:phrase"),
            ],
            [
                InlineKeyboardButton("🌵 Excusas", callback_data="humor:list:excuse"),
                InlineKeyboardButton("🔮 Pronósticos", callback_data="humor:list:forecast"),
            ],
            [
                InlineKeyboardButton("⚔️ Duelo Pecos", callback_data="humor:list:duel"),
                InlineKeyboardButton("📻 VHF ↔ UHF", callback_data="humor:list:band"),
            ],
            [
                InlineKeyboardButton("🕘 Saludos diarios", callback_data="humor:list:daily"),
                InlineKeyboardButton("🌵 Silencio", callback_data="humor:list:silence"),
            ],
            [
                InlineKeyboardButton("🤷 No sé / fuera de alcance", callback_data="humor:list:unknown"),
                InlineKeyboardButton("🛠️ Correcciones", callback_data="humor:list:correction"),
            ],
            [InlineKeyboardButton("🎭 Bromas internas", callback_data="menu:jokes")],
            [InlineKeyboardButton("⬅️ Volver", callback_data="menu:main")],
        ]
    )


def humor_pool_menu(pool_key: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("📋 Ver listado", callback_data=f"humor:list:{pool_key}")],
            [
                InlineKeyboardButton("🧪 Probar una", callback_data=f"humor:test:{pool_key}"),
                InlineKeyboardButton("✏️ Editar por Nº", callback_data=f"humor:edit:{pool_key}"),
            ],
            [
                InlineKeyboardButton("➕ Agregar", callback_data=f"humor:add:{pool_key}"),
                InlineKeyboardButton("➖ Eliminar por Nº", callback_data=f"humor:remove:{pool_key}"),
            ],
            [InlineKeyboardButton("♻️ Restaurar originales", callback_data=f"humor:reset:{pool_key}")],
            [InlineKeyboardButton("⬅️ Volver a humor", callback_data="menu:humor")],
        ]
    )


def jokes_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("📋 Ver bromas", callback_data="jokes:list"),
                InlineKeyboardButton("➕ Agregar", callback_data="jokes:add"),
            ],
            [
                InlineKeyboardButton("✏️ Editar por ID", callback_data="jokes:edit"),
                InlineKeyboardButton("➖ Eliminar por ID", callback_data="jokes:remove"),
            ],
            [InlineKeyboardButton("⬅️ Volver a humor", callback_data="menu:humor")],
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



def inactive_cleanup_date_in_range(last_seen: object) -> bool:
    """Compatibilidad: ya no define el bloque 786–1595 de la versión 2.8.58."""
    if not isinstance(last_seen, datetime):
        return False
    local_dt = (
        last_seen.astimezone(BOT_TZ)
        if last_seen.tzinfo
        else last_seen.replace(tzinfo=BOT_TZ)
    )
    observed_date = local_dt.date()
    return INACTIVE_CLEANUP_START_DATE <= observed_date <= INACTIVE_CLEANUP_END_DATE


def validate_cleanup_block_targets() -> None:
    indexes = [idx for idx, _uid, _name in CLEANUP_BLOCK_TARGETS]
    user_ids = [uid for _idx, uid, _name in CLEANUP_BLOCK_TARGETS]

    if len(CLEANUP_BLOCK_TARGETS) != CLEANUP_BLOCK_EXPECTED_COUNT:
        raise RuntimeError(
            f"Bloque de limpieza inválido: esperaba {CLEANUP_BLOCK_EXPECTED_COUNT} "
            f"usuarios y hay {len(CLEANUP_BLOCK_TARGETS)}."
        )
    if len(set(indexes)) != CLEANUP_BLOCK_EXPECTED_COUNT:
        raise RuntimeError("Bloque de limpieza inválido: hay números de fila repetidos.")
    if len(set(user_ids)) != CLEANUP_BLOCK_EXPECTED_COUNT:
        raise RuntimeError("Bloque de limpieza inválido: hay User ID repetidos.")
    if min(indexes) != CLEANUP_BLOCK_FIRST_INDEX or max(indexes) != CLEANUP_BLOCK_LAST_INDEX:
        raise RuntimeError("Bloque de limpieza inválido: rango de filas inesperado.")

    digest = hashlib.sha256(
        ",".join(str(uid) for uid in user_ids).encode("utf-8")
    ).hexdigest()
    if digest != CLEANUP_BLOCK_TARGET_SHA256:
        raise RuntimeError("Bloque de limpieza inválido: la huella SHA-256 de User ID cambió.")


def cleanup_block_candidates() -> list[dict[str, object]]:
    """Construye exactamente los 810 candidatos por User ID.

    La actividad histórica se adjunta solo como información. Un candidato sin
    last_seen sigue siendo candidato porque la selección de esta versión es el
    bloque explícito 786–1595, no un filtro por fecha.
    """
    validate_cleanup_block_targets()

    activity_by_id = {
        int(entry.get("user_id") or 0): entry
        for entry in build_member_activity_snapshot(HISTORY_SOURCE_CHAT_ID)
        if int(entry.get("user_id") or 0) > 0
    }

    candidates: list[dict[str, object]] = []
    for source_index, user_id, source_name in CLEANUP_BLOCK_TARGETS:
        item = dict(activity_by_id.get(user_id) or {})
        item["user_id"] = int(user_id)
        item.setdefault("username", "")
        item.setdefault("display_name", source_name)
        item.setdefault("first_seen", None)
        item.setdefault("last_seen", None)
        item.setdefault("message_count", 0)
        item.setdefault("messages_30d", 0)
        item["cleanup_source_index"] = int(source_index)
        item["cleanup_source_name"] = source_name
        candidates.append(item)

    return candidates


def inactive_cleanup_historical_candidates() -> list[dict[str, object]]:
    """Alias conservado para compatibilidad interna."""
    return cleanup_block_candidates()

def mtproto_cleanup_configuration_error() -> str:
    if not TELETHON_AVAILABLE:
        return (
            "Falta Telethon. Agrega «Telethon==1.45.0» a requirements.txt "
            "y vuelve a desplegar."
        )
    if TELEGRAM_API_ID <= 0:
        return "Falta TELEGRAM_API_ID en Railway."
    if not TELEGRAM_API_HASH:
        return "Falta TELEGRAM_API_HASH en Railway."
    if not BOT_TOKEN:
        return "Falta BOT_TOKEN."
    return ""


async def get_mtproto_client():
    global MTPROTO_CLIENT

    error = mtproto_cleanup_configuration_error()
    if error:
        raise RuntimeError(error)

    async with MTPROTO_CONNECT_LOCK:
        client = MTPROTO_CLIENT

        if client is None:
            client = TelegramClient(
                MTPROTO_SESSION_BASENAME,
                TELEGRAM_API_ID,
                TELEGRAM_API_HASH,
            )
            MTPROTO_CLIENT = client

        if not client.is_connected():
            await client.connect()

        if not await client.is_user_authorized():
            await client.start(bot_token=BOT_TOKEN)

        me = await client.get_me()
        log.info(
            "MTProto conectado | cuenta=@%s | bot=%s",
            getattr(me, "username", "") or "",
            bool(getattr(me, "bot", False)),
        )
        return client


async def resolve_mtproto_group_entity(client, chat_id: int):
    """Resuelve un supergrupo desde su Bot API chat_id sin usar GetDialogs.

    Telegram restringe messages.getDialogs para cuentas bot. Telethon, en
    cambio, contempla el caso de bots y puede resolver un PeerChannel conocido
    mediante channels.getChannels con access_hash=0 cuando el bot ya pertenece
    al canal/supergrupo.
    """
    if types is None or utils is None:
        raise RuntimeError("Telethon no está disponible.")

    raw_id, peer_cls = utils.resolve_id(int(chat_id))
    if peer_cls is not types.PeerChannel:
        raise RuntimeError(
            f"El chat {chat_id} no corresponde a un supergrupo/canal MTProto."
        )

    # get_input_entity(PeerChannel) usa la ruta especial de Telethon para bots:
    # channels.GetChannelsRequest(InputChannel(channel_id, access_hash=0)).
    # No llama a GetDialogsRequest.
    return await client.get_input_entity(types.PeerChannel(raw_id))


def mtproto_user_display(user) -> str:
    username = str(getattr(user, "username", "") or "").strip()
    first_name = str(getattr(user, "first_name", "") or "").strip()
    last_name = str(getattr(user, "last_name", "") or "").strip()
    full = " ".join(part for part in (first_name, last_name) if part).strip()

    if username and full:
        return f"{full} (@{username})"
    if username:
        return f"@{username}"
    if full:
        return full
    return f"ID {int(getattr(user, 'id', 0) or 0)}"


def current_member_is_admin(user) -> bool:
    participant = getattr(user, "participant", None)
    participant_type = type(participant).__name__
    return participant_type in {
        "ChannelParticipantAdmin",
        "ChannelParticipantCreator",
        "ChatParticipantAdmin",
        "ChatParticipantCreator",
    }


def mtproto_member_snapshot_row(user) -> dict[str, object]:
    username = str(getattr(user, "username", "") or "").strip().lstrip("@")
    first_name = str(getattr(user, "first_name", "") or "").strip()
    last_name = str(getattr(user, "last_name", "") or "").strip()
    display_name = " ".join(
        part for part in (first_name, last_name) if part
    ).strip()

    return {
        "user_id": int(getattr(user, "id", 0) or 0),
        "username": username,
        "display_name": display_name,
        "is_bot": bool(getattr(user, "bot", False)),
        "is_admin": current_member_is_admin(user),
    }


async def scan_current_group_members_mtproto(
    chat_id: int,
) -> tuple[object, object, dict[int, object], list[dict[str, object]]]:
    """Obtiene el padrón actual completo y lo persiste sin alterar actividad."""
    client = await get_mtproto_client()
    group_entity = await resolve_mtproto_group_entity(client, chat_id)
    participants = await client.get_participants(group_entity, limit=None)

    current_members = {
        int(user.id): user
        for user in participants
        if int(getattr(user, "id", 0) or 0) > 0
    }

    restored = db.restore_rejoined_users(chat_id, set(current_members))
    if restored:
        log.info(
            "Padrón MTProto: %s usuario(s) depurado(s) reingresaron y fueron restaurados",
            restored,
        )

    snapshot = [
        mtproto_member_snapshot_row(user)
        for user in current_members.values()
    ]
    db.replace_current_member_snapshot(chat_id, snapshot)

    log.info(
        "Padrón MTProto actualizado | chat=%s | miembros=%s",
        chat_id,
        len(current_members),
    )

    return client, group_entity, current_members, snapshot


async def build_inactive_cleanup_plan() -> dict[str, object]:
    """Construye el plan del bloque 786–1595 SIN expulsar a nadie."""
    try:
        client, group_entity, current_members, _snapshot = (
            await scan_current_group_members_mtproto(HISTORY_SOURCE_CHAT_ID)
        )
    except Exception as exc:
        raise RuntimeError(
            "No pude obtener el padrón actual del supergrupo por MTProto. "
            f"Detalle: {exc}"
        ) from exc

    # Se construye DESPUÉS del escaneo MTProto. Así, si algún usuario
    # anteriormente retirado volvió a ingresar, restore_rejoined_users() ya
    # habrá reactivado su perfil antes de consultar su actividad histórica.
    candidates = cleanup_block_candidates()

    me = await client.get_me()
    my_permissions = await client.get_permissions(group_entity, me)

    if not my_permissions or not my_permissions.is_admin:
        raise RuntimeError("Pecos no figura como administrador MTProto del grupo.")
    if not my_permissions.ban_users:
        raise RuntimeError(
            "Pecos no tiene permiso «Ban users / Bloquear usuarios»."
        )

    protected_ids = set(ADMIN_USER_IDS) | set(OWNER_USER_IDS)
    if int(getattr(me, "id", 0) or 0) > 0:
        protected_ids.add(int(me.id))

    eligible: list[tuple[dict[str, object], object]] = []
    already_out: list[dict[str, object]] = []
    admins: list[dict[str, object]] = []
    bots: list[dict[str, object]] = []
    protected: list[dict[str, object]] = []

    for entry in candidates:
        user_id = int(entry.get("user_id") or 0)
        if user_id <= 0:
            continue

        if user_id in protected_ids:
            protected.append(entry)
            continue

        user = current_members.get(user_id)
        if user is None:
            # El escaneo actual devolvió el padrón completo; este ID no forma
            # parte del padrón actual observado.
            already_out.append(entry)
            continue

        if bool(getattr(user, "bot", False)):
            bots.append(entry)
            continue

        if current_member_is_admin(user):
            admins.append(entry)
            continue

        eligible.append((entry, user))

    return {
        "client": client,
        "group_entity": group_entity,
        "group_title": db.known_group_title(HISTORY_SOURCE_CHAT_ID),
        "candidates": candidates,
        "scanned_members": len(current_members),
        "eligible": eligible,
        "not_visible": already_out,
        "already_out": already_out,
        "admins": admins,
        "bots": bots,
        "protected": protected,
        "target_first_index": CLEANUP_BLOCK_FIRST_INDEX,
        "target_last_index": CLEANUP_BLOCK_LAST_INDEX,
        "target_expected_count": CLEANUP_BLOCK_EXPECTED_COUNT,
        "target_sha256": CLEANUP_BLOCK_TARGET_SHA256,
    }


def build_inactive_cleanup_plan_report(plan: dict[str, object]) -> str:
    group_title = str(plan.get("group_title") or HISTORY_SOURCE_CHAT_ID)
    candidates = list(plan.get("candidates") or [])
    eligible = list(plan.get("eligible") or [])
    not_visible = list(plan.get("not_visible") or [])
    admins = list(plan.get("admins") or [])
    bots = list(plan.get("bots") or [])
    protected = list(plan.get("protected") or [])

    current_count = int(plan.get("scanned_members") or 0)
    projected_count = max(0, current_count - len(eligible))

    lines = [
        "PECOS PAUL KELE - SIMULACIÓN BLOQUE 786–1595",
        f"Grupo: {group_title}",
        f"Generado: {datetime.now(BOT_TZ).strftime('%d/%m/%Y %H:%M')} ({TIMEZONE_NAME})",
        "",
        "OBJETIVO FIJO POR USER ID:",
        f"Filas fuente: {CLEANUP_BLOCK_FIRST_INDEX} -> {CLEANUP_BLOCK_LAST_INDEX}",
        f"User ID configurados: {len(candidates)}",
        f"SHA-256 lista ordenada: {CLEANUP_BLOCK_TARGET_SHA256}",
        "",
        f"Miembros actuales en escaneo MTProto: {current_count}",
        f"Elegibles reales para expulsión: {len(eligible)}",
        f"Ya fuera del padrón actual: {len(not_visible)}",
        f"Administradores/creador protegidos: {len(admins)}",
        f"Bots excluidos: {len(bots)}",
        f"IDs protegidos de Pecos/propietarios: {len(protected)}",
        f"Miembros proyectados después de expulsiones exitosas: {projected_count}",
        "",
        "IMPORTANTE:",
        "- ESTA SIMULACIÓN NO EXPULSA A NADIE.",
        "- La selección se hace EXCLUSIVAMENTE por Telegram User ID.",
        "- El nombre, apodo y @username NO se usan para decidir la expulsión.",
        "- Antes de cada expulsión Pecos revalida privilegios del User ID.",
        "- Administradores, creador, bots e IDs protegidos se omiten.",
        "- La expulsión usa MTProto/Telethon kick_participant (ban + unban).",
        "- Pecos NO llama a deleteParticipantHistory ni a métodos de borrado.",
        "- Los mensajes históricos, archivos, fingerprints y memoria técnica se conservan.",
        "- Los expulsados correctamente se retiran del padrón estadístico de Pecos.",
        "- Si un User ID del bloque ya salió, solo se depura del padrón estadístico.",
        "",
        "ELEGIBLES PARA EXPULSAR:",
    ]

    if not eligible:
        lines.append("(ninguno)")
    else:
        for index, item in enumerate(eligible, start=1):
            entry, user = item
            lines.append(
                f"{index}. fila #{int(entry.get('cleanup_source_index') or 0)} | "
                f"{mtproto_user_display(user)} | "
                f"User ID: {int(entry.get('user_id') or 0)} | "
                f"Última actividad: {format_activity_timestamp(entry.get('last_seen'))} | "
                f"Mensajes históricos: {int(entry.get('message_count') or 0)}"
            )

    lines += ["", "YA FUERA DEL GRUPO — SOLO DEPURACIÓN DEL PADRÓN PECOS:"]
    if not not_visible:
        lines.append("(ninguno)")
    else:
        for index, entry in enumerate(not_visible, start=1):
            lines.append(
                f"{index}. fila #{int(entry.get('cleanup_source_index') or 0)} | "
                f"{activity_person_label(entry)} | "
                f"User ID: {int(entry.get('user_id') or 0)} | "
                f"Última actividad: {format_activity_timestamp(entry.get('last_seen'))}"
            )

    return "\n".join(lines)

def inactive_cleanup_confirmation_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton(
                    "⚠️ EXPULSAR BLOQUE 786–1595",
                    callback_data="cleanup:confirm",
                )
            ],
            [
                InlineKeyboardButton(
                    "🔄 Volver a simular",
                    callback_data="cleanup:refresh",
                ),
                InlineKeyboardButton(
                    "❌ Cancelar",
                    callback_data="cleanup:cancel",
                ),
            ],
        ]
    )


async def send_inactive_cleanup_simulation(
    chat_id: int,
    admin_user_id: int,
    context: ContextTypes.DEFAULT_TYPE,
) -> None:
    error = mtproto_cleanup_configuration_error()
    if error:
        await context.bot.send_message(
            chat_id=chat_id,
            text=(
                "🧹 Limpieza del bloque 786–1595 no disponible.\n\n"
                f"{error}\n\n"
                "El resto de Pecos continúa funcionando normalmente."
            ),
        )
        return

    status = await context.bot.send_message(
        chat_id=chat_id,
        text=(
            "🔎 Pecos está construyendo la simulación.\n"
            "No se expulsará a nadie en este paso."
        ),
    )

    try:
        plan = await build_inactive_cleanup_plan()
    except Exception as exc:
        log.exception("No se pudo simular limpieza del bloque 786–1595")
        with contextlib.suppress(TelegramError):
            await status.edit_text(f"❌ No pude construir la simulación:\n{exc}")
        return

    PENDING_INACTIVE_CLEANUP[admin_user_id] = (
        time.monotonic() + INACTIVE_CLEANUP_CONFIRM_TTL_SECONDS
    )

    report = build_inactive_cleanup_plan_report(plan)
    payload = io.BytesIO(report.encode("utf-8-sig"))
    payload.name = (
        "pecos_simulacion_bloque_786_1595_"
        + datetime.now(BOT_TZ).strftime("%Y-%m-%d_%H%M")
        + ".txt"
    )

    candidate_count = len(plan.get("candidates") or [])
    eligible_count = len(plan.get("eligible") or [])
    already_out_count = len(plan.get("already_out") or [])

    with contextlib.suppress(TelegramError):
        await status.edit_text(
            "✅ Simulación terminada. Revisa el archivo antes de confirmar."
        )

    await context.bot.send_document(
        chat_id=chat_id,
        document=payload,
        caption=(
            "🧹 SIMULACIÓN — bloque 786–1595\n\n"
            f"User ID objetivo configurados: {candidate_count}\n"
            f"Elegibles actuales para expulsión: {eligible_count}\n"
            f"Ya fuera del grupo para depurar del padrón: {already_out_count}\n"
            f"Miembros actuales escaneados: {int(plan.get('scanned_members') or 0)}\n"
            f"Proyección tras expulsiones: "
            f"{max(0, int(plan.get('scanned_members') or 0) - eligible_count)}\n\n"
            "✅ Mensajes históricos: SE CONSERVAN\n"
            "🆔 Selección y expulsión exclusivamente por User ID.\n"
            "⚠️ La confirmación vence en 10 minutos."
        ),
        reply_markup=inactive_cleanup_confirmation_menu(),
    )


async def execute_inactive_cleanup(
    chat_id: int,
    admin_user_id: int,
    context: ContextTypes.DEFAULT_TYPE,
) -> None:
    async with INACTIVE_CLEANUP_LOCK:
        progress = await context.bot.send_message(
            chat_id=chat_id,
            text=(
                "🧹 Pecos está revalidando el grupo antes de expulsar.\n"
                "Los mensajes históricos NO serán eliminados."
            ),
        )

        try:
            plan = await build_inactive_cleanup_plan()
        except Exception as exc:
            log.exception("No se pudo revalidar limpieza del bloque 786–1595")
            with contextlib.suppress(TelegramError):
                await progress.edit_text(f"❌ No pude revalidar la limpieza:\n{exc}")
            return

        client = plan["client"]
        group_entity = plan["group_entity"]
        eligible = list(plan.get("eligible") or [])
        already_out = list(plan.get("already_out") or [])

        expelled: list[tuple[dict[str, object], object]] = []
        skipped_admin: list[tuple[dict[str, object], object]] = []
        failed: list[tuple[dict[str, object], object, str]] = []

        for position, item in enumerate(eligible, start=1):
            entry, user = item
            user_id = int(entry.get("user_id") or 0)

            try:
                # Revalidación individual antes de cada expulsión.
                permissions = await client.get_permissions(group_entity, user)
                if permissions and permissions.is_admin:
                    skipped_admin.append((entry, user))
                    db.add_history(
                        f"LIMPIEZA BLOQUE 786-1595: omitido admin user_id={user_id}"
                    )
                    continue

                if user_id in ADMIN_USER_IDS or user_id in OWNER_USER_IDS:
                    skipped_admin.append((entry, user))
                    continue

                # kick_participant = ban + unban.
                # NO se llama a deleteParticipantHistory ni a ningún método
                # de borrado de mensajes.
                await client.kick_participant(group_entity, user)
                expelled.append((entry, user))

                db.add_history(
                    "LIMPIEZA BLOQUE 786-1595: EXPULSADO "
                    f"user_id={user_id} "
                    f"last_seen={format_activity_timestamp(entry.get('last_seen'))} "
                    "historial_mensajes=CONSERVAR"
                )

                if position % 10 == 0:
                    with contextlib.suppress(TelegramError):
                        await progress.edit_text(
                            "🧹 Limpieza en curso...\n"
                            f"Procesados: {position}/{len(eligible)}\n"
                            f"Expulsados: {len(expelled)}\n"
                            f"Errores: {len(failed)}\n\n"
                            "Mensajes históricos: SE CONSERVAN"
                        )

                await asyncio.sleep(INACTIVE_CLEANUP_KICK_DELAY_SECONDS)

            except FloodWaitError as exc:
                wait_seconds = int(getattr(exc, "seconds", 0) or 0)

                if 0 < wait_seconds <= 120:
                    log.warning(
                        "FloodWait %s s; reintento user_id=%s",
                        wait_seconds,
                        user_id,
                    )
                    await asyncio.sleep(wait_seconds + 1)
                    try:
                        permissions = await client.get_permissions(group_entity, user)
                        if permissions and permissions.is_admin:
                            skipped_admin.append((entry, user))
                            continue
                        await client.kick_participant(group_entity, user)
                        expelled.append((entry, user))
                        db.add_history(
                            "LIMPIEZA BLOQUE 786-1595: EXPULSADO tras FloodWait "
                            f"user_id={user_id} historial_mensajes=CONSERVAR"
                        )
                    except Exception as retry_exc:
                        failed.append((entry, user, str(retry_exc)))
                else:
                    failed.append(
                        (entry, user, f"FloodWait demasiado largo: {wait_seconds}s")
                    )
                    break

            except Exception as exc:
                failed.append((entry, user, str(exc)))
                db.add_history(
                    f"LIMPIEZA BLOQUE 786-1595: ERROR user_id={user_id} error={exc}"
                )

        # -----------------------------------------------------------------
        # Depuración del padrón estadístico de Pecos
        # -----------------------------------------------------------------
        # 1) Usuarios que ya no estaban en el grupo.
        # 2) Usuarios cuya expulsión terminó correctamente.
        # NO se borran conversation_messages ni memoria técnica.
        already_out_ids = {
            int(entry.get("user_id") or 0)
            for entry in already_out
            if int(entry.get("user_id") or 0) > 0
        }
        expelled_ids = {
            int(entry.get("user_id") or 0)
            for entry, _user in expelled
            if int(entry.get("user_id") or 0) > 0
        }
        purge_ids = already_out_ids | expelled_ids

        purged_profiles = db.retire_user_profiles(
            HISTORY_SOURCE_CHAT_ID,
            purge_ids,
            reason="limpieza_bloque_786_1595",
        )

        if purged_profiles:
            db.add_history(
                "LIMPIEZA BLOQUE 786-1595: PADRON DEPURADO "
                f"usuarios={purged_profiles} "
                f"ya_fuera={len(already_out_ids)} "
                f"expulsados={len(expelled_ids)} "
                "mensajes_historicos=CONSERVAR"
            )

        # -----------------------------------------------------------------
        # Registro privado detallado para el administrador
        # -----------------------------------------------------------------
        block_label = f"{CLEANUP_BLOCK_FIRST_INDEX}–{CLEANUP_BLOCK_LAST_INDEX}"

        lines = [
            "PECOS PAUL KELE - RESULTADO LIMPIEZA BLOQUE 786–1595",
            f"Grupo: {plan.get('group_title')}",
            f"Fecha: {datetime.now(BOT_TZ).strftime('%d/%m/%Y %H:%M')}",
            f"Bloque objetivo: filas {CLEANUP_BLOCK_FIRST_INDEX} -> {CLEANUP_BLOCK_LAST_INDEX}",
            f"User ID configurados: {CLEANUP_BLOCK_EXPECTED_COUNT}",
            f"SHA-256 lista ordenada: {CLEANUP_BLOCK_TARGET_SHA256}",
            "",
            f"Total expulsados: {len(expelled)}",
            f"Ya estaban fuera y fueron depurados del padrón: {len(already_out_ids)}",
            f"Total de perfiles depurados del padrón de Pecos: {purged_profiles}",
            f"Omitidos por privilegios: {len(skipped_admin)}",
            f"Errores: {len(failed)}",
            "",
            "MENSAJES HISTÓRICOS: CONSERVADOS",
            "MEMORIA TÉCNICA / ARCHIVOS / FINGERPRINTS: CONSERVADOS",
            "",
            "USUARIOS REALMENTE EXPULSADOS:",
        ]

        if expelled:
            for index, (entry, user) in enumerate(expelled, start=1):
                lines.extend(
                    [
                        f"{index}. fila #{int(entry.get('cleanup_source_index') or 0)} | {mtproto_user_display(user)}",
                        f"   User ID: {int(entry.get('user_id') or 0)}",
                        f"   Última actividad observada: "
                        f"{format_activity_timestamp(entry.get('last_seen'))}",
                        "",
                    ]
                )
        else:
            lines.append("(ninguno)")
            lines.append("")

        lines += [
            "USUARIOS QUE YA ESTABAN FUERA Y FUERON DEPURADOS DEL PADRÓN:",
        ]
        if already_out:
            for index, entry in enumerate(already_out, start=1):
                lines.extend(
                    [
                        f"{index}. fila #{int(entry.get('cleanup_source_index') or 0)} | {activity_person_label(entry)}",
                        f"   User ID: {int(entry.get('user_id') or 0)}",
                        f"   Última actividad observada: "
                        f"{format_activity_timestamp(entry.get('last_seen'))}",
                        "",
                    ]
                )
        else:
            lines.append("(ninguno)")
            lines.append("")

        if failed:
            lines += [
                "ERRORES / USUARIOS NO EXPULSADOS:",
            ]
            for entry, user, error_text in failed:
                lines.extend(
                    [
                        f"- {mtproto_user_display(user)}",
                        f"  User ID: {int(entry.get('user_id') or 0)}",
                        f"  Última actividad observada: "
                        f"{format_activity_timestamp(entry.get('last_seen'))}",
                        f"  Error: {error_text}",
                        "",
                    ]
                )

        payload = io.BytesIO("\n".join(lines).encode("utf-8-sig"))
        payload.name = (
            "pecos_usuarios_expulsados_"
            + datetime.now(BOT_TZ).strftime("%Y-%m-%d_%H%M")
            + ".txt"
        )

        with contextlib.suppress(TelegramError):
            await progress.edit_text(
                "✅ Limpieza terminada.\n\n"
                f"Expulsados: {len(expelled)}\n"
                f"Ya fuera y depurados del padrón: {len(already_out_ids)}\n"
                f"Perfiles depurados de Pecos: {purged_profiles}\n"
                f"Omitidos protegidos: {len(skipped_admin)}\n"
                f"Errores: {len(failed)}\n\n"
                "Mensajes históricos: SE CONSERVAN"
            )

        # El TXT detallado se entrega SOLO al administrador que ejecutó
        # la limpieza (chat privado).
        await context.bot.send_document(
            chat_id=chat_id,
            document=payload,
            caption=(
                "📄 Lista privada de usuarios realmente expulsados\n\n"
                f"Expulsados: {len(expelled)}\n"
                f"Ya fuera y depurados: {len(already_out_ids)}\n"
                f"Perfiles depurados: {purged_profiles}\n"
                f"Errores: {len(failed)}\n"
                "✅ Mensajes históricos conservados."
            ),
        )

        # -----------------------------------------------------------------
        # Aviso público en el grupo principal
        # -----------------------------------------------------------------
        # Solo se publica si al menos una expulsión fue efectiva.
        if expelled:
            expelled_count = len(expelled)
            noun = "usuario inactivo" if expelled_count == 1 else "usuarios inactivos"

            public_text = (
                "🧹 <b>Pecos hizo limpieza de la casa.</b>\n"
                f"Se expulsaron <b>{expelled_count} {noun}</b> "
                f"del bloque administrativo <b>{block_label}</b>.\n"
                "Los mensajes históricos permanecen en el grupo."
            )

            try:
                await context.bot.send_message(
                    chat_id=HISTORY_SOURCE_CHAT_ID,
                    text=public_text,
                    parse_mode="HTML",
                )
                db.add_history(
                    "LIMPIEZA BLOQUE 786-1595: AVISO PUBLICO "
                    f"expulsados={expelled_count} bloque={block_label}"
                )
            except TelegramError as exc:
                log.warning(
                    "Limpieza terminada pero no se pudo publicar aviso público: %s",
                    exc,
                )
                db.add_history(
                    "LIMPIEZA BLOQUE 786-1595: ERROR AVISO PUBLICO "
                    f"expulsados={expelled_count} error={exc}"
                )


async def command_cleanup_inactive(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
) -> None:
    message = update.effective_message
    chat = update.effective_chat
    user = update.effective_user

    if not message or not chat or not user:
        return
    if not is_admin(user.id):
        return

    if chat.type != ChatType.PRIVATE:
        await message.reply_text(
            "🔒 /limpieza_inactivos solo se ejecuta por chat privado con Pecos."
        )
        return

    await send_inactive_cleanup_simulation(chat.id, user.id, context)


async def command_activity(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not message or not chat:
        return
    if not user or not is_admin(user.id):
        if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
            await delete_group_command_invocation(message, context)
            await context.bot.send_message(
                chat_id=chat.id,
                text="🔒 Esta función está disponible solo para administradores de Pecos.",
            )
        return
    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        await message.reply_text("📊 /actividad se utiliza dentro de un grupo autorizado.")
        return

    await delete_group_command_invocation(message, context)

    roster_error = ""
    current_snapshot: list[dict[str, object]] = []
    try:
        _client, _entity, _current_members, current_snapshot = (
            await scan_current_group_members_mtproto(chat.id)
        )
    except Exception as exc:
        roster_error = str(exc)
        log.warning("No pude actualizar padrón MTProto para /actividad: %s", exc)

    if current_snapshot:
        entries = build_current_member_activity_snapshot(chat.id, current_snapshot)
        current_count = len(entries)
    else:
        # Fallback de solo lectura si MTProto no está disponible.
        entries = build_member_activity_snapshot(chat.id)
        current_count = 0

    if not entries:
        await context.bot.send_message(
            chat_id=chat.id,
            text="📊 Pecos todavía no tiene datos de actividad para este grupo.",
        )
        return

    query = " ".join(context.args).strip()
    if query:
        matches = find_activity_entries(entries, query)
        if not matches:
            await context.bot.send_message(
                chat_id=chat.id,
                text=f"📊 No encontré al usuario «{query}» en el padrón consultado.",
            )
            return
        if len(matches) > 1:
            sample = "\n".join(
                f"• {activity_person_label(e)} · ID {e['user_id']}"
                for e in matches[:8]
            )
            await context.bot.send_message(
                chat_id=chat.id,
                text=(
                    f"📊 Encontré varias coincidencias para «{query}»:\n"
                    f"{sample}\n\n"
                    "Usa /actividad @usuario o /actividad USER_ID para precisar."
                ),
            )
            return

        entry = matches[0]
        last_seen = (
            entry.get("last_seen")
            if isinstance(entry.get("last_seen"), datetime)
            else None
        )
        icon, state = member_activity_status(last_seen)

        if last_seen is None:
            activity_line = "SIN REGISTRO"
        else:
            activity_line = (
                f"{format_activity_timestamp(last_seen)} "
                f"({human_activity_age(last_seen)})"
            )

        member_status = "miembro actual (padrón MTProto)" if entry.get("member_current") else "no verificado"
        if not current_snapshot:
            try:
                member = await context.bot.get_chat_member(
                    chat_id=chat.id,
                    user_id=int(entry["user_id"]),
                )
                member_status = telegram_member_status_label(str(member.status))
            except TelegramError:
                pass

        await context.bot.send_message(
            chat_id=chat.id,
            text=(
                f"📊 Actividad observada de {activity_person_label(entry)}\n\n"
                f"{icon} Estado por actividad: {state}\n"
                f"🕒 Última actividad observada: {activity_line}\n"
                f"💬 Mensajes registrados: {int(entry.get('message_count') or 0)}\n"
                f"📅 Mensajes registrados últimos 30 días: {int(entry.get('messages_30d') or 0)}\n"
                f"👥 Estado actual: {member_status}\n"
                f"🆔 User ID: {int(entry['user_id'])}\n\n"
                "ℹ️ SIN REGISTRO significa que el usuario está en el grupo, "
                "pero Pecos no tiene actividad atribuible observada para él."
            ),
        )
        return

    buckets = {
        "ACTIVO": 0,
        "POCO ACTIVO": 0,
        "INACTIVO": 0,
        "MUY INACTIVO": 0,
        "SIN REGISTRO": 0,
    }
    for entry in entries:
        last_seen = (
            entry.get("last_seen")
            if isinstance(entry.get("last_seen"), datetime)
            else None
        )
        _, state = member_activity_status(last_seen)
        buckets[state] += 1

    observed_count = len(entries) - buckets["SIN REGISTRO"]

    report = build_activity_text_report(chat.title or str(chat.id), entries)
    payload = io.BytesIO(report.encode("utf-8-sig"))
    payload.name = (
        "pecos_actividad_"
        + datetime.now(BOT_TZ).strftime("%Y-%m-%d_%H%M")
        + ".txt"
    )

    if current_count:
        caption = (
            "📊 Actividad observada por Pecos\n"
            f"👥 Miembros actuales en Telegram: {current_count}\n"
            f"📝 Miembros con actividad registrada: {observed_count}\n"
            f"⚪ Miembros actuales sin actividad registrada: {buckets['SIN REGISTRO']}\n\n"
            f"🟢 Activos (0–30 d): {buckets['ACTIVO']}\n"
            f"🟡 Poco activos (31–90 d): {buckets['POCO ACTIVO']}\n"
            f"🟠 Inactivos (91–180 d): {buckets['INACTIVO']}\n"
            f"🔴 Muy inactivos (>180 d): {buckets['MUY INACTIVO']}\n\n"
            "📄 Adjunto va el detalle del padrón actual.\n"
            "ℹ️ SIN REGISTRO no se considera automáticamente inactivo."
        )
    else:
        caption = (
            "📊 Actividad observada por Pecos\n"
            f"📝 Usuarios con actividad registrada: {len(entries)}\n\n"
            f"🟢 Activos (0–30 d): {buckets['ACTIVO']}\n"
            f"🟡 Poco activos (31–90 d): {buckets['POCO ACTIVO']}\n"
            f"🟠 Inactivos (91–180 d): {buckets['INACTIVO']}\n"
            f"🔴 Muy inactivos (>180 d): {buckets['MUY INACTIVO']}\n\n"
            "⚠️ No pude actualizar el padrón actual por MTProto en esta consulta.\n"
            f"Detalle: {roster_error[:180]}"
        )

    await context.bot.send_document(
        chat_id=chat.id,
        document=payload,
        caption=caption,
    )


async def command_inactive(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not message or not chat:
        return
    if not user or not is_admin(user.id):
        if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
            await delete_group_command_invocation(message, context)
            await context.bot.send_message(
                chat_id=chat.id,
                text="🔒 Esta función está disponible solo para administradores de Pecos.",
            )
        return
    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        await message.reply_text("📊 /inactivos se utiliza dentro de un grupo autorizado.")
        return

    await delete_group_command_invocation(message, context)

    days = 90
    if context.args:
        try:
            days = int(context.args[0])
        except ValueError:
            await context.bot.send_message(
                chat_id=chat.id,
                text="Uso: /inactivos 90\nEl número corresponde a días sin actividad observada.",
            )
            return

    if not 1 <= days <= 3650:
        await context.bot.send_message(
            chat_id=chat.id,
            text="El rango permitido es entre 1 y 3650 días.",
        )
        return

    try:
        _client, _entity, _current_members, current_snapshot = (
            await scan_current_group_members_mtproto(chat.id)
        )
        entries = build_current_member_activity_snapshot(chat.id, current_snapshot)
    except Exception as exc:
        log.warning("No pude actualizar padrón MTProto para /inactivos: %s", exc)
        await context.bot.send_message(
            chat_id=chat.id,
            text=(
                "⚠️ No pude verificar el padrón actual del grupo por MTProto.\n"
                "Por seguridad no generaré una lista de inactivos con datos históricos "
                "que podrían incluir personas que ya salieron."
            ),
        )
        return

    inactive = [
        e for e in entries
        if isinstance(e.get("last_seen"), datetime)
        and activity_age_days(e.get("last_seen")) >= days
    ]
    no_activity = sum(
        1 for e in entries
        if not isinstance(e.get("last_seen"), datetime)
    )

    if not inactive:
        await context.bot.send_message(
            chat_id=chat.id,
            text=(
                f"📊 No encontré miembros actuales con {days} días o más "
                "sin actividad observada.\n"
                f"⚪ Miembros actuales SIN REGISTRO de actividad: {no_activity}"
            ),
        )
        return

    report = build_activity_text_report(
        chat.title or str(chat.id),
        entries,
        inactive_days=days,
    )
    payload = io.BytesIO(report.encode("utf-8-sig"))
    payload.name = (
        f"pecos_inactivos_{days}d_"
        + datetime.now(BOT_TZ).strftime("%Y-%m-%d_%H%M")
        + ".txt"
    )

    await context.bot.send_document(
        chat_id=chat.id,
        document=payload,
        caption=(
            f"📊 Miembros actuales con {days} días o más sin actividad observada: "
            f"{len(inactive)}\n"
            f"⚪ Miembros actuales SIN REGISTRO: {no_activity}\n\n"
            "📄 Adjunto va el detalle.\n"
            "ℹ️ Los SIN REGISTRO se muestran aparte y no se clasifican "
            "automáticamente como inactivos."
        ),
    )


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
            random.choice(get_humor_pool("advice")),
        )


async def command_phrase(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    if message:
        await send_clean_command_text(
            message,
            context,
            random.choice(get_humor_pool("phrase")),
        )


async def command_excuse(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    if message:
        await send_clean_command_text(
            message,
            context,
            random.choice(get_humor_pool("excuse")),
        )


async def command_forecast(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    if message:
        await send_clean_command_text(
            message,
            context,
            random.choice(get_humor_pool("forecast")),
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

    if action == "admin:search_files":
        terms = extract_archive_terms(text)

        if not terms:
            await message.reply_text(
                "📦 No encontré términos válidos.\n\n"
                "Ejemplos:\n"
                "KPG-D6\n"
                "Kenwood DMR\n"
                "CPS EM200\n\n"
                "Intenta nuevamente o usa /cancel."
            )
            return True

        if archive_query_needs_target(text, terms):
            await message.reply_text(
                "👀 Necesito un modelo, familia, plataforma o identificador más concreto.\n\n"
                "Ejemplos: EM200, DEP450, MOTOTRBO, APX, KPG-D6.\n\n"
                "Intenta nuevamente o usa /cancel."
            )
            return True

        rows = search_archive_rows(
            HISTORY_SOURCE_CHAT_ID,
            " ".join(terms),
            limit=8,
        )

        PENDING_ADMIN_ACTION.pop(user.id, None)

        await message.reply_text(
            admin_archive_search_text(text, rows),
            reply_markup=main_menu(),
        )
        return True

    if action == "qa:add":
        parts = [part.strip() for part in text.split("|", 2)]
        if len(parts) != 3:
            await message.reply_text(
                "Formato inválido. Usa:\n"
                "EXACTA | pregunta | respuesta\n"
                "o\n"
                "CONTIENE | frase detonante | respuesta\n\n"
                "Ejemplo:\n"
                "EXACTA | como van las empanadas | 🥟🤠 Van avanzando, partner.\n\n"
                "Usa /cancel para cancelar."
            )
            return True

        match_type = parse_custom_qa_match_type(parts[0])
        question = parts[1]
        response = parts[2]
        normalized_question = normalize_custom_qa_text(question)

        if not match_type or not normalized_question or not response:
            await message.reply_text(
                "Revisa el tipo, la pregunta y la respuesta. El tipo debe ser EXACTA o CONTIENE."
            )
            return True
        if match_type == "CONTAINS" and len(normalized_question) < 4:
            await message.reply_text(
                "Para CONTIENE usa una frase de al menos 4 caracteres para evitar activaciones accidentales."
            )
            return True
        if len(question) > 500 or len(response) > 3500:
            await message.reply_text("Pregunta o respuesta demasiado larga.")
            return True

        qa_id = db.add_custom_qa(
            question, normalized_question, match_type, response, user.id
        )
        if qa_id is None:
            await message.reply_text(
                "Ya existe una regla con esa misma pregunta y tipo. Puedes editarla por ID."
            )
            return True

        PENDING_ADMIN_ACTION.pop(user.id, None)
        db.add_history(f"ADMIN: agregó QA personalizada ID {qa_id}.")
        await message.reply_text(
            f"✅ Pregunta/respuesta guardada con ID {qa_id}.",
            reply_markup=qa_menu(),
        )
        return True

    if action == "qa:edit":
        parts = [part.strip() for part in text.split("|", 3)]
        if len(parts) != 4 or not parts[0].isdigit():
            await message.reply_text(
                "Formato inválido. Usa:\n"
                "ID | EXACTA | pregunta | respuesta\n"
                "o\n"
                "ID | CONTIENE | frase detonante | respuesta\n\n"
                "Ejemplo:\n"
                "3 | EXACTA | como van las empanadas | 🥟🤠 Pecos sigue haciendo control de calidad.\n\n"
                "Usa /cancel para cancelar."
            )
            return True

        qa_id = int(parts[0])
        match_type = parse_custom_qa_match_type(parts[1])
        question = parts[2]
        response = parts[3]
        normalized_question = normalize_custom_qa_text(question)

        if not match_type or not normalized_question or not response:
            await message.reply_text("Revisa ID, tipo, pregunta y respuesta.")
            return True
        if match_type == "CONTAINS" and len(normalized_question) < 4:
            await message.reply_text("Para CONTIENE usa una frase de al menos 4 caracteres.")
            return True
        if len(question) > 500 or len(response) > 3500:
            await message.reply_text("Pregunta o respuesta demasiado larga.")
            return True

        updated = db.update_custom_qa(
            qa_id, question, normalized_question, match_type, response
        )
        if not updated:
            await message.reply_text(
                "No pude actualizar ese ID. Puede no existir o duplicar otra regla ya configurada."
            )
            return True

        PENDING_ADMIN_ACTION.pop(user.id, None)
        db.add_history(f"ADMIN: editó QA personalizada ID {qa_id}.")
        await message.reply_text(
            f"✅ Pregunta/respuesta ID {qa_id} actualizada.",
            reply_markup=qa_menu(),
        )
        return True

    if action == "qa:remove":
        ids = sorted({
            int(token)
            for token in re.split(r"[,;\s]+", text)
            if token.strip().isdigit()
        })
        if not ids:
            await message.reply_text(
                "Envíame uno o más ID. Ejemplo: 2, 5, 8\n\nUsa /cancel para cancelar."
            )
            return True

        removed = db.remove_custom_qa(ids)
        PENDING_ADMIN_ACTION.pop(user.id, None)
        db.add_history(f"ADMIN: eliminó {removed} QA personalizada(s).")
        await message.reply_text(
            f"✅ Se eliminaron {removed} pregunta(s)/respuesta(s).",
            reply_markup=qa_menu(),
        )
        return True

    if action.startswith("humor:edit:"):
        pool_key = action.split(":", 2)[2]
        if not humor_pool_exists(pool_key):
            PENDING_ADMIN_ACTION.pop(user.id, None)
            await message.reply_text("Repertorio desconocido.", reply_markup=humor_menu())
            return True

        parts = [part.strip() for part in text.split("|", 1)]
        if len(parts) != 2 or not parts[0].isdigit() or not parts[1]:
            await message.reply_text(
                "Formato inválido. Usa:\n"
                "NÚMERO | nuevo texto\n\n"
                "Ejemplo:\n2 | 🤠 Nueva broma de Pecos.\n\n"
                "Usa /cancel para cancelar."
            )
            return True

        number = int(parts[0])
        pool = get_humor_pool(pool_key)
        if not (1 <= number <= len(pool)):
            await message.reply_text(
                f"El número debe estar entre 1 y {len(pool)}. Intenta nuevamente o usa /cancel."
            )
            return True

        pool[number - 1] = parts[1]
        try:
            save_humor_pool(pool_key, pool)
        except ValueError as exc:
            await message.reply_text(f"No pude guardar: {exc}")
            return True

        PENDING_ADMIN_ACTION.pop(user.id, None)
        db.add_history(
            f"ADMIN: editó mensaje #{number} del repertorio {pool_key}."
        )
        await message.reply_text(
            f"✅ Mensaje #{number} actualizado en {humor_pool_title(pool_key)}.",
            reply_markup=humor_pool_menu(pool_key),
        )
        return True

    if action.startswith("humor:add:"):
        pool_key = action.split(":", 2)[2]
        if not humor_pool_exists(pool_key):
            PENDING_ADMIN_ACTION.pop(user.id, None)
            await message.reply_text("Repertorio desconocido.", reply_markup=humor_menu())
            return True

        new_items = [line.strip() for line in text.replace("\r", "\n").split("\n") if line.strip()]
        if not new_items:
            await message.reply_text("No encontré mensajes válidos. Intenta nuevamente o usa /cancel.")
            return True

        pool = get_humor_pool(pool_key)
        pool.extend(new_items)
        try:
            save_humor_pool(pool_key, pool)
        except ValueError as exc:
            await message.reply_text(f"No pude guardar: {exc}")
            return True

        PENDING_ADMIN_ACTION.pop(user.id, None)
        db.add_history(
            f"ADMIN: agregó {len(new_items)} mensaje(s) al repertorio {pool_key}."
        )
        await message.reply_text(
            f"✅ Se agregaron {len(new_items)} mensaje(s). Total actual: {len(pool)}.",
            reply_markup=humor_pool_menu(pool_key),
        )
        return True

    if action.startswith("humor:remove:"):
        pool_key = action.split(":", 2)[2]
        if not humor_pool_exists(pool_key):
            PENDING_ADMIN_ACTION.pop(user.id, None)
            await message.reply_text("Repertorio desconocido.", reply_markup=humor_menu())
            return True

        numbers = sorted(
            {
                int(token)
                for token in re.split(r"[,;\s]+", text)
                if token.strip().isdigit()
            },
            reverse=True,
        )
        pool = get_humor_pool(pool_key)
        valid = [number for number in numbers if 1 <= number <= len(pool)]
        if not valid:
            await message.reply_text(
                f"Indica uno o más números entre 1 y {len(pool)}. Ejemplo: 2, 5\n\nUsa /cancel para cancelar."
            )
            return True
        if len(valid) >= len(pool):
            await message.reply_text(
                "No puedo dejar el repertorio vacío. Conserva al menos un mensaje."
            )
            return True

        for number in valid:
            pool.pop(number - 1)
        save_humor_pool(pool_key, pool)
        PENDING_ADMIN_ACTION.pop(user.id, None)
        db.add_history(
            f"ADMIN: eliminó {len(valid)} mensaje(s) del repertorio {pool_key}."
        )
        await message.reply_text(
            f"✅ Se eliminaron {len(valid)} mensaje(s). Total actual: {len(pool)}.",
            reply_markup=humor_pool_menu(pool_key),
        )
        return True

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
            f"✅ Hora diaria guardada: {text}\n\n{build_daily_panel_text()}",
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

    if action == "jokes:edit":
        parts = [part.strip() for part in text.split("|", 3)]
        if len(parts) != 4 or not parts[0].isdigit():
            await message.reply_text(
                "Formato inválido. Usa:\n"
                "ID | @usuario | probabilidad | respuesta\n\n"
                "Ejemplo:\n"
                "3 | @juan | 35 | 🤠 Nueva respuesta para Juan.\n\n"
                "Usa /cancel para cancelar."
            )
            return True

        joke_id = int(parts[0])
        username = parts[1].lstrip("@").strip()
        try:
            probability = int(parts[2])
        except ValueError:
            probability = 0
        response = parts[3].strip()

        if not username or not response or not (1 <= probability <= 100):
            await message.reply_text(
                "Revisa usuario, probabilidad (1–100) y respuesta. Usa /cancel para cancelar."
            )
            return True

        updated = db.update_joke(joke_id, username, probability, response)
        if not updated:
            await message.reply_text(
                "No encontré una broma con ese ID. Revisa «Ver bromas» e intenta nuevamente."
            )
            return True

        PENDING_ADMIN_ACTION.pop(user.id, None)
        db.add_history(f"ADMIN: editó broma interna ID {joke_id}.")
        await message.reply_text(
            f"✅ Broma interna ID {joke_id} actualizada.",
            reply_markup=jokes_menu(),
        )
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
            f"✅ Mensaje diario actualizado.\n\n{build_daily_panel_text()}",
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

    if data == "admin:cleanup_inactive":
        PENDING_ADMIN_ACTION.pop(user_id, None)
        await send_inactive_cleanup_simulation(chat.id, user_id, context)
        return

    if data == "cleanup:refresh":
        await send_inactive_cleanup_simulation(chat.id, user_id, context)
        return

    if data == "cleanup:cancel":
        PENDING_INACTIVE_CLEANUP.pop(user_id, None)
        await query.message.reply_text(
            "❌ Limpieza cancelada. No se expulsó a ningún usuario.",
            reply_markup=main_menu(),
        )
        return

    if data == "cleanup:confirm":
        expires_at = float(PENDING_INACTIVE_CLEANUP.get(user_id, 0.0) or 0.0)
        if expires_at <= time.monotonic():
            PENDING_INACTIVE_CLEANUP.pop(user_id, None)
            await query.message.reply_text(
                "⌛ La confirmación venció. Ejecuta nuevamente la simulación."
            )
            return

        PENDING_INACTIVE_CLEANUP.pop(user_id, None)
        await execute_inactive_cleanup(chat.id, user_id, context)
        return

    if data == "admin:activity":
        PENDING_ADMIN_ACTION.pop(user_id, None)

        try:
            _client, _entity, _members, snapshot = (
                await scan_current_group_members_mtproto(HISTORY_SOURCE_CHAT_ID)
            )
            entries = build_current_member_activity_snapshot(
                HISTORY_SOURCE_CHAT_ID,
                snapshot,
            )
        except Exception as exc:
            await query.message.reply_text(
                "⚠️ No pude actualizar el padrón actual por MTProto.\n"
                f"Detalle: {str(exc)[:220]}"
            )
            return

        buckets = {
            "ACTIVO": 0,
            "POCO ACTIVO": 0,
            "INACTIVO": 0,
            "MUY INACTIVO": 0,
            "SIN REGISTRO": 0,
        }
        for entry in entries:
            last_seen = (
                entry.get("last_seen")
                if isinstance(entry.get("last_seen"), datetime)
                else None
            )
            _, state = member_activity_status(last_seen)
            buckets[state] += 1

        observed_count = len(entries) - buckets["SIN REGISTRO"]
        group_title = db.known_group_title(HISTORY_SOURCE_CHAT_ID)

        report = build_activity_text_report(group_title, entries)
        payload = io.BytesIO(report.encode("utf-8-sig"))
        payload.name = (
            "pecos_actividad_"
            + datetime.now(BOT_TZ).strftime("%Y-%m-%d_%H%M")
            + ".txt"
        )

        caption = (
            f"👥 Actividad observada — {group_title}\n\n"
            f"Miembros actuales en Telegram: {len(entries)}\n"
            f"📝 Con actividad registrada: {observed_count}\n"
            f"⚪ Sin actividad registrada: {buckets['SIN REGISTRO']}\n\n"
            f"🟢 Activos (0–30 d): {buckets['ACTIVO']}\n"
            f"🟡 Poco activos (31–90 d): {buckets['POCO ACTIVO']}\n"
            f"🟠 Inactivos (91–180 d): {buckets['INACTIVO']}\n"
            f"🔴 Muy inactivos (>180 d): {buckets['MUY INACTIVO']}\n\n"
            "📄 Adjunto va el detalle del padrón actual."
        )

        await context.bot.send_document(
            chat_id=chat.id,
            document=payload,
            caption=caption,
        )
        return

    if data == "admin:inactive":
        PENDING_ADMIN_ACTION.pop(user_id, None)
        await safe_edit(
            query,
            "💤 Usuarios sin actividad observada\n\n"
            "Elige el período que quieres revisar.",
            inactive_admin_menu(),
        )
        return

    if data.startswith("admininactive:"):
        try:
            days = int(data.split(":", 1)[1])
        except (ValueError, IndexError):
            await query.message.reply_text("No pude interpretar el período.")
            return

        if days not in {30, 60, 90, 180, 365}:
            await query.message.reply_text("Período no permitido.")
            return

        try:
            _client, _entity, _members, snapshot = (
                await scan_current_group_members_mtproto(HISTORY_SOURCE_CHAT_ID)
            )
            entries = build_current_member_activity_snapshot(
                HISTORY_SOURCE_CHAT_ID,
                snapshot,
            )
        except Exception as exc:
            await query.message.reply_text(
                "⚠️ No pude verificar el padrón actual por MTProto.\n"
                f"Detalle: {str(exc)[:220]}"
            )
            return

        inactive = [
            entry
            for entry in entries
            if isinstance(entry.get("last_seen"), datetime)
            and activity_age_days(entry.get("last_seen")) >= days
        ]

        group_title = db.known_group_title(HISTORY_SOURCE_CHAT_ID)

        if not inactive:
            await query.message.reply_text(
                f"💤 No encontré usuarios con {days} días o más "
                "sin actividad observada."
            )
            return

        report = build_activity_text_report(
            group_title,
            entries,
            inactive_days=days,
        )
        payload = io.BytesIO(report.encode("utf-8-sig"))
        payload.name = (
            f"pecos_inactivos_{days}d_"
            + datetime.now(BOT_TZ).strftime("%Y-%m-%d_%H%M")
            + ".txt"
        )

        await context.bot.send_document(
            chat_id=chat.id,
            document=payload,
            caption=(
                f"💤 {group_title}\n"
                f"{len(inactive)} usuario(s) con {days} días o más "
                "sin actividad observada.\n\n"
                "📄 Adjunto va el detalle.\n"
                "ℹ️ No equivale a la última conexión a Telegram."
            ),
        )
        return

    if data == "admin:search":
        PENDING_ADMIN_ACTION[user_id] = "admin:search_files"
        await query.message.reply_text(
            "📦 ¿Qué archivo, programa, CPS, firmware, modelo o identificador "
            "quieres buscar en el archivo de YO REPARO RADIOS?\n\n"
            "Ejemplos:\n"
            "KPG-D6\n"
            "Kenwood DMR\n"
            "CPS EM200\n\n"
            "Usa /cancel para cancelar."
        )
        return

    if data == "admin:memory":
        PENDING_ADMIN_ACTION.pop(user_id, None)
        stats = db.admin_memory_stats(HISTORY_SOURCE_CHAT_ID)
        statuses = stats["statuses"]
        group_title = db.known_group_title(HISTORY_SOURCE_CHAT_ID)

        auto_stats = db.autonomous_memory_stats(HISTORY_SOURCE_CHAT_ID)

        memory_text = (
            f"🧠 Memoria de Pecos — {group_title}\n\n"
            f"Mensajes almacenados: {stats['messages']:,}\n"
            f"Clasificaciones: {stats['classifications']:,}\n"
            f"Pares consulta/respuesta: {stats['pairs']:,}\n"
            f"Autores con actividad registrada: {stats['users']:,}\n"
            f"Soluciones confirmadas: {statuses.get('CONFIRMED', 0):,}\n"
            f"Respuestas rechazadas: {statuses.get('REJECTED', 0):,}\n"
            f"Pendientes/probables: {statuses.get('PROBABLE', 0):,}\n"
            f"Fingerprints del grupo: {stats['fingerprints']:,}\n\n"
            f"🤖 Memoria técnica autónoma\n"
            f"Q/A confirmados aprendidos: {auto_stats['qa_confirmed']:,}\n"
            f"Q/A agradecidos como evidencia: {auto_stats['qa_acknowledged']:,}\n"
            f"Evidencias estructuradas: {auto_stats['fact_evidence']:,}\n"
            f"Hechos confiables: {auto_stats['trusted_facts']:,}\n\n"
            f"Grupo fuente: {HISTORY_SOURCE_CHAT_ID}\n"
            "Estado: ✅ Memoria histórica + aprendizaje autónomo activos"
        )
        await query.message.reply_text(memory_text)
        return

    if data == "admin:info":
        PENDING_ADMIN_ACTION.pop(user_id, None)
        unique_count, hash_count = db.duplicate_counts()
        stats = db.admin_memory_stats(HISTORY_SOURCE_CHAT_ID)
        auto_stats = db.autonomous_memory_stats(HISTORY_SOURCE_CHAT_ID)

        try:
            db_size_mb = DB_PATH.stat().st_size / (1024 * 1024)
            db_size_text = f"{db_size_mb:.1f} MB"
        except OSError:
            db_size_text = "no disponible"

        info_text = (
            f"ℹ️ {APP_NAME}\n\n"
            f"Versión: {VERSION}\n"
            f"Estado del proceso: 🟢 Online\n"
            f"Zona horaria: {TIMEZONE_NAME}\n"
            f"Bot API: {'LOCAL' if LOCAL_BOT_API else 'PÚBLICA'}\n"
            f"Base de datos: {DB_PATH}\n"
            f"Tamaño DB: {db_size_text}\n"
            f"Grupos autorizados: {len(ALLOWED_GROUP_IDS)}\n"
            f"Administradores Pecos: {len(ADMIN_USER_IDS)}\n"
            f"MTProto limpieza: {'✅ Configurado' if not mtproto_cleanup_configuration_error() else '⚠️ No disponible'}\n"
            f"Memoria histórica: ✅ Activa\n"
            f"Memoria técnica autónoma: {'✅ Activa' if autonomous_memory_enabled() else '❌ Desactivada'}\n"
            f"Q/A técnicos aprendidos: {auto_stats['qa_confirmed']:,}\n"
            f"Hechos técnicos confiables: {auto_stats['trusted_facts']:,}\n"
            f"Mensajes históricos: {stats['messages']:,}\n"
            f"Autores observados: {stats['users']:,}\n"
            f"FileUniqueId registrados: {unique_count:,}\n"
            f"SHA-256 / fingerprints registrados: {hash_count:,}\n"
            f"Duplicados: {'✅ Activo' if db.is_true('duplicates_enabled') else '❌ Desactivado'}\n"
            f"Silencio: {'✅ Activo' if db.is_true('silence_enabled') else '❌ Desactivado'}\n"
            f"Mensaje diario: {'✅ Activo' if db.is_true('daily_enabled') else '❌ Desactivado'}"
        )
        await query.message.reply_text(info_text)
        return

    if data == "admin:help":
        PENDING_ADMIN_ACTION.pop(user_id, None)
        help_text = (
            "❓ Ayuda para administradores de Pecos\n\n"
            "/config — Abrir este panel\n"
            "/buscar KPG-D6 — Buscar archivos\n"
            "/historial EM200 — Buscar conversaciones históricas\n"
            "/actividad — Resumen de actividad observada\n"
            "/actividad @usuario — Ficha de un usuario\n"
            "/inactivos 90 — Usuarios sin actividad durante 90 días\n"
            "/limpieza_inactivos — Simular/confirmar bloque 786–1595\n"
            "/recordar texto — Guardar un recuerdo del grupo\n"
            "/recuerdos — Ver recuerdos\n"
            "/olvidar ID — Borrar un recuerdo\n"
            "/encuesta — Crear encuesta\n"
            "/consejo — Consejo de Pecos\n"
            "/frase — Frase de Pecos\n"
            "/excusa — Excusa de Pecos\n"
            "/pronostico — Pronóstico de Pecos\n"
            "/cancel — Cancelar una operación del panel\n"
            "/id — Ver Telegram User ID\n\n"
            "🔒 Estas funciones manuales están reservadas a los "
            "administradores configurados de Pecos."
        )
        await query.message.reply_text(help_text)
        return

    if data == "menu:qa":
        PENDING_ADMIN_ACTION.pop(user_id, None)
        await safe_edit(
            query,
            "💬 Preguntas y respuestas de Pecos\n\n"
            f"Configuradas: {len(db.list_custom_qa())}\n\n"
            "EXACTA: responde cuando la pregunta coincide completa.\n"
            "CONTIENE: responde cuando la frase aparece dentro de un mensaje más largo.",
            qa_menu(),
        )
        return

    if data == "qa:list":
        await send_long_text(chat.id, format_custom_qa_list(), context)
        await query.message.reply_text("Opciones:", reply_markup=qa_menu())
        return

    if data == "qa:add":
        PENDING_ADMIN_ACTION[user_id] = "qa:add"
        await query.message.reply_text(
            "➕ Agregar pregunta/respuesta\n\n"
            "Formato:\n"
            "EXACTA | pregunta | respuesta\n"
            "o\n"
            "CONTIENE | frase detonante | respuesta\n\n"
            "Ejemplo:\n"
            "EXACTA | como van las empanadas | 🥟🤠 Van avanzando, partner. Pecos ya hizo control de calidad.\n\n"
            "Pecos ignora tildes, signos y su propio nombre al comparar.\n"
            "Usa /cancel para cancelar."
        )
        return

    if data == "qa:edit":
        PENDING_ADMIN_ACTION[user_id] = "qa:edit"
        await query.message.reply_text(
            "✏️ Editar pregunta/respuesta\n\n"
            "Formato:\n"
            "ID | EXACTA | pregunta | respuesta\n"
            "o\n"
            "ID | CONTIENE | frase detonante | respuesta\n\n"
            "Consulta los ID con «Ver respuestas».\n"
            "Usa /cancel para cancelar."
        )
        return

    if data == "qa:remove":
        PENDING_ADMIN_ACTION[user_id] = "qa:remove"
        await query.message.reply_text(
            "➖ Eliminar pregunta/respuesta\n\n"
            "Envíame uno o varios ID.\n"
            "Ejemplo: 2, 5, 8\n\n"
            "Usa /cancel para cancelar."
        )
        return

    if data == "menu:humor":
        PENDING_ADMIN_ACTION.pop(user_id, None)
        await safe_edit(
            query,
            "🎭 Bromas y humor de Pecos\n\n"
            "Accesos directos a los distintos repertorios y controles de humor.",
            humor_menu(),
        )
        return

    if data.startswith("humor:list:"):
        pool_key = data.split(":", 2)[2]
        if not humor_pool_exists(pool_key):
            await query.message.reply_text("Repertorio desconocido.", reply_markup=humor_menu())
            return

        await send_long_text(
            chat.id,
            format_humor_pool_list(pool_key),
            context,
        )
        await query.message.reply_text(
            f"Opciones de {humor_pool_title(pool_key)}:",
            reply_markup=humor_pool_menu(pool_key),
        )
        return

    if data.startswith("humor:test:"):
        pool_key = data.split(":", 2)[2]
        if not humor_pool_exists(pool_key):
            await query.message.reply_text("Repertorio desconocido.", reply_markup=humor_menu())
            return
        await query.message.reply_text(
            render_humor_preview(
                pool_key,
                query.from_user.first_name or "partner",
            ),
            reply_markup=humor_pool_menu(pool_key),
        )
        return

    if data.startswith("humor:edit:"):
        pool_key = data.split(":", 2)[2]
        if not humor_pool_exists(pool_key):
            await query.message.reply_text("Repertorio desconocido.", reply_markup=humor_menu())
            return
        PENDING_ADMIN_ACTION[user_id] = f"humor:edit:{pool_key}"
        await query.message.reply_text(
            f"✏️ Editar {humor_pool_title(pool_key)}\n\n"
            "Envíame:\n"
            "NÚMERO | nuevo texto\n\n"
            "Ejemplo:\n"
            "2 | 🤠 Esta es la nueva broma de Pecos.\n\n"
            "El número corresponde al listado que acabas de ver.\n"
            "Usa /cancel para cancelar."
        )
        return

    if data.startswith("humor:add:"):
        pool_key = data.split(":", 2)[2]
        if not humor_pool_exists(pool_key):
            await query.message.reply_text("Repertorio desconocido.", reply_markup=humor_menu())
            return
        PENDING_ADMIN_ACTION[user_id] = f"humor:add:{pool_key}"
        await query.message.reply_text(
            f"➕ Agregar a {humor_pool_title(pool_key)}\n\n"
            "Envíame una o varias bromas, una por línea.\n"
            "Usa /cancel para cancelar."
        )
        return

    if data.startswith("humor:remove:"):
        pool_key = data.split(":", 2)[2]
        if not humor_pool_exists(pool_key):
            await query.message.reply_text("Repertorio desconocido.", reply_markup=humor_menu())
            return
        PENDING_ADMIN_ACTION[user_id] = f"humor:remove:{pool_key}"
        await query.message.reply_text(
            f"➖ Eliminar de {humor_pool_title(pool_key)}\n\n"
            "Envíame los números que quieras eliminar.\n"
            "Ejemplo: 2, 5, 7\n\n"
            "Usa /cancel para cancelar."
        )
        return

    if data.startswith("humor:reset:"):
        pool_key = data.split(":", 2)[2]
        if not humor_pool_exists(pool_key):
            await query.message.reply_text("Repertorio desconocido.", reply_markup=humor_menu())
            return
        markup = InlineKeyboardMarkup(
            [
                [
                    InlineKeyboardButton("✅ Sí, restaurar", callback_data=f"humor:reset_yes:{pool_key}"),
                    InlineKeyboardButton("❌ No", callback_data=f"humor:list:{pool_key}"),
                ]
            ]
        )
        await safe_edit(
            query,
            f"⚠️ ¿Restaurar los mensajes originales de {humor_pool_title(pool_key)}?\n\n"
            "Se perderán las ediciones hechas desde el panel para este repertorio.",
            markup,
        )
        return

    if data.startswith("humor:reset_yes:"):
        pool_key = data.split(":", 2)[2]
        if not humor_pool_exists(pool_key):
            await query.message.reply_text("Repertorio desconocido.", reply_markup=humor_menu())
            return
        reset_humor_pool(pool_key)
        db.add_history(f"ADMIN: restauró repertorio de humor {pool_key}.")
        await safe_edit(
            query,
            f"✅ {humor_pool_title(pool_key)} restaurado a sus mensajes originales.",
            humor_pool_menu(pool_key),
        )
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

    if data == "jokes:edit":
        PENDING_ADMIN_ACTION[user_id] = "jokes:edit"
        await query.message.reply_text(
            "✏️ Editar broma interna por ID\n\n"
            "Formato:\n"
            "ID | @usuario | probabilidad | respuesta\n\n"
            "Ejemplo:\n"
            "3 | @juan | 35 | 🤠 Nueva respuesta de Pecos.\n\n"
            "Puedes consultar los ID con «Ver bromas».\n"
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
            f"Intervalo: cada {db.get_setting('silence_hours', '8')} hora(s) de silencio\n"
            "Repite mientras el grupo continúe en silencio.\n"
            "El contador se reinicia cuando alguien interviene.\n"
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
            f"Intervalo: cada {db.get_setting('silence_hours', '8')} hora(s) de silencio\n"
            "Repite mientras el grupo continúe en silencio.\n"
            "El contador se reinicia cuando alguien interviene.\n"
            "Horario: 09:00–22:00",
            silence_menu(),
        )
        return

    if data == "silence:hours":
        PENDING_ADMIN_ACTION[user_id] = "silence:hours"
        await query.message.reply_text(
            "⏱️ ¿Cada cuántas horas de silencio debe hablar Pecos?\n\n"
            "Mientras nadie intervenga, repetirá un mensaje al completar cada intervalo.\n"
            "Escribe un número entre 1 y 72.\n"
            "Ejemplo: 1 = una intervención por cada hora completa de silencio.\n\n"
            "Usa /cancel para cancelar."
        )
        return

    if data == "menu:daily":
        PENDING_ADMIN_ACTION.pop(user_id, None)
        await safe_edit(
            query,
            build_daily_panel_text(),
            daily_menu(),
        )
        return

    if data in ("daily:toggle", "daily:fun"):
        # Compatibilidad con botones de mensajes antiguos:
        # desde 2.8.25 el diario es siempre activo y aleatorio.
        db.set_setting("daily_enabled", "1")
        db.set_setting("daily_fun_enabled", "1")
        db.set_setting("daily_message", "")
        await safe_edit(
            query,
            build_daily_panel_text(),
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
        PENDING_ADMIN_ACTION.pop(user_id, None)
        db.set_setting("daily_message", "")
        await query.message.reply_text(
            "🕘 El mensaje diario ya no usa texto fijo.\n\n"
            "Edita el repertorio desde «Saludos diarios».",
            reply_markup=daily_menu(),
        )
        return

    if data == "daily:view":
        await query.message.reply_text(
            build_daily_panel_text(),
            reply_markup=daily_menu(),
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
            "Mensaje diario: SIEMPRE ACTIVO\n"
            "Modo diario: Saludo aleatorio de Pecos\n"
            f"Hora diaria: {db.get_setting('daily_time')} ({TIMEZONE_NAME})\n"
            f"Bot API: {'LOCAL integrada (--local)' if LOCAL_BOT_API else 'PÚBLICA'}\n"
            f"Archivos de hash: temporal ({TELEGRAM_FILES_DIR})\n"
            f"Bromas internas: {len(db.list_jokes())}\n"
            f"Preguntas/respuestas personalizadas: {len(db.list_custom_qa())}\n"
            f"Detector de silencio: {'Activo' if db.is_true('silence_enabled') else 'Desactivado'} "
            f"(cada {db.get_setting('silence_hours', '8')} h mientras continúe el silencio)\n"
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

                # El catálogo técnico es una capa paralela. Se actualiza solo
                # DESPUÉS de que SHA-256 ya decidió que el archivo es original.
                try:
                    technical_catalog_upsert_fingerprint(
                        chat_id=chat_id,
                        sha256=sha256,
                        message_id=message_id,
                        file_unique_id=unique_id,
                        file_name=file_name,
                        file_size=file_size,
                        sender_id=sender_id,
                        sender_name=sender_name,
                    )
                except Exception as exc:
                    log.warning(
                        "CATALOGO TECNICO: no se pudo indexar %s: %s",
                        file_name,
                        exc,
                    )

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

    if not pecos_conversational_question_allowed(message.text):
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
        origin = "VHF"
        destination = "UHF"
        direction = "VHF → UHF"
    else:
        origin = "UHF"
        destination = "VHF"
        direction = "UHF → VHF"

    joke = choose_random(
        "band_conversion",
        get_humor_pool("band"),
        display_name(message),
    )
    joke = (
        joke
        .replace("{origen}", origin)
        .replace("{destino}", destination)
    )

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



def xerax_day_period(now: datetime) -> str:
    """Tres tramos máximos por fecha local: mañana, tarde y noche."""
    hour = now.hour
    if 6 <= hour < 12:
        return "manana"
    if 12 <= hour < 19:
        return "tarde"
    return "noche"


async def handle_xerax_auto_presence(message: Message) -> bool:
    """
    Broma automática a XeraX:
    - solo cuando @XeraX interviene personalmente;
    - máximo una por mañana, una por tarde y una por noche;
    - persistente en SQLite;
    - NO consume ni reemplaza las bromas antiguas por mención.
    """
    if not XERAX_JOKES_ENABLED:
        return False

    user = message.from_user
    if not user or user.is_bot or not user.username:
        return False

    if user.username.casefold() != XERAX_USERNAME:
        return False

    now = datetime.now(BOT_TZ)
    period = xerax_day_period(now)
    today = now.strftime("%Y-%m-%d")
    event_key = f"xerax_auto_presence:{period}"

    first_in_period = db.claim_daily_user_event(
        event_key,
        int(user.id),
        user.username,
        today,
    )
    if not first_in_period:
        return False

    await message.reply_text(
        choose_random(
            f"xerax_auto_{period}",
            get_humor_pool("xerax_auto"),
            display_name(message),
        )
    )
    db.add_history(
        f"BROMA XERAX AUTO {period.upper()} | {display_name(message)} | chat {message.chat_id}"
    )
    return True


def message_offends_pecos(message: Message, bot_id: int | None) -> bool:
    text_value = message.text or message.caption or ""
    if not text_value or not PECOS_INSULT_RE.search(normalize_intent(text_value)):
        return False

    if text_mentions_pecos(text_value):
        return True

    replied = message.reply_to_message
    replied_user = replied.from_user if replied else None
    return bool(
        replied_user
        and replied_user.is_bot
        and bot_id is not None
        and int(replied_user.id) == int(bot_id)
    )


async def handle_pecos_insult_duel(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    """
    Respuesta humorística a una ofensa dirigida claramente a Pecos.
    Máximo una por usuario por bloque de 2 horas para evitar spam.
    """
    user = message.from_user
    if not user or user.is_bot:
        return False

    if not message_offends_pecos(message, context.bot.id):
        return False

    now = datetime.now(BOT_TZ)
    today = now.strftime("%Y-%m-%d")
    two_hour_slot = now.hour // 2
    event_key = f"pecos_duel:{two_hour_slot}"

    allowed = db.claim_daily_user_event(
        event_key,
        int(user.id),
        user.username or str(user.id),
        today,
    )
    if not allowed:
        return False

    template = choose_random(
        "pecos_duel",
        get_humor_pool("duel"),
        display_name(message),
    )
    await message.reply_text(
        template.format(usuario=display_name(message))
    )
    db.add_history(
        f"DUELO HUMOR PECOS | {display_name(message)} | chat {message.chat_id}"
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
    if not MELERIX_JOKES_ENABLED:
        return False

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
    if not XERAX_JOKES_ENABLED:
        return False

    if not message.from_user or message.from_user.is_bot:
        return False

    # Las intervenciones del propio XeraX usan el nuevo límite por
    # mañana/tarde/noche. Este repertorio antiguo queda para menciones.
    if (
        message.from_user.username
        and message.from_user.username.casefold() == XERAX_USERNAME
    ):
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
            get_humor_pool("xerax_manual"),
            display_name(message),
        )
    )

    db.add_history(
        f"BROMA XERAX | {display_name(message)} | chat {message.chat_id}"
    )
    return True


class SafeMathError(ValueError):
    pass



def _math_number_token(value: str) -> str:
    return value.strip().replace(",", ".")


def _math_natural_language_candidate(
    text_value: str,
) -> tuple[str | None, str | None]:
    """Convierte preguntas matemáticas simples en español a una expresión segura.

    Ejemplos:
      Pecos cuanto es 10 por 10 menos 10
      Pecos suma 25 y 18
      Pecos multiplica 7 por 8
      Pecos divide 150 entre 3
      Pecos cual es el doble de 18
      Pecos cual es la mitad de 90
      Pecos 15 por ciento de 800
    """
    raw = (text_value or "").strip()
    if not raw:
        return None, None

    normalized = normalize_intent(raw).lower()

    # Quitar llamadas al bot.
    for alias in sorted(PECOS_USERNAME_ALIASES, key=len, reverse=True):
        alias_norm = normalize_intent(alias).lower().lstrip("@")
        if alias_norm:
            normalized = re.sub(
                rf"(?<![a-z0-9_])@?{re.escape(alias_norm)}(?![a-z0-9_])",
                " ",
                normalized,
            )
    normalized = re.sub(
        r"(?<![a-z0-9_])(?:pecos|peco)(?![a-z0-9_])",
        " ",
        normalized,
    )

    # Quitar fórmulas introductorias habituales.
    normalized = re.sub(
        r"^\s*(?:"
        r"dime\s+|"
        r"me\s+dices\s+|"
        r"me\s+puedes\s+decir\s+|"
        r"cual\s+es\s+|"
        r"cuanto\s+es\s+|"
        r"cuanto\s+da\s+|"
        r"cuanto\s+resulta\s+|"
        r"calcula\s+|calcular\s+|"
        r"resuelve\s+|resolver\s+|"
        r"resultado\s+de\s+"
        r")",
        "",
        normalized,
    )
    normalized = normalized.strip(" ?¿!¡=.;:")
    normalized = re.sub(r"\s+", " ", normalized)

    number = r"([+-]?\d+(?:[.,]\d+)?)"

    # Porcentaje natural: "15 por ciento de 800".
    match = re.fullmatch(
        rf"{number}\s+(?:por\s+ciento|porciento)\s+de\s+{number}",
        normalized,
    )
    if match:
        left = _math_number_token(match.group(1))
        right = _math_number_token(match.group(2))
        return f"(({left})/100)*({right})", normalized

    # Doble / triple / mitad.
    match = re.fullmatch(rf"(?:el\s+)?doble\s+de\s+{number}", normalized)
    if match:
        n = _math_number_token(match.group(1))
        return f"2*({n})", normalized

    match = re.fullmatch(rf"(?:el\s+)?triple\s+de\s+{number}", normalized)
    if match:
        n = _math_number_token(match.group(1))
        return f"3*({n})", normalized

    match = re.fullmatch(rf"(?:la\s+)?mitad\s+de\s+{number}", normalized)
    if match:
        n = _math_number_token(match.group(1))
        return f"({n})/2", normalized

    # Raíz cuadrada simple.
    match = re.fullmatch(rf"(?:la\s+)?raiz\s+cuadrada\s+de\s+{number}", normalized)
    if match:
        n = _math_number_token(match.group(1))
        if float(n) < 0:
            return None, None
        return f"({n})**0.5", normalized

    # Verbos explícitos.
    match = re.fullmatch(rf"suma\s+{number}\s+(?:y|mas)\s+{number}", normalized)
    if match:
        a = _math_number_token(match.group(1))
        b = _math_number_token(match.group(2))
        return f"({a})+({b})", normalized

    match = re.fullmatch(rf"resta\s+{number}\s+(?:menos|y)\s+{number}", normalized)
    if match:
        a = _math_number_token(match.group(1))
        b = _math_number_token(match.group(2))
        return f"({a})-({b})", normalized

    # "resta 8 a 20" = 20 - 8
    match = re.fullmatch(rf"resta\s+{number}\s+a\s+{number}", normalized)
    if match:
        subtrahend = _math_number_token(match.group(1))
        minuend = _math_number_token(match.group(2))
        return f"({minuend})-({subtrahend})", normalized

    match = re.fullmatch(
        rf"(?:multiplica|multiplicar)\s+{number}\s+(?:por|x)\s+{number}",
        normalized,
    )
    if match:
        a = _math_number_token(match.group(1))
        b = _math_number_token(match.group(2))
        return f"({a})*({b})", normalized

    match = re.fullmatch(
        rf"(?:divide|dividir)\s+{number}\s+(?:entre|por)\s+{number}",
        normalized,
    )
    if match:
        a = _math_number_token(match.group(1))
        b = _math_number_token(match.group(2))
        return f"({a})/({b})", normalized

    # Expresión en palabras con prioridad matemática:
    # "10 por 10 menos 10", "8 mas 2 por 5", etc.
    word_expr = normalized
    word_expr = re.sub(r"\bdividido\s+(?:por|entre)\b", "/", word_expr)
    word_expr = re.sub(r"\bentre\b", "/", word_expr)
    word_expr = re.sub(r"\bpor\b", "*", word_expr)
    word_expr = re.sub(r"\bmas\b", "+", word_expr)
    word_expr = re.sub(r"\bmenos\b", "-", word_expr)
    word_expr = re.sub(r"\s+", " ", word_expr).strip()

    # Solo aceptar si después de traducir quedaron números, operadores y paréntesis.
    if (
        re.search(r"[+\-*/]", word_expr)
        and re.fullmatch(r"[0-9.,\s+\-*/()]+", word_expr)
    ):
        word_expr = re.sub(r"(?<=\d),(?=\d)", ".", word_expr)
        return word_expr, normalized

    return None, None


def _math_candidate_text(text_value: str) -> tuple[str | None, str | None]:
    """Extrae una expresión aritmética solo cuando la intención es clara."""
    raw = (text_value or "").strip()
    if not raw:
        return None, None

    normalized = normalize_intent(raw).strip()
    directed_to_pecos = text_mentions_pecos(raw)
    explicit_math = bool(
        re.search(
            r"\b(?:cuanto\s+es|calcula|calcular|resuelve|resolver|resultado\s+de)\b",
            normalized,
        )
    )

    if not (directed_to_pecos or explicit_math):
        return None, None

    # Primero probar lenguaje natural. Si no coincide, se conserva el parser
    # simbólico ya existente.
    natural_expression, natural_display = _math_natural_language_candidate(raw)
    if natural_expression is not None and natural_display is not None:
        return natural_expression, natural_display

    # Caso natural de porcentaje: "15% de 800".
    percent_source = normalized
    percent_source = re.sub(r"(?<![a-z0-9_])(?:pecos|peco)(?![a-z0-9_])", " ", percent_source)
    for alias in sorted(PECOS_USERNAME_ALIASES, key=len, reverse=True):
        alias_norm = normalize_intent(alias).lower().lstrip("@")
        if alias_norm:
            percent_source = re.sub(
                rf"(?<![a-z0-9_])@?{re.escape(alias_norm)}(?![a-z0-9_])",
                " ",
                percent_source,
            )
    percent_source = re.sub(
        r"\b(?:dime\s+)?(?:cuanto\s+es|calcula|calcular|resuelve|resolver|resultado\s+de)\b",
        " ",
        percent_source,
    )
    percent_source = re.sub(r"\s+", " ", percent_source).strip(" ?¿!¡=.")

    pm = re.fullmatch(
        r"([+-]?\d+(?:[.,]\d+)?)\s*%\s*(?:de|of)\s*([+-]?\d+(?:[.,]\d+)?)",
        percent_source,
        re.IGNORECASE,
    )
    if pm:
        left = pm.group(1).replace(",", ".")
        right = pm.group(2).replace(",", ".")
        return f"(({left})/100)*({right})", percent_source

    candidate = raw
    # Quitar username del bot y los vocativos Pecos/Peco sin tocar operadores.
    for alias in sorted(PECOS_USERNAME_ALIASES, key=len, reverse=True):
        candidate = re.sub(
            rf"(?<![\w])@?{re.escape(alias)}(?![\w])",
            " ",
            candidate,
            flags=re.IGNORECASE,
        )
    candidate = re.sub(r"(?<![\w])(?:pecos|peco)(?![\w])", " ", candidate, flags=re.IGNORECASE)
    candidate = re.sub(
        r"^\s*(?:dime\s+)?(?:cu[aá]nto\s+es|calcula|calcular|resuelve|resolver|resultado\s+de)\s*[:=,]?\s*",
        "",
        candidate,
        flags=re.IGNORECASE,
    )
    candidate = candidate.strip(" \t\r\n?¿!¡=.;:")

    # x/X entre números se interpreta como multiplicación.
    candidate = re.sub(r"(?<=\d)\s*[xX]\s*(?=[\d(+-])", "*", candidate)
    candidate = candidate.replace("×", "*").replace("÷", "/").replace("−", "-")
    candidate = re.sub(r"(?<=\d),(?=\d)", ".", candidate)

    if not candidate or len(candidate) > MATH_MAX_EXPRESSION_LENGTH:
        return None, None

    # Debe tener por lo menos un operador real; un número suelto no activa Pecos.
    if not re.search(r"[+\-*/^]", candidate):
        return None, None

    # Solo caracteres aritméticos. % queda reservado a "% de".
    if not re.fullmatch(r"[0-9.\s+\-*/^()]+", candidate):
        return None, None

    return candidate.replace("^", "**"), candidate


def _safe_math_eval(expression: str) -> float | int:
    try:
        tree = ast.parse(expression, mode="eval")
    except SyntaxError as exc:
        raise SafeMathError("expresión inválida") from exc

    nodes = list(ast.walk(tree))
    if len(nodes) > MATH_MAX_AST_NODES:
        raise SafeMathError("expresión demasiado compleja")

    allowed_binops = (ast.Add, ast.Sub, ast.Mult, ast.Div, ast.Pow)
    allowed_unary = (ast.UAdd, ast.USub)

    def visit(node):
        if isinstance(node, ast.Expression):
            return visit(node.body)

        if isinstance(node, ast.Constant):
            if isinstance(node.value, bool) or not isinstance(node.value, (int, float)):
                raise SafeMathError("solo se permiten números")
            value = node.value
            if not math.isfinite(float(value)) or abs(float(value)) > MATH_MAX_ABS_LITERAL:
                raise SafeMathError("número fuera de rango")
            return value

        if isinstance(node, ast.UnaryOp) and isinstance(node.op, allowed_unary):
            value = visit(node.operand)
            return +value if isinstance(node.op, ast.UAdd) else -value

        if isinstance(node, ast.BinOp) and isinstance(node.op, allowed_binops):
            left = visit(node.left)
            right = visit(node.right)

            if isinstance(node.op, ast.Add):
                result = left + right
            elif isinstance(node.op, ast.Sub):
                result = left - right
            elif isinstance(node.op, ast.Mult):
                result = left * right
            elif isinstance(node.op, ast.Div):
                if right == 0:
                    raise SafeMathError("no se puede dividir por cero")
                result = left / right
            else:  # Pow
                if abs(float(right)) > MATH_MAX_ABS_EXPONENT:
                    raise SafeMathError("exponente demasiado grande")
                # Evitar resultados complejos, por ejemplo (-4)^0.5.
                if left < 0 and not float(right).is_integer():
                    raise SafeMathError("el resultado no es un número real")
                try:
                    result = left ** right
                except (OverflowError, ValueError) as exc:
                    raise SafeMathError("resultado fuera de rango") from exc

            if isinstance(result, complex) or not math.isfinite(float(result)):
                raise SafeMathError("resultado fuera de rango")
            if abs(float(result)) > MATH_MAX_ABS_RESULT:
                raise SafeMathError("resultado demasiado grande")
            return result

        raise SafeMathError("operación no permitida")

    return visit(tree)


def _format_math_number(value: float | int) -> str:
    number = float(value)
    if abs(number) < 5e-13:
        number = 0.0
    if number.is_integer() and abs(number) < 1e21:
        return str(int(number))
    return format(number, ".12g")


def _pretty_math_expression(display_expression: str) -> str:
    text_value = display_expression.strip()
    text_value = text_value.replace("**", "^")
    text_value = text_value.replace("*", " × ").replace("/", " ÷ ")
    text_value = re.sub(r"\s+", " ", text_value).strip()
    return text_value


def _math_battle_key(message: Message) -> tuple[int, int] | None:
    user = message.from_user
    if not user or user.is_bot:
        return None
    return (int(message.chat_id), int(user.id))


def _math_battle_normalized_reply(text_value: str) -> str:
    normalized = normalize_intent(text_value or "").strip().lower()
    normalized = re.sub(r"^\s*(?:pecos|peco)\b[\s,:;-]*", "", normalized)
    normalized = re.sub(r"\s+", " ", normalized).strip(" .,!¡¿?")
    return normalized



def _math_battle_direct_challenge_requested(text_value: str) -> bool:
    """Permite iniciar la guerra matemática por petición explícita.

    Ejemplos admitidos:
      - "desafio matematico a pecos"
      - "desafío matemático a Pecos"
      - "Pecos desafio matematico"
      - "Pecos reto matematico"
      - "reto matematico a pecos"
      - "Pecos te desafio a una guerra matematica"
      - "Pecos guerra matematica"
    """
    normalized = normalize_intent(text_value or "").strip().lower()
    normalized = re.sub(r"\s+", " ", normalized)

    if not re.search(r"\bpecos?\b", normalized):
        return False

    patterns = (
        r"\bdesafio\s+matematico\b",
        r"\breto\s+matematico\b",
        r"\bguerra\s+matematica\b",
        r"\bte\s+desafio\b.*\bmatematic",
        r"\bdesafio\b.*\bpecos?\b.*\bmatematic",
        r"\bpecos?\b.*\bdesafio\b.*\bmatematic",
        r"\bpecos?\b.*\breto\b.*\bmatematic",
        r"\bpecos?\b.*\bguerra\b.*\bmatematic",
    )
    return any(re.search(pattern, normalized) for pattern in patterns)



MIRROR_SPANISH_HINTS = {
    "hola", "ola", "quien", "quién", "tiene", "tienen", "busca", "buscar",
    "necesito", "necesita", "alguien", "ayuda", "ayudar", "radio", "radios",
    "software", "programa", "programar", "cps", "kpg", "firmware", "manual",
    "pass", "password", "clave", "claves", "contrasena", "contraseña",
    "salta", "saltar", "para", "por", "favor", "gracias", "pecos", "buenas",
    "buenos", "dias", "días", "noches", "tardes", "como", "cómo", "que", "qué",
    "donde", "dónde", "cuando", "cuándo", "cuanto", "cuánto", "modelo", "kenwood",
    "motorola", "hytera", "archivo", "archivos", "tengo", "quiero", "puede",
    "puedes", "sabe", "sabes", "sirve", "funciona", "funcionar",
}


def _mirror_reverse_token(token: str) -> str:
    """Invierte solo la parte alfanumérica y conserva puntuación exterior."""
    match = re.fullmatch(r"([^A-Za-zÁÉÍÓÚÜÑáéíóúüñ0-9]*)(.*?)([^A-Za-zÁÉÍÓÚÜÑáéíóúüñ0-9]*)", token)
    if not match:
        return token

    prefix, core, suffix = match.groups()
    if not core:
        return token

    reversed_core = core[::-1]

    # El ejemplo histórico del grupo usa "Oal" para representar "Ola".
    # La inversión literal produce "laO"; normalizamos solo este saludo
    # específico para respetar la intención del usuario.
    if reversed_core.lower() == "lao":
        reversed_core = "Ola" if core[:1].isupper() else "ola"

    return prefix + reversed_core + suffix


def pecos_decode_mirror_text(text_value: str) -> str | None:
    """Intenta leer un mensaje escrito con cada palabra al revés.

    Se activa solo con evidencia suficiente para no interpretar conversaciones
    normales como "espejo".
    """
    raw = (text_value or "").strip()
    if not raw or len(raw) > 400:
        return None

    tokens = raw.split()
    if len(tokens) < 3:
        return None

    decoded_tokens = [_mirror_reverse_token(token) for token in tokens]
    decoded = " ".join(decoded_tokens)

    original_words = [
        normalize_intent(token).strip(".,;:!?¡¿()[]{}\"'").lower()
        for token in tokens
    ]
    decoded_words = [
        normalize_intent(token).strip(".,;:!?¡¿()[]{}\"'").lower()
        for token in decoded_tokens
    ]

    original_score = sum(word in MIRROR_SPANISH_HINTS for word in original_words)
    decoded_score = sum(word in MIRROR_SPANISH_HINTS for word in decoded_words)

    # Al menos 3 palabras deben volverse reconocibles y la lectura invertida
    # debe ser claramente mejor que la original.
    if decoded_score < 3:
        return None
    if decoded_score <= original_score + 1:
        return None

    return decoded


async def handle_mirror_math_challenge(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    """Lee texto invertido, bromea y desafía al autor a la guerra matemática."""
    if not message.text:
        return False

    decoded = pecos_decode_mirror_text(message.text)
    if not decoded:
        return False

    key = _math_battle_key(message)
    if key is None:
        return False

    # Si ya hay una batalla activa, no se superpone otra.
    if key in MATH_BATTLE_ACTIVE:
        await message.reply_text(
            f"🪞 Te entendí, {display_name(message)}: «{decoded}».\n"
            "😎 Bonito intento con el espejo, pero primero termina la guerra matemática que ya tenemos."
        )
        return True

    now = time.monotonic()
    MATH_BATTLE_UNKNOWN_TIMES.pop(key, None)
    MATH_BATTLE_COOLDOWN_UNTIL.pop(key, None)
    MATH_BATTLE_PENDING[key] = {
        "expires_at": now + MATH_BATTLE_ACCEPT_WINDOW_SECONDS,
        "usuario": display_name(message),
        "source": "mirror",
        "decoded": decoded,
    }

    await message.reply_text(
        f"🪞 Pecos también sabe leer al revés, {display_name(message)}.\n"
        f"Yo leo: «{decoded}».\n\n"
        "🤠 Ya que vienes jugando con el espejo, te desafío a una guerra matemática: "
        "5 rondas, sin calculadora. ¿Aceptas?"
    )
    db.add_history(
        f"TEXTO ESPEJO + DESAFIO | {display_name(message)} | "
        f"original={message.text[:180]} | decodificado={decoded[:180]}"
    )
    return True


def _math_battle_accepts(text_value: str) -> bool:
    value = _math_battle_normalized_reply(text_value)
    accepted = {
        "acepto", "aceptado", "desafio aceptado", "reto aceptado",
        "dale", "vamos", "venga", "ok", "okay", "bueno", "ya",
        "si", "sí", "de una", "hagamoslo", "hagámoslo",
    }
    return value in accepted or value.startswith("acepto ")


def _math_battle_declines(text_value: str) -> bool:
    value = _math_battle_normalized_reply(text_value)
    declined = {
        "no", "paso", "no gracias", "otro dia", "otro día",
        "despues", "después", "no acepto", "me retiro", "cancelar",
    }
    return value in declined


def _math_battle_cancel_task(state: dict) -> None:
    for key in ("timeout_task", "continue_timeout_task"):
        task = state.get(key)
        if task and not task.done():
            task.cancel()
        state[key] = None


def _math_battle_generate_question(difficulty: str) -> tuple[str, int]:
    """Genera cuentas enteras aptas para cálculo mental y las valida con el
    mismo evaluador matemático seguro de Pecos.
    """
    for _ in range(100):
        if difficulty == "Fácil":
            a = random.randint(4, 12)
            b = random.randint(3, 12)
            c = random.randint(3, 28)
            if random.choice((True, False)):
                expression = f"{a}*{b}+{c}"
            else:
                product = a * b
                c = min(c, max(1, product - 1))
                expression = f"{a}*{b}-{c}"

        elif difficulty == "Media":
            a = random.randint(8, 25)
            b = random.randint(3, 14)
            c = random.randint(3, 9)
            d = random.randint(5, 35)
            if random.choice((True, False)):
                expression = f"({a}+{b})*{c}-{d}"
            else:
                # Mantener el paréntesis positivo para cálculo mental limpio.
                if b >= a:
                    a, b = b + random.randint(3, 8), a
                expression = f"({a}-{b})*{c}+{d}"

        else:  # Difícil
            mode = random.randint(1, 3)
            if mode == 1:
                a = random.randint(11, 28)
                b = random.randint(4, 12)
                c = random.randint(3, 9)
                d = random.randint(3, 8)
                e = random.randint(5, 30)
                expression = f"({a}+{b})*{c}-{d}*{e}"
            elif mode == 2:
                a = random.randint(8, 18)
                b = random.randint(10, 24)
                c = random.randint(3, 9)
                d = random.randint(3, 9)
                e = random.randint(2, 8)
                q = random.randint(3, 14)
                expression = f"{a}*({b}-{c})+{q*e}/{e}"
            else:
                a = random.randint(8, 16)
                b = random.randint(6, 13)
                c = random.randint(4, 11)
                d = random.randint(3, 9)
                e = random.randint(5, 25)
                expression = f"{a}*{b}-{c}*{d}+{e}"

        try:
            result = _safe_math_eval(expression)
        except SafeMathError:
            continue

        if isinstance(result, float) and not float(result).is_integer():
            continue

        answer = int(result)
        # Evitar resultados negativos o absurdamente altos para este juego.
        if 0 <= answer <= 1500:
            return _pretty_math_expression(expression), answer

    # Fallback prácticamente inalcanzable.
    return "12 × 8 - 16", 80


def _math_battle_parse_answer(text_value: str) -> float | None:
    value = _math_battle_normalized_reply(text_value)
    match = re.fullmatch(
        r"(?:(?:es|da|resultado)\s+)?([+-]?\d+(?:[.,]\d+)?)",
        value,
    )
    if not match:
        return None
    try:
        return float(match.group(1).replace(",", "."))
    except ValueError:
        return None


def _math_battle_is_surrender(text_value: str) -> bool:
    value = _math_battle_normalized_reply(text_value)
    return value in {
        "no se", "no sé", "paso", "me rindo", "rindo", "ni idea",
    }


async def _math_battle_finish(bot, key: tuple[int, int]) -> None:
    state = MATH_BATTLE_ACTIVE.pop(key, None)
    if not state:
        return

    _math_battle_cancel_task(state)
    user_score = int(state.get("user_score", 0))
    pecos_score = int(state.get("pecos_score", 0))
    usuario = str(state.get("usuario") or "partner")

    if user_score > pecos_score:
        template = random.choice(MATH_BATTLE_WIN_MESSAGES)
    elif pecos_score > user_score:
        template = random.choice(MATH_BATTLE_PECOS_WIN_MESSAGES)
    else:
        template = (
            "⚔️ Empate {user_score}-{pecos_score}. Pecos propone dejarlo así "
            "antes de que alguien pida VAR matemático. 😂"
        )

    await bot.send_message(
        chat_id=key[0],
        text=template.format(
            usuario=usuario,
            user_score=user_score,
            pecos_score=pecos_score,
        ),
    )
    db.add_history(
        f"GUERRA MATEMATICA FINAL | {usuario} | chat {key[0]} | "
        f"usuario={user_score} pecos={pecos_score}"
    )


async def _math_battle_ask_round(bot, key: tuple[int, int]) -> None:
    state = MATH_BATTLE_ACTIVE.get(key)
    if not state:
        return

    round_index = int(state.get("round_index", 0))
    if round_index >= MATH_BATTLE_TOTAL_ROUNDS:
        await _math_battle_finish(bot, key)
        return

    difficulty, seconds = MATH_BATTLE_ROUNDS[round_index]
    expression, answer = _math_battle_generate_question(difficulty)

    # Token monotónico para impedir que un timeout antiguo afecte una ronda nueva.
    state["round_serial"] = int(state.get("round_serial", 0)) + 1
    serial = state["round_serial"]
    state["difficulty"] = difficulty
    state["time_limit"] = seconds
    state["expression"] = expression
    state["answer"] = answer
    state["awaiting_answer"] = False
    state["awaiting_continue"] = False
    state["continue_timeout_task"] = None

    icon = "🟢" if difficulty == "Fácil" else "🟡" if difficulty == "Media" else "🔴"
    await bot.send_message(
        chat_id=key[0],
        text=(
            f"⚔️ Guerra matemática — Ronda {round_index + 1}/{MATH_BATTLE_TOTAL_ROUNDS}\n"
            f"{icon} {difficulty} | ⏱️ {seconds} segundos\n"
            f"🧮 ¿Cuánto es {expression}?\n"
            "Sin calculadora, partner."
        ),
    )

    sent_at = time.monotonic()
    state["sent_at"] = sent_at
    state["awaiting_answer"] = True
    state["timeout_task"] = asyncio.create_task(
        _math_battle_timeout(bot, key, round_index, serial, seconds)
    )



def _math_battle_continue_requested(text_value: str) -> bool:
    value = _math_battle_normalized_reply(text_value)
    continue_words = {
        "siguiente", "continuar", "continua", "continúa",
        "vamos", "dale", "sigue", "seguimos", "otra",
        "proxima", "próxima", "proxima ronda", "próxima ronda",
    }
    return value in continue_words


async def _math_battle_continue_expiry(
    key: tuple[int, int],
    expected_round_index: int,
) -> None:
    """Cancela silenciosamente una partida abandonada tras 2 minutos."""
    try:
        await asyncio.sleep(MATH_BATTLE_CONTINUE_WINDOW_SECONDS)
    except asyncio.CancelledError:
        return

    state = MATH_BATTLE_ACTIVE.get(key)
    if not state:
        return

    if int(state.get("round_index", -1)) != expected_round_index:
        return
    if not state.get("awaiting_continue"):
        return

    usuario = str(state.get("usuario") or "partner")
    MATH_BATTLE_ACTIVE.pop(key, None)
    db.add_history(
        f"GUERRA MATEMATICA EXPIRADA EN PAUSA | {usuario} | "
        f"chat {key[0]} | ronda_siguiente={expected_round_index + 1}"
    )


async def _math_battle_timeout(
    bot,
    key: tuple[int, int],
    round_index: int,
    serial: int,
    seconds: int,
) -> None:
    try:
        await asyncio.sleep(seconds)
    except asyncio.CancelledError:
        return

    state = MATH_BATTLE_ACTIVE.get(key)
    if not state:
        return
    if int(state.get("round_index", -1)) != round_index:
        return
    if int(state.get("round_serial", -1)) != serial:
        return
    if not state.get("awaiting_answer"):
        return

    state["awaiting_answer"] = False
    state["timeout_task"] = None
    state["pecos_score"] = int(state.get("pecos_score", 0)) + 1

    next_round_index = round_index + 1
    state["round_index"] = next_round_index

    # Si era la última ronda, se cierra normalmente.
    if next_round_index >= MATH_BATTLE_TOTAL_ROUNDS:
        await bot.send_message(
            chat_id=key[0],
            text=(
                f"⏱️ Tiempo, partner. Punto para Pecos. 🤠\n"
                f"Resultado correcto: {state['answer']}.\n"
                f"Marcador: {state['usuario']} {state['user_score']} — "
                f"Pecos {state['pecos_score']}"
            ),
        )
        await asyncio.sleep(0.5)
        await _math_battle_finish(bot, key)
        return

    # En cualquier otra ronda, Pecos se detiene aquí. No vuelve a enviar
    # preguntas por sí solo hasta que EL MISMO jugador pida continuar.
    state["awaiting_continue"] = True
    state["continue_timeout_task"] = asyncio.create_task(
        _math_battle_continue_expiry(key, next_round_index)
    )

    await bot.send_message(
        chat_id=key[0],
        text=(
            f"⏱️ Tiempo, partner. Punto para Pecos. 🤠\n"
            f"Resultado correcto: {state['answer']}.\n"
            f"Marcador: {state['usuario']} {state['user_score']} — "
            f"Pecos {state['pecos_score']}\n\n"
            "▶️ Escribe «siguiente» para continuar la batalla."
        ),
    )


async def _math_battle_start(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> None:
    key = _math_battle_key(message)
    if key is None:
        return

    MATH_BATTLE_PENDING.pop(key, None)
    MATH_BATTLE_UNKNOWN_TIMES.pop(key, None)

    MATH_BATTLE_ACTIVE[key] = {
        "usuario": display_name(message),
        "round_index": 0,
        "round_serial": 0,
        "user_score": 0,
        "pecos_score": 0,
        "awaiting_answer": False,
        "awaiting_continue": False,
        "timeout_task": None,
        "continue_timeout_task": None,
    }

    await message.reply_text(
        "⚔️ Desafío aceptado. Son 5 rondas: Fácil 5 s, Media 7 s y Difícil 10 s. "
        "El punto es tuyo si respondes correcto dentro del tiempo; si fallas o se acaba el reloj, es para Pecos. 🤠"
    )
    await asyncio.sleep(0.5)
    await _math_battle_ask_round(context.bot, key)


async def handle_math_battle_message(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    """Gestiona aceptación, respuestas y cancelación de una guerra matemática."""
    key = _math_battle_key(message)
    if key is None:
        return False

    text_value = message.text or message.caption or ""
    now = time.monotonic()

    # Activación explícita: no obliga al usuario a provocar tres respuestas
    # desconocidas primero. Si llama a Pecos y pide un desafío/reto/guerra
    # matemática, la batalla comienza inmediatamente.
    if _math_battle_direct_challenge_requested(text_value):
        if key in MATH_BATTLE_ACTIVE:
            active_state = MATH_BATTLE_ACTIVE[key]
            if active_state.get("awaiting_continue"):
                await message.reply_text(
                    "⚔️ Partner, esa guerra sigue abierta. "
                    "Escribe «siguiente» para pasar a la próxima ronda. 😎"
                )
            else:
                await message.reply_text(
                    "⚔️ Partner, ya estamos en plena guerra matemática. "
                    "Primero responde la ronda actual. 😎"
                )
            return True

        MATH_BATTLE_PENDING.pop(key, None)
        MATH_BATTLE_UNKNOWN_TIMES.pop(key, None)
        MATH_BATTLE_COOLDOWN_UNTIL.pop(key, None)

        await _math_battle_start(message, context)
        db.add_history(
            f"GUERRA MATEMATICA INICIO DIRECTO | "
            f"{display_name(message)} | chat {message.chat_id}"
        )
        return True

    state = MATH_BATTLE_ACTIVE.get(key)
    if state:
        normalized = _math_battle_normalized_reply(text_value)
        if normalized in {"cancelar", "terminar", "fin", "me retiro", "abandono"}:
            _math_battle_cancel_task(state)
            MATH_BATTLE_ACTIVE.pop(key, None)
            await message.reply_text(
                "🏳️ Guerra matemática terminada. Pecos guarda el ábaco y volvemos a los radios. 🤠"
            )
            return True

        # Después de agotar el tiempo, Pecos NO lanza otra ronda solo.
        # Únicamente el mismo jugador puede reanudar escribiendo "siguiente"
        # (o una variante equivalente). Si no lo hace en 2 minutos, la partida
        # desaparece silenciosamente.
        if state.get("awaiting_continue"):
            if _math_battle_continue_requested(text_value):
                task = state.get("continue_timeout_task")
                if task and not task.done():
                    task.cancel()
                state["continue_timeout_task"] = None
                state["awaiting_continue"] = False
                await _math_battle_ask_round(context.bot, key)
                return True

            # Si manda una respuesta numérica tardía, aclaramos que esa ronda
            # ya terminó, pero no iniciamos otra.
            if _math_battle_parse_answer(text_value) is not None:
                await message.reply_text(
                    "⏱️ Esa ronda ya cerró, partner. "
                    "Escribe «siguiente» si quieres continuar."
                )
                return True

            return False

        if not state.get("awaiting_answer"):
            return False

        parsed = _math_battle_parse_answer(text_value)
        surrendered = _math_battle_is_surrender(text_value)
        if parsed is None and not surrendered:
            return False

        _math_battle_cancel_task(state)
        state["awaiting_answer"] = False

        elapsed = max(0.0, now - float(state.get("sent_at", now)))
        limit = float(state.get("time_limit", 0))
        correct = (parsed is not None and abs(parsed - float(state["answer"])) < 1e-9)
        round_index = int(state.get("round_index", 0))

        if elapsed > limit:
            state["pecos_score"] = int(state.get("pecos_score", 0)) + 1
            if correct:
                result_text = (
                    f"😏 Correcto… pero fuera de tiempo ({elapsed:.1f} s). "
                    "Eso huele a calculadora, partner. Punto para Pecos."
                )
            else:
                result_text = (
                    f"⏱️ Llegó después del límite de {int(limit)} s. "
                    f"Punto para Pecos. Resultado: {state['answer']}."
                )
        elif correct:
            state["user_score"] = int(state.get("user_score", 0)) + 1
            result_text = (
                f"✅ Correcto en {elapsed:.1f} s. Punto para {state['usuario']}. "
                "No te emociones, partner. 😎"
            )
        else:
            state["pecos_score"] = int(state.get("pecos_score", 0)) + 1
            if surrendered:
                result_text = (
                    f"🏳️ Pasas la ronda. Punto para Pecos. Resultado correcto: {state['answer']}."
                )
            else:
                result_text = (
                    f"❌ No, partner. El resultado era {state['answer']}. Punto para Pecos. 🤠"
                )

        await message.reply_text(
            result_text
            + "\n"
            + f"Marcador: {state['usuario']} {state['user_score']} — Pecos {state['pecos_score']}"
        )

        state["round_index"] = round_index + 1
        await asyncio.sleep(0.8)
        await _math_battle_ask_round(context.bot, key)
        return True

    pending = MATH_BATTLE_PENDING.get(key)
    if pending:
        if now > float(pending.get("expires_at", 0)):
            MATH_BATTLE_PENDING.pop(key, None)
            return False

        if _math_battle_accepts(text_value):
            await _math_battle_start(message, context)
            return True

        if _math_battle_declines(text_value):
            pending_source = str(pending.get("source") or "")
            MATH_BATTLE_PENDING.pop(key, None)

            if pending_source == "mirror":
                await message.reply_text(
                    "🐔 Jajaja… mucho mensaje en espejo, pero para las matemáticas "
                    "salió cobarde el partner. Pecos toma nota. 🤠"
                )
            else:
                await message.reply_text(
                    "🤠 Trato hecho. Pecos guarda el desafío y volvemos al tema de los radios."
                )
            return True

    return False


async def maybe_offer_math_battle(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    """Ofrece una batalla tras 3 preguntas desconocidas en 10 minutos.

    Solo se llama desde el fallback de preguntas dirigidas a Pecos; por eso no
    cuentan búsquedas técnicas, cálculos válidos ni conversaciones normales.
    """
    key = _math_battle_key(message)
    if key is None:
        return False

    now = time.monotonic()
    if key in MATH_BATTLE_ACTIVE or key in MATH_BATTLE_PENDING:
        return False
    if now < float(MATH_BATTLE_COOLDOWN_UNTIL.get(key, 0.0)):
        return False

    recent = [
        ts for ts in MATH_BATTLE_UNKNOWN_TIMES.get(key, [])
        if now - ts <= MATH_BATTLE_TRIGGER_WINDOW_SECONDS
    ]
    recent.append(now)
    MATH_BATTLE_UNKNOWN_TIMES[key] = recent

    if len(recent) < MATH_BATTLE_TRIGGER_COUNT:
        return False

    MATH_BATTLE_UNKNOWN_TIMES[key] = []
    MATH_BATTLE_COOLDOWN_UNTIL[key] = now + MATH_BATTLE_OFFER_COOLDOWN_SECONDS
    MATH_BATTLE_PENDING[key] = {
        "expires_at": now + MATH_BATTLE_ACCEPT_WINDOW_SECONDS,
        "usuario": display_name(message),
    }

    template = random.choice(MATH_BATTLE_OFFER_MESSAGES)
    await message.reply_text(template.format(usuario=display_name(message)))
    db.add_history(
        f"GUERRA MATEMATICA OFRECIDA | {display_name(message)} | chat {message.chat_id}"
    )
    return True




ADVANCED_MATH_KEYWORDS = (
    "integral", "integra", "integrar",
    "derivada", "deriva", "derivar",
    "seno", "coseno", "tangente",
    "logaritmo", "log base", "ln ",
    "factorial", "combinaciones", "combinacion",
    "permutaciones", "permutacion",
    "ecuacion", "ecuación",
    "raiz cubica", "raiz cuarta", "valor absoluto",
    "e elevado", "pi elevado",
    "sucesion aritmetica", "progresion aritmetica",
    "sucesiones aritmeticas", "progresiones aritmeticas",
    "termino general", "diferencia comun",
)


def _advanced_math_clean_text(text_value: str) -> str:
    raw = normalize_intent(text_value or "").lower()

    for alias in sorted(PECOS_USERNAME_ALIASES, key=len, reverse=True):
        alias_norm = normalize_intent(alias).lower().lstrip("@")
        if alias_norm:
            raw = re.sub(
                rf"(?<![a-z0-9_])@?{re.escape(alias_norm)}(?![a-z0-9_])",
                " ",
                raw,
            )

    raw = re.sub(
        r"(?<![a-z0-9_])(?:pecos|peco)(?![a-z0-9_])",
        " ",
        raw,
    )
    raw = raw.strip(" \t\r\n?¿!¡=.;:,")
    raw = re.sub(
        r"^\s*(?:"
        r"dime\s+|"
        r"me\s+dices\s+|"
        r"me\s+puedes\s+decir\s+|"
        r"cuanto\s+es\s+|"
        r"cual\s+es\s+|"
        r"calcula\s+|calcular\s+|"
        r"resuelve\s+|resolver\s+"
        r")",
        "",
        raw,
    )
    return re.sub(r"\s+", " ", raw).strip()


def _advanced_math_intent(text_value: str) -> bool:
    if not text_value:
        return False

    normalized = normalize_intent(text_value).lower()
    directed = text_mentions_pecos(text_value)

    if directed and any(word in normalized for word in ADVANCED_MATH_KEYWORDS):
        return True

    # También permitir "Pecos resuelve 2x+5=17".
    if directed and "=" in text_value and re.search(r"\bx\b", normalized):
        return True

    return False


def _fraction_from_text(value: str) -> Fraction:
    return Fraction(value.replace(",", "."))


def _format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _format_symbolic_term(
    coeff: Fraction,
    power: int,
    *,
    first: bool,
) -> str:
    if coeff == 0:
        return ""

    sign = "-" if coeff < 0 else "+"
    abs_coeff = abs(coeff)

    if power == 0:
        body = _format_fraction(abs_coeff)
    else:
        if abs_coeff == 1:
            coeff_text = ""
        else:
            coeff_text = _format_fraction(abs_coeff)

        if power == 1:
            var = "x"
        else:
            var = f"x^{power}"

        if coeff_text:
            body = f"{coeff_text}{var}"
        else:
            body = var

    if first:
        return f"-{body}" if sign == "-" else body
    return f" {sign} {body}"


def _format_polynomial(coeffs: dict[int, Fraction]) -> str:
    parts: list[str] = []
    first = True
    for power in sorted(coeffs.keys(), reverse=True):
        coeff = coeffs[power]
        if coeff == 0:
            continue
        term = _format_symbolic_term(coeff, power, first=first)
        if term:
            parts.append(term)
            first = False
    return "".join(parts) if parts else "0"


def _parse_polynomial(expression: str) -> dict[int, Fraction] | None:
    """Parser conservador para polinomios reales en x de grado <= 12.

    Acepta:
      x
      x^2
      3x^2 + 2x - 5
      4*x^3 - x
      constantes
    """
    expr = normalize_intent(expression or "").lower()
    expr = expr.replace("−", "-").replace("×", "*")
    expr = re.sub(r"\s+", "", expr)
    expr = re.sub(r"(?<=\d),(?=\d)", ".", expr)

    # Frases comunes.
    expr = re.sub(r"\belevadoala\b", "^", expr)
    expr = re.sub(r"\belevadoa\b", "^", expr)
    expr = expr.replace("alcuadrado", "^2")
    expr = expr.replace("alcubo", "^3")

    if not expr or len(expr) > 160:
        return None

    # No aceptar funciones dentro del parser polinómico.
    if re.search(r"[a-wyz_]", expr):
        return None

    # Normalizar signos para dividir términos.
    if expr[0] not in "+-":
        expr = "+" + expr

    terms = re.findall(r"[+-][^+-]+", expr)
    if not terms or "".join(terms) != expr:
        return None

    result: dict[int, Fraction] = {}

    for term in terms:
        sign = -1 if term[0] == "-" else 1
        body = term[1:]

        if "x" not in body:
            try:
                coeff = Fraction(body) * sign
            except Exception:
                return None
            result[0] = result.get(0, Fraction(0)) + coeff
            continue

        match = re.fullmatch(
            r"(?:(\d+(?:\.\d+)?)\*?)?x(?:\^(\d{1,2}))?",
            body,
        )
        if not match:
            return None

        coeff_text, power_text = match.groups()
        coeff = Fraction(coeff_text) if coeff_text else Fraction(1)
        coeff *= sign
        power = int(power_text) if power_text else 1
        if power > 12:
            return None
        result[power] = result.get(power, Fraction(0)) + coeff

    return result


def _differentiate_polynomial(coeffs: dict[int, Fraction]) -> dict[int, Fraction]:
    out: dict[int, Fraction] = {}
    for power, coeff in coeffs.items():
        if power == 0:
            continue
        out[power - 1] = out.get(power - 1, Fraction(0)) + coeff * power
    return out


def _integrate_polynomial(coeffs: dict[int, Fraction]) -> dict[int, Fraction]:
    out: dict[int, Fraction] = {}
    for power, coeff in coeffs.items():
        new_power = power + 1
        out[new_power] = out.get(new_power, Fraction(0)) + coeff / new_power
    return out



def _arithmetic_sequence_intent(text_value: str) -> bool:
    normalized = normalize_intent(text_value or "").lower()
    return bool(
        re.search(
            r"\b(?:sucesion(?:es)?|progresion(?:es)?)\s+aritmetica(?:s)?\b",
            normalized,
        )
        or re.search(r"\btermino\s+general\b", normalized)
        or re.search(r"\bdiferencia\s+comun\b", normalized)
    )


def _extract_arithmetic_sequence_terms(
    text_value: str,
) -> list[tuple[int, Fraction]]:
    """Extrae notaciones como a3=11, a_3=11 o a 3 = 11."""
    normalized = normalize_intent(text_value or "").lower()
    matches = re.findall(
        r"(?<![a-z0-9_])a\s*_?\s*(\d{1,5})\s*(?:=|vale|es)\s*([+-]?\d+(?:[.,]\d+)?)",
        normalized,
    )

    found: dict[int, Fraction] = {}
    for index_text, value_text in matches:
        index = int(index_text)
        if index < 1:
            continue
        value = Fraction(value_text.replace(",", "."))
        found[index] = value

    return sorted(found.items())



def _extract_arithmetic_sequence_named_values(
    text_value: str,
) -> list[tuple[int, Fraction]]:
    """Acepta respuestas tipo: m=3, am=11, k=8, ak=31."""
    normalized = normalize_intent(text_value or "").lower()
    compact = re.sub(r"\s+", "", normalized)

    m_idx = re.search(r"(?<![a-z0-9_])m\s*=\s*(\d{1,5})", normalized)
    k_idx = re.search(r"(?<![a-z0-9_])k\s*=\s*(\d{1,5})", normalized)

    am_val = re.search(
        r"(?<![a-z0-9_])a\s*_?\s*m\s*=\s*([+-]?\d+(?:[.,]\d+)?)",
        normalized,
    )
    ak_val = re.search(
        r"(?<![a-z0-9_])a\s*_?\s*k\s*=\s*([+-]?\d+(?:[.,]\d+)?)",
        normalized,
    )

    # También aceptar am=11 / ak=31 sin espacio.
    if not am_val:
        am_val = re.search(r"(?<![a-z0-9_])am\s*=\s*([+-]?\d+(?:[.,]\d+)?)", normalized)
    if not ak_val:
        ak_val = re.search(r"(?<![a-z0-9_])ak\s*=\s*([+-]?\d+(?:[.,]\d+)?)", normalized)

    if not (m_idx and k_idx and am_val and ak_val):
        return []

    m = int(m_idx.group(1))
    k = int(k_idx.group(1))
    if m < 1 or k < 1 or m == k:
        return []

    a_m = Fraction(am_val.group(1).replace(",", "."))
    a_k = Fraction(ak_val.group(1).replace(",", "."))

    return sorted(((m, a_m), (k, a_k)))


def _arithmetic_sequence_pending_key(message: Message) -> tuple[int, int] | None:
    user = message.from_user
    if not user or user.is_bot:
        return None
    return (int(message.chat_id), int(user.id))


def _arithmetic_sequence_pending_active(
    message: Message,
) -> dict | None:
    key = _arithmetic_sequence_pending_key(message)
    if key is None:
        return None

    state = ARITH_SEQUENCE_PENDING.get(key)
    if not state:
        return None

    if time.monotonic() > float(state.get("expires_at", 0)):
        ARITH_SEQUENCE_PENDING.pop(key, None)
        return None

    return state


def _arithmetic_sequence_reply_has_values(text_value: str) -> bool:
    return bool(
        len(_extract_arithmetic_sequence_terms(text_value)) >= 2
        or len(_extract_arithmetic_sequence_named_values(text_value)) >= 2
        or (
            len(_extract_arithmetic_sequence_terms(text_value)) >= 1
            and re.search(
                r"(?<![a-z0-9_])d\s*=\s*[+-]?\d+(?:[.,]\d+)?",
                normalize_intent(text_value or "").lower(),
            )
        )
    )


def _arithmetic_sequence_symbolic_request(text_value: str) -> bool:
    """Detecta la pregunta genérica con a_m y a_k, sin valores numéricos."""
    normalized = normalize_intent(text_value or "").lower()
    compact = re.sub(r"\s+", "", normalized)

    has_am = bool(re.search(r"\ba\s*_?\s*m\b", normalized)) or "am" in compact
    has_ak = bool(re.search(r"\ba\s*_?\s*k\b", normalized)) or "ak" in compact
    has_an = bool(re.search(r"\ba\s*_?\s*n\b", normalized)) or "an" in compact

    return (
        _arithmetic_sequence_intent(text_value)
        and has_am
        and has_ak
        and has_an
    )


def _format_arithmetic_general_term(
    d: Fraction,
    intercept: Fraction,
) -> str:
    """Formatea a_n = d*n + b usando fracciones exactas."""
    parts: list[str] = ["a_n = "]

    if d == 0:
        parts.append(_format_fraction(intercept))
        return "".join(parts)

    # término con n
    if d == 1:
        parts.append("n")
    elif d == -1:
        parts.append("-n")
    else:
        parts.append(f"{_format_fraction(d)}n")

    # término independiente
    if intercept > 0:
        parts.append(f" + {_format_fraction(intercept)}")
    elif intercept < 0:
        parts.append(f" - {_format_fraction(abs(intercept))}")

    return "".join(parts)


def _handle_arithmetic_sequence_math(text_value: str) -> tuple[str, bool] | None:
    """Resuelve sucesiones/progresiones aritméticas a partir de dos términos.

    Devuelve (respuesta, solved). También responde la fórmula simbólica general.
    """
    if not _arithmetic_sequence_intent(text_value):
        return None

    # Caso teórico/simbólico: a_m y a_k, m < k.
    # Si pide "calcular/resolver/hallar" pero no entrega valores, Pecos los solicita.
    if _arithmetic_sequence_symbolic_request(text_value):
        normalized_request = normalize_intent(text_value or "").lower()
        wants_calculation = bool(
            re.search(r"\b(?:calcula(?:r)?|resuelve|resolver|halla(?:r)?|determina(?:r)?)\b", normalized_request)
        )
        if wants_calculation:
            return (
                "🧮 Puedo calcularlo, pero me faltan los valores.\n"
                "Envíame m, a_m, k y a_k. Por ejemplo:\n"
                "m=3, am=11, k=8, ak=31\n"
                "o simplemente: a3=11 y a8=31.",
                False,
            )

        return (
            "🧮 Para una sucesión aritmética, si conoces a_m y a_k con m < k:\n"
            "d = (a_k - a_m) / (k - m)\n"
            "a_n = a_m + (n - m)d\n"
            "Por tanto:\n"
            "a_n = a_m + (n - m)(a_k - a_m)/(k - m)",
            True,
        )

    terms = _extract_arithmetic_sequence_terms(text_value)
    if len(terms) < 2:
        named_terms = _extract_arithmetic_sequence_named_values(text_value)
        if len(named_terms) >= 2:
            terms = named_terms

    # También aceptar a1 + diferencia d.
    normalized = normalize_intent(text_value or "").lower()
    d_match = re.search(
        r"(?<![a-z0-9_])d\s*=\s*([+-]?\d+(?:[.,]\d+)?)",
        normalized,
    )

    if len(terms) >= 2:
        # Usar los dos primeros índices distintos en orden.
        (m, a_m), (k, a_k) = terms[0], terms[1]

        if m == k:
            return (
                "🧮 Necesito dos términos con índices distintos para calcular la diferencia común.",
                False,
            )

        if m > k:
            m, k = k, m
            a_m, a_k = a_k, a_m

        d = (a_k - a_m) / Fraction(k - m)
        intercept = a_m - d * m

        # Verificar si el usuario pide un término concreto.
        target_index = None
        target_patterns = (
            r"\ba\s*_?\s*(\d{1,5})\s*\?",
            r"\bcalcula(?:r)?\s+a\s*_?\s*(\d{1,5})\b",
            r"\bhalla(?:r)?\s+a\s*_?\s*(\d{1,5})\b",
            r"\btermino\s+(\d{1,5})\b",
        )
        for pattern in target_patterns:
            tm = re.search(pattern, normalized)
            if tm:
                candidate = int(tm.group(1))
                if candidate not in {m, k}:
                    target_index = candidate
                    break

        lines = [
            f"🧮 Datos: a_{m} = {_format_fraction(a_m)}, a_{k} = {_format_fraction(a_k)}",
            f"d = (a_{k} - a_{m}) / ({k} - {m}) = {_format_fraction(d)}",
            f"✅ Término general: {_format_arithmetic_general_term(d, intercept)}",
        ]

        if target_index is not None and target_index >= 1:
            target_value = d * target_index + intercept
            lines.append(
                f"📌 a_{target_index} = {_format_fraction(target_value)}"
            )

        return ("\n".join(lines), True)

    if len(terms) == 1 and d_match:
        n0, a_n0 = terms[0]
        d = Fraction(d_match.group(1).replace(",", "."))
        intercept = a_n0 - d * n0

        return (
            "\n".join(
                [
                    f"🧮 Datos: a_{n0} = {_format_fraction(a_n0)}, d = {_format_fraction(d)}",
                    f"✅ Término general: {_format_arithmetic_general_term(d, intercept)}",
                ]
            ),
            True,
        )

    return (
        "🧮 Me faltan datos para resolverla, partner. Envíame dos términos de la sucesión, por ejemplo:\n"
        "a3=11 y a8=31\n"
        "También acepto: m=3, am=11, k=8, ak=31\n"
        "o un término y la diferencia común: a3=11, d=4.",
        False,
    )


def _advanced_math_symbolic(text_value: str) -> tuple[str, str] | None:
    """Devuelve (respuesta, tipo) para cálculo simbólico conocido."""
    query = _advanced_math_clean_text(text_value)

    # -------------------------------
    # INTEGRALES INDEFINIDAS
    # -------------------------------
    m = re.search(r"\b(?:la\s+)?(?:integral|integra|integrar)\s+(?:de\s+)?(.+)$", query)
    if m:
        expr = m.group(1).strip()
        expr_compact = re.sub(r"\s+", "", expr)

        # e elevado a la x / e^x
        if re.fullmatch(
            r"(?:e\^x|eelevadoalax|eelevadoax|e\*\*x)",
            expr_compact,
        ):
            return (
                "🧮 ∫ e^x dx = e^x + C\n"
                "📘 Porque la derivada de e^x es nuevamente e^x. "
                "C es la constante de integración.",
                "integral",
            )

        if re.fullmatch(r"(?:sen(?:o)?(?:de)?x|sin(?:de)?x)", expr_compact):
            return (
                "🧮 ∫ sen(x) dx = -cos(x) + C",
                "integral",
            )

        if re.fullmatch(r"(?:cos(?:eno)?(?:de)?x|cos(?:de)?x)", expr_compact):
            return (
                "🧮 ∫ cos(x) dx = sen(x) + C",
                "integral",
            )

        if re.fullmatch(r"(?:1/x|x\^-1)", expr_compact):
            return (
                "🧮 ∫ 1/x dx = ln|x| + C",
                "integral",
            )

        # Polinomios simples.
        coeffs = _parse_polynomial(expr)
        if coeffs is not None:
            integrated = _format_polynomial(_integrate_polynomial(coeffs))
            source = _format_polynomial(coeffs)
            return (
                f"🧮 ∫ ({source}) dx = {integrated} + C",
                "integral",
            )

        return (
            "🧮 Pecos reconoce que es una integral, pero esa forma todavía "
            "queda fuera del motor simbólico seguro. Mejor no inventar una solución.",
            "unsupported",
        )

    # -------------------------------
    # DERIVADAS
    # -------------------------------
    m = re.search(r"\b(?:la\s+)?(?:derivada|deriva|derivar)\s+(?:de\s+)?(.+)$", query)
    if m:
        expr = m.group(1).strip()
        expr_compact = re.sub(r"\s+", "", expr)

        if re.fullmatch(
            r"(?:e\^x|eelevadoalax|eelevadoax|e\*\*x)",
            expr_compact,
        ):
            return ("🧮 d/dx (e^x) = e^x", "derivative")

        if re.fullmatch(r"(?:sen(?:o)?(?:de)?x|sin(?:de)?x)", expr_compact):
            return ("🧮 d/dx [sen(x)] = cos(x)", "derivative")

        if re.fullmatch(r"(?:cos(?:eno)?(?:de)?x|cos(?:de)?x)", expr_compact):
            return ("🧮 d/dx [cos(x)] = -sen(x)", "derivative")

        if re.fullmatch(r"(?:ln(?:de)?x|logaritmonatural(?:de)?x)", expr_compact):
            return ("🧮 d/dx [ln(x)] = 1/x", "derivative")

        coeffs = _parse_polynomial(expr)
        if coeffs is not None:
            derivative = _format_polynomial(_differentiate_polynomial(coeffs))
            source = _format_polynomial(coeffs)
            return (
                f"🧮 d/dx ({source}) = {derivative}",
                "derivative",
            )

        return (
            "🧮 Pecos reconoce que es una derivada, pero esa forma todavía "
            "queda fuera del motor simbólico seguro. Mejor no inventar una solución.",
            "unsupported",
        )

    return None


def _advanced_math_numeric(text_value: str) -> tuple[str, float | int] | None:
    query = _advanced_math_clean_text(text_value)
    number = r"([+-]?\d+(?:[.,]\d+)?)"

    # Trigonometría.
    trig_specs = (
        ("seno", math.sin),
        ("sen", math.sin),
        ("coseno", math.cos),
        ("cos", math.cos),
        ("tangente", math.tan),
        ("tan", math.tan),
    )
    for label, func in trig_specs:
        m = re.fullmatch(
            rf"(?:el\s+)?{label}\s+(?:de\s+)?{number}(?:\s*(grados?|radianes?))?",
            query,
        )
        if m:
            raw_n = float(m.group(1).replace(",", "."))
            unit = (m.group(2) or "radianes").lower()
            angle = math.radians(raw_n) if unit.startswith("grado") else raw_n

            if label in {"tangente", "tan"} and unit.startswith("grado"):
                # Evitar reportar un número enorme cerca de 90° + k180°.
                normalized_angle = ((raw_n - 90.0) % 180.0)
                if min(normalized_angle, 180.0 - normalized_angle) < 1e-10:
                    raise SafeMathError("la tangente no está definida en ese ángulo")

            value = func(angle)
            return (
                f"{label}({raw_n:g} {'°' if unit.startswith('grado') else 'rad'})",
                value,
            )

    # Logaritmo base 10.
    m = re.fullmatch(rf"(?:logaritmo|log)\s+(?:de\s+)?{number}", query)
    if m:
        n = float(m.group(1).replace(",", "."))
        if n <= 0:
            raise SafeMathError("el logaritmo requiere un número positivo")
        return (f"log10({n:g})", math.log10(n))

    # Logaritmo con base.
    m = re.fullmatch(
        rf"(?:logaritmo|log)\s+base\s+{number}\s+de\s+{number}",
        query,
    )
    if m:
        base = float(m.group(1).replace(",", "."))
        n = float(m.group(2).replace(",", "."))
        if n <= 0 or base <= 0 or abs(base - 1.0) < 1e-15:
            raise SafeMathError("base o argumento inválido para el logaritmo")
        return (f"log base {base:g} de {n:g}", math.log(n, base))

    # Logaritmo natural.
    m = re.fullmatch(
        rf"(?:ln|logaritmo\s+natural)\s+(?:de\s+)?{number}",
        query,
    )
    if m:
        n = float(m.group(1).replace(",", "."))
        if n <= 0:
            raise SafeMathError("ln requiere un número positivo")
        return (f"ln({n:g})", math.log(n))

    # Factorial.
    m = re.fullmatch(r"factorial\s+(?:de\s+)?(\d{1,4})", query)
    if m:
        n = int(m.group(1))
        if n > 170:
            raise SafeMathError("factorial demasiado grande para este bot")
        return (f"{n}!", math.factorial(n))

    # Combinaciones n en r.
    m = re.fullmatch(
        r"(?:combinaciones|combinacion)\s+(?:de\s+)?(\d{1,5})\s+(?:en|tomados?\s+de)\s+(\d{1,5})",
        query,
    )
    if m:
        n, r = int(m.group(1)), int(m.group(2))
        if r > n or n > 100000:
            raise SafeMathError("valores inválidos para combinaciones")
        return (f"C({n},{r})", math.comb(n, r))

    # Permutaciones nPr.
    m = re.fullmatch(
        r"(?:permutaciones|permutacion)\s+(?:de\s+)?(\d{1,5})\s+(?:en|tomados?\s+de)\s+(\d{1,5})",
        query,
    )
    if m:
        n, r = int(m.group(1)), int(m.group(2))
        if r > n or n > 100000:
            raise SafeMathError("valores inválidos para permutaciones")
        return (f"P({n},{r})", math.perm(n, r))

    # Valor absoluto.
    m = re.fullmatch(rf"valor\s+absoluto\s+(?:de\s+)?{number}", query)
    if m:
        n = float(m.group(1).replace(",", "."))
        return (f"|{n:g}|", abs(n))

    # Raíz cúbica/cuarta/enésima.
    m = re.fullmatch(rf"raiz\s+cubica\s+(?:de\s+)?{number}", query)
    if m:
        n = float(m.group(1).replace(",", "."))
        value = math.copysign(abs(n) ** (1 / 3), n)
        return (f"∛{n:g}", value)

    m = re.fullmatch(rf"raiz\s+cuarta\s+(?:de\s+)?{number}", query)
    if m:
        n = float(m.group(1).replace(",", "."))
        if n < 0:
            raise SafeMathError("la raíz cuarta real requiere un número no negativo")
        return (f"⁴√{n:g}", n ** 0.25)

    m = re.fullmatch(rf"raiz\s+(\d{{1,2}})\s+de\s+{number}", query)
    if m:
        degree = int(m.group(1))
        n = float(m.group(2).replace(",", "."))
        if degree < 2 or degree > 20:
            raise SafeMathError("grado de raíz fuera de rango")
        if n < 0 and degree % 2 == 0:
            raise SafeMathError("una raíz par real requiere un número no negativo")
        value = math.copysign(abs(n) ** (1 / degree), n) if n < 0 else n ** (1 / degree)
        return (f"raíz {degree} de {n:g}", value)

    # Potencia en lenguaje natural.
    m = re.fullmatch(
        rf"{number}\s+elevado\s+a(?:\s+la)?\s+{number}",
        query,
    )
    if m:
        base = float(m.group(1).replace(",", "."))
        exponent = float(m.group(2).replace(",", "."))
        if abs(exponent) > MATH_MAX_ABS_EXPONENT:
            raise SafeMathError("exponente demasiado grande")
        if base < 0 and not exponent.is_integer():
            raise SafeMathError("el resultado no es un número real")
        result = base ** exponent
        if not math.isfinite(float(result)):
            raise SafeMathError("resultado fuera de rango")
        return (f"{base:g}^{exponent:g}", result)

    return None


def _advanced_math_equation(text_value: str) -> str | None:
    query = _advanced_math_clean_text(text_value)
    if "=" not in query or "x" not in query:
        return None

    # Quitar la palabra ecuación si aparece.
    query = re.sub(r"^\s*(?:ecuacion\s+)?", "", query)
    if query.count("=") != 1:
        return None

    left_text, right_text = [part.strip() for part in query.split("=", 1)]
    left = _parse_polynomial(left_text)
    right = _parse_polynomial(right_text)
    if left is None or right is None:
        return None

    coeffs: dict[int, Fraction] = {}
    for power, coeff in left.items():
        coeffs[power] = coeffs.get(power, Fraction(0)) + coeff
    for power, coeff in right.items():
        coeffs[power] = coeffs.get(power, Fraction(0)) - coeff

    # Limpiar ceros.
    coeffs = {p: c for p, c in coeffs.items() if c != 0}
    if not coeffs:
        return "🧮 La ecuación es una identidad: se cumple para cualquier x."

    degree = max(coeffs)
    if degree == 0:
        return "🧮 La ecuación es incompatible: no tiene solución."

    if degree == 1:
        a = coeffs.get(1, Fraction(0))
        b = coeffs.get(0, Fraction(0))
        if a == 0:
            return None
        x = -b / a
        return f"🧮 Solución: x = {_format_fraction(x)}"

    if degree == 2:
        a = float(coeffs.get(2, Fraction(0)))
        b = float(coeffs.get(1, Fraction(0)))
        c = float(coeffs.get(0, Fraction(0)))
        if abs(a) < 1e-15:
            return None

        disc = b * b - 4 * a * c
        if disc > 1e-12:
            root = math.sqrt(disc)
            x1 = (-b + root) / (2 * a)
            x2 = (-b - root) / (2 * a)
            return (
                "🧮 Ecuación cuadrática:\n"
                f"x₁ = {_format_math_number(x1)}\n"
                f"x₂ = {_format_math_number(x2)}"
            )

        if abs(disc) <= 1e-12:
            x = -b / (2 * a)
            return f"🧮 Raíz doble: x = {_format_math_number(x)}"

        real = -b / (2 * a)
        imag = math.sqrt(-disc) / abs(2 * a)
        sign = "+" if imag >= 0 else "-"
        return (
            "🧮 No tiene raíces reales. En números complejos:\n"
            f"x₁ = {_format_math_number(real)} + {_format_math_number(abs(imag))}i\n"
            f"x₂ = {_format_math_number(real)} - {_format_math_number(abs(imag))}i"
        )

    return (
        "🧮 Pecos reconoce la ecuación, pero por seguridad automática "
        "solo resuelve ecuaciones polinómicas de primer y segundo grado."
    )


async def handle_advanced_math(message: Message) -> bool:
    """Matemática avanzada sin SymPy ni ejecución dinámica de código."""
    user = message.from_user
    if not user or user.is_bot:
        return False

    text_value = message.text or message.caption or ""
    pending_sequence = _arithmetic_sequence_pending_active(message)

    # Si Pecos pidió datos previamente, el mismo usuario puede responder solo
    # con los valores, sin volver a escribir "Pecos" ni "sucesión aritmética".
    if pending_sequence is not None and _arithmetic_sequence_reply_has_values(text_value):
        original_request = str(pending_sequence.get("original_request") or "")
        combined_text = f"sucesion aritmetica {original_request} {text_value}"
        key = _arithmetic_sequence_pending_key(message)
        if key is not None:
            ARITH_SEQUENCE_PENDING.pop(key, None)
        text_value = combined_text
    elif not _advanced_math_intent(text_value):
        return False

    response: str | None = None
    solved = False

    try:
        arithmetic_sequence = _handle_arithmetic_sequence_math(text_value)
        if arithmetic_sequence is not None:
            response, solved = arithmetic_sequence

            # Si faltan valores, Pecos queda esperando la respuesta del mismo
            # usuario durante 5 minutos. No consume el cálculo diario.
            if not solved and _arithmetic_sequence_intent(text_value):
                key = _arithmetic_sequence_pending_key(message)
                if key is not None:
                    ARITH_SEQUENCE_PENDING[key] = {
                        "expires_at": time.monotonic() + ARITH_SEQUENCE_PENDING_SECONDS,
                        "original_request": message.text or message.caption or text_value,
                    }
        else:
            symbolic = _advanced_math_symbolic(text_value)
            if symbolic is not None:
                response, kind = symbolic
                solved = kind != "unsupported"
            else:
                equation = _advanced_math_equation(text_value)
                if equation is not None:
                    response = equation
                    solved = not equation.startswith("🧮 Pecos reconoce")
                else:
                    numeric = _advanced_math_numeric(text_value)
                    if numeric is not None:
                        label, result = numeric
                        response = f"🧮 {label} = {_format_math_number(result)}"
                        solved = True
    except SafeMathError as exc:
        await message.reply_text(
            f"🧮 Esa operación avanzada no me cuadra, {display_name(message)}: {exc}."
        )
        return True
    except (OverflowError, ValueError, ZeroDivisionError):
        await message.reply_text(
            f"🧮 Esa operación avanzada quedó fuera de rango, {display_name(message)}."
        )
        return True

    if response is None:
        await message.reply_text(
            "🧮 Pecos reconoce una consulta de matemática avanzada, pero esa forma "
            "todavía no está implementada con suficiente seguridad. Mejor no inventar."
        )
        return True

    # Solo una solución matemática directa por usuario y por día.
    # Si la consulta fue reconocida pero no resoluble, NO consume el cupo.
    if solved:
        pending_key = _arithmetic_sequence_pending_key(message)
        if pending_key is not None:
            ARITH_SEQUENCE_PENDING.pop(pending_key, None)

        today = datetime.now(BOT_TZ).strftime("%Y-%m-%d")
        allowed = db.claim_daily_user_event(
            MATH_DAILY_EVENT_KEY,
            int(user.id),
            user.username or str(user.id),
            today,
        )

        if not allowed:
            await message.reply_text(
                choose_random(
                    f"math_daily_limit:{user.id}",
                    MATH_DAILY_LIMIT_MESSAGES,
                    display_name(message),
                )
            )
            db.add_history(
                f"CALCULO AVANZADO LIMITADO | {display_name(message)} | "
                f"chat {message.chat_id} | fecha {today}"
            )
            return True

    await message.reply_text(response)
    db.add_history(
        f"MATEMATICA AVANZADA | {display_name(message)} | "
        f"chat {message.chat_id} | consulta={text_value[:220]}"
    )
    return True


def pecos_math_help_intent(text_value: str) -> bool:
    if not text_value or not text_mentions_pecos(text_value):
        return False

    normalized = normalize_intent(text_value).lower()
    patterns = (
        r"\bque\s+calculos?\s+(?:puedes|sabes)\s+hacer\b",
        r"\bcomo\s+te\s+pregunto\s+(?:un\s+)?calculo\b",
        r"\bcomo\s+hago\s+un\s+calculo\b",
        r"\bque\s+matematicas?\s+sabes\b",
        r"\bayuda\s+matematica\b",
    )
    return any(re.search(pattern, normalized) for pattern in patterns)


async def handle_math_help(message: Message) -> bool:
    if not pecos_math_help_intent(message.text or ""):
        return False

    await message.reply_text(
        "🧮 Puedes preguntarme una cuenta directa por día, partner. Ejemplos:\n"
        "• Pecos cuanto es 10*10-10?\n"
        "• Pecos cuanto es 10 por 10 menos 10?\n"
        "• Pecos suma 25 y 18?\n"
        "• Pecos multiplica 7 por 8?\n"
        "• Pecos divide 150 entre 3?\n"
        "• Pecos cual es el doble de 18?\n"
        "• Pecos cual es la mitad de 90?\n"
        "• Pecos 15 por ciento de 800?\n"
        "• Pecos raiz cuadrada de 144?\n"
        "• Pecos seno de 30 grados?\n"
        "• Pecos logaritmo base 2 de 8?\n"
        "• Pecos factorial de 8?\n"
        "• Pecos integral de e elevado a la x?\n"
        "• Pecos integral de 3x^2 + 2x - 5?\n"
        "• Pecos derivada de x^3 + 4x?\n"
        "• Pecos resuelve 2x + 5 = 17?\n"
        "• Pecos resuelve x^2 - 5x + 6 = 0?\n"
        "• Pecos sucesion aritmetica a3=11 y a8=31, calcula el termino general?\n"
        "• Pecos progresion aritmetica a5=17 y a12=45, calcula a20?\n"
        "• Pecos termino general a_n a partir de a_m y a_k, con m<k?\n"
        "Si faltan valores en una sucesión aritmética, te los pediré y podrás responderlos en el siguiente mensaje.\n\n"
        "También puedes retarme con «Pecos reto matematico» para iniciar la guerra matemática. 🤠"
    )
    return True


async def handle_safe_math(message: Message) -> bool:
    """Un cálculo correcto por usuario y por día local."""
    user = message.from_user
    if not user or user.is_bot:
        return False

    text_value = message.text or message.caption or ""
    expression, display_expression = _math_candidate_text(text_value)
    if expression is None or display_expression is None:
        return False

    # Validar primero. Una expresión mal escrita no consume la oportunidad diaria.
    try:
        result = _safe_math_eval(expression)
    except SafeMathError as exc:
        await message.reply_text(
            f"🧮 Esa cuenta no me cuadra, {display_name(message)}: {exc}."
        )
        return True

    today = datetime.now(BOT_TZ).strftime("%Y-%m-%d")
    allowed = db.claim_daily_user_event(
        MATH_DAILY_EVENT_KEY,
        int(user.id),
        user.username or str(user.id),
        today,
    )

    if not allowed:
        await message.reply_text(
            choose_random(
                f"math_daily_limit:{user.id}",
                MATH_DAILY_LIMIT_MESSAGES,
                display_name(message),
            )
        )
        db.add_history(
            f"CALCULO LIMITADO | {display_name(message)} | chat {message.chat_id} | fecha {today}"
        )
        return True

    pretty_expression = _pretty_math_expression(display_expression)
    pretty_result = _format_math_number(result)
    await message.reply_text(
        f"🧮 {pretty_expression} = {pretty_result}"
    )
    db.add_history(
        f"CALCULO MATEMATICO | {display_name(message)} | chat {message.chat_id} "
        f"| {display_expression} = {pretty_result}"
    )
    return True


async def handle_custom_qa(message: Message) -> bool:
    """Responde reglas configuradas desde /config antes de respuestas genéricas."""
    text_value = message.text or message.caption or ""
    if not text_value:
        return False

    row = find_custom_qa_response(text_value)
    if not row:
        return False

    await message.reply_text(str(row["response"]))
    db.add_history(
        f"QA PERSONALIZADA ID {row['id']} | {display_name(message)} | chat {message.chat_id}"
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



def pecos_message_looks_like_question(text_value: str) -> bool:
    """Detecta una pregunta dirigida a Pecos aunque no lleve signo '?'.

    Las funciones específicas (búsqueda, QA personalizada, matemática, etc.)
    se ejecutan antes de este fallback.
    """
    normalized = normalize_intent(text_value or "").strip()
    if not normalized:
        return False

    if "?" in (text_value or ""):
        return True

    # Quitar una llamada inicial a Pecos/Peco/@username para analizar el resto.
    probe = normalized
    for alias in sorted(PECOS_USERNAME_ALIASES, key=len, reverse=True):
        alias_norm = normalize_intent(alias).lower().lstrip("@")
        if alias_norm:
            probe = re.sub(
                rf"^\s*@?{re.escape(alias_norm)}\b[\s,:;-]*",
                "",
                probe,
                flags=re.IGNORECASE,
            )

    probe = re.sub(
        r"^\s*(?:pecos|peco)\b[\s,:;-]*",
        "",
        probe,
        flags=re.IGNORECASE,
    ).strip()

    question_starts = (
        "que ", "como ", "cuanto ", "cuanta ", "cuantos ", "cuantas ",
        "cuando ", "donde ", "por que ", "porque ", "cual ", "cuales ",
        "quien ", "quienes ", "puedes ", "podrias ", "sabes ", "dime ",
        "explica ", "muestrame ", "muéstrame ", "ensename ", "enseñame ",
        "cuentame ", "cuéntame ", "hablame ", "háblame ",
        "me dices ", "me puedes ", "me podrias ",
    )
    return probe.startswith(question_starts)


def pecos_password_jump_joke_requested(text_value: str) -> bool:
    """Detecta la broma específica pedida para 'saltar contraseña(s)'."""
    normalized = normalize_intent(text_value or "").lower()

    patterns = (
        r"\bsaltar\s+(?:la\s+|las\s+)?contrasenas?\b",
        r"\bsaltar\s+(?:la\s+|las\s+)?claves?\b",
        r"\bpasar\s+por\s+alto\s+(?:la\s+|las\s+)?contrasenas?\b",
    )
    return any(re.search(pattern, normalized) for pattern in patterns)



SPANISH_WEEKDAYS = (
    "lunes", "martes", "miércoles", "jueves",
    "viernes", "sábado", "domingo",
)

SPANISH_MONTHS = (
    "enero", "febrero", "marzo", "abril",
    "mayo", "junio", "julio", "agosto",
    "septiembre", "octubre", "noviembre", "diciembre",
)


def pecos_time_or_date_intent(text_value: str) -> str | None:
    """Detecta consultas de hora o fecha dirigidas explícitamente a Pecos."""
    if not text_value or not text_mentions_pecos(text_value):
        return None

    normalized = normalize_intent(text_value).lower()

    time_patterns = (
        r"\bque\s+hora(?:s)?\s+son\b",
        r"\bque\s+hora\s+es\b",
        r"\bque\s+hora\s+tenemos\b",
        r"\bme\s+dices\s+la\s+hora\b",
        r"\bdime\s+la\s+hora\b",
        r"\bhora\s+actual\b",
    )
    if any(re.search(pattern, normalized) for pattern in time_patterns):
        return "time"

    date_patterns = (
        r"\bque\s+dia\s+es(?:\s+hoy)?\b",
        r"\ben\s+que\s+dia\s+estamos\b",
        r"\bque\s+fecha\s+es(?:\s+hoy)?\b",
        r"\ben\s+que\s+fecha\s+estamos\b",
        r"\bque\s+fecha\s+tenemos\b",
        r"\bfecha\s+de\s+hoy\b",
        r"\bdia\s+de\s+hoy\b",
    )
    if any(re.search(pattern, normalized) for pattern in date_patterns):
        return "date"

    return None


def pecos_message_local_datetime(message: Message) -> datetime:
    """Toma la marca temporal que Telegram asignó al mensaje y la pasa a BOT_TZ."""
    telegram_dt = message.date
    try:
        return telegram_dt.astimezone(BOT_TZ)
    except (ValueError, AttributeError):
        # Compatibilidad defensiva con datetimes sin tzinfo.
        return telegram_dt.replace(tzinfo=ZoneInfo("UTC")).astimezone(BOT_TZ)


async def handle_pecos_time_date(message: Message) -> bool:
    intent = pecos_time_or_date_intent(message.text or "")
    if not intent:
        return False

    local_dt = pecos_message_local_datetime(message)

    if intent == "time":
        await message.reply_text(
            f"🕒 Partner, según la hora registrada por Telegram, son las {local_dt:%H:%M}."
        )
        return True

    weekday = SPANISH_WEEKDAYS[local_dt.weekday()]
    month = SPANISH_MONTHS[local_dt.month - 1]
    await message.reply_text(
        f"📅 Hoy es {weekday} {local_dt.day} de {month} de {local_dt.year}."
    )
    return True



ACTIVE_NOW_WINDOW_MINUTES = 5


def pecos_active_users_intent(text_value: str) -> bool:
    if not text_value or not text_mentions_pecos(text_value):
        return False

    normalized = normalize_intent(text_value).lower()

    patterns = (
        r"\bcuantos?\s+(?:usuarios?\s+)?(?:estan|hay)\s+conectados?\b",
        r"\bcuantos?\s+(?:usuarios?\s+)?(?:estan|hay)\s+en\s+linea\b",
        r"\bcuantos?\s+(?:usuarios?\s+)?(?:estan|hay)\s+online\b",
        r"\busuarios?\s+conectados?\b",
        r"\busuarios?\s+en\s+linea\b",
        r"\bgente\s+conectada\b",
        r"\bquienes?\s+estan\s+conectados?\b",
    )
    return any(re.search(pattern, normalized) for pattern in patterns)


async def handle_current_group_activity(
    message: Message,
    context: ContextTypes.DEFAULT_TYPE,
) -> bool:
    if not pecos_active_users_intent(message.text or ""):
        return False

    chat = message.chat
    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        return False

    now = datetime.now(BOT_TZ)
    cutoff = now - timedelta(minutes=ACTIVE_NOW_WINDOW_MINUTES)
    recent = db.get_recent_activity_profiles(
        message.chat_id,
        cutoff.isoformat(timespec="seconds"),
    )

    active_count = len({int(row["user_id"]) for row in recent})

    total_members = None
    try:
        total_members = await context.bot.get_chat_member_count(message.chat_id)
    except TelegramError:
        total_members = None

    lines = [
        "👥 Telegram no permite que Pecos vea la presencia «online» real de todos los miembros.",
        (
            f"📡 En el momento de esta consulta, Pecos observa "
            f"{active_count} usuario{'s' if active_count != 1 else ''} "
            f"con actividad en los últimos {ACTIVE_NOW_WINDOW_MINUTES} minutos."
        ),
    ]

    if total_members is not None:
        lines.append(f"👤 Miembros totales del grupo: {int(total_members)}.")

    lines.append(
        "ℹ️ Puede haber más personas conectadas leyendo sin escribir; "
        "Telegram no expone ese dato a los bots."
    )

    await message.reply_text("\n".join(lines))
    db.add_history(
        f"CONSULTA ACTIVOS AHORA | chat={message.chat_id} | "
        f"activos_{ACTIVE_NOW_WINDOW_MINUTES}m={active_count} | "
        f"miembros={total_members if total_members is not None else 'ND'}"
    )
    return True


def pecos_is_being_corrected(text_value: str) -> bool:
    normalized = normalize_intent(text_value or "").lower()

    patterns = (
        r"\bpecos\b.*\b(perdido|equivocado|confundido|fallando|fallo|mal)\b",
        r"\bpeco\b.*\b(perdido|equivocado|confundido|fallando|fallo|mal)\b",
        r"\b(te equivocaste|te confundiste|estas perdido|andas perdido)\b",
        r"\b(respuesta|respuestas)\b.*\b(mal|equivocad|perdid|confus)\w*",
        r"\bno sabes\b",
    )
    return any(re.search(pattern, normalized) for pattern in patterns)


async def handle_direct_pecos_mention(message: Message) -> bool:
    if not message.text:
        return False

    normalized = normalize_intent(message.text).strip()

    if not pecos_conversational_question_allowed(message.text):
        return False

    usuario = display_name(message)
    increment_user_metric(message, "pecos_mention_count")

    # Hora/fecha tienen prioridad sobre el fallback humorístico.
    # La fuente temporal es el timestamp del propio mensaje de Telegram,
    # convertido a la zona configurada de Pecos (America/Santiago).
    if await handle_pecos_time_date(message):
        return True

    # Preguntas amistosas sobre animales:
    # "Pecos, ¿te gustan los gatos/perros/etc.?"
    # Siempre responde positivamente y remata con humor sarcástico del grupo.
    if await handle_pecos_animal_likes(message):
        return True

    # Broma específica solicitada por el administrador.
    # No entrega instrucciones ni intenta resolver la consulta:
    # únicamente responde con humor rotativo.
    if pecos_password_jump_joke_requested(message.text):
        await message.reply_text(
            choose_random(
                "pecos_password_jump",
                PECOS_PASSWORD_JOKE_MESSAGES,
                usuario,
            )
        )
        return True

    if pecos_is_being_corrected(message.text):
        await message.reply_text(
            choose_random(
                "pecos_correction",
                get_humor_pool("correction"),
                usuario,
            )
        )
        return True

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

    # Si ninguna función anterior reconoció la consulta pero claramente es una
    # pregunta dirigida a Pecos, responde siempre con humor rotativo en vez de
    # inventar información.
    if pecos_message_looks_like_question(message.text):
        if await maybe_offer_math_battle(message, context):
            return True

        await message.reply_text(
            choose_random(
                "pecos_unknown_question",
                get_humor_pool("unknown"),
                usuario,
            )
        )
        return True

    # Si alguien nombra directamente a Pecos y ninguna función anterior
    # entendió la intención, Pecos YA NO se queda callado: responde siempre,
    # pero reconoce que no tiene una respuesta segura en vez de inventarla.
    await message.reply_text(
        choose_random(
            "pecos_unknown",
            get_humor_pool("unknown"),
            usuario,
        )
    )
    return True


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


def user_is_first_observed_interaction(message: Message) -> bool:
    user = message.from_user
    if not user or user.is_bot:
        return False

    # En el grupo principal, la memoria histórica es la señal más sólida.
    if history_memory_enabled_for_chat(message.chat_id):
        count = db.count_conversation_messages_for_user(message.chat_id, user.id)
        # El mensaje actual ya fue aprendido antes de llegar a los saludos.
        if count > 0:
            return count <= 1

    # Fallback para grupos sin memoria histórica: un perfil recién creado tiene
    # first_seen == last_seen en su primera interacción observada.
    row = db.get_user_profile(message.chat_id, user.id)
    if not row:
        return True
    return str(row["first_seen"] or "") == str(row["last_seen"] or "")


def message_has_request_or_technical_continuation(text_value: str) -> bool:
    """True si el saludo forma parte de una consulta/solicitud real.

    Evita interpretar como despedida mensajes del tipo:
    "Colegas buenas noches, ¿alguien me puede ayudar con un SLR5100...?"

    La detección es conservadora: exige una señal técnica estructurada o
    una frase clara de solicitud/pregunta. Un simple "buenas noches colegas"
    sigue siendo tratado por la lógica social normal.
    """
    if not text_value:
        return False

    normalized = normalize_intent(text_value).strip()

    try:
        parsed = technical_query_interpret(text_value)
        if any(
            parsed.get(key)
            for key in (
                "models",
                "raw_model_anchors",
                "brands",
                "technologies",
                "resources",
                "equipment_classes",
            )
        ):
            return True
    except Exception:
        # La clasificación social nunca debe caer por un fallo del parser técnico.
        pass

    if technical_archive_terms(text_value):
        return True

    request_patterns = (
        r"\b(?:alguien|alguno|alguna|quien|quienes)\b.{0,45}\b"
        r"(?:ayud|sabe|conoce|tiene|tenga|trabaja|trabaje|usa|utiliza|configur|conect)\w*\b",
        r"\b(?:me|nos)\s+(?:puede|pueden|podria|podrian)\s+"
        r"(?:ayudar|orientar|decir|indicar|explicar|confirmar)\b",
        r"\b(?:necesito|necesitamos|busco|buscamos)\s+(?:ayuda|informacion|datos|orientacion)\b",
        r"\b(?:tengo|tenemos)\s+(?:una\s+)?(?:consulta|pregunta|duda|problema)\b",
        r"\b(?:por\s*favor|porfavor)\b.{0,35}\b(?:ayud|consulta|pregunta|duda)\w*\b",
    )

    return any(
        re.search(pattern, normalized)
        for pattern in request_patterns
    )


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

    # No cortar una consulta técnica o una solicitud de ayuda que empieza
    # o termina con una cortesía. "Buenas noches" no significa despedida
    # cuando el resto del mensaje continúa con una pregunta real.
    if message_has_request_or_technical_continuation(message.text):
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

    # "Buenas noches" es ambigua. Si el usuario recién está entrando o
    # continúa presentándose/hablando, es SALUDO, no despedida.
    introduction_signal = (
        "tengo poco" in normalized
        or "soy nuevo" in normalized
        or "soy nueva" in normalized
        or "recien entro" in normalized
        or "recien ingres" in normalized
        or "me presento" in normalized
        or "ando empezando" in normalized
        or "estoy empezando" in normalized
        or "en el mundo de" in normalized
        or "en este mundo" in normalized
    )

    first_interaction = user_is_first_observed_interaction(message)

    collective_good_night = (
        "buenas noches" in normalized
        and collective_target
        and short_message
        and not introduction_signal
        and not first_interaction
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
        or bool(re.search(
            r"\b(?:hola|saludos|buenas(?:\s+noches|\s+tardes)?|buenos\s+dias|buen\s+dia)"
            r"\s+(?:gente|amigos|grupo|colegas|companeros|muchachos|chicos|senores|caballeros)\b",
            normalized,
        ))
        or bool(re.search(
            r"\b(?:gente|amigos|grupo|colegas|companeros|muchachos|chicos|senores|caballeros)"
            r"\s+(?:hola|saludos|buenas(?:\s+noches|\s+tardes)?|buenos\s+dias|buen\s+dia)\b",
            normalized,
        ))
    )

    if not (greeting_signal and collective_signal):
        return False

    # Si después del saludo viene una consulta real, la prioridad es técnica.
    # No enviamos un saludo social que pueda interrumpir o confundir el hilo.
    if message_has_request_or_technical_continuation(message.text):
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

    if not pecos_conversational_question_allowed(message.text):
        return False

    normalized = normalize_intent(message.text)

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
        helpful_score = get_user_metric(message.chat_id, message.from_user.id, "file_contribution_score")

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

    # Si la ofensa está dirigida claramente a Pecos, responde con humor.
    # Luego la moderación conserva su prioridad y puede actuar sobre el mensaje.
    duel_handled = False
    if (
        not is_edited
        and chat.type in (ChatType.GROUP, ChatType.SUPERGROUP)
    ):
        duel_handled = await handle_pecos_insult_duel(message, context)

    # Moderación tiene prioridad sobre el resto de respuestas.
    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        if await moderate_if_needed(message, context):
            return

    if duel_handled:
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

    # Broma automática por la propia presencia de XeraX:
    # máximo una por mañana, tarde y noche.
    if (
        not is_edited
        and chat.type in (ChatType.GROUP, ChatType.SUPERGROUP)
    ):
        if await handle_xerax_auto_presence(message):
            return

    # Broma antigua XeraX: se conserva para menciones explícitas de otros
    # usuarios. OWNER mantiene su activación sin límite.
    if (
        not is_edited
        and chat.type in (ChatType.GROUP, ChatType.SUPERGROUP)
    ):
        if await handle_xerax_fun(message):
            return

    # Fase 2: aprende respuestas explícitas a preguntas ya registradas.
    # Antes de limitarse a decir "esto ya se preguntó", Pecos intenta usar
    # asociaciones confirmadas y su memoria técnica autónoma.
    if (
        not is_edited
        and chat.type in (ChatType.GROUP, ChatType.SUPERGROUP)
    ):
        await capture_answer_to_known_question(message, context)

        # AYUDA TÉCNICA: Pecos solo responde si su nombre aparece primero.
        # El aprendizaje histórico de arriba sigue funcionando con todas
        # las conversaciones del grupo.
        if pecos_help_invocation_allowed(message.text or message.caption or ""):
            if await handle_current_group_activity(message, context):
                return

            if await handle_kpg_compatibility_question(message, context):
                return

            if await handle_radio_software_association(message, context):
                return

            if await handle_autonomous_technical_memory(message, context):
                return

        # Esta función guarda preguntas aunque Pecos no haya sido llamado,
        # pero solo emite aviso si fue invocado al inicio.
        if await handle_repeated_question(message, context):
            return

    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        if await handle_collective_farewell(message):
            return

        if await handle_collective_greeting(message):
            return

        if await handle_internal_joke(message):
            return

    # Texto escrito "en espejo": Pecos intenta leer cada palabra al revés.
    # Si la detección es segura, muestra la lectura y reta al autor a la guerra
    # matemática. Funciona aunque el mensaje original no nombre a Pecos.
    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        if await handle_mirror_math_challenge(message, context):
            return

    # Guerra matemática: puede iniciarse explícitamente ("desafío matemático a Pecos"),
    # por una invitación automática tras preguntas fuera de alcance o por un
    # desafío surgido de un mensaje en espejo.
    # Si existe una invitación pendiente o una partida activa, sus respuestas
    # tienen prioridad. El minijuego es independiente del límite diario de cálculo.
    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        if await handle_math_battle_message(message, context):
            return

    # Preguntas/respuestas y matemáticas: las consultas NUEVAS requieren
    # "Pecos ..." al comienzo Y terminar en "?". Una sucesión ya pendiente
    # conserva su respuesta de seguimiento sin obligar a repetir el nombre.
    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        conversational_question = pecos_conversational_question_allowed(
            message.text or message.caption or ""
        )
        pending_sequence_reply = (
            _arithmetic_sequence_pending_active(message) is not None
        )

        if conversational_question:
            if await handle_custom_qa(message):
                return

            # Ayuda y cálculo matemático seguro: una respuesta por usuario y por día.
            # La ayuda no consume el cálculo diario.
            if await handle_math_help(message):
                return

            if await handle_advanced_math(message):
                return

            if await handle_safe_math(message):
                return
        elif pending_sequence_reply:
            # Continuación de una consulta iniciada previamente con Pecos.
            if await handle_advanced_math(message):
                return

    if await handle_identity(message, context):
        return

    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        # Si la memoria técnica no resolvió el caso, Pecos aún puede buscar
        # archivos por referencias explícitas como KPG-D6.
        if await handle_archive_natural_query(message, context):
            return

    if await handle_social(message):
        return

    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        # Si Pecos fue llamado al comienzo, primero intenta una ayuda técnica
        # relacionada antes de caer en el fallback social/humorístico.
        if await maybe_offer_related_files(message, context):
            return

        if await handle_direct_pecos_mention(message):
            return

        if await handle_contextual_phrase(message):
            return

        await maybe_react_to_message(message, context)


async def check_group_silence(application: Application) -> None:
    if not db.is_true("silence_enabled"):
        return

    now = datetime.now(BOT_TZ)

    # Mantener el horario histórico de la función. Si hubo silencio durante
    # la noche, al volver a las 09:00 no se envían mensajes atrasados en masa:
    # se envía como máximo el aviso correspondiente al intervalo actual.
    if not (9 <= now.hour < 22):
        return

    try:
        silence_hours = int(db.get_setting("silence_hours", "8"))
    except ValueError:
        silence_hours = 8

    silence_hours = max(1, min(72, silence_hours))

    for row in db.list_groups():
        chat_id = int(row["chat_id"])
        if chat_id not in ALLOWED_GROUP_IDS:
            continue

        # El grupo de pruebas sirve para validar funciones manuales y búsquedas,
        # pero NO recibe intervenciones automáticas por silencio.
        if chat_id == TEST_GROUP_ID:
            continue

        activity_anchor = str(row["last_seen"] or "").strip()
        if not activity_anchor:
            continue

        try:
            last_seen = datetime.fromisoformat(activity_anchor)
        except Exception:
            continue

        elapsed_hours = max(0.0, (now - last_seen).total_seconds() / 3600.0)
        if elapsed_hours < silence_hours:
            continue

        # Con intervalo de 1 h: slot 1 a la primera hora, slot 2 a las dos, etc.
        slot = int(elapsed_hours // silence_hours)
        if slot < 1:
            continue

        if not db.claim_silence_interval(
            chat_id,
            activity_anchor,
            silence_hours,
            slot,
        ):
            continue

        try:
            await application.bot.send_message(
                chat_id=chat_id,
                text=build_silence_message(elapsed_hours),
            )
            db.add_history(
                f"SILENCIO RECURRENTE: Pecos habló en {row['title']} "
                f"| intervalo={silence_hours} h | slot={slot} "
                f"| silencio={elapsed_hours:.1f} h."
            )
        except TelegramError as exc:
            db.release_silence_interval(
                chat_id,
                activity_anchor,
                silence_hours,
                slot,
            )
            log.warning("No se pudo romper el silencio en %s: %s", chat_id, exc)


async def daily_loop(application: Application) -> None:
    while True:
        try:
            now = datetime.now(BOT_TZ)
            await check_group_silence(application)

            daily_time = db.get_setting("daily_time", "09:00")
            today = now.strftime("%Y-%m-%d")
            last_sent = db.get_setting("last_daily_sent_date", "")

            if now.strftime("%H:%M") == daily_time and last_sent != today:
                # Desde 2.8.25 el mensaje diario SIEMPRE usa un saludo
                # aleatorio del repertorio editable "daily".
                text = choose_random(
                    "daily_fun_greeting",
                    get_humor_pool("daily"),
                    today,
                )
                groups = [
                    row for row in db.list_groups()
                    if (
                        int(row["chat_id"]) in ALLOWED_GROUP_IDS
                        and int(row["chat_id"]) != TEST_GROUP_ID
                    )
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
                db.add_history(
                    f"MENSAJE DIARIO ALEATORIO enviado a {sent} grupo(s). "
                    f"Grupo de pruebas {TEST_GROUP_ID} excluido."
                )

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
            BotCommand("limpieza_inactivos", "Simular bloque 786–1595"),
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

    # Reconciliar el catálogo técnico desde file_fingerprints. Es una capa
    # derivada y paralela; no altera ni recalcula las huellas SHA-256.
    for catalog_chat_id in sorted(ALLOWED_GROUP_IDS):
        try:
            source_count, catalog_count = technical_catalog_sync_group(catalog_chat_id)
            log.info(
                "Catálogo técnico sincronizado | chat=%s | fingerprints=%s | catalogo=%s | parser=%s",
                catalog_chat_id,
                source_count,
                catalog_count,
                TECHNICAL_CATALOG_PARSER_VERSION,
            )
        except Exception as exc:
            log.warning(
                "Catálogo técnico: fallo sincronizando chat %s: %s",
                catalog_chat_id,
                exc,
            )

    # Reconstrucción idempotente de la memoria técnica autónoma a partir de
    # pares históricos CONFIRMED/ACKNOWLEDGED. No modifica mensajes históricos,
    # fingerprints ni SHA-256.
    if autonomous_memory_enabled():
        try:
            auto_stats = sync_autonomous_technical_memory(
                AUTONOMOUS_MEMORY_SOURCE_CHAT_ID
            )
            log.info(
                "Memoria técnica autónoma sincronizada | chat=%s | pares_revisados=%s "
                "| qa_aprendidos=%s | qa_confirmados=%s | evidencias=%s "
                "| hechos_confiables=%s",
                AUTONOMOUS_MEMORY_SOURCE_CHAT_ID,
                auto_stats["processed"],
                auto_stats["learned"],
                auto_stats["qa_confirmed"],
                auto_stats["fact_evidence"],
                auto_stats["trusted_facts"],
            )
        except Exception as exc:
            log.warning("Memoria técnica autónoma: fallo de sincronización: %s", exc)

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

    global MTPROTO_CLIENT
    if MTPROTO_CLIENT is not None:
        with contextlib.suppress(Exception):
            if MTPROTO_CLIENT.is_connected():
                await MTPROTO_CLIENT.disconnect()
        MTPROTO_CLIENT = None



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
    app.add_handler(CommandHandler("limpieza_inactivos", command_cleanup_inactive), group=0)
    app.add_handler(CommandHandler("consejo", command_advice), group=0)
    app.add_handler(CommandHandler("frase", command_phrase), group=0)
    app.add_handler(CommandHandler("excusa", command_excuse), group=0)
    app.add_handler(CommandHandler("pronostico", command_forecast), group=0)

    # Botones.
    app.add_handler(CallbackQueryHandler(callback_router), group=0)

    # Reacciones: también cuentan como actividad observada del usuario.
    # No generan respuestas; únicamente actualizan user_profiles.last_seen.
    app.add_handler(
        MessageReactionHandler(remember_user_reaction_activity),
        group=1,
    )

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
