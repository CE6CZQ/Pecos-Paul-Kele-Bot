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
from datetime import datetime, timedelta
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
    TypeHandler,
    filters,
)


APP_NAME = "Pecos Paul Kele"
VERSION = "2.8.44-ignore-no-hay-caso"
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
