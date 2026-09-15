#!/bin/sh
set -eu

: "${BOT_TOKEN:?Falta BOT_TOKEN}"
: "${TELEGRAM_API_ID:?Falta TELEGRAM_API_ID}"
: "${TELEGRAM_API_HASH:?Falta TELEGRAM_API_HASH}"

ROOT_DATA="${RAILWAY_VOLUME_MOUNT_PATH:-/data}"
TELEGRAM_DATA="${ROOT_DATA}/telegram-bot-api"
TELEGRAM_TEMP="/tmp/telegram-bot-api"

mkdir -p "${ROOT_DATA}" "${TELEGRAM_DATA}" "${TELEGRAM_TEMP}"
chown -R telegram-bot-api:telegram-bot-api "${TELEGRAM_DATA}" "${TELEGRAM_TEMP}"

export LOCAL_BOT_API=1
export LOCAL_BOT_API_URL="http://127.0.0.1:8081"

cleanup() {
    echo "Deteniendo Pecos y Telegram Bot API..."

    if [ -n "${PECOS_PID:-}" ]; then
        kill "${PECOS_PID}" 2>/dev/null || true
    fi

    if [ -n "${TELEGRAM_PID:-}" ]; then
        kill "${TELEGRAM_PID}" 2>/dev/null || true
    fi

    wait 2>/dev/null || true
}

trap cleanup INT TERM EXIT

echo "=============================================="
echo " Pecos Paul Kele - arquitectura unificada"
echo "=============================================="
echo "Datos persistentes: ${ROOT_DATA}"
echo "Telegram Bot API:   ${TELEGRAM_DATA}"

echo "Iniciando Telegram Bot API local..."

telegram-bot-api \
    --api-id="${TELEGRAM_API_ID}" \
    --api-hash="${TELEGRAM_API_HASH}" \
    --local \
    --http-ip-address=127.0.0.1 \
    --http-port=8081 \
    --dir="${TELEGRAM_DATA}" \
    --temp-dir="${TELEGRAM_TEMP}" \
    --username=telegram-bot-api \
    --groupname=telegram-bot-api &

TELEGRAM_PID=$!

echo "Esperando a que Telegram Bot API escuche en 127.0.0.1:8081..."

python3 - <<'PY'
import socket
import sys
import time

for _ in range(120):
    try:
        with socket.create_connection(("127.0.0.1", 8081), timeout=1):
            print("Telegram Bot API disponible.")
            sys.exit(0)
    except OSError:
        time.sleep(0.5)

print("ERROR: Telegram Bot API no inició en el tiempo esperado.")
sys.exit(1)
PY

echo "Iniciando Pecos..."
python3 -u /app/main.py &
PECOS_PID=$!

while true; do
    if ! kill -0 "${TELEGRAM_PID}" 2>/dev/null; then
        echo "ERROR: Telegram Bot API se detuvo."
        exit 1
    fi

    if ! kill -0 "${PECOS_PID}" 2>/dev/null; then
        echo "ERROR: Pecos se detuvo."
        exit 1
    fi

    sleep 5
done
