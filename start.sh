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

TELEGRAM_PID=""
PECOS_PID=""

start_telegram_api() {
    echo "[BOT API] Iniciando servidor local..."

    telegram-bot-api \
        --api-id="${TELEGRAM_API_ID}" \
        --api-hash="${TELEGRAM_API_HASH}" \
        --local \
        --http-ip-address=127.0.0.1 \
        --http-port=8081 \
        --dir="${TELEGRAM_DATA}" \
        --temp-dir="${TELEGRAM_TEMP}" \
        --username=telegram-bot-api \
        --groupname=telegram-bot-api \
        --verbosity=0 \
        --memory-verbosity=0 &

    TELEGRAM_PID=$!
}

wait_for_telegram_api() {
    python3 - <<'PY'
import socket
import sys
import time

for _ in range(120):
    try:
        with socket.create_connection(("127.0.0.1", 8081), timeout=1):
            print("[BOT API] Servidor local listo.")
            sys.exit(0)
    except OSError:
        time.sleep(0.5)

print("[BOT API] ERROR: no inició en el tiempo esperado.")
sys.exit(1)
PY
}

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

start_telegram_api
wait_for_telegram_api

echo "[PECOS] Iniciando main.py..."
python3 -u /app/main.py &
PECOS_PID=$!

while true; do
    if ! kill -0 "${PECOS_PID}" 2>/dev/null; then
        echo "ERROR: Pecos se detuvo. Railway reiniciará el contenedor."
        exit 1
    fi

    if ! kill -0 "${TELEGRAM_PID}" 2>/dev/null; then
        echo "[BOT API] El proceso se detuvo. Reiniciando sin tumbar Pecos..."
        start_telegram_api
        wait_for_telegram_api
    fi

    sleep 2
done
