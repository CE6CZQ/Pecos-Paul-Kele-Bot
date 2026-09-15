#!/bin/sh
set -eu

: "${BOT_TOKEN:?Falta BOT_TOKEN}"
: "${TELEGRAM_API_ID:?Falta TELEGRAM_API_ID}"
: "${TELEGRAM_API_HASH:?Falta TELEGRAM_API_HASH}"

ROOT_DATA="${RAILWAY_VOLUME_MOUNT_PATH:-/data}"

# Estado pequeño y persistente del servidor Bot API.
TELEGRAM_STATE="${ROOT_DATA}/telegram-bot-api-state"

# Los archivos grandes van únicamente al disco efímero del contenedor.
TELEGRAM_FILES="/tmp/telegram-bot-api-files"
TELEGRAM_TEMP="/tmp/telegram-bot-api-temp"

mkdir -p "${ROOT_DATA}" "${TELEGRAM_STATE}"

rm -rf "${TELEGRAM_FILES}" "${TELEGRAM_TEMP}"
mkdir -p "${TELEGRAM_FILES}" "${TELEGRAM_TEMP}"

chown -R telegram-bot-api:telegram-bot-api \
    "${TELEGRAM_STATE}" \
    "${TELEGRAM_FILES}" \
    "${TELEGRAM_TEMP}"

# Ya no usamos Hydrogram/MTProto.
rm -f \
    "${ROOT_DATA}/pecos_mtproto.session" \
    "${ROOT_DATA}/pecos_mtproto.session-journal" \
    2>/dev/null || true

export LOCAL_BOT_API=1
export LOCAL_BOT_API_URL="http://127.0.0.1:8081"
export TELEGRAM_FILES_DIR="${TELEGRAM_FILES}"

TELEGRAM_PID=""
PECOS_PID=""

start_telegram_api() {
    echo "[BOT API] Iniciando servidor local..."
    echo "[BOT API] Estado persistente: ${TELEGRAM_STATE}"
    echo "[BOT API] Archivos efímeros: ${TELEGRAM_FILES}"

    telegram-bot-api \
        --api-id="${TELEGRAM_API_ID}" \
        --api-hash="${TELEGRAM_API_HASH}" \
        --local \
        --http-ip-address=127.0.0.1 \
        --http-port=8081 \
        --dir="${TELEGRAM_STATE}" \
        --files-dir="${TELEGRAM_FILES}" \
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
echo " Pecos Paul Kele 2.4.0 - duplicados final"
echo "=============================================="
echo "Datos persistentes: ${ROOT_DATA}"
echo "Estado Bot API:     ${TELEGRAM_STATE}"
echo "Archivos Bot API:   ${TELEGRAM_FILES} (efímero)"

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
        echo "[BOT API] El proceso se detuvo. Reiniciando con el mismo estado..."
        start_telegram_api
        wait_for_telegram_api
    fi

    sleep 2
done
