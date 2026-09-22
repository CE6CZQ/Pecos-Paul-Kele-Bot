#!/bin/sh
set -eu

: "${BOT_TOKEN:?Falta BOT_TOKEN}"
: "${TELEGRAM_API_ID:?Falta TELEGRAM_API_ID}"
: "${TELEGRAM_API_HASH:?Falta TELEGRAM_API_HASH}"

ROOT_DATA="${RAILWAY_VOLUME_MOUNT_PATH:-/data}"

# Estado persistente del Telegram Bot API.
TELEGRAM_STATE="${ROOT_DATA}/telegram-bot-api-state"

# Archivos grandes únicamente en almacenamiento efímero.
TELEGRAM_FILES="/tmp/telegram-bot-api-files"
TELEGRAM_TEMP="/tmp/telegram-bot-api-temp"

# Log persistente para detectar el error real de Pecos.
PECOS_ERROR_LOG="${ROOT_DATA}/pecos_boot_error.log"

mkdir -p \
    "${ROOT_DATA}" \
    "${TELEGRAM_STATE}"

rm -rf \
    "${TELEGRAM_FILES}" \
    "${TELEGRAM_TEMP}"

mkdir -p \
    "${TELEGRAM_FILES}" \
    "${TELEGRAM_TEMP}"

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
export PYTHONUNBUFFERED=1

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
        with socket.create_connection(
            ("127.0.0.1", 8081),
            timeout=1
        ):
            print("[BOT API] Servidor local listo.", flush=True)
            sys.exit(0)

    except OSError:
        time.sleep(0.5)

print(
    "[BOT API] ERROR: no inició en el tiempo esperado.",
    flush=True
)
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

show_pecos_error() {
    echo ""
    echo "=================================================="
    echo " DIAGNOSTICO DE PECOS"
    echo "=================================================="

    if [ -f "${PECOS_ERROR_LOG}" ]; then
        cat "${PECOS_ERROR_LOG}"
    else
        echo "No se encontró ${PECOS_ERROR_LOG}"
        echo "El proceso terminó sin generar traceback."
    fi

    echo "=================================================="
    echo ""
}

trap cleanup INT TERM EXIT

echo "=============================================="
echo " Pecos Paul Kele - MODO DIAGNOSTICO"
echo "=============================================="
echo "Datos persistentes: ${ROOT_DATA}"
echo "Estado Bot API:     ${TELEGRAM_STATE}"
echo "Archivos Bot API:   ${TELEGRAM_FILES} (efímero)"
echo "Log diagnóstico:    ${PECOS_ERROR_LOG}"

# Confirmar que están ambos archivos.
if [ ! -f /app/main.py ]; then
    echo "[PECOS] ERROR: no existe /app/main.py"
    exit 1
fi

if [ ! -f /app/boot_diag.py ]; then
    echo "[PECOS] ERROR: no existe /app/boot_diag.py"
    echo "[PECOS] Debes subir boot_diag.py al repositorio."
    exit 1
fi

# Borrar solamente el diagnóstico anterior.
# NO toca pecos.db ni ningún dato de Pecos.
rm -f "${PECOS_ERROR_LOG}"

start_telegram_api
wait_for_telegram_api

echo "[PECOS] Iniciando main.py mediante boot_diag.py..."

python3 -u /app/boot_diag.py &
PECOS_PID=$!

echo "[PECOS] PID: ${PECOS_PID}"

while true; do

    # ---------------------------------------------------------
    # PECOS
    # ---------------------------------------------------------
    if ! kill -0 "${PECOS_PID}" 2>/dev/null; then

        PECOS_RC=0

        if wait "${PECOS_PID}"; then
            PECOS_RC=0
        else
            PECOS_RC=$?
        fi

        echo ""
        echo "[PECOS] ERROR: el proceso se detuvo."
        echo "[PECOS] Código de salida: ${PECOS_RC}"

        show_pecos_error

        echo "Railway reiniciará el contenedor."
        exit 1
    fi

    # ---------------------------------------------------------
    # TELEGRAM BOT API
    # ---------------------------------------------------------
    if ! kill -0 "${TELEGRAM_PID}" 2>/dev/null; then
        echo "[BOT API] El proceso se detuvo."
        echo "[BOT API] Reiniciando con el mismo estado..."

        start_telegram_api
        wait_for_telegram_api
    fi

    sleep 2
done
