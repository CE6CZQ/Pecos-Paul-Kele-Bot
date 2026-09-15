#!/usr/bin/env bash
set -Eeuo pipefail

echo "=============================================="
echo " Pecos Paul Kele - Railway Local Bot API"
echo "=============================================="

: "${BOT_TOKEN:?Falta BOT_TOKEN}"
: "${TELEGRAM_API_ID:?Falta TELEGRAM_API_ID}"
: "${TELEGRAM_API_HASH:?Falta TELEGRAM_API_HASH}"

DATA_ROOT="${RAILWAY_VOLUME_MOUNT_PATH:-${DATA_DIR:-/data}}"
STATE_DIR="${TELEGRAM_STATE_DIR:-${DATA_ROOT}/telegram-bot-api-state}"
FILES_DIR="${TELEGRAM_FILES_DIR:-/tmp/telegram-bot-api-files}"
TEMP_DIR="${TELEGRAM_TEMP_DIR:-/tmp/telegram-bot-api-temp}"
HTTP_PORT="${TELEGRAM_HTTP_PORT:-8081}"
MIGRATION_MARKER="${DATA_ROOT}/.pecos_local_bot_api_migrated"

mkdir -p "${DATA_ROOT}" "${STATE_DIR}" "${FILES_DIR}" "${TEMP_DIR}"

# El binario de la imagen aiogram conoce el usuario/grupo 101.
chown -R 101:101 "${STATE_DIR}" "${FILES_DIR}" "${TEMP_DIR}" || true

# ------------------------------------------------------------------
# MIGRACIÓN CONTROLADA:
# Solo llama a logOut del servidor oficial una vez, cuando el usuario
# haya definido MIGRATE_FROM_CLOUD=1 en Railway.
# El marker persiste en /data y evita repetir el logOut.
# ------------------------------------------------------------------
if [[ "${MIGRATE_FROM_CLOUD:-0}" == "1" && ! -f "${MIGRATION_MARKER}" ]]; then
    echo "[MIGRACION] Desregistrando Pecos de api.telegram.org..."

    LOGOUT_RESPONSE="$(
        curl -sS \
            --connect-timeout 10 \
            --max-time 30 \
            "https://api.telegram.org/bot${BOT_TOKEN}/logOut"
    )"

    if echo "${LOGOUT_RESPONSE}" | grep -Eq '"ok"[[:space:]]*:[[:space:]]*true'; then
        touch "${MIGRATION_MARKER}"
        echo "[MIGRACION] logOut confirmado. Marker persistente creado."
    else
        echo "[MIGRACION] ERROR: Telegram no confirmó logOut."
        echo "${LOGOUT_RESPONSE}"
        exit 1
    fi
fi

echo "[BOT API] Estado persistente: ${STATE_DIR}"
echo "[BOT API] Archivos descargados (efimeros): ${FILES_DIR}"
echo "[BOT API] Puerto local: ${HTTP_PORT}"

# Estado/sesión persistente en /data.
# Archivos grandes en /tmp para NO consumir el volumen persistente.
telegram-bot-api \
    --local \
    --dir="${STATE_DIR}" \
    --files-dir="${FILES_DIR}" \
    --temp-dir="${TEMP_DIR}" \
    --http-port="${HTTP_PORT}" \
    --username=telegram-bot-api \
    --groupname=telegram-bot-api &

BOT_API_PID=$!

cleanup() {
    echo "[SHUTDOWN] Deteniendo procesos..."
    if kill -0 "${BOT_API_PID}" 2>/dev/null; then
        kill "${BOT_API_PID}" 2>/dev/null || true
        wait "${BOT_API_PID}" 2>/dev/null || true
    fi
}
trap cleanup EXIT INT TERM

echo "[BOT API] Esperando a que el servidor HTTP responda..."

READY=0
for _ in $(seq 1 60); do
    if curl -sS \
        --connect-timeout 1 \
        --max-time 2 \
        -o /dev/null \
        "http://127.0.0.1:${HTTP_PORT}/"; then
        READY=1
        break
    fi

    if ! kill -0 "${BOT_API_PID}" 2>/dev/null; then
        echo "[BOT API] ERROR: el proceso terminó durante el arranque."
        wait "${BOT_API_PID}" || true
        exit 1
    fi

    sleep 1
done

if [[ "${READY}" != "1" ]]; then
    echo "[BOT API] ERROR: no respondió en 60 segundos."
    exit 1
fi

echo "[BOT API] Servidor local listo."
echo "[PECOS] Iniciando main.py..."

python /app/main.py &
PECOS_PID=$!

# Si Pecos termina, detenemos el Bot API Server y devolvemos su código.
set +e
wait "${PECOS_PID}"
PECOS_STATUS=$?
set -e

echo "[PECOS] main.py terminó con código ${PECOS_STATUS}."
exit "${PECOS_STATUS}"
