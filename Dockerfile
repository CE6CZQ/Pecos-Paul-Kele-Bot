FROM aiogram/telegram-bot-api:10.3

USER root

RUN apk add --no-cache \
    bash \
    ca-certificates \
    curl \
    python3 \
    py3-pip \
    py3-virtualenv \
    tzdata

WORKDIR /app

COPY requirements.txt /app/requirements.txt

RUN python3 -m venv /opt/pecos-venv \
    && /opt/pecos-venv/bin/pip install --no-cache-dir --upgrade pip \
    && /opt/pecos-venv/bin/pip install --no-cache-dir -r /app/requirements.txt

COPY main.py /app/main.py
COPY start.sh /app/start.sh

RUN chmod +x /app/start.sh

ENV PATH="/opt/pecos-venv/bin:${PATH}" \
    LOCAL_BOT_API="1" \
    LOCAL_BOT_API_URL="http://127.0.0.1:8081" \
    TELEGRAM_LOCAL="1" \
    TELEGRAM_HTTP_PORT="8081"

# La imagen base trae su propio ENTRYPOINT. Lo anulamos porque start.sh
# levantará Telegram Bot API Server y Pecos en el mismo contenedor.
ENTRYPOINT []

CMD ["/app/start.sh"]
