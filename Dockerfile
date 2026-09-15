FROM aiogram/telegram-bot-api:10.3

USER root

RUN apk add --no-cache \
    python3 \
    py3-pip \
    py3-virtualenv \
    tzdata \
    ca-certificates

WORKDIR /app

COPY requirements.txt /app/requirements.txt

RUN python3 -m venv /opt/venv \
    && /opt/venv/bin/pip install --no-cache-dir --upgrade pip \
    && /opt/venv/bin/pip install --no-cache-dir -r /app/requirements.txt

ENV PATH="/opt/venv/bin:$PATH"
ENV PYTHONUNBUFFERED=1

COPY . /app

RUN chmod +x /app/start.sh

ENTRYPOINT ["/app/start.sh"]
