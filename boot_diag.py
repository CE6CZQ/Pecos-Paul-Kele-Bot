#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from __future__ import annotations

import hashlib
import os
import runpy
import sys
import traceback
from datetime import datetime

TARGET = "/app/main.py"
PERSISTENT_LOG = "/data/pecos_boot_error.log"


def emit(text: str = "") -> None:
    print(text, flush=True)
    try:
        with open(PERSISTENT_LOG, "a", encoding="utf-8") as fh:
            fh.write(text + "\n")
            fh.flush()
    except Exception:
        pass


def fatal(title: str, exc: BaseException | None = None) -> None:
    emit("")
    emit("!" * 72)
    emit(f"[BOOT_DIAG] {title}")
    if exc is not None:
        emit(f"[BOOT_DIAG] Tipo: {type(exc).__name__}")
        emit(f"[BOOT_DIAG] Mensaje: {exc}")
        emit("-" * 72)
        for line in traceback.format_exc().splitlines():
            emit(line)
    emit("!" * 72)


emit("=" * 72)
emit(f"[BOOT_DIAG] Inicio: {datetime.now().isoformat()}")
emit(f"[BOOT_DIAG] Python: {sys.version.replace(chr(10), ' ')}")
emit(f"[BOOT_DIAG] Executable: {sys.executable}")
emit(f"[BOOT_DIAG] CWD: {os.getcwd()}")
emit(f"[BOOT_DIAG] main.py: {TARGET}")
emit("=" * 72)

if not os.path.isfile(TARGET):
    fatal("ERROR: /app/main.py NO EXISTE")
    raise SystemExit(91)

try:
    raw = open(TARGET, "rb").read()
except Exception as exc:
    fatal("ERROR LEYENDO /app/main.py", exc)
    raise

emit(f"[BOOT_DIAG] main.py bytes: {len(raw)}")
emit(f"[BOOT_DIAG] main.py SHA256: {hashlib.sha256(raw).hexdigest()}")

try:
    source = raw.decode("utf-8")
except Exception as exc:
    fatal("ERROR DECODIFICANDO main.py COMO UTF-8", exc)
    raise

lines = source.splitlines()
emit(f"[BOOT_DIAG] main.py líneas: {len(lines)}")

version_lines = [line.strip() for line in lines if line.strip().startswith("VERSION =")]
if version_lines:
    emit(f"[BOOT_DIAG] {version_lines[0]}")
else:
    emit("[BOOT_DIAG] ADVERTENCIA: no encontré línea VERSION = ...")

emit(f"[BOOT_DIAG] contiene 'def main()': {'def main()' in source or 'def main(' in source}")
emit(f"[BOOT_DIAG] contiene guard __main__: {'if __name__ == \"__main__\"' in source}")

emit("[BOOT_DIAG] Últimas 12 líneas de /app/main.py:")
emit("-" * 72)
for line in lines[-12:]:
    emit(line)
emit("-" * 72)

# Importar SIN ejecutar el guard __main__. Así podemos verificar exactamente
# qué cargó Railway y llamar main() de forma explícita.
try:
    emit("[BOOT_DIAG] Cargando main.py como módulo de diagnóstico...")
    ns = runpy.run_path(TARGET, run_name="pecos_diag_module")
    emit("[BOOT_DIAG] Carga del módulo: OK")
except BaseException as exc:
    fatal("ERROR FATAL DURANTE LA CARGA DE main.py", exc)
    raise

emit(f"[BOOT_DIAG] VERSION cargada: {ns.get('VERSION', '<sin VERSION>')}")
emit(f"[BOOT_DIAG] main presente: {'main' in ns}")
emit(f"[BOOT_DIAG] main callable: {callable(ns.get('main'))}")
emit(f"[BOOT_DIAG] build_application callable: {callable(ns.get('build_application'))}")

main_func = ns.get("main")
if not callable(main_func):
    fatal("ERROR: main.py CARGÓ PERO NO EXISTE UNA FUNCIÓN main() EJECUTABLE")
    raise SystemExit(92)

try:
    emit("[BOOT_DIAG] Llamando main() explícitamente...")
    main_func()
    emit("[BOOT_DIAG] ADVERTENCIA: main() TERMINÓ NORMALMENTE. Un bot long-polling no debería terminar.")
    raise SystemExit(93)
except SystemExit as exc:
    # Si es nuestro 93, conservarlo; cualquier otro SystemExit también interesa.
    if getattr(exc, "code", None) == 93:
        raise
    fatal("main() produjo SystemExit", exc)
    raise
except BaseException as exc:
    fatal("ERROR FATAL DENTRO DE main()", exc)
    raise
