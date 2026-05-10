#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

AUTORUN="${1:-}" 
CONFIG_FILE="$SCRIPT_DIR/config.ini"
RUNTIME_ROOT="$SCRIPT_DIR/.runtime"
mkdir -p "$RUNTIME_ROOT"

if [[ ! -f "$CONFIG_FILE" ]]; then
  cat > "$CONFIG_FILE" <<'EOF'
[launcher]
shell_startup_enabled = false
EOF
fi

read_config() {
  local raw
  raw="$(grep -E '^[[:space:]]*shell_startup_enabled[[:space:]]*=' "$CONFIG_FILE" | tail -n 1 | cut -d'=' -f2- | tr -d '[:space:]' | tr '[:upper:]' '[:lower:]' || true)"
  if [[ "$raw" == "true" ]]; then
    SHELL_STARTUP_ENABLED="true"
  else
    SHELL_STARTUP_ENABLED="false"
  fi
}

ensure_linux_startup_task() {
  local marker="$SCRIPT_DIR/start.sh --autorun"
  local log_file="$RUNTIME_ROOT/startup.log"
  local cron_line="@reboot /bin/bash \"$SCRIPT_DIR/start.sh\" --autorun >> \"$log_file\" 2>&1"
  local current_cron

  current_cron="$(crontab -l 2>/dev/null || true)"
  if grep -Fq "$marker" <<<"$current_cron"; then
    echo "[INFO] Startup cron already configured."
    return
  fi

  printf "%s\n%s\n" "$current_cron" "$cron_line" | crontab -
  echo "[SUCCESS] Startup cron created (@reboot)."
}

ensure_downloader() {
  if command -v curl >/dev/null 2>&1; then
    DOWNLOADER="curl -fsSL"
    return
  fi
  if command -v wget >/dev/null 2>&1; then
    DOWNLOADER="wget -qO-"
    return
  fi
  echo "[ERROR] Neither curl nor wget is available to download runtime files."
  exit 1
}

ensure_python_bootstrap() {
  if command -v python3 >/dev/null 2>&1; then
    BOOTSTRAP_PY="$(command -v python3)"
    return
  fi

  local conda_root="$RUNTIME_ROOT/miniconda"
  local conda_python="$conda_root/bin/python"
  if [[ -x "$conda_python" ]]; then
    BOOTSTRAP_PY="$conda_python"
    return
  fi

  ensure_downloader

  local arch
  arch="$(uname -m)"
  local installer_name
  case "$arch" in
    x86_64) installer_name="Miniconda3-latest-Linux-x86_64.sh" ;;
    aarch64) installer_name="Miniconda3-latest-Linux-aarch64.sh" ;;
    *)
      echo "[ERROR] Unsupported architecture for auto Python bootstrap: $arch"
      exit 1
      ;;
  esac

  local installer="$RUNTIME_ROOT/miniconda-installer.sh"
  local installer_url="https://repo.anaconda.com/miniconda/$installer_name"

  echo "[INFO] Python not found. Downloading self-contained runtime..."
  if command -v curl >/dev/null 2>&1; then
    curl -fsSL "$installer_url" -o "$installer"
  else
    wget -q "$installer_url" -O "$installer"
  fi

  bash "$installer" -b -p "$conda_root" >/dev/null
  rm -f "$installer"

  if [[ ! -x "$conda_python" ]]; then
    echo "[ERROR] Failed to bootstrap Python runtime."
    exit 1
  fi

  BOOTSTRAP_PY="$conda_python"
}

ensure_venv_and_deps() {
  local venv_dir="$RUNTIME_ROOT/venv-linux"
  PY_EXE="$venv_dir/bin/python"

  if [[ ! -x "$PY_EXE" ]]; then
    echo "[INFO] Creating Linux virtual environment..."
    "$BOOTSTRAP_PY" -m venv "$venv_dir"
  fi

  if [[ -f "$SCRIPT_DIR/backend/requirements.txt" ]]; then
    if ! "$PY_EXE" - <<'PY' >/dev/null 2>&1
import flask
import pandas
import openpyxl
PY
    then
      echo "[INFO] Installing dependencies..."
      "$PY_EXE" -m pip install --upgrade pip >/dev/null
      "$PY_EXE" -m pip install -r "$SCRIPT_DIR/backend/requirements.txt"
    else
      echo "[INFO] Dependencies already installed."
    fi
  else
    echo "[WARNING] backend/requirements.txt not found. Skipping dependency installation."
  fi
}

kill_existing_port_5000() {
  if command -v lsof >/dev/null 2>&1; then
    local pids
    pids="$(lsof -ti tcp:5000 || true)"
    if [[ -n "$pids" ]]; then
      echo "[INFO] Stopping existing process(es) on port 5000: $pids"
      kill -9 $pids || true
    fi
    return
  fi

  if command -v fuser >/dev/null 2>&1; then
    fuser -k 5000/tcp >/dev/null 2>&1 || true
  fi
}

read_config
if [[ "$SHELL_STARTUP_ENABLED" == "true" ]]; then
  ensure_linux_startup_task
fi

echo
echo "============================================"
echo " IIT-G Parent Connect"
echo " Starting server..."
echo "============================================"
echo

ensure_python_bootstrap
ensure_venv_and_deps
kill_existing_port_5000

if [[ "$AUTORUN" != "--autorun" ]]; then
  if command -v xdg-open >/dev/null 2>&1; then
    xdg-open "http://localhost:5000" >/dev/null 2>&1 || true
  fi
fi

"$PY_EXE" "$SCRIPT_DIR/backend/app.py"
