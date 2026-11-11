#!/usr/bin/env bash
# Make the Finger Exercise Coach open by itself once, after the Pi boots to the desktop.
# Closing the program does NOT restart it; it opens again at the next boot.
#
#   bash setup_autostart.sh            install
#   bash setup_autostart.sh --remove   undo
set -euo pipefail

APP_DIR="${APP_DIR:-$HOME/my_finger_project/src_code}"
PY="${PY:-$HOME/mediapipe_env/bin/python}"
LAUNCHER="$HOME/.local/bin/anti-finger-start"
DESKTOP="$HOME/.config/autostart/anti-finger.desktop"
LABWC="$HOME/.config/labwc/autostart"
WAYFIRE="$HOME/.config/wayfire.ini"

if [ "${1:-}" = "--remove" ]; then
  rm -f "$LAUNCHER" "$DESKTOP"
  [ -f "$LABWC" ] && sed -i '/anti-finger-start/d' "$LABWC"
  [ -f "$WAYFIRE" ] && sed -i '/anti-finger-start/d' "$WAYFIRE"
  echo "ยกเลิกการเปิดอัตโนมัติแล้ว"
  exit 0
fi

[ -f "$APP_DIR/main.py" ] || { echo "ไม่พบ $APP_DIR/main.py"; exit 1; }
[ -x "$PY" ] || { echo "ไม่พบ Python ที่ $PY"; exit 1; }

mkdir -p "$(dirname "$LAUNCHER")" "$(dirname "$DESKTOP")"
cat > "$LAUNCHER" <<EOF
#!/usr/bin/env bash
# Only one copy per boot, even if the desktop runs autostart from two places.
exec 9>"/tmp/anti-finger-\$(id -u).lock"
flock -n 9 || exit 0
sleep 3   # wait for the desktop, sound and USB camera to finish starting
cd "$APP_DIR"
exec "$PY" -u -X faulthandler main.py > "$APP_DIR/run.log" 2>&1
EOF
chmod +x "$LAUNCHER"

# Standard desktop autostart (X11 / LXDE and desktops that read ~/.config/autostart).
cat > "$DESKTOP" <<EOF
[Desktop Entry]
Type=Application
Name=Finger Exercise Coach
Exec=$LAUNCHER
Terminal=false
X-GNOME-Autostart-enabled=true
EOF

# labwc (Raspberry Pi OS Wayland desktop).
if [ -d "$HOME/.config/labwc" ] || command -v labwc >/dev/null 2>&1; then
  mkdir -p "$(dirname "$LABWC")"
  touch "$LABWC"
  grep -q anti-finger-start "$LABWC" || echo "$LAUNCHER &" >> "$LABWC"
fi

# wayfire (older Raspberry Pi OS Bookworm desktop).
if [ -f "$WAYFIRE" ] && ! grep -q anti-finger-start "$WAYFIRE"; then
  if grep -q '^\[autostart\]' "$WAYFIRE"; then
    sed -i "/^\[autostart\]/a anti_finger = $LAUNCHER" "$WAYFIRE"
  else
    printf '\n[autostart]\nanti_finger = %s\n' "$LAUNCHER" >> "$WAYFIRE"
  fi
fi

echo "ตั้งค่าเปิดอัตโนมัติเรียบร้อย"
echo "  โปรแกรม: $APP_DIR/main.py"
echo "  Python : $PY"
echo "  log    : $APP_DIR/run.log"
echo "รีสตาร์ตเครื่องเพื่อทดสอบ: sudo reboot"
