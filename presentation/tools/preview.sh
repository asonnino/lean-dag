#!/bin/sh
# Screenshot slides of one part file without building the whole deck.
#   presentation/tools/preview.sh parts/02-protocols-a.html OUTDIR "1 2.3 4"
# Each argument in the third parameter is SLIDE[.STEP], counted within the
# part file; screenshots are written to OUTDIR/slide-SLIDE[.STEP].png.
set -e
DIR="$(cd "$(dirname "$0")/.." && pwd)"
PART="$1"; OUT="$2"; LIST="$3"
mkdir -p "$OUT"
TMP="$DIR/.preview-$$.html"
python3 - "$DIR" "$PART" "$TMP" <<'PY'
import sys, pathlib
sys.path.insert(0, sys.argv[1] + "/tools")
import build
build.build([pathlib.Path(sys.argv[1]) / sys.argv[2]], pathlib.Path(sys.argv[3]))
PY
for s in $LIST; do
  "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" --headless=new --disable-gpu \
    --hide-scrollbars --window-size=1400,800 --virtual-time-budget=3000 \
    --screenshot="$OUT/slide-$s.png" "file://$TMP#p$s" >/dev/null 2>&1
done
rm -f "$TMP"
echo "screenshots in $OUT"
