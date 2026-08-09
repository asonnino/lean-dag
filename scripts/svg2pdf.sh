#!/usr/bin/env bash
# Vector PDFs of the support diagrams.
#
# Typst is already required for the document build (docs/build-pdf.sh) and
# renders SVG natively, so no separate converter is needed: each diagram is
# placed on a page cut to its own size, giving a borderless vector PDF that
# scales without pixelation.
#
# Usage:  scripts/svg2pdf.sh [file.svg ...]     (default: docs/depgraph/*.svg)
set -euo pipefail

cd "$(dirname "$0")/.."
mkdir -p docs/pdf

files=("$@")
if [ ${#files[@]} -eq 0 ]; then
  files=(docs/depgraph/*.svg)
fi

for svg in "${files[@]}"; do
  base=$(basename "$svg" .svg)
  dir=$(dirname "$svg")
  # page size from the SVG's own width/height, so nothing is cropped or padded
  read -r w h < <(sed -n 's/.*width="\([0-9.]*\)" height="\([0-9.]*\)".*/\1 \2/p' "$svg" | head -1)
  : "${w:=1600}" "${h:=1200}"
  tmp="$dir/.svg2pdf-$base.typ"
  printf '#set page(width: %spt, height: %spt, margin: 0pt)\n#image("%s", width: 100%%)\n' \
    "$w" "$h" "$(basename "$svg")" > "$tmp"
  typst compile "$tmp" "docs/pdf/$base.pdf"
  rm -f "$tmp"
  echo "docs/pdf/$base.pdf  (${w}x${h})"
done
