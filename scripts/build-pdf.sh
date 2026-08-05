#!/usr/bin/env bash
# Build a PDF from a markdown document via pandoc and typst.
#
#   ./scripts/build-pdf.sh [input.md] [output.pdf]
#
# Defaults to report-outline.md -> report-outline.pdf. Requires pandoc and
# typst; neither LaTeX nor any font installation is needed.
set -euo pipefail

src="${1:-report-outline.md}"
out="${2:-${src%.md}.pdf}"
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

for tool in pandoc typst; do
  command -v "$tool" >/dev/null || { echo "error: $tool not found" >&2; exit 1; }
done

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cp "$src" "$work/doc.md"

# Column widths are a presentation concern; compute them on the copy so the
# source stays readable and hand-editable.
python3 "$here/pdf/table-widths.py" "$work/doc.md"

pandoc "$work/doc.md" -o "$out" \
  --pdf-engine=typst \
  --lua-filter="$here/pdf/title.lua" \
  --include-in-header="$here/pdf/head.typ" \
  --metadata author="$(git config user.name 2>/dev/null || echo '')" \
  --metadata date="$(date +%Y-%m-%d)" \
  --toc --toc-depth=2 \
  --number-sections=false

echo "wrote $out ($(pdfinfo "$out" 2>/dev/null | awk '/^Pages/{print $2" pages"}'))"
