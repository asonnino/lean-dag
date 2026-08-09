#!/usr/bin/env bash
# Compile the design documents and the report to PDF.
#
# Requires pandoc (>= 3) with typst available as the PDF engine — both
# installable via `brew install pandoc typst`. Output lands in docs/pdf/,
# which is gitignored: the PDFs are build artifacts, the Markdown is the
# source of truth.
#
# Usage:
#   docs/build-pdf.sh            # build every document
#   docs/build-pdf.sh garbage    # build docs/garbage.md only
set -euo pipefail

cd "$(dirname "$0")"
mkdir -p pdf

build() {
  local name="$1"
  echo "building pdf/${name}.pdf"
  pandoc "${name}.md" -o "pdf/${name}.pdf" \
    --pdf-engine=typst \
    --from=gfm+tex_math_dollars+yaml_metadata_block+implicit_figures \
    -V margin-x=2.2cm -V margin-y=2.4cm \
    -V fontsize=10pt \
    --include-in-header=typst-header.typ \
    -V mainfont="Libertinus Serif" \
    -V monofont="Menlo" \
    --toc --toc-depth=2
}

if [ $# -gt 0 ]; then
  for name in "$@"; do
    build "${name%.md}"
  done
else
  for f in *.md; do
    build "${f%.md}"
  done
fi
echo "done: $(ls pdf | wc -l | tr -d ' ') PDFs in docs/pdf/"
