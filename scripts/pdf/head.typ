// Typst styling for the report PDF. Applied via pandoc --include-in-header.
#set page(margin: (x: 2.3cm, y: 2.4cm))
#set text(size: 10pt)

// Lean code: slightly smaller than body text so 80-column lines do not wrap.
#show raw: set text(size: 8.8pt)

// Tables: smaller still, unjustified, and with code smaller again. Column
// widths come from the dash proportions that table-widths.py writes.
#show table: it => {
  set text(size: 8.2pt)
  set par(justify: false, leading: 0.5em)
  show raw: set text(size: 7.6pt)
  it
}
