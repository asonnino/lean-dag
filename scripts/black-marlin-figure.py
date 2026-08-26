#!/usr/bin/env python3
"""Draw the execution that refutes Agreement (`black-marlin.md` §13).

The DAG of `LeanDagTest/BlackMarlin/Divergence.lean`, with the two twins
of the equivocating anchor, the reference the round-4 anchor omits, and
the two validators' descents. Every block, edge and label here is read
off that file; the figure asserts nothing the witness does not check.

    scripts/black-marlin-figure.py    ->  docs/figures/black-marlin-divergence.svg
"""
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "docs/figures/black-marlin-divergence.svg"

# id -> (round, validator); 12 is validator 0's second block of round 2.
ROUND = {}
CREATOR = {}
for i, (r, c) in enumerate(
        [(0, 0), (0, 1), (0, 2), (0, 3),
         (1, 0), (1, 1), (1, 2), (1, 3),
         (2, 0), (2, 1), (2, 2), (2, 3), (2, 0),
         (3, 0), (3, 1), (3, 2), (3, 3),
         (4, 0), (4, 1), (4, 2), (4, 3),
         (5, 0), (5, 1), (5, 2), (5, 3),
         (6, 0), (6, 1), (6, 2), (6, 3)]):
    ROUND[i], CREATOR[i] = r, c

REFS = {
    4: [0, 1, 2], 5: [0, 1, 2], 6: [1, 2, 3], 7: [1, 2, 3],
    8: [4, 5, 6], 9: [4, 5, 6], 10: [4, 5, 6], 11: [5, 6, 7], 12: [4, 6, 7],
    13: [9, 10, 12], 14: [8, 9, 10], 15: [8, 9, 10], 16: [8, 9, 11],
    17: [13, 14, 15], 18: [13, 14, 15], 19: [13, 15, 16], 20: [14, 15, 16],
    21: [17, 18, 19], 22: [17, 18, 19], 23: [17, 18, 19], 24: [18, 19, 20],
    25: [21, 22, 23], 26: [22, 23, 24], 27: [22, 23, 24], 28: [22, 23, 24],
}

ANCHOR = {0: 3, 1: 7, 2: (8, 12), 3: 14, 4: 19, 5: 24, 6: 26}
ANCHORS = {3, 7, 8, 12, 14, 19, 24, 26}
COMMITTED = {8, 19}                      # admitted by the rule (L16)
SUPPORT_8 = [(14, 8), (15, 8), (16, 8)]  # the three that make 8 committable
SUPPORT_12 = [(13, 12)]                  # the one that does not make 12 so
ANCHOR19 = [(19, 13), (19, 15), (19, 16)]
MISSING = (19, 14)                       # the reference 19 does not carry
DESCENT = [(19, 12), (12, 7), (7, 3)]    # the second validator's descent

X0, DX, Y0, DY, R = 105, 168, 232, 92, 21
TWIN_Y = 128


def pos(i):
    x = X0 + DX * ROUND[i]
    y = TWIN_Y if i == 12 else Y0 + DY * CREATOR[i]
    return x, y


def edge(a, b, stroke, width, dash="", arrow=""):
    """A line from block `a` to the block `b` it references."""
    (x1, y1), (x2, y2) = pos(a), pos(b)
    dx, dy = x2 - x1, y2 - y1
    d = (dx * dx + dy * dy) ** 0.5
    ux, uy = dx / d, dy / d
    return (f'<line x1="{x1 - ux * R:.1f}" y1="{y1 - uy * R:.1f}" '
            f'x2="{x2 + ux * R:.1f}" y2="{y2 + uy * R:.1f}" '
            f'stroke="{stroke}" stroke-width="{width}"{dash}{arrow}/>')


def main():
    W, H = 1290, 850
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" '
           f'viewBox="0 0 {W} {H}" font-family="Helvetica,Arial,sans-serif">',
           f'<rect width="{W}" height="{H}" fill="#ffffff"/>',
           '<defs>',
           '<marker id="ag" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" '
           'markerHeight="6" orient="auto"><path d="M0,0 L10,5 L0,10 z" fill="#2e7d32"/></marker>',
           '<marker id="ar" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" '
           'markerHeight="6" orient="auto"><path d="M0,0 L10,5 L0,10 z" fill="#c62828"/></marker>',
           '<marker id="ab" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" '
           'markerHeight="6" orient="auto"><path d="M0,0 L10,5 L0,10 z" fill="#1565c0"/></marker>',
           '<marker id="ap" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" '
           'markerHeight="6" orient="auto"><path d="M0,0 L10,5 L0,10 z" fill="#6a1b9a"/></marker>',
           '</defs>']

    # the Byzantine validator's lane
    out.append(f'<rect x="60" y="{Y0 - 42}" width="{W - 120}" height="84" '
               f'fill="#fdf1f1"/>')
    out.append(f'<text x="66" y="{Y0 - 50}" font-size="13" fill="#c62828">'
               f'validator 0 — Byzantine</text>')

    # round rulers
    for r in range(7):
        x = X0 + DX * r
        out.append(f'<text x="{x}" y="36" font-size="15" fill="#555" '
                   f'text-anchor="middle">round {r}</text>')
        a = ANCHOR[r]
        lab = "anchor 8, 12" if r == 2 else f"anchor {a}"
        out.append(f'<text x="{x}" y="56" font-size="12" fill="#888" '
                   f'text-anchor="middle">{lab}</text>')
    for c in range(4):
        out.append(f'<text x="66" y="{Y0 + DY * c + 5}" font-size="13" fill="#888">'
                   f'v{c}</text>')

    # every reference, faint
    special = set(SUPPORT_8) | set(SUPPORT_12) | set(ANCHOR19)
    for a, bs in REFS.items():
        for b in bs:
            if (a, b) not in special:
                out.append(edge(a, b, "#e2e2e2", 1.4))

    # the reference 19 does not carry
    out.append(edge(*MISSING, "#c62828", 2, ' stroke-dasharray="7,5"'))
    mx = pos(14)[0] + (pos(19)[0] - pos(14)[0]) * 0.34
    my = pos(14)[1] + (pos(19)[1] - pos(14)[1]) * 0.34
    out.append(f'<text x="{mx}" y="{my - 12}" font-size="12" fill="#c62828" '
               f'text-anchor="middle">19 omits 14</text>')

    for a, b in ANCHOR19:
        out.append(edge(a, b, "#1565c0", 2.4, "", ' marker-end="url(#ab)"'))
    for a, b in SUPPORT_8:
        out.append(edge(a, b, "#2e7d32", 2.6, "", ' marker-end="url(#ag)"'))
    for a, b in SUPPORT_12:
        out.append(edge(a, b, "#c62828", 2.6, "", ' marker-end="url(#ar)"'))
    for a, b in DESCENT:
        out.append(edge(a, b, "#6a1b9a", 3.2, ' stroke-dasharray="2,6" '
                        'stroke-linecap="round"', ' marker-end="url(#ap)"'))

    # blocks
    for i in range(29):
        x, y = pos(i)
        fill = "#ffffff"
        if i == 8:
            fill = "#dff0d8"
        elif i == 12:
            fill = "#f8d7da"
        elif i == 19:
            fill = "#dbe9f7"
        w = 3 if i in ANCHORS else 1.3
        stroke = "#333333" if i in ANCHORS else "#aaaaaa"
        out.append(f'<circle cx="{x}" cy="{y}" r="{R}" fill="{fill}" '
                   f'stroke="{stroke}" stroke-width="{w}"/>')
        out.append(f'<text x="{x}" y="{y + 5}" font-size="15" fill="#222" '
                   f'text-anchor="middle">{i}</text>')
        if i in COMMITTED:
            out.append(f'<circle cx="{x}" cy="{y}" r="{R + 5}" fill="none" '
                       f'stroke="#333333" stroke-width="1.2"/>')

    # captions on the two twins
    out.append(f'<text x="{pos(8)[0] - R - 8}" y="{pos(8)[1] + 5}" font-size="12" '
               f'fill="#2e7d32" text-anchor="end">3 supporters</text>')
    out.append(f'<text x="{pos(12)[0] - R - 8}" y="{pos(12)[1] + 5}" font-size="12" '
               f'fill="#c62828" text-anchor="end">1 supporter</text>')

    # legend
    ly = H - 196
    rows = [
        ("#2e7d32", "solid", "support for 8, and 14 links it: 8 is committed by the rule"),
        ("#c62828", "solid", "support for 12: one validator, so the rule never admits it"),
        ("#1565c0", "solid", "the references of the round-4 anchor 19"),
        ("#c62828", "dash", "the reference 19 does not carry — 3 of 4 suffice, so this is legal"),
        ("#6a1b9a", "dot", "the descent of commit(19): no round-3 anchor in its cone, "
                           "so it skips round 3 and meets both twins"),
    ]
    for n, (col, kind, text) in enumerate(rows):
        y = ly + n * 26
        dash = ' stroke-dasharray="7,5"' if kind == "dash" else (
            ' stroke-dasharray="2,6"' if kind == "dot" else '')
        out.append(f'<line x1="66" y1="{y}" x2="118" y2="{y}" stroke="{col}" '
                   f'stroke-width="2.6"{dash}/>')
        out.append(f'<text x="130" y="{y + 5}" font-size="13" fill="#333">{text}</text>')

    out.append(f'<text x="66" y="{ly + 5 * 26 + 16}" font-size="13" fill="#111">'
               f'The first validator has 17, 18 and 20 in view at delivery(4), sees 14 supported, and '
               f'commits 8. The second lacks those three — all</text>')
    out.append(f'<text x="66" y="{ly + 5 * 26 + 36}" font-size="13" fill="#111">'
               f'asynchrony allows, and Agreement is a safety property — so its attempt fails, and the '
               f'protocol never retries a round; it commits 19 at</text>')
    out.append(f'<text x="66" y="{ly + 5 * 26 + 56}" font-size="13" fill="#111">'
               f'round 6 instead, whose descent takes 12. Both twins are then flushed by the second '
               f'validator and share one author and round, so L27 must</text>')
    out.append(f'<text x="66" y="{ly + 5 * 26 + 76}" font-size="13" fill="#111">'
               f'drop one: filter, and Agreement fails; do not filter, and Integrity does — it forbids '
               f'two outputs for one party and round, whatever the block.</text>')

    out.append('</svg>')
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text("\n".join(out) + "\n")
    print(f"{OUT.relative_to(ROOT)}: 29 blocks, {sum(len(v) for v in REFS.values())} references")


if __name__ == "__main__":
    main()
