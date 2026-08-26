#!/usr/bin/env python3
"""Draw the DAG and the two delivered orders that refute Total order.

The execution of `LeanDagTest/BlackMarlin/Divergence.lean`: above, the DAG,
with the one reference that separates the equivocator's twins; below, the two
`ab-deliver` sequences that `commitSeq` — Algorithm 1's own recursion —
computes from it. Blocks `5` and `7` are authored by reliable validators and
come out in opposite orders.

    scripts/black-marlin-order-figure.py  ->  docs/figures/black-marlin-order.svg
"""
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "docs/figures/black-marlin-order.svg"

ROUND, CREATOR = {}, {}
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

ANCHOR = {0: 3, 1: 7, 2: "8, 12", 3: 14, 4: 19, 5: 24, 6: 26}
ANCHORS = {3, 7, 8, 12, 14, 19, 24, 26}
COMMITTED = {8, 19}
DESCENT = [(19, 12), (12, 7), (7, 3)]     # the second validator's descent
SPLIT = {(8, 5): "#e65100", (12, 7): "#00695c"}   # the twins' differing refs

MARK = {5: "#e65100", 7: "#00695c"}
TWIN = {8: "#dff0d8", 12: "#f8d7da"}

# Segments as `commitSeq` emits them: (anchor of the invocation, blocks).
V_SEGS = [(3, [3]), (8, [0, 1, 2, 4, 5, 6, 8]), (7, [7]), (12, []),
          (19, [9, 10, 11, 13, 15, 16, 19])]
W_SEGS = [(3, [3]), (7, [1, 2, 7]), (12, [0, 4, 6, 12]),
          (19, [5, 9, 10, 11, 13, 15, 16, 19])]

DX0, DDX, DY0, DDY, DR, TWIN_Y = 118, 170, 214, 74, 19, 146
X0, DX, R = 116, 73, 20
VY, WY = 696, 928


def dpos(i):
    return DX0 + DDX * ROUND[i], (TWIN_Y if i == 12 else DY0 + DDY * CREATOR[i])


def edge(a, b, stroke, width, dash="", arrow=""):
    (x1, y1), (x2, y2) = dpos(a), dpos(b)
    dx, dy = x2 - x1, y2 - y1
    d = (dx * dx + dy * dy) ** 0.5
    ux, uy = dx / d, dy / d
    return (f'<line x1="{x1 - ux * DR:.1f}" y1="{y1 - uy * DR:.1f}" '
            f'x2="{x2 + ux * DR:.1f}" y2="{y2 + uy * DR:.1f}" '
            f'stroke="{stroke}" stroke-width="{width}"{dash}{arrow}/>')


def dag(out):
    out.append(f'<rect x="58" y="{DY0 - 30}" width="1210" height="60" fill="#fdf1f1"/>')
    out.append(f'<text x="64" y="{DY0 - 38}" font-size="12" fill="#c62828">'
               f'validator 0 — Byzantine</text>')
    for r in range(7):
        x = DX0 + DDX * r
        out.append(f'<text x="{x}" y="96" font-size="14" fill="#555" '
                   f'text-anchor="middle">round {r}</text>')
        out.append(f'<text x="{x}" y="112" font-size="11" fill="#999" '
                   f'text-anchor="middle">anchor {ANCHOR[r]}</text>')
    for c in range(4):
        out.append(f'<text x="64" y="{DY0 + DDY * c + 5}" font-size="12" fill="#999">'
                   f'v{c}</text>')
    for a, bs in REFS.items():
        for b in bs:
            if (a, b) not in SPLIT:
                out.append(edge(a, b, "#e6e6e6", 1.3))
    for a, b in DESCENT:
        out.append(edge(a, b, "#6a1b9a", 2.8, ' stroke-dasharray="2,6" '
                        'stroke-linecap="round"', ' marker-end="url(#ap)"'))
    for (a, b), col in SPLIT.items():
        out.append(edge(a, b, col, 3.0, "", f' marker-end="url(#{"mo" if b == 5 else "mt"})"'))
    for i in range(29):
        x, y = dpos(i)
        fill = TWIN.get(i, "#dbe9f7" if i == 19 else "#ffffff")
        stroke = MARK.get(i, "#333333" if i in ANCHORS else "#bbbbbb")
        w = 3.4 if i in MARK else (2.6 if i in ANCHORS else 1.2)
        out.append(f'<circle cx="{x}" cy="{y}" r="{DR}" fill="{fill}" '
                   f'stroke="{stroke}" stroke-width="{w}"/>')
        out.append(f'<text x="{x}" y="{y + 5}" font-size="13" '
                   f'fill="{MARK.get(i, "#222")}" text-anchor="middle">{i}</text>')
        if i in COMMITTED:
            out.append(f'<circle cx="{x}" cy="{y}" r="{DR + 5}" fill="none" '
                       f'stroke="#333333" stroke-width="1.1"/>')
    return


def heading(y, label, sub):
    return [f'<rect x="18" y="{y - 106}" width="{len(label) * 8.2 + 12}" height="22" '
            f'fill="#ffffff"/>',
            f'<text x="24" y="{y - 90}" font-size="15" fill="#111">{label}</text>',
            f'<rect x="18" y="{y - 84}" width="{len(sub) * 6.4 + 12}" height="19" '
            f'fill="#ffffff"/>',
            f'<text x="24" y="{y - 70}" font-size="12" fill="#777">{sub}</text>']


def row(segs, y, out):
    pos, i, empty = {}, 0, []
    for anchor, blocks in segs:
        if not blocks:
            empty.append((anchor, X0 + DX * i - DX // 2))
            continue
        x1 = X0 + DX * i - R - 8
        x2 = X0 + DX * (i + len(blocks) - 1) + R + 8
        out.append(f'<rect x="{x1}" y="{y - R - 14}" width="{x2 - x1}" '
                   f'height="{2 * R + 28}" rx="10" fill="none" stroke="#cccccc" '
                   f'stroke-width="1.2"/>')
        out.append(f'<text x="{(x1 + x2) / 2}" y="{y - R - 22}" font-size="12" '
                   f'fill="#888" text-anchor="middle">commit({anchor})</text>')
        for b in blocks:
            x = X0 + DX * i
            pos[b] = x
            out.append(f'<circle cx="{x}" cy="{y}" r="{R}" '
                       f'fill="{TWIN.get(b, "#ffffff")}" '
                       f'stroke="{MARK.get(b, "#bbbbbb")}" '
                       f'stroke-width="{3.4 if b in MARK else 1.3}"/>')
            out.append(f'<text x="{x}" y="{y + 5}" font-size="14" '
                       f'fill="{MARK.get(b, "#222")}" text-anchor="middle">{b}</text>')
            i += 1
    return pos, empty


def main():
    W, H = 1330, 1216
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" '
           f'viewBox="0 0 {W} {H}" font-family="Helvetica,Arial,sans-serif">',
           f'<rect width="{W}" height="{H}" fill="#ffffff"/>',
           '<defs>',
           '<marker id="mo" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" '
           'markerHeight="6" orient="auto"><path d="M0,0 L10,5 L0,10 z" fill="#e65100"/></marker>',
           '<marker id="mt" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" '
           'markerHeight="6" orient="auto"><path d="M0,0 L10,5 L0,10 z" fill="#00695c"/></marker>',
           '<marker id="ap" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" '
           'markerHeight="6" orient="auto"><path d="M0,0 L10,5 L0,10 z" fill="#6a1b9a"/></marker>',
           '</defs>',
           '<text x="24" y="40" font-size="17" fill="#111">The DAG, and the two orders it '
           'delivers</text>',
           '<text x="24" y="64" font-size="13" fill="#666">The equivocator\'s twins differ '
           'in one reference: refs(8) = {4, 5, 6} takes 5 and not 7, refs(12) = {4, 6, 7} '
           'takes 7 and not 5. Those two edges are drawn in colour.</text>']
    dag(out)

    out.append('<line x1="80" y1="502" x2="132" y2="502" stroke="#6a1b9a" '
               'stroke-width="2.6" stroke-dasharray="2,6" stroke-linecap="round"/>')
    out.append('<text x="144" y="507" font-size="12" fill="#333">the second validator\'s '
               'descent, 19 → 12 → 7 → 3</text>')
    out.append('<circle cx="470" cy="502" r="8" fill="none" stroke="#333333" '
               'stroke-width="2.2"/>')
    out.append('<circle cx="470" cy="502" r="12" fill="none" stroke="#333333" '
               'stroke-width="1.1"/>')
    out.append('<text x="492" y="507" font-size="12" fill="#333">committed by the rule — '
               '8 at delivery(4) and 19 at delivery(6); 12 never is</text>')
    out.append(f'<line x1="24" y1="536" x2="{W - 24}" y2="536" stroke="#dddddd" '
               f'stroke-width="1"/>')
    out.append('<text x="24" y="570" font-size="13" fill="#666">Below: the blocks in the '
               'order each validator ab-delivers them, boxed by the invocation of commit '
               'that emitted each group.</text>')

    vp, ve = row(V_SEGS, VY, out)
    wp, we = row(W_SEGS, WY, out)
    for b, marker in ((5, "mo"), (7, "mt")):
        col, x1, x2 = MARK[b], vp[b], wp[b]
        out.append(f'<path d="M{x1},{VY + R + 16} C{x1},{VY + 110} {x2},{WY - 110} '
                   f'{x2},{WY - R - 20}" fill="none" stroke="{col}" stroke-width="2.6" '
                   f'stroke-dasharray="6,5" marker-end="url(#{marker})"/>')
    out.append(f'<text x="{wp[5]}" y="{WY + R + 34}" font-size="13" fill="#e65100" '
               f'text-anchor="middle">5 arrives late</text>')
    out.append(f'<text x="{wp[7]}" y="{WY + R + 34}" font-size="13" fill="#00695c" '
               f'text-anchor="middle">7 arrives early</text>')
    out += heading(VY, "first validator — commits 8 at delivery(4), then 19 at delivery(6)",
                   "delivery(4) emits the first two boxes; delivery(6) emits the rest")
    out += heading(WY, "second validator — delivery(4) fails, commits 19 at delivery(6)",
                   "a single invocation, descending 19 → 12 → 7 → 3 before emitting anything")
    for anchor, x in ve:
        msg = f'commit({anchor}) emits nothing — 12 is dropped by L27'
        out.append(f'<rect x="{x - len(msg) * 3.2}" y="{VY + R + 22}" '
                   f'width="{len(msg) * 6.4}" height="19" fill="#ffffff"/>')
        out.append(f'<text x="{x}" y="{VY + R + 36}" font-size="12" '
                   f'fill="#c62828" text-anchor="middle">{msg}</text>')

    ly = H - 128
    tail = [
        "The twins differ in one reference: 8 takes 5 and 12 takes 7. So 5 lies in the cone "
        "of one twin and 7 in the cone of the other, and each validator",
        "delivers whichever falls in the segment of the twin it committed, taking the other "
        "only later. The first delivers 5 before 7 and the second 7 before 5,",
        "so Definition 1's Total order fails. Neither block is a twin and neither is authored "
        "by the equivocator — 7 is the anchor of round 1, an honest leader's",
        "block — so no rule for choosing among twins repairs this; only one that makes the two "
        "descents agree, which no validator can run from its own view.",
    ]
    for n, text in enumerate(tail):
        out.append(f'<text x="24" y="{ly + n * 20}" font-size="13" fill="#111">{text}</text>')

    out.append('</svg>')
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text("\n".join(out) + "\n")
    v = [b for _, bs in V_SEGS for b in bs]
    w = [b for _, bs in W_SEGS for b in bs]
    print(f"{OUT.relative_to(ROOT)}: 29 blocks, "
          f"{sum(len(x) for x in REFS.values())} references; "
          f"5 at {v.index(5)}/{w.index(5)}, 7 at {v.index(7)}/{w.index(7)}")


if __name__ == "__main__":
    main()
