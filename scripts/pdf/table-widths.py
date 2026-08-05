#!/usr/bin/env python3
"""Rewrite markdown pipe-table separator rows with proportional column widths.

Pandoc derives relative column widths from the number of dashes in a pipe
table's separator row. Left to a uniform `|---|`, columns holding Lean
identifiers overflow into their neighbours, because inline code is unbreakable
and cannot wrap. This sizes each column by the longest unbreakable token it
holds, distributes what remains by total content length, and left-aligns
everything.

Operates on a copy; the source document is not modified.
"""
import re
import sys

CODE_WIDTH = 0.82  # monospace renders narrower than prose at the sizes used
MIN_UNITS = 5


def is_row(line):
    s = line.strip()
    return s.startswith("|") and s.endswith("|")


def cells(line):
    return [c.strip() for c in line.strip()[1:-1].split("|")]


def widths(header, body, ncol):
    hard = [0] * ncol   # longest token that cannot be broken across lines
    soft = [0] * ncol   # total content, for distributing the slack
    for row in [header] + body:
        for k, c in enumerate(cells(row)[:ncol]):
            soft[k] = max(soft[k], len(c))
            code = [int(len(t) * CODE_WIDTH) + 1 for t in re.findall(r"`([^`]+)`", c)]
            prose = [len(t) for t in re.split(r"\s+", re.sub(r"`[^`]+`", "", c)) if t]
            hard[k] = max([hard[k]] + code + prose)
    slack = max(0, 100 - sum(hard))
    total = sum(soft) or 1
    return [max(MIN_UNITS, hard[k] + round(slack * soft[k] / total)) for k in range(ncol)]


def main(path):
    lines = open(path).read().split("\n")
    out, i, n = [], 0, 0
    sep_re = re.compile(r"\s*\|[\s:|-]+\|\s*")
    while i < len(lines):
        line = lines[i]
        if (is_row(line) and i + 1 < len(lines)
                and sep_re.fullmatch(lines[i + 1] or "")):
            j = i + 2
            body = []
            while j < len(lines) and is_row(lines[j]):
                body.append(lines[j])
                j += 1
            ncol = len(cells(line))
            units = widths(line, body, ncol)
            out.append(line)
            out.append("|" + "|".join(":" + "-" * u for u in units) + "|")
            out.extend(body)
            n += 1
            i = j
            continue
        out.append(line)
        i += 1
    open(path, "w").write("\n".join(out))
    print(f"table-widths: {n} tables sized in {path}", file=sys.stderr)


if __name__ == "__main__":
    main(sys.argv[1])
