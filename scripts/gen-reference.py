#!/usr/bin/env python3
"""Generate the report's definition reference from the compiled source.

Every definition and structure of the development, verbatim, with the
docstring the source already carries. Regenerating tracks the code, so the
reference cannot drift; `audit-report.py` check 4 then compares what is
written against the same extraction on every run.

    scripts/extract-decls.py && scripts/gen-reference.py

Output replaces whatever lies between the two markers in docs/report.md.
Text outside them is hand-written and is never touched.
"""
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parent.parent
BEGIN = "<!-- BEGIN GENERATED REFERENCE -->"
END = "<!-- END GENERATED REFERENCE -->"

# Modules in the order a reader meets them, grouped into layers.
LAYERS = [
    ("The validator set and the fault model", ["Validators"]),
    ("Blocks, validity, and the universe", ["Block", "BlockDag"]),
    ("Causal structure", ["CausalHistory", "History", "Support", "CommonCore"]),
    ("Slots and the schedule", ["Schedule"]),
    ("The commit rule, and the ledger", ["Mysticeti"]),
    ("Delivery, growth, and coverage", ["Liveness", "Network.Quorum"]),
    ("Time: GST, drift, and the backoff", ["Timing", "Quantitative"]),
    ("View convergence", ["ViewSync"]),
    ("Chain quality", ["Quality.Coverage", "Quality.Inclusion", "Quality.Capstone"]),
    ("Denial of service", ["DoS.Exposure", "DoS.Density", "DoS.Counting",
                           "DoS.Adoption", "DoS.Pedigree", "DoS.Exclusion",
                           "DoS.Acceptance", "DoS.Novelty", "DoS.Composition",
                           "DoS.SafetyUnderDoS"]),
    ("Garbage collection", ["GC.Chop", "GC.ChopDecided", "GC.Window",
                            "GC.AttestedBase", "GC.Bootstrap", "GC.Horizon"]),
    ("Odontoceti", ["Odontoceti.Rules", "Odontoceti.Decision",
                    "Odontoceti.Liveness"]),
]

KINDS = ("def", "abbrev", "structure", "class", "inductive")


def tidy(doc):
    """The docstring as prose: bold markers kept, hard wraps joined."""
    if not doc:
        return ""
    doc = re.sub(r"\n\s*\n", "\x00", doc.strip())
    doc = re.sub(r"\s*\n\s*", " ", doc)
    return doc.replace("\x00", "\n\n")


def main():
    decls = json.loads((ROOT / "docs/decls.json").read_text())
    lib = [d for d in decls if d["module"].startswith("LeanDag.")
           and d["kind"] in KINDS]
    by_module = {}
    for d in lib:
        by_module.setdefault(d["module"].removeprefix("LeanDag."), []).append(d)

    placed = set()
    out = [BEGIN, ""]
    out.append("Every definition and structure of the development, in the order")
    out.append("a reader meets them. Each entry is the source text, unabridged,")
    out.append("with the explanation the source carries. This appendix is")
    out.append("generated from the compiled development by")
    out.append("`scripts/gen-reference.py`; the statements are therefore the")
    out.append("declarations themselves rather than transcriptions of them.")
    out.append("")

    n = 0
    for title, modules in LAYERS:
        entries = [d for m in modules for d in by_module.get(m, [])]
        if not entries:
            continue
        out.append(f"### {title}")
        out.append("")
        for d in entries:
            placed.add(d["name"] + "@" + d["module"])
            n += 1
            mod = d["module"].removeprefix("LeanDag.")
            out.append(f"#### `{d['name']}`")
            out.append("")
            out.append(f"*{d['kind']}, `{mod}.lean`*")
            out.append("")
            out.append("```lean")
            out.append(d["statement"])
            out.append("```")
            out.append("")
            doc = tidy(d["doc"])
            if doc:
                out.append(doc)
                out.append("")

    leftover = [d for d in lib if d["name"] + "@" + d["module"] not in placed]
    if leftover:
        out.append("### Not otherwise grouped")
        out.append("")
        for d in leftover:
            n += 1
            mod = d["module"].removeprefix("LeanDag.")
            out.append(f"#### `{d['name']}`")
            out.append("")
            out.append(f"*{d['kind']}, `{mod}.lean`*")
            out.append("")
            out.append("```lean")
            out.append(d["statement"])
            out.append("```")
            out.append("")
            doc = tidy(d["doc"])
            if doc:
                out.append(doc)
                out.append("")

    out.append(END)
    body = "\n".join(out)

    report = ROOT / "docs/report.md"
    text = report.read_text()
    if BEGIN in text and END in text:
        a = text.index(BEGIN)
        b = text.index(END) + len(END)
        text = text[:a] + body + text[b:]
    else:
        text = text.rstrip("\n") + "\n\n" + body + "\n"
    report.write_text(text)
    print(f"{n} definitions written; {len(leftover)} ungrouped")


if __name__ == "__main__":
    main()
