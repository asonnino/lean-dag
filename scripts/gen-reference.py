#!/usr/bin/env python3
"""Generate the report's reference appendices from the compiled source.

Appendix B holds every definition and structure, Appendix C every theorem
another module depends on, and Appendix D indexes the remaining lemmas.
All are verbatim, with the docstrings the source already carries. Regenerating tracks the code, so the
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
    ("The reactive schedule", ["Reactive.Basic", "Reactive.Mysticeti",
                               "Reactive.Odontoceti"]),
]

KINDS = ("def", "abbrev", "structure", "class", "inductive")


def tidy(doc):
    """The docstring as prose: bold markers kept, hard wraps joined."""
    if not doc:
        return ""
    doc = re.sub(r"\n\s*\n", "\x00", doc.strip())
    doc = re.sub(r"\s*\n\s*", " ", doc)
    return doc.replace("\x00", "\n\n")


def cross_module(root):
    """Names of theorems some other module depends on."""
    import collections
    rdeps = collections.defaultdict(set)
    mod = {}
    for line in (root / "docs/depgraph/deps.tsv").read_text().splitlines():
        p = line.split("\t")
        if p[0] == "NODE":
            mod[p[1]] = p[2]
        elif p[0] == "EDGE":
            rdeps[p[2]].add(p[1])
    out = set()
    for full, m in mod.items():
        if any(mod.get(u) and mod[u] != m for u in rdeps.get(full, ())):
            out.add((full.rsplit(".", 1)[-1], m))
    return out


def entry(d, out):
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


def main():
    decls = json.loads((ROOT / "docs/decls.json").read_text())
    lib = [d for d in decls if d["module"].startswith("LeanDag.")
           and d["kind"] in KINDS]
    by_module = {}
    for d in lib:
        by_module.setdefault(d["module"].removeprefix("LeanDag."), []).append(d)

    placed = set()
    out = [BEGIN, ""]
    out.append("## Appendix B. The definition reference")
    out.append("")
    out.append("Every definition and structure of the development, in the order")
    out.append("a reader meets them. Each entry is the source text, unabridged,")
    out.append("with the explanation the source carries. This appendix is")
    out.append("generated from the compiled development by")
    out.append("`scripts/gen-reference.py`; the statements are therefore the")
    out.append("declarations themselves rather than transcriptions of them.")
    out.append("")
    out.append("Nine entries carry proofs, which can look like a")
    out.append("misclassification. They are not. A structure in Lean may have")
    out.append("fields that are propositions — `BlockUniverse` requires causal")
    out.append("closure, validity and non-equivocation — so *constructing* one")
    out.append("means discharging those obligations, and the proof is part of")
    out.append("the definition rather than a theorem about it. `chop`, `chopD`")
    out.append("and `toDelivery` are of this kind: each builds an object whose")
    out.append("type demands the proofs shown. A theorem, by contrast, asserts")
    out.append("a proposition about objects already built, and those are")
    out.append("Appendix C.")
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

    # ---- Appendix C: the theorems other modules depend on ----
    thms = [d for d in decls if d["module"].startswith("LeanDag.")
            and d["kind"] in ("theorem", "lemma")]
    cross = cross_module(ROOT)
    public = [d for d in thms if (d["name"], d["module"]) in cross]
    internal = [d for d in thms if (d["name"], d["module"]) not in cross]

    out.append("")
    out.append("---")
    out.append("")
    out.append("## Appendix C. The theorem reference")
    out.append("")
    out.append(f"The {len(public)} theorems that another module of the development")
    out.append("depends on: the results the rest of the report reasons with, as")
    out.append("opposed to the steps internal to one file. Each is the source")
    out.append("statement, unabridged. Generated with Appendix B.")
    out.append("")
    seen_c = set()
    for title, modules in LAYERS:
        group = [d for m in modules for d in public
                 if d["module"].removeprefix("LeanDag.") == m]
        if not group:
            continue
        out.append(f"### {title}")
        out.append("")
        for d in group:
            seen_c.add(id(d))
            entry(d, out)
    rest = [d for d in public if id(d) not in seen_c]
    if rest:
        out.append("### Not otherwise grouped")
        out.append("")
        for d in rest:
            entry(d, out)

    # ---- Appendix D: the remaining lemmas, indexed ----
    out.append("---")
    out.append("")
    out.append("## Appendix D. Index of internal lemmas")
    out.append("")
    out.append(f"The {len(internal)} lemmas used only within the file that proves")
    out.append("them. They are steps of the arguments above rather than results")
    out.append("in their own right, so they are listed rather than displayed;")
    out.append("the source is the reference for their statements.")
    out.append("")
    out.append("| Lemma | Module | Role |")
    out.append("|:---|:---|:---|")
    for d in sorted(internal, key=lambda x: (x["module"], x["name"])):
        mod = d["module"].removeprefix("LeanDag.")
        doc = tidy(d["doc"]).split("\n")[0]
        doc = re.sub(r"\*\*", "", doc)
        if len(doc) > 110:
            doc = doc[:107].rsplit(" ", 1)[0] + " …"
        out.append(f"| `{d['name']}` | `{mod}` | {doc or '—'} |")
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
    print(f"{n} definitions, {len(public)} public theorems, "
          f"{len(internal)} indexed lemmas")


if __name__ == "__main__":
    main()
