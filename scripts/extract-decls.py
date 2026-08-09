#!/usr/bin/env python3
"""Extract every declaration of the development with its docstring and statement.

The report displays hundreds of statements verbatim; typing them by hand
would guarantee drift, and `audit-report.py` check 3 exists because it
happened. This reads them from the source instead.

    scripts/extract-decls.py            # writes docs/decls.json
    scripts/extract-decls.py --summary  # counts only

For each declaration it records the module, kind, the docstring (the
project writes one for nearly everything, and those are the explanations
the report needs), the statement up to the proof, and whether the proof
follows on the same line. Statements are captured with balanced-delimiter
tracking rather than by looking for `:=`, since named arguments such as
`(Validator := Validator)` contain that token.
"""
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
KINDS = r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)"
DECL = re.compile(
    rf"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)?"
    rf"({KINDS})\s+([A-Za-z_][A-Za-z0-9_.'′]*)"
)
ATTR = re.compile(r"^@\[[^\]]*\]\s*$")
# A declaration may be anonymous (`instance : Decidable … := by`), which the
# named pattern above misses; a body must still stop at one.
ANY_DECL = re.compile(
    rf"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)?{KINDS}\b")


def strip_docstring(lines):
    """Return the docstring body of a `/-- … -/` block, unwrapped."""
    text = "\n".join(lines)
    text = re.sub(r"^/--\s*", "", text)
    text = re.sub(r"\s*-/$", "", text)
    return text.strip()


def body_of(lines, start):
    """A definition's full text: signature and body, to the next declaration.

    For a `def` the body is the content the report must show, and a
    structure has no proof at all, so neither is cut at `:=`. Cutting them
    at the proof marker also truncated structures at the first `by`
    appearing inside a field docstring.
    """
    out = []
    for k, raw in enumerate(lines[start:], start):
        if k > start and (ANY_DECL.match(raw) or raw.startswith(("/--", "/-!"))
                          or ATTR.match(raw)
                          or raw.startswith(("omit ", "variable", "open ", "end ",
                                             "section", "namespace"))):
            break
        if k > start and not raw.strip() and out and not out[-1].strip():
            break
        out.append(raw.rstrip())
    return "\n".join(out).rstrip()


def statement_of(lines, start):
    """The declaration's statement: everything up to where the proof begins.

    Tracks bracket depth so that a `:=` inside a named argument or an
    anonymous constructor does not end the statement early. The proof
    begins at a top-level `:=` or a top-level `by`.
    """
    out = []
    depth = 0
    for raw in lines[start:]:
        line = raw
        cut = None
        i = 0
        while i < len(line):
            c = line[i]
            if c in "([{⟨":
                depth += 1
            elif c in ")]}⟩":
                depth -= 1
            elif depth == 0 and line.startswith(":=", i):
                cut = i
                break
            elif depth == 0 and re.match(r"\bby\b", line[i:]) and i > 0 \
                    and line[i - 1] in " \t":
                cut = i
                break
            i += 1
        if cut is not None:
            tail = line[:cut].rstrip()
            if tail:
                out.append(tail)
            return "\n".join(out).rstrip(), True
        out.append(line.rstrip())
        # a blank line at depth 0 ends a declaration with no explicit proof
        if not line.strip() and depth == 0 and out:
            break
    return "\n".join(out).rstrip(), False


def parse(path):
    lines = path.read_text().split("\n")
    module = str(path.relative_to(ROOT)).replace("/", ".").removesuffix(".lean")
    decls = []
    i = 0
    doc = None
    while i < len(lines):
        line = lines[i]
        if line.startswith("/--") or line.startswith("/-!"):
            # Lean block comments nest, and a docstring may quote `-/`, so
            # close on depth rather than on the first terminator.
            depth = 0
            j = i
            while j < len(lines):
                depth += lines[j].count("/-") - lines[j].count("-/")
                if depth <= 0:
                    break
                j += 1
            # a `/-!` section comment documents the section, not the next
            # declaration, so it is read past rather than attached
            doc = strip_docstring(lines[i:j + 1]) if line.startswith("/--") else None
            i = j + 1
            continue
        m = DECL.match(line)
        if m is None and ATTR.match(line) and i + 1 < len(lines):
            m = DECL.match(lines[i + 1])
            if m:
                i += 1
                line = lines[i]
        if m:
            if m.group(1) in ("def", "abbrev", "instance",
                              "structure", "class", "inductive"):
                stmt = body_of(lines, i)
            else:
                stmt, _ = statement_of(lines, i)
            decls.append({
                "name": m.group(2),
                "kind": m.group(1),
                "module": module,
                "line": i + 1,
                "doc": doc or "",
                "statement": stmt,
            })
            doc = None
            i += 1
            continue
        if line.strip() and not line.startswith("--"):
            doc = None      # a docstring only attaches to what follows it
        i += 1
    return decls


def main():
    out = []
    for d in ("LeanDag", "LeanDagTest"):
        for f in sorted((ROOT / d).rglob("*.lean")):
            out.extend(parse(f))
    lib = [x for x in out if x["module"].startswith("LeanDag.")]
    documented = sum(1 for x in lib if x["doc"])
    print(f"{len(out)} declarations parsed ({len(lib)} in LeanDag)")
    print(f"  with docstrings: {documented} / {len(lib)} "
          f"({100 * documented // max(len(lib), 1)}%)")
    by_kind = {}
    for x in lib:
        by_kind[x["kind"]] = by_kind.get(x["kind"], 0) + 1
    print("  by kind: " + ", ".join(f"{k}={v}" for k, v in sorted(by_kind.items())))
    if "--summary" not in sys.argv:
        dest = ROOT / "docs/decls.json"
        dest.write_text(json.dumps(out, indent=1, ensure_ascii=False))
        print(f"  written to {dest.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
