#!/usr/bin/env python3
"""Two mechanical checks on docs/report.md, per docs/style.md section 4.

  1. every section cross-reference names a section that exists;
  2. every backticked Lean identifier names a declaration that exists.

The declaration list is read from docs/depgraph/deps.tsv, the extraction of
the compiled environment that also drives the support diagrams. Regenerate
it (see docs/depgraph/README.md) before trusting a failure from check 2.

    scripts/audit-report.py [report.md ...]

Exit status is 1 if anything failed, so it can gate a commit.
"""
import re
import sys
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent

# A backticked token is treated as a Lean name only if it looks like one:
# a dotted or underscored identifier, not a file path and not English prose.
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_.'′]*$")
FILE_SUFFIX = re.compile(r"\.(lean|md|py|sh|tsv|svg|pdf|toml|yml|json)$")
# Words that are legitimately backticked in the report but are not declarations.
ALLOW = {
    "sorry", "decide", "omega", "simp", "rfl", "native_decide", "propext",
    "Classical.choice", "Quot.sound", "true", "false", "n", "f", "r", "k",
    # Lean core and Mathlib names the report mentions; the extraction keeps
    # only this development's declarations, so these cannot be checked here.
    "Environment.constants", "ConstantInfo.value", "Finset.card", "Fintype.card",
    "Finset.filter", "Finset.min", "Nat.succ", "refs.card",
}


def sections(text):
    """Section numbers that exist, e.g. {'1', '1.1', '10.3', 'A'}."""
    found = set()
    for line in text.splitlines():
        m = re.match(r"^#{2,4}\s+(?:Appendix\s+([A-Z])|([0-9]+(?:\.[0-9]+)*))[.:]?\s", line)
        if m:
            found.add(m.group(1) or m.group(2))
    return found


def declarations(tsv):
    """Fully-qualified declaration names from the extraction."""
    names = set()
    for line in tsv.splitlines():
        parts = line.split("\t")
        if len(parts) >= 2 and parts[0] == "NODE":
            names.add(parts[1])
    return names


def resolves(name, decls, suffixes):
    """A report name resolves if it is a declaration or a suffix of one.

    The report also writes projections applied to a variable — `U.block` for
    `BlockUniverse.block`, `V.ids` for `View.ids` — so a dotted name whose
    tail resolves is accepted too.
    """
    if name in decls or name in suffixes:
        return True
    return "." in name and name.split(".")[-1] in suffixes


def audit(path, decls, suffixes):
    text = path.read_text()
    failures = []

    have = sections(text)
    for ref in sorted(set(re.findall(r"§([0-9]+(?:\.[0-9]+)*|[A-Z]\b)", text))):
        if ref not in have:
            # a bare "§10" is satisfied by the existence of section 10
            failures.append(("xref", ref))

    seen = set()
    for tok in re.findall(r"`([^`\n]+)`", text):
        tok = tok.strip()
        if tok in seen or tok in ALLOW:
            continue
        seen.add(tok)
        if not IDENT.match(tok):
            continue
        if FILE_SUFFIX.search(tok) or "/" in tok:
            continue
        if "_" not in tok and "." not in tok:
            continue  # a single English word, not a Lean name
        if not resolves(tok, decls, suffixes):
            failures.append(("ident", tok))

    print(f"{path.relative_to(ROOT)}: {len(have)} sections, {len(seen)} distinct backticked tokens")
    for kind, item in failures:
        label = "unresolved section" if kind == "xref" else "unknown declaration"
        print(f"  FAIL {label}: {item}")
    if not failures:
        print("  ok")
    return len(failures)


def main(argv):
    tsv = ROOT / "docs/depgraph/deps.tsv"
    if not tsv.exists():
        sys.exit(f"missing {tsv}; see docs/depgraph/README.md to regenerate")
    decls = declarations(tsv.read_text())
    suffixes = {n.split(".", 1)[1] for n in decls if "." in n}
    for n in list(suffixes):
        while "." in n:
            n = n.split(".", 1)[1]
            suffixes.add(n)

    paths = [pathlib.Path(a) for a in argv[1:]] or [ROOT / "docs/report.md"]
    bad = sum(audit(p, decls, suffixes) for p in paths)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main(sys.argv)
