# Minnow — the minimal commit rule, and three defects

The design record for `LeanDag/Minnow/`. The report chapter is §19; this
is where the reasoning behind the model lives.

## 1. What the protocol is, and what is modelled

Minnow separates a DAG protocol into a communication component, which
builds a round-based DAG, and a **commit rule**, which reads it and
returns a sequence of committed vertices. `crs*`, the rule for the
eventually synchronous model, commits a leader vertex when a **quorum**
of `2f + 1` distinct processes point to it from the round above, and
every earlier leader slot is **resolved** — some vertex of it lies in the
candidate's causal past, or is concurrent and either committed or
**skipped**, where skipped means `2f + 1` vertices of the round above
carry no edge to it.

The arc models the rule and nothing downstream of it. Every finding is of
the form "this leader is not committed", and Definition 4 of the paper
says a leader is committed **if and only if** the pattern is enabled, so
the sort, the delivery of non-leader vertices and the round-advance loop
cannot affect any of them.

**Why the DAG type is new.** The rest of this development uses a
`ValidWrt` that requires a non-genesis block to reference a block by its
own author. Minnow does not: section 2 of the paper asks only that
"vertices are valid only if they reference at least `2f + 1` valid
vertices issued in the previous round by distinct processes". Imposing a
self-parent would not be a harmless strengthening — it would force the
faulty process of §3 to point at its own previous vertex, which is one of
the pointers that construction counts. So `Minnow.ValidHere` has exactly
three clauses. `Minnow.Dag` does keep a `correct_single` field — the
core's `no_equivocation` with its correctness guard intact — because
section 2 admits equivocating vertices of *faulty* processes only, and a
correct process issues one vertex a round. Dropping it would admit DAGs
the communication component cannot build.

**Where the paper is ambiguous, the reading is argued rather than
assumed.** Two clauses are written in a way their own sentences do not
support, and §3 settles both: a slot holding no vertex resolves nothing
at the letter, and the skip clause counts vertices where the quorum
clause counts processes. The second reading is the one that matters — the
vertex count is unsound — so `Skipped` is over distinct processes, in
line with every other quorum in the paper and with the rest of this
development, and `SkippedByVertex` is kept only to state what the letter
costs. The leader sequence is genuine round robin over all four processes
rather than one chosen to suit the construction; that choice is recorded
because it could have been made the other way to make a finding look
stronger than it is.

## 2. What the counterexamples rest on

Two theorems, read off Definition 9 and proved rather than assumed.
`quorum_of_committedAt`: a commit needs a quorum, at every position in
`leaders`, since the quorum clause is a conjunct at each.
`not_committedAt_of_dead`: if every vertex of an earlier leader slot lies
outside the candidate's causal past, carries no quorum and cannot be
skipped, the second clause is unsatisfiable.

The second is deliberately weak. It concludes nothing about what *is*
committed — only that a particular leader is not — so it cannot be
accused of resolving the recursion in a way the paper would not.

## 3. Two readings, and two defects

**An empty slot, at the letter, resolves nothing.** Definition 9's second
clause opens "there is a vertex `v′` in slot `s′` in `D` such that …",
and all three ways of resolving a slot sit inside that existential, so a
slot holding no vertex satisfies none of them. That is not the reading to
take: the skip disjunct needs no `v′` at all — it asks that `2f + 1`
vertices of the round above carry no edge into the slot, which an empty
slot satisfies trivially. The model implements the letter because a
formalisation must choose, and the two findings below are unaffected,
turning only on slots that hold exactly one vertex, where the readings
coincide.

**The skip clause, at the letter, counts vertices where the quorum
clause counts processes.** Two lines apart, Definition 9 asks for "a set
`Q` of `2f + 1` vertices issued by distinct processes" and for "`2f + 1`
vertices that do not have an edge to `v′`". A faulty process issuing
three vertices in one round contributes to the second without giving up
its place in the first, and both clauses then hold of one vertex — so two
processes with different views may commit and skip the same slot, which
is Safe-Commit, and §3.2 of the paper obtains Total-order and Agreement
from Safe-Commit. A reading on which the rule is unsafe is not the
reading meant, so the clause is over processes. This is the second
reading settled, not a defect of the rule.

**The dead zone.** Commit needs `a ≥ 2f + 1` pointing processes; skip
needs `2f + 1` non-pointers, so `a ≤ f`. The window `f + 1 ≤ a ≤ 2f` is
neither, and is non-empty for every `f ≥ 1`.

This one cannot be repaired by lowering the threshold. Read the skip
clause over distinct processes with threshold `s`. A view that skips
holds at least `s − f` correct processes with no pointing vertex, and a
correct process issues one vertex a round, so they have none in any view.
A view that commits holds at least `f + 1` correct processes that point.
Those sets are disjoint among the `2f + 1` correct processes, so a
disagreement needs `(s − f) + (f + 1) ≤ 2f + 1`, that is `s ≤ 2f`. So
`2f + 1` is the least safe threshold and the window is forced.

What is left is the causal-past escape, and that is unavailable for
exactly the leaders that follow a dead slot within one round: the other
leader of its own round is concurrent with it, and under round robin the
next round's leaders can be the processes that never received it.

**One dead slot is not enough, and that is the point.** Resolved is not
decided: the first disjunct asks only that some vertex of the slot lie in
the candidate's causal past, and two pointers carry it there in two
rounds, since a vertex references `2f + 1` of the `3f + 1` below it and
cannot miss both. So a dead slot blocks two rounds of leaders and no
more. The witness sustains the habit every cycle — round robin at
`l = 2` over four processes puts the faulty process in a leader slot
every other round, which is exactly the cadence that keeps a fresh dead
slot within reach of every leader — and `crs*` then commits nothing at
all.

**One twin resolves a slot the other commits.** The first disjunct of the
second condition asks only that some vertex of an earlier slot lie in the
candidate's causal past — resolving a slot, not deciding it. Where the
slot's process equivocates it holds two vertices, and the disjunct is
satisfied by whichever is in the way, which need not be the one later
committed. A validator whose view is one short of a twin's quorum sees
that twin undecided, resolves the slot through the other, and commits a
later leader; the missing vertex then arrives and the twin acquires its
quorum, demanding a place before what is already output. That is
Safe-Commit in the form the paper spells out, and with it Total-order and
Agreement.

The equivocation is what does it, and the witness checks the converse: a
slot with one vertex is either resolved by the vertex the rule will
decide, or not resolved at all. Two vertices break the tie between
resolving and deciding. This is the closer analogue of what `report.md`
§18 finds in Black Marlin — a slot with two vertices resolved by a test
that does not read support.

## 4. What is not covered

No attempt is made to prove anything positive about `crs*`, to model
`cra*` — the asynchronous rule — or to assess the minimality claim of
Definition 7 and Theorem 8. The sub-rule relation compares patterns, and
two of the three defects above are defects of the pattern's wording
rather than of its strength, so what they bear on is whether `crs*` is a
commit rule at all rather than whether it is a minimal one.
