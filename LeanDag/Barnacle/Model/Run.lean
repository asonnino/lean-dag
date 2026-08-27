import LeanDag.Barnacle.Model.Window

/-!
# Barnacle: the run

The object safety and liveness are stated on (`barnacle.md` §5).
Configurations are indexed `k = 0, 1, …`; configuration `k` is in force
at the rounds above `start k`, with `count k` leaders per round, and its
*range* is the rounds up to and including the next anchor's. Every slot
of the range is decided by the base relation against the configuration's
own schedule, `Sched (count k)` — including whatever decision-anchors
above the next anchor an indirect decision reads, because Algorithm 2
decides under the count in force and switches only afterwards
(`barnacle.md` §5). That is what makes the dependency well-founded
by induction on `k`.

A `PartialRun` is closed up to a configuration height `K`: the ranges
of configurations below `K` are decided in full — through the end of
the anchor's round — and configuration `K` is determined. There is no
total run: every configuration commits an anchor at its own round, and
a universe holds finitely many blocks, so a run closes finitely many
configurations and the paper's *sequence* of configurations is what
every prefix of it agrees on (`barnacle.md` §5).

Slots are numbered per configuration: `vdct k` is a verdict function on
`Sched (count k)`, the object every base theorem speaks about. The round
clauses are written as `κ / count k`, which is `Sched`'s `slotRound`.

The initial configuration is `(0, 1)`: one leader, and `lastRound = 0`
as Algorithm 2 initialises it. Round `0` therefore lies in no range —
faithful to the algorithm, whose first decision walk starts at round
`1`.

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A run closed up to height `K`.** Configurations `0, …, K` are
determined, and the ranges of configurations below `K` are decided in
full.

`closed` is the paper's `TryDecide`: every slot of the range — the
rounds after `start k`, through the anchor's round `start (k + 1)` —
decided against the configuration's schedule. `anchor_commits`
and `anchor_least` are `TryCommit`'s trigger: the anchor is the least
committed slot whose round exceeds `start k + interval`. `update` is
`UpdateLeaders`, for an arbitrary rule. `count_pos` and `count_le` are
clauses of the run because the rule is arbitrary; for the AIMD rule
they are theorems. -/
structure PartialRun (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders)
    (upd : UpdateRule R) (U : R.Universe) (V : R.View U) (K : ℕ) where
  /-- The round after which configuration `k` is in force. -/
  start : ℕ → ℕ
  /-- The leader count of configuration `k`. -/
  count : ℕ → ℕ
  /-- The back-off of configuration `k`. -/
  backoff : ℕ → ℕ
  /-- The slot, in `Sched (count k)`, of the anchor that closes
  configuration `k`. -/
  anchor : ℕ → ℕ
  /-- `vdct k κ`: the verdict of slot `κ` of `Sched (count k)`. -/
  vdct : ℕ → ℕ → Option BlockId
  /-- The initial configuration: one leader after round `0`. -/
  init : start 0 = 0 ∧ count 0 = 1 ∧ backoff 0 = 0
  count_pos : ∀ k, 0 < count k
  count_le : ∀ k, count k ≤ P.maxLeaders
  /-- Every slot of the range is decided against the configuration's
  schedule. -/
  closed : ∀ k, k < K → ∀ κ, start k < κ / count k → κ / count k ≤ start (k + 1) →
    R.Decided (Sched getLeader hk (count k) (count_pos k) (count_le k)) V κ (vdct k κ)
  /-- The anchor is committed, past the threshold … -/
  anchor_commits : ∀ k, k < K →
    (∃ A, vdct k (anchor k) = some A) ∧ start k + P.interval < anchor k / count k
  /-- … and is the least such slot. -/
  anchor_least : ∀ k, k < K → ∀ κ, κ < anchor k →
    start k + P.interval < κ / count k → vdct k κ = none
  /-- The next configuration is in force after the anchor's round. -/
  start_succ : ∀ k, k < K → start (k + 1) = anchor k / count k
  /-- The next configuration is the rule's. -/
  update : ∀ k, k < K → ∀ A, vdct k (anchor k) = some A →
    (count (k + 1), backoff (k + 1)) = upd (count k) (backoff k) U A

variable {R : BaseRule Validator BlockId Payload} {P : Params}
variable {getLeader : ℕ → Validator} {hk : Keyed getLeader P.maxLeaders}
variable {upd : UpdateRule R} {U : R.Universe} {V : R.View U}

/-- The schedule of configuration `k`. -/
abbrev PartialRun.sched {K : ℕ} (Rn : PartialRun R P getLeader hk upd U V K) (k : ℕ) :
    Slots Validator :=
  Sched getLeader hk (Rn.count k) (Rn.count_pos k) (Rn.count_le k)

/-! ## The ledger -/

/-- The committed blocks of the slots `[lo, hi)`, in slot order. -/
def ledgerOf (v : ℕ → Option BlockId) (lo hi : ℕ) : List BlockId :=
  (List.range' lo (hi - lo)).filterMap v

/-- The ledger of configuration `k`: its range's committed blocks, from
the first slot after `start k` to the last slot of round `start (k + 1)`.
Meaningful for the closed configurations, `k < K`. -/
def PartialRun.rangeLedger {K : ℕ} (Rn : PartialRun R P getLeader hk upd U V K) (k : ℕ) :
    List BlockId :=
  ledgerOf (Rn.vdct k) (Rn.count k * (Rn.start k + 1)) (Rn.count k * (Rn.start (k + 1) + 1))

/-- The ledger through configuration `K' − 1`: the ranges' ledgers,
concatenated in configuration order. Meaningful for `K' ≤ K`. -/
def PartialRun.ledgerUpto {K : ℕ} (Rn : PartialRun R P getLeader hk upd U V K) (K' : ℕ) :
    List BlockId :=
  (List.range K').flatMap Rn.rangeLedger

end Barnacle

end LeanDag
