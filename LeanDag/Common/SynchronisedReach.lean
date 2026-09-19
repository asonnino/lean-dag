import LeanDag.Common.CausalHistory
/-!
# Synchrony carries causal history

From round `R` on, a `T`-block references every `T`-block of the round
below (`SynchronisedFrom`). While `T` fills the rounds in between
(`PopulatedFrom`), that closes up: a `T`-block at or after `R` lies in
the causal history of every later `T`-block. What Validity consumes, and
the reason no self-parent edge is asked for.
-/

namespace LeanDag

variable {Validator : Type*} {BlockId : Type*} {Payload : Type*}
variable {blk : BlockId → Block Validator BlockId Payload} {ids : Finset BlockId}

/-- Every `T`-block `d + 1` rounds above a `T`-block `x` reaches it, by
induction on `d`: synchrony is the base, and a `T`-block one round down —
there is one, `T` being nonempty and filling that round — is the step. -/
theorem reachesFrom_of_synchronisedFrom {T : Finset Validator} {R : ℕ}
    (hs : SynchronisedFrom blk ids T R) (hne : T.Nonempty) {x : BlockId} (hx : x ∈ ids)
    (hxc : (blk x).creator ∈ T) (hR : R ≤ (blk x).round) :
    ∀ d, (∀ r, (blk x).round < r → r ≤ (blk x).round + d → PopulatedFrom blk ids T r) →
      ∀ c ∈ ids, (blk c).creator ∈ T → (blk c).round = (blk x).round + d + 1 →
        ReachesFrom blk c x := by
  intro d
  induction d with
  | zero =>
    intro _ c hc hcc hcr
    exact ReachesFrom.single (hs _ hR c hc hcr hcc x hx rfl hxc)
  | succ d ih =>
    intro hpop c hc hcc hcr
    obtain ⟨v, hv⟩ := hne
    obtain ⟨m, hm, hmc, hmr⟩ := hpop ((blk x).round + d + 1) (by omega) (by omega) v hv
    have hmT : (blk m).creator ∈ T := hmc ▸ hv
    have href : m ∈ (blk c).refs :=
      hs ((blk x).round + d + 1) (by omega) c hc (by omega) hcc m hm hmr hmT
    exact ReachesFrom.of_mem_refs href
      (ih (fun r h1 h2 => hpop r h1 (by omega)) m hm hmT hmr)

section Record

variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- **A `T`-block lies in the causal history of every later `T`-block**,
from the round of synchrony on and while `T` fills the rounds between. -/
theorem reaches_of_synchronisedOn {T : Finset Validator} {R : ℕ}
    (hs : SynchronisedOn U T R) (hne : T.Nonempty) {x c : BlockId}
    (hx : x ∈ U.ids) (hxc : (U.block x).creator ∈ T) (hR : R ≤ (U.block x).round)
    (hc : c ∈ U.ids) (hcc : (U.block c).creator ∈ T)
    (hlt : (U.block x).round < (U.block c).round)
    (hpop : ∀ r, (U.block x).round < r → r < (U.block c).round → PopulatedOn U T r) :
    Reaches U c x :=
  reachesFrom_of_synchronisedFrom hs hne hx hxc hR
    ((U.block c).round - (U.block x).round - 1) (fun r h1 h2 => hpop r h1 (by omega))
    c hc hcc (by omega)

end Record

end LeanDag
