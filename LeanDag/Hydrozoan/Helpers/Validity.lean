import LeanDag.Hydrozoan.Validity.Statement
import LeanDag.Hydrozoan.Delivery.Proof
import LeanDag.Common.SynchronisedReach
import LeanDag.Common.History
import Mathlib.Data.Finset.Sort
/-!
# Helpers: validity

Generated: the list-level half of validity, free of any decision rule and
so shared with the Optimal arc — a committed leader's listing is in the
ledger, a ledger entry comes from a committed leader, and under the
paper's key a non-Byzantine author's block is the only one of its key.
And the listing both hypotheses on `lin` are met by: the causal history
in identifier order, FinWhale's `histOf`.
-/

namespace LeanDag

namespace Hydrozoan

namespace Validity

open LeanDag.Hydrozoan.PrefixAgreement (ledger)
open LeanDag.Hydrozoan.Delivery (delivered authorRound)

variable {BlockId : Type*}

/-- What a committed leader lists is in the ledger. -/
theorem mem_ledger_of_commit {lin : BlockId → List BlockId} {g : ℕ → Option BlockId}
    {n k : ℕ} {L x : BlockId} (hk : k < n) (hg : g k = some L) (hx : x ∈ lin L) :
    x ∈ ledger lin g n :=
  List.mem_flatMap.mpr ⟨L, List.mem_filterMap.mpr ⟨k, List.mem_range.mpr hk, hg⟩, hx⟩

/-- A ledger entry is listed by a committed leader. -/
theorem exists_commit_of_mem_ledger {lin : BlockId → List BlockId} {g : ℕ → Option BlockId}
    {n : ℕ} {c : BlockId} (hc : c ∈ ledger lin g n) :
    ∃ j, j < n ∧ ∃ L, g j = some L ∧ c ∈ lin L := by
  obtain ⟨L, hL, hcL⟩ := List.mem_flatMap.mp hc
  obtain ⟨j, hj, hgj⟩ := List.mem_filterMap.mp hL
  exact ⟨j, List.mem_range.mp hj, L, hgj, hcL⟩

/-- What a committed leader lists has its key delivered. -/
theorem key_delivered_of_commit {κ : Type} [DecidableEq κ] (key : BlockId → κ)
    {lin : BlockId → List BlockId} {g : ℕ → Option BlockId} {n k : ℕ} {L x : BlockId}
    (hk : k < n) (hg : g k = some L) (hx : x ∈ lin L) :
    ∃ c ∈ delivered key lin g n, key c = key x :=
  (Delivery.faithful κ key lin g n).2 x (mem_ledger_of_commit hk hg hx)

section Record

variable {Validator Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- An honest author's block is the only block of the universe with its
author and round. -/
theorem eq_of_authorRound_eq {x c : BlockId} (hx : x ∈ U.ids) (hc : c ∈ U.ids)
    (hxh : (U.block x).creator ∈ honest)
    (hkey : authorRound U.block c = authorRound U.block x) : c = x := by
  simp only [authorRound, Prod.mk.injEq] at hkey
  exact (U.no_equivocation x hx c hc hxh hkey.1.symm hkey.2.symm).symm

end Record

section Listing

variable {Replica : Type*} [Fintype Replica] [DecidableEq Replica] [LinearOrder BlockId]
  [F : LeanDag.Hydrozoan.Faults Replica]

/-- A leader's causal history, in identifier order. -/
def historyListing (U : BlockUniverse Replica BlockId) (L : BlockId) : List BlockId :=
  (history U L).sort (· ≤ ·)

/-- It lists the causal history ... -/
theorem listsHistory_historyListing (U : BlockUniverse Replica BlockId) :
    ListsHistory U (historyListing U) :=
  fun _ hL _ h => (Finset.mem_sort _).mpr ((mem_history_iff hL).mpr h)

/-- ... and nothing foreign. -/
theorem listsWithin_historyListing (U : BlockUniverse Replica BlockId) :
    ListsWithin U (historyListing U) :=
  fun _ hL _ hx => history_subset_ids hL ((Finset.mem_sort _).mp hx)

end Listing

end Validity

end Hydrozoan

end LeanDag
