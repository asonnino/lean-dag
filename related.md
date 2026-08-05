# Related work: consensus on uncertified DAGs

**Scope.** This document surveys the protocols that share Mysticeti's central
structural commitment — an *uncertified* DAG, in which no certificate is ever
constructed or transmitted, and certification is instead a property of the graph
recovered by the reader. It is organised around a single question: for each
protocol, what does it re-use from the uncertified-DAG structure, and where does
it depart from Mysticeti?

Certified protocols (Narwhal/Bullshark, Sailfish, Shoal++) appear only in §5, as
contrast points that fix what "uncertified" is defined against, and the
mechanised-verification literature appears in §6, since it bears directly on the
present development.

*Survey compiled 2026-08-05 from published abstracts and papers. Claims below are
attributed to the cited work; where a detail could not be confirmed against the
paper text it is marked* (unconfirmed).

---

## 1. The distinction

In a **certified** DAG, a block is disseminated by reliable broadcast and enters
the DAG only once it carries a quorum of signatures. Every block therefore costs
three message steps — propose, acknowledge, certify — and the reader may assume
that any block it sees is non-equivocated and available, because the certificate
proves it.

In an **uncertified** DAG, a block is disseminated by a single broadcast and
enters the DAG immediately. There is no certificate message and no certificate
round. A block two rounds above a leader constitutes a certificate for that
leader precisely when its own references happen to contain a quorum of blocks
that reference the leader. Certification becomes a *pattern in the graph*,
discovered by each reader independently, rather than an artefact produced by a
writer.

Three consequences organise the entire literature below:

1. **Latency falls** by at least one round-trip, since the certification steps
   disappear from the critical path (Mysticeti, §3; Bluestreak, §4.4).
2. **Equivocation becomes the reader's problem.** Nothing structurally prevents a
   Byzantine validator from broadcasting two blocks for one slot, so the commit
   rule must be safe in the presence of equivocation rather than being protected
   from it.
3. **Liveness becomes delicate.** With no certificate to prove availability, a
   validator may reference a block it cannot supply, and correct validators may
   fail to converge on a common view. This is the sore point of the family, and
   the subject of §4.3.

The third consequence is the one this repository's development speaks to
directly; see §7.

---

## 2. Ancestors

### 2.1 Hashgraph

> L. Baird. *The Swirlds Hashgraph Consensus Algorithm: Fair, Fast, Byzantine
> Fault Tolerance.* Swirlds Tech Report SWIRLDS-TR-2016-01, 2016.
> L. Baird and A. Luykx. *The Hashgraph Protocol: Efficient Asynchronous BFT for
> High-Throughput Distributed Ledgers.* IEEE COINS, 2020.

The original uncertified construction. Validators gossip *about gossip*: each
event records the hashes of the two events it descends from, and the resulting
graph is interpreted locally by "virtual voting" — every validator computes what
every other validator *would have voted*, from graph structure alone, with no
vote messages exchanged.

**Re-uses:** the defining idea that consensus can be read off an unauthenticated
graph without any explicit voting or certification round. Mysticeti's own
framing acknowledges this lineage.

**Differs from Mysticeti:**
- *Randomised and fully asynchronous*, rather than partially synchronous with a
  deterministic commit rule. Hashgraph terminates with probability 1 using a coin
  round; Mysticeti's commit rule is deterministic and its liveness rests on
  partial synchrony.
- *Unstructured gossip graph* rather than a round-indexed DAG with a quorum
  reference rule. There are no rounds, so there is no notion of "a block at round
  r references 2f+1 blocks at round r-1" — which is precisely the invariant the
  present development builds on.
- *Latency is not the design objective*; virtual voting over famous witnesses
  costs many more effective rounds than Mysticeti's three.

### 2.2 Blockmania

> G. Danezis and D. Hrycyszyn. *Blockmania: from Block DAGs to Consensus.*
> arXiv:1809.01620, 2018.

Nodes emit blocks referencing prior blocks, forming a block DAG that each node
interprets separately to derive consensus. Blockmania shows that the message
pattern of PBFT can be *emulated* by interpreting a DAG, reducing communication
from O(N⁴) to O(N²) with small constants.

**Re-uses:** the "interpret the graph locally" discipline, and the insight that
the DAG can carry the consensus messages implicitly rather than as distinct
protocol messages.

**Differs from Mysticeti:**
- *Emulates a specific PBFT-style state machine* over the DAG, whereas Mysticeti
  defines a commit rule natively in terms of reference counting.
- *Leaderless* in its published form; Mysticeti assigns leader slots per round
  and commits leaders.
- Predates the round/wave discipline and the 3-round latency lower-bound framing.

### 2.3 Cordial Miners — the direct predecessor

> I. Keidar, O. Naor, O. Poupko, E. Shapiro. *Cordial Miners: Fast and Efficient
> Consensus for Every Eventuality.* DISC 2023, LIPIcs vol. 281.
> arXiv:2205.09174.

The most important ancestor. Cordial Miners forgoes reliable broadcast as a
building block and uses the **blocklace** — a partially-ordered counterpart of
the blockchain — to implement all three components of consensus: dissemination,
equivocation-exclusion, and ordering. It achieves optimal good-case message
complexity O(n) and roughly halves the latency of certified DAG protocols. It
comes in two instances, one for asynchrony and one for eventual synchrony.

**Re-uses:** essentially everything Mysticeti later builds on — no reliable
broadcast, no certificates, equivocation handled by graph inspection rather than
prevented by construction.

**Differs from Mysticeti:**
- *Disjoint 3-round waves with one leader in the first round of each wave.*
  Mysticeti's contribution over this is precisely to remove the wave structure:
  it assigns leader slots in *every* round and pipelines the commit rule, so that
  every block can be committed without waiting for a wave boundary. This is the
  source of Mysticeti's 3-message-round optimum.
- *Explicit equivocation-exclusion machinery* over the blocklace; Mysticeti
  instead makes the commit rule itself safe under equivocation.
- Cordial Miners' asynchronous instance uses randomisation; Mysticeti-C is
  deterministic under partial synchrony.

---

## 3. The reference point

### 3.1 Mysticeti

> K. Babel, A. Chursin, G. Danezis, A. Kichidis, L. Kokoris-Kogias, A. Koshy,
> A. Sonnino, M. Tian. *Mysticeti: Reaching the Limits of Latency with
> Uncertified DAGs.* NDSS 2025. arXiv:2310.14821.

Mysticeti-C is the first DAG-based Byzantine consensus protocol to reach the
latency lower bound of three message rounds. It achieves this by (i) forgoing
explicit certification, so a block costs one broadcast, and (ii) a commit rule
under which every block carries a leader slot and can be committed without
delay — no wave boundaries. Mysticeti-FPC weaves a fast path for owned-object
transactions into the same DAG rather than running it as a separate protocol.
Reported: 0.5s WAN commit latency at >200k TPS; deployed on Sui with a >4×
latency reduction.

This is the design the present formalisation targets. The commit rule — direct
commit, direct skip, and the indirect rule that resolves undecided slots from
later certificates — is the object of `LeanDag/Mysticeti.lean`.

---

## 4. Protocols that re-use the uncertified DAG

### 4.1 Mahi-Mahi

> P. Jovanovic, L. Kokoris-Kogias, B. Kumara, A. Sonnino, P. Tennage,
> I. Zablotchi. *Mahi-Mahi: Low-Latency Asynchronous BFT DAG-Based Consensus.*
> arXiv:2410.08670, 2024. (IEEE, 2025.)

The asynchronous sibling, from substantially the same group. It keeps the
uncertified structured DAG — explicitly to forgo certification, cutting both
message count and the CPU cost of certificate verification — and pairs it with a
commit rule that commits **multiple leader blocks in each DAG round**.

**Differs from Mysticeti:**
- *Asynchronous rather than partially synchronous.* Mahi-Mahi is designed to make
  progress against a continuously active asynchronous adversary; Mysticeti-C's
  liveness argument requires partial synchrony. This is the single largest
  difference and the reason the commit rule must change.
- *Multiple leader slots committed per round*, parameterised as either a 5-hop
  commit delay (maximising commit probability under a continuously active
  asynchronous adversary) or a 4-hop delay (lower latency under a moderate
  adversary). Mysticeti commits on a fixed 3-round pattern.
- The leader-election mechanism (whether a common coin or threshold randomness is
  used, as asynchrony would ordinarily require) could not be confirmed from the
  sources consulted (unconfirmed).

**Bearing on this development:** the parameterised commit depth suggests the
commit rule here could be generalised over a "certificate distance" parameter
rather than fixed at two rounds above the leader.

### 4.2 Odontoceti

> P. Vander Vos (supervised by P. Jovanovic and A. Sonnino). *Odontoceti:
> Ultra-Fast DAG Consensus with Two Round Commitment.* MSc thesis,
> arXiv:2510.01216, 2025.

Builds an uncertified DAG with a novel decision rule, and is the first DAG
protocol to commit in **two** communication rounds rather than three.

**Differs from Mysticeti:**
- *Weakens the fault threshold to buy a round.* Odontoceti runs with n = 5f+1
  (≈20% fault tolerance) instead of n = 3f+1 (≈33%). The extra validators make a
  quorum intersection large enough that the vote and certificate rounds can be
  collapsed into one. This is a deliberate trade of security margin for latency,
  not a strictly better commit rule.
- *Includes a slow-participant optimisation* that advances progress under crash
  faults, argued to be the common case in practice.
- Reported 300ms median latency at 10k TPS.

**Bearing on this development:** the quorum-intersection arithmetic in
`LeanDag` is stated against 3f+1. Odontoceti is a clean example of the commit
rule's round depth being a *consequence* of the quorum arithmetic, which suggests
the safety proofs could be parameterised over the threshold.

### 4.3 Starfish — and the liveness critique of uncertified DAGs

> N. Polyanskii, S. Mueller, I. Vorobyev. *Making Uncertified DAG BFT Provably
> Live with Linear Payload and Quadratic Metadata Communication.*
> IACR ePrint 2025/567, 2025 (rev. 2026). Also circulated as *Starfish: A high
> throughput BFT protocol on uncertified DAG with linear amortized communication
> complexity.*

The most consequential paper for this repository. Starfish is a partially
synchronous uncertified DAG protocol that aims for "the security properties of
certified DAGs, the efficiency of uncertified approaches, and linear amortized
communication complexity."

Its two claims against the existing family are direct:

1. **Uncertified DAG protocols, Mysticeti included, lacked a rigorous liveness
   proof.** Starfish claims to give the first.
2. **They admit a desynchronisation attack** in which correct parties fail to
   commit leaders even after GST.

Its remedies:
- A **Push pacemaker**: parties must create a block before advancing rounds, plus
  a catch-up condition for slower participants. This is what restores post-GST
  synchronisation.
- **Encoded Cordial Dissemination**: Reed–Solomon erasure coding plus Data
  Availability Certificates, decoupling transaction data from block headers so
  headers can be push-disseminated. This attacks the O(Mn²) payload cost that
  follows from coupling data to metadata in uncertified designs.
- **Starfish-L** and, applying the same techniques to Mysticeti, **Mysticeti-L**,
  which retains Mysticeti's latency at quadratic metadata and linear payload cost
  in the happy case.

**Differs from Mysticeti:** adds a pacemaker discipline and an encoded
dissemination layer; retains the uncertified commit structure.

**Bearing on this development — the important one.** The report's §4.4 derives
`SynchronisedOn` (beyond some round, every correct block references every correct
block of the round below) from GST *together with the protocol's own build
rules*. Starfish's desynchronisation attack is exactly an attack on that
property, and its Push pacemaker is exactly a build rule that restores it. The
two accounts should be reconciled explicitly: either the build rules assumed in
§4.4 already imply Starfish's pacemaker condition — in which case the derivation
answers their critique and should say so — or they do not, in which case §4.4's
assumption is stronger than advertised and the gap must be stated. **This is the
single highest-value citation to engage with in the report**, since it is the
literature's standing claim that the property this development derives cannot be
had for free.

### 4.4 Bluestreak

> N. Polyanskii, I. Vorobyev, S. Mueller. *Bluestreak: Scaling DAG BFT by
> Sparsifying Metadata.* IACR ePrint 2026/898, May 2026.

A **sparse** uncertified DAG. The observation: dense round-based DAGs require
every block to reference ≥2f+1 blocks of the previous round, giving O(n) metadata
per block, O(n²) per round, and O(n³) metadata bytes transmitted per round under
all-to-all dissemination — so at large committee sizes *metadata*, not payload,
becomes the latency bottleneck.

**Differs from Mysticeti:**
- *Non-leader blocks are kept constant-size in n.* Committee-scale ancestry is
  concentrated into a single leader block per round, so average metadata per
  block stays constant as committees grow.
- This directly changes the reference structure that Mysticeti's commit rule
  counts over. The rule "a block references a quorum of the round below" — P1 and
  the quorum reference invariant in this development — no longer holds uniformly
  across all blocks.

**Bearing on this development:** the model here assumes every block references a
quorum below (report §2, P1). Bluestreak is the case where that assumption is
deliberately dropped for non-leader blocks, and is therefore the natural boundary
marker for the model's scope.

### 4.5 Lifefin

> J. Zhang et al. *Lifefin: Escaping Mempool Explosions in DAG-based BFT.*
> arXiv:2511.15936, 2025.

Not a new DAG protocol but a *generic overlay*, and it targets Mysticeti by name.
It identifies a liveness vulnerability in which an adversary triggers a **mempool
explosion**: during asynchrony, nodes maintain an ever-growing set of uncommitted
vertices, exhaust their resources, and can then no longer generate vertices
supporting the latest leader — so the protocol stalls. Lifefin uses Agreement on
Common Subset to commit transactions under bounded resource usage, and is
instantiated as **Sailfish-Lifefin** and **Mysticeti-Lifefin**.

**Differs from Mysticeti:** an add-on layer rather than a redesign; applies to
certified and uncertified DAGs alike.

**Bearing on this development:** the attack is resource-exhaustion driven and
therefore lies outside the model here, which has no notion of node resources and
no executions (report §1.4). Worth citing as an explicitly out-of-scope liveness
threat, so that the liveness claims are not read as stronger than they are.

---

## 5. Certified DAGs — what the family is defined against

Included only to fix the contrast; none of these re-use the uncertified
structure.

- **Narwhal & Tusk / Bullshark.** > G. Danezis, L. Kokoris-Kogias,
  A. Sonnino, A. Spiegelman. *Narwhal and Tusk.* EuroSys 2022. /
  A. Spiegelman, N. Giridharan, A. Sonnino, L. Kokoris-Kogias. *Bullshark: DAG
  BFT Protocols Made Practical.* CCS 2022, arXiv:2201.05677.
  The certified baseline: reliable broadcast per block, certificates in the DAG,
  leaders every other round. Mysticeti's latency claim is stated against these.

- **Sailfish.** > N. Shrestha, R. Shrothrium, A. Kate, K. Nayak. *Sailfish: Towards
  Improving the Latency of DAG-based BFT.* IEEE S&P 2025, ePrint 2024/472.
  Keeps certification (RBC) but supports **a leader vertex in every round**,
  committing a leader in one RBC round plus 1δ — roughly 25% below Bullshark.
  Instructive because Sailfish and Mysticeti reach for the same goal (a leader
  every round) from opposite sides: Sailfish keeps certificates and restructures
  leaders; Mysticeti drops certificates.

- **Shoal++.** > B. Arun, Z. Li, F. Suri-Payer, S. Das, A. Spiegelman
  (Aptos Labs / Cornell / UIUC). *Shoal++: High Throughput DAG BFT Can Be Fast
  and Robust!* NSDI 2025, arXiv:2405.20488.
  The explicit counter-argument to the uncertified thesis: it contends that
  *certification is not the root cause of high latency*, reaching 4.5 message
  delays on a certified DAG. It argues uncertified designs are less robust —
  under message drops Shoal++ latency rises at most 1.3×, whereas uncertified
  DAGs "experience sharp latency spikes as replicas perform critical-path
  synchronization on missing data," which is the availability problem of §1.
  Notably **hybrid**: it also commits anchors on observing 2f+1 *uncertified*
  proposals, so it re-uses the uncertified commit pattern as a fast path over a
  certified DAG.

---

## 6. Mechanised verification of DAG consensus

Directly relevant, since this repository is a Lean 4 development.

- **LiDO-DAG.** > *LiDO-DAG: A Framework for Verifying Safety and Liveness of
  DAG-Based Consensus Protocols.* Proc. ACM Program. Lang., 2025.
  doi:10.1145/3729306 (Yale FLINT).
  Coq. Applied to Narwhal, Bullshark and Sailfish, giving mechanised safety *and
  liveness* proofs — claimed as the first mechanised liveness proofs of any
  DAG-based protocol. **All three targets are certified DAGs**, which is the gap
  the present development occupies: uncertified, and with liveness stated
  structurally rather than over a time model.

- **Reusable Formal Verification of DAG-based Consensus Protocols.**
  > N. Bertrand, P. Ghorpade, S. Rubin, B. Scholz, P. Subotic. arXiv:2407.02167,
  2024; Springer, doi:10.1007/978-3-031-93706-4_9.
  TLA+ with TLAPS, over DAG-Rider, **Cordial Miners**, **Hashgraph**, eventually
  synchronous Bullshark, and an Aleph variant, with modular specifications
  separating DAG construction from ordering to enable proof reuse (≈half the
  effort). **Safety only — liveness is not covered.** The two uncertified targets
  make this the closest prior art; the modular construction/ordering split is
  also the same decomposition used here.

- **Formal Verification of Blockchain Nonforking in DAG-Based BFT Consensus with
  Dynamic Stake.** > arXiv:2504.16853, 2025.
  Nonforking under dynamic stake — orthogonal to the static-committee model here,
  but relevant if committee reconfiguration is ever added. (Proof assistant and
  authorship not confirmed in this pass.)

---

## 7. Summary: where this development sits

| Protocol | Uncertified | Synchrony | Leader cadence | Commit depth | Fault bound |
|---|---|---|---|---|---|
| Hashgraph | yes | asynchronous | none (virtual voting) | — | 3f+1 |
| Blockmania | yes | partial | leaderless | PBFT-emulating | 3f+1 |
| Cordial Miners | yes | both instances | 1 per 3-round wave | 3 rounds | 3f+1 |
| **Mysticeti** | **yes** | **partial** | **every round** | **3 rounds** | **3f+1** |
| Mahi-Mahi | yes | asynchronous | multiple per round | 4 or 5 hops | 3f+1 |
| Odontoceti | yes | partial | every round | **2 rounds** | **5f+1** |
| Starfish | yes | partial | every round | 3 rounds | 3f+1 |
| Bluestreak | yes (sparse) | partial | every round | 3 rounds | 3f+1 |
| Sailfish | no | partial | every round | 1 RBC + 1δ | 3f+1 |
| Shoal++ | no (hybrid) | partial | every round | 4.5 delays | 3f+1 |

Three observations for the report.

1. **The uncertified family is converging on Mysticeti's shape** — leader every
   round, commit by reference counting — and varying one parameter at a time:
   the synchrony assumption (Mahi-Mahi), the fault threshold (Odontoceti), the
   reference density (Bluestreak), the dissemination layer (Starfish). This
   supports the claim that the commit rule formalised here is the family's
   common core, and suggests parameterising the Lean development over quorum
   threshold and certificate distance rather than fixing them.

2. **Liveness is the family's acknowledged weak point**, and it is contested
   ground: Starfish claims uncertified DAGs including Mysticeti lacked a rigorous
   liveness proof and admit post-GST desynchronisation; Shoal++ argues from the
   certified side that uncertified DAGs are less robust because availability is
   not guaranteed. The report's structural condition and its GST derivation land
   squarely in this dispute and should engage with both by name.

3. **No mechanised treatment of an uncertified DAG's liveness exists.** LiDO-DAG
   mechanises liveness but only for certified protocols; the TLA+ work covers two
   uncertified protocols but safety only. A machine-checked liveness development
   for a Mysticeti-style uncertified commit rule is, on this survey, unoccupied
   ground — and the strongest available statement of this repository's
   contribution.

---

## Sources

- [Mysticeti — arXiv:2310.14821](https://arxiv.org/abs/2310.14821) · [NDSS 2025](https://www.ndss-symposium.org/ndss-paper/mysticeti-reaching-the-latency-limits-with-uncertified-dags/)
- [Cordial Miners — arXiv:2205.09174](https://arxiv.org/abs/2205.09174) · [DISC 2023](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.DISC.2023.26)
- [Blockmania — arXiv:1809.01620](https://arxiv.org/abs/1809.01620)
- [Hashgraph — COINS 2020](https://hedera.com/wp-content/uploads/2025/11/hh-ieee_coins_paper-200516.pdf)
- [Mahi-Mahi — arXiv:2410.08670](https://arxiv.org/abs/2410.08670)
- [Odontoceti — arXiv:2510.01216](https://arxiv.org/abs/2510.01216)
- [Starfish — ePrint 2025/567](https://eprint.iacr.org/2025/567) · [preprint](https://nikitapolyanskii.com/writings/2025-44-starfish/preprint.pdf)
- [Bluestreak — ePrint 2026/898](https://eprint.iacr.org/2026/898)
- [Lifefin — arXiv:2511.15936](https://arxiv.org/abs/2511.15936)
- [Sailfish — ePrint 2024/472](https://eprint.iacr.org/2024/472)
- [Shoal++ — arXiv:2405.20488](https://arxiv.org/abs/2405.20488) · [NSDI 2025](https://www.usenix.org/conference/nsdi25/presentation/arun)
- [LiDO-DAG — doi:10.1145/3729306](https://dl.acm.org/doi/10.1145/3729306) · [PDF](https://flint.cs.yale.edu/flint/publications/lido-dag.pdf)
- [Reusable Formal Verification of DAG-based Consensus — arXiv:2407.02167](https://arxiv.org/abs/2407.02167)
- [Nonforking with Dynamic Stake — arXiv:2504.16853](https://arxiv.org/abs/2504.16853)
