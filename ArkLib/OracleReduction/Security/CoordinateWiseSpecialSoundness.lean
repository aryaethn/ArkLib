/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.TranscriptTree
import ArkLib.OracleReduction.Security.RoundByRound
import VCVio.CryptoFoundations.ReplayFork

/-!
  # Coordinate-Wise Special Soundness (CWSS)

  This file defines **coordinate-wise special soundness** for (oracle) reductions, following
  Fenzi–Moghaddas–Nguyen (*Lattice-Based Polynomial Commitments*, J. Cryptology 2024, who introduce
  the notion) and Nguyen–O'Rourke–Zhang (*Hachi*, 2026, Definition 3, which is the multi-round form
  we target for verification).

  ## The idea

  Coordinate-wise special soundness generalizes `k`-special soundness. In `k`-special soundness one
  extracts a witness from a tree of accepting transcripts in which, at each challenge round, there
  are `k` children with pairwise distinct challenges. In coordinate-wise special soundness the
  challenge of round `i` is a *vector* `Sᵢ^{ℓᵢ}`, and the children challenges form a structured set
  `SS(Sᵢ, ℓᵢ, kᵢ)`: there is a "central" challenge vector together with, for every coordinate,
  `kᵢ-1` sibling vectors that differ from the central one *only in that coordinate*. The arity at
  round `i` is therefore `ℓᵢ·(kᵢ-1)+1`.

  Plain `kᵢ`-special soundness is recovered as the special case `ℓᵢ = 1` (see
  `CWSSStructure.ofSpecialSound`), so this development is shared with special soundness via the
  common `ProtocolSpec.ChallengeTree` (defined in `TranscriptTree.lean`).

  ## What is defined here

  1. The combinatorics of `SS(S, ℓ, k)`: `CoordEq` (the relation `≡ᵢ`) and `IsSpecialSoundFamily`.
  2. A `CWSSStructure`, packaging the per-round coordinate decomposition `Challenge i ≃ Sᵢ^{ℓᵢ}` and
     soundness parameters `kᵢ`.
  3. `ChallengeTree.IsStructured`: the predicate that a tree's sibling challenges form `SS`-sets.
  4. `Verifier.coordinateWiseSpecialSound`: existence of a (deterministic) extractor that turns any
     structured, accepting tree of transcripts into a valid input witness — exactly Hachi Def. 3.
  5. The connection to knowledge soundness via **rewinding**: CWSS implies knowledge soundness with
     error `∑ᵢ ℓᵢ·kᵢ / |Sᵢ|^{ℓᵢ}` (Hachi Lemma 4 / FMN §7–8). The knowledge extractor is *not*
     straightline: it grows the tree of transcripts by repeatedly **forking** the prover at each
     challenge round, using `VCVio.CryptoFoundations.forkReplay`, and then applies the combinatorial
     extractor above. This is the role rewinding plays in CWSS.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace CoordinateWise

/-! ## The combinatorial structure `SS(S, ℓ, k)`

These definitions are pure combinatorics on vectors in `S^ℓ ≃ (Fin ℓ → S)`, independent of any
protocol. They capture exactly the set `SS(S, ℓ, k)` from FMN / Hachi.
-/

variable {S : Type*}

/-- The relation `x ≡ᵢ y`: the coordinate-vectors `x` and `y` agree in every coordinate except the
  `i`-th, where they differ. For `ℓ = 1` this is just `x 0 ≠ y 0`. -/
def CoordEq {ℓ : ℕ} (i : Fin ℓ) (x y : Fin ℓ → S) : Prop :=
  x i ≠ y i ∧ ∀ j, j ≠ i → x j = y j

/-- A family of `ℓ·(k-1)+1` coordinate-vectors `c` is **coordinate-wise special sound**, i.e. lies
  in `SS(S, ℓ, k)`, if there is a *central* index `e` such that for every coordinate `i ∈ Fin ℓ`
  there are `k-1` other indices whose vectors agree with `c e` off coordinate `i` (and differ on
  it).

  This is the precise rendering of the set `SS(S, ℓ, k)` from FMN Def. 2.9 / Hachi §2.3. The
  branching arity `ℓ·(k-1)+1` is built into the index type. -/
def IsSpecialSoundFamily (ℓ k : ℕ) (c : Fin (ℓ * (k - 1) + 1) → (Fin ℓ → S)) : Prop :=
  ∃ e : Fin (ℓ * (k - 1) + 1),
    ∀ i : Fin ℓ, ∃ J : Finset (Fin (ℓ * (k - 1) + 1)),
      e ∉ J ∧ J.card = k - 1 ∧ ∀ j ∈ J, CoordEq i (c e) (c j)

/-- For `ℓ = 1`, coordinate-wise special soundness is ordinary `k`-special soundness: there is a
  central vector together with `k - 1` siblings, all differing in the single coordinate, i.e. `k`
  pairwise-distinct challenge values. -/
theorem isSpecialSoundFamily_one {k : ℕ} (c : Fin (1 * (k - 1) + 1) → (Fin 1 → S)) :
    IsSpecialSoundFamily 1 k c ↔
      ∃ e, ∃ J : Finset (Fin (1 * (k - 1) + 1)),
        e ∉ J ∧ J.card = k - 1 ∧ ∀ j ∈ J, c e 0 ≠ c j 0 := by
  unfold IsSpecialSoundFamily CoordEq
  constructor
  · rintro ⟨e, h⟩
    obtain ⟨J, hJ⟩ := h 0
    exact ⟨e, J, hJ.1, hJ.2.1, fun j hj => (hJ.2.2 j hj).1⟩
  · rintro ⟨e, J, heJ, hcard, hdiff⟩
    refine ⟨e, fun i => ?_⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    refine ⟨J, heJ, hcard, fun j hj => ⟨hdiff j hj, fun j' hj' => ?_⟩⟩
    exact absurd (Subsingleton.elim _ _) hj'

end CoordinateWise

/-! ## Coordinate-wise structure on a protocol -/

variable {n : ℕ}

/-- A **coordinate-wise special-soundness structure** for a protocol `pSpec`. For each challenge
  round `i` it provides:
  - the number `coordIndex i = ℓᵢ` of coordinates,
  - the per-coordinate alphabet `alphabet i = Sᵢ`,
  - an identification `decompose i : Challenge i ≃ Sᵢ^{ℓᵢ}` of the challenge as a coordinate-vector,
  - the soundness parameter `soundnessParam i = kᵢ`.

  The branching arity it induces at round `i` is `arity i = ℓᵢ·(kᵢ-1)+1`. -/
structure CWSSStructure (pSpec : ProtocolSpec n) where
  /-- Number of coordinates `ℓᵢ` of the `i`-th challenge. -/
  coordIndex : pSpec.ChallengeIdx → ℕ
  /-- Per-coordinate alphabet `Sᵢ` of the `i`-th challenge. -/
  alphabet : pSpec.ChallengeIdx → Type
  /-- Identification of the `i`-th challenge as a coordinate-vector `Sᵢ^{ℓᵢ}`. -/
  decompose : (i : pSpec.ChallengeIdx) → pSpec.Challenge i ≃ (Fin (coordIndex i) → alphabet i)
  /-- The soundness parameter `kᵢ` for the `i`-th challenge. -/
  soundnessParam : pSpec.ChallengeIdx → ℕ

namespace CWSSStructure

variable {pSpec : ProtocolSpec n} (D : CWSSStructure pSpec)

/-- The branching arity `arity i = ℓᵢ·(kᵢ-1)+1` of the transcript tree at challenge round `i`. -/
@[reducible]
def arity : pSpec.ChallengeIdx → ℕ :=
  fun i => D.coordIndex i * (D.soundnessParam i - 1) + 1

/-- The canonical coordinate-wise structure underlying plain `k`-special soundness: every challenge
  has a single coordinate (`ℓᵢ = 1`) over the alphabet `Challenge i`, with soundness parameters `k`.
  Used to obtain `k`-special soundness as a special case of CWSS, reusing all of the machinery
  below. -/
def ofSpecialSound (k : pSpec.ChallengeIdx → ℕ) : CWSSStructure pSpec where
  coordIndex := fun _ => 1
  alphabet := fun i => pSpec.Challenge i
  decompose := fun i => (Equiv.funUnique (Fin 1) (pSpec.Challenge i)).symm
  soundnessParam := k

end CWSSStructure

namespace ProtocolSpec.ChallengeTree

open CoordinateWise

variable {pSpec : ProtocolSpec n}

/-- A tree of transcripts with arity `D.arity` is **`D`-structured** if, at every challenge node,
  the sibling challenges — read as coordinate-vectors via `D.decompose` — form a coordinate-wise
  special-sound family `SS(Sᵢ, ℓᵢ, kᵢ)`.

  This is the structural condition that makes a tree usable by a coordinate-wise special-soundness
  extractor. With `D = CWSSStructure.ofSpecialSound k` it specializes to "the `k` sibling challenges
  at each node are pairwise distinct", i.e. the condition for plain `k`-special soundness. -/
def IsStructured (D : CWSSStructure pSpec) :
    {m : Fin (n + 1)} → ChallengeTree pSpec D.arity m → Prop
  | _, .leaf => True
  | _, .msgNode _ _ _ child => child.IsStructured D
  | _, .chalNode m h challenges children =>
      IsSpecialSoundFamily (D.coordIndex ⟨m, h⟩) (D.soundnessParam ⟨m, h⟩)
        (fun j => D.decompose ⟨m, h⟩ (challenges j))
      ∧ ∀ j, (children j).IsStructured D

end ProtocolSpec.ChallengeTree

/-! ## The coordinate-wise special-soundness extractor and predicate -/

namespace Extractor

open ProtocolSpec

/-- A **tree-based extractor**: a deterministic algorithm that, given the input statement and a tree
  of transcripts (rooted at round `0`), outputs an input witness.

  This is the type of extractor used by (coordinate-wise) special soundness. The tree already
  contains all transcripts, so the extractor is a plain function; it is the rewinding/forking
  extractor of the knowledge-soundness reduction that actually *produces* the tree. -/
def TreeBased (StmtIn WitIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (arity : pSpec.ChallengeIdx → ℕ) : Type :=
  StmtIn → ProtocolSpec.ChallengeTree pSpec arity 0 → WitIn

end Extractor

namespace Verifier

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- A verifier is **coordinate-wise special sound** with respect to a coordinate-wise structure `D`,
  an input relation `relIn` and an output language `langOut` if there is a tree-based extractor `E`
  such that: for every input statement `stmtIn` and every tree of transcripts that is

  - `D`-structured (its sibling challenges form `SS(Sᵢ, ℓᵢ, kᵢ)`-sets), and
  - accepting (the verifier accepts every root-to-leaf transcript, landing in `langOut`),

  the extracted witness `E stmtIn tree` satisfies `(stmtIn, E stmtIn tree) ∈ relIn`.

  This is the multi-round coordinate-wise special soundness of Hachi Def. 3 / FMN Def. 2.10,
  phrased over ArkLib's IOR machinery. Specializing `D` to `CWSSStructure.ofSpecialSound k` yields
  the standard notion of `k`-special soundness. -/
def coordinateWiseSpecialSound (D : CWSSStructure pSpec)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) : Prop :=
  ∃ E : Extractor.TreeBased StmtIn WitIn pSpec D.arity,
  ∀ stmtIn : StmtIn,
  ∀ tree : ChallengeTree pSpec D.arity 0,
    tree.IsStructured D →
    tree.IsAccepting init impl verifier stmtIn langOut →
      (stmtIn, E stmtIn tree) ∈ relIn

/-- `k`-special soundness as the `ℓᵢ = 1` case of coordinate-wise special soundness. -/
def specialSound (k : pSpec.ChallengeIdx → ℕ)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) : Prop :=
  verifier.coordinateWiseSpecialSound init impl (CWSSStructure.ofSpecialSound k) relIn langOut

end Verifier

namespace OracleVerifier

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut : Type}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, OracleInterface (pSpec.Message i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Coordinate-wise special soundness of an oracle reduction, defined (as for round-by-round
  notions) via the underlying non-oracle verifier on the combined (oracle + non-oracle) statements.
  The challenge structure `D` is unchanged, since the verifier's challenges are the same. -/
def coordinateWiseSpecialSound (D : CWSSStructure pSpec)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (langOut : Set (StmtOut × ∀ i, OStmtOut i))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) : Prop :=
  verifier.toVerifier.coordinateWiseSpecialSound init impl D relIn langOut

end OracleVerifier

/-! ## From CWSS to knowledge soundness, via rewinding

The combinatorial extractor above turns any *given* structured, accepting tree into a witness. To
turn this into knowledge soundness one must *produce* such a tree from a single (malicious) prover.
This is done by **rewinding**: run the prover once, then at each challenge round repeatedly fork it
— replaying the transcript up to that round and resampling that single challenge — to obtain the
`ℓᵢ·(kᵢ-1)+1` coordinate-wise-related siblings. The forking primitive is
`VCVio.CryptoFoundations.forkReplay`, which records a first run's query log and replays it up to a
distinguished challenge query while changing exactly that answer.

We record the resulting knowledge error and state the implication. The proof (future work) iterates
`forkReplay` over the challenge rounds to build a `ChallengeTree`, following FMN §7–8 / Hachi
Lemma 4 and the Fiat–Shamir analysis of Attema–Fehr–Klooß.
-/

namespace CWSSStructure

variable {pSpec : ProtocolSpec n}

/-- The CWSS knowledge error `∑ᵢ ℓᵢ·kᵢ / |Sᵢ|^{ℓᵢ}` of Hachi Lemma 4, summed over challenge rounds.
  Here `(2βC+1)^N`-style denominators of the paper are `|Sᵢ|^{ℓᵢ}`, the size of the challenge space
  of round `i`. -/
def knowledgeError (D : CWSSStructure pSpec) [∀ i, Fintype (D.alphabet i)] : ℝ≥0 :=
  ∑ i : pSpec.ChallengeIdx,
    (D.coordIndex i * D.soundnessParam i : ℝ≥0) /
      ((Fintype.card (D.alphabet i) : ℝ≥0) ^ D.coordIndex i)

end CWSSStructure

namespace Verifier

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **Coordinate-wise special soundness implies knowledge soundness**, with the CWSS knowledge error
  of Hachi Lemma 4.

  The acceptance language for the tree is taken to be `relOut.language`, the set of output
  statements admitting some valid output witness. The knowledge extractor witnessing
  `knowledgeSoundness` is the rewinding extractor that builds a structured, accepting tree of
  transcripts by iterating
  `VCVio.CryptoFoundations.forkReplay` at each challenge round, then applies the combinatorial
  extractor supplied by `coordinateWiseSpecialSound`. -/
theorem coordinateWiseSpecialSound_implies_knowledgeSoundness
    (D : CWSSStructure pSpec) [∀ i, Fintype (D.alphabet i)]
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) :
      verifier.coordinateWiseSpecialSound init impl D relIn relOut.language →
        verifier.knowledgeSoundness init impl relIn relOut D.knowledgeError := by
  -- Proof outline (future work): the straightline knowledge extractor is replaced by a rewinding
  -- one. Given black-box access to the prover, run it once to get an accepting leaf; then, at each
  -- challenge round, repeatedly invoke `VCVio.CryptoFoundations.forkReplay` on the challenge
  -- oracle to obtain the `ℓ·(k-1)+1` coordinate-wise-related siblings, assembling a `ChallengeTree`
  -- that is `IsStructured` and `IsAccepting`. Feeding this tree to the combinatorial extractor from
  -- the `coordinateWiseSpecialSound` hypothesis yields a witness in `relIn`; the forking-bound
  -- analysis (FMN §7–8 / Hachi Lemma 4) gives the error `D.knowledgeError`.
  sorry

end Verifier
