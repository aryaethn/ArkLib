/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Fri.Interaction.FoldRound
import ArkLib.Interaction.Oracle.Chain

/-!
# Interaction-Native FRI: Native Fold Phase

This module composes the `k` non-final FRI fold rounds over the native
`Interaction.Oracle.Spec.Chain` layer.
-/

open Interaction CompPoly CPoly OracleComp OracleSpec

namespace Fri

namespace NativeOracle

section

variable {F : Type} [BEq F] [LawfulBEq F] [DecidableEq F] [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ}
variable [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (x : Fˣ)
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ)

private theorem initialRoundEq :
    0 + k = k := by
  omega

private theorem stateRound_lt {m round : ℕ}
    (h : round + (m + 1) = k) :
    round < k := by
  omega

private theorem nextStateEq {m round : ℕ}
    (h : round + (m + 1) = k) :
    round.succ + m = k := by
  omega

private theorem finalRoundEq {round : ℕ}
    (h : round + 0 = k) :
    round = k := by
  simpa using h

/-- Total challenge vector used internally while the fold phase is running.
Entries beyond the current round are irrelevant until they are filled in. -/
def initialFoldChallenges :
    FoldChallenges (F := F) (k := k) :=
  fun _ => 0

/-- Record the verifier challenge produced at a given non-final fold round. -/
def recordChallenge
    (round : Fin k)
    (challenges : FoldChallenges (F := F) (k := k))
    (α : F) :
    FoldChallenges (F := F) (k := k) :=
  Function.update challenges round α

/-- The native chain of the remaining non-final fold rounds, starting at
round `start`. -/
def foldPhaseChainFrom :
    (remaining start : Nat) → (h : start + remaining = k) →
    Interaction.Oracle.Spec.Chain remaining
  | 0, _, _ => ⟨⟩
  | remaining + 1, start, h =>
      let round : Fin k := ⟨start, stateRound_lt (k := k) h⟩
      ⟨foldRoundSpec (F := F) (n := n) D x s round,
       foldRoundRoles (F := F) (n := n) D x s round,
       foldRoundOD (F := F) (n := n) D x s round,
       fun _ => foldPhaseChainFrom remaining start.succ (nextStateEq (k := k) h)⟩

/-- The native chain of all non-final fold rounds. -/
def foldPhaseChain : Interaction.Oracle.Spec.Chain k :=
  foldPhaseChainFrom (D := D) (n := n) (x := x) (s := s) (k := k)
    k 0 (initialRoundEq (k := k))

/-- Native oracle context for the full non-final folding phase. -/
abbrev foldPhaseContext : Interaction.Oracle.Spec :=
  Interaction.Oracle.Spec.Chain.toSpec k
    (foldPhaseChain (D := D) (n := n) (x := x) (s := s))

/-- Native role decoration for the full non-final folding phase. -/
abbrev foldPhaseRoles :
    Interaction.Oracle.Spec.RoleDeco
      (foldPhaseContext (D := D) (n := n) (x := x) (s := s) (k := k)) :=
  Interaction.Oracle.Spec.Chain.toRoles k
    (foldPhaseChain (D := D) (n := n) (x := x) (s := s))

/-- Native oracle decoration for the full non-final folding phase. -/
abbrev foldPhaseOD :
    Interaction.Oracle.Spec.OracleDeco
      (foldPhaseContext (D := D) (n := n) (x := x) (s := s) (k := k)) :=
  Interaction.Oracle.Spec.Chain.toOracleDeco k
    (foldPhaseChain (D := D) (n := n) (x := x) (s := s))

/-- The indexed native chain of the remaining non-final fold rounds, starting
at absolute fold round `round`.

Unlike `foldPhaseChainFrom`, the current round is part of the chain index. This
is the cast-free shape for heterogeneous protocols such as FRI: party state can
be indexed directly by the same round index as the current chain node. -/
def foldPhaseIndexedChainFrom :
    (remaining round : Nat) → (h : round + remaining = k) →
      Interaction.Oracle.Spec.IndexedChain Nat remaining round
  | 0, _, _ => ⟨⟩
  | remaining + 1, round, h =>
      let i : Fin k := ⟨round, stateRound_lt (k := k) h⟩
      ⟨foldRoundSpec (F := F) (n := n) D x s i,
       foldRoundRoles (F := F) (n := n) D x s i,
       foldRoundOD (F := F) (n := n) D x s i,
       fun _ =>
        ⟨round.succ,
          foldPhaseIndexedChainFrom remaining round.succ (nextStateEq (k := k) h)⟩⟩

/-- Indexed native chain for all non-final fold rounds. -/
def foldPhaseIndexedChain :
    Interaction.Oracle.Spec.IndexedChain Nat k 0 :=
  foldPhaseIndexedChainFrom (D := D) (n := n) (x := x) (s := s) (k := k)
    k 0 (initialRoundEq (k := k))

/-- Native oracle context for the full indexed non-final folding phase. -/
abbrev foldPhaseIndexedContext : Interaction.Oracle.Spec :=
  Interaction.Oracle.Spec.IndexedChain.toSpec k
    (foldPhaseIndexedChain (D := D) (n := n) (x := x) (s := s))

/-- Native role decoration for the full indexed non-final folding phase. -/
abbrev foldPhaseIndexedRoles :
    Interaction.Oracle.Spec.RoleDeco
      (foldPhaseIndexedContext (D := D) (n := n) (x := x) (s := s) (k := k)) :=
  Interaction.Oracle.Spec.IndexedChain.toRoles k
    (foldPhaseIndexedChain (D := D) (n := n) (x := x) (s := s))

/-- Native oracle decoration for the full indexed non-final folding phase. -/
abbrev foldPhaseIndexedOD :
    Interaction.Oracle.Spec.OracleDeco
      (foldPhaseIndexedContext (D := D) (n := n) (x := x) (s := s) (k := k)) :=
  Interaction.Oracle.Spec.IndexedChain.toOracleDeco k
    (foldPhaseIndexedChain (D := D) (n := n) (x := x) (s := s))

/-- Honest prover state indexed directly by the absolute fold round. -/
private structure IndexedProverState (round : Nat) where
  challenges : FoldChallenges (F := F) (k := k)
  codewords :
    OracleStatement (FoldCodewordPrefix (F := F) (n := n) D x s round)
  poly : HonestPoly (F := F) s d round

/-- Initial honest prover state for the indexed fold phase. -/
private def indexedProverInit
    {SharedIn : Type}
    (shared : SharedIn)
    (sWithOracles :
      StatementWithOracles (fun _ : SharedIn => PUnit)
        (fun _ => InputOracleFamily (F := F) (n := n) D x s) shared)
    (witness : HonestPoly (F := F) s d 0) :
    IndexedProverState (D := D) (n := n) (x := x) (s := s) (d := d) 0 :=
  let initialCodeword :
      Codeword (F := F) s n 0 :=
    sWithOracles.oracleStmt ()
  { challenges := initialFoldChallenges (F := F) (k := k)
    codewords :=
      initialCodewords (F := F) (D := D) (n := n) (x := x) (s := s)
        initialCodeword
    poly := witness }

/-- Pure cast-free honest prover transition for a non-final fold round. -/
private def indexedProverNext
    (round : Nat) (hround : round < k)
    (state : IndexedProverState (D := D) (n := n) (x := x) (s := s) (d := d) round)
    (α : F) :
    Codeword (F := F) s n round.succ ×
      IndexedProverState
        (D := D) (n := n) (x := x) (s := s) (d := d) round.succ :=
  let i : Fin k := ⟨round, hround⟩
  let nextPoly : HonestPoly (F := F) s d round.succ :=
    honestFoldPoly (F := F) (s := s) (d := d) (i := i) state.poly α
  let nextCodeword : Codeword (F := F) s n round.succ :=
    honestCodeword (F := F) (D := D) (x := x) (s := s) (d := d)
      round.succ nextPoly
  let nextCodewordLast :
      FoldCodewordPrefix (F := F) (n := n) D x s round.succ
        (Fin.last round.succ) :=
    nextCodeword
  let nextChallenges : FoldChallenges (F := F) (k := k) :=
    recordChallenge (F := F) i state.challenges α
  let nextCodewords :
      OracleStatement
        (FoldCodewordPrefix (F := F) (n := n) D x s round.succ) :=
    Fin.snoc state.codewords nextCodewordLast
  let nextState :
      IndexedProverState
        (D := D) (n := n) (x := x) (s := s) (d := d) round.succ :=
    { challenges := nextChallenges
      codewords := nextCodewords
      poly := nextPoly }
  ⟨nextCodeword, nextState⟩

/-- Verifier state indexed directly by the absolute fold round. -/
private structure IndexedVerifierState (round : Nat) where
  challenges : FoldChallenges (F := F) (k := k)

/-- Initial verifier state for the indexed fold phase. -/
private def indexedVerifierInit :
    IndexedVerifierState (F := F) (k := k) 0 :=
  { challenges := initialFoldChallenges (F := F) (k := k) }

/-- Pure cast-free verifier transition for a non-final fold round. -/
private def indexedVerifierNext
    (round : Nat) (hround : round < k)
    (state : IndexedVerifierState (F := F) (k := k) round)
    (α : F) :
    IndexedVerifierState (F := F) (k := k) round.succ :=
  let i : Fin k := ⟨round, hround⟩
  { challenges := recordChallenge (F := F) i state.challenges α }

/-- One indexed honest-prover fold-round handler. -/
private def indexedProverStepAux {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {remaining round : Nat}
    (hround : round + (remaining + 1) = k)
    (state : IndexedProverState (D := D) (n := n) (x := x) (s := s) (d := d) round) :
    OracleComp oSpec
      (Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
        (foldRoundSpec (F := F) (n := n) D x s
          ⟨round, stateRound_lt (k := k) hround⟩).toInteractionSpec
        ((foldRoundSpec (F := F) (n := n) D x s
          ⟨round, stateRound_lt (k := k) hround⟩).toSpecRoles
            (foldRoundRoles (F := F) (n := n) D x s
              ⟨round, stateRound_lt (k := k) hround⟩))
        (fun _ => IndexedProverState
          (D := D) (n := n) (x := x) (s := s) (d := d) round.succ)) := do
  let roundIdx : Fin k := ⟨round, stateRound_lt (k := k) hround⟩
  pure <| fun α => do
    let next := indexedProverNext
      (F := F) (D := D) (n := n) (x := x) (s := s) (d := d)
      round roundIdx.2 state α
    let roundOutput :
        (_cw : Codeword (F := F) s n round.succ) ×
          IndexedProverState
            (D := D) (n := n) (x := x) (s := s) (d := d) round.succ :=
      ⟨next.1, next.2⟩
    pure <|
      (show OracleComp oSpec
          ((_cw : Codeword (F := F) s n round.succ) ×
            IndexedProverState
              (D := D) (n := n) (x := x) (s := s) (d := d) round.succ) from
        pure roundOutput)

/-- One indexed verifier fold-round handler. -/
private def indexedVerifierStepAux {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (sampleChallenge : (i : Fin k) → OracleComp oSpec F)
    {remaining round : Nat}
    (hround : round + (remaining + 1) = k)
    (state : IndexedVerifierState (F := F) (k := k) round) :
    Interaction.Spec.Counterpart.withMonads
      (foldRoundSpec (F := F) (n := n) D x s
        ⟨round, stateRound_lt (k := k) hround⟩).toInteractionSpec
      ((foldRoundSpec (F := F) (n := n) D x s
        ⟨round, stateRound_lt (k := k) hround⟩).toSpecRoles
          (foldRoundRoles (F := F) (n := n) D x s
            ⟨round, stateRound_lt (k := k) hround⟩))
      ((foldRoundSpec (F := F) (n := n) D x s
        ⟨round, stateRound_lt (k := k) hround⟩).toMonadDecoration oSpec
          (InputOracleFamily (F := F) (n := n) D x s)
          (foldRoundRoles (F := F) (n := n) D x s
            ⟨round, stateRound_lt (k := k) hround⟩)
          (foldRoundOD (F := F) (n := n) D x s
            ⟨round, stateRound_lt (k := k) hround⟩)
          []ₒ)
      (fun _ => IndexedVerifierState (F := F) (k := k) round.succ) := do
  let roundIdx : Fin k := ⟨round, stateRound_lt (k := k) hround⟩
  let α ← sampleChallenge roundIdx
  pure ⟨α, fun _ =>
    indexedVerifierNext (F := F) (k := k)
      round (stateRound_lt (k := k) hround) state α⟩

/-- Indexed honest-prover handlers for all remaining fold rounds. -/
private def indexedProverSteps {ι : Type} {oSpec : OracleSpec.{0, 0} ι} :
    (remaining round : Nat) → (h : round + remaining = k) →
      Interaction.Oracle.Spec.IndexedChain.Prover.RoundSteps
        (m := OracleComp oSpec)
        (IndexedProverState (D := D) (n := n) (x := x) (s := s) (d := d))
        remaining
        (foldPhaseIndexedChainFrom
          (D := D) (n := n) (x := x) (s := s) (k := k)
          remaining round h)
  | 0, _, _ => ⟨⟩
  | remaining + 1, round, h =>
      ⟨indexedProverStepAux
          (F := F) (D := D) (n := n) (x := x) (s := s) (d := d)
          (k := k) (oSpec := oSpec) h,
        fun _ =>
          indexedProverSteps (oSpec := oSpec)
            remaining round.succ (nextStateEq (k := k) h)⟩

/-- Indexed verifier handlers for all remaining fold rounds. -/
private def indexedVerifierSteps {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (sampleChallenge : (i : Fin k) → OracleComp oSpec F) :
    (remaining round : Nat) → (h : round + remaining = k) →
      Interaction.Oracle.Spec.IndexedChain.Verifier.RoundSteps
        (oSpec := oSpec)
        (OStmtIn := InputOracleFamily (F := F) (n := n) D x s)
        (IndexedVerifierState (F := F) (k := k))
        remaining
        (foldPhaseIndexedChainFrom
          (D := D) (n := n) (x := x) (s := s) (k := k)
          remaining round h)
  | 0, _, _ => ⟨⟩
  | remaining + 1, round, h =>
      ⟨indexedVerifierStepAux
          (F := F) (D := D) (n := n) (x := x) (s := s) (k := k)
          (oSpec := oSpec) sampleChallenge h,
        fun _ =>
          indexedVerifierSteps (oSpec := oSpec) sampleChallenge
            remaining round.succ (nextStateEq (k := k) h)⟩

end

end NativeOracle

end Fri
