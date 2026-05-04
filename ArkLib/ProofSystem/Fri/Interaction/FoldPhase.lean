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
terminal-indexed `Interaction.Oracle.Spec.PathChain` layer.
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

/-- Terminal-indexed native chain of the remaining non-final fold rounds.

The current round and terminal round `k` are both part of the chain type. That
extra endpoint is what lets final result code recover an `IndexedProverState k`
without a result-time cast. -/
def foldPhasePathChainFrom :
    (remaining round : Nat) → (h : round + remaining = k) →
      Interaction.Oracle.Spec.PathChain Nat remaining round k
  | 0, _round, h =>
      match h with
      | rfl => .nil
  | remaining + 1, round, h =>
      let i : Fin k := ⟨round, stateRound_lt (k := k) h⟩
      .cons
        (foldRoundSpec (F := F) (n := n) D x s i)
        (foldRoundRoles (F := F) (n := n) D x s i)
        (foldRoundOD (F := F) (n := n) D x s i)
        (fun _ => round.succ)
        (fun _ =>
          foldPhasePathChainFrom remaining round.succ
            (nextStateEq (k := k) h))

/-- Terminal-indexed native chain for all non-final fold rounds. -/
def foldPhasePathChain :
    Interaction.Oracle.Spec.PathChain Nat k 0 k :=
  foldPhasePathChainFrom (D := D) (n := n) (x := x) (s := s) (k := k)
    k 0 (initialRoundEq (k := k))

/-- Native oracle context for the full terminal-indexed non-final fold phase. -/
abbrev foldPhasePathContext : Interaction.Oracle.Spec :=
  Interaction.Oracle.Spec.PathChain.toSpec k
    (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))

/-- Native role decoration for the full terminal-indexed non-final fold phase. -/
abbrev foldPhasePathRoles :
    Interaction.Oracle.Spec.RoleDeco
      (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k)) :=
  Interaction.Oracle.Spec.PathChain.toRoles k
    (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))

/-- Native oracle decoration for the full terminal-indexed non-final fold phase. -/
abbrev foldPhasePathOD :
    Interaction.Oracle.Spec.OracleDeco
      (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k)) :=
  Interaction.Oracle.Spec.PathChain.toOracleDeco k
    (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))

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

/-- Terminal-indexed honest-prover handlers for all remaining fold rounds. -/
private def pathProverSteps {ι : Type} {oSpec : OracleSpec.{0, 0} ι} :
    (remaining round : Nat) → (h : round + remaining = k) →
      Interaction.Oracle.Spec.PathChain.Prover.RoundSteps
        (m := OracleComp oSpec)
        (IndexedProverState (D := D) (n := n) (x := x) (s := s) (d := d))
        remaining
        (foldPhasePathChainFrom
          (D := D) (n := n) (x := x) (s := s) (k := k)
          remaining round h)
  | 0, _, h => by
      cases h
      exact ⟨⟩
  | remaining + 1, round, h =>
      ⟨indexedProverStepAux
          (F := F) (D := D) (n := n) (x := x) (s := s) (d := d)
          (k := k) (oSpec := oSpec) h,
        fun _ =>
          pathProverSteps (oSpec := oSpec)
            remaining round.succ (nextStateEq (k := k) h)⟩

/-- Terminal-indexed verifier handlers for all remaining fold rounds. -/
private def pathVerifierSteps {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (sampleChallenge : (i : Fin k) → OracleComp oSpec F) :
    (remaining round : Nat) → (h : round + remaining = k) →
      Interaction.Oracle.Spec.PathChain.Verifier.RoundSteps
        (oSpec := oSpec)
        (OStmtIn := InputOracleFamily (F := F) (n := n) D x s)
        (IndexedVerifierState (F := F) (k := k))
        remaining
        (foldPhasePathChainFrom
          (D := D) (n := n) (x := x) (s := s) (k := k)
          remaining round h)
  | 0, _, h => by
      cases h
      exact ⟨⟩
  | remaining + 1, round, h =>
      ⟨indexedVerifierStepAux
          (F := F) (D := D) (n := n) (x := x) (s := s) (k := k)
          (oSpec := oSpec) sampleChallenge h,
        fun _ =>
          pathVerifierSteps (oSpec := oSpec) sampleChallenge
            remaining round.succ (nextStateEq (k := k) h)⟩

/-- Terminal prover state selected by a full terminal-indexed fold transcript. -/
private def pathTerminalProverState
    (pt :
      Interaction.Oracle.Spec.PublicTranscript
        (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k)))
    (state :
      Interaction.Oracle.Spec.PathChain.outputFamily
        (IndexedProverState (D := D) (n := n) (x := x) (s := s) (d := d))
        k
        (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))
        pt) :
    IndexedProverState (D := D) (n := n) (x := x) (s := s) (d := d) k :=
  Interaction.Oracle.Spec.PathChain.terminalOutput
    (IndexedProverState (D := D) (n := n) (x := x) (s := s) (d := d))
    k
    (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))
    pt state

/-- Terminal verifier state selected by a full terminal-indexed fold transcript. -/
private def pathTerminalVerifierState
    (pt :
      Interaction.Oracle.Spec.PublicTranscript
        (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k)))
    (state :
      Interaction.Oracle.Spec.PathChain.outputFamily
        (IndexedVerifierState (F := F) (k := k))
        k
        (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))
        pt) :
    IndexedVerifierState (F := F) (k := k) k :=
  Interaction.Oracle.Spec.PathChain.terminalOutput
    (IndexedVerifierState (F := F) (k := k))
    k
    (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))
    pt state

/-- Plain output statement extracted from the terminal prover state. -/
private def pathProverStatementResult
    (pt :
      Interaction.Oracle.Spec.PublicTranscript
        (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k)))
    (state :
      Interaction.Oracle.Spec.PathChain.outputFamily
        (IndexedProverState (D := D) (n := n) (x := x) (s := s) (d := d))
        k
        (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))
        pt) :
    FoldChallenges (F := F) (k := k) :=
  (pathTerminalProverState
    (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k)
    pt state).challenges

/-- Plain output statement extracted from the terminal verifier state. -/
private def pathVerifierStatementResult
    (pt :
      Interaction.Oracle.Spec.PublicTranscript
        (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k)))
    (state :
      Interaction.Oracle.Spec.PathChain.outputFamily
        (IndexedVerifierState (F := F) (k := k))
        k
        (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))
        pt) :
    FoldChallenges (F := F) (k := k) :=
  (pathTerminalVerifierState
    (F := F) (D := D) (n := n) (x := x) (s := s) (k := k)
    pt state).challenges

/-- Output oracle statements extracted from the terminal prover state. -/
private def pathOracleStatementResult
    (pt :
      Interaction.Oracle.Spec.PublicTranscript
        (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k)))
    (state :
      Interaction.Oracle.Spec.PathChain.outputFamily
        (IndexedProverState (D := D) (n := n) (x := x) (s := s) (d := d))
        k
        (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))
        pt) :
    OracleStatement (FoldCodewordOracleFamily (F := F) (n := n) D x s) :=
  (pathTerminalProverState
    (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k)
    pt state).codewords

/-- Honest witness extracted from the terminal prover state. -/
private def pathWitnessResult
    (pt :
      Interaction.Oracle.Spec.PublicTranscript
        (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k)))
    (state :
      Interaction.Oracle.Spec.PathChain.outputFamily
        (IndexedProverState (D := D) (n := n) (x := x) (s := s) (d := d))
        k
        (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))
        pt) :
    HonestPoly (F := F) s d k :=
  (pathTerminalProverState
    (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k)
    pt state).poly

end

end NativeOracle

end Fri
