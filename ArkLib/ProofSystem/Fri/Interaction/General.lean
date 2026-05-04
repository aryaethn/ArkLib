/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Fri.Interaction.FoldPhase
import ArkLib.ProofSystem.Fri.Interaction.QueryRound
import ArkLib.Interaction.Oracle.Composition

/-!
# FRI Interaction: Full Reduction

This module composes the FRI fold phase, terminal fold, and query round
using `Interaction.Oracle.Reduction.comp`.
-/

open Interaction CompPoly CPoly OracleComp OracleSpec

namespace Fri

namespace OracleLayer

section

variable {F : Type} [BEq F] [LawfulBEq F] [DecidableEq F] [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ}
variable [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (x : Fˣ)
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ)
variable (l : ℕ)

/-- Public interaction context for the fold phase followed by the
terminal fold. -/
abbrev foldFinalContext : Interaction.Oracle.Spec :=
  (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k)).append
    (fun _ => finalFoldSpec (F := F) (d := d))

/-- Role decoration for `foldFinalContext`. -/
abbrev foldFinalRoles :
    Interaction.Oracle.Spec.RoleDeco
      (foldFinalContext (F := F) (D := D) (n := n) (x := x) (s := s) (d := d)) :=
  Interaction.Oracle.Spec.RoleDeco.append
    (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k))
    (fun _ => finalFoldSpec (F := F) (d := d))
    (foldPhasePathRoles (D := D) (n := n) (x := x) (s := s) (k := k))
    (fun _ => finalFoldRoles (F := F) (d := d))

/-- Oracle-message decoration for `foldFinalContext`. -/
abbrev foldFinalOD :
    Interaction.Oracle.Spec.OracleDeco
      (foldFinalContext (F := F) (D := D) (n := n) (x := x) (s := s) (d := d)) :=
  Interaction.Oracle.Spec.OracleDeco.append
    (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k))
    (fun _ => finalFoldSpec (F := F) (d := d))
    (foldPhasePathOD (D := D) (n := n) (x := x) (s := s) (k := k))
    (fun _ => finalFoldOD (F := F) (d := d))

/-- Composition of the non-final FRI fold phase with the terminal fold.

The non-final fold phase emits the accumulated challenge vector and the full
codeword trace. The terminal fold consumes those challenges, sends the final
degree-bounded polynomial, and preserves the trace oracle for the query phase. -/
def foldFinalReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (sampleFoldChallenge : (i : Fin k) → OracleComp oSpec F)
    (sampleFinalChallenge : OracleComp oSpec F) :
    Interaction.Oracle.Reduction (ι := ι) oSpec PUnit
      (fun _ => foldFinalContext (F := F) (D := D) (n := n) (x := x) (s := s) (d := d))
      (fun _ => foldFinalRoles (F := F) (D := D) (n := n) (x := x) (s := s) (d := d))
      (fun _ => foldFinalOD (F := F) (D := D) (n := n) (x := x) (s := s) (d := d))
      (fun _ => PUnit)
      (ιₛᵢ := fun _ => Unit)
      (fun _ => InputOracleFamily (F := F) (n := n) D x s)
      (fun _ => HonestPoly (F := F) s d 0)
      (fun _ _ => FinalStatement (F := F) (k := k) (d := d))
      (ιₛₒ := fun _ _ => Unit)
      (fun _ _ => FoldCodewordTraceOracleFamily (F := F) (n := n) D x s)
      (fun _ _ => PUnit) := by
  exact Interaction.Oracle.Reduction.comp
    (foldPhaseContinuation (F := F) (D := D) (n := n) (x := x) (s := s) (d := d)
      sampleFoldChallenge)
    (fun _ _ =>
      finalFoldReduction (F := F) (D := D) (n := n) (x := x) (s := s) (d := d)
        (SharedIn := PUnit)
        (StatementIn := fun _ => FoldChallenges (F := F) (k := k))
        (fun _ challenges => challenges)
        (fun _ => sampleFinalChallenge))

/-- Public interaction context for the full FRI protocol. -/
abbrev context : Interaction.Oracle.Spec :=
  (foldFinalContext (F := F) (D := D) (n := n) (x := x) (s := s) (d := d)).append
    (fun _ => queryRoundSpec (n := n) (s := s) (l := l))

/-- Role decoration for the full FRI protocol. -/
abbrev roles :
    Interaction.Oracle.Spec.RoleDeco
      (context (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) l) :=
  Interaction.Oracle.Spec.RoleDeco.append
    (foldFinalContext (F := F) (D := D) (n := n) (x := x) (s := s) (d := d))
    (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
    (foldFinalRoles (F := F) (D := D) (n := n) (x := x) (s := s) (d := d))
    (fun _ => queryRoundRoles (n := n) (s := s) (l := l))

/-- Oracle-message decoration for the full FRI protocol. -/
abbrev oracleDeco :
    Interaction.Oracle.Spec.OracleDeco
      (context (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) l) :=
  Interaction.Oracle.Spec.OracleDeco.append
    (foldFinalContext (F := F) (D := D) (n := n) (x := x) (s := s) (d := d))
    (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
    (foldFinalOD (F := F) (D := D) (n := n) (x := x) (s := s) (d := d))
    (fun _ => queryRoundOD (n := n) (s := s) (l := l))

/-- Full FRI interaction reduction.

It runs all non-final folds, the terminal fold, and the query phase in one
oracle-reduction composition. The output statement is the query-phase
acceptance bit and the output oracle family is empty. -/
noncomputable def reduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (h_domain : totalShift s ≤ n)
    (sampleFoldChallenge : (i : Fin k) → OracleComp oSpec F)
    (sampleFinalChallenge : OracleComp oSpec F)
    (sampleQueries : OracleComp oSpec (QueryBatch (n := n) s l)) :
    Interaction.Oracle.Reduction (ι := ι) oSpec PUnit
      (fun _ => context (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) l)
      (fun _ => roles (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) l)
      (fun _ => oracleDeco (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) l)
      (fun _ => PUnit)
      (ιₛᵢ := fun _ => Unit)
      (fun _ => InputOracleFamily (F := F) (n := n) D x s)
      (fun _ => HonestPoly (F := F) s d 0)
      (fun _ _ => QueryResult)
      (ιₛₒ := fun _ _ => PEmpty)
      (fun _ _ => EmptyOracleFamily)
      (fun _ _ => PUnit) := by
  exact Interaction.Oracle.Reduction.comp
    (foldFinalReduction (F := F) (D := D) (n := n) (x := x) (s := s) (d := d)
      sampleFoldChallenge sampleFinalChallenge)
    (fun _ _ =>
      queryRoundReduction (F := F) (D := D) (n := n) (x := x) (s := s) (d := d)
        (l := l)
        (SharedIn := PUnit)
        (StatementIn := fun _ => FinalStatement (F := F) (k := k) (d := d))
        h_domain
        (fun _ stmt => stmt)
        (fun _ => sampleQueries))

end

end OracleLayer

end Fri
