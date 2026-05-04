/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Oracle
import ArkLib.Interaction.Oracle.Execution

/-!
# Sum-Check Single Round

This module defines the single-round sum-check oracle reduction on
`Interaction.Oracle.Spec`.
-/

namespace Sumcheck

open Interaction CompPoly CPoly OracleComp OracleSpec

section

variable {R : Type} [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R] {deg : ℕ}

/-- Advance a residual polynomial by fixing its first variable to the sampled
challenge. This is the stateful prover update for one sum-check round. -/
def stepResidual (chal : R)
    {numVars : ℕ} (poly : Sumcheck.PolyStmt R deg (numVars + 1)) :
    Sumcheck.PolyStmt R deg numVars :=
  ⟨CMvPolynomial.partialEvalFirst chal poly.1,
    CMvPolynomial.partialEvalFirst_individualDegreeLE chal poly.1 poly.2⟩

/-- The honest round polynomial computed from the current active residual. -/
def honestRoundPoly {m_dom : ℕ} (D : Fin m_dom → R)
    {numVars : ℕ}
    (poly : Sumcheck.PolyStmt R deg (numVars + 1)) :
    CDegreeLE R deg :=
  ⟨CMvPolynomial.roundPoly D numVars poly.1,
    CMvPolynomial.roundPoly_natDegree_le D poly.1 (fun mono hmono =>
      poly.2 ⟨0, by omega⟩ mono hmono)⟩

/-- The honest prover step for one oracle round, specialized to a private
residual polynomial witness that is threaded across rounds. -/
def roundProverStep (m : Type → Type) [Monad m]
    {NextState : Type}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {numVars : ℕ}
    (poly : Sumcheck.PolyStmt R deg (numVars + 1))
    (computeNext : R → NextState) :
    Interaction.Spec.Strategy.withRoles m
      (roundSpec R deg).toInteractionSpec
      ((roundSpec R deg).toSpecRoles (roundRoles R deg))
      (fun _ => NextState) :=
  let sentPoly := honestRoundPoly (R := R) (deg := deg) D poly
  pure ⟨sentPoly, fun chal => pure (computeNext chal)⟩

/-- One-round sum-check oracle reduction with a private residual polynomial
witness. The public oracle statement stays fixed as the original polynomial,
while the witness shrinks from `numVars + 1` variables to `numVars` after the
sampled challenge. -/
noncomputable def roundReduction
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R) :
    Interaction.Oracle.Reduction oSpec
      (RoundClaim R)
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ => roundOracleDeco R deg)
      (fun _ => PUnit)
      (fun _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (fun _ => Sumcheck.PolyStmt R deg (numVars + 1))
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (fun _ _ => Sumcheck.PolyStmt R deg numVars) where
  prover target sWithOracles witness := do
    let sentPoly := honestRoundPoly (R := R) (deg := deg) D witness
    pure <|
      roundProverStep (m := OracleComp oSpec) (R := R) (deg := deg) D witness
        (fun chal =>
          let nextClaim : Option (RoundClaim R) := some (CPolynomial.eval chal sentPoly.1)
          (⟨⟨nextClaim, sWithOracles.oracleStmt⟩,
              stepResidual (R := R) (deg := deg) chal witness⟩ :
            HonestProverOutput
              (StatementWithOracles (fun _ => Option (RoundClaim R))
                (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) target)
              (Sumcheck.PolyStmt R deg numVars)))
  verifier := {
    toFun := fun target _ =>
      verifierStep (R := R) (deg := deg)
        (Sumcheck.PolyFamily R deg (numVars + 1)) []ₒ D target sampleChallenge
    simulate := fun _ _ q =>
      liftM <| ([Sumcheck.PolyFamily R deg (numVars + 1)]ₒ).query q
  }

end

end Sumcheck
