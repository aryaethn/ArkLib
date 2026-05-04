/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.SingleRound
import ArkLib.Interaction.Oracle.Chain

/-!
# Interaction-Native Sum-Check: Native Multi-Round Surface

This module builds the native `n`-round sum-check oracle reduction from the
native single-round reduction and `Oracle.Reduction.comp`. The prover's private
state is the residual polynomial witness; its type shrinks from
`PolyStmt ... (n + 1)` to `PolyStmt ... n` at each round.
-/

namespace Sumcheck

open Interaction CompPoly OracleComp OracleSpec

namespace NativeOracle

section

variable (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R] (deg : ℕ)

/-- The native `n`-round sum-check oracle chain.

Each level is the existing one-round native oracle spec. The continuation is
constant because the next round shape does not depend on the public challenge;
participant state is handled by the parties, not by the protocol shape. -/
def fullChain : (n : Nat) → Interaction.Oracle.Spec.Chain n
  | 0 => ⟨⟩
  | n + 1 =>
      ⟨roundSpec R deg, roundRoles R deg, roundOracleDeco R deg, fun _ => fullChain n⟩

/-- Native `n`-round sum-check oracle spec, flattened from `fullChain`. -/
abbrev fullSpec (n : Nat) : Interaction.Oracle.Spec :=
  Interaction.Oracle.Spec.Chain.toSpec n (fullChain R deg n)

/-- Native role decoration for `fullSpec`. -/
abbrev fullRoles (n : Nat) : Interaction.Oracle.Spec.RoleDeco (fullSpec R deg n) :=
  Interaction.Oracle.Spec.Chain.toRoles n (fullChain R deg n)

/-- Native oracle decoration for `fullSpec`. -/
abbrev fullOracleDeco (n : Nat) :
    Interaction.Oracle.Spec.OracleDeco (fullSpec R deg n) :=
  Interaction.Oracle.Spec.Chain.toOracleDeco n (fullChain R deg n)

end

section

variable {R : Type} [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R] {deg : ℕ}

/-- Terminal native reduction for zero remaining sum-check rounds. -/
noncomputable def reductionStatefulOptionZero
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} (OStatementIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStatementIn i)] :
    Interaction.Oracle.Reduction oSpec
      (Option (RoundClaim R))
      (fun _ => .done)
      (fun _ => ⟨⟩)
      (fun _ => ⟨⟩)
      (fun _ => PUnit)
      (fun _ => OStatementIn)
      (fun _ => Sumcheck.PolyStmt R deg 0)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => OStatementIn)
      (fun _ _ => Sumcheck.PolyStmt R deg 0) where
  prover stmt sWithOracles witness :=
    pure ⟨⟨stmt, sWithOracles.oracleStmt⟩, witness⟩
  verifier := {
    toFun := fun stmt _ => stmt
    simulate := fun _ _ q => liftM <| ([OStatementIn]ₒ).query q
  }

/-- View an option-valued suffix reduction as the continuation expected by
`Oracle.Reduction.comp`.

The recursive suffix uses the current claim as its ambient shared input. Binary
composition instead passes the current claim as the local input statement to a
`PUnit`-shared continuation. This adapter moves the claim across that boundary
while leaving the oracle statement and shrinking witness untouched. -/
private noncomputable def optionReductionAsContinuation
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} (OStatementIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStatementIn i)]
    (n : Nat)
    (suffix :
      Interaction.Oracle.Reduction oSpec
        (Option (RoundClaim R))
        (fun _ => fullSpec R deg n)
        (fun _ => fullRoles R deg n)
        (fun _ => fullOracleDeco R deg n)
        (fun _ => PUnit)
        (fun _ => OStatementIn)
        (fun _ => Sumcheck.PolyStmt R deg n)
        (fun _ _ => Option (RoundClaim R))
        (fun _ _ => OStatementIn)
        (fun _ _ => Sumcheck.PolyStmt R deg 0)) :
    Interaction.Oracle.Reduction oSpec PUnit
      (fun _ => fullSpec R deg n)
      (fun _ => fullRoles R deg n)
      (fun _ => fullOracleDeco R deg n)
      (fun _ => Option (RoundClaim R))
      (fun _ => OStatementIn)
      (fun _ => Sumcheck.PolyStmt R deg n)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => OStatementIn)
      (fun _ _ => Sumcheck.PolyStmt R deg 0) where
  prover _ sWithOracles witness := do
    let input' : StatementWithOracles
        (fun _ : Option (RoundClaim R) => PUnit)
        (fun _ : Option (RoundClaim R) => OStatementIn)
        sWithOracles.stmt :=
      ⟨PUnit.unit, sWithOracles.oracleStmt⟩
    let strat ← suffix.prover sWithOracles.stmt input' witness
    let remap :
        (tr : Interaction.Spec.Transcript (fullSpec R deg n).toInteractionSpec) →
        HonestProverOutput
          (StatementWithOracles
            (fun _ : Option (RoundClaim R) => Option (RoundClaim R))
            (fun _ : Option (RoundClaim R) => OStatementIn)
            sWithOracles.stmt)
          (Sumcheck.PolyStmt R deg 0) →
        HonestProverOutput
          (StatementWithOracles
            (fun _ : PUnit => Option (RoundClaim R))
            (fun _ : PUnit => OStatementIn)
            PUnit.unit)
          (Sumcheck.PolyStmt R deg 0)
      | _, ⟨stmtOut, witOut⟩ => ⟨⟨stmtOut.stmt, stmtOut.oracleStmt⟩, witOut⟩
    pure <|
      Interaction.Spec.Strategy.withRolesAndMonads.mapOutput
        (fullSpec R deg n).toInteractionSpec
        ((fullSpec R deg n).toSpecRoles (fullRoles R deg n))
        ((fullSpec R deg n).toProverMonadDecoration oSpec)
        remap strat
  verifier := {
    toFun := fun _ stmt => suffix.verifier.toFun stmt PUnit.unit
    simulate := fun _ pt q => suffix.verifier.simulate none pt q
  }

/-- Successor step for the option-valued native sum-check reduction. -/
private noncomputable def reductionStatefulOptionSucc
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} (OStatementIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStatementIn i)]
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R)
    (n : Nat)
    (suffix :
      Interaction.Oracle.Reduction oSpec
        (Option (RoundClaim R))
        (fun _ => fullSpec R deg n)
        (fun _ => fullRoles R deg n)
        (fun _ => fullOracleDeco R deg n)
        (fun _ => PUnit)
        (fun _ => OStatementIn)
        (fun _ => Sumcheck.PolyStmt R deg n)
        (fun _ _ => Option (RoundClaim R))
        (fun _ _ => OStatementIn)
        (fun _ _ => Sumcheck.PolyStmt R deg 0)) :
    Interaction.Oracle.Reduction oSpec
      (Option (RoundClaim R))
      (fun _ => fullSpec R deg (n + 1))
      (fun _ => fullRoles R deg (n + 1))
      (fun _ => fullOracleDeco R deg (n + 1))
      (fun _ => PUnit)
      (fun _ => OStatementIn)
      (fun _ => Sumcheck.PolyStmt R deg (n + 1))
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => OStatementIn)
      (fun _ _ => Sumcheck.PolyStmt R deg 0) := by
  simpa [fullSpec, fullRoles, fullOracleDeco, fullChain] using
    Interaction.Oracle.Reduction.comp
      (SharedIn := Option (RoundClaim R))
      (Context₁ := fun _ => roundSpec R deg)
      (Roles₁ := fun _ => roundRoles R deg)
      (OracleDeco₁ := fun _ => roundOracleDeco R deg)
      (StatementIn := fun _ => PUnit)
      (ιₛᵢ := fun _ : Option (RoundClaim R) => ιₛᵢ)
      (OStatementIn := fun _ => OStatementIn)
      (WitnessIn := fun _ => Sumcheck.PolyStmt R deg (n + 1))
      (StatementMid := fun _ _ => Option (RoundClaim R))
      (ιₛₘ := fun _ _ => ιₛᵢ)
      (OStatementMid := fun _ _ => OStatementIn)
      (WitnessMid := fun _ _ => Sumcheck.PolyStmt R deg n)
      (Context₂ := fun _ _ => fullSpec R deg n)
      (Roles₂ := fun _ _ => fullRoles R deg n)
      (OracleDeco₂ := fun _ _ => fullOracleDeco R deg n)
      (StatementOut := fun _ _ _ => Option (RoundClaim R))
      (ιₛₒ := fun _ _ _ => ιₛᵢ)
      (OStatementOut := fun _ _ _ => OStatementIn)
      (WitnessOut := fun _ _ _ => Sumcheck.PolyStmt R deg 0)
      (roundReductionStatefulOptionWithOracle (R := R) (deg := deg)
        (oSpec := oSpec) OStatementIn D n sampleChallenge)
      (fun _ _ =>
        optionReductionAsContinuation (R := R) (deg := deg) (oSpec := oSpec)
          OStatementIn n suffix)

/-- Native stateful sum-check reduction with option-valued current claim.

This is the recursive continuation used after the first round. A `none` claim
means a previous verifier check failed; later rounds keep the same interaction
shape but preserve rejection. -/
noncomputable abbrev reductionStatefulOption
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} (OStatementIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStatementIn i)]
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) (n : Nat) :
    Interaction.Oracle.Reduction oSpec
      (Option (RoundClaim R))
      (fun _ => fullSpec R deg n)
      (fun _ => fullRoles R deg n)
      (fun _ => fullOracleDeco R deg n)
      (fun _ => PUnit)
      (fun _ => OStatementIn)
      (fun _ => Sumcheck.PolyStmt R deg n)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => OStatementIn)
      (fun _ _ => Sumcheck.PolyStmt R deg 0) :=
  Nat.rec
    (motive := fun n =>
      Interaction.Oracle.Reduction oSpec
        (Option (RoundClaim R))
        (fun _ => fullSpec R deg n)
        (fun _ => fullRoles R deg n)
        (fun _ => fullOracleDeco R deg n)
        (fun _ => PUnit)
        (fun _ => OStatementIn)
        (fun _ => Sumcheck.PolyStmt R deg n)
        (fun _ _ => Option (RoundClaim R))
        (fun _ _ => OStatementIn)
        (fun _ _ => Sumcheck.PolyStmt R deg 0))
    (by
      simpa [fullSpec, fullRoles, fullOracleDeco] using
        reductionStatefulOptionZero (R := R) (deg := deg) (oSpec := oSpec) OStatementIn)
    (fun n suffix =>
      reductionStatefulOptionSucc (R := R) (deg := deg) (oSpec := oSpec)
        OStatementIn D sampleChallenge n suffix)
    n

/-- Successor step for the top-level native sum-check reduction. -/
private noncomputable def reductionStatefulSucc
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} (OStatementIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStatementIn i)]
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R)
    (n : Nat)
    (suffix :
      Interaction.Oracle.Reduction oSpec
        (Option (RoundClaim R))
        (fun _ => fullSpec R deg n)
        (fun _ => fullRoles R deg n)
        (fun _ => fullOracleDeco R deg n)
        (fun _ => PUnit)
        (fun _ => OStatementIn)
        (fun _ => Sumcheck.PolyStmt R deg n)
        (fun _ _ => Option (RoundClaim R))
        (fun _ _ => OStatementIn)
        (fun _ _ => Sumcheck.PolyStmt R deg 0)) :
    Interaction.Oracle.Reduction oSpec
      (RoundClaim R)
      (fun _ => fullSpec R deg (n + 1))
      (fun _ => fullRoles R deg (n + 1))
      (fun _ => fullOracleDeco R deg (n + 1))
      (fun _ => PUnit)
      (fun _ => OStatementIn)
      (fun _ => Sumcheck.PolyStmt R deg (n + 1))
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => OStatementIn)
      (fun _ _ => Sumcheck.PolyStmt R deg 0) := by
  simpa [fullSpec, fullRoles, fullOracleDeco, fullChain] using
    Interaction.Oracle.Reduction.comp
      (SharedIn := RoundClaim R)
      (Context₁ := fun _ => roundSpec R deg)
      (Roles₁ := fun _ => roundRoles R deg)
      (OracleDeco₁ := fun _ => roundOracleDeco R deg)
      (StatementIn := fun _ => PUnit)
      (ιₛᵢ := fun _ : RoundClaim R => ιₛᵢ)
      (OStatementIn := fun _ => OStatementIn)
      (WitnessIn := fun _ => Sumcheck.PolyStmt R deg (n + 1))
      (StatementMid := fun _ _ => Option (RoundClaim R))
      (ιₛₘ := fun _ _ => ιₛᵢ)
      (OStatementMid := fun _ _ => OStatementIn)
      (WitnessMid := fun _ _ => Sumcheck.PolyStmt R deg n)
      (Context₂ := fun _ _ => fullSpec R deg n)
      (Roles₂ := fun _ _ => fullRoles R deg n)
      (OracleDeco₂ := fun _ _ => fullOracleDeco R deg n)
      (StatementOut := fun _ _ _ => Option (RoundClaim R))
      (ιₛₒ := fun _ _ _ => ιₛᵢ)
      (OStatementOut := fun _ _ _ => OStatementIn)
      (WitnessOut := fun _ _ _ => Sumcheck.PolyStmt R deg 0)
      (roundReductionStatefulWithOracle (R := R) (deg := deg)
        (oSpec := oSpec) OStatementIn D n sampleChallenge)
      (fun _ _ =>
        optionReductionAsContinuation (R := R) (deg := deg) (oSpec := oSpec)
          OStatementIn n suffix)

/-- Native stateful `n`-round sum-check reduction, built by composing native
one-round oracle reductions.

The input statement is the initial claim. The input oracle statement is carried
unchanged through all rounds, while the private residual polynomial witness
shrinks from `n` variables to zero variables. The output statement is
`Option (RoundClaim R)`, with `none` representing verifier rejection. -/
noncomputable def reductionStateful
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} (OStatementIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStatementIn i)]
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) (n : Nat) :
    Interaction.Oracle.Reduction oSpec
      (RoundClaim R)
      (fun _ => fullSpec R deg n)
      (fun _ => fullRoles R deg n)
      (fun _ => fullOracleDeco R deg n)
      (fun _ => PUnit)
      (fun _ => OStatementIn)
      (fun _ => Sumcheck.PolyStmt R deg n)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => OStatementIn)
      (fun _ _ => Sumcheck.PolyStmt R deg 0) :=
  match n with
  | 0 => {
      prover := fun stmt sWithOracles witness =>
        pure ⟨⟨some stmt, sWithOracles.oracleStmt⟩, witness⟩
      verifier := {
        toFun := fun stmt _ => some stmt
        simulate := fun _ _ q => liftM <| ([OStatementIn]ₒ).query q
      }
    }
  | n + 1 =>
      let suffix :=
        reductionStatefulOption (oSpec := oSpec) OStatementIn D sampleChallenge n
      reductionStatefulSucc (R := R) (deg := deg) (oSpec := oSpec)
        OStatementIn D sampleChallenge n suffix

end

end NativeOracle

end Sumcheck
