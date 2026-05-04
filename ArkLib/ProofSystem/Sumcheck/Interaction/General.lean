/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.SingleRound
import ArkLib.Interaction.Oracle.Chain

/-!
# Interaction-Native Sum-Check: Native Multi-Round Surface

This module is intentionally small: it uses `Interaction.Oracle.Spec.Chain` as
the protocol-shape primitive, then gives a concrete one-round `StateT` prover
example.

The point of the state example is limited but useful. Ordinary, non-dependent
participant state, such as a challenge log, is cleanly carried by the monad. The
sum-check residual witness is more dependent: its type changes from
`PolyStmt ... (n + 1)` to `PolyStmt ... n` each round. That fits the generalized
chain composition layer as a `State : {k : Nat} → Chain k → Type`; this file
keeps the example to an ordinary challenge log.
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

/-- Stateful prover action monad used by the challenge-log examples. -/
abbrev ChallengeLogM {ι : Type} (oSpec : OracleSpec.{0, 0} ι) (R : Type) :=
  StateT (List R) (OracleComp oSpec)

/-- Constant node decoration whose prover nodes can update the challenge log. -/
abbrev challengeLogMonadDecoration
    {ι : Type} (oSpec : OracleSpec.{0, 0} ι) (s : Interaction.Oracle.Spec) :
    Interaction.Spec.MonadDecoration s.toInteractionSpec :=
  Interaction.Spec.MonadDecoration.constant
    ⟨ChallengeLogM oSpec R, inferInstance⟩ s.toInteractionSpec

/-- Lift construction in `OracleComp` into stateful challenge-log node effects.

This is the concrete `setupLift` bridge: building the suffix strategy does not
touch the challenge log, but the prefix nodes into which that build is spliced
run in `StateT (List R) (OracleComp oSpec)`. -/
def oracleCompToChallengeLogHom
    {ι : Type} (oSpec : OracleSpec.{0, 0} ι) (s : Interaction.Oracle.Spec) :
    Interaction.Spec.MonadDecoration.Hom s.toInteractionSpec
      (Interaction.Spec.MonadDecoration.constant
        ⟨OracleComp oSpec, inferInstance⟩ s.toInteractionSpec)
      (challengeLogMonadDecoration (R := R) oSpec s) :=
  Interaction.Spec.MonadDecoration.Hom.constant
    (fun {α} (mx : OracleComp oSpec α) (log : List R) => do
      let x ← mx
      pure (x, log))
    s.toInteractionSpec

/-- One native sum-check round where the prover records the verifier challenge
in its monadic state.

This is a genuine stateful-monad example: the challenge log lives in the
strategy action monad, and the terminal strategy output is just `PUnit`. -/
def challengeLogRoundStrategy
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (poly : CDegreeLE R deg) :
    Interaction.Spec.Strategy.withRoles (ChallengeLogM oSpec R)
      (roundSpec R deg).toInteractionSpec
      ((roundSpec R deg).toSpecRoles (roundRoles R deg))
      (fun _ => PUnit) := by
  unfold roundSpec roundRoles
  change StateT (List R) (OracleComp oSpec)
    ((x : CDegreeLE R deg) × (R → StateT (List R) (OracleComp oSpec) PUnit))
  exact fun log =>
    let respond : R → StateT (List R) (OracleComp oSpec) PUnit :=
      fun chal log' => pure (PUnit.unit, log' ++ [chal])
    pure (Sigma.mk poly respond, log)

/-- Monad-decorated view of `challengeLogRoundStrategy`. -/
def challengeLogRoundStrategyWithMonads
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (poly : CDegreeLE R deg) :
    Interaction.Spec.Strategy.withRolesAndMonads
      (roundSpec R deg).toInteractionSpec
      ((roundSpec R deg).toSpecRoles (roundRoles R deg))
      (challengeLogMonadDecoration (R := R) oSpec (roundSpec R deg))
      (fun _ => PUnit) :=
  Interaction.Spec.Strategy.withRolesAndMonads.ofWithRolesConstant
    (roundSpec R deg).toInteractionSpec
    ((roundSpec R deg).toSpecRoles (roundRoles R deg))
    (challengeLogRoundStrategy (oSpec := oSpec) poly)

/-- One-round prover setup for `challengeLogRoundStrategy`.

The setup monad is also `StateT`, but this example keeps setup pure and uses
state in the actual party continuation where the verifier challenge arrives. -/
def challengeLogRoundProver
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (poly : CDegreeLE R deg) :
    StateT (List R) (OracleComp oSpec)
      (Interaction.Spec.Strategy.withRoles (StateT (List R) (OracleComp oSpec))
        (roundSpec R deg).toInteractionSpec
        ((roundSpec R deg).toSpecRoles (roundRoles R deg))
        (fun _ => PUnit)) :=
  pure (challengeLogRoundStrategy (oSpec := oSpec) poly)

/-- Two native sum-check rounds composed through the monad-decorated oracle
composition API.

Here the build monad `m` is plain `OracleComp oSpec`: selecting the suffix
strategy may use oracle effects, but it does not itself update the challenge
log. The runtime node monads are `StateT (List R) (OracleComp oSpec)`, so
`oracleCompToChallengeLogHom` is the nontrivial `setupLift` from build effects
into stateful node effects. -/
def challengeLogTwoRoundStrategyWithMonads
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (poly₁ poly₂ : CDegreeLE R deg) :
    OracleComp oSpec
      (Interaction.Spec.Strategy.withRolesAndMonads
        ((roundSpec R deg).append (fun _ => roundSpec R deg)).toInteractionSpec
        (((roundSpec R deg).append (fun _ => roundSpec R deg)).toSpecRoles
          (Interaction.Oracle.Spec.RoleDeco.append
            (roundSpec R deg) (fun _ => roundSpec R deg)
            (roundRoles R deg) (fun _ => roundRoles R deg)))
        (Interaction.Oracle.Spec.MonadDecoration.appendPublic
          (roundSpec R deg) (fun _ => roundSpec R deg)
          (challengeLogMonadDecoration (R := R) oSpec (roundSpec R deg))
          (fun _ => challengeLogMonadDecoration (R := R) oSpec (roundSpec R deg)))
        (fun _ => PUnit)) :=
  Interaction.Oracle.Prover.compAuxWithMonads
    (roundSpec R deg) (fun _ => roundSpec R deg)
    (roundRoles R deg) (fun _ => roundRoles R deg)
    (md₂ := fun _ => challengeLogMonadDecoration (R := R) oSpec (roundSpec R deg))
    (oracleCompToChallengeLogHom (R := R) oSpec (roundSpec R deg))
    (OutType := fun _ _ => PUnit)
    (challengeLogRoundStrategyWithMonads (oSpec := oSpec) poly₁)
    (fun _ _ => pure (challengeLogRoundStrategyWithMonads (oSpec := oSpec) poly₂))

end

end NativeOracle

end Sumcheck
