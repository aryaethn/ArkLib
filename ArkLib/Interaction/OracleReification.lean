import ArkLib.Interaction.Oracle.Core

/-!
# Optional Reification for Interaction-Native Oracle Verifiers

This module adds an explicit optional layer on top of
`ArkLib.Interaction.Oracle`: concrete output-oracle reification is *not* part
of the core oracle-only API, but can be attached when a client knows how to
materialize the output oracle family from the input oracle data and transcript.
-/

open OracleComp

namespace Interaction
namespace OracleDecoration

namespace OracleReduction

/-- Query-level agreement between a reduction's output-oracle simulation and a
concrete family of output oracles. -/
def SimulatesConcrete
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : OracleReduction oSpec SharedIn Context Roles OD
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (shared : SharedIn)
    (oStatementIn : OracleStatement (OStatementIn shared))
    (tr : Spec.Transcript (Context shared))
    (oStatementOut : OracleStatement (OStatementOut shared tr)) : Prop :=
  ∀ i (q : OracleInterface.Query (OStatementOut shared tr i)),
    simulateQ
        (OracleDecoration.oracleContextImpl
          (Context shared) (Roles shared) (OD shared) oStatementIn tr)
        (reduction.simulate shared tr ⟨i, q⟩) =
      pure (OracleInterface.answer (oStatementOut i) q)

/-- Optional materialization of a reduction's output-oracle family. -/
structure Reification
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : OracleReduction oSpec SharedIn Context Roles OD
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut) where
  reify : (shared : SharedIn) → OracleStatement (OStatementIn shared) →
    (tr : Spec.Transcript (Context shared)) → Option (OracleStatement (OStatementOut shared tr))
  correct : ∀ (shared : SharedIn) (oStatementIn : OracleStatement (OStatementIn shared))
      (tr : Spec.Transcript (Context shared))
      (oStatementOut : OracleStatement (OStatementOut shared tr)),
      reify shared oStatementIn tr = some oStatementOut →
      SimulatesConcrete reduction shared oStatementIn tr oStatementOut

/-- Concrete output type obtained by reifying the output oracle family. -/
abbrev Output
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _)
    (shared : SharedIn) (tr : Spec.Transcript (Context shared)) :=
  StatementWithOracles
    (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr) shared

/-- Package a plain output statement together with reified output-oracle data. -/
def output
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {reduction : OracleReduction oSpec SharedIn Context Roles OD
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut}
    (reification : OracleReduction.Reification reduction)
    (shared : SharedIn) (oStatementIn : OracleStatement (OStatementIn shared))
    (tr : Spec.Transcript (Context shared)) (stmtOut : StatementOut shared tr) :
    Option (Output (Context := Context) (StatementOut := StatementOut) OStatementOut shared tr) := do
  let oStatementOut ← reification.reify shared oStatementIn tr
  pure ⟨stmtOut, oStatementOut⟩

end OracleReduction

end OracleDecoration

namespace OracleVerifier

/-- Query-level agreement between a statement-indexed oracle verifier's
output-oracle simulation and a concrete family of output oracles. -/
def SimulatesConcrete
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (verifier : Interaction.OracleVerifier oSpec SharedIn Context Roles OD
      StatementIn OStatementIn StatementOut OStatementOut)
    (shared : SharedIn)
    (oStatementIn : OracleStatement (OStatementIn shared))
    (tr : Spec.Transcript (Context shared))
    (oStatementOut : OracleStatement (OStatementOut shared tr)) : Prop :=
  ∀ i (q : OracleInterface.Query (OStatementOut shared tr i)),
    simulateQ
        (OracleDecoration.oracleContextImpl
          (Context shared) (Roles shared) (OD shared) oStatementIn tr)
        (verifier.simulate shared tr ⟨i, q⟩) =
      pure (OracleInterface.answer (oStatementOut i) q)

/-- Optional materialization of a statement-indexed oracle verifier's output
oracle family. -/
structure Reification
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (verifier : Interaction.OracleVerifier oSpec SharedIn Context Roles OD
      StatementIn OStatementIn StatementOut OStatementOut) where
  reify : (shared : SharedIn) → OracleStatement (OStatementIn shared) →
    (tr : Spec.Transcript (Context shared)) → Option (OracleStatement (OStatementOut shared tr))
  correct : ∀ (shared : SharedIn) (oStatementIn : OracleStatement (OStatementIn shared))
      (tr : Spec.Transcript (Context shared))
      (oStatementOut : OracleStatement (OStatementOut shared tr)),
      reify shared oStatementIn tr = some oStatementOut →
      SimulatesConcrete verifier shared oStatementIn tr oStatementOut

/-- Materialized output of a statement-indexed oracle verifier. -/
abbrev Output
    {SharedIn : Type _} {Context : SharedIn → Spec}
    (StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _)
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _)
    (shared : SharedIn) (tr : Spec.Transcript (Context shared)) :=
  StatementWithOracles
    (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr) shared

/-- Package a plain output statement together with reified oracle data. -/
def output
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {verifier : Interaction.OracleVerifier oSpec SharedIn Context Roles OD
      StatementIn OStatementIn StatementOut OStatementOut}
    (reification : OracleVerifier.Reification verifier)
    (shared : SharedIn) (oStatementIn : OracleStatement (OStatementIn shared))
    (tr : Spec.Transcript (Context shared)) (stmtOut : StatementOut shared tr) :
    Option (Output (Context := Context) StatementOut OStatementOut shared tr) := do
  let oStatementOut ← reification.reify shared oStatementIn tr
  pure ⟨stmtOut, oStatementOut⟩

end OracleVerifier

end Interaction
