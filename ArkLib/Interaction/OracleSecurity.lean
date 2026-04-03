import ArkLib.Interaction.OracleReification
import ArkLib.Interaction.Oracle.Continuation
import ArkLib.Interaction.Security

/-!
# Security Definitions for Interaction-Native Oracle Protocols

This module gives the oracle-side analog of `ArkLib.Interaction.Security`,
using the redesigned oracle-only reduction API from `ArkLib.Interaction.Oracle`.

The key design point is that verifier-side acceptance is phrased in terms of
*existence* of concrete output oracle statements compatible with the verifier's
query-level `simulate` interface, rather than by assuming a built-in
reification function. This means:

- The verifier never holds concrete oracle data; it only issues queries.
- Soundness asks: for any malicious prover, the probability that there *exists*
  a concrete output oracle family realizing the verifier's simulation *and*
  the resulting output passes the acceptance predicate is at most `ε`.
- Completeness asks: the honest prover produces concrete output oracle data
  that *does* realize the simulation, and the output passes acceptance.

## Main definitions

- `OracleReduction.completeness` — honest-execution completeness
- `OracleVerifier.soundness` — soundness against arbitrary provers
- `OracleVerifier.knowledgeSoundness` — knowledge soundness with a
  `Straightline` extractor
- `OracleStatement.Realizes` — coherence between a concrete oracle family
  and a deterministic query implementation

## See also

- `Security.lean` — plain (non-oracle) security definitions
- `OracleReification.lean` — optional concrete reification layer
-/

noncomputable section

open OracleComp
open scoped ENNReal

universe u v w

namespace Interaction
namespace OracleDecoration

namespace OracleStatement

/-- A concrete oracle statement `oStmt` realizes a deterministic query
implementation `impl` when every query is answered exactly as `oStmt` would
answer it. -/
def Realizes
    {ιₛ : Type v} {OStmt : ιₛ → Type w}
    [∀ i, OracleInterface (OStmt i)]
    (impl : QueryImpl [OStmt]ₒ Id) (oStmt : OracleStatement OStmt) : Prop :=
  ∀ i (q : OracleInterface.Query (OStmt i)),
    impl ⟨i, q⟩ = OracleInterface.answer (oStmt i) q

@[simp]
theorem realizes_simOracle0
    {ιₛ : Type v} {OStmt : ιₛ → Type w}
    [∀ i, OracleInterface (OStmt i)]
    (oStmt : OracleStatement OStmt) :
    Realizes (OracleInterface.simOracle0 OStmt oStmt) oStmt := by
  intro i q
  rfl

end OracleStatement

namespace OracleReduction

namespace Extractor

/-- A straightline extractor for a top-level oracle reduction observes the full
input statement (including oracle data), the transcript, the full output
statement (including output oracle data), and the malicious prover's terminal
witness output. -/
structure Straightline
    (Input : Type _) {ιₛᵢ : Input → Type _}
    (OStmtIn : (i : Input) → ιₛᵢ i → Type _)
    [∀ i j, OracleInterface (OStmtIn i j)]
    (LocalStmt WitnessIn : Input → Type _)
    (Context : Input → Spec)
    (StatementOut : (i : Input) → Spec.Transcript (Context i) → Type _)
    {ιₛₒ : (i : Input) → (tr : Spec.Transcript (Context i)) → Type _}
    (OStmtOut : (i : Input) → (tr : Spec.Transcript (Context i)) → ιₛₒ i tr → Type _)
    [∀ i tr j, OracleInterface (OStmtOut i tr j)]
    (WitnessOut : (i : Input) → Spec.Transcript (Context i) → Type _) where
  toFun : ∀ (i : Input)
      (s : StatementWithOracles LocalStmt OStmtIn i)
      (tr : Spec.Transcript (Context i)),
      StatementWithOracles (fun _ => StatementOut i tr) (fun _ => OStmtOut i tr) i →
      WitnessOut i tr → WitnessIn i

instance
    {Input : Type _} {ιₛᵢ : Input → Type _}
    {OStmtIn : (i : Input) → ιₛᵢ i → Type _}
    [∀ i j, OracleInterface (OStmtIn i j)]
    {LocalStmt WitnessIn : Input → Type _}
    {Context : Input → Spec}
    {StatementOut : (i : Input) → Spec.Transcript (Context i) → Type _}
    {ιₛₒ : (i : Input) → (tr : Spec.Transcript (Context i)) → Type _}
    {OStmtOut : (i : Input) → (tr : Spec.Transcript (Context i)) → ιₛₒ i tr → Type _}
    [∀ i tr j, OracleInterface (OStmtOut i tr j)]
    {WitnessOut : (i : Input) → Spec.Transcript (Context i) → Type _} :
    CoeFun
      (Straightline (Input := Input) (OStmtIn := OStmtIn)
        (LocalStmt := LocalStmt) (WitnessIn := WitnessIn)
        (Context := Context) (StatementOut := StatementOut)
        (OStmtOut := OStmtOut) (WitnessOut := WitnessOut))
      (fun _ => ∀ (i : Input) (s : StatementWithOracles LocalStmt OStmtIn i)
        (tr : Spec.Transcript (Context i)),
        StatementWithOracles (fun _ => StatementOut i tr) (fun _ => OStmtOut i tr) i →
        WitnessOut i tr → WitnessIn i) where
  coe E := E.toFun

end Extractor

/-- Honest completeness for an oracle reduction: on valid full inputs, honest
execution produces a valid full output, the prover and verifier agree on the
plain output statement, and the verifier's oracle-access semantics agree with
the honest prover's concrete output oracle statements. -/
def completeness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {Input : Type _} {ιₛᵢ : Input → Type _}
    {OStmtIn : (i : Input) → ιₛᵢ i → Type _}
    [∀ i j, OracleInterface (OStmtIn i j)]
    {Context : Input → Spec}
    {Roles : (i : Input) → RoleDecoration (Context i)}
    {OD : (i : Input) → OracleDecoration (Context i) (Roles i)}
    {LocalStmt WitnessIn : Input → Type _}
    {StatementOut : (i : Input) → Spec.Transcript (Context i) → Type _}
    {ιₛₒ : (i : Input) → (tr : Spec.Transcript (Context i)) → Type _}
    {OStmtOut : (i : Input) → (tr : Spec.Transcript (Context i)) → ιₛₒ i tr → Type _}
    [∀ i tr j, OracleInterface (OStmtOut i tr j)]
    {WitnessOut : (i : Input) → Spec.Transcript (Context i) → Type _}
    (reduction : OracleReduction oSpec Input OStmtIn
      Context Roles OD LocalStmt WitnessIn StatementOut OStmtOut WitnessOut)
    (relIn : ∀ (i : Input), StatementWithOracles LocalStmt OStmtIn i → WitnessIn i → Prop)
    (relOut : ∀ (i : Input) (tr : Spec.Transcript (Context i)),
      StatementWithOracles (fun _ => StatementOut i tr) (fun _ => OStmtOut i tr) i →
      WitnessOut i tr → Prop)
    (ε : ℝ≥0∞) : Prop :=
  ∀ (i : Input) (s : StatementWithOracles LocalStmt OStmtIn i) (w : WitnessIn i),
      relIn i s w →
    1 - ε ≤ Pr[fun z =>
      z.2.1.stmt.stmt = z.2.2.1 ∧
        OracleDecoration.OracleReduction.Simulates
          reduction i s.oracleStmt z.1 z.2.1.stmt.oracleStmt ∧
        relOut i z.1 z.2.1.stmt z.2.1.wit
      | reduction.execute i s w]

/-- Perfect completeness for an oracle reduction: completeness with error `0`. -/
def perfectCompleteness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {Input : Type _} {ιₛᵢ : Input → Type _}
    {OStmtIn : (i : Input) → ιₛᵢ i → Type _}
    [∀ i j, OracleInterface (OStmtIn i j)]
    {Context : Input → Spec}
    {Roles : (i : Input) → RoleDecoration (Context i)}
    {OD : (i : Input) → OracleDecoration (Context i) (Roles i)}
    {LocalStmt WitnessIn : Input → Type _}
    {StatementOut : (i : Input) → Spec.Transcript (Context i) → Type _}
    {ιₛₒ : (i : Input) → (tr : Spec.Transcript (Context i)) → Type _}
    {OStmtOut : (i : Input) → (tr : Spec.Transcript (Context i)) → ιₛₒ i tr → Type _}
    [∀ i tr j, OracleInterface (OStmtOut i tr j)]
    {WitnessOut : (i : Input) → Spec.Transcript (Context i) → Type _}
    (reduction : OracleReduction oSpec Input OStmtIn
      Context Roles OD LocalStmt WitnessIn StatementOut OStmtOut WitnessOut)
    (relIn : ∀ (i : Input), StatementWithOracles LocalStmt OStmtIn i → WitnessIn i → Prop)
    (relOut : ∀ (i : Input) (tr : Spec.Transcript (Context i)),
      StatementWithOracles (fun _ => StatementOut i tr) (fun _ => OStmtOut i tr) i →
      WitnessOut i tr → Prop) : Prop :=
  reduction.completeness relIn relOut 0

/-- A top-level oracle reduction accepts a plain verifier output `stmtOut` when
there exists concrete output oracle data that both agrees with `simulate` and
lands in the designated output language. -/
def Accepts
    {ι : Type _} {oSpec : OracleSpec ι}
    {Input : Type _} {ιₛᵢ : Input → Type _}
    {OStmtIn : (i : Input) → ιₛᵢ i → Type _}
    [∀ i j, OracleInterface (OStmtIn i j)]
    {Context : Input → Spec}
    {Roles : (i : Input) → RoleDecoration (Context i)}
    {OD : (i : Input) → OracleDecoration (Context i) (Roles i)}
    {LocalStmt WitnessIn : Input → Type _}
    {StatementOut : (i : Input) → Spec.Transcript (Context i) → Type _}
    {ιₛₒ : (i : Input) → (tr : Spec.Transcript (Context i)) → Type _}
    {OStmtOut : (i : Input) → (tr : Spec.Transcript (Context i)) → ιₛₒ i tr → Type _}
    [∀ i tr j, OracleInterface (OStmtOut i tr j)]
    {WitnessOut : (i : Input) → Spec.Transcript (Context i) → Type _}
    (reduction : OracleReduction oSpec Input OStmtIn
      Context Roles OD LocalStmt WitnessIn StatementOut OStmtOut WitnessOut)
    (langOut : ∀ (i : Input) (tr : Spec.Transcript (Context i)),
      Set (StatementWithOracles (fun _ => StatementOut i tr) (fun _ => OStmtOut i tr) i))
    (i : Input)
    (s : StatementWithOracles LocalStmt OStmtIn i)
    (tr : Spec.Transcript (Context i))
    (stmtOut : StatementOut i tr) : Prop :=
  ∃ oStmtOut : OracleStatement (OStmtOut i tr),
    OracleDecoration.OracleReduction.Simulates reduction i s.oracleStmt tr oStmtOut ∧
      ⟨stmtOut, oStmtOut⟩ ∈ langOut i tr

namespace Continuation

/-- Query-level agreement between a continuation's output-oracle simulation and
concrete output oracle data, relative to an arbitrary deterministic
implementation of the input oracle family. -/
def Simulates
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _} {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (shared : SharedIn) (inputImpl : QueryImpl [OStmtIn shared]ₒ Id)
    (tr : Spec.Transcript (Context shared))
    (oStmtOut : OracleStatement (OStmtOut shared tr)) : Prop :=
  ∀ i (q : OracleInterface.Query (OStmtOut shared tr i)),
    simulateQ (QueryImpl.add inputImpl
      (OracleDecoration.answerQuery (Context shared) (Roles shared) (OD shared) tr))
      (reduction.simulate shared tr ⟨i, q⟩) =
        pure (OracleInterface.answer (oStmtOut i) q)

/-- An abstract continuation input is in the input language when some concrete
oracle statement realizes the supplied input oracle implementation and yields a
full input statement in `langIn`. -/
def InLangIn
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _} {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    (langIn : ∀ shared,
      Set (StatementWithOracles StatementIn OStmtIn shared))
    (shared : SharedIn) (stmt : StatementIn shared)
    (inputImpl : QueryImpl [OStmtIn shared]ₒ Id) : Prop :=
  ∃ oStmtIn : OracleStatement (OStmtIn shared),
    OracleStatement.Realizes inputImpl oStmtIn ∧
      ⟨stmt, oStmtIn⟩ ∈ langIn shared

/-- A continuation accepts a plain verifier output `stmtOut` when some concrete
output oracle statement both agrees with the verifier's oracle-only semantics
and lands in the target language. -/
def Accepts
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _} {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (langOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementWithOracles (fun _ => StatementOut shared tr) (fun _ => OStmtOut shared tr) shared))
    (shared : SharedIn) (inputImpl : QueryImpl [OStmtIn shared]ₒ Id)
    (tr : Spec.Transcript (Context shared))
    (stmtOut : StatementOut shared tr) : Prop :=
  ∃ oStmtOut : OracleStatement (OStmtOut shared tr),
    Simulates reduction shared inputImpl tr oStmtOut ∧
      ⟨stmtOut, oStmtOut⟩ ∈ langOut shared tr

namespace Extractor

/-- A straightline extractor for a continuation observes a concrete realized
full input statement, the transcript, the full output statement, and the
malicious prover's terminal witness output. -/
structure Straightline
    (SharedIn : Type _)
    (Context : SharedIn → Spec)
    (StatementIn : SharedIn → Type _) {ιₛᵢ : SharedIn → Type _}
    (OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    (WitnessIn : SharedIn → Type _)
    (StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _)
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    (OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _)
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    (WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _) where
  toFun : ∀ (shared : SharedIn)
      (_ : StatementWithOracles StatementIn OStmtIn shared)
      (tr : Spec.Transcript (Context shared)),
      StatementWithOracles (fun _ => StatementOut shared tr) (fun _ => OStmtOut shared tr) shared →
      WitnessOut shared tr → WitnessIn shared

instance
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {StatementIn : SharedIn → Type _} {ιₛᵢ : SharedIn → Type _}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _} :
    CoeFun
      (Straightline (SharedIn := SharedIn) (Context := Context)
        (StatementIn := StatementIn) (OStmtIn := OStmtIn)
        (WitnessIn := WitnessIn) (StatementOut := StatementOut)
        (OStmtOut := OStmtOut) (WitnessOut := WitnessOut))
      (fun _ => ∀ (shared : SharedIn)
        (_ : StatementWithOracles StatementIn OStmtIn shared)
        (tr : Spec.Transcript (Context shared)),
        StatementWithOracles (fun _ => StatementOut shared tr) (fun _ => OStmtOut shared tr) shared →
        WitnessOut shared tr → WitnessIn shared) where
  coe E := E.toFun

end Extractor

/-- Honest completeness for a continuation oracle reduction. This quantifies
over arbitrary accumulated oracle context because continuations can start after
an earlier phase of a larger reduction. -/
def completeness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _} {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (relIn : ∀ (shared : SharedIn),
      StatementWithOracles StatementIn OStmtIn shared →
        WitnessIn shared → Prop)
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      StatementWithOracles (fun _ => StatementOut shared tr) (fun _ => OStmtOut shared tr) shared →
      WitnessOut shared tr → Prop)
    (ε : ℝ≥0∞) : Prop :=
  ∀ (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStmtIn shared)
      (w : WitnessIn shared) {ιₐ : Type _} (accSpec : OracleSpec ιₐ)
      (accImpl : QueryImpl accSpec Id),
      relIn shared s w →
        1 - ε ≤ Pr[fun z =>
          z.2.1.stmt.stmt = z.2.2.1 ∧
            Simulates reduction shared
              (OracleInterface.simOracle0 (OStmtIn shared) s.oracleStmt)
              z.1 z.2.1.stmt.oracleStmt ∧
            relOut shared z.1 z.2.1.stmt z.2.1.wit
          | reduction.execute shared s w accSpec accImpl]

/-- Perfect completeness for a continuation oracle reduction: completeness with
error `0`. -/
def perfectCompleteness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _} {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (relIn : ∀ (shared : SharedIn),
      StatementWithOracles StatementIn OStmtIn shared →
        WitnessIn shared → Prop)
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      StatementWithOracles (fun _ => StatementOut shared tr) (fun _ => OStmtOut shared tr) shared →
      WitnessOut shared tr → Prop) : Prop :=
  reduction.completeness relIn relOut 0

end Continuation
end OracleReduction

end OracleDecoration

namespace OracleVerifier

/-- An abstract verifier input is in the input language when some concrete input
oracle statement realizes the supplied input implementation and yields a full
input in `langIn`. -/
def InLangIn
    {Input : Type _}
    {ιₛᵢ : Input → Type _}
    {OStmtIn : (i : Input) → ιₛᵢ i → Type _}
    [∀ i j, OracleInterface (OStmtIn i j)]
    {LocalStmt : Input → Type _}
    (langIn : ∀ (i : Input), Set (StatementWithOracles LocalStmt OStmtIn i))
    (i : Input) (stmt : LocalStmt i) (inputImpl : QueryImpl [OStmtIn i]ₒ Id) : Prop :=
  ∃ oStmtIn : OracleStatement (OStmtIn i),
    OracleDecoration.OracleStatement.Realizes inputImpl oStmtIn ∧
      ⟨stmt, oStmtIn⟩ ∈ langIn i

/-- A verifier-only oracle protocol accepts a plain output when some concrete
realization of the abstract input oracle implementation, together with some
concrete output oracle family realizing the verifier's simulation, lands in the
target language. -/
def Accepts
    {ι : Type _} {oSpec : OracleSpec ι}
    {Input : Type _} {ιₛᵢ : Input → Type _}
    {OStmtIn : (i : Input) → ιₛᵢ i → Type _}
    [∀ i j, OracleInterface (OStmtIn i j)]
    {Context : Input → Spec}
    {Roles : (i : Input) → RoleDecoration (Context i)}
    {OD : (i : Input) → OracleDecoration (Context i) (Roles i)}
    {LocalStmt : Input → Type _}
    {StatementOut : (i : Input) → Spec.Transcript (Context i) → Type _}
    {ιₛₒ : (i : Input) → (tr : Spec.Transcript (Context i)) → Type _}
    {OStmtOut : (i : Input) → (tr : Spec.Transcript (Context i)) → ιₛₒ i tr → Type _}
    [∀ i tr j, OracleInterface (OStmtOut i tr j)]
    (verifier : Interaction.OracleVerifier oSpec Input OStmtIn Context Roles OD
      LocalStmt StatementOut OStmtOut)
    (langOut : ∀ (i : Input) (tr : Spec.Transcript (Context i)),
      Set (StatementWithOracles (fun _ => StatementOut i tr) (fun _ => OStmtOut i tr) i))
    (i : Input)
    (stmt : LocalStmt i)
    (inputImpl : QueryImpl [OStmtIn i]ₒ Id)
    (tr : Spec.Transcript (Context i))
    (stmtOut : StatementOut i tr) : Prop :=
  ∃ oStmtIn : OracleStatement (OStmtIn i),
    ∃ oStmtOut : OracleStatement (OStmtOut i tr),
      OracleDecoration.OracleStatement.Realizes inputImpl oStmtIn ∧
        Interaction.OracleVerifier.Simulates verifier i oStmtIn tr oStmtOut ∧
        ⟨stmtOut, oStmtOut⟩ ∈ langOut i tr

/-- Soundness for a verifier-only oracle protocol. The input oracle access may
be any deterministic implementation; invalidity means that no concrete full
input in `langIn` realizes that implementation. -/
def soundness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {Input : Type _} {ιₛᵢ : Input → Type _}
    {OStmtIn : (i : Input) → ιₛᵢ i → Type _}
    [∀ i j, OracleInterface (OStmtIn i j)]
    {Context : Input → Spec}
    {Roles : (i : Input) → RoleDecoration (Context i)}
    {OD : (i : Input) → OracleDecoration (Context i) (Roles i)}
    {LocalStmt : Input → Type _}
    {StatementOut : (i : Input) → Spec.Transcript (Context i) → Type _}
    {ιₛₒ : (i : Input) → (tr : Spec.Transcript (Context i)) → Type _}
    {OStmtOut : (i : Input) → (tr : Spec.Transcript (Context i)) → ιₛₒ i tr → Type _}
    [∀ i tr j, OracleInterface (OStmtOut i tr j)]
    (verifier : Interaction.OracleVerifier oSpec Input OStmtIn Context Roles OD
      LocalStmt StatementOut OStmtOut)
    (langIn : ∀ (i : Input), Set (StatementWithOracles LocalStmt OStmtIn i))
    (langOut : ∀ (i : Input) (tr : Spec.Transcript (Context i)),
      Set (StatementWithOracles (fun _ => StatementOut i tr) (fun _ => OStmtOut i tr) i))
    (ε : ℝ≥0∞) : Prop :=
  ∀ (i : Input) (stmt : LocalStmt i) (inputImpl : QueryImpl [OStmtIn i]ₒ Id)
      {OutputP : Spec.Transcript (Context i) → Type _}
      (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context i) (Roles i) OutputP)
      {ιₐ : Type _} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id),
      ¬ InLangIn langIn i stmt inputImpl →
        Pr[fun z => Accepts verifier langOut i stmt inputImpl z.1 z.2.2.1
          | OracleVerifier.run verifier i stmt inputImpl prover accSpec accImpl] ≤ ε

/-- Knowledge soundness for a verifier-only oracle protocol. The bad event says
that some concrete realization of the abstract input implementation together
with some compatible realization of the output oracle access satisfies the
output relation, yet the extractor's recovered witness does not validate that
realized full input. -/
def knowledgeSoundness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {Input : Type _} {ιₛᵢ : Input → Type _}
    {OStmtIn : (i : Input) → ιₛᵢ i → Type _}
    [∀ i j, OracleInterface (OStmtIn i j)]
    {Context : Input → Spec}
    {Roles : (i : Input) → RoleDecoration (Context i)}
    {OD : (i : Input) → OracleDecoration (Context i) (Roles i)}
    {LocalStmt WitnessIn : Input → Type _}
    {StatementOut : (i : Input) → Spec.Transcript (Context i) → Type _}
    {ιₛₒ : (i : Input) → (tr : Spec.Transcript (Context i)) → Type _}
    {OStmtOut : (i : Input) → (tr : Spec.Transcript (Context i)) → ιₛₒ i tr → Type _}
    [∀ i tr j, OracleInterface (OStmtOut i tr j)]
    {WitnessOut : (i : Input) → Spec.Transcript (Context i) → Type _}
    (verifier : Interaction.OracleVerifier oSpec Input OStmtIn Context Roles OD
      LocalStmt StatementOut OStmtOut)
    (relIn : ∀ (i : Input), Set (StatementWithOracles LocalStmt OStmtIn i × WitnessIn i))
    (relOut : ∀ (i : Input) (tr : Spec.Transcript (Context i)),
      Set (StatementWithOracles (fun _ => StatementOut i tr) (fun _ => OStmtOut i tr) i ×
        WitnessOut i tr))
    (ε : ℝ≥0∞) : Prop :=
  ∃ extractor : OracleDecoration.OracleReduction.Extractor.Straightline
      Input OStmtIn LocalStmt WitnessIn Context StatementOut OStmtOut WitnessOut,
  ∀ (i : Input) (stmt : LocalStmt i) (inputImpl : QueryImpl [OStmtIn i]ₒ Id)
      (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context i) (Roles i)
        (WitnessOut i))
      {ιₐ : Type _} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id),
      Pr[fun z =>
        ∃ oStmtIn : OracleStatement (OStmtIn i),
          ∃ oStmtOut : OracleStatement (OStmtOut i z.1),
            OracleDecoration.OracleStatement.Realizes inputImpl oStmtIn ∧
              Interaction.OracleVerifier.Simulates verifier i oStmtIn z.1 oStmtOut ∧
              (⟨z.2.2.1, oStmtOut⟩, z.2.1) ∈ relOut i z.1 ∧
              (⟨stmt, oStmtIn⟩,
                extractor i ⟨stmt, oStmtIn⟩ z.1 ⟨z.2.2.1, oStmtOut⟩ z.2.1) ∉ relIn i
        | OracleVerifier.run verifier i stmt inputImpl prover accSpec accImpl] ≤ ε

namespace Continuation

/-- An oracle verifier continuation input is valid when some concrete input
oracle statement realizes the supplied query implementation and lies in the
input language. -/
def InLangIn
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _} {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    (langIn : ∀ shared,
      Set (StatementWithOracles StatementIn OStmtIn shared))
    (shared : SharedIn) (stmt : StatementIn shared)
    (inputImpl : QueryImpl [OStmtIn shared]ₒ Id) : Prop :=
  ∃ oStmtIn : OracleStatement (OStmtIn shared),
    OracleDecoration.OracleStatement.Realizes inputImpl oStmtIn ∧
      ⟨stmt, oStmtIn⟩ ∈ langIn shared

/-- A verifier-only oracle continuation accepts a plain output when some
concrete output oracle family realizes the verifier's simulation and lies in
the target language. -/
def Simulates
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _} {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    (verifier : Interaction.OracleVerifier.Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn StatementOut OStmtOut)
    (shared : SharedIn) (inputImpl : QueryImpl [OStmtIn shared]ₒ Id)
    (tr : Spec.Transcript (Context shared))
    (oStmtOut : OracleStatement (OStmtOut shared tr)) : Prop :=
  ∀ i (q : OracleInterface.Query (OStmtOut shared tr i)),
    simulateQ (QueryImpl.add inputImpl
      (OracleDecoration.answerQuery (Context shared) (Roles shared) (OD shared) tr))
      (verifier.simulate shared tr ⟨i, q⟩) =
        pure (OracleInterface.answer (oStmtOut i) q)

/-- A verifier-only oracle continuation accepts a plain output when some
concrete output oracle family realizes the verifier's simulation and lies in
the target language. -/
def Accepts
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _} {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    (verifier : Interaction.OracleVerifier.Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn StatementOut OStmtOut)
    (langOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementWithOracles (fun _ => StatementOut shared tr) (fun _ => OStmtOut shared tr) shared))
    (shared : SharedIn) (inputImpl : QueryImpl [OStmtIn shared]ₒ Id)
    (tr : Spec.Transcript (Context shared))
    (stmtOut : StatementOut shared tr) : Prop :=
  ∃ oStmtOut : OracleStatement (OStmtOut shared tr),
    Simulates verifier shared inputImpl tr oStmtOut ∧
      ⟨stmtOut, oStmtOut⟩ ∈ langOut shared tr

/-- Soundness for a verifier-only oracle continuation. The input oracle access
is allowed to be any deterministic implementation; invalidity means that no
full input statement in `langIn` realizes that implementation. -/
def soundness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _} {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    (verifier : Interaction.OracleVerifier.Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn StatementOut OStmtOut)
    (langIn : ∀ shared,
      Set (StatementWithOracles StatementIn OStmtIn shared))
    (langOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementWithOracles (fun _ => StatementOut shared tr) (fun _ => OStmtOut shared tr) shared))
    (ε : ℝ≥0∞) : Prop :=
  ∀ (shared : SharedIn) (stmt : StatementIn shared) (inputImpl : QueryImpl [OStmtIn shared]ₒ Id)
      {OutputP : Spec.Transcript (Context shared) → Type _}
      (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context shared)
        (Roles shared) OutputP)
      {ιₐ : Type _} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id),
      ¬ InLangIn langIn shared stmt inputImpl →
        Pr[fun z => Accepts verifier langOut shared inputImpl z.1 z.2.2.1
          | OracleVerifier.Continuation.run verifier shared stmt inputImpl prover accSpec accImpl] ≤ ε

/-- Knowledge soundness for a verifier-only oracle continuation. The bad event
says that some realization of the input oracle access together with some
compatible realization of the output oracle access satisfies the output
relation, yet the extractor's recovered witness does not validate that
realized full input. -/
def knowledgeSoundness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _} {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (verifier : Interaction.OracleVerifier.Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn StatementOut OStmtOut)
    (relIn : ∀ shared,
      Set (StatementWithOracles StatementIn OStmtIn shared ×
        WitnessIn shared))
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementWithOracles (fun _ => StatementOut shared tr) (fun _ => OStmtOut shared tr) shared ×
        WitnessOut shared tr))
    (ε : ℝ≥0∞) : Prop :=
  ∃ extractor : OracleDecoration.OracleReduction.Continuation.Extractor.Straightline
      SharedIn Context StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut,
  ∀ (shared : SharedIn) (stmt : StatementIn shared) (inputImpl : QueryImpl [OStmtIn shared]ₒ Id)
      (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context shared)
        (Roles shared) (WitnessOut shared))
      {ιₐ : Type _} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id),
      Pr[fun z =>
        ∃ oStmtIn : OracleStatement (OStmtIn shared),
          ∃ oStmtOut : OracleStatement (OStmtOut shared z.1),
            OracleDecoration.OracleStatement.Realizes inputImpl oStmtIn ∧
              Simulates verifier shared inputImpl z.1 oStmtOut ∧
              (⟨z.2.2.1, oStmtOut⟩, z.2.1) ∈ relOut shared z.1 ∧
              (⟨stmt, oStmtIn⟩,
                extractor shared ⟨stmt, oStmtIn⟩ z.1 ⟨z.2.2.1, oStmtOut⟩ z.2.1)
                  ∉ relIn shared
        | OracleVerifier.Continuation.run verifier shared stmt inputImpl prover accSpec accImpl] ≤ ε

end Continuation
end OracleVerifier

end Interaction
