/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.ToyProblem.Spec.General

/-!
# Knowledge soundness of the toy-problem IOR (ABF26 Lemma 6.6, corrected)

Plain (straightline) knowledge soundness of Construction 6.2
(`protocol62_knowledgeSound`), against the relaxed relation `R̃²_{C,δ}`.

## The error term deviates from the paper — deliberately

[ABF26] Lemma 6.6 claims knowledge error
`max{ε_mca(C,δ) + |Λ(C^{≡2},δ)|/|F|, (1−δ)^t}`. That bound is **false as
stated**: the paper's proof (tex 2224–2499) twice replaces conditional
probabilities by unconditional ones (`Pr[E | Δ≤δ] ⤳ Pr[E]`, and the
conditioning is silently dropped from the collision term), and there is a
concrete counterexample — take `f₁, f₂` to be exact codewords whose linear
targets are off by one; at the single `γ*` solving the folded linear
constraint the prover achieves acceptance probability `1` while no relaxed
witness exists. See `PAPER_REVS.md` item 11 for the full analysis (both the
proof-gap reading and the counterexample were independently adversarially
verified before this file was written).

What the paper's own pointwise arguments *do* prove — and what this file
formalizes — is the **sum form**

  `(ε_mca(C,δ) + |Λ(C^{≡2},δ)|/|F|) + (1−δ)^t`,

which coincides with the sum of the L6.8 round-by-round errors (so the
generic rbr→plain implication would give the same bound; the max-form's
apparent advantage was illusory).

## Proof structure

The proof is a two-level prefix split over the 3-round game, using the
generic machinery of `ArkLib/ToVCVio/OracleComp/RbrGame.lean`:

* The straightline extractor is the always-`some` classical choice
  `Spec.extractZero` (shared with L6.8/L6.10) — under the post-PR-#569
  game, extraction failure scores against the prover, and the choice
  extractor succeeds whenever *any* relaxed witness exists, so the game
  event forces "no witness exists".
* `verifier_run_loggingOracle_eq` collapses the (logged) oracle verifier on
  an arbitrary transcript to a `pure` `if accepts … then … else none`
  (via `verifierBody_simulateQ_eq_pure_ite`).
* The game then has the challenge-first shape consumed by
  `ProtocolSpec.probEvent_optionT_simulateQ_addLift_getChallenge_first_bind_le_add`
  (round-0 challenge `γ`), with prefix event "some message satisfies the
  post-γ state `gammaState` while extraction fails", bounded by
  `gamma_round_game_bound` (the MCA + list-decoding term).
* Off the prefix event, the remaining 2-round tail is bounded via
  `ProtocolSpec.probEvent_optionT_simulateQ_addLift_prefix_getChallenge_bind_le`
  (round-2 challenge `xs`), per-prefix bound `spotcheck_round_game_bound`
  (the `(1−δ)^t` term).

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6.2, Lemma 6.6 — error term corrected,
  see above).
-/

namespace ToyProblem

namespace Spec

open OracleSpec OracleComp ProtocolSpec
open Code InterleavedCode ListDecodable ProximityGap
open scoped NNReal ENNReal

variable {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]
variable (k t : ℕ)

section Protocol

omit [Fintype ι] [Fintype F] in
/-- The (logged) run of the C6.2 oracle verifier on an arbitrary transcript collapses to the
deterministic `pure` of "`some` output iff the §6.1 acceptance predicate holds", with an empty
verifier query log. Packages `verifierBody_simulateQ_eq_pure_ite` together with the
`toVerifier` output wrapper and the logging layer, so the L6.6 game reduction can rewrite the
verifier away in one step (under the prover-run binders, where the transcript is abstract). -/
private lemma verifier_run_loggingOracle_eq
    (encode : (Fin k → F) → (ι → F))
    (stmt : Statement (F := F) k) (oStmt : ∀ i, OracleStatement ι F i)
    (tr : (pSpec (ι := ι) (F := F) k t).FullTranscript) :
    (simulateQ loggingOracle
        ((oracleVerifier (k := k) (t := t) encode).toVerifier.run (stmt, oStmt) tr)).run
      = pure ((if accepts (k := k) (t := t) encode stmt oStmt
            (tr.challenges ⟨0, rfl⟩) (tr.messages ⟨1, rfl⟩)
            (tr.challenges ⟨2, rfl⟩)
          then some (((), nofun) :
            OutputStatement × ∀ i, OutputOracleStatement i) else none), ∅) := by
  classical
  simp only [Verifier.run, OracleVerifier.toVerifier, oracleVerifier]
  simp only [bind_pure_comp]
  rw [verifierBody_simulateQ_eq_pure_ite (k := k) (t := t) encode oStmt tr.messages
    stmt.1 stmt.2.1 stmt.2.2 (tr.challenges ⟨⟨0, by norm_num⟩, rfl⟩)
    (tr.challenges ⟨⟨2, by norm_num⟩, rfl⟩)]
  -- The `OptionT`-mapped output wrapper over a `pure` body, logged, is a `pure` with empty
  -- log — with the wrapper function abstract, so the `embed`-match term need not be spelled.
  have hmap : ∀ (fn : Unit → OutputStatement × ∀ i, OutputOracleStatement i)
      (o : Option Unit),
      (simulateQ loggingOracle
        ((fn <$> (show OptionT (OracleComp []ₒ) Unit from
            (pure o : OracleComp []ₒ (Option Unit))) :
          OptionT (OracleComp []ₒ) (OutputStatement × ∀ i, OutputOracleStatement i)) :
          OracleComp []ₒ (Option (OutputStatement × ∀ i, OutputOracleStatement i)))).run
        = pure (o.map fn, ∅) := by
    intro fn o
    cases o with
    | none =>
        rw [show ((fn <$> (show OptionT (OracleComp []ₒ) Unit from
            (pure none : OracleComp []ₒ (Option Unit))) :
            OptionT (OracleComp []ₒ) (OutputStatement × ∀ i, OutputOracleStatement i)) :
            OracleComp []ₒ (Option (OutputStatement × ∀ i, OutputOracleStatement i)))
          = (pure none : OracleComp []ₒ
              (Option (OutputStatement × ∀ i, OutputOracleStatement i))) from rfl,
          simulateQ_pure]
        rfl
    | some u =>
        rw [show ((fn <$> (show OptionT (OracleComp []ₒ) Unit from
            (pure (some u) : OracleComp []ₒ (Option Unit))) :
            OptionT (OracleComp []ₒ) (OutputStatement × ∀ i, OutputOracleStatement i)) :
            OracleComp []ₒ (Option (OutputStatement × ∀ i, OutputOracleStatement i)))
          = (pure (some (fn u)) : OracleComp []ₒ
              (Option (OutputStatement × ∀ i, OutputOracleStatement i))) from rfl,
          simulateQ_pure]
        rfl
  rw [hmap]
  split <;> rename_i h
  · rw [if_pos (show accepts (k := k) (t := t) encode stmt oStmt (tr.challenges ⟨0, rfl⟩)
      (tr.messages ⟨1, rfl⟩) (tr.challenges ⟨2, rfl⟩) from h)]
    rw [Option.map_some]
    refine congrArg pure (congrArg (·, ∅) (congrArg some (congrArg (Prod.mk ()) ?_)))
    funext i
    exact i.elim0
  · rw [if_neg (fun hacc : accepts (k := k) (t := t) encode stmt oStmt
        (tr.challenges ⟨0, rfl⟩) (tr.messages ⟨1, rfl⟩) (tr.challenges ⟨2, rfl⟩) ↦ h hacc),
      Option.map_none]

/-- **Lemma 6.6 of [ABF26], corrected** (knowledge soundness of Construction 6.2).

For any `δ ∈ (0, δ_min(C))` and fixed injective linear encoder with
range `C` (injectivity is implicit in the paper's encoding map and
load-bearing for the extractor's per-list-pair counting),
the toy-problem IOR has knowledge soundness against the relaxed relation
`R̃_{C,δ}^2` with error

  `(ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|) + (1 − δ)^t`.

**This error term corrects the paper.** [ABF26] Lemma 6.6 claims the `max`
of the two summands, which is **false as stated** — its proof replaces
conditional probabilities by unconditional ones, and a concrete
counterexample (exact codewords with off-by-one linear targets) beats the
claimed bound. The sum form is what the paper's own pointwise arguments
prove, and coincides with the sum of the L6.8 round errors. See
`PAPER_REVS.md` item 11 and this file's module docstring.

The `(Lambda …).toNat` in the error term is faithful: `Lambda` is never
`⊤` over a finite alphabet (`ListDecodable.Lambda_ne_top`), so `toNat`
loses nothing.

Stated against ArkLib's `OracleVerifier.knowledgeSoundness` (cf.
`OracleReduction/Security/Basic.lean :: OracleVerifier.knowledgeSoundness`,
definitionally `toVerifier.knowledgeSoundness`) — the faithful object
for an IOPP whose inputs `f₁, f₂` are oracles.

**Naming convention — paper vs API.** The ArkLib API's
`OracleVerifier.knowledgeSoundness` takes `(relIn, relOut)` where `relIn`
is the relation the extracted witness satisfies and `relOut` is the
relation the verifier's output must satisfy. In this file `relIn` is
*our* `outputRelationFor` (paper's `R̃²_{C,δ}`, checked against the
messages returned by the extractor) and `relOut` is `Set.univ` (paper's
C6.2 has trivial output `Unit`). The name `outputRelationFor` reflects
the **paper's** "this is the protocol's output relation" perspective; do
not be misled by the API parameter named `relIn`.

The straightline extractor is the always-`some` classical choice
`extractZero` (stmtIn-only; shared with L6.8/L6.10): under the
post-PR-#569 game extraction failure scores against the prover, and the
choice extractor succeeds whenever *any* relaxed witness exists, so the
game event forces "no relaxed witness exists" and the bound reduces to
the two-round prefix split described in the module docstring. -/
theorem protocol62_knowledgeSound
    [SampleableType F] [SampleableType ι] [Nonempty ι]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (C : Set (ι → F)) (δ : ℝ≥0)
    (encode : (Fin k → F) →ₗ[F] (ι → F))
    (hinj : Function.Injective encode)
    (hC : Set.range encode = C)
    (hδ_pos : 0 < δ)
    (hδ_lt_min : δ < (minRelHammingDistCode C : ℝ≥0)) :
      (oracleVerifier (k := k) (t := t) (encode : (Fin k → F) → (ι → F))).knowledgeSoundness
        (WitOut := OutputWitness)
        init impl (outputRelationFor k (encode : (Fin k → F) → (ι → F)) δ)
        (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) ×
          OutputWitness))
        (((epsMCA (F := F) (A := F) C δ).toNNReal +
            ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
              / (Fintype.card F : ℝ≥0)) +
          (1 - δ) ^ t) := by
  classical
  unfold OracleVerifier.knowledgeSoundness Verifier.knowledgeSoundness
  -- The straightline extractor: classical choice of any `R̃²` witness, from the input
  -- statement alone (always-`some`; cf. `Spec.extractZero`).
  refine ⟨fun stmtIn _ _ _ _ ↦
    pure (extractZero k ((encode : (Fin k → F) → (ι → F))) δ stmtIn), ?_⟩
  rintro ⟨stmt, oStmt⟩ witIn prover
  rw [ENNReal.coe_add]
  -- Outer split at the leading γ-draw (C6.2 is verifier-first): prefix event = "extraction
  -- fails yet some message satisfies the post-γ state", tail = the remaining two rounds.
  refine ProtocolSpec.probEvent_optionT_simulateQ_addLift_getChallenge_first_bind_le_add
    init impl _ ⟨0, rfl⟩
    (fun γ ↦ do
      let pre ← (liftComp (prover.receiveChallenge ⟨0, rfl⟩
            (prover.input ((stmt, oStmt), witIn)))
            ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)) >>= fun fc ↦
          liftComp (prover.sendMessage ⟨1, rfl⟩ (fc γ))
            ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)
      let xs ← liftComp ((pSpec (ι := ι) (F := F) k t).getChallenge ⟨2, rfl⟩)
          ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)
      (fun out : (OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness ↦
        if accepts (k := k) (t := t) ((encode : (Fin k → F) → (ι → F)))
            stmt oStmt γ pre.1 xs
        then some ((stmt, oStmt),
          some (extractZero k ((encode : (Fin k → F) → (ι → F))) δ (stmt, oStmt)),
          (((), nofun) : OutputStatement × ∀ i, OutputOracleStatement i), out.2)
        else none) <$>
        ((liftComp (prover.receiveChallenge
            (⟨2, by rfl⟩ : (pSpec (ι := ι) (F := F) k t).ChallengeIdx) pre.2)
            ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)) >>= fun fc2 ↦
          liftComp (prover.output (fc2 xs))
            ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)))
    _
    (fun γ ↦ ∃ w : Fin k → F,
      ((stmt, oStmt), extractZero k ((encode : (Fin k → F) → (ι → F))) δ (stmt, oStmt)) ∉
          outputRelationFor k ((encode : (Fin k → F) → (ι → F))) δ ∧
        gammaState k ((encode : (Fin k → F) → (ι → F))) δ stmt.1 stmt.2.1 stmt.2.2
          (oStmt 0) (oStmt 1) γ w)
    ?hoa ?h₁ ?h₂
  case h₁ =>
    exact gamma_round_game_bound k C δ encode hinj hC hδ_pos hδ_lt_min (stmt, oStmt)
  case h₂ =>
    intro γ hγ s
    -- Inner split at the spot-check draw, per fixed prefix `(γ, g)`.
    refine ProtocolSpec.probEvent_optionT_simulateQ_addLift_prefix_getChallenge_bind_le
      s impl _ ⟨2, rfl⟩ _ _ _ _ rfl (fun pre ↦ ?_)
    refine le_trans (probEvent_mono ?_) (spotcheck_round_game_bound k t
        ((encode : (Fin k → F) → (ι → F))) δ (stmt, oStmt) γ pre.1)
    rintro xs - ⟨out, b, hfb, hE⟩
    by_cases hacc : accepts (k := k) (t := t) ((encode : (Fin k → F) → (ι → F)))
        stmt oStmt γ pre.1 xs
    · rw [if_pos hacc, Option.some_inj] at hfb
      subst hfb
      refine ⟨PUnit.unit.{1}, fun hgs ↦ hγ ⟨pre.1, hE.1 _ rfl, hgs⟩, hacc⟩
    · rw [if_neg hacc] at hfb
      exact absurd hfb (by simp)
  case hoa =>
    simp only [Reduction.runWithLog, Verifier.run, Prover.runWithLog,
      OptionT.run_bind, OptionT.run_pure, liftM_pure, pure_bind, bind_assoc]
    simp only [verifier_run_loggingOracle_eq (k := k) (t := t)
      ((encode : (Fin k → F) → (ι → F))) stmt oStmt]
    simp only [Option.elimM, liftM_pure, OptionT.run_pure, pure_bind]
    -- `getM`-of-`if` and `elim`-of-`if` collapse to a pure `if`-value.
    have hgetM_run : ∀ {A : Type} (o : Option A),
        (Option.getM o : OptionT (OracleComp ([]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)) A).run = pure o := by
      intro A o; cases o <;> rfl
    have helim_ite : ∀ {A B : Type} (c : Prop) [Decidable c] (x y : Option A)
        (N : B) (S : A → B),
        (if c then x else y).elim N S = if c then x.elim N S else y.elim N S :=
      fun c _ x y N S ↦ apply_ite (fun o ↦ o.elim N S) c x y
    have hpure_ite : ∀ {A : Type} (c : Prop) [Decidable c] (x y : A),
        (if c then (pure x : OracleComp ([]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ) A) else pure y)
          = pure (if c then x else y) :=
      fun c _ x y ↦ (apply_ite pure c x y).symm
    simp only [Option.elim_some, hgetM_run, pure_bind, helim_ite, Option.elim_none,
      hpure_ite]
    done


end Protocol

end Spec

end ToyProblem
