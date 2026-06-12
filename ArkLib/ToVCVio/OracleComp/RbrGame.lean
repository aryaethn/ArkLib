/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ArkLib.OracleReduction.ProtocolSpec.Basic
import ArkLib.Data.Probability.Instances

/-!
# Generic glue for the round-by-round (knowledge) soundness games

ArkLib's round-by-round soundness games (`Verifier.rbrSoundness`,
`Verifier.rbrKnowledgeSoundness` in `ArkLib/OracleReduction/Security/RoundByRound.lean`) all
compute, per challenge round `i`, a probability of the shape

```
Pr[ event | do
  (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
    (do
      let tr ← proverRun                                -- adversarial, arbitrary
      let challenge ← liftComp (pSpec.getChallenge i) _
      return (… tr … challenge …))).run' (← init)]
```

This file provides the generic ArkLib-local glue to bound such probabilities from
per-fixed-transcript bounds `∀ tr, Pr[ event tr · | $ᵗ (pSpec.Challenge i)] ≤ ε`:

* `ProtocolSpec.simulateQ_addLift_challengeQueryImpl_getChallenge` resolves the simulated
  challenge query into an explicit uniform draw `liftM ($ᵗ (pSpec.Challenge i))`;
* `ProtocolSpec.probEvent_simulateQ_addLift_getChallenge_bind_le` is the master mixture bound
  for the full game shape (built on VCV-io's `probEvent_bind_le_of_forall_le`);
* `probEvent_uniformSample_eq_prob_uniformOfFintype` bridges VCV-io's `$ᵗ` (the
  `SampleableType` uniform sampler used by `challengeQueryImpl`) to the PMF-level
  `Pr_{ let x ←$ᵖ α }[…]` notation in which per-transcript bounds are usually proven.

Everything here is ArkLib-local. The first two lemmas mention `ProtocolSpec`-specific
definitions and hence belong to ArkLib core rather than VCV-io; the bridge lemma is an
upstream candidate only after the `Pr_{…}` notation itself moves.
-/

open OracleComp OracleSpec ProtocolSpec ProbabilityTheory
open scoped ENNReal

namespace ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} [∀ j, SampleableType (pSpec.Challenge j)]
  {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- **Challenge-query resolution for the rbr games.** Simulating the lifted challenge query
`liftComp (pSpec.getChallenge i) _` under the game's combined implementation
`impl.addLift challengeQueryImpl` is exactly the uniform draw `$ᵗ (pSpec.Challenge i)` lifted
into `StateT σ ProbComp` (the oracle state is untouched).

The proof routes the lifted computation to the right summand of the `addLift`
(`QueryImpl.simulateQ_add_liftComp_right`), then resolves the single query
(`simulateQ_spec_query`); `challengeQueryImpl ⟨i, ()⟩ = $ᵗ (pSpec.Challenge i)` holds by
definition. -/
lemma simulateQ_addLift_challengeQueryImpl_getChallenge
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (i : pSpec.ChallengeIdx) :
    simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)) =
      (liftM ($ᵗ (pSpec.Challenge i)) : StateT σ ProbComp (pSpec.Challenge i)) := by
  rw [QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_right]
  -- `pSpec.getChallenge i` is reducibly `liftM ([pSpec.Challenge]ₒ.query ⟨i, ()⟩)`, and
  -- `(challengeQueryImpl.liftTarget _) ⟨i, ()⟩` is definitionally `liftM ($ᵗ _)`.
  exact (simulateQ_spec_query (challengeQueryImpl.liftTarget (StateT σ ProbComp))
    ⟨i, ()⟩).trans rfl

/-- **Master mixture bound for the rbr game shape.** If, for every *fixed* output `tr` of the
(adversarial, arbitrary) simulated prover run `oa`, the event holds over a fresh uniform
challenge with probability at most `ε`, then the whole game probability — initial state
sampled from `init`, prover run simulated under `impl.addLift challengeQueryImpl`, challenge
obtained via `liftComp (pSpec.getChallenge i) _` — is at most `ε`.

`f` packages the game's `return` expression (e.g. `fun tr c ↦ (tr.1.1, c, tr.2)` for
`rbrKnowledgeSoundness`); when applying this lemma to a game whose `do`-block destructures
the prover output, pass `f` explicitly and use `exact` (the match-lambdas agree only up to
definitional structure eta). -/
theorem probEvent_simulateQ_addLift_getChallenge_bind_le
    {T β : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) T) (i : pSpec.ChallengeIdx)
    (f : T → pSpec.Challenge i → β) (E : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ tr : T, Pr[ fun c ↦ E (f tr c) | $ᵗ (pSpec.Challenge i)] ≤ ε) :
    Pr[ E | do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let tr ← oa
          let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
          return f tr challenge)).run' (← init)] ≤ ε := by
  refine probEvent_bind_le_of_forall_le fun s _ ↦ ?_
  have hbody : (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (do
        let tr ← oa
        let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
        return f tr challenge)).run' s
      = (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp)) oa).run s
          >>= fun x ↦ f x.1 <$> ($ᵗ (pSpec.Challenge i)) := by
    rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
    refine bind_congr fun x ↦ ?_
    rw [simulateQ_bind, simulateQ_addLift_challengeQueryImpl_getChallenge, StateT.run_bind]
    simp only [simulateQ_pure, StateT.run_monadLift, StateT.run_pure, bind_pure_comp,
      Functor.map_map, monadLift_self]
  rw [hbody]
  refine probEvent_bind_le_of_forall_le fun x _ ↦ ?_
  rw [probEvent_map]
  exact h x.1

end ProtocolSpec

/-- **`$ᵗ` ↔ `$ᵖ` bridge.** The probability of an event under VCV-io's canonical uniform
sampler `$ᵗ α` (the `SampleableType.selectElem` used by `challengeQueryImpl`) coincides with
the PMF-level probability `Pr_{ let x ←$ᵖ α }[…]` under `PMF.uniformOfFintype`. Use it to
discharge the per-transcript hypothesis of
`ProtocolSpec.probEvent_simulateQ_addLift_getChallenge_bind_le` from a PMF-level bound. -/
lemma probEvent_uniformSample_eq_prob_uniformOfFintype {α : Type} [SampleableType α]
    [Fintype α] [Nonempty α] (p : α → Prop) :
    Pr[ p | $ᵗ α] = Pr_{ let x ←$ᵖ α }[ p x ] := by
  classical
  rw [probEvent_uniformSample, prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]

section ExecutableDocumentation

open ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} [∀ j, SampleableType (pSpec.Challenge j)]
  {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- Executable documentation: the master lemma engages the exact `rbrKnowledgeSoundness` game
shape — destructuring prover-output bind, challenge via `liftComp (pSpec.getChallenge i) _`,
`return` of the `(transcript, challenge, log)` triple — with `f` passed explicitly. -/
example {T₁ T₂ L : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) ((T₁ × T₂) × L)) (i : pSpec.ChallengeIdx)
    (E : T₁ × pSpec.Challenge i × L → Prop) {ε : ℝ≥0∞}
    (h : ∀ (t₁ : T₁) (log : L),
      Pr[ fun c ↦ E (t₁, c, log) | $ᵗ (pSpec.Challenge i)] ≤ ε) :
    Pr[ E | do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨⟨t₁, _⟩, log⟩ ← oa
          let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
          return (t₁, challenge, log))).run' (← init)] ≤ ε :=
  probEvent_simulateQ_addLift_getChallenge_bind_le init impl oa i
    (fun x c ↦ (x.1.1, c, x.2)) E (fun x ↦ h x.1.1 x.2)

end ExecutableDocumentation
