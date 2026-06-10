/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ArkLib.ToVCVio.EvalDist.Instances.OptionT
import ArkLib.ToVCVio.OracleComp.Coercions.SubSpec
import ArkLib.ToVCVio.ToMathlib.Control.StateT
import VCVio.EvalDist.Defs.NeverFails
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.SimSemantics.StateT.Basic
import VCVio.OracleComp.SimSemantics.OptionT.Basic

/-!
# Additions to VCV-io's `OracleComp.SimSemantics.SimulateQ`
-/

open OracleSpec OracleComp

/-- Simulating the random oracle leaves a mapped uniform `Fin` sample unchanged. -/
lemma simulateQ_randomOracle_map_uniformFin {α : Type} (n : ℕ) (f : Fin (n + 1) → α) :
    ((simulateQ (unifSpec.randomOracle :
      QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
      (f <$> uniformSample (Fin (n + 1)) : ProbComp α) :
        StateT unifSpec.QueryCache ProbComp α).run' ∅) =
      (f <$> uniformSample (Fin (n + 1))) := by
  rw [simulateQ_map, StateT.run'_map_comm]
  congr 1

/-- If all outputs of the original `OracleComp` are successful and satisfy `P`, then the
    simulated `OptionT` computation satisfies `P` with probability one. -/
lemma OptionT.probEvent_eq_one_of_simulateQ_support
    {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec (Option α)) (s₀ : σ) (P : α → Prop)
    (h : ∀ x ∈ support oa, ∃ a, x = some a ∧ P a) :
    Pr[P | OptionT.mk ((simulateQ impl oa).run' s₀)] = 1 := by
  letI := Classical.decPred P
  rw [probEvent_eq_one_iff]
  constructor
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    have hfail : Pr[⊥ | (simulateQ impl oa).run' s₀] = 0 :=
      probFailure_eq_zero
    rw [hfail, _root_.zero_add]
    exact probOutput_eq_zero_of_not_mem_support fun hnone =>
      let hnone' := support_simulateQ_run'_subset impl oa s₀ hnone
      let ⟨_, hsome, _⟩ := h none hnone'
      by cases hsome
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    obtain ⟨a, ha, hP⟩ := h (some x) (support_simulateQ_run'_subset impl oa s₀ hx)
    cases ha
    exact hP

/-- Bind-prefixed variant of `OptionT.probEvent_eq_one_of_simulateQ_support`: the simulated
    `OptionT` computation may sample its initial state `s₀` from an arbitrary `ProbComp σ`
    (e.g. the `(← init)` of `Reduction.perfectCompleteness`). Since
    `support_simulateQ_run'_subset` bounds the support uniformly in `s₀`, the support hypothesis
    `h` (independent of `s₀`) still discharges both the never-fail and all-outputs-`P` obligations.

    This is the form needed to close `OracleReduction`-style perfect-completeness goals, whose
    `OptionT.mk` body is `do let s ← init; (simulateQ impl oa).run' s`. -/
lemma OptionT.probEvent_eq_one_of_simulateQ_support_bind
    {ι σ α : Type} {spec : OracleSpec ι}
    (init : ProbComp σ)
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec (Option α)) (P : α → Prop)
    (h : ∀ x ∈ support oa, ∃ a, x = some a ∧ P a) :
    Pr[P | OptionT.mk (do let s ← init; (simulateQ impl oa).run' s)] = 1 := by
  letI := Classical.decPred P
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- The simulated computation never fails: for every sampled state `s`, the run' has no `none`
    -- in its support (it is bounded by `support oa`, which contains no `none` by `h`).
    rw [OptionT.probFailure_eq, OptionT.run_mk, add_eq_zero]
    refine ⟨probFailure_eq_zero, ?_⟩
    refine probOutput_eq_zero_of_not_mem_support fun hnone => ?_
    rw [mem_support_bind_iff] at hnone
    obtain ⟨s, _, hnone⟩ := hnone
    obtain ⟨_, hsome, _⟩ := h none (support_simulateQ_run'_subset impl oa s hnone)
    cases hsome
  · -- Every successful output satisfies `P`: peel the `init` bind, then `support_simulateQ_run'`.
    intro x hx
    rw [OptionT.mem_support_iff, OptionT.run_mk, mem_support_bind_iff] at hx
    obtain ⟨s, _, hx⟩ := hx
    obtain ⟨a, ha, hP⟩ := h (some x) (support_simulateQ_run'_subset impl oa s hx)
    cases ha
    exact hP

/-- Properties of `Option`-valued outputs of an underlying `OracleComp`
    propagate to elements in the support of the simulated, run, and `OptionT`-wrapped
    version. -/
lemma OptionT.aux_mem_support_simulateQ_run'
    {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec (Option α)) (s₀ : σ) (P : α → Prop)
    (h : ∀ x ∈ support oa, ∀ a, x = some a → P a)
    {x : α} (hx : x ∈ support (OptionT.mk ((simulateQ impl oa).run' s₀))) : P x := by
  rw [OptionT.mem_support_iff] at hx
  exact h (some x) (support_simulateQ_run'_subset impl oa s₀ hx) x rfl

namespace OptionT

lemma mem_support_bind_mk
    {α β : Type} (sample : ProbComp α) (body : α → ProbComp (Option β))
    {x : β}
    (hx : x ∈ support (OptionT.mk (do
      let a ← sample
      body a))) :
    ∃ a, a ∈ support sample ∧ x ∈ support (OptionT.mk (body a)) := by
  rw [OptionT.mem_support_iff] at hx
  simp only [OptionT.run_mk] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨a, _, hx⟩ := hx
  exact ⟨a, ‹a ∈ support sample›, by simpa [OptionT.mem_support_iff] using hx⟩

lemma map_mk_bind_eq_of_body
    {α β γ δ : Type}
    (sample : ProbComp α)
    (body₁ : α → ProbComp (Option β))
    (body₂ : α → ProbComp (Option γ))
    (f : β → δ) (post : α → γ → δ)
    (hBody : ∀ a, Option.map f <$> body₁ a = Option.map (post a) <$> body₂ a) :
    f <$> OptionT.mk (do
      let a ← sample
      body₁ a)
    =
    OptionT.mk (do
      let a ← sample
      let r ← body₂ a
      pure (Option.map (post a) r)) := by
  apply OptionT.ext
  rw [OptionT.run_map]
  simp only [OptionT.run_mk, map_eq_bind_pure_comp, bind_assoc]
  congr 1
  funext a
  rw [← map_eq_bind_pure_comp, hBody a, map_eq_bind_pure_comp]
  rfl

end OptionT

namespace StateT

lemma map_run'_eq_of_map_eq {m : Type → Type} {σ α β γ : Type}
    [Monad m] [LawfulMonad m] (f : α → γ) (g : β → γ)
    (mx : StateT σ m α) (my : StateT σ m β) (s : σ)
    (h : f <$> mx = g <$> my) :
    f <$> mx.run' s = g <$> my.run' s := by
  rw [← StateT.run'_map_comm f, ← StateT.run'_map_comm g]
  exact congrArg (fun mx : StateT σ m γ => mx.run' s) h

end StateT

lemma simulateQ_bind_map_eq_of_body
    {ι σ α β γ : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec α) (body₁ : α → OracleComp spec β)
    (body₂ : α → OracleComp spec γ) (f : γ → β)
    (hBody : ∀ a, simulateQ impl (body₁ a) = f <$> simulateQ impl (body₂ a)) :
    simulateQ impl (oa >>= body₁) = f <$> simulateQ impl (oa >>= body₂) := by
  rw [← simulateQ_map]
  simp only [map_eq_bind_pure_comp, simulateQ_bind, simulateQ_pure, bind_assoc,
    Function.comp]
  congr 1
  funext a
  exact hBody a

lemma StateT.run'_simulateQ_bind_map_eq_of_body
    {ι σ α β γ : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec α) (body₁ : α → OracleComp spec β)
    (body₂ : α → OracleComp spec γ) (f : γ → β) (s : σ)
    (hBody : ∀ a, simulateQ impl (body₁ a) = f <$> simulateQ impl (body₂ a)) :
    (simulateQ impl (oa >>= body₁)).run' s =
      f <$> (simulateQ impl (oa >>= body₂)).run' s := by
  rw [← StateT.run'_map_comm f]
  exact congrArg (fun mx : StateT σ ProbComp β => mx.run' s)
    (simulateQ_bind_map_eq_of_body impl oa body₁ body₂ f hBody)

/-- Resolve a `simulateQ` over a three-way `addLift impl (impl₁ + impl₂)` applied to a
computation `x : OracleComp spec₁ α` that has been double-`liftM`'d — first into the inner
sum `spec₁ + spec₂`, then into the outer sum `spec + (spec₁ + spec₂)`. The query routes to
the *left* inner implementation `impl₁`, leaving `liftM (simulateQ impl₁ x)`.

This is the `left` half of the `simOracle2`-routing pair: it peels the outer `addLift`
(`simulateQ_add_liftComp_right`), commutes the inner `simulateQ` past the target lift
(`simulateQ_liftTarget`), then peels the inner sum (`simulateQ_add_liftComp_left`). Stated
for the inner pair living in a possibly-different monad `n` lifted into the target `m`
(as `simOracle2`'s `Id`-valued `simOracle0`s are). Candidate for upstreaming to VCVio
next to `QueryImpl.simulateQ_add_liftComp_left`. -/
lemma simulateQ_addLift_add_liftM_left
    {ι ι₁ ι₂ : Type} {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {m₀ : Type → Type} [Monad m₀] [LawfulMonad m₀] [MonadLiftT m₀ m] [LawfulMonadLiftT m₀ m]
    {n : Type → Type} [Monad n] [LawfulMonad n] [MonadLiftT n m] [LawfulMonadLiftT n m]
    (impl : QueryImpl spec m₀) (impl₁ : QueryImpl spec₁ n) (impl₂ : QueryImpl spec₂ n)
    {α : Type} (x : OracleComp spec₁ α) :
    simulateQ (QueryImpl.addLift impl (QueryImpl.add impl₁ impl₂)
        : QueryImpl (spec + (spec₁ + spec₂)) m)
      (liftM (liftM x : OracleComp (spec₁ + spec₂) α) : OracleComp (spec + (spec₁ + spec₂)) α)
      = (liftM (simulateQ impl₁ x) : m α) := by
  rw [show QueryImpl.add impl₁ impl₂ = impl₁ + impl₂ from rfl,
    ← OracleComp.liftComp_eq_liftM, ← OracleComp.liftComp_eq_liftM,
    QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_right,
    simulateQ_liftTarget, QueryImpl.simulateQ_add_liftComp_left]

/-- Resolve a `simulateQ` over a three-way `addLift impl (impl₁ + impl₂)` applied to a
computation `x : OracleComp spec₂ α` that has been double-`liftM`'d — first into the inner
sum `spec₁ + spec₂`, then into the outer sum `spec + (spec₁ + spec₂)`. The query routes to
the *right* inner implementation `impl₂`, leaving `liftM (simulateQ impl₂ x)`.

The `right` companion of `simulateQ_addLift_add_liftM_left`; see that lemma for the
`simOracle2` motivation. -/
lemma simulateQ_addLift_add_liftM_right
    {ι ι₁ ι₂ : Type} {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {m₀ : Type → Type} [Monad m₀] [LawfulMonad m₀] [MonadLiftT m₀ m] [LawfulMonadLiftT m₀ m]
    {n : Type → Type} [Monad n] [LawfulMonad n] [MonadLiftT n m] [LawfulMonadLiftT n m]
    (impl : QueryImpl spec m₀) (impl₁ : QueryImpl spec₁ n) (impl₂ : QueryImpl spec₂ n)
    {α : Type} (x : OracleComp spec₂ α) :
    simulateQ (QueryImpl.addLift impl (QueryImpl.add impl₁ impl₂)
        : QueryImpl (spec + (spec₁ + spec₂)) m)
      (liftM (liftM x : OracleComp (spec₁ + spec₂) α) : OracleComp (spec + (spec₁ + spec₂)) α)
      = (liftM (simulateQ impl₂ x) : m α) := by
  rw [show QueryImpl.add impl₁ impl₂ = impl₁ + impl₂ from rfl,
    ← OracleComp.liftComp_eq_liftM, ← OracleComp.liftComp_eq_liftM,
    QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_right,
    simulateQ_liftTarget, QueryImpl.simulateQ_add_liftComp_right]
