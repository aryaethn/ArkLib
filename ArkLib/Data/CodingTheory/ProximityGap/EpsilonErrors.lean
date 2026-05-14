/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.Probability.Instances

/-!
# Numeric ε-error functions: ε_ca and ε_mca

Numeric versions of the proximity gap, correlated agreement (CA), and mutual correlated
agreement (MCA) error functions as defined in
*Open Problems in List Decoding and Correlated Agreement*
(Arnon, Boneh, Fenzi; April 8, 2026), Section 4.

This file implements the **numeric error-function API** for CA and MCA. It coexists with the
predicate-style API in [`Basic.lean`](Basic.lean); each predicate has a bridging
`*_iff_eps*_le` lemma elsewhere in this directory.

## Main definitions

- `ProximityGap.epsPG` — proximity gap error, introduced informally in paper §4.1.
- `ProximityGap.epsCA` — ABF26 Definition 4.1: correlated agreement error
  `ε_ca(C, δ_fld, δ_int)`.
- `ProximityGap.epsCA'` — Convenience alias for the no-proximity-loss case
  `ε_ca(C, δ) := ε_ca(C, δ, δ)`.
- `ProximityGap.epsMCA` — ABF26 Definition 4.3: mutual correlated agreement error.

## Note on MCA with proximity loss (ABF26 Remark 4.4)

The paper intentionally does **not** define a proximity-loss variant of `ε_mca` analogous to
`ε_ca(C, δ_fld, δ_int)`. Per Remark 4.4 this remains to be thoroughly explored, so this file
exposes only the no-loss `ε_mca(C, δ)`.

## Open follow-ups

The following items from ABF26 Section 4 are tracked in `ABF26_PLAN.md` §7 and remain to be
added on top of this file's definitions. Each is in scope for Phase 1 of the plan:

- **Monotonicity / antitonicity of `epsCA`** (ABF26-D4.1 sub-tasks 4–5). `epsCA` is
  *monotone* in `δ_fld` (larger fold-distance ⇒ more `γ` in the event) and **antitone**
  in `δ_int` (larger interleaved-distance ⇒ stricter `Δ_joint > δ_int` condition).
- **ABF26 Remark 4.2** — discretization: `epsCA C δ (δ + β) = epsCA C δ (δ + β')` for
  `β, β' ∈ [0, 1/n)`. Follows from `Δ ∈ {0, 1/n, ..., 1}`.
- **ABF26 Fact 4.5** — `ε_pg ≤ ε_ca ≤ ε_mca`. Requires defining `epsPG` first.
- **ABF26 Lemma 4.6** — `ε_mca = ε_ca` below `δ_min(C)/2`. Proof leans on the helper
  predicates `pairJointAgreesOn` and `mcaEvent` defined here.
- **ABF26 Lemma 4.7** — `ε_mca(C^≡t, δ) ≤ t · ε_mca(C, δ)` via union bound.
- **Bridging lemmas**: `δ_ε_correlatedAgreementAffineLines C δ ε ↔ epsCA C δ δ ≤ ε` (and
  similar for `Curves`, `AffineSpaces`) connecting the predicate API in `Basic.lean` to the
  numeric API here.

## Design notes worth flagging

- **`F` is implicit in `epsCA` but does not appear in its return type**, so callers that
  invoke `epsCA` without an explicit pair `(f₁, f₂)` (e.g. inside `epsCA'`) need
  `epsCA (F := F) C δ δ` to thread `F` through. If this becomes painful in proofs,
  switching `epsCA` to take `F` as an explicit argument is a cheap refactor.
- **`epsMCA` and `mcaEvent` are `Fin 2`-only** (the affine-line case). Paper Section 4
  considers more general interleavings; generalizing to `Fin ℓ` is a future extension,
  not required for F4.5 or L4.6.
- **`pairJointAgreesOn` and `mcaEvent` are intentionally public**, exposed as named
  anchors for the planned L4.6 proof and bridging lemmas. If they prove unhelpful in
  practice they can be inlined / marked `private`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
-/

-- The definitions and proofs below all take the variables `ι`, `F`, `A` from a single section
-- (PMF forces them into `Type 0`). Several theorems use `Fintype`/`DecidableEq` instances at
-- proof-time but not in their types; suppressing the noisy `unused...InType` linter warnings
-- file-wide here, matching the idiom used in `ReedSolomon/FftDomain.lean` and similar files.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

section

-- Universe constraints: `PMF` (used by the `Pr_{...}` notation) is universe-monomorphic at
-- `Type 0`, so `ι`, `F`, and `A` must live in `Type`, matching the existing predicate-style API
-- in `Basic.lean` (`δ_ε_correlatedAgreementAffineLines` and friends).
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **ABF26 Section 4.1 (proximity gap error).** Worst-case "bad fraction" of `γ`-points
for which a line `f₁ + γ·f₂` is `δ`-close to `C` while the line is *not* entirely `δ`-close.

Paper §4.1 page 17 introduces this informally: a code has proximity gap `ε_pg(C, δ)` if
every line is either entirely `δ`-close to `C` (i.e. every `γ ∈ F` gives a δ-close point)
or at most `ε_pg` fraction of it is — a dichotomy. The strict comparison with `ε_ca`
(`epsPG ≤ epsCA`, paper Fact 4.5) is that the "bad" set for `epsPG` (`¬ ∀ γ, line close`)
is contained in the "bad" set for `epsCA` (`¬ jointProximity`) when `C` is closed under
linear combination, since any joint codeword pair `(v₀, v₁)` produces a line of codewords
`v₀ + γ·v₁ ∈ C`. -/
noncomputable def epsPG (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin 2) ι,
    if (∀ γ : F, δᵣ(u 0 + γ • u 1, C) ≤ δ) then (0 : ENNReal)
    else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ]

open Classical in
/-- **ABF26 Definition 4.1.** Correlated agreement (CA) error of an `F`-additive code `C`
with respect to fold-distance `δ_fld` and interleaved-distance `δ_int`.

The worst-case probability over pairs of words `(f₁, f₂)` and over `γ ← $ᵖ F` that

- the line `f₁ + γ·f₂` is `δ_fld`-close to `C`, **and**
- the pair `(f₁, f₂)` is **not** `δ_int`-close to the interleaved code `C^⋈ (Fin 2)`.

The second condition is `γ`-independent, so the formula simplifies to `0` when `(f₁, f₂)`
is jointly close, and to the line probability otherwise. Cf. paper Section 4.1. -/
noncomputable def epsCA (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin 2) ι,
    if jointProximity C (u := u) δ_int then (0 : ENNReal)
    else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ_fld]

/-- No-proximity-loss specialization: `ε_ca(C, δ) := ε_ca(C, δ, δ)`. Matches the paper's
short-form notation when both fold-distance and interleaved-distance coincide.

By definition `epsCA C δ δ ≡ epsCA' C δ`; no explicit `epsCA_self` simp lemma is needed
because the two forms are definitionally equal.

Currently unused inside this file — F4.5 and downstream theorems state things in terms of
`epsCA C δ δ` directly to keep the two `δ` arguments visible. Kept exported because external
callers (and future bridging lemmas) may prefer the short form. -/
noncomputable def epsCA' (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal :=
  epsCA (F := F) C δ δ

/-- The pair `(u₀, u₁)` jointly agrees with two codewords of `C` on every position in `S`.
Equivalent in spirit to `Δ_S((u₀, u₁), C^≡2) = 0` from the paper. -/
def pairJointAgreesOn (C : Set (ι → A)) (S : Finset ι) (u₀ u₁ : ι → A) : Prop :=
  ∃ v₀ ∈ C, ∃ v₁ ∈ C, ∀ i ∈ S, v₀ i = u₀ i ∧ v₁ i = u₁ i

/-- The "bad" event in ABF26 Definition 4.3: there is a witness set `S` of size at least
`(1-δ)·n` on which the line `u₀ + γ • u₁` exactly equals some codeword of `C`, but no
joint pair of codewords agrees with `(u₀, u₁)` on `S`. -/
def mcaEvent (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F) : Prop :=
  ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
    (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
    ¬ pairJointAgreesOn C S u₀ u₁

open Classical in
/-- **ABF26 Definition 4.3.** Mutual correlated agreement (MCA) error.

The worst-case probability over pairs `(f₁, f₂)` and over `γ ← $ᵖ F` of the
`mcaEvent`: a single set `S` of size `≥ (1-δ)·n` witnesses both that the line
`f₁ + γ·f₂` exactly equals some codeword of `C` on `S` **and** that no joint pair
of codewords agrees with `(f₁, f₂)` on `S`. MCA strengthens CA (Definition 4.1)
by requiring the witness set for closeness and non-agreement to coincide.

Per Remark 4.4, the paper intentionally does not define a proximity-loss variant. -/
noncomputable def epsMCA (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin 2) ι,
    Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ]

/-! ## Monotonicity of `epsCA` (ABF26 Definition 4.1 sub-tasks 4–5)

These two lemmas, together with `epsCA_eq_of_floor_eq`, characterize how `epsCA` varies
with its two distance arguments.

- `epsCA` is **monotone** in `δ_fld`: a larger fold-distance means more `γ` satisfy the
  "line `δ_fld`-close" event, so the inner `Pr` grows.
- `epsCA` is **antitone** in `δ_int`: a larger interleaved-distance is a *weaker* condition
  for `jointProximity`, so *more* pairs `(f₁, f₂)` are jointly close and contribute `0`
  rather than a non-zero `Pr`, decreasing the supremum.

The direction of the second one was a recurring confusion in the original plan; the proof
makes it concrete. -/

/-- **ABF26 Definition 4.1, sub-task 5.** `epsCA` is monotone in `δ_fld`. -/
theorem epsCA_mono_δ_fld
    (C : Set (ι → A)) {δ_fld δ_fld' : ℝ≥0} (δ_int : ℝ≥0) (h : δ_fld ≤ δ_fld') :
    epsCA (F := F) C δ_fld δ_int ≤ epsCA (F := F) C δ_fld' δ_int := by
  classical
  unfold epsCA
  apply iSup_mono
  intro u
  by_cases hjp : jointProximity (C := C) (u := u) δ_int
  · rw [if_pos hjp, if_pos hjp]
  · rw [if_neg hjp, if_neg hjp]
    -- `Pr_γ[Δ ≤ δ_fld] ≤ Pr_γ[Δ ≤ δ_fld']` by event implication.
    apply Pr_le_Pr_of_implies
    intro _ h_close
    exact le_trans h_close (by exact_mod_cast h)

/-- **ABF26 Definition 4.1, sub-task 4.** `epsCA` is **antitone** in `δ_int`. -/
theorem epsCA_antitone_δ_int
    (C : Set (ι → A)) (δ_fld : ℝ≥0) {δ_int δ_int' : ℝ≥0} (h : δ_int ≤ δ_int') :
    epsCA (F := F) C δ_fld δ_int' ≤ epsCA (F := F) C δ_fld δ_int := by
  classical
  unfold epsCA
  apply iSup_mono
  intro u
  -- `jointProximity` is monotone in `δ` (the relative distance comparison `δᵣ ≤ δ`
  -- becomes easier when `δ` grows), so `jointProximity_δ_int → jointProximity_δ_int'`.
  have h_jp_mono :
      jointProximity (C := C) (u := u) δ_int →
      jointProximity (C := C) (u := u) δ_int' := by
    intro h_jp
    exact le_trans h_jp (by exact_mod_cast h)
  by_cases hjp' : jointProximity (C := C) (u := u) δ_int'
  · rw [if_pos hjp']; exact zero_le _
  · -- Contrapositive of `h_jp_mono`: `¬jointProximity_δ_int' → ¬jointProximity_δ_int`.
    have hjp : ¬ jointProximity (C := C) (u := u) δ_int := fun h_jp => hjp' (h_jp_mono h_jp)
    rw [if_neg hjp', if_neg hjp]

/-! ## Helpers toward ABF26 Fact 4.5

Fact 4.5 says `ε_pg ≤ ε_ca ≤ ε_mca`. The first inequality requires the underlying code to
be closed under linear combination, so we state the helper lemmas with a `Submodule F (ι → A)`
hypothesis. -/

/-- **Helper for ABF26 Fact 4.5.** If the pair `(u 0, u 1)` is jointly `δ`-close to the
interleaved code from a `Submodule` `MC`, then for *every* scalar `γ`, the line
`u 0 + γ • u 1` is `δ`-close to `MC`. The proof uses the witness codeword pair
`(v 0, v 1)` to build a single line of codewords `v 0 + γ • v 1 ∈ MC`. -/
theorem jointProximity_imp_line_close
    (MC : Submodule F (ι → A)) (u : WordStack A (Fin 2) ι) (δ : ℝ≥0)
    (h : jointProximity (C := (MC : Set (ι → A))) (u := u) δ) :
    ∀ γ : F, δᵣ(u 0 + γ • u 1, (MC : Set (ι → A))) ≤ δ := by
  rw [← jointAgreement_iff_jointProximity] at h
  obtain ⟨S, hS_card, v, hv⟩ := h
  -- Common: pointwise agreement of `v i` and `u i` on `S`.
  have h_agree : ∀ j ∈ S, v 0 j = u 0 j ∧ v 1 j = u 1 j := by
    intro j hj
    refine ⟨?_, ?_⟩
    · have : j ∈ Finset.filter (fun k => v 0 k = u 0 k) Finset.univ := (hv 0).2 hj
      exact (Finset.mem_filter.mp this).2
    · have : j ∈ Finset.filter (fun k => v 1 k = u 1 k) Finset.univ := (hv 1).2 hj
      exact (Finset.mem_filter.mp this).2
  intro γ
  have hv_γ_mem : (v 0 + γ • v 1) ∈ (MC : Set (ι → A)) :=
    MC.add_mem (hv 0).1 (MC.smul_mem γ (hv 1).1)
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist]
  refine ⟨v 0 + γ • v 1, hv_γ_mem, ?_⟩
  rw [relCloseToWord_iff_exists_agreementCols]
  refine ⟨S, (relDist_floor_bound_iff_complement_bound _ _ _).mpr hS_card, ?_⟩
  intro j
  refine ⟨fun hj_in => ?_, fun hne hj_in => ?_⟩
  · obtain ⟨h0, h1⟩ := h_agree j hj_in
    simp [Pi.add_apply, Pi.smul_apply, h0, h1]
  · obtain ⟨h0, h1⟩ := h_agree j hj_in
    exact hne (by simp [Pi.add_apply, Pi.smul_apply, h0, h1])

/-- **ABF26 Fact 4.5, first inequality.** `ε_pg ≤ ε_ca` for a `Submodule F (ι → A)`.

Pointwise on `u : WordStack A (Fin 2) ι`:

- If `jointProximity` holds, every `γ` gives a δ-close line (by
  `jointProximity_imp_line_close`), so the `epsPG` contribution is 0; `epsCA`'s contribution
  is also 0 (its `if jointProximity` branch).
- Otherwise both contributions collapse to the same `Pr_γ[line δ-close]` because the inner
  expression is syntactically identical and the bad-set conditions both fail or both hold. -/
theorem epsPG_le_epsCA (MC : Submodule F (ι → A)) (δ : ℝ≥0) :
    epsPG (F := F) (MC : Set (ι → A)) δ ≤ epsCA (F := F) (MC : Set (ι → A)) δ δ := by
  unfold epsPG epsCA
  apply iSup_mono
  intro u
  by_cases hjp : jointProximity (C := (MC : Set (ι → A))) (u := u) δ
  · -- jointProximity ⇒ ∀ γ close (via the helper), so both `if`s pick the 0 branch.
    -- `rw` closes the residual `0 ≤ 0` goal automatically via its built-in `rfl` step.
    have h_all : ∀ γ : F, δᵣ(u 0 + γ • u 1, (MC : Set (ι → A))) ≤ δ :=
      jointProximity_imp_line_close MC u δ hjp
    rw [if_pos h_all, if_pos hjp]
  · by_cases h_all : ∀ γ : F, δᵣ(u 0 + γ • u 1, (MC : Set (ι → A))) ≤ δ
    · -- `epsPG` picks 0; `epsCA` picks Pr ≥ 0.
      rw [if_pos h_all, if_neg hjp]
      exact zero_le _
    · -- Both pick the same `Pr_γ[line δ-close]` (same expression inside the `Pr`).
      rw [if_neg h_all, if_neg hjp]

/-- **ABF26 Fact 4.5, second inequality.** `ε_ca ≤ ε_mca` for a `Submodule F (ι → A)`.

Pointwise on `u`:

- If `jointProximity`, `epsCA`'s contribution is 0, ≤ anything.
- Otherwise we apply `Pr_le_Pr_of_implies` with the fact that "line δ-close to `MC`" implies
  `mcaEvent MC δ (u 0) (u 1) γ` (in the `¬jointProximity` regime): the witness set `S` for
  the line-close fact has size `≥ (1-δ)·n` and is automatically *not* a joint-agreement
  set (because if it were, `jointProximity` would hold via the equivalence
  `jointAgreement_iff_jointProximity`). -/
theorem epsCA_le_epsMCA (MC : Submodule F (ι → A)) (δ : ℝ≥0) :
    epsCA (F := F) (MC : Set (ι → A)) δ δ ≤ epsMCA (F := F) (MC : Set (ι → A)) δ := by
  unfold epsCA epsMCA
  apply iSup_mono
  intro u
  by_cases hjp : jointProximity (C := (MC : Set (ι → A))) (u := u) δ
  · rw [if_pos hjp]; exact zero_le _
  · rw [if_neg hjp]
    -- Probability monotonicity: `Pr_γ[line close] ≤ Pr_γ[mcaEvent]` because, in the
    -- `¬jointProximity` regime, "line δ-close to MC" implies `mcaEvent`. The implication
    -- is proved per γ below.
    apply Pr_le_Pr_of_implies
    intro γ h_line
    -- Step 1: unfold the line-close witness. `h_line : δᵣ(line, MC) ≤ δ` gives a codeword `w`
    -- and a finite set `S` on which `line = w` pointwise.
    rw [relCloseToCode_iff_relCloseToCodeword_of_minDist] at h_line
    obtain ⟨w, hw_mem, hw_close⟩ := h_line
    rw [relCloseToWord_iff_exists_agreementCols] at hw_close
    obtain ⟨S, hS_card_nat, h_word_agree⟩ := hw_close
    have hS_card_real : (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι :=
      (relDist_floor_bound_iff_complement_bound _ _ _).mp hS_card_nat
    -- Step 2: assemble `mcaEvent` with witness `S`, codeword `w` for the line-side, and the
    -- still-to-prove negation on the pair-side.
    refine ⟨S, hS_card_real, ⟨w, hw_mem, fun i hi => ((h_word_agree i).1 hi).symm⟩, ?_⟩
    -- Step 3: ¬ pairJointAgreesOn MC S (u 0) (u 1). Argue by contradiction with `hjp`:
    -- if there were a joint codeword pair agreeing on `S`, `finMapTwoWords` would build a
    -- jointAgreement witness, which `jointAgreement_iff_jointProximity` would lift to
    -- `jointProximity`, contradicting the hypothesis `¬jointProximity`.
    intro h_pair
    apply hjp
    rw [← jointAgreement_iff_jointProximity]
    obtain ⟨v₀, hv₀_mem, v₁, hv₁_mem, h_pair_agree⟩ := h_pair
    refine ⟨S, hS_card_real, finMapTwoWords v₀ v₁, ?_⟩
    intro i
    refine ⟨?_, ?_⟩
    · -- `(finMapTwoWords v₀ v₁) i ∈ MC` by cases on `i : Fin 2`.
      fin_cases i
      · exact hv₀_mem
      · exact hv₁_mem
    · -- `S ⊆ filter (· = u i)` by cases on `i`.
      intro j hj
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      fin_cases i
      · exact (h_pair_agree j hj).1
      · exact (h_pair_agree j hj).2

/-- **ABF26 Fact 4.5.** For an `F`-additive code (here: a `Submodule F (ι → A)`):
`ε_pg(C, δ) ≤ ε_ca(C, δ, δ) ≤ ε_mca(C, δ)`. -/
theorem epsPG_le_epsCA_le_epsMCA (MC : Submodule F (ι → A)) (δ : ℝ≥0) :
    epsPG (F := F) (MC : Set (ι → A)) δ ≤ epsCA (F := F) (MC : Set (ι → A)) δ δ ∧
    epsCA (F := F) (MC : Set (ι → A)) δ δ ≤ epsMCA (F := F) (MC : Set (ι → A)) δ :=
  ⟨epsPG_le_epsCA MC δ, epsCA_le_epsMCA MC δ⟩

/-- **ABF26 Remark 4.2 (level-set form).** Because relative Hamming distance only takes
values in `{0, 1/n, ..., 1}`, the predicate `jointProximity C u δ_int` (which is
`δᵣ(⋈|u, C^⋈ 2) ≤ δ_int`) depends on `δ_int` only through `⌊δ_int · n⌋`. Hence
`epsCA C δ_fld δ_int` is constant on every "level set" `[k/n, (k+1)/n)` of `δ_int`.

The paper states this with a "shift by `β, β' ∈ [0, 1/n)`" idiom (`ε_ca(C, δ, δ + β) =
ε_ca(C, δ, δ + β')`); that form follows from this lemma whenever the interval
`[δ + min β β', δ + max β β']` does not cross a multiple of `1/n` — in particular when
`δ` is itself such a multiple. -/
theorem epsCA_eq_of_floor_eq (C : Set (ι → A)) (δ_fld δ_int δ_int' : ℝ≥0)
    (h : Nat.floor (δ_int * Fintype.card ι) = Nat.floor (δ_int' * Fintype.card ι)) :
    epsCA (F := F) C δ_fld δ_int = epsCA (F := F) C δ_fld δ_int' := by
  unfold epsCA
  apply iSup_congr
  intro u
  -- `jointProximity` is determined by `Δ₀ ≤ ⌊δ · n⌋` via
  -- `relDistFromCode_le_iff_distFromCode_le`, so it agrees on `δ_int` and `δ_int'`
  -- whenever the floors agree.
  have h_iff : jointProximity (C := C) (u := u) δ_int ↔
               jointProximity (C := C) (u := u) δ_int' := by
    unfold jointProximity
    rw [relDistFromCode_le_iff_distFromCode_le, relDistFromCode_le_iff_distFromCode_le, h]
  by_cases hjp : jointProximity (C := C) (u := u) δ_int
  · rw [if_pos hjp, if_pos (h_iff.mp hjp)]
  · rw [if_neg hjp, if_neg (mt h_iff.mpr hjp)]

/-! ## Bridging the predicate-style API in `Basic.lean` to the numeric API here

These iff-lemmas let downstream code that was written against `δ_ε_correlatedAgreement*`
predicates migrate to the numeric `eps*` form (or vice versa) without rewriting proofs. -/

/-- **Bridge.** The predicate `δ_ε_correlatedAgreementAffineLines C δ ε` (from `Basic.lean`)
is equivalent to the numeric inequality `epsCA C δ δ ≤ ε`.

Forward: assume the predicate. For each `u`, the `epsCA` body is either `0` (when
`jointProximity`) or `Pr_γ[line δ-close]`; in the latter case `¬jointAgreement`, so the
predicate's contrapositive gives `Pr ≤ ε`. `iSup_le` concludes.

Backward: assume `epsCA ≤ ε`. For any `u` with `Pr > ε`, the contribution `body u` is at most
`epsCA ≤ ε`. If `¬jointProximity`, `body u = Pr > ε` is a contradiction; so
`jointProximity`, hence `jointAgreement` via the existing equivalence. -/
theorem δ_ε_correlatedAgreementAffineLines_iff_epsCA_le
    (C : Set (ι → A)) (δ ε : ℝ≥0) :
    δ_ε_correlatedAgreementAffineLines (F := F) C δ ε ↔
    epsCA (F := F) C δ δ ≤ (ε : ENNReal) := by
  classical
  constructor
  · intro h_pred
    refine iSup_le fun u => ?_
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [if_pos hjp]; exact zero_le _
    · rw [if_neg hjp]
      have h_not_ja : ¬ jointAgreement (C := C) (W := u) δ := by
        rw [jointAgreement_iff_jointProximity]; exact hjp
      by_contra h_gt
      push Not at h_gt
      exact h_not_ja (h_pred u h_gt)
  · intro h_eps u h_pr
    unfold epsCA at h_eps
    -- `iSup_le_iff` turns `⨆ u, body u ≤ ε` into `∀ u, body u ≤ ε`,
    -- then we specialize at this `u`.
    have h_term_le := iSup_le_iff.mp h_eps u
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [jointAgreement_iff_jointProximity]; exact hjp
    · rw [if_neg hjp] at h_term_le
      exact absurd h_pr (not_lt.mpr h_term_le)

end

end ProximityGap
