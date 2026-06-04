/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.ProofSystem.ToyProblem.Definitions

/-!
# Toy problem soundness bounds (ABF26 §6)

Statement-layer for the §6 soundness bounds that do **not** depend on a
formal protocol object. The three protocol-level soundness lemmas
(`L6.6`, `L6.8`, `L6.10`) live alongside the protocol definitions in
`ToyProblem/Spec/General.lean` (C6.2) and
`ToyProblem/Spec/SimplifiedIOR.lean` (C6.9).

Items in this file:

* `ToyProblem.additive_code_supports_erasure_correction_grs25`
   — Lemma 6.5 [GRS25]: every additive code supports erasure correction
   with correction time `O((s · n)^3)`.

* `ToyProblem.simplified_iop_soundness_listDecoding_lb`
   — Lemma 6.12 [ABF26]: list-decoding-based lower bound on the
   soundness error of the simplified IOR `T'[C, t]` (Construction 6.9).
   Uses Claim B.1 via `Probability.exists_large_image_of_pairwise_collision_bound`.

* `ToyProblem.simplified_iop_soundness_ca_lb`
   — Lemma 6.13 [ABF26]: correlated-agreement-based lower bound on the
   soundness error of `T'[C, t]`.

All three are tagged sorries, but of two distinct kinds:

* **L6.5** is `external admit [GRS25]` — a classical result imported from
  another work; admitting it is acceptable for a survey formalization.
* **L6.12 and L6.13** are `paper-proof-owed` — ABF26's OWN results, proved
  in full in §6.4.1/§6.4.2. They are **in-tree provable now** (L6.12's key
  lemma Claim B.1 is already closed); the sorries are unfinished work, not
  external dependencies. They are stated in coding-theory form (direct
  cardinality bounds on `winningSet`); their protocol-level reading bounds
  the soundness of `ToyProblem.SimplifiedIOR.reduction` from below.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26]
* [Guruswami, V., Rudra, A., Sudan, M., *Essential Coding Theory*][GRS25]
-/

namespace ToyProblem

open Code InterleavedCode ListDecodable ProximityGap
open scoped NNReal ENNReal ProbabilityTheory

variable {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
/-- **Lemma 6.5 of [ABF26]** (= [GRS25]).

Every `F`-additive code `C : F^k → (F^s)^n` supports erasure correction
(in the sense of `CodingTheory.SupportsErasureCorrection`) with correction
time `O((s · n)^3)`. Equivalently: the predicate
`CodingTheory.SupportsErasureCorrection C ecor` holds for some
`ecor ≤ K · (s · n)^3`. We state the more permissive
"some `ecor` works" form here; pinning down the constant `K` requires
modelling the encoder concretely.

Admitted as an external result. -/
theorem additive_code_supports_erasure_correction_grs25
    (C : Set (ι → F)) :
    ∃ ecor : ℕ, CodingTheory.SupportsErasureCorrection C ecor := by
  -- ABF26-L6.5; external admit [GRS25]. Polynomial-time erasure-correction
  -- algorithm via Gaussian elimination on the parity-check matrix of any
  -- additive code (cf. Guruswami-Rudra-Sudan, *Essential Coding Theory*).
  sorry

omit [DecidableEq F] in
/-- **Lemma 6.12 of [ABF26]** (list-decoding lower bound on the simplified IOR).

Coding-theory form: if `C` is a linear code (the image of an `F`-linear
encoding of message dimension `k`) and `|Λ(C^{≡2}, δ)| < |F|`,
then there exist witnesses `(v, μ_1, μ_2, f_1, f_2)` with `(f_1, f_2)` lying
**outside** the relaxed relation `R̃_{C,δ}^2` (the `violates` conjunct), for
which the winning challenge set `Ω^{f_1,f_2}_{v,μ_1,μ_2}` (Definition 6.11)
has at least `|Λ(C^{≡2}, δ)| · |F| / (|F| + 2·|Λ(C^{≡2}, δ)|)` elements.

The protocol-level reading: the soundness error of the simplified IOR
`T'[C, t]` (Construction 6.9, `ToyProblem.SimplifiedIOR.reduction`) is
at least `|Λ(C^{≡2}, δ)| / (|F| + 2·|Λ(C^{≡2}, δ)|)`.

## Statement provenance (corrected 2026-06-04, finding S5)

Writing `N := |Λ(C^{≡2}, δ)|`, `F := |F|`, the **final** soundness bound in
ABF26 §6.4.1 (canonical `.tex` `lemma:list-decoding-attack`, lines 2655–2719)
is `N / (F + 2N)`, hence the winning-set cardinality bound `N · F / (F + 2N)`.
The earlier in-tree denominator `F + N − 1` was the *intermediate* `|S_v|`
bound from the **first** Claim-B.1 application (paper step 3); the winning set
is bounded only after a **second** B.1 application (step 4) by
`F · |S_v| / (F + |S_v| − 1)`, which the paper then chains down (via the
increasing map `z ↦ z/(F + z − 1)` and `(F−1)² + (2F−1)N ≤ F² + 2FN`) to the
final `N/(F + 2N)`. The old `N · F / (F + N − 1)` therefore *overshot* the
provable bound. The corrected `N · F / (F + 2N)` matches the `.tex`.

## Proof recipe (ABF26 §6.4.1, with B.1 now machine-checked)

The intermediate `|S_v| ≥ N · F / (F + N − 1)` is exactly the conclusion of
Claim B.1 specialised to `|S| = N`, `|T| = F`, `ε = 1/F`:
`N / (1 + (N − 1) · (1/F)) = N · F / (F + N − 1)`, so the proof skeleton is:

1. **Build the list.** Enumerate `Λ(C^{≡2}, δ)` as pairs `(W₀(λ), W₁(λ))` of
   `δ`-close codewords in `C` (paper `(v_0(λ), v_1(λ))`). Pick `v ∈ F^k` and
   define `φ_v : λ ↦ (⟨W₀(λ), v⟩, ⟨W₁(λ), v⟩)`.

2. **Pairwise collision bound.** For distinct list entries the linear
   functional `⟨·, v⟩` collides with probability `≤ 1/F` over `v ←$ F^k`.

3. **Apply B.1 (first time).** Obtain `v*` with `|S_{v*}| ≥ N·F/(F+N−1)`.

4. **Apply B.1 (second time) + violation.** Pick `μ₂` not a second coordinate
   in `S_{v*}` and (by a second B.1 on the affine map `(a₁,a₂) ↦
   (μ₁−a₁)/(a₂−μ₂)`) a `μ₁` giving a winning set of size
   `≥ F·|S_{v*}|/(F+|S_{v*}|−1)`. Since `(μ₁,μ₂) ∉ S_{v*}`, the instance
   violates `R̃_{C,δ}^2` (the `violates` conjunct). Chasing the algebra gives
   the final `N·F/(F+2N)`.

Tagged sorry (`paper-proof-owed` — ABF26's OWN result, proved in §6.4.1);
steps 2-3 are in scope thanks to B.1's closure (2026-05-20). -/
theorem simplified_iop_soundness_listDecoding_lb {k : ℕ}
    [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ≥0) (_hδ_pos : (0 : ℝ≥0) < δ) (_hδ_lt : δ < 1)
    (_hClin : ∃ enc : (Fin k → F) →ₗ[F] (ι → F), Set.range enc = C)
    (_hF : ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ)
      < Fintype.card F) :
    ∃ (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → F),
      ¬ relaxedRelation (ℓ := 2) C δ v ![μ₁, μ₂] ![f₁, f₂] ∧
      ((winningSet C δ v μ₁ μ₂ f₁ f₂).ncard : ℝ) ≥
        (((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ)
            * Fintype.card F)
          / (Fintype.card F
              + 2 * ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ)) := by
  -- ABF26-L6.12; paper-proof-owed [ABF26 §6.4.1]. Paper's OWN result with a
  -- full elementary proof; IN-TREE PROVABLE NOW — its key lemma Claim B.1
  -- (`Probability.exists_large_image_of_pairwise_collision_bound`) is already
  -- closed. Follow §6.4.1: build the collision map `φ_v` and apply B.1 twice.
  sorry

omit [Fintype F] in
/-- **Membership helper for the §6.4 attacks.** If `C` is a linear code (the
range of an `F`-linear encoding `enc` of message dimension `k`) and the line
`f₁ + γ·f₂` is `δ`-close to `C`, then `γ` is a winning challenge for the
all-zero instance `(v, μ₁, μ₂) = (0, 0, 0)` (Definition 6.11). This is the
inclusion `S ⊆ Ω^{f₁,f₂}_{0,0,0}` from the proof of **Lemma 6.13 of [ABF26]**
(§6.4.2), generalised to any line. -/
theorem mem_winningSet_zero_of_relClose {k : ℕ} [Nonempty ι] {C : Set (ι → F)}
    {δ : ℝ≥0} (_hδ_lt : δ < 1)
    (enc : (Fin k → F) →ₗ[F] (ι → F)) (hC : Set.range enc = C)
    (f₁ f₂ : ι → F) {γ : F} (hγ : δᵣ(f₁ + γ • f₂, C) ≤ δ) :
    γ ∈ winningSet C δ (0 : Fin k → F) 0 0 f₁ f₂ := by
  classical
  rw [winningSet, Set.mem_setOf_eq]
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist] at hγ
  obtain ⟨w, hwC, hwd⟩ := hγ
  obtain ⟨m, hm⟩ : ∃ m, enc m = w := by rw [← hC] at hwC; exact hwC
  refine ⟨fun _ ↦ w, ⟨fun _ ↦ m, ⟨enc, fun m' ↦ hC ▸ ⟨m', rfl⟩, fun i ↦ by simp [hm]⟩,
      fun i ↦ by simp⟩, ?_⟩
  rw [relCloseToWord_iff_exists_agreementCols] at hwd
  obtain ⟨S, hScard, hSagree⟩ := hwd
  refine ⟨S, ?_, ?_⟩
  · -- `(1 - δ)·|ι| ≤ |S|` in ℝ, from the `|ι| - ⌊δ|ι|⌋ ≤ |S|` agreement bound.
    have h2 := (relDist_floor_bound_iff_complement_bound (Fintype.card ι) S.card δ).mp hScard
    have e : ((1 - δ : ℝ≥0) : ℝ) = 1 - (δ : ℝ) := by rw [NNReal.coe_sub _hδ_lt.le]; simp
    have := (NNReal.coe_le_coe.mpr h2)
    rw [NNReal.coe_mul, e] at this
    push_cast at this ⊢
    linarith [this]
  · intro i j hj
    have hag := (hSagree j).1 hj
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hag

/-- **Lemma 6.13 of [ABF26]** (correlated-agreement lower bound on the simplified IOR).

Coding-theory form: if `C` is a linear code (range of an `F`-linear encoding
`enc` of message dimension `k`) and the correlated-agreement error is positive,
then there exist `(v, μ_1, μ_2, f_1, f_2)` with `(f_1, f_2)` lying **outside**
the relaxed relation `R̃_{C,δ}^2` (the `violates` conjunct) whose winning
challenge set has size at least `ε_ca(C, δ) · |F|`.

Protocol-level reading: the soundness error of the simplified IOR
`T'[C, t]` (Construction 6.9) is at least `ε_ca(C, δ)`.

Proof (ABF26 §6.4.2, now machine-checked): the CA error is a supremum over a
finite type of word-stacks, hence attained at some `u = (f_1, f_2)`; since the
error is positive, `u` is *not* jointly `δ`-close to `C^{≡2}` — this is exactly
the violation `¬ R̃_{C,δ}^2` (via `jointAgreement_iff_jointProximity`). Its
value is then `Pr_γ[Δ(f_1 + γ·f_2, C) ≤ δ] = |S|/|F|` with `S = {γ : Δ(f_1 +
γ·f_2, C) ≤ δ}`, and `S ⊆ Ω^{f_1,f_2}_{0,0,0}` (`mem_winningSet_zero_of_relClose`).
The `0 < ε_ca` hypothesis matches the paper's "if not, the statement holds
vacuously". The bound is in terms of `ε_ca` (correlated agreement) rather than
`ε_mca`; the latter would be qualitatively stronger but no attack reaching
`ε_mca > ε_ca` is currently known (Remark 6.14). -/
theorem simplified_iop_soundness_ca_lb {k : ℕ} [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ≥0) (_hδ_pos : (0 : ℝ≥0) < δ) (_hδ_lt : δ < 1)
    (hClin : ∃ enc : (Fin k → F) →ₗ[F] (ι → F), Set.range enc = C)
    (hca : 0 < epsCA (F := F) (A := F) C δ δ) :
    ∃ (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → F),
      ¬ relaxedRelation (ℓ := 2) C δ v ![μ₁, μ₂] ![f₁, f₂] ∧
      ((winningSet (k := k) C δ v μ₁ μ₂ f₁ f₂).ncard : ENNReal)
        ≥ epsCA (F := F) (A := F) C δ δ * (Fintype.card F : ENNReal) := by
  classical
  obtain ⟨enc, hC⟩ := hClin
  -- The CA error is attained at some word-stack `u` (finite supremum).
  obtain ⟨u, hu_max⟩ := Finite.exists_max
    (fun u : WordStack F (Fin 2) ι ↦
      if jointProximity C u δ then (0 : ENNReal)
      else Pr_{ let γ ← $ᵖ F }[δᵣ(u 0 + γ • u 1, C) ≤ δ])
  have h_eps : epsCA (F := F) (A := F) C δ δ =
      (if jointProximity C u δ then (0 : ENNReal)
       else Pr_{ let γ ← $ᵖ F }[δᵣ(u 0 + γ • u 1, C) ≤ δ]) := by
    refine le_antisymm ?_ ?_
    · rw [epsCA]; exact iSup_le hu_max
    · rw [epsCA]
      exact le_iSup (fun w : WordStack F (Fin 2) ι ↦
        if jointProximity C w δ then (0 : ENNReal)
        else Pr_{ let γ ← $ᵖ F }[δᵣ(w 0 + γ • w 1, C) ≤ δ]) u
  -- Positivity forces the maximiser to be *not* jointly close.
  have hjp : ¬ jointProximity C u δ := by
    intro h; rw [h_eps, if_pos h] at hca; exact lt_irrefl _ hca
  rw [if_neg hjp] at h_eps
  refine ⟨0, 0, 0, u 0, u 1, ?_, ?_⟩
  · -- Violation: `¬ R̃²`. Else relaxedRelation → jointAgreement → jointProximity.
    intro hrel
    apply hjp
    have hu_eq : u = ![u 0, u 1] := by funext i; fin_cases i <;> rfl
    rw [hu_eq, ← jointAgreement_iff_jointProximity]
    obtain ⟨Wstar, ⟨M, ⟨encode, hencC, hWstar⟩, _hconstr⟩, S, hScard, hSag⟩ := hrel
    refine ⟨S, ?_, Wstar, fun i ↦ ⟨hWstar i ▸ hencC (M i), ?_⟩⟩
    · -- card bound ℝ → ℝ≥0
      have e : ((1 - δ : ℝ≥0) : ℝ) = 1 - (δ : ℝ) := by rw [NNReal.coe_sub _hδ_lt.le]; simp
      rw [ge_iff_le, ← NNReal.coe_le_coe, NNReal.coe_mul, e]
      push_cast
      linarith [hScard]
    · intro j hj
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ j, (hSag i j hj).symm⟩
  · -- Cardinality bound: `S ⊆ Ω`, and `Pr·|F| = |S|`.
    rw [h_eps]
    have hsub : {γ : F | δᵣ(u 0 + γ • u 1, C) ≤ δ} ⊆ winningSet C δ 0 0 0 (u 0) (u 1) :=
      fun γ hγ ↦ mem_winningSet_zero_of_relClose _hδ_lt enc hC (u 0) (u 1) hγ
    have hF0 : (Fintype.card F : ℝ≥0) ≠ 0 := by
      simp [Fintype.card_ne_zero]
    have key : Pr_{ let γ ← $ᵖ F }[δᵣ(u 0 + γ • u 1, C) ≤ δ] * (Fintype.card F : ENNReal)
        = ({γ : F | δᵣ(u 0 + γ • u 1, C) ≤ δ}.ncard : ENNReal) := by
      rw [prob_uniform_eq_card_filter_div_card,
          Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
      push_cast
      rw [ENNReal.div_mul_cancel (by exact_mod_cast hF0) (ENNReal.natCast_ne_top _)]
    rw [key]
    have hmono := Set.ncard_le_ncard hsub (Set.toFinite _)
    exact_mod_cast hmono

end ToyProblem
