/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.Probability.Combinatorial
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
  in full in §6.4.1/§6.4.2. They are stated in coding-theory form (direct
  cardinality bounds on `winningSet`); their protocol-level reading bounds
  the soundness of `ToyProblem.SimplifiedIOR.reduction` from below.

**L6.12 status (Phase 4, 2026-06-04).** The proof is decomposed and its full
logical skeleton compiles; all the probability/algebra infrastructure is proven
and axiom-clean (`exists_dotProduct_image_lb` and `exists_affine_image_lb` —
the two Claim-B.1 applications; `claimB1_bound_to_real`; `listDecoding_winning_lb`;
`mem_winningSet_of_agree`; `affine_collision_card_le_one`; plus
`Pr_map_eq` / `prob_dotProduct_eq_zero_le` / `prob_uniform_le_inv_of_card_le_one`
in `Data/Probability/Instances.lean`). Three coding-theory obligations remain:
two are *provable-and-owed* (`hSmsgN`, the enc-injective codeword↔message
bijection; `hmem`, winning-set membership). The third — the **violation
conjunct** — surfaced a **faithfulness finding**: under ArkLib's
*existential-encoding* `relation` (Definitions.lean), `¬ relaxedRelation (ℓ:=2)`
is not just unproven but *false* for this attack's parameters (an adversary can
reparameterise the linear constraint through a different linear encoding). The
paper's `R²_C` fixes the code's encoding, under which the violation is exactly
`(μ₁,μ₂) ∉ S_v` and holds. The faithful fix is to parameterise
`relation`/`relaxedRelation` by the encoding; see the in-proof note at the
violation conjunct. The quantitative winning-set bound is unaffected.

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

omit [Fintype ι] [Fintype F] [DecidableEq F] in
/-- **ENNReal → ℝ bridge for the Claim-B.1 output.** Rewrites Claim B.1's image
bound `M / (1 + (M−1)·|F|⁻¹) ≤ s` into the real-arithmetic form
`M·c/(c+M−1) ≤ s` consumed by `listDecoding_winning_lb` (here `c = |F|`). -/
private lemma claimB1_bound_to_real {M s c : ℕ} (hc : 1 ≤ c) (hM : 1 ≤ M)
    (h : (M : ENNReal) / (1 + ((M : ENNReal) - 1) * (c : ENNReal)⁻¹) ≤ (s : ENNReal)) :
    (M : ℝ) * c / (c + M - 1) ≤ s := by
  have hc0 : (c : ENNReal) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hc
  have hct : (c : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcc : (c : ENNReal)⁻¹ * c = 1 := ENNReal.inv_mul_cancel hc0 hct
  have hMc : (M : ENNReal) - 1 = ((M - 1 : ℕ) : ENNReal) := by
    have hMe : (M : ENNReal) = ((M - 1 : ℕ) : ENNReal) + 1 := by
      rw [← Nat.cast_add_one, Nat.sub_add_cancel hM]
    rw [hMe, ENNReal.add_sub_cancel_right ENNReal.one_ne_top]
  set D : ENNReal := 1 + ((M : ENNReal) - 1) * (c : ENNReal)⁻¹ with hD
  have hD0 : D ≠ 0 := by
    rw [hD]; exact (add_pos_of_pos_of_nonneg one_pos (zero_le _)).ne'
  have hDt : D ≠ ⊤ := by
    rw [hD, hMc]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top,
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.inv_ne_top.mpr hc0)⟩
  -- `M ≤ s · D`, then multiply through by `c`.
  have hle : (M : ENNReal) ≤ (s : ENNReal) * D := by
    have hmul := mul_le_mul_right' h D
    rwa [ENNReal.div_mul_cancel hD0 hDt] at hmul
  have hDc : D * (c : ENNReal) = (c : ENNReal) + ((M - 1 : ℕ) : ENNReal) := by
    rw [hD, hMc, add_mul, one_mul, mul_assoc, hcc, mul_one]
  have hsum : (c : ENNReal) + ((M - 1 : ℕ) : ENNReal) = ((c + M - 1 : ℕ) : ENNReal) := by
    rw [← Nat.cast_add]; congr 1; omega
  have hkey : ((M * c : ℕ) : ENNReal) ≤ ((s * (c + M - 1) : ℕ) : ENNReal) := by
    calc ((M * c : ℕ) : ENNReal) = (M : ENNReal) * c := by push_cast; ring
      _ ≤ (s : ENNReal) * D * c := by gcongr
      _ = (s : ENNReal) * (D * c) := by ring
      _ = (s : ENNReal) * ((c + M - 1 : ℕ) : ENNReal) := by rw [hDc, hsum]
      _ = ((s * (c + M - 1) : ℕ) : ENNReal) := by push_cast; ring
  have hnat : M * c ≤ s * (c + M - 1) := by exact_mod_cast hkey
  have hcM : ((c + M - 1 : ℕ) : ℝ) = (c : ℝ) + M - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ c + M)]; push_cast; ring
  have hpos : (0 : ℝ) < (c : ℝ) + M - 1 := by
    have h1 : (1 : ℝ) ≤ ((c + M - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ c + M - 1)
    rw [hcM] at h1; linarith
  rw [div_le_iff₀ hpos]
  have hnat' : (M : ℝ) * c ≤ s * ((c : ℝ) + M - 1) := by
    rw [← hcM]; exact_mod_cast hnat
  linarith [hnat']

/-- **Stacked-codeword matrix.** The interleaved word whose two columns are the
codewords `enc m.1` and `enc m.2`; used to enumerate `Λ(C^{≡2}, δ, (f₁,f₂))` by
message pairs in the proof of ABF26 Lemma 6.12. -/
private def encStack {k : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → F))
    (m : (Fin k → F) × (Fin k → F)) : Matrix ι (Fin 2) F :=
  Matrix.of (fun i j ↦ if j = 0 then enc m.1 i else enc m.2 i)

open Probability in
/-- **First Claim-B.1 application (abstract inner-product form).** For an
injective family `a : σ → (F^k)²` of message pairs, there is a constraint vector
`v` under which the collision map `s ↦ (⟨a(s)₁, v⟩, ⟨a(s)₂, v⟩)` has image of
size at least `|σ| / (1 + (|σ|−1)/|F|)` (= `|σ|·|F|/(|F|+|σ|−1)`).

This is the first of the two `exists_large_image_of_pairwise_collision_bound`
(Claim B.1) applications in ABF26 §6.4.1, stripped of all coding theory: the
pairwise-collision bound is exactly `prob_dotProduct_eq_zero_le` (a nonzero
linear form vanishes with probability `≤ 1/|F|`), pulled back through the
pushforward identity `Pr_map_eq`. -/
private lemma exists_dotProduct_image_lb {k : ℕ} {σ : Type} [Fintype σ]
    (a : σ → (Fin k → F) × (Fin k → F)) (ha : Function.Injective a) :
    ∃ v : Fin k → F,
      (Fintype.card σ : ENNReal) / (1 + (Fintype.card σ - 1) * (Fintype.card F : ENNReal)⁻¹)
        ≤ ((Finset.univ.image
            (fun s : σ ↦ ((∑ j, (a s).1 j * v j), (∑ j, (a s).2 j * v j)))).card : ENNReal) := by
  classical
  set g : (Fin k → F) → (σ → F × F) :=
    fun v s ↦ ((∑ j, (a s).1 j * v j), (∑ j, (a s).2 j * v j)) with hg
  set Φ : PMF (σ → F × F) := (PMF.uniformOfFintype (Fin k → F)).map g with hΦ
  have hcoll : ∀ x y : σ, x ≠ y →
      Pr_{ let φ ← Φ }[(decide (φ x = φ y) : Prop)] ≤ (Fintype.card F : ENNReal)⁻¹ := by
    intro x y hxy
    rw [hΦ, Pr_map_eq]
    have hne : a x ≠ a y := fun h ↦ hxy (ha h)
    by_cases h1 : (a x).1 = (a y).1
    · have h2 : (a x).2 ≠ (a y).2 := fun h ↦ hne (Prod.ext h1 h)
      refine le_trans (Pr_le_Pr_of_implies _ _
        (fun v ↦ (∑ j, ((a x).2 - (a y).2) j * v j = 0)) ?_)
        (prob_dotProduct_eq_zero_le ((a x).2 - (a y).2) (sub_ne_zero.mpr h2))
      intro v hv
      have hv' : g v x = g v y := by simpa using hv
      have : (∑ j, (a x).2 j * v j) = (∑ j, (a y).2 j * v j) := (Prod.ext_iff.mp hv').2
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, this, sub_self]
    · refine le_trans (Pr_le_Pr_of_implies _ _
        (fun v ↦ (∑ j, ((a x).1 - (a y).1) j * v j = 0)) ?_)
        (prob_dotProduct_eq_zero_le ((a x).1 - (a y).1) (sub_ne_zero.mpr h1))
      intro v hv
      have hv' : g v x = g v y := by simpa using hv
      have : (∑ j, (a x).1 j * v j) = (∑ j, (a y).1 j * v j) := (Prod.ext_iff.mp hv').1
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, this, sub_self]
  obtain ⟨φ, hφ_supp, hφ_card⟩ :=
    exists_large_image_of_pairwise_collision_bound Φ (Fintype.card F : ENNReal)⁻¹ hcoll
  rw [hΦ, PMF.mem_support_map_iff] at hφ_supp
  obtain ⟨v, _, hv⟩ := hφ_supp
  refine ⟨v, ?_⟩
  have hgv : (fun s : σ ↦ ((∑ j, (a s).1 j * v j), (∑ j, (a s).2 j * v j))) = g v := rfl
  rw [hgv, hv]
  exact hφ_card

omit [Fintype ι] in
/-- **Affine collision has at most one solution (ABF26 §6.4.1, second B.1).**
For distinct points `(a₁,a₂) ≠ (b₁,b₂)` with `a₂, b₂ ≠ μ₂`, the equation
`(μ₁−a₁)/(a₂−μ₂) = (μ₁−b₁)/(b₂−μ₂)` has at most one solution `μ₁`: if `a₂ ≠ b₂`
it is affine in `μ₁`; if `a₂ = b₂` it is unsatisfiable. -/
private lemma affine_collision_card_le_one {a₁ a₂ b₁ b₂ μ₂ : F}
    (ha : a₂ ≠ μ₂) (hb : b₂ ≠ μ₂) (hpq : (a₁, a₂) ≠ (b₁, b₂)) :
    (Finset.univ.filter
      (fun μ₁ : F ↦ (μ₁ - a₁) / (a₂ - μ₂) = (μ₁ - b₁) / (b₂ - μ₂))).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  rw [div_eq_div_iff (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb)] at hx hy
  have key : (x - y) * (b₂ - a₂) = 0 := by linear_combination hx - hy
  rcases mul_eq_zero.mp key with hxy | hba
  · exact sub_eq_zero.mp hxy
  · exfalso
    have hab : a₂ = b₂ := (sub_eq_zero.mp hba).symm
    apply hpq
    subst hab
    have hx' : (x - a₁) = (x - b₁) := mul_right_cancel₀ (sub_ne_zero.mpr ha) hx
    have : a₁ = b₁ := sub_right_injective hx'
    rw [this]

open Probability in
/-- **Second Claim-B.1 application (abstract affine form).** For a set `T ⊆ F×F`
with `|T| < |F|`, there is a value `μ₂` avoiding every second coordinate of `T`
and a `μ₁` under which the affine map `(a,b) ↦ (μ₁−a)/(b−μ₂)` has image of size
at least `|T| / (1 + (|T|−1)/|F|)` (= `|F|·|T|/(|F|+|T|−1)`).

This is the second `exists_large_image_of_pairwise_collision_bound` (Claim B.1)
application in ABF26 §6.4.1: the per-point collision bound is `≤ 1/|F|` because
the affine equation has `≤ 1` solution (`affine_collision_card_le_one`). The
`∀ p ∈ T, p.2 ≠ μ₂` clause also forces `(μ₁,μ₂) ∉ T` (the violation step). -/
private lemma exists_affine_image_lb (T : Finset (F × F))
    (hTcard : T.card < Fintype.card F) :
    ∃ (μ₁ μ₂ : F), (∀ p ∈ T, p.2 ≠ μ₂) ∧
      (T.card : ENNReal) / (1 + (T.card - 1) * (Fintype.card F : ENNReal)⁻¹)
        ≤ ((T.image (fun p ↦ (μ₁ - p.1) / (p.2 - μ₂))).card : ENNReal) := by
  classical
  obtain ⟨μ₂, hμ₂⟩ : ∃ μ₂ : F, μ₂ ∉ T.image Prod.snd := by
    by_contra h
    push_neg at h
    have heq : T.image Prod.snd = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    have h2 : Fintype.card F ≤ T.card := by
      rw [← Finset.card_univ (α := F), ← heq]; exact Finset.card_image_le
    exact absurd h2 (not_le.mpr hTcard)
  have hμ₂' : ∀ p ∈ T, p.2 ≠ μ₂ := fun p hp h ↦ hμ₂ (h ▸ Finset.mem_image_of_mem Prod.snd hp)
  set g' : F → (↥T → F) := fun μ₁ p ↦ (μ₁ - (p : F × F).1) / ((p : F × F).2 - μ₂) with hg'
  set Φ' : PMF (↥T → F) := (PMF.uniformOfFintype F).map g' with hΦ'
  have hcoll : ∀ x y : ↥T, x ≠ y →
      Pr_{ let φ ← Φ' }[(decide (φ x = φ y) : Prop)] ≤ (Fintype.card F : ENNReal)⁻¹ := by
    intro x y hxy
    rw [hΦ', Pr_map_eq]
    have hxy' : (x : F × F) ≠ (y : F × F) := fun h ↦ hxy (Subtype.ext h)
    have hpq : ((x : F × F).1, (x : F × F).2) ≠ ((y : F × F).1, (y : F × F).2) := by
      simpa using hxy'
    simp only [hg', decide_eq_true_eq]
    exact prob_uniform_le_inv_of_card_le_one _
      (affine_collision_card_le_one (hμ₂' x x.2) (hμ₂' y y.2) hpq)
  obtain ⟨φ, hφ_supp, hφ_card⟩ :=
    exists_large_image_of_pairwise_collision_bound Φ' (Fintype.card F : ENNReal)⁻¹ hcoll
  rw [hΦ', PMF.mem_support_map_iff] at hφ_supp
  obtain ⟨μ₁, _, hμ₁⟩ := hφ_supp
  refine ⟨μ₁, μ₂, hμ₂', ?_⟩
  -- relate `Finset.univ.image (g' μ₁)` to `T.image (fun p ↦ (μ₁ - p.1)/(p.2 - μ₂))`
  have hset : Finset.univ.image φ = T.image (fun p ↦ (μ₁ - p.1) / (p.2 - μ₂)) := by
    rw [← hμ₁]
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists, hg']
    constructor <;> rintro ⟨a, ha, rfl⟩ <;> exact ⟨a, ha, rfl⟩
  have hcardT : (Fintype.card ↥T) = T.card := Fintype.card_coe T
  rw [hset, hcardT] at hφ_card
  exact hφ_card

omit [Fintype F] [DecidableEq F] in
/-- **General winning-set membership (agreement form).** Generalises
`mem_winningSet_zero_of_relClose` to arbitrary instance data `(v, μ₁, μ₂)`.

If `f₁ + γ·f₂` agrees with the codeword `enc m` on a column set `S` covering at
least a `(1 - δ)`-fraction of `ι`, and the message `m` satisfies the linear
constraint `⟨m, v⟩ = μ₁ + γ·μ₂`, then `γ` is a winning challenge for the
instance `(v, μ₁, μ₂, f₁, f₂)` (Definition 6.11 of [ABF26]). This is the
membership step of the §6.4.1 list-decoding attack (paper: "every
`γ = (μ₁−a₁)/(a₂−μ₂)` belongs to `Ω`"). -/
theorem mem_winningSet_of_agree {k : ℕ} {C : Set (ι → F)} {δ : ℝ≥0}
    (enc : (Fin k → F) →ₗ[F] (ι → F)) (hC : Set.range enc = C)
    {v : Fin k → F} {μ₁ μ₂ : F} {f₁ f₂ : ι → F} {γ : F} {m : Fin k → F}
    (hconstr : ∑ j, m j * v j = μ₁ + γ * μ₂)
    (S : Finset ι) (hScard : (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card)
    (hagree : ∀ j ∈ S, f₁ j + γ * f₂ j = enc m j) :
    γ ∈ winningSet C δ v μ₁ μ₂ f₁ f₂ := by
  rw [winningSet, Set.mem_setOf_eq]
  exact ⟨fun _ ↦ enc m,
    ⟨fun _ ↦ m, ⟨enc, fun m' ↦ hC ▸ Set.mem_range_self m', fun _ ↦ rfl⟩, fun _ ↦ hconstr⟩,
    S, hScard, fun _ j hj ↦ hagree j hj⟩

/-- **Real-arithmetic chain closing ABF26 §6.4.1.** From the first Claim-B.1
lower bound `N·|F|/(|F|+N−1) ≤ s` (here `s = |S_v|`), the second Claim-B.1
application's winning fraction `|F|·s/(|F|+s−1)` is at least the final bound
`N·|F|/(|F|+2N)`.

The paper argues via the increasing map `z ↦ z/(|F|+z−1)` and the inequality
`(|F|−1)²+(2|F|−1)N ≤ |F|²+2|F|N`; after clearing denominators the whole chain
collapses to `N·(|F|−1) ≤ s·(|F|+N)`, which follows from `N·|F| ≤ s·(|F|+N−1)`
and `s ≥ 0`. -/
lemma listDecoding_winning_lb {Fc N s : ℝ} (hF : (1 : ℝ) ≤ Fc) (hN : (1 : ℝ) ≤ N)
    (hslb : N * Fc / (Fc + N - 1) ≤ s) :
    N * Fc / (Fc + 2 * N) ≤ Fc * s / (Fc + s - 1) := by
  have hFN1 : (0 : ℝ) < Fc + N - 1 := by linarith
  have hslb' : N * Fc ≤ s * (Fc + N - 1) := by rwa [div_le_iff₀ hFN1] at hslb
  have hs1 : (1 : ℝ) ≤ s := by
    refine le_trans ?_ hslb
    rw [le_div_iff₀ hFN1]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ N - 1) (by linarith : (0 : ℝ) ≤ Fc - 1)]
  have hFs1 : (0 : ℝ) < Fc + s - 1 := by linarith
  have hF2N : (0 : ℝ) < Fc + 2 * N := by linarith
  rw [div_le_div_iff₀ hF2N hFs1]
  nlinarith [mul_le_mul_of_nonneg_left hslb' (by linarith : (0 : ℝ) ≤ Fc), hs1, hN, hF,
    mul_nonneg (by linarith : (0:ℝ) ≤ s) (by linarith : (0:ℝ) ≤ N)]

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

The encoding hypothesis is `∃ enc, Function.Injective enc ∧ range enc = C` — the
faithful "linear code of dimension `k`" assumption (an injective `F`-linear
encoding onto `C`), which is what makes `Λ(C^{≡2}, δ)` enumerable by *message*
pairs `F^k × F^k` (the inner products `⟨·, v⟩` of paper step 1 live on messages).
This strengthens L6.13's `range enc = C` and matches the linear `encode` field of
`ToyProblem.relation`.

The proof decomposes into reusable, separately-verified pieces:
`exists_dotProduct_image_lb` (first B.1, inner-product collision via
`prob_dotProduct_eq_zero_le`), `exists_affine_image_lb` (second B.1, affine
collision via `affine_collision_card_le_one`), `claimB1_bound_to_real` (the
ENNReal→ℝ bridge), `listDecoding_winning_lb` (the `z ↦ z/(F+z−1)` denominator
chain), and `mem_winningSet_of_agree` (the membership step). -/
theorem simplified_iop_soundness_listDecoding_lb {k : ℕ}
    [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ≥0) (_hδ_pos : (0 : ℝ≥0) < δ) (_hδ_lt : δ < 1)
    (hClin : ∃ enc : (Fin k → F) →ₗ[F] (ι → F), Function.Injective enc ∧ Set.range enc = C)
    (hF : ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ)
      < Fintype.card F) :
    ∃ (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → F),
      ¬ relaxedRelation (ℓ := 2) C δ v ![μ₁, μ₂] ![f₁, f₂] ∧
      ((winningSet C δ v μ₁ μ₂ f₁ f₂).ncard : ℝ) ≥
        (((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ)
            * Fintype.card F)
          / (Fintype.card F
              + 2 * ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ)) := by
  classical
  obtain ⟨enc, hinj, hC⟩ := hClin
  set Cint : Set (Matrix ι (Fin 2) F) := interleavedCodeSet (κ := Fin 2) C with hCint
  -- Maximising matrix `fStar` for the list size (finite supremum, as in L6.13).
  obtain ⟨fStar, hfStar⟩ := Finite.exists_max
    (fun f : ι → Fin 2 → F ↦ (closeCodewordsRel Cint f (δ : ℝ)).ncard)
  set N : ℕ := (Lambda Cint (δ : ℝ)).toNat with hNdef
  have hNeq : N = (closeCodewordsRel Cint fStar (δ : ℝ)).ncard := by
    rw [hNdef, Lambda,
      show (⨆ f : ι → Fin 2 → F, ((closeCodewordsRel Cint f (δ : ℝ)).ncard : ℕ∞))
          = ((closeCodewordsRel Cint fStar (δ : ℝ)).ncard : ℕ∞) from
        le_antisymm (iSup_le fun f ↦ by exact_mod_cast hfStar f)
          (le_iSup (fun f ↦ ((closeCodewordsRel Cint f (δ : ℝ)).ncard : ℕ∞)) fStar),
      ENat.toNat_coe]
  set f₁ : ι → F := fun i ↦ fStar i 0 with hf1
  set f₂ : ι → F := fun i ↦ fStar i 1 with hf2
  have hcardF1 : 1 ≤ Fintype.card F := Fintype.card_pos
  have hNltF : N < Fintype.card F := by exact_mod_cast hF
  -- Message-pair enumeration of `Λ(C^{≡2}, δ, (f₁,f₂))`.
  set Smsg : Finset ((Fin k → F) × (Fin k → F)) :=
    Finset.univ.filter (fun p ↦ encStack enc p ∈ closeCodewordsRel Cint fStar (δ : ℝ)) with hSmsg
  -- ENUMERATION (bijection codewords ↔ message pairs via the injective `enc`).
  have hSmsgN : Smsg.card = N := by
    -- ABF26-L6.12 enumeration: `encStack enc` is a bijection from the message
    -- pairs `Smsg` onto `closeCodewordsRel C^{≡2} fStar δ` (injective since `enc`
    -- is injective; surjective since every close codeword stack has both columns
    -- in `C = range enc`). Provable; mechanical `Finset.card_bij`.
    sorry -- ABF26-L6.12 enumeration: codeword↔message bijection (provable, owed)
  have hcardSmsg : Fintype.card ↥Smsg = N := by rw [Fintype.card_coe, hSmsgN]
  -- FIRST B.1: a constraint vector `v` with a large inner-product image `S_v`.
  obtain ⟨v, hv⟩ :=
    exists_dotProduct_image_lb (Subtype.val : ↥Smsg → (Fin k → F) × (Fin k → F))
      Subtype.coe_injective
  rw [hcardSmsg] at hv
  set Sv : Finset (F × F) := Finset.univ.image
    (fun s : ↥Smsg ↦ ((∑ j, (s : (Fin k → F) × (Fin k → F)).1 j * v j),
                       (∑ j, (s : (Fin k → F) × (Fin k → F)).2 j * v j))) with hSvdef
  -- `|S_v| ≤ N < |F|`.
  have hSvle : Sv.card ≤ N := by
    rw [← hcardSmsg, hSvdef]; exact le_trans Finset.card_image_le (le_of_eq (Finset.card_univ))
  have hSvltF : Sv.card < Fintype.card F := lt_of_le_of_lt hSvle hNltF
  -- SECOND B.1: pick `μ₂` off the second coordinates and a winning `μ₁`.
  obtain ⟨μ₁, μ₂, hμ₂off, hwin⟩ := exists_affine_image_lb Sv hSvltF
  set winImg : Finset F := Sv.image (fun p ↦ (μ₁ - p.1) / (p.2 - μ₂)) with hwinImg
  refine ⟨v, μ₁, μ₂, f₁, f₂, ?_, ?_⟩
  · -- VIOLATION CONJUNCT — ⚠ FAITHFULNESS FINDING (2026-06-04, Phase 4).
    --
    -- The paper's violation is `Δ((f₁,f₂), R²[x]) > δ` where `R²[x]` is the
    -- valid-witness set for the instance `x = (v, μ₁, μ₂)` under **the code's
    -- fixed encoding**. With a fixed encoding this is exactly `(μ₁,μ₂) ∉ S_v`
    -- (no δ-close codeword stack has the right inner products), which the
    -- `μ₂`-off-second-coordinates choice from the second B.1 step guarantees —
    -- PROVABLE.
    --
    -- But ArkLib's `relation` (Definitions.lean) quantifies the encoding
    -- **existentially** (`∃ encode, (∀ m, encode m ∈ C) ∧ …`), to also cover
    -- general `F`-additive codes. Under that existential, the violation conjunct
    -- `¬ relaxedRelation (ℓ:=2) …` is NOT provable here — in fact it is FALSE
    -- for the parameters this attack produces: given any δ-close codeword stack
    -- `(W₀,W₁)` (one exists, `N ≥ 1`) and the target `(μ₁,μ₂)`, an adversary
    -- picks messages `M₀,M₁` with `⟨Mᵢ,v⟩ = μᵢ` (solvable for `v ≠ 0`) and a
    -- linear `encode` with `encode Mᵢ = Wᵢ`, `image ⊆ C` (extend a basis,
    -- `span{W₀,W₁} ⊆ C`), satisfying `relation` — so `R̃²` HOLDS, no violation.
    -- (Contrast L6.13, whose violation comes from being δ-far from *every*
    -- codeword stack — encoding-independent, hence robust.)
    --
    -- FAITHFUL FIX (next session): parameterise `relation`/`relaxedRelation` by
    -- the encoding (`relationFor enc …`), keeping the existential `relation` as a
    -- wrapper; state this conjunct as `¬ relaxedRelationFor enc …`. Then it
    -- reduces to `(μ₁,μ₂) ∉ S_v`, which is proven by `hμ₂off`. See the module
    -- docstring and the Phase-5 bootstrap. The quantitative winning-set bound
    -- below is unaffected (the existential encoding only enlarges `winningSet`).
    -- ABF26-L6.12 violation: blocked on the fixed-encoding `relation` refactor
    -- (faithfulness finding documented above).
    sorry
  · -- CARDINALITY CHAIN.
    rcases Nat.eq_zero_or_pos N with hN0 | hN1
    · -- N = 0: the bound is `0 ≤ ncard`, trivially true.
      rw [hN0, ge_iff_le]; simp
    -- Main case N ≥ 1.
    -- MEMBERSHIP: every winning challenge in `winImg` lies in the winning set.
    have hmem : (winImg : Set F) ⊆ winningSet C δ v μ₁ μ₂ f₁ f₂ := by
      -- ABF26-L6.12 membership: each `γ = (μ₁−a)/(b−μ₂)` with `(a,b) = φ_v(m)`,
      -- `m ∈ Smsg`, is winning via `mem_winningSet_of_agree` (message `m.1+γ•m.2`,
      -- constraint `⟨m.1+γ·m.2, v⟩ = a+γb = μ₁+γμ₂`, agreement from `encStack`
      -- closeness + `enc`-linearity). Provable; uses the same agreement-cols
      -- reconciliation as `mem_winningSet_zero_of_relClose`.
      sorry -- ABF26-L6.12 membership: winImg ⊆ winningSet (provable, owed)
    -- A + bridge: `N·F/(F+N−1) ≤ |S_v|`.
    have hAreal : (N : ℝ) * Fintype.card F / (Fintype.card F + N - 1) ≤ (Sv.card : ℝ) :=
      claimB1_bound_to_real hcardF1 hN1 hv
    -- B + bridge: `|S_v|·F/(F+|S_v|−1) ≤ |winImg|`.
    have hSv1 : 1 ≤ Sv.card := by
      rcases Nat.eq_zero_or_pos Sv.card with h0 | h; swap; · exact h
      -- |S_v| = 0 would force the A-bound `N·F/(F+N−1) ≤ 0`, impossible for N ≥ 1.
      exfalso
      have hpos : (0 : ℝ) < (N : ℝ) * Fintype.card F / (Fintype.card F + N - 1) := by
        have : (0 : ℝ) < Fintype.card F + N - 1 := by
          have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
          have : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast hcardF1
          linarith
        positivity
      rw [h0] at hAreal; norm_num at hAreal; linarith
    have hBreal : (Sv.card : ℝ) * Fintype.card F / (Fintype.card F + Sv.card - 1)
        ≤ (winImg.card : ℝ) := claimB1_bound_to_real hcardF1 hSv1 hwin
    -- Denominator chain.
    have hchain : (N : ℝ) * Fintype.card F / (Fintype.card F + 2 * N)
        ≤ Fintype.card F * (Sv.card : ℝ) / (Fintype.card F + Sv.card - 1) :=
      listDecoding_winning_lb (by exact_mod_cast hcardF1) (by exact_mod_cast hN1) hAreal
    have hwinge : (N : ℝ) * Fintype.card F / (Fintype.card F + 2 * N) ≤ (winImg.card : ℝ) := by
      refine le_trans hchain (le_trans (le_of_eq ?_) hBreal)
      ring
    -- winImg ⊆ winningSet ⇒ |winImg| ≤ ncard(winningSet).
    have hncard : (winImg.card : ℝ) ≤ ((winningSet C δ v μ₁ μ₂ f₁ f₂).ncard : ℝ) := by
      have : winImg.card ≤ (winningSet C δ v μ₁ μ₂ f₁ f₂).ncard := by
        rw [← Set.ncard_coe_finset winImg]
        exact Set.ncard_le_ncard hmem (Set.toFinite _)
      exact_mod_cast this
    rw [ge_iff_le]
    exact le_trans hwinge hncard

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
