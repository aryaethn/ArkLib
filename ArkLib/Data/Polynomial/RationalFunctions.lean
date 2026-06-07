/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.Prelims
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Function Fields and Rings of Regular Functions

We define the notions of Appendix A of [BCIKS20].

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/

set_option linter.style.longFile 2000

open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace BCIKS20AppendixA

section

variable {F : Type} [CommRing F] [IsDomain F]

/-- Construction of the monicized polynomial `H_tilde` in Appendix A.1 of [BCIKS20].
Note: Here `H ∈ F[X][Y]` translates to `H ∈ F[Z][Y]` in [BCIKS20], and `H_tilde` in
`Polynomial (RatFunc F)` translates to `H_tilde ∈ F(Z)[T]` in [BCIKS20]. -/
noncomputable def H_tilde (H : F[X][Y]) : Polynomial (RatFunc F) :=
  let hᵢ (i : ℕ) := H.coeff i
  let d := H.natDegree
  let W := (RingHom.comp Polynomial.C univPolyHom) (hᵢ d)
  let S : Polynomial (RatFunc F) := Polynomial.X / W
  let H' := Polynomial.eval₂ (RingHom.comp Polynomial.C univPolyHom) S H
  W ^ (d - 1) * H'

section FieldIrreducibility

variable {F : Type} [Field F]

private lemma univPolyHom_injective :
    Function.Injective (univPolyHom (F := F)) := by
  simpa [ToRatFunc.univPolyHom] using (RatFunc.algebraMap_injective (K := F))

private lemma irreducible_comp_C_mul_X_iff {K : Type} [Field K] (a : K) (ha : a ≠ 0)
    (p : K[X]) :
    Irreducible (p.comp (Polynomial.C a * Polynomial.X)) ↔ Irreducible p := by
  letI : Invertible a := invertibleOfNonzero ha
  let e : K[X] ≃ₐ[K] K[X] := Polynomial.algEquivCMulXAddC a 0
  have hp : e p = p.comp (Polynomial.C a * Polynomial.X) := by
    simp [e, ← Polynomial.comp_eq_aeval]
  rw [← hp]
  exact MulEquiv.irreducible_iff (f := (e : K[X] ≃* K[X])) (x := p)

private lemma irreducible_map_univPolyHom_of_irreducible
    {H : Polynomial (Polynomial F)} (hdeg : H.natDegree ≠ 0)
    (hH : Irreducible H) :
    Irreducible (H.map (univPolyHom (F := F))) := by
  have hprim : H.IsPrimitive := Irreducible.isPrimitive hH hdeg
  simpa [ToRatFunc.univPolyHom] using
    (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map
      (K := RatFunc F) hprim).mp hH

/-- Corrected irreducibility statement for `H_tilde`: the paper assumes positive `Y`-degree.
Without this hypothesis, a constant irreducible in `F[Z][Y]` can become a unit in `F(Z)[T]`. -/
lemma irreducibleHTildeOfIrreducible_of_natDegree_pos
    {H : Polynomial (Polynomial F)} (hdeg : 0 < H.natDegree)
    (hH : Irreducible H) :
    Irreducible (H_tilde H) := by
  classical
  let d : ℕ := H.natDegree
  let a : RatFunc F := univPolyHom (F := F) H.leadingCoeff
  let W : Polynomial (RatFunc F) := Polynomial.C a
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hdeg
  have hlead_ne : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hH_ne
  have ha_ne : a ≠ 0 := by
    intro ha
    exact hlead_ne (univPolyHom_injective (by simpa [a] using ha))
  have hmap_irreducible : Irreducible (H.map (univPolyHom (F := F))) :=
    irreducible_map_univPolyHom_of_irreducible (Nat.ne_of_gt hdeg) hH
  have hsub :
      Polynomial.X / W = Polynomial.C a⁻¹ * (Polynomial.X : Polynomial (RatFunc F)) := by
    calc
      Polynomial.X / W = Polynomial.X / Polynomial.C a := rfl
      _ = Polynomial.X * Polynomial.C a⁻¹ := Polynomial.div_C
      _ = Polynomial.C a⁻¹ * Polynomial.X := by rw [mul_comm]
  have hcomp_irreducible :
      Irreducible
        ((H.map (univPolyHom (F := F))).comp
          (Polynomial.C a⁻¹ * (Polynomial.X : Polynomial (RatFunc F)))) := by
    exact (irreducible_comp_C_mul_X_iff (a := a⁻¹) (inv_ne_zero ha_ne)
      (H.map (univPolyHom (F := F)))).mpr hmap_irreducible
  have heval :
      Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / W) H =
        (H.map (univPolyHom (F := F))).comp (Polynomial.X / W) := by
    simpa [Polynomial.comp] using
      (Polynomial.eval₂_map (p := H) (f := univPolyHom (F := F))
        (g := (Polynomial.C : RatFunc F →+* Polynomial (RatFunc F)))
        (x := Polynomial.X / W)).symm
  have heval_irreducible :
      Irreducible
        (Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / W)
          H) := by
    rw [heval, hsub]
    exact hcomp_irreducible
  have hunitW : IsUnit (W ^ (d - 1)) := by
    exact (isUnit_C.mpr (Ne.isUnit ha_ne)).pow (d - 1)
  rcases hunitW with ⟨u, hu⟩
  have htilde :
      H_tilde H =
        W ^ (d - 1) *
          Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / W)
            H := by
    rfl
  rw [htilde, ← hu]
  exact (irreducible_units_mul (M := Polynomial (RatFunc F)) (u := u)).2 heval_irreducible

end FieldIrreducibility

/-- The monicized version `H_tilde` is irreducible if the original polynomial `H` is irreducible
and has positive degree in `Y`, as assumed in Appendix A.1 of [BCIKS20]. -/
lemma irreducibleHTildeOfIrreducible {F : Type} [Field F] {H : Polynomial (Polynomial F)}
    (hHdeg : 0 < H.natDegree) :
    Irreducible H → Irreducible (H_tilde H) :=
  irreducibleHTildeOfIrreducible_of_natDegree_pos hHdeg

/-- The function field `𝕃` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝕃 (H : F[X][Y]) : Type :=
  (Polynomial (RatFunc F)) ⧸ (Ideal.span {H_tilde H})

/-- The function field `𝕃` is a field when `H` is irreducible and has positive `Y`-degree. -/
lemma isField_of_irreducible_of_natDegree_pos {F : Type} [Field F] {H : F[X][Y]}
    (hHdeg : 0 < H.natDegree) (hH : Irreducible H) : IsField (𝕃 H) := by
  unfold 𝕃
  erw [← Ideal.Quotient.maximal_ideal_iff_isField_quotient, principal_is_maximal_iff_irred]
  exact irreducibleHTildeOfIrreducible_of_natDegree_pos hHdeg hH

/-- The function field `𝕃` is a field under the standard Appendix A irreducibility hypothesis. -/
lemma isField_of_irreducible {F : Type} [Field F] {H : F[X][Y]} (hHdeg : 0 < H.natDegree) :
    Irreducible H → IsField (𝕃 H) := by
  intro h
  unfold 𝕃
  erw [← Ideal.Quotient.maximal_ideal_iff_isField_quotient, principal_is_maximal_iff_irred]
  exact irreducibleHTildeOfIrreducible hHdeg h

/-- The function field `𝕃` is a field under positive-degree irreducibility assumptions. -/
noncomputable instance {F : Type} [Field F] {H : F[X][Y]} [hHdeg : Fact (0 < H.natDegree)]
    [inst : Fact (Irreducible H)] : Field (𝕃 H) :=
  IsField.toField (isField_of_irreducible hHdeg.out inst.out)

/-- The integral monicized polynomial corresponding to `H_tilde`, with coefficients in `F[X]`. -/
noncomputable def H_tilde' (H : F[X][Y]) : F[X][Y] :=
  if H.natDegree = 0 then
    Polynomial.C (H.coeff 0)
  else
    let hᵢ (i : ℕ) := H.coeff i
    let d := H.natDegree
    let W := hᵢ d
    Polynomial.X ^ d +
      ∑ i ∈ Finset.range d,
        Polynomial.C (hᵢ i * W ^ (d - 1 - i)) * Polynomial.X ^ i

omit [IsDomain F] in
/-- If `H` has positive degree in `Y`, then `H_tilde' H` is monic. -/
lemma H_tilde'_monic (H : F[X][Y]) (hH : 0 < H.natDegree) :
    (H_tilde' H).Monic := by
  classical
  have hdeg : H.natDegree ≠ 0 := Nat.ne_of_gt hH
  rw [H_tilde', if_neg hdeg]
  exact Polynomial.monic_X_pow_add <| (Polynomial.degree_sum_le _ _).trans_lt <| by
    exact (Finset.sup_lt_iff (WithBot.bot_lt_coe H.natDegree)).2 <| by
      intro i hi
      exact (Polynomial.degree_C_mul_X_pow_le i _).trans_lt
        (WithBot.coe_lt_coe.2 (Finset.mem_range.mp hi))

private lemma monicize_term {K : Type} [Field K] (a b : K) (i d : ℕ)
    (ha : a ≠ 0) (hi : i < d) :
    (Polynomial.C a ^ (d - 1)) * (Polynomial.C b * (Polynomial.X / Polynomial.C a) ^ i) =
      Polynomial.C (b * a ^ (d - 1 - i)) * Polynomial.X ^ i := by
  rw [Polynomial.div_C, mul_pow]
  rw [show Polynomial.C a ^ (d - 1) = Polynomial.C (a ^ (d - 1)) by rw [Polynomial.C_pow]]
  rw [show Polynomial.C a⁻¹ ^ i = Polynomial.C (a⁻¹ ^ i) by rw [Polynomial.C_pow]]
  have hscalar : a ^ (d - 1) * b * a⁻¹ ^ i = b * a ^ (d - 1 - i) := by
    have hsplit : d - 1 = (d - 1 - i) + i := by omega
    rw [hsplit, pow_add, inv_pow]
    field_simp [ha]
    have hexp : d - 1 - i + i - i = d - 1 - i := by omega
    rw [hexp]
    ring_nf
  have hscalar' : a ^ (d - 1) * (b * a⁻¹ ^ i) = b * a ^ (d - 1 - i) := by
    simpa [mul_assoc] using hscalar
  calc
    Polynomial.C (a ^ (d - 1)) * (Polynomial.C b * (Polynomial.X ^ i * Polynomial.C (a⁻¹ ^ i))) =
        Polynomial.X ^ i * Polynomial.C (a ^ (d - 1) * (b * a⁻¹ ^ i)) := by
          calc
            Polynomial.C (a ^ (d - 1)) *
                (Polynomial.C b * (Polynomial.X ^ i * Polynomial.C (a⁻¹ ^ i))) =
                Polynomial.X ^ i *
                  (Polynomial.C (a ^ (d - 1)) * Polynomial.C b * Polynomial.C (a⁻¹ ^ i)) := by
                    ring
            _ = Polynomial.X ^ i * Polynomial.C (a ^ (d - 1) * (b * a⁻¹ ^ i)) := by
                  rw [← Polynomial.C_mul, ← Polynomial.C_mul]
                  simp [mul_assoc]
    _ = Polynomial.X ^ i * Polynomial.C (b * a ^ (d - 1 - i)) := by rw [hscalar']
    _ = Polynomial.C (b * a ^ (d - 1 - i)) * Polynomial.X ^ i := by rw [mul_comm]

private lemma monicize_leading_term {K : Type} [Field K] (a : K) (d : ℕ)
    (ha : a ≠ 0) (hd : 0 < d) :
    (Polynomial.C a ^ (d - 1)) * (Polynomial.C a * (Polynomial.X / Polynomial.C a) ^ d) =
      Polynomial.X ^ d := by
  rw [Polynomial.div_C, mul_pow]
  rw [show Polynomial.C a ^ (d - 1) = Polynomial.C (a ^ (d - 1)) by rw [Polynomial.C_pow]]
  rw [show Polynomial.C a⁻¹ ^ d = Polynomial.C (a⁻¹ ^ d) by rw [Polynomial.C_pow]]
  have hscalar : a ^ (d - 1) * a * a⁻¹ ^ d = (1 : K) := by
    have hd' : d = (d - 1) + 1 := by omega
    rw [hd', pow_add, pow_one, inv_pow]
    field_simp [ha]
    have hexp : d - 1 + 1 - 1 = d - 1 := by omega
    rw [hexp]
  have hscalar' : a ^ (d - 1) * (a * a⁻¹ ^ d) = (1 : K) := by
    simpa [mul_assoc] using hscalar
  calc
    Polynomial.C (a ^ (d - 1)) * (Polynomial.C a * (Polynomial.X ^ d * Polynomial.C (a⁻¹ ^ d))) =
        Polynomial.X ^ d * Polynomial.C (a ^ (d - 1) * (a * a⁻¹ ^ d)) := by
          calc
            Polynomial.C (a ^ (d - 1)) *
                (Polynomial.C a * (Polynomial.X ^ d * Polynomial.C (a⁻¹ ^ d))) =
                Polynomial.X ^ d *
                  (Polynomial.C (a ^ (d - 1)) * Polynomial.C a * Polynomial.C (a⁻¹ ^ d)) := by
                    ring
            _ = Polynomial.X ^ d * Polynomial.C (a ^ (d - 1) * (a * a⁻¹ ^ d)) := by
                  rw [← Polynomial.C_mul, ← Polynomial.C_mul]
                  simp [mul_assoc]
    _ = Polynomial.X ^ d * Polynomial.C (1 : K) := by rw [hscalar']
    _ = Polynomial.X ^ d := by simp

/-- The polynomial `H_tilde'` agrees with the monicization `H_tilde` after embedding into
`Polynomial (RatFunc F)`. -/
lemma map_H_tilde'_eq_H_tilde (H : F[X][Y]) : (H_tilde' H).map univPolyHom = H_tilde H := by
  classical
  by_cases hdeg : H.natDegree = 0
  · simp only [H_tilde', hdeg, ↓reduceIte, map_C]
    have hconst : H = Polynomial.C (H.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero (by omega)
    rw [hconst, H_tilde]
    simp
  · have hH_ne : H ≠ 0 := by
      intro hzero
      apply hdeg
      simp [hzero]
    have hw_ne_zero : univPolyHom H.leadingCoeff ≠ 0 := by
      apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      rw [mem_nonZeroDivisors_iff_ne_zero]
      exact Polynomial.leadingCoeff_ne_zero.mpr hH_ne
    have hd : 0 < H.natDegree := Nat.pos_of_ne_zero hdeg
    have hEval :
        Polynomial.eval₂ (RingHom.comp Polynomial.C univPolyHom)
          (Polynomial.X /
            (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) H =
        ∑ i ∈ Finset.range (H.natDegree + 1),
          Polynomial.C (univPolyHom (H.coeff i)) *
            (Polynomial.X /
              (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^ i := by
      simpa using
        (Polynomial.eval₂_eq_sum_range
          (p := H) (f := RingHom.comp Polynomial.C univPolyHom)
          (x := Polynomial.X /
            (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)))
    simp only [H_tilde', hdeg, ↓reduceIte, coeff_natDegree, map_mul, map_pow,
      Polynomial.map_add, Polynomial.map_pow, map_X]
    rw [H_tilde, hEval, Finset.sum_range_succ, mul_add, Finset.mul_sum, Polynomial.map_sum]
    have hsum :
        ∑ i ∈ Finset.range H.natDegree,
          ((RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
              (H.natDegree - 1)) *
            (Polynomial.C (univPolyHom (H.coeff i)) *
              (Polynomial.X /
                (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^ i) =
        ∑ i ∈ Finset.range H.natDegree,
          Polynomial.map univPolyHom
            (Polynomial.C (H.coeff i) * Polynomial.C H.leadingCoeff ^ (H.natDegree - 1 - i) *
              Polynomial.X ^ i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [Polynomial.coeff_natDegree, map_mul, map_pow] using
        monicize_term (univPolyHom H.leadingCoeff) (univPolyHom (H.coeff i)) i H.natDegree
          hw_ne_zero (Finset.mem_range.mp hi)
    have hlead :
        ((RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
            (H.natDegree - 1)) *
          (Polynomial.C (univPolyHom (H.coeff H.natDegree)) *
            (Polynomial.X /
              (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^
              H.natDegree) =
        Polynomial.X ^ H.natDegree := by
      simpa [Polynomial.coeff_natDegree] using
        monicize_leading_term (univPolyHom H.leadingCoeff) H.natDegree hw_ne_zero hd
    rw [hlead]
    calc
      Polynomial.X ^ H.natDegree +
          ∑ i ∈ Finset.range H.natDegree,
            Polynomial.map univPolyHom
              (Polynomial.C (H.coeff i) * Polynomial.C H.leadingCoeff ^ (H.natDegree - 1 - i) *
                Polynomial.X ^ i) =
          Polynomial.X ^ H.natDegree +
            ∑ i ∈ Finset.range H.natDegree,
              (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
                  (H.natDegree - 1) *
                (Polynomial.C (univPolyHom (H.coeff i)) *
                  (Polynomial.X /
                    (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^
                    i) := by
              exact congrArg (fun p => Polynomial.X ^ H.natDegree + p) hsum.symm
      _ =
          ∑ i ∈ Finset.range H.natDegree,
            (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
                (H.natDegree - 1) *
              (Polynomial.C (univPolyHom (H.coeff i)) *
                (Polynomial.X /
                  (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^
                  i) +
            Polynomial.X ^ H.natDegree := by
              rw [add_comm]

section IntegralIrreducibility

variable {F : Type} [Field F]

/-- The integral monicized polynomial `H_tilde'` is irreducible whenever `H` is irreducible and has
positive degree in `Y`. -/
lemma irreducibleHTilde'OfIrreducible {H : F[X][Y]} (hHdeg : 0 < H.natDegree)
    (hH : Irreducible H) :
    Irreducible (H_tilde' H) := by
  have hmap : Irreducible ((H_tilde' H).map (univPolyHom (F := F))) := by
    simpa [map_H_tilde'_eq_H_tilde] using
      irreducibleHTildeOfIrreducible_of_natDegree_pos hHdeg hH
  exact (H_tilde'_monic H hHdeg).isPrimitive.irreducible_of_irreducible_map_of_injective
    (univPolyHom_injective (F := F)) hmap

end IntegralIrreducibility

/-- The ring of regular elements `𝒪` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝒪 (H : F[X][Y]) : Type :=
  (Polynomial (Polynomial F)) ⧸ (Ideal.span {H_tilde' H})

/-- The ring of regular elements `𝒪` is a ring. -/
noncomputable instance {H : F[X][Y]} : Ring (𝒪 H) :=
  Ideal.Quotient.ring (Ideal.span {H_tilde' H})

/-- The ring homomorphism defining the embedding of `𝒪` into `𝕃`. -/
noncomputable def embeddingOf𝒪Into𝕃 (H : F[X][Y]) : 𝒪 H →+* 𝕃 H :=
  Ideal.quotientMap
    (I := Ideal.span {H_tilde' H}) (Ideal.span {H_tilde H})
    bivPolyHom (by
      rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      change bivPolyHom (H_tilde' H) ∈ span {H_tilde H}
      rw [show bivPolyHom (H_tilde' H) = (H_tilde' H).map univPolyHom from rfl,
        map_H_tilde'_eq_H_tilde]
      exact Ideal.subset_span rfl)

section FieldEmbedding

variable {F : Type} [Field F]

private lemma H_tilde'_dvd_of_map_dvd_H_tilde {H p : F[X][Y]} (hHdeg : 0 < H.natDegree)
    (hp : H_tilde H ∣ p.map (univPolyHom (F := F))) :
    H_tilde' H ∣ p := by
  let q : F[X][Y] := H_tilde' H
  have hqmonic : q.Monic := H_tilde'_monic H hHdeg
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hqmonic]
  rw [← Polynomial.map_eq_zero_iff (univPolyHom_injective (F := F))]
  have hqmap_dvd_p : q.map (univPolyHom (F := F)) ∣ p.map (univPolyHom (F := F)) := by
    simpa [q, map_H_tilde'_eq_H_tilde] using hp
  have hqmap_dvd_rem :
      q.map (univPolyHom (F := F)) ∣
        (p %ₘ q).map (univPolyHom (F := F)) := by
    have hrem :
        (p %ₘ q).map (univPolyHom (F := F)) =
          p.map (univPolyHom (F := F)) -
            q.map (univPolyHom (F := F)) * (p /ₘ q).map (univPolyHom (F := F)) := by
      have h := congrArg (fun r : F[X][Y] => r.map (univPolyHom (F := F)))
        (Polynomial.modByMonic_add_div p q)
      simp only [Polynomial.map_add, Polynomial.map_mul] at h
      rw [← h]
      ring
    rw [hrem]
    exact dvd_sub hqmap_dvd_p (dvd_mul_right _ _)
  have hdegree :
      ((p %ₘ q).map (univPolyHom (F := F))).degree <
        (q.map (univPolyHom (F := F))).degree := by
    rw [Polynomial.degree_map_eq_of_injective (univPolyHom_injective (F := F))]
    rw [Polynomial.degree_map_eq_of_injective (univPolyHom_injective (F := F))]
    exact Polynomial.degree_modByMonic_lt p hqmonic
  exact Polynomial.eq_zero_of_dvd_of_degree_lt hqmap_dvd_rem hdegree

private lemma mem_span_H_tilde'_of_bivPolyHom_mem_span_H_tilde {H p : F[X][Y]}
    (hHdeg : 0 < H.natDegree)
    (hp : bivPolyHom p ∈ Ideal.span {H_tilde H}) :
    p ∈ Ideal.span {H_tilde' H} := by
  rw [Ideal.mem_span_singleton] at hp ⊢
  exact H_tilde'_dvd_of_map_dvd_H_tilde hHdeg (by
    simpa [show bivPolyHom p = p.map (univPolyHom (F := F)) from rfl] using hp)

/-- The regular quotient embeds injectively into the function-field quotient when `H` has positive
degree in `Y`. -/
lemma embeddingOf𝒪Into𝕃_injective {H : F[X][Y]} (hHdeg : 0 < H.natDegree) :
    Function.Injective (embeddingOf𝒪Into𝕃 H) := by
  unfold embeddingOf𝒪Into𝕃
  apply Ideal.quotientMap_injective'
  intro p hp
  exact mem_span_H_tilde'_of_bivPolyHom_mem_span_H_tilde hHdeg hp

end FieldEmbedding

/-- The set of regular elements inside `𝕃 H`, i.e. the set of elements of `𝕃 H`
that in fact lie in `𝒪 H`. -/
def regularElementsSet (H : F[X][Y]) : Set (𝕃 H) :=
  {a : 𝕃 H | ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- The regular elements inside `𝕃 H`, i.e. the elements of `𝕃 H` that in fact lie in `𝒪 H`
as Type. -/
def regularElements (H : F[X][Y]) : Type :=
  {a : 𝕃 H // ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- Zero is regular. -/
@[simp]
lemma regularElementsSet_zero (H : F[X][Y]) : (0 : 𝕃 H) ∈ regularElementsSet H :=
  ⟨0, by simp⟩

/-- One is regular. -/
@[simp]
lemma regularElementsSet_one (H : F[X][Y]) : (1 : 𝕃 H) ∈ regularElementsSet H :=
  ⟨1, by simp⟩

/-- The regular elements are closed under addition. -/
lemma regularElementsSet_add {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElementsSet H) (hb : b ∈ regularElementsSet H) :
    a + b ∈ regularElementsSet H := by
  rcases ha with ⟨a', rfl⟩
  rcases hb with ⟨b', rfl⟩
  exact ⟨a' + b', by simp⟩

/-- The regular elements are closed under negation. -/
lemma regularElementsSet_neg {H : F[X][Y]} {a : 𝕃 H}
    (ha : a ∈ regularElementsSet H) : -a ∈ regularElementsSet H := by
  rcases ha with ⟨a', rfl⟩
  exact ⟨-a', by simp⟩

/-- The regular elements are closed under subtraction. -/
lemma regularElementsSet_sub {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElementsSet H) (hb : b ∈ regularElementsSet H) :
    a - b ∈ regularElementsSet H := by
  simpa [sub_eq_add_neg] using regularElementsSet_add ha (regularElementsSet_neg hb)

/-- The regular elements are closed under multiplication. -/
lemma regularElementsSet_mul {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElementsSet H) (hb : b ∈ regularElementsSet H) :
    a * b ∈ regularElementsSet H := by
  rcases ha with ⟨a', rfl⟩
  rcases hb with ⟨b', rfl⟩
  exact ⟨a' * b', by simp⟩

/-- The regular elements are closed under natural powers. -/
lemma regularElementsSet_pow {H : F[X][Y]} {a : 𝕃 H}
    (ha : a ∈ regularElementsSet H) (n : ℕ) : a ^ n ∈ regularElementsSet H := by
  induction n with
  | zero => simp
  | succ n ih =>
      simpa [pow_succ] using regularElementsSet_mul ih ha

/-- The regular elements are closed under finite sums. -/
lemma regularElementsSet_sum {ι : Type} {H : F[X][Y]} (s : Finset ι) {f : ι → 𝕃 H}
    (hf : ∀ i ∈ s, f i ∈ regularElementsSet H) :
    (∑ i ∈ s, f i) ∈ regularElementsSet H := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _hf
    simp
  · intro a s ha ih hf
    rw [Finset.sum_insert ha]
    exact regularElementsSet_add
      (hf a (by simp [ha]))
      (ih fun i hi => hf i (by simp [hi]))

/-- Given an element `z ∈ F`, `t_z ∈ F` is a rational root of a bivariate polynomial if the pair
`(z, t_z)` is a root of the bivariate polynomial. -/
def rationalRoot (H : F[X][Y]) (z : F) : Type :=
  {t_z : F // evalEval z t_z H = 0}

/-- The rational substitution `π_z` from Appendix A.3 defined on the whole ring of
bivariate polynomials. -/
noncomputable def π_z_lift {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) :
    F[X][Y] →+* F :=
  Polynomial.evalEvalRingHom z root.1

/-- The rational substitution `π_z` from Appendix A.3 of [BCIKS20] is a well-defined map on the
quotient ring `𝒪`. -/
noncomputable def π_z {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) :
    𝒪 H →+* F :=
  Ideal.Quotient.lift (Ideal.span {H_tilde' H}) (π_z_lift z root) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    simp only [π_z_lift, map_mul]
    rw [show (Polynomial.evalEvalRingHom z root.1) (H_tilde' H) = 0 from root.2]
    ring)

/-- The canonical representative of an element of `F[X][Y]` inside the ring of regular elements
`𝒪`, defined when `H` has positive degree in `Y`. -/
noncomputable def canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) : F[X][Y] :=
  let _hHt := H_tilde'_monic H hH
  Polynomial.modByMonic β.out (H_tilde' H)

/-- The canonical representative has degree strictly smaller than the defining relation. -/
lemma canonicalRepOf𝒪_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    (canonicalRepOf𝒪 hH β).degree < (H_tilde' H).degree := by
  rw [canonicalRepOf𝒪]
  exact Polynomial.degree_modByMonic_lt _ (H_tilde'_monic H hH)

omit [IsDomain F] in
/-- The canonical representative has natural degree bounded by the defining relation. -/
lemma canonicalRepOf𝒪_natDegree_le {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    (canonicalRepOf𝒪 hH β).natDegree ≤ (H_tilde' H).natDegree := by
  rw [canonicalRepOf𝒪]
  exact Polynomial.natDegree_modByMonic_le _ (H_tilde'_monic H hH)

omit [IsDomain F] in
/-- The canonical representative maps back to the original quotient element of `𝒪`. -/
@[simp]
lemma mk_canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (canonicalRepOf𝒪 hH β) = β := by
  let I : Ideal F[X][Y] := Ideal.span {H_tilde' H}
  let q : F[X][Y] := H_tilde' H
  let p : F[X][Y] := β.out
  have hq_zero : Ideal.Quotient.mk I (q * (p /ₘ q)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  calc
    Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (canonicalRepOf𝒪 hH β)
        = Ideal.Quotient.mk I (p %ₘ q) := by
            simp [canonicalRepOf𝒪, I, q, p]
    _ = Ideal.Quotient.mk I (p %ₘ q) + Ideal.Quotient.mk I (q * (p /ₘ q)) := by
            simp [hq_zero]
    _ = Ideal.Quotient.mk I (p %ₘ q + q * (p /ₘ q)) := by
            rw [map_add]
    _ = Ideal.Quotient.mk I p := by
            rw [Polynomial.modByMonic_add_div]
    _ = β := by
            simp [I, p]

omit [IsDomain F] in
/-- Canonical representatives of quotient constructors are computed by `modByMonic`. -/
lemma canonicalRepOf𝒪_mk {H : F[X][Y]} (hH : 0 < H.natDegree) (p : F[X][Y]) :
    canonicalRepOf𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) =
      p %ₘ H_tilde' H := by
  apply Polynomial.modByMonic_eq_of_dvd_sub (H_tilde'_monic H hH)
  rw [← Ideal.mem_span_singleton]
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  calc
    Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        ((Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H).out)
        = (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) := by simp
    _ = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p := rfl

omit [IsDomain F] in
/-- The canonical representative of zero is zero. -/
@[simp]
lemma canonicalRepOf𝒪_zero {H : F[X][Y]} (hH : 0 < H.natDegree) :
    canonicalRepOf𝒪 hH (0 : 𝒪 H) = 0 := by
  simpa using (canonicalRepOf𝒪_mk (H := H) hH 0)

/-- A polynomial whose degree is already below the relation is its own canonical representative. -/
lemma canonicalRepOf𝒪_mk_eq_self_of_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree)
    {p : F[X][Y]} (hp : p.degree < (H_tilde' H).degree) :
    canonicalRepOf𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) = p := by
  rw [canonicalRepOf𝒪_mk]
  exact (Polynomial.modByMonic_eq_self_iff (H_tilde'_monic H hH)).2 hp

/-- `Λ` is a weight function on the ring of bivariate polynomials `F[X][Y]`. The weight of
a polynomial is the maximal weight of all monomials appearing in it with non-zero coefficients.
The weight of the zero polynomial is `−∞`.
Requires `D ≥ Bivariate.totalDegree H` to match definition in [BCIKS20]. -/
noncomputable def weight_Λ (f H : F[X][Y]) (D : ℕ) : WithBot ℕ :=
  Finset.sup
    f.support
    (fun deg =>
      WithBot.some <| deg * (D + 1 - Bivariate.natDegreeY H) + (f.coeff deg).natDegree
    )

omit [IsDomain F] in
/-- The zero polynomial has bottom `Λ`-weight. -/
@[simp]
lemma weight_Λ_zero (H : F[X][Y]) (D : ℕ) :
    weight_Λ (0 : F[X][Y]) H D = ⊥ := by
  simp [weight_Λ]

/-- The weight function `Λ` on regular elements is the weight of their canonical representatives
in `F[X][Y]`. -/
noncomputable def weight_Λ_over_𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (f : 𝒪 H) (D : ℕ) :
    WithBot ℕ := weight_Λ (canonicalRepOf𝒪 hH f) H D

omit [IsDomain F] in
/-- The `𝒪`-weight of zero is bottom. -/
@[simp]
lemma weight_Λ_over_𝒪_zero {H : F[X][Y]} (hH : 0 < H.natDegree) (D : ℕ) :
    weight_Λ_over_𝒪 hH (0 : 𝒪 H) D = ⊥ := by
  simp [weight_Λ_over_𝒪]

omit [IsDomain F] in
/-- The `𝒪`-weight of a quotient constructor is computed on its canonical remainder. -/
lemma weight_Λ_over_𝒪_mk {H : F[X][Y]} (hH : 0 < H.natDegree) (p : F[X][Y])
    (D : ℕ) :
    weight_Λ_over_𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) D =
      weight_Λ (p %ₘ H_tilde' H) H D := by
  simp [weight_Λ_over_𝒪, canonicalRepOf𝒪_mk]

/-- If a representative is already reduced, its `𝒪`-weight is its polynomial `Λ`-weight. -/
lemma weight_Λ_over_𝒪_mk_eq_self_of_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree)
    {p : F[X][Y]} (hp : p.degree < (H_tilde' H).degree) (D : ℕ) :
    weight_Λ_over_𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) D =
      weight_Λ p H D := by
  simp [weight_Λ_over_𝒪, canonicalRepOf𝒪_mk_eq_self_of_degree_lt hH hp]

/-! ### Λ-weight calculus

Algebraic identities for the bivariate `Λ`-weight from Appendix A.2 of [BCIKS20]. The weight
`m := D + 1 − natDegreeY H` is the per-Y-power contribution; constants in `F[X]` contribute their
`natDegree`. -/

omit [IsDomain F] in
/-- A monomial `n` in `f`'s support contributes a lower bound on `Λ(f)`. -/
lemma le_weight_Λ_of_mem_support {f H : F[X][Y]} {D : ℕ} {n : ℕ} (hn : n ∈ f.support) :
    (WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree) :
      WithBot ℕ) ≤ weight_Λ f H D := by
  classical
  exact Finset.le_sup (f := fun deg =>
    (WithBot.some (deg * (D + 1 - Bivariate.natDegreeY H) + (f.coeff deg).natDegree) :
      WithBot ℕ)) hn

omit [IsDomain F] in
/-- Characterization: `Λ(f) ≤ b` iff every monomial in `f`'s support contributes at most `b`. -/
lemma weight_Λ_le_iff {f H : F[X][Y]} {D b : ℕ} :
    weight_Λ f H D ≤ (WithBot.some b : WithBot ℕ) ↔
      ∀ n ∈ f.support,
        n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree ≤ b := by
  classical
  refine ⟨fun h n hn => ?_, fun h => ?_⟩
  · have := (le_weight_Λ_of_mem_support hn).trans h
    exact_mod_cast this
  · refine Finset.sup_le (fun n hn => ?_)
    exact_mod_cast (h n hn)

omit [IsDomain F] in
/-- `Λ(C c) ≤ c.natDegree`. -/
lemma weight_Λ_C_le (H : F[X][Y]) (D : ℕ) (c : F[X]) :
    weight_Λ (Polynomial.C c) H D ≤ (WithBot.some c.natDegree : WithBot ℕ) := by
  classical
  rw [weight_Λ_le_iff]
  intro n hn
  have : (Polynomial.C c : F[X][Y]).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hn0 : n = 0 := by
    by_contra h
    simp [Polynomial.coeff_C, h] at this
  subst hn0
  simp [Polynomial.coeff_C]

omit [IsDomain F] in
/-- `Λ(Y^k) ≤ k · m`. -/
lemma weight_Λ_X_pow_le (H : F[X][Y]) (D k : ℕ) :
    weight_Λ ((Polynomial.X : F[X][Y]) ^ k) H D ≤
      (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H)) : WithBot ℕ) := by
  classical
  rw [weight_Λ_le_iff]
  intro n hn
  have : ((Polynomial.X : F[X][Y]) ^ k).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hnk : n = k := by
    by_contra h
    simp [Polynomial.coeff_X_pow, h] at this
  subst hnk
  simp [Polynomial.coeff_X_pow]

omit [IsDomain F] in
/-- `Λ(C c · Y^k) ≤ k · m + c.natDegree`. -/
lemma weight_Λ_C_mul_X_pow_le (H : F[X][Y]) (D : ℕ) (c : F[X]) (k : ℕ) :
    weight_Λ (Polynomial.C c * Polynomial.X ^ k) H D ≤
      (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree) : WithBot ℕ) := by
  classical
  rw [weight_Λ_le_iff]
  intro n hn
  have : (Polynomial.C c * Polynomial.X ^ k : F[X][Y]).coeff n ≠ 0 :=
    Polynomial.mem_support_iff.mp hn
  have hnk : n = k := by
    by_contra h
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, h] at this
  subst hnk
  simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]

omit [IsDomain F] in
/-- The `Λ`-weight is invariant under negation. -/
@[simp]
lemma weight_Λ_neg (f H : F[X][Y]) (D : ℕ) : weight_Λ (-f) H D = weight_Λ f H D := by
  classical
  unfold weight_Λ
  rw [Polynomial.support_neg]
  refine Finset.sup_congr rfl (fun n _ => ?_)
  simp [Polynomial.coeff_neg]

omit [IsDomain F] in
/-- `Λ(f + g) ≤ max(Λ(f), Λ(g))`. -/
lemma weight_Λ_add_le (f g H : F[X][Y]) (D : ℕ) :
    weight_Λ (f + g) H D ≤ max (weight_Λ f H D) (weight_Λ g H D) := by
  classical
  refine Finset.sup_le (fun n hn => ?_)
  -- The contribution at `n` to weight_Λ (f + g) is bounded by f's or g's contribution.
  have hcoeff : (f + g).coeff n = f.coeff n + g.coeff n := Polynomial.coeff_add _ _ _
  have hsum_ne : f.coeff n + g.coeff n ≠ 0 := by
    rw [← hcoeff]
    exact Polynomial.mem_support_iff.mp hn
  by_cases hf : f.coeff n = 0
  · -- f.coeff n = 0, so g.coeff n ≠ 0
    have hg : g.coeff n ≠ 0 := by simpa [hf] using hsum_ne
    have hng : n ∈ g.support := Polynomial.mem_support_iff.mpr hg
    have heq : (f + g).coeff n = g.coeff n := by simp [hcoeff, hf]
    change (WithBot.some _ : WithBot ℕ) ≤ _
    rw [heq]
    exact (le_weight_Λ_of_mem_support hng).trans (le_max_right _ _)
  · have hnf : n ∈ f.support := Polynomial.mem_support_iff.mpr hf
    by_cases hg : g.coeff n = 0
    · have heq : (f + g).coeff n = f.coeff n := by simp [hcoeff, hg]
      change (WithBot.some _ : WithBot ℕ) ≤ _
      rw [heq]
      exact (le_weight_Λ_of_mem_support hnf).trans (le_max_left _ _)
    · have hng : n ∈ g.support := Polynomial.mem_support_iff.mpr hg
      have hdeg : ((f + g).coeff n).natDegree ≤
          max (f.coeff n).natDegree (g.coeff n).natDegree := by
        rw [hcoeff]
        exact Polynomial.natDegree_add_le _ _
      rcases le_total (f.coeff n).natDegree (g.coeff n).natDegree with h | h
      · -- bound by g's contribution
        have hbound : ((f + g).coeff n).natDegree ≤ (g.coeff n).natDegree :=
          hdeg.trans_eq (max_eq_right h)
        have hle : n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree ≤
            n * (D + 1 - Bivariate.natDegreeY H) + (g.coeff n).natDegree :=
          Nat.add_le_add_left hbound _
        calc (WithBot.some
                (n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree) :
                WithBot ℕ)
            ≤ WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (g.coeff n).natDegree) :=
              by exact_mod_cast hle
          _ ≤ weight_Λ g H D := le_weight_Λ_of_mem_support hng
          _ ≤ max (weight_Λ f H D) (weight_Λ g H D) := le_max_right _ _
      · have hbound : ((f + g).coeff n).natDegree ≤ (f.coeff n).natDegree :=
          hdeg.trans_eq (max_eq_left h)
        have hle : n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree ≤
            n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree :=
          Nat.add_le_add_left hbound _
        calc (WithBot.some
                (n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree) :
                WithBot ℕ)
            ≤ WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree) :=
              by exact_mod_cast hle
          _ ≤ weight_Λ f H D := le_weight_Λ_of_mem_support hnf
          _ ≤ max (weight_Λ f H D) (weight_Λ g H D) := le_max_left _ _

omit [IsDomain F] in
/-- `Λ(f − g) ≤ max(Λ(f), Λ(g))`. -/
lemma weight_Λ_sub_le (f g H : F[X][Y]) (D : ℕ) :
    weight_Λ (f - g) H D ≤ max (weight_Λ f H D) (weight_Λ g H D) := by
  rw [sub_eq_add_neg]
  exact (weight_Λ_add_le f (-g) H D).trans_eq (by rw [weight_Λ_neg])

omit [IsDomain F] in
/-- `Λ` of a finite sum is bounded by the max of the summands' weights. -/
lemma weight_Λ_sum_le {ι : Type} (s : Finset ι) (f : ι → F[X][Y]) (H : F[X][Y]) (D : ℕ) :
    weight_Λ (∑ i ∈ s, f i) H D ≤ s.sup (fun i => weight_Λ (f i) H D) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sup_insert]
      exact (weight_Λ_add_le _ _ _ _).trans (max_le_max le_rfl ih)

omit [IsDomain F] in
/-- Bound on the `X`-degree of a coefficient of `H` from a `totalDegree` bound. -/
lemma natDegree_coeff_le_of_totalDegree_le (f : F[X][Y]) {D : ℕ}
    (hD : Bivariate.totalDegree f ≤ D) (i : ℕ) :
    (f.coeff i).natDegree ≤ D - i := by
  classical
  by_cases hi : f.coeff i = 0
  · simp [hi]
  · have hi_in : i ∈ f.support := Polynomial.mem_support_iff.mpr hi
    have h1 : (f.coeff i).natDegree + i ≤ Bivariate.totalDegree f :=
      Bivariate.coeff_totalDegree_le f hi_in
    omega

omit [IsDomain F] in
/-- Sub-additivity for `C c · Y^k · f`: given `Λ(f) ≤ b`, multiplying by `C c · Y^k` adds
`k · m + c.natDegree` to the weight. -/
lemma weight_Λ_C_mul_X_pow_mul_le {c : F[X]} {k : ℕ} {f H : F[X][Y]} {D b : ℕ}
    (hf : weight_Λ f H D ≤ (WithBot.some b : WithBot ℕ)) :
    weight_Λ (Polynomial.C c * Polynomial.X ^ k * f) H D ≤
      (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree + b) :
        WithBot ℕ) := by
  classical
  rw [weight_Λ_le_iff]
  rw [weight_Λ_le_iff] at hf
  intro n hn
  have hcoeff_ne : (Polynomial.C c * Polynomial.X ^ k * f : F[X][Y]).coeff n ≠ 0 :=
    Polynomial.mem_support_iff.mp hn
  have hcoeff_eq :
      (Polynomial.C c * Polynomial.X ^ k * f : F[X][Y]).coeff n =
        (if k ≤ n then c * f.coeff (n - k) else 0) := by
    rw [show (Polynomial.C c * Polynomial.X ^ k * f : F[X][Y]) =
           Polynomial.C c * (f * Polynomial.X ^ k) by ring]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
    split <;> simp
  by_cases hkn : k ≤ n
  · rw [hcoeff_eq, if_pos hkn] at hcoeff_ne
    have hf_ne : f.coeff (n - k) ≠ 0 := by
      intro h0
      apply hcoeff_ne
      rw [h0, mul_zero]
    have hn_k_in : n - k ∈ f.support := Polynomial.mem_support_iff.mpr hf_ne
    have hf_bound := hf (n - k) hn_k_in
    rw [hcoeff_eq, if_pos hkn]
    have hdeg : (c * f.coeff (n - k)).natDegree ≤ c.natDegree + (f.coeff (n - k)).natDegree :=
      Polynomial.natDegree_mul_le
    have hsplit : n = k + (n - k) := (Nat.add_sub_cancel' hkn).symm
    have hgoal :
        n * (D + 1 - Bivariate.natDegreeY H) + (c * f.coeff (n - k)).natDegree ≤
          k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree + b := by
      have h1 :
          n * (D + 1 - Bivariate.natDegreeY H) + (c * f.coeff (n - k)).natDegree ≤
            n * (D + 1 - Bivariate.natDegreeY H) +
              (c.natDegree + (f.coeff (n - k)).natDegree) :=
        Nat.add_le_add_left hdeg _
      have h2 :
          n * (D + 1 - Bivariate.natDegreeY H) +
              (c.natDegree + (f.coeff (n - k)).natDegree) =
            k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree +
              ((n - k) * (D + 1 - Bivariate.natDegreeY H) +
                (f.coeff (n - k)).natDegree) := by
        have hnk : k + (n - k) = n := Nat.add_sub_cancel' hkn
        conv_lhs => rw [hsplit, Nat.add_mul]
        rw [show k + (n - k) - k = n - k from by omega]
        ring
      rw [h2] at h1
      exact h1.trans (Nat.add_le_add_left hf_bound _)
    exact hgoal
  · rw [hcoeff_eq, if_neg hkn] at hcoeff_ne
    exact (hcoeff_ne rfl).elim

/-- The `natDegree` of `H_tilde' H` matches that of `H` when `0 < H.natDegree`. -/
lemma natDegree_H_tilde' {H : F[X][Y]} (hH : 0 < H.natDegree) :
    (H_tilde' H).natDegree = H.natDegree := by
  classical
  rw [H_tilde', if_neg (Nat.ne_of_gt hH)]
  have hsum_deg :
      (∑ i ∈ Finset.range H.natDegree,
          Polynomial.C (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)) *
            Polynomial.X ^ i : F[X][Y]).degree < (H.natDegree : WithBot ℕ) :=
    (Polynomial.degree_sum_le _ _).trans_lt <|
      (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr <| by
        intro i hi
        exact (Polynomial.degree_C_mul_X_pow_le i _).trans_lt
          (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hi))
  rw [show (Polynomial.X ^ H.natDegree +
        ∑ i ∈ Finset.range H.natDegree,
          Polynomial.C (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)) *
            Polynomial.X ^ i : F[X][Y]) =
      (∑ i ∈ Finset.range H.natDegree,
          Polynomial.C (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)) *
            Polynomial.X ^ i) + Polynomial.X ^ H.natDegree by ring]
  have hX_deg : (Polynomial.X ^ H.natDegree : F[X][Y]).degree = (H.natDegree : WithBot ℕ) :=
    Polynomial.degree_X_pow _
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [Polynomial.degree_add_eq_right_of_degree_lt (hsum_deg.trans_eq hX_deg.symm), hX_deg]

/-- The canonical representative has `Y`-degree strictly smaller than `H`. -/
lemma canonicalRepOf𝒪_natDegree_lt_H {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    (canonicalRepOf𝒪 hH β).natDegree < H.natDegree := by
  classical
  by_cases hβ : canonicalRepOf𝒪 hH β = 0
  · simp [hβ, hH]
  · have hdeg := canonicalRepOf𝒪_degree_lt hH β
    have hq_ne : H_tilde' H ≠ 0 := (H_tilde'_monic H hH).ne_zero
    rw [Polynomial.degree_eq_natDegree hβ, Polynomial.degree_eq_natDegree hq_ne] at hdeg
    exact_mod_cast (by simpa [natDegree_H_tilde' hH] using hdeg)

omit [IsDomain F] in
/-- The `Λ`-weight of `H_tilde' H` is bounded by `d_H · m`, where `d_H = H.natDegree`. -/
lemma weight_Λ_H_tilde'_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    weight_Λ (H_tilde' H) H D ≤
      (WithBot.some (H.natDegree * (D + 1 - Bivariate.natDegreeY H)) : WithBot ℕ) := by
  classical
  have hbY : Bivariate.natDegreeY H = H.natDegree := rfl
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
  have hH_in : H.natDegree ∈ H.support :=
    Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hH_ne)
  have hd_le_D : H.natDegree ≤ D := by
    have : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hH_in
    omega
  rw [H_tilde', if_neg (Nat.ne_of_gt hH)]
  refine (weight_Λ_add_le _ _ _ _).trans ?_
  refine max_le ?_ ?_
  · -- weight_Λ Y^d ≤ d · m
    refine (weight_Λ_X_pow_le H D _).trans ?_
    rw [WithBot.coe_le_coe]
  · -- weight_Λ (∑ ... · Y^i) ≤ d · m
    refine (weight_Λ_sum_le _ _ _ _).trans ?_
    refine Finset.sup_le (fun i hi => ?_)
    have hi_lt : i < H.natDegree := Finset.mem_range.mp hi
    refine (weight_Λ_C_mul_X_pow_le H D _ _).trans ?_
    -- Goal: WithBot.some (i·m + (H.coeff i · W^(d-1-i)).natDegree) ≤ WithBot.some (d·m)
    rw [WithBot.coe_le_coe]
    rw [hbY]
    have hcoeff_natDeg :
        (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
          (D - i) + (H.natDegree - 1 - i) * (D - H.natDegree) := by
      have h1 :
          (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
            (H.coeff i).natDegree +
              (H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree :=
        Polynomial.natDegree_mul_le
      have h2 :
          (H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
            (H.natDegree - 1 - i) * (H.coeff H.natDegree).natDegree :=
        Polynomial.natDegree_pow_le
      have hi_deg : (H.coeff i).natDegree ≤ D - i :=
        natDegree_coeff_le_of_totalDegree_le H hD i
      have hd_deg : (H.coeff H.natDegree).natDegree ≤ D - H.natDegree :=
        natDegree_coeff_le_of_totalDegree_le H hD H.natDegree
      calc (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree
          ≤ (H.coeff i).natDegree +
              (H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree := h1
        _ ≤ (D - i) + (H.natDegree - 1 - i) * (H.coeff H.natDegree).natDegree := by
            exact Nat.add_le_add hi_deg h2
        _ ≤ (D - i) + (H.natDegree - 1 - i) * (D - H.natDegree) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ hd_deg) _
    -- numeric bound: i·m + (D-i) + (d-1-i)(D-d) = d·m
    have hadd : i * (D + 1 - H.natDegree) +
        (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
          i * (D + 1 - H.natDegree) +
            ((D - i) + (H.natDegree - 1 - i) * (D - H.natDegree)) :=
      Nat.add_le_add_left hcoeff_natDeg _
    refine hadd.trans ?_
    -- Numeric identity: i*(D+1-d) + (D-i) + (d-1-i)(D-d) = d*(D+1-d)
    have hkey : i * (D + 1 - H.natDegree) +
        ((D - i) + (H.natDegree - 1 - i) * (D - H.natDegree)) =
        H.natDegree * (D + 1 - H.natDegree) := by
      have hi_le : i ≤ H.natDegree - 1 := by omega
      have hi_le_D : i ≤ D := by omega
      have hd_le_D1 : H.natDegree ≤ 1 + D := by omega
      have hd_le_D' : H.natDegree ≤ D + 1 := by omega
      zify [hd_le_D, hd_le_D', hi_le, hi_le_D, hH]
      ring
    omega

omit [IsDomain F] in
/-- One reduction step in `modByMonic` does not increase `Λ`-weight: subtracting
`C(p.leadingCoeff) · Y^(p.natDegree - d_H) · H_tilde' H` from `p` keeps the weight bounded by
`Λ(p)`. -/
lemma weight_Λ_sub_leadingCoeff_mul_H_tilde'_le {p H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hp_deg : H.natDegree ≤ p.natDegree) :
    weight_Λ (p - Polynomial.C p.leadingCoeff *
        Polynomial.X ^ (p.natDegree - H.natDegree) * H_tilde' H) H D ≤
      weight_Λ p H D := by
  classical
  refine (weight_Λ_sub_le _ _ _ _).trans ?_
  refine max_le le_rfl ?_
  refine (weight_Λ_C_mul_X_pow_mul_le (weight_Λ_H_tilde'_le hD hH)).trans ?_
  by_cases hp : p = 0
  · subst hp
    simp at hp_deg
    omega
  · have hp_lead_ne : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have hp_in : p.natDegree ∈ p.support := Polynomial.mem_support_iff.mpr hp_lead_ne
    refine le_trans ?_ (le_weight_Λ_of_mem_support hp_in)
    rw [WithBot.coe_le_coe]
    change (p.natDegree - H.natDegree) * (D + 1 - Bivariate.natDegreeY H) +
        (p.coeff p.natDegree).natDegree + H.natDegree * (D + 1 - Bivariate.natDegreeY H) ≤
        p.natDegree * (D + 1 - Bivariate.natDegreeY H) + (p.coeff p.natDegree).natDegree
    have hsum : (p.natDegree - H.natDegree) + H.natDegree = p.natDegree := by omega
    have hadd_mul :
        (p.natDegree - H.natDegree) * (D + 1 - Bivariate.natDegreeY H) +
            H.natDegree * (D + 1 - Bivariate.natDegreeY H) =
          p.natDegree * (D + 1 - Bivariate.natDegreeY H) := by
      rw [← Nat.add_mul, hsum]
    linarith [hadd_mul]

/-- Reduction modulo `H_tilde' H` does not increase `Λ`-weight. -/
lemma weight_Λ_modByMonic_H_tilde'_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    ∀ p : F[X][Y], weight_Λ (p %ₘ H_tilde' H) H D ≤ weight_Λ p H D
  | p => by
      classical
      have hq : (H_tilde' H).Monic := H_tilde'_monic H hH
      unfold Polynomial.modByMonic Polynomial.divModByMonicAux
      rw [dif_pos hq]
      by_cases h : (H_tilde' H).degree ≤ p.degree ∧ p ≠ 0
      · have _wf := Polynomial.div_wf_lemma h hq
        simp only [ne_eq, dite_eq_ite, ge_iff_le, p, h]
        let z := Polynomial.C p.leadingCoeff *
          Polynomial.X ^ (p.natDegree - (H_tilde' H).natDegree)
        have ih := weight_Λ_modByMonic_H_tilde'_le hD hH (p - H_tilde' H * z)
        have ih' :
            weight_Λ ((Polynomial.divModByMonicAux (p - H_tilde' H * z) hq).2) H D ≤
              weight_Λ (p - H_tilde' H * z) H D := by
          simpa [Polynomial.modByMonic, hq, z] using ih
        have hqnat : (H_tilde' H).natDegree = H.natDegree := natDegree_H_tilde' hH
        have hp_deg : H.natDegree ≤ p.natDegree := by
          have hdeg := h.1
          rw [Polynomial.degree_eq_natDegree h.2, Polynomial.degree_eq_natDegree hq.ne_zero]
            at hdeg
          exact_mod_cast (by simpa [hqnat] using hdeg)
        have hstep0 :=
          weight_Λ_sub_leadingCoeff_mul_H_tilde'_le (p := p) (H := H) hD hH hp_deg
        have hstep : weight_Λ (p - H_tilde' H * z) H D ≤ weight_Λ p H D := by
          have hz :
              z = Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - H.natDegree) := by
            simp [z, hqnat]
          rw [hz]
          convert hstep0 using 1
          ring_nf
        exact ih'.trans hstep
      · simp only [ne_eq, dite_eq_ite, ge_iff_le, p, h]
        exact le_rfl
termination_by p => p

/-- The `𝒪`-weight of a quotient constructor is bounded by any representative's `Λ`-weight. -/
lemma weight_Λ_over_𝒪_mk_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) (p : F[X][Y]) :
    weight_Λ_over_𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) D ≤
      weight_Λ p H D := by
  rw [weight_Λ_over_𝒪_mk]
  exact weight_Λ_modByMonic_H_tilde'_le hD hH p

/-- The set `S_β` from the statement of Lemma A.1 in Appendix A of [BCIKS20].
Note: Here `F[X][Y]` is `F[Z][T]`. -/
noncomputable def S_β {H : F[X][Y]} (β : 𝒪 H) : Set F :=
  {z : F | ∃ root : rationalRoot (H_tilde' H) z, (π_z z root) β = 0}

omit [IsDomain F] in
/-- The rational substitution `π_z` can be computed on the canonical representative. -/
lemma π_z_eq_eval_canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree)
    (z : F) (root : rationalRoot (H_tilde' H) z) (β : 𝒪 H) :
    (π_z z root) β = Polynomial.evalEvalRingHom z root.1 (canonicalRepOf𝒪 hH β) := by
  conv_lhs => rw [← mk_canonicalRepOf𝒪 hH β]
  rfl

end

section LemmaA1

variable {F : Type} [Field F]

/-- The statement of Lemma A.1 in Appendix A.3 of [BCIKS20]. -/
lemma lemmaA1_embedding_eq_zero_of_many_rational_roots {H : F[X][Y]}
    [hHirreducible : Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ)
    (hD : D ≥ Bivariate.totalDegree H)
    (S_β_card : Set.ncard (S_β β) > (weight_Λ_over_𝒪 hH β D) * H.natDegree) :
  embeddingOf𝒪Into𝕃 _ β = 0 := by sorry

end LemmaA1

section

variable {F : Type} [CommRing F] [IsDomain F]

/-- The embedding of the coefficients of a bivariate polynomial into the bivariate polynomial ring
with rational coefficients. -/
noncomputable def coeffAsRatFunc : F[X] →+* Polynomial (RatFunc F) :=
  RingHom.comp bivPolyHom Polynomial.C

/-- The embedding of coefficient polynomials into the function field `𝕃`. -/
noncomputable def liftToFunctionField {H : F[X][Y]} : F[X] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) coeffAsRatFunc

/-- The embedding of bivariate polynomials into the function field `𝕃`. -/
noncomputable def liftBivariate {H : F[X][Y]} : F[X][Y] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) bivPolyHom

/-- The image of the polynomial variable `T` in the function field `𝕃 H`. -/
noncomputable def functionFieldT {H : F[X][Y]} : 𝕃 H :=
  Ideal.Quotient.mk (Ideal.span {H_tilde H}) Polynomial.X

/-- Quotient constructors in `𝒪` embed by applying the bivariate lift. -/
@[simp]
lemma embeddingOf𝒪Into𝕃_mk (H : F[X][Y]) (p : F[X][Y]) :
    embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) =
      liftBivariate (H := H) p := by
  rfl

/-- Every bivariate polynomial representative gives a regular element of the function field. -/
lemma regular_liftBivariate (H : F[X][Y]) (p : F[X][Y]) :
    ∃ pre : 𝒪 H, embeddingOf𝒪Into𝕃 H pre = liftBivariate (H := H) p :=
  ⟨Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p, by simp⟩

/-- Bivariate-polynomial images are regular elements of the function field. -/
lemma regularElementsSet_liftBivariate (H : F[X][Y]) (p : F[X][Y]) :
    liftBivariate (H := H) p ∈ regularElementsSet H := by
  rcases regular_liftBivariate H p with ⟨pre, hpre⟩
  exact ⟨pre, hpre.symm⟩

/-- Coefficients embedded into `𝕃` are regular elements. -/
lemma regular_liftToFunctionField (H : F[X][Y]) (p : F[X]) :
    ∃ pre : 𝒪 H, embeddingOf𝒪Into𝕃 H pre = liftToFunctionField (H := H) p :=
  regular_liftBivariate H (Polynomial.C p)

/-- Coefficient-polynomial images are regular elements of the function field. -/
lemma regularElementsSet_liftToFunctionField (H : F[X][Y]) (p : F[X]) :
    liftToFunctionField (H := H) p ∈ regularElementsSet H := by
  simpa using regularElementsSet_liftBivariate H (Polynomial.C p)

/-- Nonzero coefficient polynomials remain nonzero after embedding into the function field. -/
lemma liftToFunctionField_ne_zero {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {p : F[X]} (hp : p ≠ 0) :
    liftToFunctionField (H := H) p ≠ 0 := by
  intro hzero
  have hmem : coeffAsRatFunc p ∈ Ideal.span ({H_tilde H} : Set (Polynomial (RatFunc F))) := by
    simpa [liftToFunctionField] using (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  rw [Ideal.mem_span_singleton] at hmem
  have hp_map : univPolyHom (F := F) p ≠ 0 := by
    intro hp_zero
    exact hp (univPolyHom_injective (F := F) (by simpa using hp_zero))
  have hunit : IsUnit (coeffAsRatFunc p) := by
    have hunitC : IsUnit (Polynomial.C (univPolyHom (F := F) p) :
        Polynomial (RatFunc F)) :=
      Polynomial.isUnit_C.mpr (Ne.isUnit hp_map)
    simpa only [coeffAsRatFunc, RingHom.comp_apply, ToRatFunc.bivPolyHom,
      Polynomial.coe_mapRingHom, Polynomial.map_C] using hunitC
  exact (irreducibleHTildeOfIrreducible_of_natDegree_pos H_natDegree_pos.out
    H_irreducible.out).not_dvd_isUnit hunit hmem

/-- The leading coefficient `W` of a positive-`Y`-degree `H` is nonzero in the function field. -/
lemma liftToFunctionField_leadingCoeff_ne_zero {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)] :
    liftToFunctionField (H := H) H.leadingCoeff ≠ 0 := by
  exact liftToFunctionField_ne_zero
    (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out))

/-- If `q ∣ p` in `F[X]`, then `p / q` is regular after embedding into `𝕃`. -/
lemma regularElementsSet_liftToFunctionField_div_of_dvd {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {p q : F[X]} (hq : q ≠ 0) (hdiv : q ∣ p) :
    liftToFunctionField (H := H) p / liftToFunctionField (H := H) q ∈ regularElementsSet H := by
  rcases hdiv with ⟨r, rfl⟩
  have hq_lift : liftToFunctionField (H := H) q ≠ 0 := liftToFunctionField_ne_zero hq
  have heq :
      liftToFunctionField (H := H) (q * r) / liftToFunctionField (H := H) q =
        liftToFunctionField (H := H) r := by
    rw [map_mul]
    field_simp [hq_lift]
  rw [heq]
  exact regularElementsSet_liftToFunctionField H r

/-- If `W = H.leadingCoeff` divides `p`, then `p / W` is regular after embedding into `𝕃`. -/
lemma regularElementsSet_liftToFunctionField_div_leadingCoeff_of_dvd {F : Type} [Field F]
    {H : F[X][Y]} [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] {p : F[X]}
    (hdiv : H.leadingCoeff ∣ p) :
    liftToFunctionField (H := H) p / liftToFunctionField (H := H) H.leadingCoeff ∈
      regularElementsSet H := by
  exact regularElementsSet_liftToFunctionField_div_of_dvd
    (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out))
    hdiv

private lemma mul_pow_mul_div_pow_eq_lower {K : Type} [Field K] {W T a : K}
    (hW : W ≠ 0) {k i : ℕ} (hi : i ≤ k) :
    W ^ k * (a * (T / W) ^ i) = a * (T ^ i * W ^ (k - i)) := by
  rw [div_pow]
  have hk : k = k - i + i := (Nat.sub_add_cancel hi).symm
  calc
    W ^ k * (a * (T ^ i / W ^ i)) = a * (T ^ i * (W ^ k / W ^ i)) := by
      ring
    _ = a * (T ^ i * W ^ (k - i)) := by
      rw [hk, pow_add]
      field_simp [hW]
      have hsub : k - i + i - i = k - i := by omega
      rw [hsub]

private lemma mul_pow_mul_div_pow_succ_eq_top {K : Type} [Field K] {W T a : K}
    (hW : W ≠ 0) (k : ℕ) :
    W ^ k * (a * (T / W) ^ (k + 1)) = (a / W) * T ^ (k + 1) := by
  rw [div_pow, pow_succ]
  field_simp [hW]
  ring

/-- Clearing denominators in `W^k · P(T/W)` as an explicit sum: if `P.natDegree ≤ k + 1`, then
`W^k * eval₂ lift (T/W) P` decomposes into a low-degree polynomial sum plus a single
`(P.coeff(k+1)/W) · T^(k+1)` term. The divisibility `W ∣ P.coeff(k+1)` is not needed here -
the formula holds in `𝕃 H` directly via field division. -/
lemma W_pow_mul_eval₂_div_eq_sum {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {P : F[X][Y]} {k : ℕ} (hP : P.natDegree ≤ k + 1) :
    liftToFunctionField (H := H) H.leadingCoeff ^ k *
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) P =
      (∑ i ∈ Finset.range (k + 1),
          liftToFunctionField (H := H) (P.coeff i) *
            (functionFieldT (H := H) ^ i *
              liftToFunctionField (H := H) H.leadingCoeff ^ (k - i))) +
        (liftToFunctionField (H := H) (P.coeff (k + 1)) /
            liftToFunctionField (H := H) H.leadingCoeff) *
          functionFieldT (H := H) ^ (k + 1) := by
  set W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff with hW_def
  set T : 𝕃 H := functionFieldT (H := H) with hT_def
  have hW : W ≠ 0 := by
    simpa [W] using (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  have hP_lt : P.natDegree < k + 2 := by omega
  rw [Polynomial.eval₂_eq_sum_range' liftToFunctionField hP_lt (T / W)]
  rw [Finset.mul_sum]
  rw [show k + 2 = k + 1 + 1 by omega, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi_le : i ≤ k := by
      have hi_lt := Finset.mem_range.mp hi
      omega
    exact mul_pow_mul_div_pow_eq_lower (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff i)) hW hi_le
  · exact mul_pow_mul_div_pow_succ_eq_top (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff (k + 1))) hW k

/-- The bivariate variable maps to the function-field variable `T`. -/
@[simp]
lemma liftBivariate_X {H : F[X][Y]} :
    liftBivariate (H := H) (Polynomial.X : F[X][Y]) = functionFieldT (H := H) := by
  simp [liftBivariate, functionFieldT, bivPolyHom]

/-- The function-field variable `T` is regular. -/
lemma regularElementsSet_functionFieldT (H : F[X][Y]) :
    functionFieldT (H := H) ∈ regularElementsSet H := by
  simpa using regularElementsSet_liftBivariate H (Polynomial.X : F[X][Y])

/-- A linear polynomial evaluated at `T / W` is regular when its linear coefficient is divisible by
`W = H.leadingCoeff`. -/
lemma regularElementsSet_eval₂_linear_of_coeff_one_dvd {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {P : F[X][Y]} (hP : P.natDegree ≤ 1) (hdiv : H.leadingCoeff ∣ P.coeff 1) :
    Polynomial.eval₂ liftToFunctionField
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) P ∈
      regularElementsSet H := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hP]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X]
  have hterm :
      liftToFunctionField (H := H) (P.coeff 1) *
          (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) =
        (liftToFunctionField (H := H) (P.coeff 1) /
            liftToFunctionField (H := H) H.leadingCoeff) * functionFieldT (H := H) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [hterm]
  exact regularElementsSet_add
    (regularElementsSet_mul
      (regularElementsSet_liftToFunctionField_div_leadingCoeff_of_dvd hdiv)
      (regularElementsSet_functionFieldT H))
    (regularElementsSet_liftToFunctionField H (P.coeff 0))

/-- Clearing denominators in `P(T / W)`: if `P` has degree at most `k + 1` and its top
coefficient is divisible by `W = H.leadingCoeff`, then `W^k * P(T/W)` is regular. -/
lemma regularElementsSet_mul_pow_eval₂_div_of_natDegree_le_succ_of_coeff_succ_dvd
    {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {P : F[X][Y]} {k : ℕ} (hP : P.natDegree ≤ k + 1)
    (hdiv : H.leadingCoeff ∣ P.coeff (k + 1)) :
    liftToFunctionField (H := H) H.leadingCoeff ^ k *
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) P ∈
      regularElementsSet H := by
  let W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff
  let T : 𝕃 H := functionFieldT (H := H)
  have hW : W ≠ 0 := by
    simpa [W] using (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  have hP_lt : P.natDegree < k + 2 := by omega
  change W ^ k * Polynomial.eval₂ liftToFunctionField (T / W) P ∈ regularElementsSet H
  rw [Polynomial.eval₂_eq_sum_range' liftToFunctionField hP_lt (T / W)]
  rw [Finset.mul_sum]
  rw [show k + 2 = k + 1 + 1 by omega, Finset.sum_range_succ]
  refine regularElementsSet_add ?_ ?_
  · refine regularElementsSet_sum (Finset.range (k + 1)) ?_
    intro i hi
    have hi_lt : i < k + 1 := Finset.mem_range.mp hi
    have hi_le : i ≤ k := by omega
    rw [mul_pow_mul_div_pow_eq_lower (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff i)) hW hi_le]
    exact regularElementsSet_mul
      (regularElementsSet_liftToFunctionField H (P.coeff i))
      (regularElementsSet_mul
        (by simpa [T] using regularElementsSet_pow (regularElementsSet_functionFieldT H) i)
        (by
          simpa [W] using
            regularElementsSet_pow
              (regularElementsSet_liftToFunctionField H H.leadingCoeff) (k - i)))
  · rw [mul_pow_mul_div_pow_succ_eq_top (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff (k + 1))) hW k]
    exact regularElementsSet_mul
      (by
        simpa [W] using
          regularElementsSet_liftToFunctionField_div_leadingCoeff_of_dvd (H := H) hdiv)
      (by simpa [T] using regularElementsSet_pow (regularElementsSet_functionFieldT H) (k + 1))

/-- Constant bivariate polynomials map through the coefficient embedding. -/
@[simp]
lemma liftBivariate_C {H : F[X][Y]} (p : F[X]) :
    liftBivariate (H := H) (Polynomial.C p : F[X][Y]) = liftToFunctionField (H := H) p := by
  rfl

/-- The embedding of scalars into the function field `𝕃`. -/
noncomputable def fieldTo𝕃 {H : F[X][Y]} : F →+* 𝕃 H :=
  RingHom.comp liftToFunctionField Polynomial.C

/-- View a bivariate polynomial as a power series over `𝕃 H` by lifting its coefficients. -/
noncomputable def polyToPowerSeries𝕃 (H : F[X][Y]) (P : F[X][Y]) : PowerSeries (𝕃 H) :=
  PowerSeries.mk <| fun n => liftToFunctionField (P.coeff n)


end

noncomputable section

namespace ClaimA2

variable {F : Type} [Field F] {R : F[X][X][X]} {H : F[X][Y]}
  [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]

/-! ### Claim A.2 hypotheses and derivative setup -/

/-- The algebraic hypotheses for Claim A.2 from Appendix A.4 of [BCIKS20], after specializing
`R` at `X = x₀`. -/
structure Hypotheses (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) : Prop where
  dvd_evalX : H ∣ Bivariate.evalX (Polynomial.C x₀) R
  separable_evalX : (Bivariate.evalX (Polynomial.C x₀) R).Separable

private lemma evalX_natDegree_le {K : Type} [CommSemiring K] (x : K) (P : K[X][Y]) :
    (Bivariate.evalX x P).natDegree ≤ P.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hcoeff : P.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hn
  simp [Bivariate.evalX_eq_map, Polynomial.coeff_map, hcoeff]

lemma evalX_ne_zero_of_Hypotheses {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    Bivariate.evalX (Polynomial.C x₀) R ≠ 0 :=
  hHyp.separable_evalX.ne_zero

lemma H_natDegree_le_R_natDegree_of_Hypotheses {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.natDegree ≤ R.natDegree :=
  (Polynomial.natDegree_le_of_dvd hHyp.dvd_evalX (evalX_ne_zero_of_Hypotheses hHyp)).trans
    (evalX_natDegree_le (Polynomial.C x₀) R)

lemma derivative_evalX_coeff (x₀ : F) (R : F[X][X][Y]) (i : ℕ) :
    (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i =
      (Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1) * ((i + 1 : ℕ) : F[X]) := by
  have hsucc_cast : (((i : ℕ) : F[X][X]) + 1) = ((i + 1 : ℕ) : F[X][X]) := by
    rw [← Nat.cast_one (R := F[X][X]), ← Nat.cast_add]
  calc
    (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i =
        ((R.derivative).coeff i).eval (Polynomial.C x₀) := by
      simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
    _ = (R.coeff (i + 1) * ((i + 1 : ℕ) : F[X][X])).eval (Polynomial.C x₀) := by
      rw [Polynomial.coeff_derivative, hsucc_cast]
    _ = (Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1) * ((i + 1 : ℕ) : F[X]) := by
      simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]

lemma natDegree_derivative_evalX_coeff_le (x₀ : F) (R : F[X][X][Y]) {D i : ℕ}
    (hD : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D) :
    ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i).natDegree ≤ D - (i + 1) := by
  rw [derivative_evalX_coeff]
  calc
    (((Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1) * ((i + 1 : ℕ) : F[X])).natDegree)
        ≤ ((Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1)).natDegree +
            (((i + 1 : ℕ) : F[X]).natDegree) := Polynomial.natDegree_mul_le
    _ = ((Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1)).natDegree := by
        rw [← Polynomial.C_eq_natCast, Polynomial.natDegree_C, Nat.add_zero]
    _ ≤ D - (i + 1) :=
        natDegree_coeff_le_of_totalDegree_le (Bivariate.evalX (Polynomial.C x₀) R) hD (i + 1)

/-- The leading coefficient `W` of `H` divides the leading coefficient of `R(x₀,Y,Z)`. -/
lemma leadingCoeff_dvd_evalX_leadingCoeff {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.leadingCoeff ∣ (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff := by
  rcases hHyp.dvd_evalX with ⟨q, hq⟩
  refine ⟨q.leadingCoeff, ?_⟩
  calc
    (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff = (H * q).leadingCoeff := by rw [hq]
    _ = H.leadingCoeff * q.leadingCoeff := Polynomial.leadingCoeff_mul H q

/-- The leading coefficient `W` of `H` divides the coefficient of `Y ^ R.natDegree` in
`R(x₀,Y,Z)`. If specialization lowers the `Y`-degree, that coefficient is zero. -/
lemma leadingCoeff_dvd_evalX_coeff_natDegree {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.leadingCoeff ∣ (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R
  have hdeg : P.natDegree ≤ R.natDegree := evalX_natDegree_le (Polynomial.C x₀) R
  by_cases hEq : P.natDegree = R.natDegree
  · simpa [P, hEq.symm] using leadingCoeff_dvd_evalX_leadingCoeff hHyp
  · have hlt : P.natDegree < R.natDegree := lt_of_le_of_ne hdeg hEq
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    exact dvd_zero H.leadingCoeff

/-- The leading coefficient `W` of `H` divides the top possible coefficient of
`∂R/∂Y(x₀,Y,Z)`. This is the coefficient that remains after multiplying `ζ` by `W^(d-2)`. -/
lemma leadingCoeff_dvd_evalX_derivative_coeff_pred {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.leadingCoeff ∣
      (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) := by
  by_cases hR : R.natDegree = 0
  · have hderiv : R.derivative = 0 := Polynomial.derivative_of_natDegree_zero hR
    rw [hderiv]
    exact ⟨0, by simp [Bivariate.evalX_eq_map]⟩
  · have hsucc : R.natDegree - 1 + 1 = R.natDegree :=
      Nat.sub_add_cancel (Nat.pos_of_ne_zero hR)
    have hsucc_cast : (((R.natDegree - 1 : ℕ) : F[X][X]) + 1) =
        (R.natDegree : F[X][X]) := by
      rw [← Nat.cast_one (R := F[X][X])]
      rw [← Nat.cast_add, hsucc]
    have hcoeff :
        (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) =
          (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree *
            (R.natDegree : F[X]) := by
      calc
        (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) =
            ((R.derivative).coeff (R.natDegree - 1)).eval (Polynomial.C x₀) := by
          simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
        _ = (R.coeff R.natDegree * (R.natDegree : F[X][X])).eval (Polynomial.C x₀) := by
          rw [Polynomial.coeff_derivative, hsucc, hsucc_cast]
        _ = (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree *
            (R.natDegree : F[X]) := by
          simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
    rcases leadingCoeff_dvd_evalX_coeff_natDegree hHyp with ⟨q, hq⟩
    refine ⟨q * (R.natDegree : F[X]), ?_⟩
    rw [hcoeff, hq]
    ring

/-- The element `ζ` from Appendix A.4 of [BCIKS20]. -/
def ζ (R : F[X][X][Y]) (x₀ : F) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  let T : 𝕃 H := functionFieldT (H := H)
  Polynomial.eval₂ liftToFunctionField (T / W)
    (Bivariate.evalX (Polynomial.C x₀) R.derivative)

/-- If the derivative specialization is constant in the function-field variable, then `ζ` is
regular. -/
lemma ζ_regular_of_derivative_evalX_eq_C (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)] {p : F[X]}
    (hp : Bivariate.evalX (Polynomial.C x₀) R.derivative = Polynomial.C p) :
    ζ R x₀ H ∈ regularElementsSet H := by
  rw [ζ, hp]
  simp only [Polynomial.eval₂_C]
  exact regularElementsSet_liftToFunctionField H p

/-- If `R` has `Y`-degree at most one, then the specialized derivative is constant. -/
lemma derivative_evalX_eq_C_of_natDegree_le_one
    (x₀ : F) (R : F[X][X][Y]) (hR : R.natDegree ≤ 1) :
    ∃ p : F[X], Bivariate.evalX (Polynomial.C x₀) R.derivative = Polynomial.C p := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  refine ⟨P.coeff 0, ?_⟩
  have hderiv : R.derivative.natDegree ≤ 0 := by
    calc
      R.derivative.natDegree ≤ R.natDegree - 1 := Polynomial.natDegree_derivative_le R
      _ = 0 := by omega
  have hP : P.natDegree ≤ 0 :=
    (evalX_natDegree_le (Polynomial.C x₀) R.derivative).trans hderiv
  exact Polynomial.eq_C_of_natDegree_le_zero hP

/-- In the constant-derivative, low-`Y`-degree case, the `ξ` regularity witness is explicit. -/
lemma ξ_regular_of_derivative_evalX_eq_C_of_natDegree_le_one
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)]
    {p : F[X]} (hp : Bivariate.evalX (Polynomial.C x₀) R.derivative = Polynomial.C p)
    (hR : R.natDegree ≤ 1) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  rcases ζ_regular_of_derivative_evalX_eq_C x₀ R H hp with ⟨pre, hpre⟩
  refine ⟨pre, ?_⟩
  have hd : R.natDegree - 2 = 0 := by omega
  simpa [hd] using hpre.symm

/-- If `R` has `Y`-degree at most one, the regularity statement for `ξ` follows from the
constant-derivative case. -/
lemma ξ_regular_of_natDegree_le_one
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hR : R.natDegree ≤ 1) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  rcases derivative_evalX_eq_C_of_natDegree_le_one x₀ R hR with ⟨p, hp⟩
  exact ξ_regular_of_derivative_evalX_eq_C_of_natDegree_le_one x₀ R H hp hR

/-- In the quadratic case, `ξ = ζ` is regular by clearing the single denominator with the
divisibility of the top derivative coefficient. -/
lemma ξ_regular_of_natDegree_eq_two
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (hR : R.natDegree = 2) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  have hP : P.natDegree ≤ 1 := by
    calc
      P.natDegree ≤ R.derivative.natDegree := evalX_natDegree_le (Polynomial.C x₀) R.derivative
      _ ≤ R.natDegree - 1 := Polynomial.natDegree_derivative_le R
      _ = 1 := by omega
  have hdiv : H.leadingCoeff ∣ P.coeff 1 := by
    simpa [P, hR] using leadingCoeff_dvd_evalX_derivative_coeff_pred hHyp
  have hreg : ζ R x₀ H ∈ regularElementsSet H := by
    simpa [ζ, P] using regularElementsSet_eval₂_linear_of_coeff_one_dvd (H := H) hP hdiv
  rcases hreg with ⟨pre, hpre⟩
  refine ⟨pre, ?_⟩
  have hd : R.natDegree - 2 = 0 := by omega
  simpa [hd] using hpre.symm

/-- Explicit polynomial representative for the regular element `ξ = W^(d-2) · ζ` of Claim A.2.
For `2 ≤ R.natDegree`, this is the polynomial obtained by clearing the single denominator that
appears in `W^(d-2) · ζ`; the divisibility `W ∣ R'(x₀, Z)_{d-1}` is captured implicitly by
Euclidean division in `F[X]`. For `R.natDegree ≤ 1`, the derivative specialization is constant
in `Y`, so we take it as the representative. -/
noncomputable def ξ_pre (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) : F[X][Y] :=
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  let d : ℕ := R.natDegree
  let W : F[X] := H.leadingCoeff
  if 2 ≤ d then
    (∑ i ∈ Finset.range (d - 1),
        Polynomial.C (P.coeff i * W ^ (d - 2 - i)) * Polynomial.X ^ i) +
      Polynomial.C (P.coeff (d - 1) / W) * Polynomial.X ^ (d - 1)
  else
    P

/-- The image of `⟦ξ_pre⟧` in the function field equals `W^(d-2) · ζ`, matching Claim A.2's
algebraic identity. -/
lemma embeddingOf𝒪Into𝕃_mk_ξ_pre (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk _ (ξ_pre x₀ R H) : 𝒪 H) =
      liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2) * ζ R x₀ H := by
  rw [embeddingOf𝒪Into𝕃_mk]
  by_cases hRle : R.natDegree ≤ 1
  · -- d ≤ 1: ξ_pre = R'(x₀, Z), constant in Y; ζ is the lift of that constant.
    rcases derivative_evalX_eq_C_of_natDegree_le_one x₀ R hRle with ⟨p, hp⟩
    have hd2 : R.natDegree - 2 = 0 := by omega
    have hbranch : ¬ 2 ≤ R.natDegree := by omega
    have hξ_pre : ξ_pre x₀ R H = Polynomial.C p := by
      simp [ξ_pre, hbranch, hp]
    rw [hξ_pre, hd2, pow_zero, one_mul, liftBivariate_C]
    change liftToFunctionField (H := H) p =
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
        (Bivariate.evalX (Polynomial.C x₀) R.derivative)
    rw [hp, Polynomial.eval₂_C]
  · have hd2 : 2 ≤ R.natDegree := by omega
    set P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative with hP_def
    set W_poly : F[X] := H.leadingCoeff with hW_poly_def
    have hkk : R.natDegree - 1 = R.natDegree - 2 + 1 := by omega
    have hP_le : P.natDegree ≤ R.natDegree - 2 + 1 := by
      have h1 : P.natDegree ≤ R.derivative.natDegree := evalX_natDegree_le _ R.derivative
      have h2 : R.derivative.natDegree ≤ R.natDegree - 1 := Polynomial.natDegree_derivative_le R
      omega
    have hdiv : W_poly ∣ P.coeff (R.natDegree - 2 + 1) := by
      have h := leadingCoeff_dvd_evalX_derivative_coeff_pred (H := H) hHyp
      rwa [hkk] at h
    have hW_poly_ne : W_poly ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr
        (Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out)
    have hW_ne : (liftToFunctionField (H := H) W_poly : 𝕃 H) ≠ 0 :=
      liftToFunctionField_leadingCoeff_ne_zero (H := H)
    have hξ_pre_eq : ξ_pre x₀ R H =
        (∑ i ∈ Finset.range (R.natDegree - 2 + 1),
            Polynomial.C (P.coeff i * W_poly ^ (R.natDegree - 2 - i)) * Polynomial.X ^ i) +
          Polynomial.C (P.coeff (R.natDegree - 2 + 1) / W_poly) *
            Polynomial.X ^ (R.natDegree - 2 + 1) := by
      simp only [ξ_pre, hd2, ↓reduceIte, ← hP_def, ← hW_poly_def, hkk]
    rw [hξ_pre_eq]
    rw [show (ζ R x₀ H : 𝕃 H) =
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) W_poly) P from rfl]
    rw [W_pow_mul_eval₂_div_eq_sum (H := H) (P := P) (k := R.natDegree - 2) hP_le]
    have hlift_div :
        liftToFunctionField (H := H) (P.coeff (R.natDegree - 2 + 1) / W_poly) =
          liftToFunctionField (H := H) (P.coeff (R.natDegree - 2 + 1)) /
            liftToFunctionField (H := H) W_poly := by
      rw [eq_div_iff hW_ne, ← map_mul, mul_comm,
          EuclideanDomain.mul_div_cancel' hW_poly_ne hdiv]
    simp only [map_add, map_sum, map_mul, map_pow, liftBivariate_C, liftBivariate_X, hlift_div]
    refine congr_arg₂ (· + ·) ?_ rfl
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring

/-- The regular element `ξ = W(Z)^(d-2) * ζ` has a quotient representative in the total Lean
form of Claim A.2 of Appendix A.4 of [BCIKS20].

For `R.natDegree < 2`, the natural-number exponent truncates to zero. The paper's weight
bound is therefore stated separately with the explicit hypothesis `2 ≤ R.natDegree`. -/
lemma ξ_regular (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H :=
  ⟨Ideal.Quotient.mk _ (ξ_pre x₀ R H),
    by simpa using embeddingOf𝒪Into𝕃_mk_ξ_pre x₀ R H hHyp⟩

/-- The regular element `ξ = W(Z)^(d-2) * ζ` used in the Lean version of Claim A.2.

The `Fact` and `Hypotheses` arguments are kept for API compatibility with downstream callers
(`α`, `γ`); they are needed for the embedding equation in `embeddingOf𝒪Into𝕃_ξ`. -/
noncomputable def ξ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [_φ : Fact (Irreducible H)]
    [_H_natDegree_pos : Fact (0 < H.natDegree)] (_hHyp : Hypotheses x₀ R H) : 𝒪 H :=
  Ideal.Quotient.mk _ (ξ_pre x₀ R H)

/-- The defining equation `embedding ξ = W^(d-2) · ζ`, the specialization of
`embeddingOf𝒪Into𝕃_mk_ξ_pre` to `ξ`. -/
lemma embeddingOf𝒪Into𝕃_ξ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp) =
      liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2) * ζ R x₀ H :=
  embeddingOf𝒪Into𝕃_mk_ξ_pre x₀ R H hHyp

/-- The bound of the weight `Λ` of the elements `ξ` as stated in Claim A.2 of Appendix A.4
of [BCIKS20].

The explicit hypothesis `2 ≤ R.natDegree` is needed because the paper uses `W^(d-2)`, while
Lean's natural-number exponent would otherwise totalize the low-degree cases by truncation. -/
lemma ξ_weight_le (x₀ : F) (hH : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    {D : ℕ} (hD_H : D ≥ Bivariate.totalDegree H)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R)) :
    weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D ≤
    WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) := by
  sorry

/-- The exponent of `ξ` in the denominator of the `t`-th Hensel coefficient.

The paper separates `t = 0`, where no `ξ` factor appears, from `t ≥ 1`, where the exponent is
`2*t - 1`. -/
def henselDenominatorExponent (t : ℕ) : ℕ :=
  if t = 0 then 0 else 2 * t - 1

@[simp]
lemma henselDenominatorExponent_zero : henselDenominatorExponent 0 = 0 := by
  simp [henselDenominatorExponent]

@[simp]
lemma henselDenominatorExponent_succ (t : ℕ) :
    henselDenominatorExponent (t + 1) = 2 * (t + 1) - 1 := by
  simp [henselDenominatorExponent]

/-- A total degree for the trivariate polynomial `R`, represented as a polynomial in `Y` with
bivariate coefficients in the `Z` and `X` variables. -/
def trivariateTotalDegree (R : F[X][X][Y]) : ℕ :=
  R.support.sup (fun i => Bivariate.totalDegree (R.coeff i) + i)

/-- Each coefficient of `R` is bounded by `trivariateTotalDegree R`. -/
lemma coeff_totalDegree_add_index_le_trivariateTotalDegree (R : F[X][X][Y]) {i : ℕ}
    (hi : i ∈ R.support) :
    Bivariate.totalDegree (R.coeff i) + i ≤ trivariateTotalDegree R := by
  classical
  unfold trivariateTotalDegree
  exact Finset.le_sup (f := fun i => Bivariate.totalDegree (R.coeff i) + i) hi

/-- A canonical degree bound large enough for both `H` and all coefficients of `R`. -/
def defaultDegreeBound (R : F[X][X][Y]) (H : F[X][Y]) : ℕ :=
  max (Bivariate.totalDegree H) (trivariateTotalDegree R)

lemma defaultDegreeBound_ge_H (R : F[X][X][Y]) (H : F[X][Y]) :
    Bivariate.totalDegree H ≤ defaultDegreeBound R H :=
  le_max_left _ _

lemma defaultDegreeBound_ge_R_coeff (R : F[X][X][Y]) (H : F[X][Y]) {i : ℕ}
    (hi : i ∈ R.support) :
    Bivariate.totalDegree (R.coeff i) + i ≤ defaultDegreeBound R H :=
  (coeff_totalDegree_add_index_le_trivariateTotalDegree R hi).trans (le_max_right _ _)

/-- Coefficients in `F[Z][X]` evaluated as power series over the function field: `Z` is sent to
the function-field coefficient embedding, and `X` is sent to the power-series variable. -/
noncomputable def liftCoeffToPowerSeries (H : F[X][Y]) :
    F[X][X] →+* PowerSeries (𝕃 H) :=
  Polynomial.eval₂RingHom (RingHom.comp PowerSeries.C (liftToFunctionField (H := H)))
    PowerSeries.X

/-- Evaluation of the trivariate polynomial `R(X,Y,Z)` at a power series `Γ` for the `Y`
variable, with the `X` variable interpreted as the power-series variable and `Z` interpreted in
the function field of `H`. -/
noncomputable def evalRAtPowerSeries (H : F[X][Y]) (R : F[X][X][Y])
    (Γ : PowerSeries (𝕃 H)) : PowerSeries (𝕃 H) :=
  Polynomial.eval₂ (liftCoeffToPowerSeries H) Γ R

/-- The coefficient sequence obtained from a candidate sequence of regular numerators. -/
noncomputable def alphaOfNumerators (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (βseq : ℕ → 𝒪 H) (t : ℕ) : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  embeddingOf𝒪Into𝕃 _ (βseq t) /
    (W ^ (t + 1) * (embeddingOf𝒪Into𝕃 _ (ξ x₀ R H hHyp)) ^
      henselDenominatorExponent t)

/-- The power series induced by a candidate sequence of regular numerators. -/
noncomputable def gammaOfNumerators (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (βseq : ℕ → 𝒪 H) :
    PowerSeries (𝕃 H) :=
  let subst (t : ℕ) : 𝕃 H :=
    match t with
    | 0 => fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0
  PowerSeries.subst (PowerSeries.mk subst)
    (PowerSeries.mk (alphaOfNumerators x₀ R H hHyp βseq))

/-- A numerator sequence has the semantic content required by Claim A.2: it gives the Hensel
lift starting at `T / W`, and the induced power series is a root of `R(X,Y,Z)`. -/
def IsHenselNumeratorSequence (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (βseq : ℕ → 𝒪 H) : Prop :=
  alphaOfNumerators x₀ R H hHyp βseq 0 =
      functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff ∧
    evalRAtPowerSeries H R (gammaOfNumerators x₀ R H hHyp βseq) = 0

theorem evalX_totalDegree_le_of_coeff_bound (x₀ : F) (R : F[X][X][Y]) {D : ℕ}
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D) :
    Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D := by
  classical
  unfold Bivariate.totalDegree
  refine Finset.sup_le ?_
  intro i hi
  have hcoeff_eval_ne : (Bivariate.evalX (Polynomial.C x₀) R).coeff i ≠ 0 :=
    Polynomial.mem_support_iff.mp hi
  have hcoeff_eq : (Bivariate.evalX (Polynomial.C x₀) R).coeff i =
      (R.coeff i).eval (Polynomial.C x₀) := by
    simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
  have hRcoeff_ne : R.coeff i ≠ 0 := by
    intro h0
    apply hcoeff_eval_ne
    rw [hcoeff_eq, h0]
    simp
  have hiR : i ∈ R.support := Polynomial.mem_support_iff.mpr hRcoeff_ne
  have heval_deg : ((Bivariate.evalX (Polynomial.C x₀) R).coeff i).natDegree ≤
      Bivariate.totalDegree (R.coeff i) := by
    rw [hcoeff_eq]
    have hP : (Polynomial.C x₀ : F[X]).natDegree ≤ 1 - 1 := by
      simp [Polynomial.natDegree_C]
    have hle := Bivariate.degree_eval_le_weightedDegree (Q := R.coeff i)
      (P := Polynomial.C x₀) (k := 1) hP
    have hw_le_total : Bivariate.natWeightedDegree (R.coeff i) 1 (1 - 1) ≤
        Bivariate.totalDegree (R.coeff i) := by
      unfold Bivariate.natWeightedDegree Bivariate.totalDegree
      simp only [Nat.sub_self, one_mul, zero_mul, add_zero]
      refine Finset.sup_le ?_
      intro j hj
      have hsup : ((R.coeff i).coeff j).natDegree + j ≤
          (R.coeff i).support.sup (fun m => ((R.coeff i).coeff m).natDegree + m) :=
        Finset.le_sup (s := (R.coeff i).support)
          (f := fun m => ((R.coeff i).coeff m).natDegree + m) hj
      exact le_trans (Nat.le_add_right ((R.coeff i).coeff j).natDegree j) hsup
    exact hle.trans hw_le_total
  have hD := hD_R i hiR
  omega

noncomputable def gammaFromAlpha (x₀ : F) (H : F[X][Y]) (αseq : ℕ → 𝕃 H) :
    PowerSeries (𝕃 H) :=
  let subst : ℕ → 𝕃 H := fun t =>
    match t with
    | 0 => fieldTo𝕃 (H := H) (-x₀)
    | 1 => 1
    | _ => 0
  PowerSeries.subst (PowerSeries.mk subst) (PowerSeries.mk αseq)

def HasNumeratorShape (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H) : Prop :=
  ∀ t : ℕ, alphaOfNumerators x₀ R H hHyp βseq t = αseq t

theorem beta_zero_eq_X_of_shape (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H)
    (hα0 : αseq 0 = functionFieldT (H := H) /
      liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries H R (gammaFromAlpha x₀ H αseq) = 0)
    (hshape : HasNumeratorShape x₀ R H hHyp αseq βseq) :
    βseq 0 =
      (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.X : F[X][Y]) : 𝒪 H) := by
  classical
  apply embeddingOf𝒪Into𝕃_injective hH
  have h0 := hshape 0
  unfold alphaOfNumerators at h0
  simp only [henselDenominatorExponent_zero, pow_zero, mul_one, zero_add, pow_one] at h0
  rw [hα0] at h0
  have hW : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  field_simp [hW] at h0
  rw [embeddingOf𝒪Into𝕃_mk, liftBivariate_X]
  exact h0

theorem formalHenselAlphaSequence (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hinit : Polynomial.eval₂ (liftToFunctionField (H := H))
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
      (Bivariate.evalX (Polynomial.C x₀) R) = 0)
    (hzeta : ζ R x₀ H ≠ 0) :
    ∃ αseq : ℕ → 𝕃 H,
      αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff ∧
      evalRAtPowerSeries H R (gammaFromAlpha x₀ H αseq) = 0 := by
  -- Pure formal-Hensel theorem over the field `𝕃 H`. Do not use `exists_hensel_numerator_sequence`, `βSeq`, `βSeq_spec`, `α`, or `γ` (circular). Construct `αseq` recursively. Set `α 0 = T/W`. For the inductive step, after coefficients below `t` are fixed, define the temporary series with future coefficients zero; let `c_t` be coefficient `t` of `evalRAtPowerSeries H R` for this temporary series. The coefficient of degree `t` after inserting an unknown `u` at position `t` is `c_t + ζ R x₀ H * u`; prove this coefficient-linearity lemma by expanding `Polynomial.eval₂` and using power-series coefficient formulas. Since `hzeta` makes `ζ` a unit in the field, set `u = -c_t / ζ`. Inductively prove all coefficients vanish, then use `PowerSeries.ext`/`PowerSeries.forall_coeff_eq_zero`. Base coefficient is exactly `hinit` after unfolding `gammaFromAlpha` and the shift series. Alternative if imports are available: use Henselian-ring machinery for `𝕃 H⟦X⟧` and translate the derivative unit to `hzeta`.
  sorry

theorem gammaOfNumerators_eq_gammaFromAlpha (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H)
    (hshape : HasNumeratorShape x₀ R H hHyp αseq βseq) :
    gammaOfNumerators x₀ R H hHyp βseq = gammaFromAlpha x₀ H αseq := by
  unfold HasNumeratorShape at hshape
  have hcoeff : PowerSeries.mk (alphaOfNumerators x₀ R H hHyp βseq) = PowerSeries.mk αseq := by
    ext n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    exact hshape n
  unfold gammaOfNumerators gammaFromAlpha
  rw [hcoeff]

noncomputable def henselCoeffResidual (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (αseq : ℕ → 𝕃 H) (t : ℕ) : 𝕃 H :=
  PowerSeries.coeff (t + 1) (evalRAtPowerSeries H R (gammaFromAlpha x₀ H αseq)) -
    ζ R x₀ H * αseq (t + 1)

theorem hensel_numerator_sequence_of_alpha_shape (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H)
    (hα0 : αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries H R (gammaFromAlpha x₀ H αseq) = 0)
    (hshape : HasNumeratorShape x₀ R H hHyp αseq βseq) :
    IsHenselNumeratorSequence x₀ R H hHyp βseq := by
  unfold IsHenselNumeratorSequence
  constructor
  · rw [hshape 0]
    exact hα0
  · rw [gammaOfNumerators_eq_gammaFromAlpha x₀ R H hHyp αseq βseq hshape]
    exact hroot

theorem mk_H_tilde_eq_W_pow_mul_eval2 (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)] :
    (Ideal.Quotient.mk (Ideal.span ({H_tilde H} : Set (Polynomial (RatFunc F)))) (H_tilde H) : 𝕃 H) =
      liftToFunctionField (H := H) H.leadingCoeff ^ (H.natDegree - 1) *
        Polynomial.eval₂ (liftToFunctionField (H := H))
          (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) H := by
  unfold liftToFunctionField functionFieldT coeffAsRatFunc
  unfold H_tilde
  simp only [Polynomial.coeff_natDegree, ToRatFunc.bivPolyHom, Polynomial.coe_mapRingHom,
    Polynomial.map_C, RingHom.comp_apply]
  let Wp : Polynomial (RatFunc F) := Polynomial.C (univPolyHom (F := F) H.leadingCoeff)
  let I : Ideal (Polynomial (RatFunc F)) := Ideal.span ({Wp ^ (H.natDegree - 1) * Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / Wp) H} : Set (Polynomial (RatFunc F)))
  let q : Polynomial (RatFunc F) →+* 𝕃 H := Ideal.Quotient.mk I
  have hW_ne : univPolyHom (F := F) H.leadingCoeff ≠ 0 := by
    intro h
    exact (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt _H_natDegree_pos.out))
      (univPolyHom_injective (F := F) (by simpa using h))
  have hdiv : q (Polynomial.X / Wp) = q Polynomial.X / q Wp := by
    dsimp [Wp]
    rw [Polynomial.div_C]
    rw [map_mul]
    rw [div_eq_mul_inv]
    congr 1
    have hmul : q (Polynomial.C (univPolyHom (F := F) H.leadingCoeff)) *
        q (Polynomial.C ((univPolyHom (F := F) H.leadingCoeff)⁻¹)) = 1 := by
      rw [← map_mul, ← Polynomial.C_mul]
      rw [mul_inv_cancel₀ hW_ne]
      exact map_one q
    exact (inv_eq_of_mul_eq_one_right hmul).symm
  change q (Wp ^ (H.natDegree - 1) * Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / Wp) H) = q Wp ^ (H.natDegree - 1) * Polynomial.eval₂ (q.comp ((Polynomial.mapRingHom (univPolyHom (F := F))).comp Polynomial.C)) (q Polynomial.X / q Wp) H
  rw [map_mul, map_pow]
  rw [← hdiv]
  rw [Polynomial.hom_eval₂]
  have hhom : q.comp (RingHom.comp Polynomial.C (univPolyHom (F := F)) : F[X] →+* Polynomial (RatFunc F)) =
      q.comp ((Polynomial.mapRingHom (univPolyHom (F := F))).comp Polynomial.C) := by
    ext p <;> simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C]
  rw [hhom]

theorem H_eval2_T_div_W_eq_zero (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)] :
    Polynomial.eval₂ (liftToFunctionField (H := H))
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) H = 0 := by
  have hzero : (Ideal.Quotient.mk (Ideal.span ({H_tilde H} : Set (Polynomial (RatFunc F)))) (H_tilde H) : 𝕃 H) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  rw [mk_H_tilde_eq_W_pow_mul_eval2] at hzero
  have hW : liftToFunctionField (H := H) H.leadingCoeff ^ (H.natDegree - 1) ≠ 0 := by
    exact pow_ne_zero _ (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  exact (mul_eq_zero.mp hzero).resolve_left hW

theorem initial_root_at_x0 (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    Polynomial.eval₂ (liftToFunctionField (H := H))
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
      (Bivariate.evalX (Polynomial.C x₀) R) = 0 := by
  classical
  rcases hHyp.dvd_evalX with ⟨Q, hQ⟩
  rw [hQ, Polynomial.eval₂_mul]
  rw [H_eval2_T_div_W_eq_zero H, zero_mul]

theorem zeta_ne_zero_of_Hypotheses (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    ζ R x₀ H ≠ 0 := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R
  let t : 𝕃 H := functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff
  have hroot : Polynomial.eval₂ (liftToFunctionField (H := H)) t P = 0 := by
    simpa [P, t] using initial_root_at_x0 x₀ R H hHyp
  have hderiv_evalX : Bivariate.evalX (Polynomial.C x₀) R.derivative = P.derivative := by
    ext i
    simp [P, derivative_evalX_coeff, Polynomial.coeff_derivative, Nat.cast_add, Nat.cast_one]
  have hne : Polynomial.eval₂ (liftToFunctionField (H := H)) t P.derivative ≠ 0 := by
    exact hHyp.separable_evalX.eval₂_derivative_ne_zero (liftToFunctionField (H := H)) hroot
  simpa [ζ, P, t, hderiv_evalX] using hne

theorem exists_hensel_alpha_sequence (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    ∃ αseq : ℕ → 𝕃 H,
      αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff ∧
      evalRAtPowerSeries H R (gammaFromAlpha x₀ H αseq) = 0 := by
  exact formalHenselAlphaSequence x₀ R H (initial_root_at_x0 x₀ R H hHyp) (zeta_ne_zero_of_Hypotheses x₀ R H hHyp)

theorem henselCoeffResidual_regular_after_clearing (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H)
    (hα0 : αseq 0 = functionFieldT (H := H) /
      liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries H R (gammaFromAlpha x₀ H αseq) = 0)
    (hzeta : ζ R x₀ H ≠ 0)
    (t : ℕ) (βprev : Fin (t + 1) → 𝒪 H)
    (hprev : ∀ i : Fin (t + 1),
      embeddingOf𝒪Into𝕃 H (βprev i) /
        (liftToFunctionField (H := H) H.leadingCoeff ^ (i.val + 1) *
          (embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)) ^ henselDenominatorExponent i.val) =
        αseq i.val) :
    let W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff
    let eta : 𝕃 H := embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)
    let E : ℕ := henselDenominatorExponent (t + 1)
    let Ddiv : 𝕃 H := W ^ (t + 1 + 1) * eta ^ (E - 1) * W ^ (R.natDegree - 2)
    henselCoeffResidual x₀ R H αseq t * Ddiv ∈ regularElementsSet H := by
  -- This is the substantial residual-regularity lemma requested by the prover for `regular_numerator_shape_succ`. Expand `henselCoeffResidual`: it is the coefficient of degree `t+1` in `evalRAtPowerSeries H R (gammaFromAlpha x₀ H αseq)` after subtracting the unique linear term `ζ * αseq (t+1)`. Prove a coefficient expansion as a finite sum over `R.support` and bounded partitions of `t+1`; after subtracting the linear term, every term only uses coefficients `αseq i` with `i ≤ t`. Replace those coefficients using `hprev`. Then multiply by the clearing denominator `Ddiv`; use `embeddingOf𝒪Into𝕃_ξ`, powers of `W`, and closure of `regularElementsSet` under addition, negation, multiplication, powers, and finite sums. Useful lemmas: `regularElementsSet_add`, `regularElementsSet_neg`, `regularElementsSet_mul`, `regularElementsSet_pow`, `regularElementsSet_sum`, `regularElementsSet_liftBivariate`, `regularElementsSet_liftToFunctionField`, `embeddingOf𝒪Into𝕃_ξ`, and `liftToFunctionField_leadingCoeff_ne_zero`.
  sorry

theorem numerator_shape_weight_succ_le_strong (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H)
    (hα0 : αseq 0 = functionFieldT (H := H) /
      liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries H R (gammaFromAlpha x₀ H αseq) = 0)
    (hshape : HasNumeratorShape x₀ R H hHyp αseq βseq)
    (t : ℕ)
    (ihAll : ∀ s ≤ t,
      weight_Λ_over_𝒪 hH (βseq s) D ≤
        (WithBot.some ((2 * s + 1) * Bivariate.natDegreeY R * D) : WithBot ℕ)) :
    weight_Λ_over_𝒪 hH (βseq (t + 1)) D ≤
      (WithBot.some ((2 * (t + 1) + 1) * Bivariate.natDegreeY R * D) : WithBot ℕ) := by
  -- Strong successor step for the weight induction. This fixes the weakness of the old node by assuming bounds for all previous numerators `βseq s`, `s ≤ t`, matching the partition-indexed Hensel recurrence. Prove it from the explicit successor numerator/partition formula (or the same residual formula used for `regular_numerator_shape_succ`). Bound finite sums with `weight_Λ_sum_le`; products with `weight_Λ_C_mul_X_pow_mul_le`, `weight_Λ_add_le`, and `weight_Λ_over_𝒪_mk_le`; use `ξ_weight_le` with `hD_Rx0` in the high-degree case and a separate low-degree case for `Bivariate.natDegreeY R < 2`. Use `ihAll` for every previous β term appearing in the partition. Finish by weakening the sharper paper bound to `(2*(t+1)+1)*natDegreeY R*D` using explicit arithmetic.
  sorry

theorem numerator_shape_weight_bound (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H)
    (hα0 : αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries H R (gammaFromAlpha x₀ H αseq) = 0)
    (hshape : HasNumeratorShape x₀ R H hHyp αseq βseq) :
    ∀ t : ℕ,
      weight_Λ_over_𝒪 hH (βseq t) D ≤
        (WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) : WithBot ℕ) := by
  intro t
  exact Nat.strong_induction_on t (fun t ih => by
    cases t with
    | zero =>
        have hβ0 := beta_zero_eq_X_of_shape x₀ R H hHyp hH hD_H hD_R αseq βseq hα0 hroot hshape
        rw [hβ0]
        refine (weight_Λ_over_𝒪_mk_le (H := H) (D := D) hD_H hH (Polynomial.X : F[X][Y])).trans ?_
        have hX : weight_Λ (Polynomial.X : F[X][Y]) H D ≤
            (WithBot.some (D + 1 - Bivariate.natDegreeY H) : WithBot ℕ) := by
          simpa only [pow_one, one_mul] using (weight_Λ_X_pow_le (H := H) (D := D) (k := 1))
        refine hX.trans ?_
        rw [WithBot.coe_le_coe]
        rw [show 2 * 0 + 1 = 1 by norm_num, one_mul]
        have hYpos : 0 < Bivariate.natDegreeY H := by
          exact hH
        have hH_le_R : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R := by
          exact H_natDegree_le_R_natDegree_of_Hypotheses hHyp
        have hR_pos : 0 < Bivariate.natDegreeY R := lt_of_lt_of_le hYpos hH_le_R
        have hDsub : D + 1 - Bivariate.natDegreeY H ≤ D := by
          omega
        exact le_trans hDsub (Nat.le_mul_of_pos_left D hR_pos)
    | succ t =>
        have hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) := by
          exact evalX_totalDegree_le_of_coeff_bound x₀ R hD_R
        exact numerator_shape_weight_succ_le_strong x₀ R H hHyp hH hD_H hD_R hD_Rx0 αseq βseq hα0 hroot hshape t (by
          intro s hs
          exact ih s (Nat.lt_succ_of_le hs)))

theorem regular_numerator_shape_succ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H)
    (hα0 : αseq 0 = functionFieldT (H := H) /
      liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries H R (gammaFromAlpha x₀ H αseq) = 0)
    (hzeta : ζ R x₀ H ≠ 0)
    (t : ℕ) (βprev : Fin (t + 1) → 𝒪 H)
    (hprev : ∀ i : Fin (t + 1),
      embeddingOf𝒪Into𝕃 H (βprev i) /
        (liftToFunctionField (H := H) H.leadingCoeff ^ (i.val + 1) *
          (embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)) ^ henselDenominatorExponent i.val) =
        αseq i.val) :
    ∃ βnext : 𝒪 H,
      embeddingOf𝒪Into𝕃 H βnext /
        (liftToFunctionField (H := H) H.leadingCoeff ^ (t + 1 + 1) *
          (embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)) ^ henselDenominatorExponent (t + 1)) =
        αseq (t + 1) := by
  classical
  let W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff
  let eta : 𝕃 H := embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)
  let E : ℕ := henselDenominatorExponent (t + 1)
  let D : 𝕃 H := W ^ (t + 1 + 1) * eta ^ E
  let Ddiv : 𝕃 H := W ^ (t + 1 + 1) * eta ^ (E - 1) * W ^ (R.natDegree - 2)
  let S : 𝕃 H :=
    PowerSeries.coeff (t + 1) (evalRAtPowerSeries H R (gammaFromAlpha x₀ H αseq)) -
      ζ R x₀ H * αseq (t + 1)
  have hSreg : S * Ddiv ∈ regularElementsSet H := by
    exact henselCoeffResidual_regular_after_clearing x₀ R H hHyp αseq hα0 hroot hzeta t βprev hprev
  have hW : W ≠ 0 := by
    simpa [W] using (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  have heta : eta ≠ 0 := by
    have hξeq := embeddingOf𝒪Into𝕃_ξ x₀ R H hHyp
    simpa [eta, W, hξeq] using mul_ne_zero (pow_ne_zero (R.natDegree - 2) hW) hzeta
  have hD : D ≠ 0 := by
    simp only [D]
    exact mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ heta)
  have hcoeff : PowerSeries.coeff (t + 1) (evalRAtPowerSeries H R (gammaFromAlpha x₀ H αseq)) = 0 := by
    simpa using congrArg (fun p : PowerSeries (𝕃 H) => PowerSeries.coeff (t + 1) p) hroot
  have hS : S = - ζ R x₀ H * αseq (t + 1) := by
    simp only [S, hcoeff, zero_sub]
    ring
  have hEpos : 0 < E := by
    dsimp [E]
    rw [henselDenominatorExponent_succ]
    omega
  have hE : E = (E - 1) + 1 := by omega
  have hpeta : eta ^ E = eta ^ (E - 1) * eta := by
    conv_lhs => rw [hE, pow_succ]
  have hD_eq : D = ζ R x₀ H * Ddiv := by
    have heta_eq : eta = W ^ (R.natDegree - 2) * ζ R x₀ H := by
      simpa [eta, W] using embeddingOf𝒪Into𝕃_ξ x₀ R H hHyp
    calc
      D = W ^ (t + 1 + 1) * eta ^ E := rfl
      _ = W ^ (t + 1 + 1) * (eta ^ (E - 1) * eta) := by
        rw [hpeta]
      _ = W ^ (t + 1 + 1) * (eta ^ (E - 1) * (W ^ (R.natDegree - 2) * ζ R x₀ H)) := by
        exact congrArg (fun x => W ^ (t + 1 + 1) * (eta ^ (E - 1) * x)) heta_eq
      _ = ζ R x₀ H * (W ^ (t + 1 + 1) * eta ^ (E - 1) * W ^ (R.natDegree - 2)) := by
        ring
      _ = ζ R x₀ H * Ddiv := rfl
  have hprod_eq : αseq (t + 1) * D = -(S * Ddiv) := by
    rw [hD_eq, hS]
    ring
  have hregProd : αseq (t + 1) * D ∈ regularElementsSet H := by
    rw [hprod_eq]
    exact regularElementsSet_neg hSreg
  rcases hregProd with ⟨βnext, hβnext⟩
  refine ⟨βnext, ?_⟩
  have hβnext' : (embeddingOf𝒪Into𝕃 H) βnext = αseq (t + 1) * D := hβnext.symm
  rw [hβnext']
  change (αseq (t + 1) * D) / D = αseq (t + 1)
  exact mul_div_cancel_right₀ (αseq (t + 1)) hD

theorem exists_regular_numerator_shape (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H)
    (hα0 : αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries H R (gammaFromAlpha x₀ H αseq) = 0) :
    ∃ βseq : ℕ → 𝒪 H,
      HasNumeratorShape x₀ R H hHyp αseq βseq := by
  classical
  let W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff
  let Xi : 𝕃 H := embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)
  let shapeAt : ℕ → 𝒪 H → Prop := fun t β =>
    embeddingOf𝒪Into𝕃 H β / (W ^ (t + 1) * Xi ^ henselDenominatorExponent t) = αseq t
  have hprefix : ∀ n : ℕ, ∃ βpref : Fin (n + 1) → 𝒪 H, ∀ i : Fin (n + 1), shapeAt i.val (βpref i) := by
    intro n
    induction n with
    | zero =>
        let β0 : 𝒪 H := (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.X : F[X][Y]) : 𝒪 H)
        refine ⟨fun _ => β0, ?_⟩
        intro i
        have hi : i.val = 0 := by omega
        rw [hi]
        unfold shapeAt
        rw [hα0]
        simp [β0, W, Xi, div_eq_mul_inv]
    | succ n ih =>
        rcases ih with ⟨βpref, hβpref⟩
        have hnext : ∃ βnext : 𝒪 H, shapeAt (n + 1) βnext := by
          unfold shapeAt
          exact regular_numerator_shape_succ x₀ R H hHyp αseq hα0 hroot
            (zeta_ne_zero_of_Hypotheses x₀ R H hHyp) n βpref (by
              intro i
              exact hβpref i)
        rcases hnext with ⟨βnext, hβnext⟩
        refine ⟨fun i => if hlt : i.val < n + 1 then βpref ⟨i.val, hlt⟩ else βnext, ?_⟩
        intro i
        by_cases hlt : i.val < n + 1
        · simp [hlt]
          exact hβpref ⟨i.val, hlt⟩
        · have hval : i.val = n + 1 := by
            have hi_lt : i.val < n + 1 + 1 := i.isLt
            omega
          simp [hlt, hval]
          exact hβnext
  let βseq : ℕ → 𝒪 H := fun t => (Classical.choose (hprefix t)) ⟨t, Nat.lt_succ_self t⟩
  refine ⟨βseq, ?_⟩
  intro t
  unfold HasNumeratorShape at *
  unfold alphaOfNumerators
  change shapeAt t (βseq t)
  unfold βseq
  exact (Classical.choose_spec (hprefix t)) ⟨t, Nat.lt_succ_self t⟩


/-- There is a sequence of regular numerators `β_t` with the Hensel-lift semantics and the
weight bound stated in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
lemma exists_hensel_numerator_sequence (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D) :
    ∃ βseq : ℕ → 𝒪 H,
      IsHenselNumeratorSequence x₀ R H hHyp βseq ∧
      ∀ t : ℕ,
        weight_Λ_over_𝒪 hH (βseq t) D ≤
          (WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) : WithBot ℕ) := by
  rcases exists_hensel_alpha_sequence x₀ R H hHyp with ⟨αseq, hα0, hroot⟩
  rcases exists_regular_numerator_shape x₀ R H hHyp αseq hα0 hroot with ⟨βseq, hshape⟩
  refine ⟨βseq, ?_, ?_⟩
  · exact hensel_numerator_sequence_of_alpha_shape x₀ R H hHyp αseq βseq hα0 hroot hshape
  · exact numerator_shape_weight_bound x₀ R H hHyp hH hD_H hD_R αseq βseq hα0 hroot hshape

/-- The chosen regular numerator sequence supplied by `exists_hensel_numerator_sequence`. -/
noncomputable def βSeq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) : ℕ → 𝒪 H :=
  if hH : 0 < H.natDegree then
    (exists_hensel_numerator_sequence x₀ R H hHyp hH
      (defaultDegreeBound_ge_H R H) (fun _ hi => defaultDegreeBound_ge_R_coeff R H hi)).choose
  else
    fun _ => 0

/-- The specification satisfied by the chosen numerator sequence. -/
lemma βSeq_spec (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) :
    IsHenselNumeratorSequence x₀ R H hHyp (βSeq x₀ R H hHyp) ∧
      ∀ t : ℕ,
        weight_Λ_over_𝒪 hH ((βSeq x₀ R H hHyp) t) (defaultDegreeBound R H) ≤
          (WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * defaultDegreeBound R H) :
            WithBot ℕ) := by
  unfold βSeq
  rw [dif_pos hH]
  exact (exists_hensel_numerator_sequence x₀ R H hHyp hH
    (defaultDegreeBound_ge_H R H) (fun _ hi => defaultDegreeBound_ge_R_coeff R H hi)).choose_spec

/-- The regular element `β_t` giving the numerator of the `t`-th chosen Hensel coefficient. -/
noncomputable def β (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝒪 H :=
  βSeq x₀ R H hHyp t

/-- The chosen Hensel-lift coefficients induced by the regular numerator sequence. -/
def α (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  alphaOfNumerators x₀ R H hHyp (βSeq x₀ R H hHyp) t

/-- Variant of `α` taking explicit irreducibility and positive-degree hypotheses. -/
def α' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H)
    (hHdeg : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  α x₀ R _ (φ := ⟨H_irreducible⟩) (H_natDegree_pos := ⟨hHdeg⟩) hHyp t

/-- The chosen power series `γ = ∑ α_t (X - x₀)^t`, induced by the selected regular numerator
sequence from `exists_hensel_numerator_sequence`. -/
def γ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) :
    PowerSeries (𝕃 H) :=
  gammaOfNumerators x₀ R H hHyp (βSeq x₀ R H hHyp)

/-- Variant of `γ` taking explicit irreducibility and positive-degree hypotheses. -/
def γ' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H)
    (hHdeg : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H) : PowerSeries (𝕃 H) :=
  γ x₀ R H (φ := ⟨H_irreducible⟩) (H_natDegree_pos := ⟨hHdeg⟩) hHyp

end ClaimA2
end
end BCIKS20AppendixA
