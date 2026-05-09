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
# Definitions and Theorems about Function Fields and Rings of Regular Functions

We define the notions of Appendix A of [BCIKS20].

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

## Main Definitions

-/

open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace BCIKS20AppendixA

section

variable {F : Type} [CommRing F] [IsDomain F]

/-- Construction of the monisized polynomial `H_tilde` in Appendix A.1 of [BCIKS20].
Note: Here `H ∈ F[X][Y]` translates to `H ∈ F[Z][Y]` in [BCIKS20] and H_tilde in
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

/-- The monisized version `H_tilde` is irreducible if the original polynomial `H` is irreducible
and has positive degree in `Y`, as assumed in Appendix A.1 of [BCIKS20]. -/
lemma irreducibleHTildeOfIrreducible {F : Type} [Field F] {H : Polynomial (Polynomial F)}
    (hHdeg : 0 < H.natDegree) :
    Irreducible H → Irreducible (H_tilde H) :=
  irreducibleHTildeOfIrreducible_of_natDegree_pos hHdeg

/-- The function field `𝕃 ` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝕃 (H : F[X][Y]) : Type :=
  (Polynomial (RatFunc F)) ⧸ (Ideal.span {H_tilde H})

/-- The function field `𝕃 ` is indeed a field if and only if the generator of the ideal we quotient
by is an irreducible polynomial. -/
lemma isField_of_irreducible_of_natDegree_pos {F : Type} [Field F] {H : F[X][Y]}
    (hHdeg : 0 < H.natDegree) (hH : Irreducible H) : IsField (𝕃 H) := by
  unfold 𝕃
  erw
    [
      ← Ideal.Quotient.maximal_ideal_iff_isField_quotient,
      principal_is_maximal_iff_irred
    ]
  exact irreducibleHTildeOfIrreducible_of_natDegree_pos hHdeg hH

/-- The function field `𝕃 ` is indeed a field when the generator of the ideal we quotient by is
irreducible and has positive degree in `Y`. -/
lemma isField_of_irreducible {F : Type} [Field F] {H : F[X][Y]} (hHdeg : 0 < H.natDegree) :
    Irreducible H → IsField (𝕃 H) := by
  intros h
  unfold 𝕃
  erw
    [
      ← Ideal.Quotient.maximal_ideal_iff_isField_quotient,
      principal_is_maximal_iff_irred
    ]
  exact irreducibleHTildeOfIrreducible hHdeg h

/-- The function field `𝕃` as defined above is a field. -/
noncomputable instance {F : Type} [Field F] {H : F[X][Y]} [hHdeg : Fact (0 < H.natDegree)]
    [inst : Fact (Irreducible H)] : Field (𝕃 H) :=
  IsField.toField (isField_of_irreducible hHdeg.out inst.out)

/-- The monisized polynomial `H_tilde` is in fact an element of `F[X][Y]`. -/
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
lemma H_tilde_equiv_H_tilde' (H : F[X][Y]) : (H_tilde' H).map univPolyHom = H_tilde H := by
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

section FieldIrreducibility

variable {F : Type} [Field F]

/-- The integral monicized polynomial `H_tilde'` is irreducible whenever `H` is irreducible and has
positive degree in `Y`. -/
lemma irreducibleHTilde'OfIrreducible {H : F[X][Y]} (hHdeg : 0 < H.natDegree)
    (hH : Irreducible H) :
    Irreducible (H_tilde' H) := by
  have hmap : Irreducible ((H_tilde' H).map (univPolyHom (F := F))) := by
    simpa [H_tilde_equiv_H_tilde'] using
      irreducibleHTildeOfIrreducible_of_natDegree_pos hHdeg hH
  exact (H_tilde'_monic H hHdeg).isPrimitive.irreducible_of_irreducible_map_of_injective
    (univPolyHom_injective (F := F)) hmap

end FieldIrreducibility

/-- The ring of regular elements `𝒪` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝒪 (H : F[X][Y]) : Type :=
  (Polynomial (Polynomial F)) ⧸ (Ideal.span {H_tilde' H})

/-- The ring of regular elements field `𝒪` is a indeed a ring. -/
noncomputable instance {H : F[X][Y]} : Ring (𝒪 H) :=
  Ideal.Quotient.ring (Ideal.span {H_tilde' H})

/-- The ring homomorphism defining the embedding of `𝒪` into `𝕃`. -/
noncomputable def embeddingOf𝒪Into𝕃 (H : F[X][Y]) : 𝒪 H →+* 𝕃 H :=
  Ideal.quotientMap
        (I := Ideal.span {H_tilde' H}) (Ideal.span {H_tilde H})
        bivPolyHom (by
          rw [Ideal.span_le]
          intro x hx
          rw [Set.mem_singleton_iff] at hx; subst hx
          change bivPolyHom (H_tilde' H) ∈ span {H_tilde H}
          rw [show bivPolyHom (H_tilde' H) = (H_tilde' H).map univPolyHom from rfl,
              H_tilde_equiv_H_tilde']
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
    simpa [q, H_tilde_equiv_H_tilde'] using hp
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
def regularElms_set (H : F[X][Y]) : Set (𝕃 H) :=
  {a : 𝕃 H | ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- The regular elements inside `𝕃 H`, i.e. the elements of `𝕃 H` that in fact lie in `𝒪 H`
as Type. -/
def regularElms (H : F[X][Y]) : Type :=
  {a : 𝕃 H // ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- Zero is regular. -/
@[simp]
lemma regularElms_set_zero (H : F[X][Y]) : (0 : 𝕃 H) ∈ regularElms_set H :=
  ⟨0, by simp⟩

/-- One is regular. -/
@[simp]
lemma regularElms_set_one (H : F[X][Y]) : (1 : 𝕃 H) ∈ regularElms_set H :=
  ⟨1, by simp⟩

/-- The regular elements are closed under addition. -/
lemma regularElms_set_add {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElms_set H) (hb : b ∈ regularElms_set H) :
    a + b ∈ regularElms_set H := by
  rcases ha with ⟨a', rfl⟩
  rcases hb with ⟨b', rfl⟩
  exact ⟨a' + b', by simp⟩

/-- The regular elements are closed under negation. -/
lemma regularElms_set_neg {H : F[X][Y]} {a : 𝕃 H}
    (ha : a ∈ regularElms_set H) : -a ∈ regularElms_set H := by
  rcases ha with ⟨a', rfl⟩
  exact ⟨-a', by simp⟩

/-- The regular elements are closed under subtraction. -/
lemma regularElms_set_sub {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElms_set H) (hb : b ∈ regularElms_set H) :
    a - b ∈ regularElms_set H := by
  simpa [sub_eq_add_neg] using regularElms_set_add ha (regularElms_set_neg hb)

/-- The regular elements are closed under multiplication. -/
lemma regularElms_set_mul {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElms_set H) (hb : b ∈ regularElms_set H) :
    a * b ∈ regularElms_set H := by
  rcases ha with ⟨a', rfl⟩
  rcases hb with ⟨b', rfl⟩
  exact ⟨a' * b', by simp⟩

/-- The regular elements are closed under natural powers. -/
lemma regularElms_set_pow {H : F[X][Y]} {a : 𝕃 H}
    (ha : a ∈ regularElms_set H) (n : ℕ) : a ^ n ∈ regularElms_set H := by
  induction n with
  | zero => simp
  | succ n ih =>
      simpa [pow_succ] using regularElms_set_mul ih ha

/-- Given an element `z ∈ F`, `t_z ∈ F` is a rational root of a bivariate polynomial if the pair
`(z, t_z)` is a root of the bivariate polynomial. -/
def rationalRoot (H : F[X][Y]) (z : F) : Type :=
  {t_z : F // evalEval z t_z H = 0}

/-- The rational substitution `π_z` from Appendix A.3 defined on the whole ring of
bivariate polynomials. -/
noncomputable def π_z_lift {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) :
  F[X][Y] →+* F := Polynomial.evalEvalRingHom z root.1

/-- The rational substitution `π_z` from Appendix A.3 of [BCIKS20] is a well-defined map on the
quotient ring `𝒪`. -/
noncomputable def π_z {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) : 𝒪 H →+* F :=
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

/-- The weight function `Λ` on the ring of regular elements `𝒪` is defined as the weight their
canonical representatives in `F[X][Y]`. -/
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

/-- The set `S_β` from the statement of Lemma A.1 in Appendix A of [BCIKS20].
Note: Here `F[X][Y]` is `F[Z][T]`. -/
noncomputable def S_β {H : F[X][Y]} (β : 𝒪 H) : Set F :=
  {z : F | ∃ root : rationalRoot (H_tilde' H) z, (π_z z root) β = 0}

/-- The statement of Lemma A.1 in Appendix A.3 of [BCIKS20]. -/
lemma Lemma_A_1 {H : F[X][Y]} [hHirreducible : Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ)
    (hD : D ≥ Bivariate.totalDegree H)
    (S_β_card : Set.ncard (S_β β) > (weight_Λ_over_𝒪 hH β D) * H.natDegree) :
  embeddingOf𝒪Into𝕃 _ β = 0 := by sorry

/-- The embeddining of the coefficients of a bivarite polynomial into the bivariate polynomial ring
with rational coefficients. -/
noncomputable def coeffAsRatFunc : F[X] →+* Polynomial (RatFunc F) :=
  RingHom.comp bivPolyHom Polynomial.C

/-- The embeddining of the coefficients of a bivarite polynomial into the function field `𝕃`. -/
noncomputable def liftToFunctionField {H : F[X][Y]} : F[X] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) coeffAsRatFunc

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
lemma regularElms_set_liftBivariate (H : F[X][Y]) (p : F[X][Y]) :
    liftBivariate (H := H) p ∈ regularElms_set H := by
  rcases regular_liftBivariate H p with ⟨pre, hpre⟩
  exact ⟨pre, hpre.symm⟩

/-- Coefficients embedded into `𝕃` are regular elements. -/
lemma regular_liftToFunctionField (H : F[X][Y]) (p : F[X]) :
    ∃ pre : 𝒪 H, embeddingOf𝒪Into𝕃 H pre = liftToFunctionField (H := H) p :=
  regular_liftBivariate H (Polynomial.C p)

/-- Coefficient-polynomial images are regular elements of the function field. -/
lemma regularElms_set_liftToFunctionField (H : F[X][Y]) (p : F[X]) :
    liftToFunctionField (H := H) p ∈ regularElms_set H := by
  simpa using regularElms_set_liftBivariate H (Polynomial.C p)

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
lemma regularElms_set_liftToFunctionField_div_of_dvd {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {p q : F[X]} (hq : q ≠ 0) (hdiv : q ∣ p) :
    liftToFunctionField (H := H) p / liftToFunctionField (H := H) q ∈ regularElms_set H := by
  rcases hdiv with ⟨r, rfl⟩
  have hq_lift : liftToFunctionField (H := H) q ≠ 0 := liftToFunctionField_ne_zero hq
  have heq :
      liftToFunctionField (H := H) (q * r) / liftToFunctionField (H := H) q =
        liftToFunctionField (H := H) r := by
    rw [map_mul]
    field_simp [hq_lift]
  rw [heq]
  exact regularElms_set_liftToFunctionField H r

/-- If `W = H.leadingCoeff` divides `p`, then `p / W` is regular after embedding into `𝕃`. -/
lemma regularElms_set_liftToFunctionField_div_leadingCoeff_of_dvd {F : Type} [Field F]
    {H : F[X][Y]} [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] {p : F[X]}
    (hdiv : H.leadingCoeff ∣ p) :
    liftToFunctionField (H := H) p / liftToFunctionField (H := H) H.leadingCoeff ∈
      regularElms_set H := by
  exact regularElms_set_liftToFunctionField_div_of_dvd
    (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out))
    hdiv

/-- The bivariate variable maps to the function-field variable `T`. -/
@[simp]
lemma liftBivariate_X {H : F[X][Y]} :
    liftBivariate (H := H) (Polynomial.X : F[X][Y]) = functionFieldT (H := H) := by
  simp [liftBivariate, functionFieldT, bivPolyHom]

/-- The function-field variable `T` is regular. -/
lemma regularElms_set_functionFieldT (H : F[X][Y]) :
    functionFieldT (H := H) ∈ regularElms_set H := by
  simpa using regularElms_set_liftBivariate H (Polynomial.X : F[X][Y])

/-- A linear polynomial evaluated at `T / W` is regular when its linear coefficient is divisible by
`W = H.leadingCoeff`. -/
lemma regularElms_set_eval₂_linear_of_coeff_one_dvd {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {P : F[X][Y]} (hP : P.natDegree ≤ 1) (hdiv : H.leadingCoeff ∣ P.coeff 1) :
    Polynomial.eval₂ liftToFunctionField
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) P ∈
      regularElms_set H := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hP]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
  have hterm :
      liftToFunctionField (H := H) (P.coeff 1) *
          (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) =
        (liftToFunctionField (H := H) (P.coeff 1) /
            liftToFunctionField (H := H) H.leadingCoeff) * functionFieldT (H := H) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [hterm]
  exact regularElms_set_add
    (regularElms_set_mul
      (regularElms_set_liftToFunctionField_div_leadingCoeff_of_dvd hdiv)
      (regularElms_set_functionFieldT H))
    (regularElms_set_liftToFunctionField H (P.coeff 0))

/-- Constant bivariate polynomials map through the coefficient embedding. -/
@[simp]
lemma liftBivariate_C {H : F[X][Y]} (p : F[X]) :
    liftBivariate (H := H) (Polynomial.C p : F[X][Y]) = liftToFunctionField (H := H) p := by
  rfl

/-- The embeddining of the scalars into the function field `𝕃`. -/
noncomputable def fieldTo𝕃 {H : F[X][Y]} : F →+* 𝕃 H :=
  RingHom.comp liftToFunctionField Polynomial.C

/-- Constructing power series over the function field `𝕃 H` out of a polynomial. -/
noncomputable def polyToPowerSeries𝕃 (H : F[X][Y]) (P : F[X][Y]) : PowerSeries (𝕃 H) :=
  PowerSeries.mk <| fun n => liftToFunctionField (P.coeff n)


end

noncomputable section

namespace ClaimA2

variable {F : Type} [Field F]
         {R : F[X][X][X]}
         {H : F[X][Y]} [H_irreducible : Fact (Irreducible H)]
         [H_natDegree_pos : Fact (0 < H.natDegree)]

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

/-- The definition of `ζ` given in Appendix A.4 of [BCIKS20]. -/
def ζ (R : F[X][X][Y]) (x₀ : F) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] : 𝕃 H :=
  let W  : 𝕃 H := liftToFunctionField (H.leadingCoeff);
  let T : 𝕃 H := functionFieldT (H := H);
    Polynomial.eval₂ liftToFunctionField (T / W)
      (Bivariate.evalX (Polynomial.C x₀) R.derivative)

/-- If the derivative specialization is constant in the function-field variable, then `ζ` is
regular. -/
lemma ζ_regular_of_derivative_evalX_eq_C (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)] {p : F[X]}
    (hp : Bivariate.evalX (Polynomial.C x₀) R.derivative = Polynomial.C p) :
    ζ R x₀ H ∈ regularElms_set H := by
  rw [ζ, hp]
  simp only [Polynomial.eval₂_C]
  exact regularElms_set_liftToFunctionField H p

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
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff);
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
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff);
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
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff);
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  have hP : P.natDegree ≤ 1 := by
    calc
      P.natDegree ≤ R.derivative.natDegree := evalX_natDegree_le (Polynomial.C x₀) R.derivative
      _ ≤ R.natDegree - 1 := Polynomial.natDegree_derivative_le R
      _ = 1 := by omega
  have hdiv : H.leadingCoeff ∣ P.coeff 1 := by
    simpa [P, hR] using leadingCoeff_dvd_evalX_derivative_coeff_pred hHyp
  have hreg : ζ R x₀ H ∈ regularElms_set H := by
    simpa [ζ, P] using regularElms_set_eval₂_linear_of_coeff_one_dvd (H := H) hP hdiv
  rcases hreg with ⟨pre, hpre⟩
  refine ⟨pre, ?_⟩
  have hd : R.natDegree - 2 = 0 := by omega
  simpa [hd] using hpre.symm

/-- There exist regular elements `ξ = W(Z)^(d-2) * ζ` as defined in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
lemma ξ_regular (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff);
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  by_cases hRle : R.natDegree ≤ 1
  · exact ξ_regular_of_natDegree_le_one x₀ R H hRle
  by_cases hRtwo : R.natDegree = 2
  · exact ξ_regular_of_natDegree_eq_two x₀ R H hHyp hRtwo
  sorry

/-- The elements `ξ = W(Z)^(d-2) * ζ` as defined in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
def ξ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) : 𝒪 H :=
  (ξ_regular x₀ R H hHyp).choose

/-- The bound of the weight `Λ` of the elements `ζ` as stated in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
lemma weight_ξ_bound (x₀ : F) (hH : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H)
    {D : ℕ} (hD_H : D ≥ Bivariate.totalDegree H)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R)) :
    weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D ≤
    WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) := by
  sorry

/-- There exist regular elements `β` with a weight bound as given in Claim A.2
of Appendix A.4 of [BCIKS20]. -/
lemma β_regular (R : F[X][X][Y])
                (H : F[X][Y]) [_H_irreducible : Fact (Irreducible H)]
                [_H_natDegree_pos : Fact (0 < H.natDegree)]
                (hH : 0 < H.natDegree)
                {D : ℕ} (_hD : D ≥ Bivariate.totalDegree H) :
    ∀ t : ℕ, ∃ β : 𝒪 H,
      weight_Λ_over_𝒪 hH β D ≤ (2 * t + 1) * Bivariate.natDegreeY R * D :=
  fun _ => ⟨0, by simp⟩

/-- The definition of the regular elements `β` giving the numerators of the Hensel lift coefficients
as defined in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
def β (R : F[X][X][Y]) (t : ℕ) : 𝒪 H :=
  if hH : 0 < H.natDegree then
    (β_regular R H hH (Nat.le_refl _) t).choose
  else
    0

/-- The Hensel lift coefficients `α` are of the form as given in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
def α (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  embeddingOf𝒪Into𝕃 _ (β R t) /
    (W ^ (t + 1) * (embeddingOf𝒪Into𝕃 _ (ξ x₀ R H hHyp)) ^ (2*t - 1))

def α' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H)
    (hHdeg : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  α x₀ R _ (φ := ⟨H_irreducible⟩) (H_natDegree_pos := ⟨hHdeg⟩) hHyp t

/-- The power series `γ = ∑ α^t (X - x₀)^t ∈ 𝕃 [[X - x₀]]` as defined in Appendix A.4
of [BCIKS20]. -/
def γ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) :
    PowerSeries (𝕃 H) :=
  let subst (t : ℕ) : 𝕃 H :=
    match t with
    | 0 => fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0
  PowerSeries.subst (PowerSeries.mk subst) (PowerSeries.mk (α x₀ R H hHyp))

def γ' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H)
    (hHdeg : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H) : PowerSeries (𝕃 H) :=
  γ x₀ R H (φ := ⟨H_irreducible⟩) (H_natDegree_pos := ⟨hHdeg⟩) hHyp

end ClaimA2
end
end BCIKS20AppendixA
