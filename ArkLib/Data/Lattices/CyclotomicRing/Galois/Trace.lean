/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Galois.Group

/-!
# The Trace Map `Tr_H`

For a subgroup `H` of Galois automorphisms, the relative trace is `Tr_H(a) := Σ_{σ ∈ H} σ(a)`.
Hachi [NOZ26, §3] uses `Tr_H` (for `H = ⟨σ_{-1}, σ_{4k+1}⟩`) to express inner products over the
subfield `F_{q^k} ≅ R_q^H` as relations over `R_q` (Theorem 2).

Computably, the trace is the finite sum of the automorphism actions over the exponent set `Hexp`.
It is additive (proven here, from additivity of `galoisAut`). That its image lands in the fixed
subring `R_q^H` and that `Tr_H` restricted there is `(d/k)·id` on the diagonal (Theorem 2) are
deferred.

## Main definitions

* `traceOver Φ S` — `Σ_{i ∈ S} σ_i`, the trace over an arbitrary exponent set.
* `traceH α k` — the trace `Tr_H` over `H = ⟨σ_{-1}, σ_{4k+1}⟩`.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi …*][NOZ26]
-/

open CompPoly Finset

namespace ArkLib.Lattices.CyclotomicModulus

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]
variable (Φ : CyclotomicModulus R) [IsCyclotomic Φ]

/-- The **trace over an exponent set** `S`: `Σ_{i ∈ S} σ_i(a)`.

Noncomputable as stated, since `Finset.sum` routes through `Rq`'s (transported, noncomputable)
`CommRing`. A `List.foldr`-based computable version using the primitive `Add` can be added if the
verifier needs to evaluate the trace; the underlying automorphism action `galoisAut` is
computable. -/
noncomputable def traceOver (S : Finset ℕ) (a : Rq Φ) : Rq Φ := ∑ i ∈ S, galoisAut Φ i a

@[simp] theorem traceOver_zero (S : Finset ℕ) : traceOver Φ S 0 = 0 := by
  unfold traceOver
  simp only [galoisAut_zero, Finset.sum_const_zero]

/-- The trace is additive. -/
theorem traceOver_add (S : Finset ℕ) (a b : Rq Φ) :
    traceOver Φ S (a + b) = traceOver Φ S a + traceOver Φ S b := by
  unfold traceOver
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => galoisAut_add Φ i a b)

/-- The **trace map `Tr_H`** for `H = ⟨σ_{-1}, σ_{4k+1}⟩`. -/
noncomputable def traceH (α k : ℕ) (a : Rq (powTwoCyclotomic (R := R) α)) :
    Rq (powTwoCyclotomic (R := R) α) :=
  traceOver (powTwoCyclotomic α) (Hexp α k) a

/-- `Tr_H` is fixed by every generator of `H`, hence lands in the fixed subring `R_q^H`.
(Sorried — needs the group structure of `H`.) -/
theorem traceH_mem_fixed (α k : ℕ) (a : Rq (powTwoCyclotomic (R := R) α)) :
    conjAut α (traceH α k a) = traceH α k a ∧ genAut α k (traceH α k a) = traceH α k a := by
  sorry

end ArkLib.Lattices.CyclotomicModulus
