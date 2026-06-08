/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Galois.Trace

/-!
# The Fixed Subring `R_q^H`

Hachi [NOZ26, §3, Lemma 5] shows that the subring `R_q^H` of elements fixed by every
automorphism in `H = ⟨σ_{-1}, σ_{4k+1}⟩` is a subfield isomorphic to `F_{q^k}`. This file
provides `R_q^H` as a `Subring`.

Because a homomorphism is fixed by all of `H` iff it is fixed by the *generators*, the fixed
subring is exactly the intersection of the equalizers of the two generating automorphisms with
the identity. We therefore define it via Mathlib's `RingHom.eqLocus`, which yields a genuine
`Subring` for free (no closure obligations):

  `R_q^H := eqLocus σ_{-1} id ⊓ eqLocus σ_{4k+1} id`.

The field structure and cardinality `|R_q^H| = q^k` (Lemma 5 / Eq. 7) live in
`CyclotomicRing/Subfield/` and are not addressed here.

## Main definitions

* `fixedSubring α k` — the subring `R_q^H` of `H`-fixed elements.
* `mem_fixedSubring_iff` — membership in terms of the two generators.

## References

* [Lyubashevsky, V., Nguyen, N. K., and Plançon, M., *Lattice-Based Zero-Knowledge Proofs*][LNP22]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi …*][NOZ26]
-/

namespace ArkLib.Lattices.CyclotomicModulus

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]

/-- The **fixed subring `R_q^H`** for `H = ⟨σ_{-1}, σ_{4k+1}⟩`: the elements fixed by both
generating automorphisms. Defined as the meet of the two generator equalizers with the identity,
so it is a `Subring` directly from Mathlib. By Hachi [NOZ26, Lemma 5] it is a subfield `≅ F_{q^k}`
(established elsewhere). -/
noncomputable def fixedSubring (α k : ℕ) : Subring (Rq (powTwoCyclotomic (R := R) α)) :=
  RingHom.eqLocus (conjAut α) (RingHom.id _) ⊓ RingHom.eqLocus (genAut α k) (RingHom.id _)

/-- Membership in `R_q^H`: an element is `H`-fixed iff it is fixed by both generators. -/
theorem mem_fixedSubring_iff (α k : ℕ) (x : Rq (powTwoCyclotomic (R := R) α)) :
    x ∈ fixedSubring α k ↔ conjAut α x = x ∧ genAut α k x = x := by
  simp only [fixedSubring, Subring.mem_inf, RingHom.mem_eqLocus, RingHom.id_apply]

end ArkLib.Lattices.CyclotomicModulus
