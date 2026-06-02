# Ring Switching

This page is the KB landing page for the **ring-switching** technique and ArkLib's generic
formalization of it.

## Scope

Use this page when a question is about:

- what ring switching is and why a polynomial commitment scheme uses it;
- the `RingSwitchingProfile` abstraction and how a protocol family instantiates it;
- where Binius plugs in, and how Hachi (and other small-ring/large-ring PCS work) would;
- which security statements are generic vs. instance-specific.

## The idea

Ring switching reduces a multilinear evaluation claim `s = t(r)` over a **small** coefficient ring
`B` (a binary-tower field, `𝔽₂`, or a cyclotomic ring `R_q`) to an evaluation claim over a **large**
extension `L`, paying only an additive `O(1/|L|)` soundness cost and **without re-committing** over
`L`. This lets a PCS commit cheaply over a tiny ring while running sum-check and the final opening
over a field large enough for soundness.

With `ℓ = ℓ' + κ`, a small-field multilinear `t` in `ℓ` variables is *packed* into a large-field
multilinear `t'` in `ℓ'` variables (`packMLE`): each block of `2^κ` coefficients becomes one
`L`-element via a `B`-basis `β` of `L`. The interaction runs in a *pack/trace carrier* `A` where the
folded element `ŝ` lives; an eq̃/trace inner-product identity (DP24 §2.5) ties `ŝ`'s coordinates to
the original claim and the new sum-check target.

## ArkLib's abstraction

ArkLib formalizes ring switching **once**, generic over a `RingSwitchingProfile (B L) κ`:

- `basis`, carrier `A`, embeddings `φ₀`/`φ₁ : L →+* A`, coordinate maps `decomposeRows`/`Columns`,
- plus two **reconstruction laws** (`decomposeRows_spec`, `decomposeColumns_spec`) — the eq̃/trace
  identity — which the completeness/soundness proofs consume and which rule out degenerate profiles.

The protocol is three phases (batching → sum-check → large-field IOPCS opening); see the blueprint
section *Ring Switching* (`blueprint/src/proof_systems/ring_switching.tex`) for the protocol and
security statements. The RBR knowledge error is `κ/|L| + Σ 2/|L| + 1/|L| + ε_IOPCS` (DP24 §3.1–3.2),
and soundness requires `[IsDomain L]` (Schwartz–Zippel).

## Instances

- **Binius** (`binaryTowerProfile`): `A = L ⊗_K L`, `φ₀ = ·⊗1`, `φ₁ = 1⊗·`, coordinates from the
  left/right `L`-module bases; the two laws are **proven** in ArkLib.
- **Hachi** ([`../papers/NOZ26.md`](../papers/NOZ26.md)): `L = R_q`, `A = R_q`, `φ₀ = id`,
  `φ₁ = σ₋₁`, `β = ψ` (Theorem 2). `R_q` is not a domain, so the Schwartz–Zippel soundness theorem
  does not apply — Hachi soundness is a separate (CWSS) argument.

## Core References

- [`../papers/DP24.md`](../papers/DP24.md) — origin of ring switching for binary towers.
- [`../papers/NOZ26.md`](../papers/NOZ26.md) — Hachi; the extension-field→cyclotomic-ring reduction.

## Main ArkLib Touchpoints

- [`../../../ArkLib/ProofSystem/RingSwitching/Profile.lean`](../../../ArkLib/ProofSystem/RingSwitching/Profile.lean) — the abstraction.
- [`../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean`](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean) — `packMLE`, the Binius instance `binaryTowerProfile`, shared defs.
- [`../../../ArkLib/ProofSystem/RingSwitching/General.lean`](../../../ArkLib/ProofSystem/RingSwitching/General.lean) — full reduction + security theorems.
- [`../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean`](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean) — `biniusProfile`, the concrete instantiation.

## Notes

- The protocol skeleton and security *statements* are generic and final; the leaf
  completeness/soundness *proofs* are tracked as follow-up (see `M5_BOOTSTRAP.md` at repo root).
- Soundness reuse across instances is weaker than data-layer reuse: the `[IsDomain L]` theorems fit
  field instances (Binius) but not non-domain rings (Hachi `R_q`), whose soundness is a sibling
  theorem with a different error.
