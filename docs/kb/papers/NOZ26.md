---
kind: paper
bibkey: NOZ26
title: "Hachi: Efficient Lattice-Based Multilinear Polynomial Commitments over Extension Fields"
year: 2026
bib_source: blueprint/src/references.bib
source_metadata: ../sources/NOZ26/metadata.yml
status: stub
related_modules:
  - ArkLib/ProofSystem/RingSwitching/Profile.lean
---

# NOZ26

## At A Glance

`NOZ26` ("Hachi", Nguyen–O'Rourke–Zhang, ePrint 2026/156) is a concretely efficient lattice-based
multilinear polynomial commitment scheme over extension fields, with a "square-root" verifier-time
complexity under Module-SIS. It is the **second intended instance** of ArkLib's generic
ring-switching abstraction (the first being Binius / [`DP24`](DP24.md)).

## What ArkLib Uses From This Paper

- The **extension-field → cyclotomic-ring reduction**: Hachi reduces evaluation proofs over `F_{q^k}`
  to equivalent statements over a power-of-two cyclotomic ring `R_q := Z_q[X]/(X^d+1)`. This is the
  ring-switching shape ArkLib factors out as `RingSwitchingProfile`.
- The packing-layer instantiation: `L = R_q`, carrier `A = R_q`, `φ₀ = id`, `φ₁ = σ₋₁` (order-two
  automorphism), basis `ψ` from its **Theorem 2** — which discharges the profile's reconstruction
  laws for the Hachi instance.

## Main ArkLib Touchpoints

- [`../../../ArkLib/ProofSystem/RingSwitching/Profile.lean`](../../../ArkLib/ProofSystem/RingSwitching/Profile.lean)
- Concept page: [`../concepts/ring-switching.md`](../concepts/ring-switching.md)

## Known Divergences From ArkLib

- ArkLib has not yet built the Hachi instance; the abstraction is designed to admit it but only the
  Binius instance is implemented.
- `R_q` is **not an integral domain**, so the generic `[IsDomain L]` Schwartz–Zippel soundness
  theorem does not instantiate Hachi. Hachi soundness (a CWSS-style argument) is a separate theorem
  with a different error and is out of scope for the current ring-switching module.

## Open Formalization Gaps

- Construct `hachiProfile : RingSwitchingProfile R_qH R_q κ` and discharge `decomposeRows_spec` /
  `decomposeColumns_spec` via Theorem 2.
- Formalize Hachi-specific soundness separately (does not reuse the field/domain soundness theorem).

## Version Notes

- Builds on the ring-switching idea of Huang–Mao–Zhang (ePrint 2025) and integrates Greyhound
  (CRYPTO 2024); track which version is cited if proof obligations depend on exact statements.

## Source Access

- Source metadata: [`../sources/NOZ26/metadata.yml`](../sources/NOZ26/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib) (key `NOZ26`)
- ePrint: https://eprint.iacr.org/2026/156
