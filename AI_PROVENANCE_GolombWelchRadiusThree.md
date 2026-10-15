# AI provenance: No lattice tiling of ℤ^35 or ℤ^805 by Lee balls of radius three

Authors: Deep Bhattacharjee (corresponding author, ORCID 0000-0003-0466-750X)
and Ushashi Bhattacharya (ORCID 0009-0002-2254-3914).

- Paper: https://github.com/creelie/refactored-waddle/blob/main/preprintGolombWelchRadiusThree/GolombWelchRadiusThree.pdf
- Lean formalisation and code: Zenodo, release v1.0.0, https://doi.org/10.5281/zenodo.23398805 (all versions: https://doi.org/10.5281/zenodo.23398804)
- Repository: https://github.com/creelie/refactored-waddle

## Result

The Golomb–Welch conjecture (1970) states that ℤ^n has no tiling by the Lee
ball B^n(r) when n ≥ 3 and r ≥ 2. A. Xiao and Y. Zhou (arXiv:2610.19775,
Theorem 5.1) decided the lattice form for every such pair with
|B^n(r)| < 2^30, except (n, r) = (35, 3) and (805, 3). The paper proves that
ℤ^35 and ℤ^805 have no lattice tiling by B^n(3). With the result of Xiao and
Zhou, the lattice form of the conjecture holds for every Lee ball with fewer
than 2^30 points.

## Who did what

Deep Bhattacharjee chose the problem, directed the work, set the format and
the target journal, and ran the computations. Claude (Anthropic), used through
Claude Code under his direction, produced the following:

- the proofs of Sections 2 to 6, in particular the use of the constant term
  modulo 29² for n = 805 and the joint projection through dual numbers with
  the circulant system for n = 35;
- the Lean 4 formalisation;
- the checking programs in C, C++, Python and Julia;
- the figures;
- the LaTeX text of the paper.

No other AI system took part. The reduction to group-ring equations follows
Zhang and Zhou and Xiao and Zhou, and the paper credits them.

## How the result is checked

- **Lean 4.34.1 with Mathlib.** The theorems `GolombWelch.golomb_welch_35`
  and `GolombWelch.golomb_welch_805` state that no subgroup L of ℤ^35 (resp.
  ℤ^805) has the property that every point of the space lies at Lee distance at
  most 3 from exactly one point of L. They depend only on the standard axioms
  propext, Classical.choice and Quot.sound. There is no `sorry`, `admit`,
  `native_decide`, `bv_decide` or added axiom. The finite computations in
  𝔽₂₉, 𝔽₇₁ and ℤ/841 are checked by the kernel.
- **Independent programs.** Programs in C, C++, Python and Julia recompute the
  sizes of the balls, the ball identity on small cases, the table of
  coefficients, the congruences modulo 29² for n = 805, the case analysis for
  n = 35, the coefficients of the joint relation and the rank of the circulant
  systems over 𝔽₇₁. The C++ program also computes the ε-part of the identity
  directly in 𝔽₇₁[ℤ/29][ε].
- **Release workflow.** It builds the Lean proof, checks its axioms and runs
  the programs before publishing.

## What is not claimed

The paper does not prove the Golomb–Welch conjecture, nor its lattice form in
general. It settles two cases of the lattice form; tilings that are not
lattice tilings are not covered, since 59711 and 696845031 are not prime. The
corollary for all balls with fewer than 2^30 points uses Theorem 5.1 of Xiao
and Zhou, which is not formalised in Lean. The authors checked on 15 October
2026 that the two cases appear as open in version 1 of the preprint of Xiao
and Zhou (14 October 2026), and found no other treatment of them on arXiv, on
GitHub or on the web.
