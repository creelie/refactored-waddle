**No lattice tiling of ℤ^35 or ℤ^805 by Lee balls of radius three**, by Deep Bhattacharjee (corresponding author) and Ushashi Bhattacharya.

Golomb and Welch conjectured in 1970 that ℤ^n has no tiling by the Lee ball B^n(r) when n ≥ 3 and r ≥ 2. A. Xiao and Y. Zhou ([arXiv:2610.19775](https://arxiv.org/abs/2610.19775), Theorem 5.1) settled the lattice form of the conjecture for every such pair with |B^n(r)| < 2^30 except (n, r) = (35, 3) and (805, 3). The paper settles these two.

**Theorem.** There is no lattice tiling of ℤ^35 by B^35(3), and there is no lattice tiling of ℤ^805 by B^805(3).

**Corollary.** If n ≥ 3, r ≥ 2 and |B^n(r)| < 2^30, then ℤ^n has no lattice tiling by B^n(r).

Here |B^35(3)| = 59711 = 29²·71 and |B^805(3)| = 696845031 = 3·29²·179·1543. Neither is prime, so the theorem says nothing about tilings that are not lattice tilings.

| Step | Content |
|---|---|
| Lemma 2.2, Proposition 2.3 | a lattice tiling gives a perfect code in a finite abelian group; the ball identity 6Σχ = T₁³ + 3T₁T₂ + 2T₃ − 6nT₁ in any commutative ring |
| Section 3 | power sums of a projection to ℤ/p vanish below p − 1; the pair counts c(h) + c(−h) are constant modulo p |
| Section 4 | the constant term of the ball identity modulo p² |
| Section 5 | n = 805: the constant term modulo 29² rules out every distribution left by the prime 29 |
| Section 6 | n = 35: the primes 71 and 29 separately, then one character into dual numbers over 𝔽₇₁[ℤ/29], which leads to a circulant system over 𝔽₇₁ with only the zero solution |

Lean 4 with Mathlib proves both theorems (`GolombWelch.golomb_welch_35`, `GolombWelch.golomb_welch_805`) from the definition of a lattice tiling, with every step of Sections 2 to 6; they depend only on the axioms propext, Classical.choice and Quot.sound, with no `sorry`, `native_decide` or `bv_decide`. Independent checks of the arithmetic in C, C++, Julia and Python.

Version 1.1.0 is the journal version for Journal of Combinatorial Theory, Series A: it cites this release instead of a DOI and leaves out the footnotes unrelated to the proof. The paper is also in `paper/paper1/` and its LaTeX source zip in `paper/paper2/`.

Files:
- `GolombWelchRadiusThree_final2.pdf`: the paper
- `GolombWelchRadiusThree_final2-tex.zip`: LaTeX source (`main.tex`, figures as PNG)
- `GolombWelchRadiusThree_final2-arxiv.tar.gz`: the same source, ready for arXiv

The repository also holds `preprintGolombWelchRadiusThree/GolombWelchRadiusThree.pdf` and `MasterGolombWelchRadiusThree_masterzipfinal2.zip`, which holds every file of the repository. Run `scripts/run_all.sh` to repeat the checks and `scripts/build_paper.sh` to rebuild the files above.
