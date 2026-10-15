import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ReduceModChar
import Mathlib.Data.ZMod.Basic

/-!
# Two circulant systems over `ZMod 71`

If `μ` is `28`-periodic and `a μ k + b μ (k + 1) + μ (k + 5) = 0` for every `k`, with
`X ^ 5 + b X + a` invertible modulo `X ^ 28 - 1` over `ZMod 71`, then `μ = 0`.  The
coefficients of the combinations are those of the inverse.
-/

namespace GolombWelch

theorem circ_zero_a (μ : ℕ → ZMod 71) (hper : ∀ k, μ (k + 28) = μ k)
    (hE : ∀ k, 56 * μ k + 13 * μ (k + 1) + μ (k + 5) = 0) : μ 0 = 0 := by
  have e0 : 56 * μ 0 + 13 * μ 1 + μ 5 = 0 := hE 0
  have e1 : 56 * μ 1 + 13 * μ 2 + μ 6 = 0 := hE 1
  have e2 : 56 * μ 2 + 13 * μ 3 + μ 7 = 0 := hE 2
  have e3 : 56 * μ 3 + 13 * μ 4 + μ 8 = 0 := hE 3
  have e4 : 56 * μ 4 + 13 * μ 5 + μ 9 = 0 := hE 4
  have e5 : 56 * μ 5 + 13 * μ 6 + μ 10 = 0 := hE 5
  have e6 : 56 * μ 6 + 13 * μ 7 + μ 11 = 0 := hE 6
  have e7 : 56 * μ 7 + 13 * μ 8 + μ 12 = 0 := hE 7
  have e8 : 56 * μ 8 + 13 * μ 9 + μ 13 = 0 := hE 8
  have e9 : 56 * μ 9 + 13 * μ 10 + μ 14 = 0 := hE 9
  have e10 : 56 * μ 10 + 13 * μ 11 + μ 15 = 0 := hE 10
  have e11 : 56 * μ 11 + 13 * μ 12 + μ 16 = 0 := hE 11
  have e12 : 56 * μ 12 + 13 * μ 13 + μ 17 = 0 := hE 12
  have e13 : 56 * μ 13 + 13 * μ 14 + μ 18 = 0 := hE 13
  have e14 : 56 * μ 14 + 13 * μ 15 + μ 19 = 0 := hE 14
  have e15 : 56 * μ 15 + 13 * μ 16 + μ 20 = 0 := hE 15
  have e16 : 56 * μ 16 + 13 * μ 17 + μ 21 = 0 := hE 16
  have e17 : 56 * μ 17 + 13 * μ 18 + μ 22 = 0 := hE 17
  have e18 : 56 * μ 18 + 13 * μ 19 + μ 23 = 0 := hE 18
  have e19 : 56 * μ 19 + 13 * μ 20 + μ 24 = 0 := hE 19
  have e20 : 56 * μ 20 + 13 * μ 21 + μ 25 = 0 := hE 20
  have e21 : 56 * μ 21 + 13 * μ 22 + μ 26 = 0 := hE 21
  have e22 : 56 * μ 22 + 13 * μ 23 + μ 27 = 0 := hE 22
  have e23 : 56 * μ 23 + 13 * μ 24 + μ 0 = 0 := by rw [← hper 0]; exact hE 23
  have e24 : 56 * μ 24 + 13 * μ 25 + μ 1 = 0 := by rw [← hper 1]; exact hE 24
  have e25 : 56 * μ 25 + 13 * μ 26 + μ 2 = 0 := by rw [← hper 2]; exact hE 25
  have e26 : 56 * μ 26 + 13 * μ 27 + μ 3 = 0 := by rw [← hper 3]; exact hE 26
  have e27 : 56 * μ 27 + 13 * μ 0 + μ 4 = 0 := by rw [← hper 4, ← hper 0]; exact hE 27
  linear_combination (norm := ring_nf) 23 * e0 + 48 * e1 + 24 * e2 + 16 * e3 + 61 * e4 + 26 * e5 + 21 * e6 + 34 * e7 + 40 * e8 + 34 * e9 + 17 * e10 + 54 * e11 + 68 * e12 + 19 * e13 + 14 * e14 + 18 * e15 + 5 * e16 + 42 * e17 + 14 * e18 + 32 * e19 + 10 * e20 + 9 * e21 + 39 * e22 + 30 * e23 + 66 * e24 + 20 * e25 + 70 * e26 + 68 * e27
  reduce_mod_char

theorem circ_zero_b (μ : ℕ → ZMod 71) (hper : ∀ k, μ (k + 28) = μ k)
    (hE : ∀ k, 16 * μ k + 42 * μ (k + 1) + μ (k + 5) = 0) : μ 0 = 0 := by
  have e0 : 16 * μ 0 + 42 * μ 1 + μ 5 = 0 := hE 0
  have e1 : 16 * μ 1 + 42 * μ 2 + μ 6 = 0 := hE 1
  have e2 : 16 * μ 2 + 42 * μ 3 + μ 7 = 0 := hE 2
  have e3 : 16 * μ 3 + 42 * μ 4 + μ 8 = 0 := hE 3
  have e4 : 16 * μ 4 + 42 * μ 5 + μ 9 = 0 := hE 4
  have e5 : 16 * μ 5 + 42 * μ 6 + μ 10 = 0 := hE 5
  have e6 : 16 * μ 6 + 42 * μ 7 + μ 11 = 0 := hE 6
  have e7 : 16 * μ 7 + 42 * μ 8 + μ 12 = 0 := hE 7
  have e8 : 16 * μ 8 + 42 * μ 9 + μ 13 = 0 := hE 8
  have e9 : 16 * μ 9 + 42 * μ 10 + μ 14 = 0 := hE 9
  have e10 : 16 * μ 10 + 42 * μ 11 + μ 15 = 0 := hE 10
  have e11 : 16 * μ 11 + 42 * μ 12 + μ 16 = 0 := hE 11
  have e12 : 16 * μ 12 + 42 * μ 13 + μ 17 = 0 := hE 12
  have e13 : 16 * μ 13 + 42 * μ 14 + μ 18 = 0 := hE 13
  have e14 : 16 * μ 14 + 42 * μ 15 + μ 19 = 0 := hE 14
  have e15 : 16 * μ 15 + 42 * μ 16 + μ 20 = 0 := hE 15
  have e16 : 16 * μ 16 + 42 * μ 17 + μ 21 = 0 := hE 16
  have e17 : 16 * μ 17 + 42 * μ 18 + μ 22 = 0 := hE 17
  have e18 : 16 * μ 18 + 42 * μ 19 + μ 23 = 0 := hE 18
  have e19 : 16 * μ 19 + 42 * μ 20 + μ 24 = 0 := hE 19
  have e20 : 16 * μ 20 + 42 * μ 21 + μ 25 = 0 := hE 20
  have e21 : 16 * μ 21 + 42 * μ 22 + μ 26 = 0 := hE 21
  have e22 : 16 * μ 22 + 42 * μ 23 + μ 27 = 0 := hE 22
  have e23 : 16 * μ 23 + 42 * μ 24 + μ 0 = 0 := by rw [← hper 0]; exact hE 23
  have e24 : 16 * μ 24 + 42 * μ 25 + μ 1 = 0 := by rw [← hper 1]; exact hE 24
  have e25 : 16 * μ 25 + 42 * μ 26 + μ 2 = 0 := by rw [← hper 2]; exact hE 25
  have e26 : 16 * μ 26 + 42 * μ 27 + μ 3 = 0 := by rw [← hper 3]; exact hE 26
  have e27 : 16 * μ 27 + 42 * μ 0 + μ 4 = 0 := by rw [← hper 4, ← hper 0]; exact hE 27
  linear_combination (norm := ring_nf) 36 * e0 + 66 * e1 + 54 * e2 + 21 * e3 + 56 * e4 + 46 * e5 + 26 * e6 + 26 * e7 + 68 * e8 + 31 * e9 + 40 * e10 + 62 * e11 + 22 * e12 + 9 * e13 + 41 * e14 + 23 * e15 + 60 * e16 + 63 * e17 + 16 * e18 + 22 * e19 + 34 * e20 + 49 * e21 + 5 * e22 + 48 * e23 + 59 * e24 + 56 * e25 + 23 * e26 + 68 * e27
  reduce_mod_char

end GolombWelch
