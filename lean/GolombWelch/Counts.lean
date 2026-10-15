import GolombWelch.Moments

/-!
# Counting the projected coordinates

For `x : Fin n → ZMod p` let `c h = #{j | x j = h}`.  When the power sums `P x k` vanish for
`1 ≤ k < p - 1`, the moment argument shows that `c h + c (-h)` is constant modulo `p` on
`h ≠ 0`, equal to `-P x (p - 1)`.
-/

open Finset AddMonoidAlgebra

namespace GolombWelch

variable {p : ℕ} [hp : Fact p.Prime]

local notation "F" => ZMod p

theorem count_eq {n : ℕ} (x : Fin n → F) (hP : ∀ k, 1 ≤ k → k < p - 1 → P x k = 0) (h : F) :
    (if h = 0 then (1 : F) else 0) + (#{j | x j = h} : F) + (#{j | x j = -h} : F) -
      (if h = 0 then 1 + 2 * (n : F) else 0) = -P x (p - 1) := by
  classical
  have hp1 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
  set f : AddMonoidAlgebra F F := Tg F x 1 - single 0 (1 + 2 * (n : F)) with hf
  have hmom : ∀ k, 1 ≤ k → mom k f = P x k := by
    intro k hk
    rw [hf, map_sub, mom_Tg x 1 k hk, mom_const k hk, Nat.cast_one, one_pow, one_mul, sub_zero]
  have hmom0 : mom 0 f = 0 := by
    rw [hf, map_sub, mom_zero_Tg, mom_single, pow_zero, mul_one, sub_self]
  have hl := lagrange f (fun k hk => by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact hmom0
    · rw [hmom k hpos]; exact hP k hpos hk) h
  rw [hmom (p - 1) hp1, hf, coeff_sub, Finsupp.sub_apply, coeff_Tg, coeff_single,
    Finsupp.single_apply] at hl
  simp only [one_smul] at hl
  rw [← hl]
  congr 1
  by_cases h0 : h = 0
  · simp [h0]
  · simp [h0, Ne.symm h0]

/-- `c h + c (-h)` for `h ≠ 0`. -/
theorem count_pair {n : ℕ} (x : Fin n → F) (hP : ∀ k, 1 ≤ k → k < p - 1 → P x k = 0) {h : F}
    (h0 : h ≠ 0) : (#{j | x j = h} : F) + (#{j | x j = -h} : F) = -P x (p - 1) := by
  have := count_eq x hP h
  simpa [h0] using this

/-- `c 0`. -/
theorem count_zero {n : ℕ} (x : Fin n → F) (hP : ∀ k, 1 ≤ k → k < p - 1 → P x k = 0) :
    2 * (#{j | x j = 0} : F) - 2 * (n : F) = -P x (p - 1) := by
  have := count_eq x hP 0
  simp only [ite_true, neg_zero] at this
  rw [← this]; ring

end GolombWelch
