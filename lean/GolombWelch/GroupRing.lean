import GolombWelch.Ball
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The ball identity in a group ring

For an additive group `H` and `x : Fin n → H` the ball identity, applied to the units
`single (x j) 1` of `R[H]`, reads
`6 ∑_{a ∈ ball n 3} single (∑ j, a j • x j) 1 = T 1 ^ 3 + 3 T 1 T 2 + 2 T 3 - 6 n T 1`,
with `T i = 1 + ∑ j, (single (i • x j) 1 + single (-(i • x j)) 1)`.
-/

open Finset AddMonoidAlgebra

namespace GolombWelch

variable {R : Type*} [CommRing R] {H : Type*} [AddCommGroup H]

theorem single_pw (x : H) (t : ℤ) :
    pw (single x (1 : R)) (single (-x) 1) t = single (t • x) 1 := by
  unfold pw
  split_ifs with h
  · rw [single_pow, one_pow]
    congr 1
    rw [← natCast_zsmul, Int.toNat_of_nonneg h]
  · rw [single_pow, one_pow]
    congr 1
    rw [← natCast_zsmul, Int.toNat_of_nonneg (by omega), smul_neg, ← neg_smul, neg_neg]

/-- The elements `T i` of the group ring. -/
noncomputable def Tg (R : Type*) [CommRing R] {n : ℕ} (x : Fin n → H) (i : ℕ) : AddMonoidAlgebra R H :=
  1 + ∑ j, (single (i • x j) 1 + single (-(i • x j)) 1)

theorem ball_identity_groupRing (n : ℕ) (x : Fin n → H) :
    6 * ∑ a ∈ ball n 3, single (∑ j, a j • x j) (1 : R) =
      Tg R x 1 ^ 3 + 3 * Tg R x 1 * Tg R x 2 + 2 * Tg R x 3 - 6 * n * Tg R x 1 := by
  have h := ball_identity (R := AddMonoidAlgebra R H) n (fun j => single (x j) 1)
    (fun j => single (-x j) 1) (fun j => by rw [single_mul_single]; simp [one_def])
  have hb : ballSum 3 (fun j => single (x j) (1 : R)) (fun j => single (-x j) 1) =
      ∑ a ∈ ball n 3, single (∑ j, a j • x j) (1 : R) := by
    refine sum_congr rfl fun a _ => ?_
    simp only [single_pw]
    rw [prod_single, prod_const_one]
  have hY : ∀ i : ℕ, Ysum (fun j => single (x j) (1 : R)) (fun j => single (-x j) 1) i =
      ∑ j, (single (i • x j) 1 + single (-(i • x j)) 1) := by
    intro i
    refine sum_congr rfl fun j _ => ?_
    rw [single_pow, single_pow, one_pow, smul_neg]
  rw [hb, hY, hY, hY] at h
  simpa [Tg] using h


theorem coeff_Tg [DecidableEq H] {n : ℕ} (x : Fin n → H) (i : ℕ) (h : H) :
    (Tg R x i).coeff h = (if h = 0 then 1 else 0) + (#{j | i • x j = h} : R) +
      (#{j | i • x j = -h} : R) := by
  rw [Tg, coeff_add, Finsupp.add_apply, one_def, coeff_sum, Finsupp.finsetSum_apply]
  simp only [coeff_add, Finsupp.add_apply, coeff_single, Finsupp.single_apply, sum_add_distrib]
  rw [sum_boole, sum_boole, add_assoc]
  congr 2
  · simp [eq_comm]
  · congr 2; ext j; simp [neg_eq_iff_eq_neg]

end GolombWelch
