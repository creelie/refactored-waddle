import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Lee balls and the ball identity

`ball n r` is the set of `a ∈ ℤ^n` with `∑ |a j| ≤ r`, built by recursion on `n`;
`mem_ball` identifies it with that set.  The main result of this file is the
*ball identity* for radius three: for elements `u j, v j` of a commutative ring with
`u j * v j = 1`, with `Y i = ∑ j, (u j ^ i + v j ^ i)` and `T i = 1 + Y i`,
`6 ∑_{a ∈ ball n 3} ∏ j u_j^{a_j} = T 1 ^ 3 + 3 T 1 T 2 + 2 T 3 - 6 n T 1`,
where `u_j^{a_j}` means `v_j^{-a_j}` for negative exponents.
-/

open Finset

namespace GolombWelch

/-- Prepending a first coordinate. -/
def consEmb {n : ℕ} (t : ℤ) : (Fin n → ℤ) ↪ (Fin (n + 1) → ℤ) :=
  ⟨fun b => Fin.cons t b, Fin.cons_right_injective (α := fun _ => ℤ) t⟩

@[simp] theorem consEmb_apply {n : ℕ} (t : ℤ) (b : Fin n → ℤ) :
    consEmb t b = Fin.cons t b := rfl

/-- The Lee ball of radius `r` in `ℤ^n`. -/
def ball : (n : ℕ) → ℕ → Finset (Fin n → ℤ)
  | 0, _ => {0}
  | n + 1, r => (Icc (-(r : ℤ)) r).biUnion fun t => (ball n (r - t.natAbs)).map (consEmb t)

theorem mem_ball {n r : ℕ} {a : Fin n → ℤ} : a ∈ ball n r ↔ ∑ j, (a j).natAbs ≤ r := by
  induction n generalizing r with
  | zero => simp [ball, Subsingleton.elim a 0]
  | succ n ih =>
    simp only [ball, mem_biUnion, mem_map, consEmb_apply, mem_Icc, ih,
      Fin.sum_univ_succ]
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, b, hb, rfl⟩
      simp only [Fin.cons_zero, Fin.cons_succ]
      omega
    · intro h
      refine ⟨a 0, ⟨by omega, by omega⟩, Fin.tail a, ?_, Fin.cons_self_tail a⟩
      simp only [Fin.tail]
      omega

theorem sum_ball_succ {M : Type*} [AddCommMonoid M] (n r : ℕ) (f : (Fin (n + 1) → ℤ) → M) :
    ∑ a ∈ ball (n + 1) r, f a =
      ∑ t ∈ Icc (-(r : ℤ)) r, ∑ b ∈ ball n (r - t.natAbs), f (Fin.cons t b) := by
  rw [ball, sum_biUnion]
  · simp [sum_map]
  · intro t _ t' _ htt'
    simp only [Function.onFun]
    rw [disjoint_left]
    intro a ha ha'
    simp only [mem_map, consEmb_apply] at ha ha'
    obtain ⟨b, -, rfl⟩ := ha
    obtain ⟨b', -, h⟩ := ha'
    exact htt' (by simpa using (congrFun h 0).symm)

/-- `pw u v t` is `u ^ t` for `t ≥ 0` and `v ^ (-t)` for `t < 0`. -/
def pw {R : Type*} [Monoid R] (u v : R) (t : ℤ) : R :=
  if 0 ≤ t then u ^ t.toNat else v ^ (-t).toNat

section Identity

variable {R : Type*} [CommRing R]

/-- The ball sum `∑_{a ∈ ball n r} ∏ j, pw (u j) (v j) (a j)`. -/
def ballSum (r : ℕ) {n : ℕ} (u v : Fin n → R) : R :=
  ∑ a ∈ ball n r, ∏ j, pw (u j) (v j) (a j)

/-- Power sums `Y i = ∑ j, (u j ^ i + v j ^ i)`. -/
def Ysum {n : ℕ} (u v : Fin n → R) (i : ℕ) : R := ∑ j, (u j ^ i + v j ^ i)

theorem ballSum_succ (r : ℕ) {n : ℕ} (u v : Fin (n + 1) → R) :
    ballSum r u v = ∑ t ∈ Icc (-(r : ℤ)) r,
      pw (u 0) (v 0) t * ballSum (r - t.natAbs) (Fin.tail u) (Fin.tail v) := by
  rw [ballSum, sum_ball_succ]
  refine sum_congr rfl fun t _ => ?_
  rw [ballSum, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [Fin.prod_univ_succ]
  simp [Fin.tail]

theorem Ysum_succ {n : ℕ} (u v : Fin (n + 1) → R) (i : ℕ) :
    Ysum u v i = (u 0 ^ i + v 0 ^ i) + Ysum (Fin.tail u) (Fin.tail v) i := by
  rw [Ysum, Fin.sum_univ_succ]; rfl

theorem Icc_three : Icc (-((3 : ℕ) : ℤ)) ((3 : ℕ) : ℤ) = {-3, -2, -1, 0, 1, 2, 3} := by decide
theorem Icc_two : Icc (-((2 : ℕ) : ℤ)) ((2 : ℕ) : ℤ) = {-2, -1, 0, 1, 2} := by decide
theorem Icc_one : Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by decide
theorem Icc_zero : Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) = {0} := by decide

section Steps

variable {n : ℕ} (u v : Fin (n + 1) → R)

theorem ballSum_succ_zero : ballSum 0 u v = ballSum 0 (Fin.tail u) (Fin.tail v) := by
  rw [ballSum_succ, Icc_zero]; simp [pw]

theorem ballSum_succ_one : ballSum 1 u v = v 0 * ballSum 0 (Fin.tail u) (Fin.tail v) +
    ballSum 1 (Fin.tail u) (Fin.tail v) + u 0 * ballSum 0 (Fin.tail u) (Fin.tail v) := by
  rw [ballSum_succ, Icc_one]; simp [pw]; ring

theorem ballSum_succ_two : ballSum 2 u v = v 0 ^ 2 * ballSum 0 (Fin.tail u) (Fin.tail v) +
    v 0 * ballSum 1 (Fin.tail u) (Fin.tail v) + ballSum 2 (Fin.tail u) (Fin.tail v) +
    u 0 * ballSum 1 (Fin.tail u) (Fin.tail v) + u 0 ^ 2 * ballSum 0 (Fin.tail u) (Fin.tail v) := by
  rw [ballSum_succ, Icc_two]; simp [pw]; ring

theorem ballSum_succ_three : ballSum 3 u v = v 0 ^ 3 * ballSum 0 (Fin.tail u) (Fin.tail v) +
    v 0 ^ 2 * ballSum 1 (Fin.tail u) (Fin.tail v) + v 0 * ballSum 2 (Fin.tail u) (Fin.tail v) +
    ballSum 3 (Fin.tail u) (Fin.tail v) + u 0 * ballSum 2 (Fin.tail u) (Fin.tail v) +
    u 0 ^ 2 * ballSum 1 (Fin.tail u) (Fin.tail v) +
    u 0 ^ 3 * ballSum 0 (Fin.tail u) (Fin.tail v) := by
  rw [ballSum_succ, Icc_three]; simp [pw]; ring

end Steps

/-- Closed forms of the ball sums of radius at most three. -/
theorem ballSum_closed (n : ℕ) (u v : Fin n → R) (huv : ∀ j, u j * v j = 1) :
    ballSum 0 u v = 1 ∧
    ballSum 1 u v = 1 + Ysum u v 1 ∧
    2 * ballSum 2 u v = 2 + 2 * Ysum u v 1 + Ysum u v 1 ^ 2 + Ysum u v 2 - 2 * n ∧
    6 * ballSum 3 u v = 6 + 6 * Ysum u v 1 + 3 * Ysum u v 1 ^ 2 + 3 * Ysum u v 2 - 6 * n +
      Ysum u v 1 ^ 3 + 3 * Ysum u v 1 * Ysum u v 2 + 2 * Ysum u v 3 - 6 * n * Ysum u v 1 := by
  induction n with
  | zero => simp [ballSum, Ysum, ball]
  | succ n ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih (Fin.tail u) (Fin.tail v) (fun j => huv _)
    have e : u 0 * v 0 = 1 := huv 0
    rw [ballSum_succ_zero, ballSum_succ_one, ballSum_succ_two, ballSum_succ_three,
      Ysum_succ u v 1, Ysum_succ u v 2, Ysum_succ u v 3]
    set B0 := ballSum 0 (Fin.tail u) (Fin.tail v)
    set B1 := ballSum 1 (Fin.tail u) (Fin.tail v)
    set B2 := ballSum 2 (Fin.tail u) (Fin.tail v)
    set B3 := ballSum 3 (Fin.tail u) (Fin.tail v)
    set Y1 := Ysum (Fin.tail u) (Fin.tail v) 1
    set Y2 := Ysum (Fin.tail u) (Fin.tail v) 2
    set Y3 := Ysum (Fin.tail u) (Fin.tail v) 3
    push_cast
    refine ⟨h0, ?_, ?_, ?_⟩
    · rw [h1, h0]; ring
    · rw [h0]
      linear_combination 2 * (u 0 + v 0) * h1 + h2 - 2 * e
    · rw [h0]
      linear_combination (u 0 + v 0) * 3 * h2 + 6 * (u 0 ^ 2 + v 0 ^ 2) * h1 + h3
        - (6 + 6 * Y1 + 6 * u 0 + 6 * v 0) * e

end Identity

end GolombWelch

namespace GolombWelch

section Identity

variable {R : Type*} [CommRing R]

/-- The ball identity for radius three. -/
theorem ball_identity (n : ℕ) (u v : Fin n → R) (huv : ∀ j, u j * v j = 1) :
    6 * ballSum 3 u v = (1 + Ysum u v 1) ^ 3 + 3 * (1 + Ysum u v 1) * (1 + Ysum u v 2) +
      2 * (1 + Ysum u v 3) - 6 * n * (1 + Ysum u v 1) := by
  rw [(ballSum_closed n u v huv).2.2.2]; ring

end Identity

/-- The number of points of the Lee ball of radius three. -/
theorem card_ball_three (n : ℕ) :
    6 * ((ball n 3).card : ℤ) = (1 + 2 * n) ^ 3 + 3 * (1 + 2 * n) ^ 2 + 2 * (1 + 2 * n) -
      6 * n * (1 + 2 * n) := by
  have h := ball_identity (R := ℤ) n (fun _ => 1) (fun _ => 1) (fun _ => by norm_num)
  simp only [ballSum, pw, one_pow, ite_self, Finset.prod_const_one, Finset.sum_const,
    nsmul_eq_mul, mul_one, Ysum, Finset.card_univ, Fintype.card_fin] at h
  rw [h]; ring

theorem card_ball_35 : (ball 35 3).card = 59711 := by
  have := card_ball_three 35; push_cast at this; omega

theorem card_ball_805 : (ball 805 3).card = 696845031 := by
  have := card_ball_three 805; push_cast at this; omega

end GolombWelch
