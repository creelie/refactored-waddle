import GolombWelch.Uniform
import Mathlib.FieldTheory.Finite.Basic

/-!
# Moments over `ZMod p`

For `f` in the group ring `(ZMod p)[ZMod p]` the `k`-th moment is
`mom k f = ∑ h, f.coeff h * h ^ k`.  Moments satisfy the binomial product rule, and a
function all of whose moments of order `< p - 1` vanish is constant (`lagrange`).
Applied to the ball identity they show that the power sums
`P x k = ∑ j, (x j ^ k + (-x j) ^ k)` of a projection of a perfect code vanish in low degree.
-/

open Finset AddMonoidAlgebra

namespace GolombWelch

variable {p : ℕ} [hp : Fact p.Prime]

local notation "F" => ZMod p

/-- The `k`-th moment, as an additive homomorphism. -/
noncomputable def mom (k : ℕ) : AddMonoidAlgebra F F →+ F where
  toFun f := ∑ h, f.coeff h * h ^ k
  map_zero' := by simp
  map_add' f g := by simp [coeff_add, add_mul, sum_add_distrib]

theorem mom_apply (k : ℕ) (f : AddMonoidAlgebra F F) : mom k f = ∑ h, f.coeff h * h ^ k := rfl

theorem mom_single (k : ℕ) (a r : F) : mom k (single a r) = r * a ^ k := by
  classical
  rw [mom_apply]
  simp only [coeff_single, Finsupp.single_apply, ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]

theorem mom_smul (k : ℕ) (c : F) (f : AddMonoidAlgebra F F) : mom k (c • f) = c * mom k f := by
  simp [mom_apply, coeff_smul, mul_sum, mul_assoc]

/-- The product rule for moments. -/
theorem mom_mul (k : ℕ) (f g : AddMonoidAlgebra F F) :
    mom k (f * g) = ∑ i ∈ range (k + 1), (k.choose i : F) * mom i f * mom (k - i) g := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simp [add_mul, h₁, h₂, mul_add, sum_add_distrib]
  | single a r =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ => simp [mul_add, h₁, h₂, sum_add_distrib]
    | single b s =>
      rw [single_mul_single, mom_single, add_pow, mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [mom_single, mom_single]; ring

theorem mom_zero_mul (f g : AddMonoidAlgebra F F) : mom 0 (f * g) = mom 0 f * mom 0 g := by
  rw [mom_mul]; simp

/-- `f` is flat below `v`: its moments of orders `1, …, v - 1` vanish. -/
def IsFlat (v : ℕ) (f : AddMonoidAlgebra F F) : Prop := ∀ i, 1 ≤ i → i < v → mom i f = 0

theorem isFlat_const (v : ℕ) (c : F) : IsFlat v (single 0 c) := by
  intro i hi _
  rw [mom_single, zero_pow (by omega), mul_zero]

theorem mom_const (v : ℕ) (hv : 1 ≤ v) (c : F) : mom v (single 0 c) = 0 := by
  rw [mom_single, zero_pow (by omega), mul_zero]

theorem IsFlat.add {v : ℕ} {f g : AddMonoidAlgebra F F} (hf : IsFlat v f) (hg : IsFlat v g) :
    IsFlat v (f + g) := fun i h1 h2 => by rw [map_add, hf i h1 h2, hg i h1 h2, add_zero]

theorem IsFlat.sub {v : ℕ} {f g : AddMonoidAlgebra F F} (hf : IsFlat v f) (hg : IsFlat v g) :
    IsFlat v (f - g) := fun i h1 h2 => by rw [map_sub, hf i h1 h2, hg i h1 h2, sub_zero]

theorem IsFlat.mul {v : ℕ} {f g : AddMonoidAlgebra F F} (hf : IsFlat v f) (hg : IsFlat v g) :
    IsFlat v (f * g) := by
  intro k h1 h2
  rw [mom_mul]
  refine sum_eq_zero fun i hi => ?_
  have hi' : i ≤ k := Nat.lt_succ_iff.1 (mem_range.1 hi)
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [Nat.sub_zero, hg k h1 h2, mul_zero]
  · rw [hf i hpos (by omega), mul_zero, zero_mul]

theorem mom_flat_mul {v : ℕ} (hv : 1 ≤ v) {f g : AddMonoidAlgebra F F} (hf : IsFlat v f)
    (_hg : IsFlat v g) : mom v (f * g) = mom 0 f * mom v g + mom v f * mom 0 g := by
  rw [mom_mul, sum_eq_add 0 v (by omega)]
  · simp
  · intro i hi hne
    have hi' : i ≤ v := Nat.lt_succ_iff.1 (mem_range.1 hi)
    rw [hf i (by omega) (by omega), mul_zero, zero_mul]
  · intro h; exact absurd (mem_range.2 (by omega)) h
  · intro h; exact absurd (mem_range.2 (by omega)) h


theorem single_zero_mul (c : F) (f : AddMonoidAlgebra F F) : single 0 c * f = c • f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [mul_add, hf, hg, smul_add]
  | single a r => rw [single_mul_single, zero_add, smul_single']

theorem mom_const_mul (k : ℕ) (c : F) (f : AddMonoidAlgebra F F) :
    mom k (single 0 c * f) = c * mom k f := by
  rw [single_zero_mul, mom_smul]

/-- Power sums of `± x j`. -/
def P {n : ℕ} (x : Fin n → F) (k : ℕ) : F := ∑ j, (x j ^ k + (-x j) ^ k)

theorem P_odd {n : ℕ} (x : Fin n → F) {k : ℕ} (hk : Odd k) : P x k = 0 := by
  simp [P, hk.neg_pow]

theorem mom_Tg {n : ℕ} (x : Fin n → F) (i k : ℕ) (hk : 1 ≤ k) :
    mom k (Tg F x i) = (i : F) ^ k * P x k := by
  rw [Tg, map_add, one_def, mom_single, zero_pow (by omega), mul_zero, zero_add, map_sum, P,
    mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [map_add, mom_single, mom_single, nsmul_eq_mul, ← mul_neg, mul_pow, mul_pow, one_mul,
    one_mul, mul_add]

theorem mom_zero_Tg {n : ℕ} (x : Fin n → F) (i : ℕ) : mom 0 (Tg F x i) = 1 + 2 * n := by
  rw [Tg, map_add, one_def, mom_single, map_sum]
  simp only [map_add, mom_single, pow_zero, mul_one, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

theorem isFlat_Tg {n : ℕ} (x : Fin n → F) (i v : ℕ) (hflat : ∀ k, 1 ≤ k → k < v → P x k = 0) :
    IsFlat v (Tg F x i) := fun k h1 h2 => by rw [mom_Tg x i k h1, hflat k h1 h2, mul_zero]

/-- The coefficient `κ` of the moment identity. -/
def kappa (n v : ℕ) : F :=
  3 * (1 + 2 * n) ^ 2 + 3 * (1 + 2 * n) * (1 + 2 ^ v) + 2 * 3 ^ v - 6 * n

theorem mom_rhs {n : ℕ} (x : Fin n → F) (v : ℕ) (hv : 1 ≤ v)
    (hflat : ∀ k, 1 ≤ k → k < v → P x k = 0) :
    mom v (Tg F x 1 ^ 3 + 3 * Tg F x 1 * Tg F x 2 + 2 * Tg F x 3 -
        6 * (n : AddMonoidAlgebra F F) * Tg F x 1) =
      kappa n v * P x v := by
  have f1 := isFlat_Tg x 1 v hflat
  have f2 := isFlat_Tg x 2 v hflat
  have m1 := mom_Tg x 1 v hv
  have m2 := mom_Tg x 2 v hv
  have m3 := mom_Tg x 3 v hv
  have z1 := mom_zero_Tg x 1
  have z2 := mom_zero_Tg x 2
  have c3 : (3 : AddMonoidAlgebra F F) = single 0 3 := rfl
  have c2 : (2 : AddMonoidAlgebra F F) = single 0 2 := rfl
  have c6n : (6 : AddMonoidAlgebra F F) * (n : AddMonoidAlgebra F F) = single 0 (6 * (n : F)) := by
    rw [show (6 : AddMonoidAlgebra F F) = single 0 6 from rfl,
      show ((n : ℕ) : AddMonoidAlgebra F F) = single 0 (n : F) from rfl, single_mul_single,
      zero_add]
  rw [pow_three, mul_assoc 3, c3, c2, c6n, map_sub, map_add, map_add, mom_const_mul,
    mom_const_mul, mom_const_mul, mom_flat_mul hv f1 (f1.mul f1), mom_flat_mul hv f1 f1,
    mom_flat_mul hv f1 f2, mom_zero_mul, m1, m2, m3, z1, z2, kappa]
  push_cast
  ring


theorem sum_pow_card_sub_one : ∑ h : F, h ^ (p - 1) = -1 := by
  classical
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  have e : ∀ h : F, h ^ (p - 1) = if h = 0 then 0 else 1 := by
    intro h
    split_ifs with h0
    · rw [h0, zero_pow hp1]
    · exact ZMod.pow_card_sub_one_eq_one h0
  rw [sum_congr rfl fun h _ => e h, sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul,
    mul_one, filter_ne' univ (0 : F), card_erase_of_mem (mem_univ _), card_univ, ZMod.card,
    Nat.cast_sub hp.out.one_le]
  simp

theorem sum_pow_lt (k : ℕ) (hk : k < p - 1) : ∑ h : F, h ^ k = 0 :=
  FiniteField.sum_pow_lt_card_sub_one (K := F) k (by rw [ZMod.card]; exact hk)

section Perfect

variable {G : Type*} [AddCommGroup G] [Fintype G] {n : ℕ} {g : Fin n → G}

/-- The moment identity for a projection of a perfect code. -/
theorem key_moment (hg : IsPerfect g) (ψ : G →+ F) (hψ : Function.Surjective ψ) (v : ℕ)
    (hv : 1 ≤ v) (hflat : ∀ k, 1 ≤ k → k < v → P (fun j => ψ (g j)) k = 0) :
    kappa n v * P (fun j => ψ (g j)) v =
      6 * ((Fintype.card G / p : ℕ) : F) * ∑ h : F, h ^ v := by
  have hid := congrArg (mom v) (ball_identity_groupRing (R := F) n (fun j => ψ (g j)))
  rw [mom_rhs _ v hv hflat] at hid
  rw [← hid, show (6 : AddMonoidAlgebra F F) = single 0 6 from rfl, mom_const_mul, map_sum]
  simp only [mom_single, one_mul]
  rw [sum_ball_uniform hg ψ hψ (fun h => h ^ v), ZMod.card, nsmul_eq_mul, mul_assoc]

/-- Low power sums vanish when `κ` does not. -/
theorem P_vanish (hg : IsPerfect g) (ψ : G →+ F) (hψ : Function.Surjective ψ) (L : ℕ)
    (hL : L ≤ p - 1) (hκ : ∀ v, 1 ≤ v → v < L → Even v → kappa n v ≠ (0 : F)) :
    ∀ k, 1 ≤ k → k < L → P (fun j => ψ (g j)) k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro h1 h2
    rcases Nat.even_or_odd k with he | ho
    · have e := key_moment hg ψ hψ k h1 (fun i hi1 hi2 => ih i hi2 hi1 (by omega))
      rw [sum_pow_lt k (by omega), mul_zero] at e
      exact (mul_eq_zero.1 e).resolve_left (hκ k h1 h2 he)
    · exact P_odd _ ho

end Perfect

/-- A function on `ZMod p` whose moments of order `< p - 1` vanish is constant. -/
theorem lagrange (f : AddMonoidAlgebra F F) (hf : ∀ k, k < p - 1 → mom k f = 0) (h : F) :
    f.coeff h = -mom (p - 1) f := by
  classical
  have hp1 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
  have e1 : ∑ g, f.coeff g * (g - h) ^ (p - 1) = mom (p - 1) f := by
    have hexp : ∀ g : F, (g - h) ^ (p - 1) =
        ∑ i ∈ range (p - 1 + 1), g ^ i * (-h) ^ (p - 1 - i) * ((p - 1).choose i : F) := by
      intro g; rw [sub_eq_add_neg, add_pow]
    simp_rw [hexp, mul_sum]
    rw [sum_comm, sum_range_succ, sum_eq_zero, zero_add]
    · simp [mom_apply]
    · intro i hi
      have : ∑ g, f.coeff g * (g ^ i * (-h) ^ (p - 1 - i) * ((p - 1).choose i : F)) =
          mom i f * ((-h) ^ (p - 1 - i) * ((p - 1).choose i : F)) := by
        rw [mom_apply, sum_mul]; refine sum_congr rfl fun g _ => by ring
      rw [this, hf i (mem_range.1 hi), zero_mul]
  have e2 : ∑ g, f.coeff g * (g - h) ^ (p - 1) = mom 0 f - f.coeff h := by
    have hpow : ∀ g : F, (g - h) ^ (p - 1) = if g = h then 0 else 1 := by
      intro g
      split_ifs with hgh
      · rw [hgh, sub_self, zero_pow (by omega)]
      · exact ZMod.pow_card_sub_one_eq_one (sub_ne_zero.2 hgh)
    simp_rw [hpow, mul_ite, mul_zero, mul_one]
    rw [mom_apply, sum_ite, sum_const_zero, zero_add]
    simp only [pow_zero, mul_one]
    rw [← sum_filter_add_sum_filter_not univ (fun g => g = h)]
    simp [filter_eq']
  rw [hf 0 (by omega)] at e2
  linear_combination e2 - e1

end GolombWelch
