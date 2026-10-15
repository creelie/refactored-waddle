import GolombWelch.Counts
import Mathlib.Tactic.NormNum.Prime

/-!
# The ball identity modulo `29 ^ 2`

Let `x : Fin n → ZMod 29` be such that `29` divides `c h + c (-h)` for every `h ≠ 0`, where
`c h = #{j | x j = h}`.  Then in `(ZMod 841)[ZMod 29]` each `T i` (`i = 1, 2, 3`) is the
constant `A = 1 + 2 c 0` plus `29` times an element with zero constant term.  Products of two
such corrections vanish, and the coefficient of `0` in the ball identity reduces to
`6 m = A ^ 3 + 3 A ^ 2 + 2 A - 6 n A` in `ZMod 841`, where `m = |G| / 29`.
-/

open Finset AddMonoidAlgebra

namespace GolombWelch

local notation "R" => ZMod 841
local notation "H" => ZMod 29

instance fact_prime_29 : Fact (Nat.Prime 29) := ⟨by norm_num⟩

/-- The group ring element with coefficients `w`. -/
noncomputable def ofFun (w : H → R) : AddMonoidAlgebra R H := ∑ h, single h (w h)

theorem coeff_ofFun (w : H → R) (h : H) : (ofFun w).coeff h = w h := by
  classical
  simp [ofFun, coeff_sum, Finsupp.finsetSum_apply, coeff_single, Finsupp.single_apply]

theorem single_zero_mul' {S M : Type*} [CommRing S] [AddCommGroup M] (c : S)
    (f : AddMonoidAlgebra S M) : single 0 c * f = c • f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [mul_add, hf, hg, smul_add]
  | single a r => rw [single_mul_single, zero_add, smul_single']

theorem coeff_single_zero_mul {S M : Type*} [CommRing S] [AddCommGroup M] (c : S)
    (f : AddMonoidAlgebra S M) (h : M) : (single 0 c * f).coeff h = c * f.coeff h := by
  rw [single_zero_mul', coeff_smul_apply, smul_eq_mul]

theorem card_nsmul_eq {n : ℕ} (x : Fin n → H) (i : ℕ) (hi : (i : H) ≠ 0) (h : H) :
    #{j | i • x j = h} = #{j | x j = (i : H)⁻¹ * h} := by
  congr 1
  ext j
  simp only [mem_filter, mem_univ, true_and, nsmul_eq_mul]
  exact (eq_inv_mul_iff_mul_eq₀ hi).symm

theorem T_decomp {n : ℕ} (x : Fin n → H) (i : ℕ) (hi : (i : H) ≠ 0)
    (hdiv : ∀ h, h ≠ 0 → 29 ∣ #{j | x j = h} + #{j | x j = -h}) :
    ∃ W : AddMonoidAlgebra R H, W.coeff 0 = 0 ∧
      Tg R x i = single 0 (((1 + 2 * #{j | x j = 0} : ℕ) : R)) + single 0 29 * W := by
  classical
  set w : H → R := fun h => if h = 0 then 0 else
    (((#{j | x j = (i : H)⁻¹ * h} + #{j | x j = -((i : H)⁻¹ * h)}) / 29 : ℕ) : R) with hw
  refine ⟨ofFun w, by rw [coeff_ofFun]; simp [hw], ?_⟩
  ext h
  rw [coeff_Tg, coeff_add, Finsupp.add_apply, coeff_single_zero_mul, coeff_ofFun, coeff_single,
    Finsupp.single_apply, card_nsmul_eq x i hi, card_nsmul_eq x i hi]
  by_cases h0 : h = 0
  · subst h0
    simp [hw]
    ring
  · have h0' : (i : H)⁻¹ * h ≠ 0 := mul_ne_zero (inv_ne_zero hi) h0
    have hd := hdiv _ h0'
    simp only [h0, ite_false, Ne.symm h0, hw, zero_add, mul_neg]
    rw [← Nat.cast_add, ← Nat.mul_div_cancel' hd]
    push_cast
    rw [Nat.mul_div_cancel_left _ (by norm_num)]

theorem sq29 : (single 0 (29 : R) : AddMonoidAlgebra R H) * single 0 29 = 0 := by
  rw [single_mul_single, zero_add, show (29 * 29 : R) = 0 by decide, single_zero]

/-- The coefficient of `0` in the ball identity modulo `29 ^ 2`. -/
theorem coeff_zero_ball {n : ℕ} (x : Fin n → H)
    (hdiv : ∀ h, h ≠ 0 → 29 ∣ #{j | x j = h} + #{j | x j = -h}) :
    (6 * ∑ a ∈ ball n 3, single (∑ j, a j • x j) (1 : R)).coeff 0 =
      ((1 + 2 * #{j | x j = 0} : ℕ) : R) ^ 3 + 3 * ((1 + 2 * #{j | x j = 0} : ℕ) : R) ^ 2 +
        2 * ((1 + 2 * #{j | x j = 0} : ℕ) : R) - 6 * n * ((1 + 2 * #{j | x j = 0} : ℕ) : R) := by
  classical
  obtain ⟨W1, h1, e1⟩ := T_decomp x 1 (by decide) hdiv
  obtain ⟨W2, h2, e2⟩ := T_decomp x 2 (by decide) hdiv
  obtain ⟨W3, h3, e3⟩ := T_decomp x 3 (by decide) hdiv
  rw [ball_identity_groupRing, e1, e2, e3]
  set A : R := ((1 + 2 * #{j | x j = 0} : ℕ) : R)
  set a : AddMonoidAlgebra R H := single 0 A with ha
  set q : AddMonoidAlgebra R H := single 0 29 with hq
  have key : (a + q * W1) ^ 3 + 3 * (a + q * W1) * (a + q * W2) + 2 * (a + q * W3) -
      6 * (n : AddMonoidAlgebra R H) * (a + q * W1) =
      (a ^ 3 + 3 * a ^ 2 + 2 * a - 6 * (n : AddMonoidAlgebra R H) * a) +
        q * ((3 * a ^ 2 + 3 * a - 6 * (n : AddMonoidAlgebra R H)) * W1 + 3 * a * W2 + 2 * W3) +
        (q * q) * (3 * a * W1 ^ 2 + 3 * W1 * W2 + q * W1 ^ 3) := by ring
  rw [key, sq29, zero_mul, add_zero]
  have c1 : a ^ 3 + 3 * a ^ 2 + 2 * a - 6 * (n : AddMonoidAlgebra R H) * a =
      single 0 (A ^ 3 + 3 * A ^ 2 + 2 * A - 6 * n * A) := by
    rw [show single 0 (A ^ 3 + 3 * A ^ 2 + 2 * A - 6 * n * A) =
      (singleZeroRingHom : R →+* AddMonoidAlgebra R H) (A ^ 3 + 3 * A ^ 2 + 2 * A - 6 * n * A) from rfl]
    simp only [map_add, map_sub, map_mul, map_pow, map_natCast, map_ofNat]
    rfl
  have c2 : 3 * a ^ 2 + 3 * a - 6 * (n : AddMonoidAlgebra R H) =
      single 0 (3 * A ^ 2 + 3 * A - 6 * n) := by
    rw [show single 0 (3 * A ^ 2 + 3 * A - 6 * n) =
      (singleZeroRingHom : R →+* AddMonoidAlgebra R H) (3 * A ^ 2 + 3 * A - 6 * n) from rfl]
    simp only [map_add, map_sub, map_mul, map_pow, map_natCast, map_ofNat]
    rfl
  have c3 : 3 * a = single 0 (3 * A) := by
    rw [ha, show (3 : AddMonoidAlgebra R H) = single 0 3 from rfl, single_mul_single, zero_add]
  have c4 : (2 : AddMonoidAlgebra R H) = single 0 2 := rfl
  rw [c1, c2, c3, c4, hq, coeff_add, Finsupp.add_apply, coeff_single_zero_mul, coeff_add,
    coeff_add, Finsupp.add_apply, Finsupp.add_apply, coeff_single_zero_mul, coeff_single_zero_mul,
    coeff_single_zero_mul, h1, h2, h3, coeff_single, Finsupp.single_eq_same]
  ring

section Perfect

variable {G : Type*} [AddCommGroup G] [Fintype G] {n : ℕ} {g : Fin n → G}

/-- The coefficient of `0` on the left of the ball identity. -/
theorem coeff_zero_lhs (hg : IsPerfect g) (ψ : G →+ H) (hψ : Function.Surjective ψ) :
    (6 * ∑ a ∈ ball n 3, single (∑ j, a j • ψ (g j)) (1 : R)).coeff 0 =
      ((6 * (Fintype.card G / 29) : ℕ) : R) := by
  classical
  rw [sum_ball_uniform hg ψ hψ (fun h => single h (1 : R)), ZMod.card, nsmul_eq_mul,
    show (6 : AddMonoidAlgebra R H) = single 0 6 from rfl,
    show ((Fintype.card G / 29 : ℕ) : AddMonoidAlgebra R H) = single 0 ((Fintype.card G / 29 : ℕ) : R)
      from rfl, coeff_single_zero_mul, coeff_single_zero_mul, coeff_sum, Finsupp.finsetSum_apply]
  simp only [coeff_single, Finsupp.single_apply]
  rw [sum_ite_eq' univ (0 : H) (fun _ => (1 : R))]
  simp only [mem_univ, ite_true]
  push_cast; ring

/-- The ball identity at `0` modulo `29 ^ 2`. -/
theorem mod841 (hg : IsPerfect g) (ψ : G →+ H) (hψ : Function.Surjective ψ)
    (hdiv : ∀ h, h ≠ 0 → 29 ∣ #{j | ψ (g j) = h} + #{j | ψ (g j) = -h}) :
    ((6 * (Fintype.card G / 29) : ℕ) : R) =
      ((1 + 2 * #{j | ψ (g j) = 0} : ℕ) : R) ^ 3 +
        3 * ((1 + 2 * #{j | ψ (g j) = 0} : ℕ) : R) ^ 2 +
        2 * ((1 + 2 * #{j | ψ (g j) = 0} : ℕ) : R) -
        6 * n * ((1 + 2 * #{j | ψ (g j) = 0} : ℕ) : R) := by
  rw [← coeff_zero_lhs hg ψ hψ, coeff_zero_ball (fun j => ψ (g j)) hdiv]

end Perfect

end GolombWelch
