import GolombWelch.Dual

/-!
# The joint step

Suppose that `c (t) + c (-t) = d` for every `t ≠ 0`, where `c` counts the coordinates of the
projection `y` to `ZMod 29`.  Then `T i = A + d S` with `S = ∑_t single t 1`, and `S` kills the
`ε`-parts of the dual numbers.  The `ε`-part of the ball identity becomes the relation
`α m t + 6 A m (2⁻¹ t) + 6 m (3⁻¹ t) = 0` for
`m t = ∑_{y j = t} x j - ∑_{y j = -t} x j`.
-/

open Finset AddMonoidAlgebra Multiplicative TrivSqZeroExt

namespace GolombWelch

local notation "K" => ZMod 71
local notation "H" => ZMod 29
local notation "B" => AddMonoidAlgebra K H

/-- The sum of all group elements. -/
noncomputable def Sall : B := ∑ t : H, single t 1

theorem coeff_Sall (t : H) : Sall.coeff t = 1 := by
  classical
  simp [Sall, coeff_sum, Finsupp.finsetSum_apply, coeff_single, Finsupp.single_apply]

theorem Sall_mul_single (t : H) (r : K) : Sall * single t r = r • Sall := by
  rw [Sall, sum_mul, smul_sum]
  simp only [single_mul_single, one_mul, smul_single', mul_one]
  exact Fintype.sum_equiv (Equiv.addRight t) _ _ (fun u => rfl)

variable {n : ℕ}

/-- The `ε`-part of `T i`. -/
noncomputable def Nn (x : Fin n → K) (y : Fin n → H) (i : ℕ) : B :=
  ∑ j, ((i • x j) • single (i • y j) 1 + (-(i • x j)) • single (-(i • y j)) 1)

theorem Sall_mul_Nn (x : Fin n → K) (y : Fin n → H) (i : ℕ) : Sall * Nn x y i = 0 := by
  rw [Nn, mul_sum]
  refine sum_eq_zero fun j _ => ?_
  rw [mul_add, mul_smul_comm, mul_smul_comm, Sall_mul_single, Sall_mul_single, one_smul,
    neg_smul, add_neg_cancel]

/-- The signed sums `m t`. -/
def msum (x : Fin n → K) (y : Fin n → H) (t : H) : K :=
  ∑ j ∈ ({j | y j = t} : Finset (Fin n)), x j - ∑ j ∈ ({j | y j = -t} : Finset (Fin n)), x j

theorem coeff_Nn (x : Fin n → K) (y : Fin n → H) (i : ℕ) (hi : (i : H) ≠ 0) (t : H) :
    (Nn x y i).coeff t = (i : K) * msum x y ((i : H)⁻¹ * t) := by
  classical
  rw [Nn, coeff_sum, Finsupp.finsetSum_apply, msum, sum_filter, sum_filter, ← sum_sub_distrib,
    mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have hc1 : ((i : H) * y j = t) ↔ (y j = (i : H)⁻¹ * t) :=
    (eq_inv_mul_iff_mul_eq₀ hi).symm
  have hc2 : (-((i : H) * y j) = t) ↔ (y j = -((i : H)⁻¹ * t)) := by
    rw [neg_eq_iff_eq_neg, ← mul_neg]; exact (eq_inv_mul_iff_mul_eq₀ hi).symm
  simp only [coeff_add, Finsupp.add_apply, coeff_smul_apply, coeff_single, Finsupp.single_apply,
    smul_eq_mul, nsmul_eq_mul, hc1, hc2]
  split_ifs <;> ring

theorem Tg_decomp (y : Fin n → H) (d : ℕ) (hpair : ∀ t, t ≠ 0 → cnt y t + cnt y (-t) = d)
    (i : ℕ) (hi : (i : H) ≠ 0) :
    Tg K y i = single 0 (((1 + 2 * cnt y 0 : ℕ) : K) - d) + single 0 (d : K) * Sall := by
  classical
  ext t
  rw [coeff_Tg, coeff_add, Finsupp.add_apply, coeff_single_zero_mul, coeff_Sall, coeff_single,
    Finsupp.single_apply, card_nsmul_eq y i hi, card_nsmul_eq y i hi]
  by_cases h0 : t = 0
  · subst h0
    simp only [mul_zero, neg_zero, ite_true]
    unfold cnt; push_cast; ring
  · have h0' : (i : H)⁻¹ * t ≠ 0 := mul_ne_zero (inv_ne_zero hi) h0
    have hd := hpair _ h0'
    unfold cnt at hd
    simp only [h0, ite_false, Ne.symm h0, zero_add, mul_neg, mul_one]
    rw [← Nat.cast_add, hd]

section Perfect

variable {G : Type*} [AddCommGroup G] [Fintype G] {g : Fin n → G}

/-- The relation between the signed sums. -/
theorem msum_relation (hg : IsPerfect g) (ψ1 : G →+ K) (ψ2 : G →+ H)
    (hcard : ∀ t, ((#{g' | ψ2 g' = t} : ℕ) : K) = 0) (d : ℕ)
    (hpair : ∀ t, t ≠ 0 → cnt (fun j => ψ2 (g j)) t + cnt (fun j => ψ2 (g j)) (-t) = d) (t : H) :
    let A : K := ((1 + 2 * cnt (fun j => ψ2 (g j)) 0 : ℕ) : K) - d
    (3 * A ^ 2 + 3 * A - 6 * n) * msum (fun j => ψ1 (g j)) (fun j => ψ2 (g j)) t +
      6 * A * msum (fun j => ψ1 (g j)) (fun j => ψ2 (g j)) (15 * t) +
      6 * msum (fun j => ψ1 (g j)) (fun j => ψ2 (g j)) (10 * t) = 0 := by
  intro A
  set x : Fin n → K := fun j => ψ1 (g j)
  set y : Fin n → H := fun j => ψ2 (g j)
  have hid := snd_identity hg ψ1 ψ2 hcard
  have hN : ∀ i, (Te dualHom (fun j => (ψ1 (g j), ψ2 (g j))) i).snd = Nn x y i :=
    fun i => snd_Te x y i
  rw [hN, hN, hN, Tg_decomp y d hpair 1 (by decide), Tg_decomp y d hpair 2 (by decide)] at hid
  set a : B := single 0 A
  set δ : B := single 0 (d : K)
  have key : 3 * (a + δ * Sall) ^ 2 * Nn x y 1 +
      3 * ((a + δ * Sall) * Nn x y 2 + Nn x y 1 * (a + δ * Sall)) + 2 * Nn x y 3 -
      6 * (n : B) * Nn x y 1 =
      (3 * a ^ 2 + 3 * a - 6 * (n : B)) * Nn x y 1 + 3 * a * Nn x y 2 + 2 * Nn x y 3 +
        (3 * (2 * a * δ + δ * δ * Sall) + 3 * δ) * (Sall * Nn x y 1) +
        3 * δ * (Sall * Nn x y 2) := by ring
  rw [key, Sall_mul_Nn, Sall_mul_Nn, mul_zero, mul_zero, add_zero, add_zero] at hid
  have c1 : 3 * a ^ 2 + 3 * a - 6 * (n : B) = single 0 (3 * A ^ 2 + 3 * A - 6 * n) := by
    rw [show single 0 (3 * A ^ 2 + 3 * A - 6 * n) =
      (singleZeroRingHom : K →+* B) (3 * A ^ 2 + 3 * A - 6 * n) from rfl]
    simp only [map_add, map_sub, map_mul, map_pow, map_natCast, map_ofNat]
    rfl
  have c2 : 3 * a = single 0 (3 * A) := by
    rw [show (3 : B) = single 0 3 from rfl, single_mul_single, zero_add]
  have c3 : (2 : B) = single 0 2 := rfl
  rw [c1, c2, c3] at hid
  have ht := congrArg (fun f : B => f.coeff t) hid
  simp only [coeff_add, Finsupp.add_apply, coeff_single_zero_mul] at ht
  rw [coeff_Nn x y 1 (by decide), coeff_Nn x y 2 (by decide), coeff_Nn x y 3 (by decide),
    show ((2 : ℕ) : H)⁻¹ = 15 from inv_eq_of_mul_eq_one_right (by decide),
    show ((3 : ℕ) : H)⁻¹ = 10 from inv_eq_of_mul_eq_one_right (by decide)] at ht
  simp only [Nat.cast_one, inv_one, one_mul] at ht
  simp only [coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at ht
  push_cast at ht
  linear_combination ht

end Perfect

end GolombWelch
