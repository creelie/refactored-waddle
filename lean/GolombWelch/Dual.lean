import GolombWelch.BallHom
import GolombWelch.Mod841
import GolombWelch.Pairs
import Mathlib.Algebra.DualNumber

/-!
# The joint projection to `ZMod 71 × ZMod 29`

Map `(s, t)` to the dual number `single t 1 + ε • s • single t 1` over `(ZMod 71)[ZMod 29]`.
The ball identity, read off in the `ε`-part, gives a linear relation between the sums
`∑_{y j = t} x j - ∑_{y j = -t} x j`.
-/

open Finset AddMonoidAlgebra Multiplicative TrivSqZeroExt

namespace GolombWelch

local notation "K" => ZMod 71
local notation "H" => ZMod 29
local notation "B" => AddMonoidAlgebra K H

instance fact_prime_71 : Fact (Nat.Prime 71) := ⟨by norm_num⟩

/-- The homomorphism `(s, t) ↦ single t 1 + ε s single t 1`. -/
noncomputable def dualHom : Multiplicative (K × H) →* DualNumber B where
  toFun z := inl (single (toAdd z).2 1) + inr ((toAdd z).1 • single (toAdd z).2 1)
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [one_def]
    · simp
  map_mul' z w := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [single_mul_single]
    · simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, snd_add, snd_inl, snd_inr, zero_add,
        DualNumber.snd_mul, fst_add, fst_inl, fst_inr, add_zero]
      rw [mul_smul_comm, smul_mul_assoc, single_mul_single, one_mul, add_smul]
      abel

theorem fst_dualHom (s : K) (t : H) : (dualHom (ofAdd (s, t))).fst = single t 1 := by
  simp [dualHom]

theorem snd_dualHom (s : K) (t : H) : (dualHom (ofAdd (s, t))).snd = s • single t 1 := by
  simp [dualHom]

theorem snd_poly (a1 a2 a3 : DualNumber B) (n : ℕ) :
    (a1 ^ 3 + 3 * a1 * a2 + 2 * a3 - 6 * n * a1).snd =
      3 * a1.fst ^ 2 * a1.snd + 3 * (a1.fst * a2.snd + a1.snd * a2.fst) + 2 * a3.snd -
        6 * n * a1.snd := by
  have h3 : (3 : DualNumber B) = inl 3 := rfl
  have h2 : (2 : DualNumber B) = inl 2 := rfl
  have h6 : (6 : DualNumber B) = inl 6 := rfl
  have hn : (n : DualNumber B) = inl (n : B) := rfl
  rw [h3, h2, h6, hn, pow_three]
  simp only [snd_sub, snd_add, DualNumber.snd_mul, fst_mul, fst_inl, snd_inl]
  ring

variable {n : ℕ}

theorem fst_Te (x : Fin n → K) (y : Fin n → H) (i : ℕ) :
    (Te dualHom (fun j => (x j, y j)) i).fst = Tg K y i := by
  simp only [Te, Tg, fst_add, fst_one, fst_sum, Prod.smul_mk, Prod.neg_mk, fst_dualHom]

theorem snd_Te (x : Fin n → K) (y : Fin n → H) (i : ℕ) :
    (Te dualHom (fun j => (x j, y j)) i).snd =
      ∑ j, ((i • x j) • single (i • y j) 1 + (-(i • x j)) • single (-(i • y j)) 1) := by
  simp only [Te, snd_add, snd_one, snd_sum, Prod.smul_mk, Prod.neg_mk, snd_dualHom, zero_add]

section Perfect

variable {G : Type*} [AddCommGroup G] [Fintype G] {g : Fin n → G}

/-- A fibre of `ψ2` whose size is divisible by `71` has `ψ1`-sum zero. -/
theorem fiber_sum_zero (ψ1 : G →+ K) (ψ2 : G →+ H) (t : H)
    (hcard : ((#{g' | ψ2 g' = t} : ℕ) : K) = 0) : ∑ g' ∈ ({g' | ψ2 g' = t} : Finset G), ψ1 g' = 0 := by
  classical
  set s : Finset G := {g' | ψ2 g' = t} with hs
  rcases s.eq_empty_or_nonempty with he | ⟨g0, hg0⟩
  · rw [he, sum_empty]
  · have hg0' : ψ2 g0 = t := (mem_filter.1 hg0).2
    have hsym : ∑ g' ∈ s, ψ1 (2 • g0 - g') = ∑ g' ∈ s, ψ1 g' := by
      refine sum_equiv (Equiv.subLeft (2 • g0)) (fun g' => ?_) (fun g' _ => rfl)
      simp only [hs, mem_filter, mem_univ, true_and, Equiv.subLeft_apply, map_sub, map_add, hg0',
        two_nsmul]
      constructor <;> intro h <;> linear_combination -h
    have h2 : 2 * ∑ g' ∈ s, ψ1 g' = 0 := by
      have e : ∑ g' ∈ s, (ψ1 g' + ψ1 (2 • g0 - g')) = ∑ _g' ∈ s, 2 * ψ1 g0 := by
        refine sum_congr rfl fun g' _ => ?_
        rw [map_sub, map_nsmul, two_nsmul]; ring
      rw [sum_add_distrib, hsym, sum_const, nsmul_eq_mul, hcard, zero_mul] at e
      rw [two_mul]; exact e
    exact (mul_eq_zero.1 h2).resolve_left (by decide)

theorem sum_group_zero (ψ1 : G →+ K) (ψ2 : G →+ H)
    (hcard : ∀ t, ((#{g' | ψ2 g' = t} : ℕ) : K) = 0) :
    ∑ g' : G, ψ1 g' • single (ψ2 g') (1 : K) = 0 := by
  classical
  ext t
  rw [coeff_sum, Finsupp.finsetSum_apply]
  simp only [coeff_smul_apply, coeff_single, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  rw [← sum_filter]
  simpa using fiber_sum_zero ψ1 ψ2 t (hcard t)

theorem sum_prod_mk (a : Fin n → ℤ) (x : Fin n → K) (y : Fin n → H) :
    ∑ j, a j • (x j, y j) = (∑ j, a j • x j, ∑ j, a j • y j) := by
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

/-- The `ε`-part of the ball identity. -/
theorem snd_identity (hg : IsPerfect g) (ψ1 : G →+ K) (ψ2 : G →+ H)
    (hcard : ∀ t, ((#{g' | ψ2 g' = t} : ℕ) : K) = 0) :
    3 * Tg K (fun j => ψ2 (g j)) 1 ^ 2 * (Te dualHom (fun j => (ψ1 (g j), ψ2 (g j))) 1).snd +
      3 * (Tg K (fun j => ψ2 (g j)) 1 * (Te dualHom (fun j => (ψ1 (g j), ψ2 (g j))) 2).snd +
        (Te dualHom (fun j => (ψ1 (g j), ψ2 (g j))) 1).snd * Tg K (fun j => ψ2 (g j)) 2) +
      2 * (Te dualHom (fun j => (ψ1 (g j), ψ2 (g j))) 3).snd -
      6 * n * (Te dualHom (fun j => (ψ1 (g j), ψ2 (g j))) 1).snd = 0 := by
  have h := congrArg TrivSqZeroExt.snd
    (ball_identity_hom dualHom n (fun j => (ψ1 (g j), ψ2 (g j))))
  rw [snd_poly, fst_Te, fst_Te] at h
  rw [← h, show (6 : DualNumber B) = inl 6 from rfl, DualNumber.snd_mul, fst_inl, snd_inl,
    zero_mul, add_zero, snd_sum]
  simp only [sum_prod_mk, snd_dualHom, psi_phi g ψ1, psi_phi g ψ2]
  rw [sum_ball_eq_sum_group hg (fun g' => ψ1 g' • single (ψ2 g') (1 : K)),
    sum_group_zero ψ1 ψ2 hcard, mul_zero]

end Perfect

end GolombWelch
