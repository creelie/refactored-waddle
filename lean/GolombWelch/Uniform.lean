import GolombWelch.GroupRing
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.ZMod.Basic

/-!
# Projections of a perfect code

A tiling of `ℤ^n` by translates of `ball n 3` along a lattice gives a finite abelian group
`G` and elements `g j` such that `a ↦ ∑ j, a j • g j` maps `ball n 3` bijectively onto `G`.
For a surjective homomorphism `ψ : G →+ H` every value of `H` is taken by `|G| / |H|`
points of the ball.
-/

open Finset

namespace GolombWelch

variable {G : Type*} [AddCommGroup G] [Fintype G] {n : ℕ}

/-- The map `a ↦ ∑ j, a j • g j`. -/
def phi (g : Fin n → G) (a : Fin n → ℤ) : G := ∑ j, a j • g j

/-- `g` is a perfect code of radius three: `phi g` maps `ball n 3` bijectively onto `G`. -/
def IsPerfect (g : Fin n → G) : Prop := Set.BijOn (phi g) (ball n 3 : Set (Fin n → ℤ)) Set.univ

theorem card_eq_of_perfect {g : Fin n → G} (hg : IsPerfect g) :
    Fintype.card G = (ball n 3).card := by
  symm
  rw [← card_univ]
  refine card_nbij (phi g) (fun a _ => mem_univ _) hg.injOn ?_
  intro y _
  obtain ⟨a, ha, rfl⟩ := hg.surjOn (Set.mem_univ y)
  exact ⟨a, ha, rfl⟩

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem card_fiber (ψ : G →+ H) (hψ : Function.Surjective ψ) (h : H) :
    #{x | ψ x = h} = Fintype.card G / Fintype.card H := by
  have hall : ∀ h', #{x | ψ x = h'} = #{x | ψ x = h} := fun h' =>
    AddMonoidHom.card_fiber_eq_of_mem_range ψ (hψ h') (hψ h)
  have hsum : Fintype.card G = ∑ h' : H, #{x | ψ x = h'} := by
    rw [← card_univ]
    exact card_eq_sum_card_fiberwise (fun x _ => mem_univ (ψ x))
  rw [hsum, sum_congr rfl (fun h' _ => hall h'), sum_const, card_univ, smul_eq_mul,
    Nat.mul_div_cancel_left _ Fintype.card_pos]

omit [Fintype G] [Fintype H] [DecidableEq H] in
theorem psi_phi (g : Fin n → G) (ψ : G →+ H) (a : Fin n → ℤ) :
    ∑ j, a j • ψ (g j) = ψ (phi g a) := by
  simp [phi, map_sum, map_zsmul]

/-- Sums over the ball become sums over `G`. -/
theorem sum_ball_eq_sum_group {g : Fin n → G} (hg : IsPerfect g) {M : Type*} [AddCommMonoid M]
    (F : G → M) : ∑ a ∈ ball n 3, F (phi g a) = ∑ x, F x := by
  refine sum_nbij (phi g) (fun a _ => mem_univ _) hg.injOn ?_ (fun a _ => rfl)
  intro y _
  obtain ⟨a, ha, rfl⟩ := hg.surjOn (Set.mem_univ y)
  exact ⟨a, ha, rfl⟩

/-- Uniformity of a projection. -/
theorem sum_ball_uniform {g : Fin n → G} (hg : IsPerfect g) (ψ : G →+ H)
    (hψ : Function.Surjective ψ) {M : Type*} [AddCommMonoid M] (F : H → M) :
    ∑ a ∈ ball n 3, F (∑ j, a j • ψ (g j)) =
      (Fintype.card G / Fintype.card H) • ∑ h, F h := by
  simp_rw [psi_phi g ψ]
  rw [sum_ball_eq_sum_group hg (fun x => F (ψ x)),
    ← sum_fiberwise univ ψ (fun x => F (ψ x)), smul_sum]
  refine sum_congr rfl fun h _ => ?_
  rw [sum_congr rfl (fun x hx => by rw [(mem_filter.1 hx).2]), sum_const, card_fiber ψ hψ h]

omit [Fintype G] in
/-- A finite abelian group whose order is divisible by a prime `p` maps onto `ZMod p`. -/
theorem exists_surj_zmod [Finite G] (p : ℕ) [hp : Fact p.Prime] (hdvd : p ∣ Nat.card G) :
    ∃ ψ : G →+ ZMod p, Function.Surjective ψ := by
  classical
  obtain ⟨ι, _, q, hq, e, ⟨f⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
  have hcard : Nat.card G = ∏ i, q i ^ e i := by
    rw [Nat.card_congr f.toEquiv,
      show Nat.card (DirectSum ι fun i => ZMod (q i ^ e i)) = Nat.card (Π₀ i, ZMod (q i ^ e i))
        from rfl,
      Nat.card_congr DFinsupp.equivFunOnFintype, Nat.card_pi]
    simp [Nat.card_zmod]
  obtain ⟨i, -, hi⟩ := (Nat.Prime.prime hp.out).exists_mem_finset_dvd (hcard ▸ hdvd)
  refine ⟨(ZMod.castHom hi (ZMod p)).toAddMonoidHom.comp
    ((DFinsupp.evalAddMonoidHom i).comp f.toAddMonoidHom), ?_⟩
  intro y
  obtain ⟨z, rfl⟩ := ZMod.castHom_surjective hi y
  refine ⟨f.symm (DirectSum.of (fun i => ZMod (q i ^ e i)) i z), ?_⟩
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.apply_symm_apply]
  change ZMod.castHom hi (ZMod p) ((DirectSum.of (fun i => ZMod (q i ^ e i)) i z) i) = _
  rw [DirectSum.of_eq_same]

end GolombWelch
