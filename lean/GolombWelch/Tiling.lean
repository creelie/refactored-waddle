import GolombWelch.Final

/-!
# Lattice tilings by Lee balls

`IsLatticeTiling n r L` says that the Lee balls of radius `r` centred at the points of the
subgroup `L ⊆ ℤ^n` partition `ℤ^n`: every point lies at Lee distance at most `r` from exactly
one point of `L`.  A lattice tiling by balls of radius three gives a perfect code in the finite
group `ℤ^n / L`, so the results of `Final` rule out lattice tilings of `ℤ^35` and `ℤ^805`.
-/

open Finset

namespace GolombWelch

/-- The Lee balls of radius `r` centred at the points of `L` partition `ℤ^n`. -/
def IsLatticeTiling (n r : ℕ) (L : AddSubgroup (Fin n → ℤ)) : Prop :=
  ∀ x : Fin n → ℤ, ∃! l : Fin n → ℤ, l ∈ L ∧ ∑ j, |x j - l j| ≤ (r : ℤ)

theorem abs_sum_le_iff {n r : ℕ} (a : Fin n → ℤ) : ∑ j, |a j| ≤ (r : ℤ) ↔ a ∈ ball n r := by
  rw [mem_ball]
  simp only [Int.abs_eq_natAbs]
  norm_cast

theorem sum_single_smul {n : ℕ} (a : Fin n → ℤ) :
    ∑ j, a j • (Pi.single j (1 : ℤ) : Fin n → ℤ) = a := by
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

/-- A lattice tiling by Lee balls of radius three gives a perfect code. -/
theorem perfect_of_tiling {n : ℕ} {L : AddSubgroup (Fin n → ℤ)} (hL : IsLatticeTiling n 3 L) :
    ∃ (G : Type) (_ : AddCommGroup G) (_ : Fintype G) (g : Fin n → G), IsPerfect g := by
  classical
  let G := (Fin n → ℤ) ⧸ L
  let π : (Fin n → ℤ) →+ G := QuotientAddGroup.mk' L
  have hπ : ∀ a b, π a = π b ↔ a - b ∈ L := by
    intro a b
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq,
      ← L.neg_mem_iff, neg_add, neg_neg, ← sub_eq_add_neg]
  -- every class has a representative in the ball
  have hrep : ∀ q : G, ∃ a ∈ ball n 3, π a = q := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L q
    obtain ⟨l, ⟨hl, hd⟩, -⟩ := hL x
    refine ⟨x - l, (abs_sum_le_iff _).1 (by simpa using hd), ?_⟩
    rw [hπ]
    simpa using L.neg_mem hl
  have : Finite G := by
    refine Finite.of_surjective (fun a : (ball n 3 : Set (Fin n → ℤ)) => π a) ?_
    intro q
    obtain ⟨a, ha, rfl⟩ := hrep q
    exact ⟨⟨a, ha⟩, rfl⟩
  let _ : Fintype G := Fintype.ofFinite G
  refine ⟨G, inferInstance, inferInstance, fun j => π (Pi.single j 1), ?_⟩
  have hphi : ∀ a, phi (fun j => π (Pi.single j 1)) a = π a := by
    intro a
    rw [phi, ← sum_single_smul a, map_sum]
    simp only [map_zsmul, sum_single_smul]
  refine ⟨fun a _ => Set.mem_univ _, ?_, ?_⟩
  · intro a ha b hb hab
    rw [hphi, hphi, hπ] at hab
    have ha' : ∑ j, |a j - (0 : Fin n → ℤ) j| ≤ ((3 : ℕ) : ℤ) := by
      simpa using (abs_sum_le_iff a).2 ha
    have hb' : ∑ j, |a j - (a - b) j| ≤ ((3 : ℕ) : ℤ) := by
      simpa using (abs_sum_le_iff b).2 hb
    have := (hL a).unique ⟨L.zero_mem, ha'⟩ ⟨hab, hb'⟩
    exact (sub_eq_zero.1 this.symm)
  · intro q _
    obtain ⟨a, ha, rfl⟩ := hrep q
    exact ⟨a, ha, hphi a⟩

/-- There is no lattice tiling of `ℤ^35` by Lee balls of radius three. -/
theorem golomb_welch_35 : ¬ ∃ L : AddSubgroup (Fin 35 → ℤ), IsLatticeTiling 35 3 L := by
  rintro ⟨L, hL⟩
  obtain ⟨G, _, _, g, hg⟩ := perfect_of_tiling hL
  exact no_perfect_35 g hg

/-- There is no lattice tiling of `ℤ^805` by Lee balls of radius three. -/
theorem golomb_welch_805 : ¬ ∃ L : AddSubgroup (Fin 805 → ℤ), IsLatticeTiling 805 3 L := by
  rintro ⟨L, hL⟩
  obtain ⟨G, _, _, g, hg⟩ := perfect_of_tiling hL
  exact no_perfect_805 g hg

end GolombWelch
