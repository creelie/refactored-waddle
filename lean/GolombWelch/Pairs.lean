import GolombWelch.Counts

/-!
# Counting pairs `± h`

For `x : Fin n → ZMod p` write `cnt x h = #{j | x j = h}`.  If `cnt x h + cnt x (-h)` is
congruent to `d < p` for every `h ≠ 0`, then `(p - 1) d + 2 cnt x 0 ≤ 2 n`, with equality only
when every such sum equals `d`.
-/

open Finset

namespace GolombWelch

variable {p : ℕ} [hp : Fact p.Prime]

local notation "F" => ZMod p

/-- The number of coordinates equal to `h`. -/
def cnt {n : ℕ} (x : Fin n → F) (h : F) : ℕ := #{j | x j = h}

theorem sum_cnt {n : ℕ} (x : Fin n → F) : ∑ h, cnt x h = n := by
  classical
  unfold cnt
  rw [← card_eq_sum_card_fiberwise (f := x) (s := univ) (t := univ) (fun j _ => mem_univ _)]
  simp

theorem sum_pairs {n : ℕ} (x : Fin n → F) :
    ∑ h ∈ univ.erase 0, (cnt x h + cnt x (-h)) + 2 * cnt x 0 = 2 * n := by
  have e1 : ∑ h ∈ univ.erase 0, cnt x h + cnt x 0 = n := by
    rw [sum_erase_add _ _ (mem_univ 0), sum_cnt]
  have e2 : ∑ h ∈ univ.erase 0, cnt x (-h) + cnt x 0 = n := by
    have := sum_erase_add univ (fun h => cnt x (-h)) (mem_univ (0 : F))
    simp only [neg_zero] at this
    rw [this, Fintype.sum_equiv (Equiv.neg F) (fun h => cnt x (-h)) (cnt x) (fun h => rfl),
      sum_cnt]
  rw [sum_add_distrib]; omega

theorem pairs_ge {n : ℕ} (x : Fin n → F) (d : ℕ) (hd : d < p)
    (hN : ∀ h, h ≠ 0 → ((cnt x h + cnt x (-h) : ℕ) : F) = d) (h : F) (h0 : h ≠ 0) :
    d ≤ cnt x h + cnt x (-h) := by
  have := hN h h0
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hd] at this
  exact this ▸ Nat.mod_le _ _

theorem card_erase_zero : (univ.erase (0 : F)).card = p - 1 := by
  rw [card_erase_of_mem (mem_univ _), card_univ, ZMod.card]

theorem pairs_bound {n : ℕ} (x : Fin n → F) (d : ℕ) (hd : d < p)
    (hN : ∀ h, h ≠ 0 → ((cnt x h + cnt x (-h) : ℕ) : F) = d) :
    (p - 1) * d + 2 * cnt x 0 ≤ 2 * n := by
  rw [← sum_pairs x]
  have : (p - 1) * d ≤ ∑ h ∈ univ.erase (0 : F), (cnt x h + cnt x (-h)) := by
    calc (p - 1) * d = ∑ _h ∈ univ.erase (0 : F), d := by
          rw [sum_const, card_erase_zero, smul_eq_mul]
      _ ≤ _ := sum_le_sum fun h hh => pairs_ge x d hd hN h (ne_of_mem_erase hh)
  omega

theorem pairs_eq {n : ℕ} (x : Fin n → F) (d : ℕ) (hd : d < p)
    (hN : ∀ h, h ≠ 0 → ((cnt x h + cnt x (-h) : ℕ) : F) = d)
    (heq : (p - 1) * d + 2 * cnt x 0 = 2 * n) (h : F) (h0 : h ≠ 0) :
    cnt x h + cnt x (-h) = d := by
  have hs : ∑ _h ∈ univ.erase (0 : F), d = ∑ h ∈ univ.erase (0 : F), (cnt x h + cnt x (-h)) := by
    rw [sum_const, card_erase_zero, smul_eq_mul]
    have := sum_pairs x
    omega
  exact ((sum_eq_sum_iff_of_le fun h hh => pairs_ge x d hd hN h (ne_of_mem_erase hh)).1 hs h
    (mem_erase.2 ⟨h0, mem_univ _⟩)).symm

/-- The congruence of `count_pair` in terms of `cnt`. -/
theorem pairs_mod {n : ℕ} (x : Fin n → F) (hP : ∀ k, 1 ≤ k → k < p - 1 → P x k = 0) (h : F)
    (h0 : h ≠ 0) : ((cnt x h + cnt x (-h) : ℕ) : F) = ((-P x (p - 1)).val : ℕ) := by
  rw [ZMod.natCast_zmod_val, Nat.cast_add]
  exact count_pair x hP h0

theorem zero_mod {n : ℕ} (x : Fin n → F) (hP : ∀ k, 1 ≤ k → k < p - 1 → P x k = 0) :
    ((2 * cnt x 0 : ℕ) : F) = ((2 * n + (-P x (p - 1)).val : ℕ) : F) := by
  rw [Nat.cast_add, ZMod.natCast_zmod_val, ← count_zero x hP]
  push_cast [cnt]; ring

end GolombWelch
