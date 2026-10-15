import GolombWelch.Ball
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# The ball identity through a monoid homomorphism

For a homomorphism `e : Multiplicative M →* D` into a commutative ring and `z : Fin n → M`,
the ball identity applied to the units `e (ofAdd (z j))` reads
`6 ∑_{a ∈ ball n 3} e (ofAdd (∑ j, a j • z j)) = T 1 ^ 3 + 3 T 1 T 2 + 2 T 3 - 6 n T 1`
with `T i = 1 + ∑ j, (e (ofAdd (i • z j)) + e (ofAdd (-(i • z j))))`.
-/

open Finset Multiplicative

namespace GolombWelch

variable {D : Type*} [CommRing D] {M : Type*} [AddCommGroup M]

theorem pw_hom (e : Multiplicative M →* D) (z : M) (t : ℤ) :
    pw (e (ofAdd z)) (e (ofAdd (-z))) t = e (ofAdd (t • z)) := by
  unfold pw
  split_ifs with h
  · rw [← map_pow, ← ofAdd_nsmul, ← natCast_zsmul, Int.toNat_of_nonneg h]
  · rw [← map_pow, ← ofAdd_nsmul, ← natCast_zsmul, Int.toNat_of_nonneg (by omega), smul_neg,
      ← neg_smul, neg_neg]

/-- The elements `T i` for a homomorphism `e`. -/
def Te (e : Multiplicative M →* D) {n : ℕ} (z : Fin n → M) (i : ℕ) : D :=
  1 + ∑ j, (e (ofAdd (i • z j)) + e (ofAdd (-(i • z j))))

theorem ball_identity_hom (e : Multiplicative M →* D) (n : ℕ) (z : Fin n → M) :
    6 * ∑ a ∈ ball n 3, e (ofAdd (∑ j, a j • z j)) =
      Te e z 1 ^ 3 + 3 * Te e z 1 * Te e z 2 + 2 * Te e z 3 - 6 * n * Te e z 1 := by
  have h := ball_identity (R := D) n (fun j => e (ofAdd (z j))) (fun j => e (ofAdd (-z j)))
    (fun j => by rw [← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero, map_one])
  have hb : ballSum 3 (fun j => e (ofAdd (z j))) (fun j => e (ofAdd (-z j))) =
      ∑ a ∈ ball n 3, e (ofAdd (∑ j, a j • z j)) := by
    refine sum_congr rfl fun a _ => ?_
    simp only [pw_hom]
    rw [ofAdd_sum, map_prod]
  have hY : ∀ i : ℕ, Ysum (fun j => e (ofAdd (z j))) (fun j => e (ofAdd (-z j))) i =
      ∑ j, (e (ofAdd (i • z j)) + e (ofAdd (-(i • z j)))) := by
    intro i
    refine sum_congr rfl fun j _ => ?_
    show e (ofAdd (z j)) ^ i + e (ofAdd (-z j)) ^ i = _
    rw [← map_pow e, ← map_pow e, ← ofAdd_nsmul, ← ofAdd_nsmul, smul_neg]
  rw [hb, hY, hY, hY] at h
  simpa [Te] using h

end GolombWelch
