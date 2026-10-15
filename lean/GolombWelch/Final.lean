import GolombWelch.Joint
import GolombWelch.Circulant

/-!
# No perfect code of radius three in dimensions `35` and `805`

`no_perfect_805`: the moment argument modulo `29` and the identity modulo `29 ^ 2`.
`no_perfect_35`: the moment argument modulo `71` and modulo `29`, then either the identity
modulo `29 ^ 2` or the joint step through `ZMod 71 × ZMod 29`.
-/

open Finset

namespace GolombWelch

local notation "K" => ZMod 71
local notation "H" => ZMod 29

/-- The relation of `msum_relation` along the orbit of `t0` under multiplication by `15`. -/
theorem circ_seq (m : H → K) (a b c : K)
    (hrel : ∀ t, a * m t + b * m (15 * t) + c * m (10 * t) = 0) (t0 : H) :
    (∀ k, m (15 ^ (k + 28) * t0) = m (15 ^ k * t0)) ∧
      ∀ k, a * m (15 ^ k * t0) + b * m (15 ^ (k + 1) * t0) + c * m (15 ^ (k + 5) * t0) = 0 := by
  refine ⟨fun k => ?_, fun k => ?_⟩
  · rw [pow_add, show (15 : H) ^ 28 = 1 by decide, mul_one]
  · have e1 : (15 : H) ^ (k + 1) * t0 = 15 * (15 ^ k * t0) := by rw [pow_succ]; ring
    have e5 : (15 : H) ^ (k + 5) * t0 = 10 * (15 ^ k * t0) := by
      rw [pow_add, show (15 : H) ^ 5 = 10 by decide]; ring
    rw [e1, e5]
    exact hrel _

variable {n : ℕ}

/-- The final contradiction of the case `35`. -/
theorem final_contra (x : Fin n → K) (y : Fin n → H) (hx0 : cnt x 0 = 0)
    (hx : ∀ h, h ≠ 0 → cnt x h + cnt x (-h) = 1) (d : ℕ) (hd : d = 1 ∨ d = 2)
    (hy : cnt y 1 + cnt y (-1) = d) (hm : msum x y 1 = 0) : False := by
  classical
  have hne : ∀ j, x j ≠ 0 := by
    intro j hj
    have : j ∈ ({j | x j = 0} : Finset (Fin n)) := by simp [hj]
    unfold cnt at hx0
    rw [card_eq_zero] at hx0
    simp [hx0] at this
  have hle : ∀ h, h ≠ 0 → cnt x h ≤ 1 := fun h h0 => by have := hx h h0; omega
  have hinj : ∀ j j', j ≠ j' → x j ≠ x j' := by
    intro j j' hjj' he
    have h2 : 2 ≤ cnt x (x j) := by
      unfold cnt
      have hsub : ({j, j'} : Finset (Fin n)) ⊆ filter (fun i => x i = x j) univ := by
        intro i hi; simp only [mem_insert, mem_singleton] at hi; rcases hi with rfl | rfl <;> simp [he]
      have := card_le_card hsub
      rwa [card_pair hjj'] at this
    have := hle (x j) (hne j); omega
  have hneg : ∀ j j', j ≠ j' → x j ≠ -x j' := by
    intro j j' hjj' he
    have h1 : 1 ≤ cnt x (x j) := by
      unfold cnt; exact card_pos.2 ⟨j, by simp⟩
    have h2 : 1 ≤ cnt x (-x j) := by
      unfold cnt; exact card_pos.2 ⟨j', by simp [he]⟩
    have := hx (x j) (hne j); omega
  have hy1 : (1 : H) ≠ -1 := by decide
  unfold msum at hm
  unfold cnt at hy
  set J1 : Finset (Fin n) := {j | y j = 1} with hJ1
  set J2 : Finset (Fin n) := {j | y j = -1} with hJ2
  have hc : (#J1 = 1 ∧ #J2 = 0) ∨ (#J1 = 0 ∧ #J2 = 1) ∨ (#J1 = 2 ∧ #J2 = 0) ∨
      (#J1 = 1 ∧ #J2 = 1) ∨ (#J1 = 0 ∧ #J2 = 2) := by omega
  rcases hc with ⟨c1, c2⟩ | ⟨c1, c2⟩ | ⟨c1, c2⟩ | ⟨c1, c2⟩ | ⟨c1, c2⟩
  · obtain ⟨j, hj⟩ := card_eq_one.1 c1
    rw [card_eq_zero.1 c2, hj, sum_singleton, sum_empty, sub_zero] at hm
    exact hne j hm
  · obtain ⟨j, hj⟩ := card_eq_one.1 c2
    rw [card_eq_zero.1 c1, hj, sum_singleton, sum_empty, zero_sub, neg_eq_zero] at hm
    exact hne j hm
  · obtain ⟨j, j', hjj', hj⟩ := card_eq_two.1 c1
    rw [card_eq_zero.1 c2, hj, sum_pair hjj', sum_empty, sub_zero] at hm
    exact hneg j j' hjj' (eq_neg_of_add_eq_zero_left hm)
  · obtain ⟨j, hj⟩ := card_eq_one.1 c1
    obtain ⟨j', hj'⟩ := card_eq_one.1 c2
    have m1 : y j = 1 := by
      have : j ∈ J1 := by rw [hj]; exact mem_singleton_self j
      simpa [hJ1] using this
    have m2 : y j' = -1 := by
      have : j' ∈ J2 := by rw [hj']; exact mem_singleton_self j'
      simpa [hJ2] using this
    have hjj' : j ≠ j' := by
      rintro rfl; exact hy1 (m1.symm.trans m2)
    rw [hj, hj', sum_singleton, sum_singleton, sub_eq_zero] at hm
    exact hinj j j' hjj' hm
  · obtain ⟨j, j', hjj', hj⟩ := card_eq_two.1 c2
    rw [card_eq_zero.1 c1, hj, sum_pair hjj', sum_empty, zero_sub, neg_eq_zero] at hm
    exact hneg j j' hjj' (eq_neg_of_add_eq_zero_left hm)

section Perfect

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem kappa_805 : ∀ v < 28, 1 ≤ v → Even v → kappa 805 v ≠ (0 : H) := by decide +kernel

theorem check_805 : ∀ c, c ≤ 805 → c % 29 = 22 →
    ((6 * (696845031 / 29) : ℕ) : ZMod 841) ≠ ((1 + 2 * c : ℕ) : ZMod 841) ^ 3 +
      3 * ((1 + 2 * c : ℕ) : ZMod 841) ^ 2 + 2 * ((1 + 2 * c : ℕ) : ZMod 841) -
      6 * ((805 : ℕ) : ZMod 841) * ((1 + 2 * c : ℕ) : ZMod 841) := by decide +kernel

theorem cnt_le {p : ℕ} [Fact p.Prime] (x : Fin n → ZMod p) (h : ZMod p) : cnt x h ≤ n := by
  unfold cnt
  exact (card_filter_le _ _).trans (by simp)

/-- There is no perfect code of radius three in dimension `805`. -/
theorem no_perfect_805 (g : Fin 805 → G) (hg : IsPerfect g) : False := by
  classical
  have hcardG : Fintype.card G = 696845031 := by rw [card_eq_of_perfect hg, card_ball_805]
  obtain ⟨ψ, hψ⟩ := exists_surj_zmod (G := G) 29
    (by rw [Nat.card_eq_fintype_card, hcardG]; norm_num)
  set x : Fin 805 → H := fun j => ψ (g j) with hx
  have hP := P_vanish hg ψ hψ 28 (by norm_num) fun v h1 h2 he => kappa_805 v h2 h1 he
  have h28 : P x 28 = 0 := by
    have e := key_moment hg ψ hψ 28 (by norm_num) hP
    have hs : ∑ h : H, h ^ 28 = -1 := sum_pow_card_sub_one (p := 29)
    rw [hs, hcardG, show ((696845031 / 29 : ℕ) : H) = 0 by decide, mul_zero, zero_mul] at e
    exact (mul_eq_zero.1 e).resolve_left (by decide +kernel)
  have hP' : ∀ k, 1 ≤ k → k < 29 - 1 → P x k = 0 := fun k h1 h2 => hP k h1 (by omega)
  have hval : (-P x (29 - 1)).val = 0 := by
    rw [show 29 - 1 = 28 from rfl, h28, neg_zero, ZMod.val_zero]
  have hdiv : ∀ h, h ≠ 0 → 29 ∣ #{j | ψ (g j) = h} + #{j | ψ (g j) = -h} := by
    intro h h0
    have := pairs_mod x hP' h h0
    rw [hval, Nat.cast_zero, ZMod.natCast_eq_zero_iff] at this
    exact this
  have hc0 : cnt x 0 % 29 = 22 := by
    have := zero_mod x hP'
    rw [hval, ZMod.natCast_eq_natCast_iff'] at this
    omega
  have h841 := mod841 hg ψ hψ hdiv
  rw [hcardG] at h841
  exact check_805 (cnt x 0) (cnt_le x 0) hc0 h841

theorem kappa_35_71 : ∀ v < 70, 1 ≤ v → Even v → kappa 35 v ≠ (0 : K) := by decide +kernel

theorem kappa_35_29 : ∀ v < 28, 1 ≤ v → Even v → kappa 35 v ≠ (0 : H) := by decide +kernel

theorem check_35 : ∀ c, c = 6 ∨ c = 35 →
    ((6 * (59711 / 29) : ℕ) : ZMod 841) ≠ ((1 + 2 * c : ℕ) : ZMod 841) ^ 3 +
      3 * ((1 + 2 * c : ℕ) : ZMod 841) ^ 2 + 2 * ((1 + 2 * c : ℕ) : ZMod 841) -
      6 * ((35 : ℕ) : ZMod 841) * ((1 + 2 * c : ℕ) : ZMod 841) := by
  rintro c (rfl | rfl) <;> decide +kernel

/-- The circulant step: the relation forces `m 1 = 0`. -/
theorem msum_one_zero (m : H → K) (a b : K)
    (hrel : ∀ t, a * m t + b * m (15 * t) + 1 * m (10 * t) = 0)
    (hcirc : ∀ μ : ℕ → K, (∀ k, μ (k + 28) = μ k) →
      (∀ k, a * μ k + b * μ (k + 1) + μ (k + 5) = 0) → μ 0 = 0) : m 1 = 0 := by
  obtain ⟨hper, hE⟩ := circ_seq m a b 1 hrel 1
  have h := hcirc (fun k => m (15 ^ k * 1)) hper
    (fun k => by have h := hE k; rw [one_mul] at h; exact h)
  rwa [pow_zero, one_mul] at h

/-- The case `d = 1`, where `c 0 = 21` and `A = 42`. -/
theorem branch_one (g : Fin 35 → G) (hg : IsPerfect g) (ψ1 : G →+ K) (ψ2 : G →+ H)
    (hcard : ∀ t, ((#{g' | ψ2 g' = t} : ℕ) : K) = 0)
    (hpair : ∀ t, t ≠ 0 → cnt (fun j => ψ2 (g j)) t + cnt (fun j => ψ2 (g j)) (-t) = 1)
    (hc : cnt (fun j => ψ2 (g j)) 0 = 21) :
    msum (fun j => ψ1 (g j)) (fun j => ψ2 (g j)) 1 = 0 := by
  have hrel := msum_relation hg ψ1 ψ2 hcard 1 hpair
  have hA : ((1 + 2 * cnt (fun j => ψ2 (g j)) 0 : ℕ) : K) - ((1 : ℕ) : K) = 42 := by
    rw [hc]; decide
  simp only [hA] at hrel
  have e1 : (3 * (42 : K) ^ 2 + 3 * 42 - 6 * ((35 : ℕ) : K)) = 6 * 16 := by decide
  have h12 : (12 : K) * 6 = 1 := by decide
  refine msum_one_zero _ 16 42 (fun t => ?_) circ_zero_b
  have h := hrel t
  rw [e1] at h
  set m := msum (fun j => ψ1 (g j)) (fun j => ψ2 (g j))
  linear_combination 12 * h - (16 * m t + 42 * m (15 * t) + 1 * m (10 * t)) * h12

/-- The case `d = 2`, where `c 0 = 7` and `A = 13`. -/
theorem branch_two (g : Fin 35 → G) (hg : IsPerfect g) (ψ1 : G →+ K) (ψ2 : G →+ H)
    (hcard : ∀ t, ((#{g' | ψ2 g' = t} : ℕ) : K) = 0)
    (hpair : ∀ t, t ≠ 0 → cnt (fun j => ψ2 (g j)) t + cnt (fun j => ψ2 (g j)) (-t) = 2)
    (hc : cnt (fun j => ψ2 (g j)) 0 = 7) :
    msum (fun j => ψ1 (g j)) (fun j => ψ2 (g j)) 1 = 0 := by
  have hrel := msum_relation hg ψ1 ψ2 hcard 2 hpair
  have hA : ((1 + 2 * cnt (fun j => ψ2 (g j)) 0 : ℕ) : K) - ((2 : ℕ) : K) = 13 := by
    rw [hc]; decide
  simp only [hA] at hrel
  have e1 : (3 * (13 : K) ^ 2 + 3 * 13 - 6 * ((35 : ℕ) : K)) = 6 * 56 := by decide
  have h12 : (12 : K) * 6 = 1 := by decide
  refine msum_one_zero _ 56 13 (fun t => ?_) circ_zero_a
  have h := hrel t
  rw [e1] at h
  set m := msum (fun j => ψ1 (g j)) (fun j => ψ2 (g j))
  linear_combination 12 * h - (56 * m t + 13 * m (15 * t) + 1 * m (10 * t)) * h12

/-- Modulo `71`: no coordinate is `0` and the pairs `{h, -h}` each hold one coordinate. -/
theorem step71 (g : Fin 35 → G) (hg : IsPerfect g) (hcardG : Fintype.card G = 59711)
    (ψ1 : G →+ K) (hψ1 : Function.Surjective ψ1) :
    cnt (fun j => ψ1 (g j)) 0 = 0 ∧
      ∀ h, h ≠ 0 → cnt (fun j => ψ1 (g j)) h + cnt (fun j => ψ1 (g j)) (-h) = 1 := by
  classical
  set x : Fin 35 → K := fun j => ψ1 (g j) with hx
  have hP1 := P_vanish hg ψ1 hψ1 70 (by norm_num) fun v h1 h2 he => kappa_35_71 v h2 h1 he
  have h70 : P x 70 = -1 := by
    have e := key_moment hg ψ1 hψ1 70 (by norm_num) hP1
    have hs : ∑ h : K, h ^ 70 = -1 := sum_pow_card_sub_one (p := 71)
    rw [hs, hcardG, show ((59711 / 71 : ℕ) : K) = 60 by decide,
      show kappa 35 70 = (5 : K) by decide +kernel] at e
    refine mul_left_cancel₀ (show (5 : K) ≠ 0 by decide) ?_
    rw [e]; decide
  have hP1' : ∀ k, 1 ≤ k → k < 71 - 1 → P x k = 0 := fun k h1 h2 => hP1 k h1 (by omega)
  have hval1 : (-P x (71 - 1)).val = 1 := by
    rw [show 71 - 1 = 70 from rfl, h70, neg_neg]; rfl
  have hN1 : ∀ h, h ≠ 0 → ((cnt x h + cnt x (-h) : ℕ) : K) = (1 : ℕ) := by
    intro h h0; rw [pairs_mod x hP1' h h0, hval1]
  have hx0 : cnt x 0 = 0 := by
    have := zero_mod x hP1'
    rw [hval1, ZMod.natCast_eq_natCast_iff'] at this
    have := cnt_le x 0
    omega
  exact ⟨hx0, pairs_eq x 1 (by norm_num) hN1 (by rw [hx0])⟩

/-- Modulo `29`: the three possible patterns of the counts. -/
theorem step29 (g : Fin 35 → G) (hg : IsPerfect g) (ψ2 : G →+ H)
    (hψ2 : Function.Surjective ψ2) :
    ∃ D : ℕ, D < 29 ∧ (∀ h, h ≠ 0 → ((cnt (fun j => ψ2 (g j)) h + cnt (fun j => ψ2 (g j)) (-h) : ℕ) : H)
        = D) ∧ (28 * D + 2 * cnt (fun j => ψ2 (g j)) 0 ≤ 70) ∧
      ((D = 0 ∧ (cnt (fun j => ψ2 (g j)) 0 = 6 ∨ cnt (fun j => ψ2 (g j)) 0 = 35)) ∨
        (D = 1 ∧ cnt (fun j => ψ2 (g j)) 0 = 21) ∨ (D = 2 ∧ cnt (fun j => ψ2 (g j)) 0 = 7)) := by
  classical
  set y : Fin 35 → H := fun j => ψ2 (g j) with hy
  have hP2 := P_vanish hg ψ2 hψ2 28 (by norm_num) fun v h1 h2 he => kappa_35_29 v h2 h1 he
  have hP2' : ∀ k, 1 ≤ k → k < 29 - 1 → P y k = 0 := fun k h1 h2 => hP2 k h1 (by omega)
  set D := (-P y (29 - 1)).val with hD
  have hDlt : D < 29 := ZMod.val_lt _
  have hN2 : ∀ h, h ≠ 0 → ((cnt y h + cnt y (-h) : ℕ) : H) = D := pairs_mod y hP2'
  have hz2 := zero_mod y hP2'
  rw [← hD, ZMod.natCast_eq_natCast_iff'] at hz2
  have hbd := pairs_bound y D hDlt hN2
  have hc0 := cnt_le y 0
  refine ⟨D, hDlt, hN2, hbd, ?_⟩
  rcases (show D = 0 ∨ D = 1 ∨ D = 2 by omega) with h | h | h <;> rw [h] at hz2 hbd <;> omega

/-- There is no perfect code of radius three in dimension `35`. -/
theorem no_perfect_35 (g : Fin 35 → G) (hg : IsPerfect g) : False := by
  classical
  have hcardG : Fintype.card G = 59711 := by rw [card_eq_of_perfect hg, card_ball_35]
  obtain ⟨ψ1, hψ1⟩ := exists_surj_zmod (G := G) 71
    (by rw [Nat.card_eq_fintype_card, hcardG]; norm_num)
  obtain ⟨ψ2, hψ2⟩ := exists_surj_zmod (G := G) 29
    (by rw [Nat.card_eq_fintype_card, hcardG]; norm_num)
  obtain ⟨hx0, hx1⟩ := step71 g hg hcardG ψ1 hψ1
  obtain ⟨D, hDlt, hN2, hbd, hcases⟩ := step29 g hg ψ2 hψ2
  have hcard : ∀ t, ((#{g' | ψ2 g' = t} : ℕ) : K) = 0 := by
    intro t
    rw [card_fiber ψ2 hψ2 t, hcardG, ZMod.card]
    decide
  rcases hcases with ⟨hD0, hc⟩ | ⟨hD1, hc⟩ | ⟨hD2, hc⟩
  · have hdiv : ∀ h, h ≠ 0 → 29 ∣ #{j | ψ2 (g j) = h} + #{j | ψ2 (g j) = -h} := by
      intro h h0
      have := hN2 h h0
      rw [hD0, Nat.cast_zero, ZMod.natCast_eq_zero_iff] at this
      exact this
    have h841 := mod841 hg ψ2 hψ2 hdiv
    rw [hcardG] at h841
    exact check_35 (cnt (fun j => ψ2 (g j)) 0) hc h841
  · have hpair := pairs_eq _ D hDlt hN2 (by omega)
    rw [hD1] at hpair
    exact final_contra _ _ hx0 hx1 1 (Or.inl rfl) (hpair 1 one_ne_zero)
      (branch_one g hg ψ1 ψ2 hcard hpair hc)
  · have hpair := pairs_eq _ D hDlt hN2 (by omega)
    rw [hD2] at hpair
    exact final_contra _ _ hx0 hx1 2 (Or.inr rfl) (hpair 1 one_ne_zero)
      (branch_two g hg ψ1 ψ2 hcard hpair hc)

end Perfect

end GolombWelch
