/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMinimumCollisionAudit

/-!
# A signed renewal coefficient before estimating the minimum boundary

The lattice Euler recurrences used in the optional all-count probe have a
positive small-cycle cumulative sequence. Its successive differences are
the signed selected-mode coefficients. This gives a sign for the complete
cutoff second difference, after summing the count recurrence.

This file is a lattice model audit. It does not replace the literal prime
measure, transfer a complete-leg phase through a mask, or bound the joined
arithmetic carrier.
-/

namespace RiemannGaussian.ZetaRieszRenewalCurvature
noncomputable section
open scoped BigOperators

/-- Positive cumulative coefficients with cycle lengths strictly below
the lattice cutoff. The initial coefficient includes the empty object. -/
def smoothCoeff (ell : ℕ) : ℕ → ℝ
  | 0 => 1
  | n+1 => (∑ m : Fin (n+1),
      if n+1 < (m : ℕ)+ell then smoothCoeff ell m else 0)/(n+1)
termination_by n => n

/-- The signed coefficient, including its atom at zero. -/
def signedCoeff (ell : ℕ) : ℕ → ℝ
  | 0 => 1
  | n+1 => smoothCoeff ell (n+1)-smoothCoeff ell n

/-- Unsigned rough Euler coefficients; their count sum retains its
empty coefficient and every admissible positive order. -/
def roughCoeff (ell : ℕ) : ℕ → ℝ
  | 0 => 1
  | n+1 => (∑ m : Fin (n+1),
      if (m : ℕ)+ell ≤ n+1 then roughCoeff ell m else 0)/(n+1)
termination_by n => n

theorem smoothCoeff_nonneg (ell n : ℕ) : 0 ≤ smoothCoeff ell n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => norm_num [smoothCoeff]
    | succ n =>
      rw [smoothCoeff]
      apply div_nonneg ?_ (by positivity)
      apply Finset.sum_nonneg
      intro m _
      split_ifs
      · exact ih m m.isLt
      · rfl

theorem roughCoeff_nonneg (ell n : ℕ) : 0 ≤ roughCoeff ell n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => norm_num [roughCoeff]
    | succ n =>
      rw [roughCoeff]
      apply div_nonneg ?_ (by positivity)
      apply Finset.sum_nonneg
      intro m _
      split_ifs
      · exact ih m m.isLt
      · rfl

/-- A single admissible small cycle gives a strict cumulative lower
bound. No alternating sum is bounded by its absolute coefficients. -/
theorem factorial_lower_smooth {ell : ℕ} (hell : 2 ≤ ell) (n : ℕ) :
    1/(n.factorial : ℝ) ≤ smoothCoeff ell n := by
  induction n with
  | zero => norm_num [smoothCoeff]
  | succ n ih =>
    have hmem : (⟨n, Nat.lt_succ_self n⟩ : Fin (n+1)) ∈ Finset.univ := Finset.mem_univ _
    have hsum := Finset.single_le_sum
      (f := fun m : Fin (n+1) => if n+1 < (m : ℕ)+ell then smoothCoeff ell m else 0)
      (fun m _ => by split_ifs; exact smoothCoeff_nonneg _ _; rfl) hmem
    have hn : n+1 < n+ell := by omega
    simp only [if_pos hn] at hsum
    rw [smoothCoeff]
    have hn0 : (0 : ℝ) < n+1 := by positivity
    apply (div_le_div_of_nonneg_right (ih.trans hsum) hn0.le).trans_eq'
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp

/-- The defining cumulative recurrence as a literal interval sum. -/
theorem smoothCoeff_scaled {n : ℕ} (hn : 0 < n) (ell : ℕ) :
    (n : ℝ)*smoothCoeff ell n =
      ∑ m ∈ Finset.Ico (n+1-ell) n, smoothCoeff ell m := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [smoothCoeff, Nat.cast_succ, mul_div_cancel₀ _ (by positivity : (n+1 : ℝ) ≠ 0)]
  rw [Fin.sum_univ_eq_sum_range (fun m : ℕ =>
    if n+1 < m+ell then smoothCoeff ell m else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

private theorem smoothCoeff_sum_difference {ell : ℕ} (hell : 1 ≤ ell) (n : ℕ) :
    (n : ℝ)*smoothCoeff ell n =
      (∑ m ∈ Finset.range n, smoothCoeff ell m)-
      ∑ m ∈ Finset.range (n+1-ell), smoothCoeff ell m := by
  by_cases hn : n = 0
  · subst n
    simp [Nat.sub_eq_zero_of_le hell]
  · rw [smoothCoeff_scaled (Nat.pos_of_ne_zero hn),
      Finset.sum_Ico_eq_sub _ (by omega)]

/-- The complete alternating count recurrence collapses to one negative
smooth coefficient. This retains the empty atom and all lower orders. -/
theorem signedCoeff_scaled {ell : ℕ} (hell : 1 ≤ ell) (n : ℕ) :
    (n+1 : ℝ)*signedCoeff ell (n+1) =
      -(if ell ≤ n+1 then smoothCoeff ell (n+1-ell) else 0) := by
  have h₀ := smoothCoeff_sum_difference hell n
  have h₁ := smoothCoeff_sum_difference hell (n+1)
  rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one] at h₁
  by_cases he : ell ≤ n+1
  · have hn : n+1+1-ell = (n+1-ell)+1 := by omega
    rw [hn, Finset.sum_range_succ] at h₁
    rw [if_pos he, signedCoeff]
    linarith
  · have hn₀ : n+1-ell = 0 := by omega
    have hn₁ : n+1+1-ell = 0 := by omega
    simp only [hn₀, Finset.sum_range_zero, sub_zero] at h₀
    simp only [hn₁, Finset.sum_range_zero, sub_zero] at h₁
    rw [if_neg he, signedCoeff]
    linarith

theorem signedCoeff_nonpos {ell n : ℕ} (hell : 1 ≤ ell) (hn : 0 < n) :
    signedCoeff ell n ≤ 0 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hs := signedCoeff_scaled hell n
  have hnon : 0 ≤ (if ell ≤ n+1 then smoothCoeff ell (n+1-ell) else 0) := by
    split_ifs
    · exact smoothCoeff_nonneg _ _
    · rfl
  have hn0 : (0 : ℝ) < n+1 := by positivity
  nlinarith

theorem signedCoeff_strict {ell n : ℕ} (hell : 2 ≤ ell) (hn : ell ≤ n) :
    signedCoeff ell n < 0 := by
  have hn0 : 0 < n := by omega
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0.ne'
  have hs := signedCoeff_scaled (by omega : 1 ≤ ell) n
  rw [if_pos hn] at hs
  have hp : 0 < smoothCoeff ell (n+1-ell) :=
    lt_of_lt_of_le (by positivity) (factorial_lower_smooth hell _)
  have hnn : (0 : ℝ) < n+1 := by positivity
  nlinarith

/-- Exact recovery of the positive cumulative sequence from the signed
coefficients. No signed mass is dropped. -/
theorem sum_signedCoeff (ell n : ℕ) :
    (∑ m ∈ Finset.range (n+1), signedCoeff ell m) = smoothCoeff ell n := by
  induction n with
  | zero => simp [signedCoeff,smoothCoeff]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, signedCoeff]
    ring

/-- Euler recurrence of the negative count exponential, now proved for
the concrete signed coefficients rather than postulated as a sign rule. -/
theorem signedCoeff_euler {ell : ℕ} (hell : 1 ≤ ell) (n : ℕ) :
    (n+1 : ℝ)*signedCoeff ell (n+1) =
      -(∑ m ∈ Finset.range (n+2-ell), signedCoeff ell m) := by
  rw [signedCoeff_scaled hell]
  by_cases he : ell ≤ n+1
  · rw [if_pos he]
    have hn : n+2-ell = (n+1-ell)+1 := by omega
    rw [hn,sum_signedCoeff]
  · have hn : n+2-ell = 0 := by omega
    simp [he,hn]

/-- The probe's Euler recurrence determines this sequence uniquely. -/
theorem signedCoeff_unique {ell : ℕ} (hell : 1 ≤ ell) (a : ℕ → ℝ)
    (ha : a 0 = 1)
    (hrec : ∀ n : ℕ, (n+1 : ℝ)*a (n+1) =
      -(∑ m ∈ Finset.range (n+2-ell), a m)) : a = signedCoeff ell := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact ha
    | succ n =>
      have hs := signedCoeff_euler hell n
      have he := hrec n
      have hsum : (∑ m ∈ Finset.range (n+2-ell), a m) =
          ∑ m ∈ Finset.range (n+2-ell), signedCoeff ell m := by
        apply Finset.sum_congr rfl
        intro m hm
        exact ih m (by have := Finset.mem_range.mp hm; omega)
      rw [hsum] at he
      have hn : (0 : ℝ) < n+1 := by positivity
      nlinarith

/-- The single-cycle term is retained in the unsigned count sum. -/
theorem roughCoeff_lower {ell n : ℕ} (hell : 1 ≤ ell) (hn : ell ≤ n) :
    1/(n : ℝ) ≤ roughCoeff ell n := by
  have hn0 : 0 < n := by omega
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0.ne'
  have hmem : (⟨0, by omega⟩ : Fin (n+1)) ∈ Finset.univ := Finset.mem_univ _
  have hsum := Finset.single_le_sum
    (f := fun m : Fin (n+1) => if (m : ℕ)+ell ≤ n+1 then roughCoeff ell m else 0)
    (fun m _ => by split_ifs; exact roughCoeff_nonneg _ _; rfl) hmem
  simp only [zero_add, if_pos hn, roughCoeff] at hsum
  rw [roughCoeff, Nat.cast_succ]
  exact div_le_div_of_nonneg_right hsum (by positivity)

/-- The finite inverse ramp convolution. Both coefficient atoms at zero
are kept. The total degree is discrete; the cutoff remains real. -/
def response (ell S : ℕ) (d : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (S+1),
    -signedCoeff ell (S-j)*roughCoeff ell j*max 0 (d-j)

/-- One marked pair gives the same four-hinge tent already used for
literal divisor incidences. -/
def triangle (r d : ℝ) : ℝ :=
  ZetaSquarefreeRieszWindows.primePairTent r r d

theorem triangle_nonneg {r : ℝ} (hr : 0 ≤ r) (d : ℝ) : 0 ≤ triangle r d :=
  (ZetaSquarefreeRieszWindows.primePairTent_bounds hr hr d).1

theorem triangle_zero {r d : ℝ} (hr : 0 ≤ r) (hd : d ≤ 0) : triangle r d = 0 :=
  ZetaSquarefreeRieszWindows.primePairTent_eq_zero_of_outside hr hr (Or.inl hd)

theorem triangle_pos {r d : ℝ} (hd : 0 < d) (hdr : d < 2*r) :
    0 < triangle r d := by
  dsimp [triangle, ZetaSquarefreeRieszWindows.primePairTent]
  simp only [max_def]
  split_ifs <;> linarith

/-- All selected-background counts are summed before the pair's second
cutoff difference is estimated. This is an exact finite identity. -/
theorem response_second_difference (ell S : ℕ) (r d : ℝ) :
    response ell S d-2*response ell S (d-r)+response ell S (d-2*r) =
      ∑ j ∈ Finset.range (S+1),
        -signedCoeff ell (S-j)*roughCoeff ell j*triangle r (d-j) := by
  unfold response
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold triangle ZetaSquarefreeRieszWindows.primePairTent
  have h₁ : d-r-j = d-j-r := by ring
  have h₂ : d-2*r-j = d-j-r-r := by ring
  rw [h₁,h₂]
  ring

private theorem response_second_term_nonneg {ell S : ℕ} (hell : 1 ≤ ell)
    {r d : ℝ} (hr : 0 ≤ r) (hd : d < S) {j : ℕ}
    (hj : j ∈ Finset.range (S+1)) :
    0 ≤ -signedCoeff ell (S-j)*roughCoeff ell j*triangle r (d-j) := by
  have hjle : j ≤ S := by have := Finset.mem_range.mp hj; omega
  by_cases he : j = S
  · subst j
    rw [triangle_zero hr (by linarith)]
    simp
  · exact mul_nonneg (mul_nonneg (neg_nonneg.mpr
      (signedCoeff_nonpos hell (by omega))) (roughCoeff_nonneg _ _))
        (triangle_nonneg hr _)

/-- The joined selected-background coefficient has a definite sign.
The diagonal atom vanishes by the strict support inequality, not deletion. -/
theorem response_second_difference_nonneg {ell S : ℕ} (hell : 1 ≤ ell)
    {r d : ℝ} (hr : 0 ≤ r) (hd : d < S) :
    0 ≤ response ell S d-2*response ell S (d-r)+response ell S (d-2*r) := by
  rw [response_second_difference]
  exact Finset.sum_nonneg (fun _ hj => response_second_term_nonneg hell hr hd hj)

/-- In an interior chamber the count sum does not annihilate the pair
coefficient. This is a lattice-model theorem, not a prime-sum residue. -/
theorem response_second_difference_pos {ell S j : ℕ} (hell : 2 ≤ ell)
    (hj : ell ≤ j) (hSj : ell ≤ S-j) {r d : ℝ}
    (hr : 0 < r) (hd : d < S) (hdj : 0 < d-j) (hjr : d-j < 2*r) :
    0 < response ell S d-2*response ell S (d-r)+response ell S (d-2*r) := by
  have hjmem : j ∈ Finset.range (S+1) := Finset.mem_range.mpr (by omega)
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have ht : 0 < -signedCoeff ell (S-j)*roughCoeff ell j*triangle r (d-j) :=
    mul_pos (mul_pos (neg_pos.mpr (signedCoeff_strict hell hSj))
      (lt_of_lt_of_le (div_pos zero_lt_one hjpos)
        (roughCoeff_lower (by omega) hj))) (triangle_pos hdj hjr)
  rw [response_second_difference]
  exact ht.trans_le (Finset.single_le_sum
    (fun _ hm => response_second_term_nonneg (by omega) hr.le hd hm) hjmem)

/-- A rational upper-face interior regression with all orders included:
the signed recurrence is not zero even after its entire count sum. -/
theorem upper_face_lattice_strict :
    0 < response 20 185 (143/2)-2*response 20 185 (103/2)+
      response 20 185 (63/2) := by
  have h := response_second_difference_pos
    (ell := 20) (S := 185) (j := 60) (r := 20) (d := 143/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- Higher even differences need not have the paired coefficient's sign.
Ten unit insertions and one background share of 5/4 give this exact
normalized Riesz difference. Other modal assignments cannot be discarded
on the strength of the second-difference sign theorem. -/
theorem tenth_difference_one_background :
    (ZetaRieszMinimumCollisionAudit.equalKernel 10 1 (143/40)-
      ZetaRieszMinimumCollisionAudit.equalKernel 10 1 (143/40-5/4))/(5/4) =
        -(96/5 : ℝ) := by
  norm_num [ZetaRieszMinimumCollisionAudit.equalKernel,
    Finset.sum_range_succ,Nat.choose]

end
end RiemannGaussian.ZetaRieszRenewalCurvature
