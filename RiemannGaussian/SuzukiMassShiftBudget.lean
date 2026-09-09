/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiLogarithmicWork

/-!
# Logarithmic control of a fixed shift in the actual prime mass

The cumulative cost of a fixed additive shift in the old prime mass is
controlled by a telescoping logarithm of that same mass. This is an
unconditional estimate, retaining every prime-power atom and its old mass.
It lets the new logarithmic-loss criterion tolerate removing the constant
Archimedean slope correction without discarding the nonlinear logarithm.
The exact logarithmic mass drift is also separated: its centered remainder
is absolutely summable, with a uniform inverse-square-root finite-band bound.

The independent lower bound for the remaining signed work is still open.
-/

namespace RiemannGaussian
noncomputable section
open Filter
open scoped BigOperators Topology

/-- The full old prime-power mass at the original work cell. -/
abbrev suzukiOldPrimeMass (count : ℕ) : ℝ :=
  screwPrefixMass suzukiPrimeWeight (count + 1)

/-- Exact update of the full old mass by its next von-Mangoldt atom. -/
theorem suzukiOldPrimeMass_succ (count : ℕ) :
    suzukiOldPrimeMass (count + 1) =
      suzukiOldPrimeMass count + suzukiPrimeWeight (count + 1) := by
  exact screwPrefixMass_succ suzukiPrimeWeight (count + 1)

/-- The initial old mass consists of the original prime-two atom. -/
theorem suzukiOldPrimeMass_zero :
    suzukiOldPrimeMass 0 = Real.log 2 / Real.sqrt 2 := by
  simp [suzukiOldPrimeMass, screwPrefixMass, suzukiPrimeWeight,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

/-- Nonnegative arithmetic atoms make the original old masses monotone. -/
theorem monotone_suzukiOldPrimeMass : Monotone suzukiOldPrimeMass := by
  apply monotone_nat_of_le_succ
  intro count
  rw [suzukiOldPrimeMass_succ]
  exact le_add_of_nonneg_right (suzukiPrimeWeight_nonnegative _)

/-- Every logarithm of an unshifted old mass has a positive argument. -/
theorem suzukiOldPrimeMass_pos (count : ℕ) : 0 < suzukiOldPrimeMass count := by
  have h0 : 0 < suzukiOldPrimeMass 0 := by
    rw [suzukiOldPrimeMass_zero]
    exact div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))
  exact h0.trans_le (monotone_suzukiOldPrimeMass (Nat.zero_le count))

/-- A uniform bound on every literal von-Mangoldt atom, using its elementary
logarithmic bound and positivity of its square-root denominator. -/
theorem suzukiPrimeWeight_le_two (count : ℕ) : suzukiPrimeWeight count ≤ 2 := by
  have hn : 0 < ((count + 2 : ℕ) : ℝ) := by positivity
  have hs := Real.sqrt_pos.mpr hn
  have hl : Real.log ((count + 2 : ℕ) : ℝ) ≤ 2 * Real.sqrt ((count + 2 : ℕ) : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt hn.le] at h
    linarith
  unfold suzukiPrimeWeight
  exact (div_le_iff₀ hs).mpr (ArithmeticFunction.vonMangoldt_le_log.trans hl)

/-- Each relative mass increment is paid for by its own logarithmic mass
increase, with one constant depending only on the retained initial atom. -/
theorem suzuki_relative_atom_le_log_mass_increment (count : ℕ) :
    suzukiPrimeWeight (count + 1) / suzukiOldPrimeMass count ≤
      (1 + 2 / suzukiOldPrimeMass 0) *
        (Real.log (suzukiOldPrimeMass (count + 1)) - Real.log (suzukiOldPrimeMass count)) := by
  let m := suzukiOldPrimeMass count
  let a := suzukiPrimeWeight (count + 1)
  have hm : 0 < m := suzukiOldPrimeMass_pos count
  have ha : 0 ≤ a := suzukiPrimeWeight_nonnegative _
  have hma : 0 < m + a := by positivity
  have h0 : 0 < suzukiOldPrimeMass 0 := suzukiOldPrimeMass_pos 0
  have hrel : a / m ≤ 2 / suzukiOldPrimeMass 0 :=
    div_le_div₀ (by norm_num) (suzukiPrimeWeight_le_two _) h0
      (monotone_suzukiOldPrimeMass (Nat.zero_le count))
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hma hm)
  rw [Real.log_div hma.ne' hm.ne'] at hlog
  have hfrac : 1 - ((m + a) / m)⁻¹ = a / (m + a) := by
    field_simp
    ring
  rw [hfrac] at hlog
  have hlogpos : 0 ≤ Real.log (m + a) - Real.log m :=
    sub_nonneg.mpr (Real.log_le_log hm (by linarith))
  have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 1 + a / m)
  have heq : (1 + a / m) * (a / (m + a)) = a / m := by
    field_simp
  rw [heq] at hmul
  rw [suzukiOldPrimeMass_succ]
  exact hmul.trans (mul_le_mul_of_nonneg_right (by linarith) hlogpos)

/-- The whole relative-atom cost on an arbitrary finite band is bounded
by its actual logarithmic mass ratio, retaining both endpoints. -/
theorem sum_suzuki_relative_atom_le_log_mass_ratio (start count : ℕ) :
    (∑ j ∈ Finset.range count,
      suzukiPrimeWeight (start + j + 1) / suzukiOldPrimeMass (start + j)) ≤
      (1 + 2 / suzukiOldPrimeMass 0) *
        (Real.log (suzukiOldPrimeMass (start + count)) - Real.log (suzukiOldPrimeMass start)) := by
  calc
    _ ≤ ∑ j ∈ Finset.range count, (1 + 2 / suzukiOldPrimeMass 0) *
        (Real.log (suzukiOldPrimeMass (start + j + 1)) -
          Real.log (suzukiOldPrimeMass (start + j))) :=
      Finset.sum_le_sum (fun j _ => suzuki_relative_atom_le_log_mass_increment (start + j))
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simpa only [Nat.add_assoc, Nat.add_zero] using
        (Finset.sum_range_sub (fun j => Real.log (suzukiOldPrimeMass (start + j))) count)

/-- The old mass has an explicit square-root upper envelope. -/
theorem suzukiOldPrimeMass_le_twelve_sqrt (count : ℕ) :
    suzukiOldPrimeMass count ≤ 12 * Real.sqrt ((count + 2 : ℕ) : ℝ) := by
  rw [suzukiOldPrimeMass, screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass]
  exact suzukiChebyshevWeightedMass_le_twelve_sqrt (by norm_cast; omega)

/-- The initial atom and actual Chebyshev envelope turn the logarithmic
mass ratio into a logarithmic cutoff allowance with fixed constants. -/
theorem suzuki_log_mass_ratio_le_log_cutoff (count : ℕ) :
    Real.log (suzukiOldPrimeMass count) - Real.log (suzukiOldPrimeMass 0) ≤
      Real.log 12 + |Real.log (suzukiOldPrimeMass 0)| +
        Real.log ((count + 2 : ℕ) : ℝ) / 2 := by
  have h := Real.log_le_log (suzukiOldPrimeMass_pos count)
    (suzukiOldPrimeMass_le_twelve_sqrt count)
  rw [Real.log_mul (by norm_num) (Real.sqrt_pos.mpr (by positivity)).ne',
    Real.log_sqrt (by positivity)] at h
  linarith [neg_abs_le (Real.log (suzukiOldPrimeMass 0))]

/-- A finite arithmetic work with a fixed additive old-mass shift. At zero
shift it contains no Archimedean or implicit-center constant. -/
def suzukiMassShiftWork (δ : ℝ) (count : ℕ) : ℝ :=
  suzukiPrimeWeight (count + 1) *
    (suzukiPrimeLocation (count + 1) - 2 * Real.log ((suzukiOldPrimeMass count + δ) / 2))

/-- Exact cost of a nonnegative shift inside the mass logarithm. All
logarithm arguments are proved positive before the identity is used. -/
theorem suzukiMassShiftWork_sub_eq {δ : ℝ} (hδ : 0 ≤ δ) (count : ℕ) :
    suzukiMassShiftWork 0 count - suzukiMassShiftWork δ count =
      2 * suzukiPrimeWeight (count + 1) * Real.log (1 + δ / suzukiOldPrimeMass count) := by
  have hm := suzukiOldPrimeMass_pos count
  have hmd : 0 < suzukiOldPrimeMass count + δ := by positivity
  have he : 1 + δ / suzukiOldPrimeMass count =
      (suzukiOldPrimeMass count + δ) / suzukiOldPrimeMass count := by field_simp
  unfold suzukiMassShiftWork
  rw [add_zero, he, Real.log_div hm.ne' (by norm_num),
    Real.log_div hmd.ne' (by norm_num), Real.log_div hmd.ne' hm.ne']
  ring

/-- The shift cost is nonnegative and bounded by the same atom's relative
mass increment, retaining that atom/mass coupling. -/
theorem suzukiMassShiftWork_sub_bounds {δ : ℝ} (hδ : 0 ≤ δ) (count : ℕ) :
    0 ≤ suzukiMassShiftWork 0 count - suzukiMassShiftWork δ count ∧
      suzukiMassShiftWork 0 count - suzukiMassShiftWork δ count ≤
        2 * δ * (suzukiPrimeWeight (count + 1) / suzukiOldPrimeMass count) := by
  rw [suzukiMassShiftWork_sub_eq hδ]
  have hfrac : 0 ≤ δ / suzukiOldPrimeMass count :=
    div_nonneg hδ (suzukiOldPrimeMass_pos count).le
  have ha := suzukiPrimeWeight_nonnegative (count + 1)
  constructor
  · exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  · have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + δ / suzukiOldPrimeMass count)
    have h := mul_le_mul_of_nonneg_left hlog
      (by positivity : 0 ≤ 2 * suzukiPrimeWeight (count + 1))
    exact h.trans_eq (by ring)

/-- Independent quantitative control of the complete finite-band shift
cost by a telescoping logarithm of the original old masses. -/
theorem sum_suzukiMassShiftWork_sub_le_log_mass_ratio {δ : ℝ} (hδ : 0 ≤ δ)
    (start count : ℕ) :
    (∑ j ∈ Finset.range count,
      (suzukiMassShiftWork 0 (start + j) - suzukiMassShiftWork δ (start + j))) ≤
      2 * δ * (1 + 2 / suzukiOldPrimeMass 0) *
        (Real.log (suzukiOldPrimeMass (start + count)) - Real.log (suzukiOldPrimeMass start)) := by
  calc
    _ ≤ ∑ j ∈ Finset.range count,
        2 * δ * (suzukiPrimeWeight (start + j + 1) / suzukiOldPrimeMass (start + j)) :=
      Finset.sum_le_sum (fun j _ => (suzukiMassShiftWork_sub_bounds hδ (start + j)).2)
    _ = 2 * δ * ∑ j ∈ Finset.range count,
        suzukiPrimeWeight (start + j + 1) / suzukiOldPrimeMass (start + j) := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (sum_suzuki_relative_atom_le_log_mass_ratio start count)
        (by positivity : 0 ≤ 2 * δ)
      simpa only [mul_assoc] using h

/-- The complete cumulative discrepancy from a fixed nonnegative mass
shift grows at most logarithmically, with explicit initial-mass constants. -/
theorem sum_suzukiMassShiftWork_sub_le_log_cutoff {δ : ℝ} (hδ : 0 ≤ δ) (count : ℕ) :
    (∑ j ∈ Finset.range count, (suzukiMassShiftWork 0 j - suzukiMassShiftWork δ j)) ≤
      2 * δ * (1 + 2 / suzukiOldPrimeMass 0) *
        (Real.log 12 + |Real.log (suzukiOldPrimeMass 0)| +
          Real.log ((count + 2 : ℕ) : ℝ) / 2) := by
  have h := sum_suzukiMassShiftWork_sub_le_log_mass_ratio hδ 0 count
  simp only [Nat.zero_add] at h
  exact h.trans (mul_le_mul_of_nonneg_left (suzuki_log_mass_ratio_le_log_cutoff count)
    (by have h0 := suzukiOldPrimeMass_pos 0; positivity))

/-- The exact Archimedean constant is negative. Its removal is therefore a
nonnegative mass-shift comparison covered by the independent budget above. -/
theorem suzukiArchimedeanSlopeConstant_neg : suzukiArchimedeanSlopeConstant < 0 := by
  have h := suzukiPointwiseArchimedeanSlope_lt_two_mul_exp_half
    (t := Real.log 2) le_rfl
  rw [suzukiPointwiseArchimedeanSlope_eq_exp_add_constant_add_positiveTail
    (Real.log_pos (by norm_num))] at h
  linarith [suzukiArchimedeanPositiveSlopeTail_nonneg (Real.log 2)]

/-- The original finite mass-log work is exactly the shifted family at the
actual constant; it has not been redefined by removing that constant. -/
theorem suzukiMassShiftWork_neg_constant_eq (count : ℕ) :
    suzukiMassShiftWork (-suzukiArchimedeanSlopeConstant) count = suzukiFirstTailMassLogWork count := by
  simp only [suzukiMassShiftWork, suzukiOldPrimeMass, suzukiFirstTailMassLogWork, sub_eq_add_neg]

/-- Ordinary-prime new events in the finite shifted work. Every preceding
prime power is still present in the old mass inside the logarithm. -/
def suzukiOrdinaryPrimeMassShiftWork (δ : ℝ) (count : ℕ) : ℝ :=
  ∑ j ∈ Finset.range count, if (j + 3).Prime then suzukiMassShiftWork δ j else 0

/-- The complete ordinary-prime shift discrepancy is nonnegative and has
the same independent logarithmic budget as the full event sequence. -/
theorem suzukiOrdinaryPrimeMassShiftWork_sub_bounds {δ : ℝ} (hδ : 0 ≤ δ) (count : ℕ) :
    0 ≤ suzukiOrdinaryPrimeMassShiftWork 0 count - suzukiOrdinaryPrimeMassShiftWork δ count ∧
      suzukiOrdinaryPrimeMassShiftWork 0 count - suzukiOrdinaryPrimeMassShiftWork δ count ≤
        2 * δ * (1 + 2 / suzukiOldPrimeMass 0) *
          (Real.log 12 + |Real.log (suzukiOldPrimeMass 0)| +
            Real.log ((count + 2 : ℕ) : ℝ) / 2) := by
  have he : suzukiOrdinaryPrimeMassShiftWork 0 count - suzukiOrdinaryPrimeMassShiftWork δ count =
      ∑ j ∈ Finset.range count,
        if (j + 3).Prime then suzukiMassShiftWork 0 j - suzukiMassShiftWork δ j else 0 := by
    unfold suzukiOrdinaryPrimeMassShiftWork
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  rw [he]
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    split_ifs
    · exact (suzukiMassShiftWork_sub_bounds hδ j).1
    · exact le_refl 0
  · apply le_trans _ (sum_suzukiMassShiftWork_sub_le_log_cutoff hδ count)
    apply Finset.sum_le_sum
    intro j hj
    split_ifs
    · exact le_refl _
    · exact (suzukiMassShiftWork_sub_bounds hδ j).1

/-- Exact identification of the old ordinary-prime mass-log target inside
the shifted finite family. -/
theorem suzukiOrdinaryPrimeMassShiftWork_neg_constant_eq (count : ℕ) :
    suzukiOrdinaryPrimeMassShiftWork (-suzukiArchimedeanSlopeConstant) count =
      ∑ j ∈ Finset.range count, if (j + 3).Prime then suzukiFirstTailMassLogWork j else 0 := by
  simp only [suzukiOrdinaryPrimeMassShiftWork, suzukiMassShiftWork_neg_constant_eq]

/-- The logarithmic-loss RH target can omit the fixed Archimedean mass
shift, with its full discrepancy paid by the proved independent budget.
The lower bound for this finite unshifted prime sum is still open. -/
theorem riemannHypothesis_of_suzuki_unshifted_ordinaryPrime_work_eventually_log_lower_bound
    (B : ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hw : ∀ᶠ count : ℕ in atTop, -(B + D * Real.log ((count + 2 : ℕ) : ℝ)) ≤
      suzukiOrdinaryPrimeMassShiftWork 0 count) :
    RiemannHypothesis := by
  let δ := -suzukiArchimedeanSlopeConstant
  let A := 2 * δ * (1 + 2 / suzukiOldPrimeMass 0)
  let K := Real.log 12 + |Real.log (suzukiOldPrimeMass 0)|
  have hδ : 0 ≤ δ := (neg_pos.mpr suzukiArchimedeanSlopeConstant_neg).le
  have hA : 0 ≤ A := by dsimp [A]; have h0 := suzukiOldPrimeMass_pos 0; positivity
  apply riemannHypothesis_of_suzuki_ordinaryPrime_massLog_eventually_log_lower_bound
    (B + A * K) (D := D + A / 2) (by positivity)
  filter_upwards [hw] with count hc
  have h := (suzukiOrdinaryPrimeMassShiftWork_sub_bounds hδ count).2
  change suzukiOrdinaryPrimeMassShiftWork 0 count - suzukiOrdinaryPrimeMassShiftWork δ count ≤
    A * (K + Real.log ((count + 2 : ℕ) : ℝ) / 2) at h
  dsimp [δ] at h
  rw [suzukiOrdinaryPrimeMassShiftWork_neg_constant_eq] at h
  nlinarith

private theorem log_gap_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x - Real.log (1 + x) ∧ x - Real.log (1 + x) ≤ x ^ 2 / (1 + x) := by
  have hp : 0 < 1 + x := by positivity
  have hl := Real.log_le_sub_one_of_pos hp
  have hu := Real.one_sub_inv_le_log_of_pos hp
  constructor
  · linarith
  · have he : x - (1 - (1 + x)⁻¹) = x ^ 2 / (1 + x) := by field_simp; ring
    linarith

/-- The relative-atom/log-increment discrepancy has a summable reciprocal
mass envelope; it does not carry a further logarithmic loss. -/
theorem suzuki_relative_atom_sub_log_increment_bounds (count : ℕ) :
    0 ≤ suzukiPrimeWeight (count + 1) / suzukiOldPrimeMass count -
      (Real.log (suzukiOldPrimeMass (count + 1)) - Real.log (suzukiOldPrimeMass count)) ∧
    suzukiPrimeWeight (count + 1) / suzukiOldPrimeMass count -
      (Real.log (suzukiOldPrimeMass (count + 1)) - Real.log (suzukiOldPrimeMass count)) ≤
        2 * (1 / suzukiOldPrimeMass count - 1 / suzukiOldPrimeMass (count + 1)) := by
  let m := suzukiOldPrimeMass count
  let a := suzukiPrimeWeight (count + 1)
  have hm : 0 < m := suzukiOldPrimeMass_pos count
  have ha : 0 ≤ a := suzukiPrimeWeight_nonnegative _
  have hma : 0 < m + a := by positivity
  have hg := log_gap_bounds (div_nonneg ha hm.le)
  have he : 1 + a / m = (m + a) / m := by field_simp
  rw [he, Real.log_div hma.ne' hm.ne'] at hg
  have hfrac : (a / m) ^ 2 / ((m + a) / m) = a * (1 / m - 1 / (m + a)) := by
    field_simp
    ring
  rw [hfrac] at hg
  have hd : 0 ≤ 1 / m - 1 / (m + a) :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hm (by linarith))
  rw [suzukiOldPrimeMass_succ]
  exact ⟨hg.1, hg.2.trans (mul_le_mul_of_nonneg_right (suzukiPrimeWeight_le_two _) hd)⟩

/-- After removing the explicit logarithmic mass drift, the fixed-shift
error is bounded cellwise by a reciprocal-mass difference. -/
theorem suzukiMassShiftWork_centered_error_bound {δ : ℝ} (hδ : 0 ≤ δ) (count : ℕ) :
    |suzukiMassShiftWork 0 count - suzukiMassShiftWork δ count -
      2 * δ * (Real.log (suzukiOldPrimeMass (count + 1)) - Real.log (suzukiOldPrimeMass count))| ≤
      (4 * δ + 2 * δ ^ 2 * (1 + 2 / suzukiOldPrimeMass 0)) *
        (1 / suzukiOldPrimeMass count - 1 / suzukiOldPrimeMass (count + 1)) := by
  let m := suzukiOldPrimeMass count
  let a := suzukiPrimeWeight (count + 1)
  let d := 1 / suzukiOldPrimeMass count - 1 / suzukiOldPrimeMass (count + 1)
  let k := 1 + 2 / suzukiOldPrimeMass 0
  have hm : 0 < m := suzukiOldPrimeMass_pos count
  have ha : 0 ≤ a := suzukiPrimeWeight_nonnegative _
  have hma : 0 < m + a := by positivity
  have h0 := suzukiOldPrimeMass_pos 0
  have hd : 0 ≤ d := sub_nonneg.mpr (one_div_le_one_div_of_le hm
    (monotone_suzukiOldPrimeMass (Nat.le_succ count)))
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hg := suzuki_relative_atom_sub_log_increment_bounds count
  have hrel : 1 + a / m ≤ k := by
    have h := div_le_div₀ (by norm_num : (0 : ℝ) ≤ 2)
      (suzukiPrimeWeight_le_two (count + 1)) h0
      (monotone_suzukiOldPrimeMass (Nat.zero_le count))
    dsimp [k, a, m]
    linarith
  have hfrac : a / m ^ 2 = (1 + a / m) * d := by
    dsimp [d]
    rw [suzukiOldPrimeMass_succ]
    change a / m ^ 2 = (1 + a / m) * (1 / m - 1 / (m + a))
    field_simp
    ring
  have hag : a / m ^ 2 ≤ k * d := by
    rw [hfrac]
    exact mul_le_mul_of_nonneg_right hrel hd
  have hlog := log_gap_bounds (div_nonneg hδ hm.le)
  have hlog' : δ / m - Real.log (1 + δ / m) ≤ (δ / m) ^ 2 :=
    hlog.2.trans (div_le_self (sq_nonneg _) (by linarith [div_nonneg hδ hm.le]))
  have hb := mul_le_mul_of_nonneg_left hlog' (by positivity : 0 ≤ 2 * a)
  have he : 2 * a * (δ / m) ^ 2 = 2 * δ ^ 2 * (a / m ^ 2) := by ring
  rw [he] at hb
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hag (by positivity : 0 ≤ 2 * δ ^ 2))
  have hl := mul_nonneg (by positivity : 0 ≤ 2 * a) hlog.1
  have hu := mul_le_mul_of_nonneg_left hg.2 (by positivity : 0 ≤ 2 * δ)
  have hp := mul_nonneg (by positivity : 0 ≤ 2 * δ) hg.1
  rw [suzukiMassShiftWork_sub_eq hδ]
  apply abs_le.mpr
  change -((4 * δ + 2 * δ ^ 2 * k) * d) ≤ _ ∧ _ ≤ (4 * δ + 2 * δ ^ 2 * k) * d
  change 2 * δ * (a / m - _) ≤ 2 * δ * (2 * d) at hu
  change 0 ≤ 2 * δ * (a / m - _) at hp
  change 0 ≤ 2 * a * (δ / m - _) at hl
  change 2 * a * (δ / m - _) ≤ 2 * δ ^ 2 * (k * d) at hb'
  change _ ≤ 2 * a * Real.log (1 + δ / m) - 2 * δ * _ ∧
    2 * a * Real.log (1 + δ / m) - 2 * δ * _ ≤ _
  have hcomm : a * (δ / m) = δ * (a / m) := by ring
  constructor <;> nlinarith [mul_nonneg hδ hd, mul_nonneg (mul_nonneg (sq_nonneg δ) hk) hd]

/-- The signed remainder after removing the exact logarithmic old-mass
drift from the fixed-shift cost. -/
def suzukiMassShiftCenteredError (δ : ℝ) (count : ℕ) : ℝ :=
  suzukiMassShiftWork 0 count - suzukiMassShiftWork δ count -
    2 * δ * (Real.log (suzukiOldPrimeMass (count + 1)) - Real.log (suzukiOldPrimeMass count))

/-- The full absolute error over any finite band is controlled by its
reciprocal-mass endpoints, without dependence on the number of events. -/
theorem sum_abs_suzukiMassShiftCenteredError_le {δ : ℝ} (hδ : 0 ≤ δ) (start count : ℕ) :
    (∑ j ∈ Finset.range count, |suzukiMassShiftCenteredError δ (start + j)|) ≤
      (4 * δ + 2 * δ ^ 2 * (1 + 2 / suzukiOldPrimeMass 0)) *
        (1 / suzukiOldPrimeMass start - 1 / suzukiOldPrimeMass (start + count)) := by
  calc
    _ ≤ ∑ j ∈ Finset.range count,
        (4 * δ + 2 * δ ^ 2 * (1 + 2 / suzukiOldPrimeMass 0)) *
          (1 / suzukiOldPrimeMass (start + j) - 1 / suzukiOldPrimeMass (start + j + 1)) :=
      Finset.sum_le_sum (fun j _ => suzukiMassShiftWork_centered_error_bound hδ (start + j))
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simpa only [Nat.add_assoc, Nat.add_zero] using
        (Finset.sum_range_sub' (fun j => 1 / suzukiOldPrimeMass (start + j)) count)

/-- Exact finite-band accounting: the shift cost is its logarithmic mass
drift plus the retained signed centered error. -/
theorem sum_suzukiMassShiftWork_sub_eq_log_mass_add_error (δ : ℝ) (start count : ℕ) :
    (∑ j ∈ Finset.range count,
      (suzukiMassShiftWork 0 (start + j) - suzukiMassShiftWork δ (start + j))) =
      2 * δ * (Real.log (suzukiOldPrimeMass (start + count)) - Real.log (suzukiOldPrimeMass start)) +
        ∑ j ∈ Finset.range count, suzukiMassShiftCenteredError δ (start + j) := by
  have ht : (∑ j ∈ Finset.range count,
      (Real.log (suzukiOldPrimeMass (start + j + 1)) - Real.log (suzukiOldPrimeMass (start + j)))) =
      Real.log (suzukiOldPrimeMass (start + count)) - Real.log (suzukiOldPrimeMass start) := by
    simpa only [Nat.add_assoc, Nat.add_zero] using
      (Finset.sum_range_sub (fun j => Real.log (suzukiOldPrimeMass (start + j))) count)
  simp only [suzukiMassShiftCenteredError, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [show (∑ j ∈ Finset.range count, Real.log (suzukiOldPrimeMass (start + j + 1))) -
      (∑ j ∈ Finset.range count, Real.log (suzukiOldPrimeMass (start + j))) =
      Real.log (suzukiOldPrimeMass (start + count)) - Real.log (suzukiOldPrimeMass start) by
        simpa only [Finset.sum_sub_distrib] using ht]
  ring

/-- A simple square-root lower bound for the original old mass on every
prefix from the already checked Chebyshev range onward. -/
theorem half_sqrt_le_suzukiOldPrimeMass {count : ℕ} (hc : 3 ≤ count) :
    Real.sqrt ((count + 2 : ℕ) : ℝ) / 2 ≤ suzukiOldPrimeMass count := by
  have hb : (5 : ℝ) ≤ ((count + 2 : ℕ) : ℝ) := by norm_cast; omega
  have h := sqrt_sub_half_sqrt_five_le_suzukiChebyshevWeightedMass hb
  have hs := Real.sqrt_le_sqrt hb
  rw [suzukiOldPrimeMass, screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass]
  linarith

/-- The centered shift error has a quantitative inverse-square-root band
bound, uniformly in band length, on the original physical cutoffs. -/
theorem sum_abs_suzukiMassShiftCenteredError_le_inv_sqrt {δ : ℝ} (hδ : 0 ≤ δ)
    {start : ℕ} (hs : 3 ≤ start) (count : ℕ) :
    (∑ j ∈ Finset.range count, |suzukiMassShiftCenteredError δ (start + j)|) ≤
      2 * (4 * δ + 2 * δ ^ 2 * (1 + 2 / suzukiOldPrimeMass 0)) /
        Real.sqrt ((start + 2 : ℕ) : ℝ) := by
  let K := 4 * δ + 2 * δ ^ 2 * (1 + 2 / suzukiOldPrimeMass 0)
  have hK : 0 ≤ K := by dsimp [K]; have h0 := suzukiOldPrimeMass_pos 0; positivity
  have hm := suzukiOldPrimeMass_pos (start + count)
  have hp : 0 < Real.sqrt ((start + 2 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  calc
    _ ≤ K * (1 / suzukiOldPrimeMass start - 1 / suzukiOldPrimeMass (start + count)) :=
      sum_abs_suzukiMassShiftCenteredError_le hδ start count
    _ ≤ K / suzukiOldPrimeMass start := by
      calc
        _ = K / suzukiOldPrimeMass start - K / suzukiOldPrimeMass (start + count) := by ring
        _ ≤ _ := sub_le_self _ (div_nonneg hK hm.le)
    _ ≤ K / (Real.sqrt ((start + 2 : ℕ) : ℝ) / 2) :=
      div_le_div₀ hK le_rfl (by positivity) (half_sqrt_le_suzukiOldPrimeMass hs)
    _ = _ := by dsimp [K]; ring

/-- The actual old mass tends to infinity by the unconditional Chebyshev
lower bound, so its reciprocal gives a genuine vanishing tail budget. -/
theorem suzukiOldPrimeMass_tendsto_atTop : Tendsto suzukiOldPrimeMass atTop atTop := by
  have hx : Tendsto (fun count : ℕ => ((count + 2 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hr : Tendsto (fun count : ℕ => Real.sqrt ((count + 2 : ℕ) : ℝ) / 2) atTop atTop := by
    simp only [Real.sqrt_eq_rpow, div_eq_mul_inv]
    exact ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hx).atTop_mul_const
      (by norm_num : (0 : ℝ) < 2⁻¹)
  apply tendsto_atTop_mono' atTop _ hr
  exact (eventually_ge_atTop 3).mono (fun _ hc => half_sqrt_le_suzukiOldPrimeMass hc)

private theorem reciprocal_mass_difference_hasSum :
    HasSum (fun count : ℕ => 1 / suzukiOldPrimeMass count - 1 / suzukiOldPrimeMass (count + 1))
      (1 / suzukiOldPrimeMass 0) := by
  have hn (count : ℕ) : 0 ≤ 1 / suzukiOldPrimeMass count - 1 / suzukiOldPrimeMass (count + 1) :=
    sub_nonneg.mpr (one_div_le_one_div_of_le (suzukiOldPrimeMass_pos count)
      (monotone_suzukiOldPrimeMass (Nat.le_succ count)))
  apply (hasSum_iff_tendsto_nat_of_nonneg hn _).mpr
  have hi : Tendsto (fun count : ℕ => 1 / suzukiOldPrimeMass count) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop suzukiOldPrimeMass_tendsto_atTop
  simpa only [Finset.sum_range_sub', sub_zero] using tendsto_const_nhds.sub hi

/-- The centered fixed-shift error is absolutely summable without any zero
hypothesis. Its logarithmic main drift remains explicit and is not discarded. -/
theorem summable_abs_suzukiMassShiftCenteredError {δ : ℝ} (hδ : 0 ≤ δ) :
    Summable (fun count : ℕ => |suzukiMassShiftCenteredError δ count|) := by
  apply (reciprocal_mass_difference_hasSum.summable.mul_left
    (4 * δ + 2 * δ ^ 2 * (1 + 2 / suzukiOldPrimeMass 0))).of_nonneg_of_le
    (fun _ => abs_nonneg _)
  exact fun count => suzukiMassShiftWork_centered_error_bound hδ count

/-- Removing the explicit logarithmic drift leaves a convergent signed
cumulative shift discrepancy, with the actual summable error as its limit. -/
theorem suzukiMassShiftWork_centered_sum_tendsto {δ : ℝ} (hδ : 0 ≤ δ) :
    Tendsto (fun count : ℕ =>
      (∑ j ∈ Finset.range count, (suzukiMassShiftWork 0 j - suzukiMassShiftWork δ j)) -
        2 * δ * (Real.log (suzukiOldPrimeMass count) - Real.log (suzukiOldPrimeMass 0)))
      atTop (𝓝 (∑' j : ℕ, suzukiMassShiftCenteredError δ j)) := by
  have hs : Summable (suzukiMassShiftCenteredError δ) :=
    (summable_abs_iff.mp (summable_abs_suzukiMassShiftCenteredError hδ))
  convert hs.hasSum.tendsto_sum_nat using 1
  ext count
  have he := sum_suzukiMassShiftWork_sub_eq_log_mass_add_error δ 0 count
  simp only [Nat.zero_add] at he
  rw [he, add_sub_cancel_left]

end
end RiemannGaussian
