/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiLocalCancellationKernel
import RiemannGaussian.RosserSchoenfeldLargeSmoothed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Explicit inherited smoothed-PNT bounds for the complete local filter

The compact kernel retains all knot and endpoint terms when transferred
against the actual logarithmically smoothed prime sum. No subpower bound
on the resulting signed comparison is claimed.
-/

namespace RiemannGaussian
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators

private theorem local_step_monotone (r : ℝ) :
    Monotone (fun s : ℝ => if r ≤ s then (1 : ℝ) else 0) := by
  intro x y hxy
  change (if r ≤ x then (1 : ℝ) else 0) ≤ (if r ≤ y then 1 else 0)
  split_ifs with hx hy hy <;> norm_num
  exact False.elim (hy (hx.trans hxy))

private theorem local_integral_step_deriv {k k' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hk : ∀ s, HasDerivAt k (k' s) s) (hkc : Continuous k') (r : ℝ) :
    (∫ s in a..b, k' s * (if r ≤ s then (1 : ℝ) else 0)) =
      k b * (if r ≤ b then 1 else 0) - k a * (if r ≤ a then 1 else 0) -
        (if a < r ∧ r ≤ b then k r else 0) := by
  have hi (x y : ℝ) : IntervalIntegrable
      (fun s : ℝ => k' s * (if r ≤ s then (1 : ℝ) else 0)) volume x y :=
    (local_step_monotone r).intervalIntegrable.continuousOn_mul hkc.continuousOn
  by_cases hra : r ≤ a
  · have hrb := hra.trans hab
    rw [ite_eq_left hrb, ite_eq_left hra, ite_eq_right (by rintro ⟨h, _⟩; linarith), sub_zero]
    simp only [mul_one]
    calc
      _ = ∫ s in a..b, k' s := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hab] at hs
        dsimp only
        rw [ite_eq_left (hra.trans hs.1), mul_one]
      _ = _ := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hk s)
        (hkc.intervalIntegrable _ _)
  · by_cases hrb : r ≤ b
    · have har : a ≤ r := (lt_of_not_ge hra).le
      have hzero : (∫ s in a..r, k' s * (if r ≤ s then (1 : ℝ) else 0)) = 0 := by
        calc
          _ = ∫ _ in a..r, (0 : ℝ) := by
            apply intervalIntegral.integral_congr_Ioo_of_le har
            intro s hs
            dsimp only
            rw [ite_eq_right (not_le.mpr hs.2), mul_zero]
          _ = 0 := by simp
      have htail : (∫ s in r..b, k' s * (if r ≤ s then (1 : ℝ) else 0)) = k b - k r := by
        calc
          _ = ∫ s in r..b, k' s := by
            apply intervalIntegral.integral_congr
            intro s hs
            rw [uIcc_of_le hrb] at hs
            dsimp only
            rw [ite_eq_left hs.1, mul_one]
          _ = _ := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hk s)
            (hkc.intervalIntegrable _ _)
      rw [← intervalIntegral.integral_add_adjacent_intervals (hi a r) (hi r b),
        hzero, htail, ite_eq_left hrb, ite_eq_right hra,
        ite_eq_left ⟨lt_of_not_ge hra, hrb⟩]
      ring
    · rw [ite_eq_right hrb, ite_eq_right hra, ite_eq_right (by rintro ⟨_, h⟩; exact hrb h)]
      simp only [mul_zero, sub_zero]
      calc
        _ = ∫ _ in a..b, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_le hab] at hs
          dsimp only
          rw [ite_eq_right (by intro h; exact hrb (h.trans hs.2)), mul_zero]
        _ = 0 := by simp

private theorem local_hinge_right_deriv (r s : ℝ) :
    HasDerivWithinAt (fun x : ℝ => max (x - r) 0)
      (if r ≤ s then 1 else 0) (Ioi s) s := by
  by_cases hrs : r ≤ s
  · rw [ite_eq_left hrs]
    apply ((hasDerivAt_id s).sub_const r).hasDerivWithinAt.congr
    · intro x hx
      exact max_eq_left (by linarith [show s < x from hx])
    · exact max_eq_left (sub_nonneg.mpr hrs)
  · rw [ite_eq_right hrs]
    apply (hasDerivAt_const s (0 : ℝ)).hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [eventually_lt_nhds (lt_of_not_ge hrs) |>.filter_mono nhdsWithin_le_nhds]
        with x hx
      exact max_eq_right (by linarith)
    · exact max_eq_right (by linarith)

private theorem local_twice_abel_hinge {k k' k'' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hk : ∀ s, HasDerivAt k (k' s) s)
    (hk' : ∀ s, HasDerivAt k' (k'' s) s) (hkc : Continuous k')
    (hkcc : Continuous k'') (r : ℝ) :
    (if a < r ∧ r ≤ b then k r else 0) =
      k b * (if r ≤ b then 1 else 0) - k a * (if r ≤ a then 1 else 0) -
        k' b * max (b - r) 0 + k' a * max (a - r) 0 +
          ∫ s in a..b, k'' s * max (s - r) 0 := by
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (a := a) (b := b) (u := k') (u' := k'') (v := fun s : ℝ => max (s - r) 0)
    (v' := fun s : ℝ => if r ≤ s then 1 else 0)
    hkc.continuousOn (by fun_prop)
    (fun s _ => (hk' s).hasDerivWithinAt) (fun s _ => local_hinge_right_deriv r s)
    (hkcc.intervalIntegrable _ _) (local_step_monotone r).intervalIntegrable
  rw [local_integral_step_deriv hab hk hkc r] at hip
  linarith

private def localBand (t A B s : ℝ) : ℝ := Real.exp (-s / 2) * (A * (s - t) + B)
private def localBandD (t A B s : ℝ) : ℝ :=
  Real.exp (-s / 2) * (A - (A * (s - t) + B) / 2)
private def localBandDD (t A B s : ℝ) : ℝ :=
  Real.exp (-s / 2) * (-A + (A * (s - t) + B) / 4)

private theorem localBand_deriv (t A B s : ℝ) :
    HasDerivAt (localBand t A B) (localBandD t A B s) s := by
  have he := (((hasDerivAt_id s).neg).div_const 2).exp
  have ha := (((hasDerivAt_id s).sub_const t).const_mul A).add_const B
  convert he.mul ha using 1
  · rfl
  · dsimp [localBandD]
    ring

private theorem localBandD_deriv (t A B s : ℝ) :
    HasDerivAt (localBandD t A B) (localBandDD t A B s) s := by
  have he := (((hasDerivAt_id s).neg).div_const 2).exp
  have ha := (hasDerivAt_const s A).sub
    (((((hasDerivAt_id s).sub_const t).const_mul A).add_const B).div_const 2)
  convert he.mul ha using 1
  · rfl
  · dsimp [localBandDD]
    ring

private theorem local_twice_abel_band {a b : ℝ} (hab : a ≤ b) (t A B r : ℝ) :
    (if a < r ∧ r ≤ b then localBand t A B r else 0) =
      localBand t A B b * (if r ≤ b then 1 else 0) -
        localBand t A B a * (if r ≤ a then 1 else 0) -
        localBandD t A B b * max (b - r) 0 +
        localBandD t A B a * max (a - r) 0 +
          ∫ s in a..b, localBandDD t A B s * max (s - r) 0 := by
  exact local_twice_abel_hinge hab (localBand_deriv t A B)
    (localBandD_deriv t A B) (by unfold localBandD; fun_prop)
    (by unfold localBandDD; fun_prop) r

private theorem local_kernel_three_bands (t r : ℝ) :
    Real.exp (-r / 2) * suzukiLocalSignedKernel (r - t) =
      (if t < r ∧ r ≤ t + Real.log 2 then localBand t (Real.sqrt 2) 0 r else 0) +
      (if t + Real.log 2 < r ∧ r ≤ t + 2 * Real.log 2 then
        localBand t (-(Real.sqrt 2 + 1)) ((2 * Real.sqrt 2 + 1) * Real.log 2) r else 0) +
      (if t + 2 * Real.log 2 < r ∧ r ≤ t + 3 * Real.log 2 then
        localBand t 1 (-3 * Real.log 2) r else 0) := by
  have hh : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  by_cases h0 : r ≤ t
  · rw [suzukiLocalSignedKernel_eq_zero_of_nonpos (by linarith),
      ite_eq_right (by rintro ⟨h, _⟩; linarith),
      ite_eq_right (by rintro ⟨h, _⟩; linarith),
      ite_eq_right (by rintro ⟨h, _⟩; linarith)]
    ring
  · by_cases h1 : r ≤ t + Real.log 2
    · rw [suzukiLocalSignedKernel_eq_first (by linarith) (by linarith),
        ite_eq_left ⟨lt_of_not_ge h0, h1⟩,
        ite_eq_right (by rintro ⟨h, _⟩; linarith),
        ite_eq_right (by rintro ⟨h, _⟩; linarith)]
      unfold localBand
      ring
    · by_cases h2 : r ≤ t + 2 * Real.log 2
      · rw [suzukiLocalSignedKernel_eq_middle (by linarith) (by linarith),
          ite_eq_right (by rintro ⟨_, h⟩; linarith),
          ite_eq_left ⟨lt_of_not_ge h1, h2⟩,
          ite_eq_right (by rintro ⟨h, _⟩; linarith)]
        unfold localBand
        ring
      · by_cases h3 : r ≤ t + 3 * Real.log 2
        · rw [suzukiLocalSignedKernel_eq_last (by linarith) (by linarith),
            ite_eq_right (by rintro ⟨_, h⟩; linarith),
            ite_eq_right (by rintro ⟨_, h⟩; linarith),
            ite_eq_left ⟨lt_of_not_ge h2, h3⟩]
          unfold localBand
          ring
        · rw [suzukiLocalSignedKernel_eq_zero_of_three_mul_le (by linarith),
            ite_eq_right (by rintro ⟨_, h⟩; linarith),
            ite_eq_right (by rintro ⟨_, h⟩; linarith),
            ite_eq_right (by rintro ⟨_, h⟩; linarith)]
          ring

/-- The complete twice-Abel functional, retaining all four derivative jumps
and the three smooth open-band contributions. -/
def suzukiLocalAbelFunctional (t : ℝ) (f : ℝ → ℝ) : ℝ :=
  Real.sqrt 2 * Real.exp (-t / 2) * f t -
    (2 * Real.sqrt 2 + 1) * Real.exp (-(t + Real.log 2) / 2) * f (t + Real.log 2) +
    (Real.sqrt 2 + 2) * Real.exp (-(t + 2 * Real.log 2) / 2) *
      f (t + 2 * Real.log 2) -
    Real.exp (-(t + 3 * Real.log 2) / 2) * f (t + 3 * Real.log 2) +
    (∫ s in t..t + Real.log 2, localBandDD t (Real.sqrt 2) 0 s * f s) +
    (∫ s in t + Real.log 2..t + 2 * Real.log 2,
      localBandDD t (-(Real.sqrt 2 + 1)) ((2 * Real.sqrt 2 + 1) * Real.log 2) s * f s) +
    (∫ s in t + 2 * Real.log 2..t + 3 * Real.log 2,
      localBandDD t 1 (-3 * Real.log 2) s * f s)

/-- Exact Green identity for each literal source atom, including atoms at knots. -/
theorem suzukiLocalAbelFunctional_hinge (t r : ℝ) :
    suzukiLocalAbelFunctional t (fun s => max (s - r) 0) =
      Real.exp (-r / 2) * suzukiLocalSignedKernel (r - t) := by
  have hh : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 := local_twice_abel_band (show t ≤ t + Real.log 2 by linarith)
    t (Real.sqrt 2) 0 r
  have h2 := local_twice_abel_band
    (show t + Real.log 2 ≤ t + 2 * Real.log 2 by linarith)
    t (-(Real.sqrt 2 + 1)) ((2 * Real.sqrt 2 + 1) * Real.log 2) r
  have h3 := local_twice_abel_band
    (show t + 2 * Real.log 2 ≤ t + 3 * Real.log 2 by linarith)
    t 1 (-3 * Real.log 2) r
  rw [local_kernel_three_bands]
  unfold suzukiLocalAbelFunctional
  unfold localBand
  dsimp only [localBand, localBandD] at h1 h2 h3
  linear_combination -h1 - h2 - h3

private theorem localAbel_add (t : ℝ) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    suzukiLocalAbelFunctional t (f + g) =
      suzukiLocalAbelFunctional t f + suzukiLocalAbelFunctional t g := by
  have hi (A B a b : ℝ) :
      (∫ s in a..b, localBandDD t A B s * (f s + g s)) =
        (∫ s in a..b, localBandDD t A B s * f s) +
          ∫ s in a..b, localBandDD t A B s * g s := by
    simp_rw [mul_add]
    apply intervalIntegral.integral_add <;>
      exact (by unfold localBandDD; fun_prop : Continuous _).intervalIntegrable _ _
  unfold suzukiLocalAbelFunctional
  simp only [Pi.add_apply, hi]
  ring

private theorem localAbel_const_mul (t a : ℝ) (f : ℝ → ℝ) :
    suzukiLocalAbelFunctional t (fun s => a * f s) = a * suzukiLocalAbelFunctional t f := by
  have hi (A B x y : ℝ) :
      (∫ s in x..y, localBandDD t A B s * (a * f s)) =
        a * ∫ s in x..y, localBandDD t A B s * f s := by
    simp_rw [show ∀ s, localBandDD t A B s * (a * f s) =
      a * (localBandDD t A B s * f s) by intro s; ring]
    exact intervalIntegral.integral_const_mul _ _
  unfold suzukiLocalAbelFunctional
  simp only [hi]
  ring

private theorem localAbel_sum {ι : Type*} (t : ℝ) (I : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ I, Continuous (f i)) :
    suzukiLocalAbelFunctional t (fun s => ∑ i ∈ I, f i s) =
      ∑ i ∈ I, suzukiLocalAbelFunctional t (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [suzukiLocalAbelFunctional]
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    rw [show (fun s => f i s + ∑ j ∈ I, f j s) =
      f i + (fun s => ∑ j ∈ I, f j s) by rfl,
      localAbel_add t (hf i (Finset.mem_insert_self _ _))
        (continuous_finsetSum _ (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

private theorem localAbel_congr (t : ℝ) {f g : ℝ → ℝ}
    (hfg : ∀ s ∈ Icc t (t + 3 * Real.log 2), f s = g s) :
    suzukiLocalAbelFunctional t f = suzukiLocalAbelFunctional t g := by
  have hh : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hi (A B a b : ℝ) (ha : t ≤ a) (hb : b ≤ t + 3 * Real.log 2) (hab : a ≤ b) :
      (∫ s in a..b, localBandDD t A B s * f s) =
        ∫ s in a..b, localBandDD t A B s * g s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hab] at hs
    dsimp only
    rw [hfg s ⟨ha.trans hs.1, hs.2.trans hb⟩]
  unfold suzukiLocalAbelFunctional
  rw [hfg t ⟨le_rfl, by linarith⟩,
    hfg (t + Real.log 2) ⟨by linarith, by linarith⟩,
    hfg (t + 2 * Real.log 2) ⟨by linarith, by linarith⟩,
    hfg (t + 3 * Real.log 2) ⟨by linarith, le_rfl⟩,
    hi _ _ _ _ le_rfl (by linarith) (by linarith),
    hi _ _ _ _ (by linarith) (by linarith) (by linarith),
    hi _ _ _ _ (by linarith) le_rfl (by linarith)]

/-- The twice-Abel functional is exactly the original complete prime
comparison when applied to the actual logarithmically smoothed prime sum. -/
theorem suzukiLocalPrimeComparison_eq_abel_primitive (t : ℝ) :
    suzukiLocalPrimeComparison t =
      suzukiLocalAbelFunctional t RosserSchoenfeldPrimePrimitive.value := by
  let I := suzukiArithmeticPrimeWindow (t + 3 * Real.log 2)
  have hp : suzukiLocalAbelFunctional t RosserSchoenfeldPrimePrimitive.value =
      suzukiLocalAbelFunctional t
        (fun s => ∑ n ∈ I, ArithmeticFunction.vonMangoldt n * max (s - Real.log n) 0) := by
    apply localAbel_congr
    intro s hs
    exact RosserSchoenfeldPrimePrimitive.value_eq_fixed_sum hs.2
  rw [hp, localAbel_sum t I _ (by intro n _; fun_prop),
    suzukiLocalPrimeComparison_eq_sum_signed_kernel]
  apply Finset.sum_congr rfl
  intro n hn
  rw [localAbel_const_mul, suzukiLocalAbelFunctional_hinge]
  obtain ⟨hn1, _⟩ := mem_suzukiArithmeticPrimeWindow_iff.mp hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have he : Real.exp (-Real.log n / 2) = 1 / Real.sqrt n := by
    rw [show -Real.log n / 2 = -(Real.log n / 2) by ring, Real.exp_neg,
      Real.exp_half, Real.exp_log hnpos]
    simp only [one_div]
  rw [he]
  ring

private theorem local_twice_abel_smooth {f f' f'' k k' k'' : ℝ → ℝ} (a b : ℝ)
    (hf : ∀ s, HasDerivAt f (f' s) s) (hf' : ∀ s, HasDerivAt f' (f'' s) s)
    (hk : ∀ s, HasDerivAt k (k' s) s) (hk' : ∀ s, HasDerivAt k' (k'' s) s)
    (hfc : Continuous f') (hfcc : Continuous f'')
    (hkc : Continuous k') (hkcc : Continuous k'') :
    (∫ s in a..b, k s * f'' s) =
      k b * f' b - k a * f' a - k' b * f b + k' a * f a +
        ∫ s in a..b, k'' s * f s := by
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b) (u := k) (v := f') (u' := k') (v' := f'')
    (fun s _ => hk s) (fun s _ => hf' s)
    (hkc.intervalIntegrable _ _) (hfcc.intervalIntegrable _ _)
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b) (u := k') (v := f) (u' := k'') (v' := f')
    (fun s _ => hk' s) (fun s _ => hf s)
    (hkcc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _)
  linarith

private theorem localAbel_eq_bands (t : ℝ) {f f' f'' : ℝ → ℝ}
    (hf : ∀ s, HasDerivAt f (f' s) s) (hf' : ∀ s, HasDerivAt f' (f'' s) s)
    (hfc : Continuous f') (hfcc : Continuous f'') :
    suzukiLocalAbelFunctional t f =
      (∫ s in t..t + Real.log 2, localBand t (Real.sqrt 2) 0 s * f'' s) +
      (∫ s in t + Real.log 2..t + 2 * Real.log 2,
        localBand t (-(Real.sqrt 2 + 1)) ((2 * Real.sqrt 2 + 1) * Real.log 2) s * f'' s) +
      (∫ s in t + 2 * Real.log 2..t + 3 * Real.log 2,
        localBand t 1 (-3 * Real.log 2) s * f'' s) := by
  have hi (A B a b : ℝ) := local_twice_abel_smooth a b hf hf'
    (localBand_deriv t A B) (localBandD_deriv t A B) hfc hfcc
    (by unfold localBandD; fun_prop) (by unfold localBandDD; fun_prop)
  have h1 := hi (Real.sqrt 2) 0 t (t + Real.log 2)
  have h2 := hi (-(Real.sqrt 2 + 1)) ((2 * Real.sqrt 2 + 1) * Real.log 2)
    (t + Real.log 2) (t + 2 * Real.log 2)
  have h3 := hi 1 (-3 * Real.log 2) (t + 2 * Real.log 2) (t + 3 * Real.log 2)
  unfold suzukiLocalAbelFunctional
  unfold localBand
  dsimp only [localBand, localBandD] at h1 h2 h3
  linear_combination -h1 - h2 - h3

private theorem localBand_integral_exp (t A B a b : ℝ) :
    (∫ s in a..b, localBand t A B s * Real.exp s) =
      (Real.exp (b / 2) * (2 * (A * (b - t) + B) - 4 * A)) -
        (Real.exp (a / 2) * (2 * (A * (a - t) + B) - 4 * A)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro s _
    have hd := (((hasDerivAt_id s).div_const 2).exp).mul
      (((((hasDerivAt_id s).sub_const t).const_mul A).add_const B).const_mul 2 |>.sub_const (4 * A))
    convert hd using 1
    · rfl
    · dsimp [localBand]
      have he : Real.exp (-s / 2) * Real.exp s = Real.exp (s / 2) := by
        rw [← Real.exp_add, show -s / 2 + s = s / 2 by ring]
      linear_combination (A * (s - t) + B) * he
  · exact (by unfold localBand; fun_prop : Continuous _).intervalIntegrable _ _

/-- The functional annihilates the full smooth main term of the actual
prime primitive, including its constant and linear normalization. -/
theorem suzukiLocalAbelFunctional_main (t C : ℝ) :
    suzukiLocalAbelFunctional t (fun s => Real.exp s - 1 - C * s) = 0 := by
  have hf (s : ℝ) : HasDerivAt (fun s => Real.exp s - 1 - C * s)
      (Real.exp s - C) s := by
    convert ((Real.hasDerivAt_exp s).sub_const 1).sub ((hasDerivAt_id s).const_mul C) using 1 <;>
      first | rfl | ring
  have hf' (s : ℝ) : HasDerivAt (fun s => Real.exp s - C) (Real.exp s) s :=
    (Real.hasDerivAt_exp s).sub_const C
  rw [localAbel_eq_bands t hf hf' (by fun_prop) (by fun_prop),
    localBand_integral_exp, localBand_integral_exp, localBand_integral_exp]
  have he1 : Real.exp ((t + Real.log 2) / 2) = Real.exp (t / 2) * Real.sqrt 2 := by
    rw [add_div, Real.exp_add, Real.exp_half (Real.log 2),
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have he2 : Real.exp ((t + 2 * Real.log 2) / 2) = Real.exp (t / 2) * 2 := by
    rw [show (t + 2 * Real.log 2) / 2 = t / 2 + Real.log 2 by ring,
      Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have he3 : Real.exp ((t + 3 * Real.log 2) / 2) = Real.exp (t / 2) * (2 * Real.sqrt 2) := by
    rw [show (t + 3 * Real.log 2) / 2 =
      (t + Real.log 2) / 2 + Real.log 2 by ring, Real.exp_add,
      Real.exp_log (by norm_num : (0 : ℝ) < 2), he1]
    ring
  rw [he1, he2, he3]
  linear_combination (-8 * Real.exp (t / 2)) *
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

private theorem local_sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

private theorem local_log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h
  exact h

private theorem local_kernel_abs_le_three (v : ℝ) : |suzukiLocalSignedKernel v| ≤ 3 := by
  have ht (w : ℝ) : 0 ≤ suzukiLocalTriangle (Real.log 2) w ∧
      suzukiLocalTriangle (Real.log 2) w ≤ 1 := by
    unfold suzukiLocalTriangle
    exact ⟨le_max_left _ _, max_le (by norm_num)
      ((sub_le_self _ (abs_nonneg _)).trans local_log_two_le_one)⟩
  have hc := Real.sqrt_nonneg 2
  unfold suzukiLocalSignedKernel
  calc
    _ ≤ |Real.sqrt 2 * suzukiLocalTriangle (Real.log 2) v| +
        |suzukiLocalTriangle (Real.log 2) (v - Real.log 2)| := abs_sub _ _
    _ = Real.sqrt 2 * suzukiLocalTriangle (Real.log 2) v +
        suzukiLocalTriangle (Real.log 2) (v - Real.log 2) := by
      rw [abs_of_nonneg (mul_nonneg hc (ht v).1), abs_of_nonneg (ht _).1]
    _ ≤ 3 := by nlinarith [ht v, ht (v - Real.log 2), local_sqrt_two_le_two]

private theorem localBandDD_abs_le {t A B s : ℝ} (hts : t ≤ s)
    (hA : |A| ≤ 3) (hL : |A * (s - t) + B| ≤ 3) :
    |localBandDD t A B s| ≤ 4 * Real.exp (-t / 2) := by
  have hf : |-A + (A * (s - t) + B) / 4| ≤ 4 := by
    calc
      _ ≤ |A| + |A * (s - t) + B| / 4 := by
        simpa only [abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)] using
          (abs_add_le (-A) ((A * (s - t) + B) / 4))
      _ ≤ 4 := by linarith
  unfold localBandDD
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-s / 2) * 4 := mul_le_mul_of_nonneg_left hf (Real.exp_nonneg _)
    _ ≤ Real.exp (-t / 2) * 4 := by gcongr
    _ = _ := by ring

/-- A uniform primitive remainder on the full packet support gives a
complete explicit bound, including every derivative jump and band integral. -/
theorem abs_suzukiLocalAbelFunctional_le {t B : ℝ} (hB : 0 ≤ B) {f : ℝ → ℝ}
    (hf : ∀ s ∈ Icc t (t + 3 * Real.log 2), |f s| ≤ B) :
    |suzukiLocalAbelFunctional t f| ≤ 24 * B * Real.exp (-t / 2) := by
  have hh : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hc := local_sqrt_two_le_two
  have hc0 := Real.sqrt_nonneg 2
  have hpoint (s m M : ℝ) (hs : s ∈ Icc t (t + 3 * Real.log 2))
      (hm : |m| ≤ M) : |m * Real.exp (-s / 2) * f s| ≤ M * Real.exp (-t / 2) * B := by
    have hM : 0 ≤ M := (abs_nonneg _).trans hm
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul _ (hf s hs) (abs_nonneg _) (by positivity)
    apply mul_le_mul hm (Real.exp_le_exp.mpr (by linarith [hs.1]))
      (Real.exp_nonneg _) ((abs_nonneg _).trans hm)
  have hint (A C a b : ℝ) (ha : t ≤ a) (hb : b ≤ t + 3 * Real.log 2)
      (hab : a ≤ b) (hlen : b - a ≤ 1) (hA : |A| ≤ 3)
      (hL : ∀ s ∈ Icc a b, |A * (s - t) + C| ≤ 3) :
      |∫ s in a..b, localBandDD t A C s * f s| ≤ 4 * Real.exp (-t / 2) * B := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := 4 * Real.exp (-t / 2) * B)
      (f := fun s => localBandDD t A C s * f s) (by
        intro s hs
        rw [uIoc_of_le hab] at hs
        have hs' : s ∈ Icc a b := ⟨hs.1.le, hs.2⟩
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (localBandDD_abs_le (ha.trans hs'.1) hA (hL s hs'))
          (hf s ⟨ha.trans hs'.1, hs'.2.trans hb⟩) (abs_nonneg _) (by positivity))
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hnorm
    exact hnorm.trans (mul_le_of_le_one_right (by positivity) hlen)
  have h0 := hpoint t (Real.sqrt 2) 2 ⟨le_rfl, by linarith⟩
    (by rw [abs_of_nonneg hc0]; exact hc)
  have h1 := hpoint (t + Real.log 2) (2 * Real.sqrt 2 + 1) 5
    ⟨by linarith, by linarith⟩ (by rw [abs_of_nonneg (by positivity)]; linarith)
  have h2 := hpoint (t + 2 * Real.log 2) (Real.sqrt 2 + 2) 4
    ⟨by linarith, by linarith⟩ (by rw [abs_of_nonneg (by positivity)]; linarith)
  have h3 := hpoint (t + 3 * Real.log 2) 1 1 ⟨by linarith, le_rfl⟩ (by norm_num)
  have hi1 := hint (Real.sqrt 2) 0 t (t + Real.log 2)
    le_rfl (by linarith) (by linarith) (by linarith [local_log_two_le_one])
    (by rw [abs_of_nonneg hc0]; linarith) (by
      intro s hs
      rw [add_zero, ← suzukiLocalSignedKernel_eq_first
        (by linarith [hs.1]) (by linarith [hs.2])]
      exact local_kernel_abs_le_three _)
  have hi2 := hint (-(Real.sqrt 2 + 1)) ((2 * Real.sqrt 2 + 1) * Real.log 2)
    (t + Real.log 2) (t + 2 * Real.log 2)
    (by linarith) (by linarith) (by linarith) (by linarith [local_log_two_le_one])
    (by rw [abs_neg, abs_of_nonneg (by positivity)]; linarith) (by
      intro s hs
      have hw := suzukiLocalSignedKernel_eq_middle
        (show Real.log 2 ≤ s - t by linarith [hs.1])
        (show s - t ≤ 2 * Real.log 2 by linarith [hs.2])
      have he : -(Real.sqrt 2 + 1) * (s - t) + (2 * Real.sqrt 2 + 1) * Real.log 2 =
          suzukiLocalSignedKernel (s - t) := by rw [hw]; ring
      rw [he]
      exact local_kernel_abs_le_three _)
  have hi3 := hint 1 (-3 * Real.log 2) (t + 2 * Real.log 2) (t + 3 * Real.log 2)
    (by linarith) le_rfl (by linarith) (by linarith [local_log_two_le_one]) (by norm_num) (by
      intro s hs
      have hw := suzukiLocalSignedKernel_eq_last
        (show 2 * Real.log 2 ≤ s - t by linarith [hs.1])
        (show s - t ≤ 3 * Real.log 2 by linarith [hs.2])
      have hb := local_kernel_abs_le_three (s - t)
      rw [hw] at hb
      convert hb using 1
      congr 1
      ring)
  simp only [one_mul] at h3
  unfold suzukiLocalAbelFunctional
  rw [abs_le] at h0 h1 h2 h3 hi1 hi2 hi3 ⊢
  constructor <;> nlinarith

/-- The full original signed comparison inherits a bound from the actual
smoothed PNT remainder on exactly its compact logarithmic support. -/
theorem abs_suzukiLocalPrimeComparison_le_of_primitive_envelope {t B : ℝ}
    (hB : 0 ≤ B)
    (hR : ∀ s ∈ Icc t (t + 3 * Real.log 2),
      |RosserSchoenfeldPrimePrimitive.value s -
        (Real.exp s - 1 - Real.log (2 * Real.pi) * s)| ≤ B) :
    |suzukiLocalPrimeComparison t| ≤ 24 * B * Real.exp (-t / 2) := by
  let q : ℝ → ℝ := fun s => Real.exp s - 1 - Real.log (2 * Real.pi) * s
  let R : ℝ → ℝ := fun s => RosserSchoenfeldPrimePrimitive.value s - q s
  have hcq : Continuous q := by dsimp [q]; fun_prop
  have hcR : Continuous R := RosserSchoenfeldPrimePrimitive.continuous_value.sub hcq
  have hsum : R + q = RosserSchoenfeldPrimePrimitive.value := by ext s; simp [R]
  have he := localAbel_add t hcR hcq
  rw [hsum, show suzukiLocalAbelFunctional t q = 0 from
    suzukiLocalAbelFunctional_main t (Real.log (2 * Real.pi)), add_zero] at he
  rw [suzukiLocalPrimeComparison_eq_abel_primitive, he]
  exact abs_suzukiLocalAbelFunctional_le hB hR

/-- The existing smoothed PNT estimate transfers directly to the complete
signed filter with a logarithmic-square saving, without desmoothing first.
This is an inherited quantitative baseline, not the required subpower bound. -/
theorem abs_suzukiLocalPrimeComparison_le_log_square {t : ℝ} (ht : 4900 ≤ t) :
    |suzukiLocalPrimeComparison t| ≤ 3 * Real.exp (t / 2) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hh : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hb := abs_suzukiLocalPrimeComparison_le_of_primitive_envelope
    (t := t) (B := Real.exp (t + 3 * Real.log 2) / (64 * t ^ 2)) (by positivity) (by
      intro s hs
      have hp := RosserSchoenfeldLargeSmoothed.abs_prime_sub_main_lt
        (show 4900 ≤ s by linarith [hs.1])
      apply hp.le.trans
      gcongr
      · exact hs.2
      · nlinarith [hs.1])
  have he : Real.exp (t + 3 * Real.log 2) * Real.exp (-t / 2) =
      8 * Real.exp (t / 2) := by
    rw [← Real.exp_add, show t + 3 * Real.log 2 + -t / 2 =
      t / 2 + (Real.log 2 + Real.log 2 + Real.log 2) by ring,
      Real.exp_add, Real.exp_add, Real.exp_add,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    ring
  apply hb.trans_eq
  field_simp
  simp only [neg_div] at he
  linear_combination 24 * he

end
end RiemannGaussian
