/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryMellinBranches

/-!
# Ordinary lag quadrature of the unchanged carry tent

This is the ordinary, rather than alternating, inner lag sum. Its integral
is the autocorrelation of the original tent. The Bernoulli remainder is
retained exactly before the outer alternating lag sum is formed.
-/

namespace RiemannGaussian.SuzukiCarryPhaseQuadrature
noncomputable section
open Complex MeasureTheory Set Filter
open SuzukiCarryMellinLimit
open scoped BigOperators Topology

/-- Positive ramp whose grid sums generate the tent overlap. -/
def ramp (a t : ℝ) : ℝ := max 0 (a-t)

/-- Second Bernoulli polynomial in the exact endpoint correction. -/
def bernoulliTwo (v : ℝ) : ℝ := v^2-v+1/6

/-- Third Bernoulli polynomial in the exact endpoint correction. -/
def bernoulliThree (v : ℝ) : ℝ := v^3-3*v^2/2+v/2

/-- Fractional grid position of a ramp endpoint. -/
def remainderShare (a step : ℝ) : ℝ := a/step-(⌊a/step⌋₊ : ℝ)

/-- Finite ramp-power sum retaining the grid endpoint. -/
def rampPrefix (j : ℕ) (a step : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊a/step⌋₊+1), (a-(n : ℝ)*step)^j

private theorem sum_id (K : ℕ) :
    (∑ n ∈ Finset.range K, (n : ℝ)) = (K : ℝ)*((K : ℝ)-1)/2 := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

private theorem sum_sq (K : ℕ) :
    (∑ n ∈ Finset.range K, (n : ℝ)^2) =
      (K : ℝ)*((K : ℝ)-1)*(2*(K : ℝ)-1)/6 := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem remainderShare_bounds {a step : ℝ} (ha : 0 ≤ a) (hs : 0 < step) :
    0 ≤ remainderShare a step ∧ remainderShare a step < 1 := by
  have h := Nat.floor_le (show 0 ≤ a/step by positivity)
  have h' := Nat.lt_floor_add_one (a/step)
  simp only [remainderShare]
  constructor <;> linarith

/-- Exact ramp sum, including its literal order-zero endpoint. -/
theorem rampPrefix_one {a step : ℝ} (hs : 0 < step) :
    rampPrefix 1 a step = a^2/(2*step)+a/2+step/12-
      step/2*bernoulliTwo (remainderShare a step) := by
  unfold rampPrefix
  simp_rw [pow_one]
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.sum_mul, sum_id]
  simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  unfold remainderShare bernoulliTwo
  field_simp [hs.ne']
  ring

/-- Exact quadratic ramp sum; no oscillatory or low-order term is deleted. -/
theorem rampPrefix_two {a step : ℝ} (hs : 0 < step) :
    rampPrefix 2 a step = a^3/(3*step)+a^2/2+a*step/6-
      step^2/3*bernoulliThree (remainderShare a step) := by
  unfold rampPrefix
  simp_rw [show ∀ n : ℕ, (a-(n : ℝ)*step)^2 =
    a^2-2*a*step*(n : ℝ)+step^2*(n : ℝ)^2 by intro n; ring]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_id, sum_sq]
  simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  unfold remainderShare bernoulliThree
  field_simp [hs.ne']
  ring

theorem bernoulliTwo_abs_le {v : ℝ} (hv : v ∈ Icc 0 1) :
    |bernoulliTwo v| ≤ 1/6 := by
  rw [abs_le]
  unfold bernoulliTwo
  constructor
  · nlinarith [sq_nonneg (v-1/2)]
  · nlinarith [mul_nonneg hv.1 (sub_nonneg.mpr hv.2)]

theorem bernoulliThree_abs_le {v : ℝ} (hv : v ∈ Icc 0 1) :
    |bernoulliThree v| ≤ 1/2 := by
  have h : bernoulliThree v = v*(v-1)*(v-1/2) := by
    unfold bernoulliThree; ring
  rw [h, abs_mul, abs_mul]
  have h1 : |v| ≤ 1 := by rw [abs_of_nonneg hv.1]; exact hv.2
  have h2 : |v-1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hv.1,hv.2]
  have h3 : |v-1/2| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith [hv.1,hv.2]
  exact (mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)) h3
    (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem ramp_eq_zero {a t : ℝ} (h : a ≤ t) : ramp a t = 0 := by
  exact max_eq_left (by linarith)

theorem ramp_eq_sub {a t : ℝ} (h : t ≤ a) : ramp a t = a-t := by
  exact max_eq_right (by linarith)

/-- Exact four-knot representation of the ordinary tent overlap. -/
theorem tent_product_small {v : ℝ} (hv : v ∈ Icc 0 1) (t : ℝ) :
    tent t*tent (t+v) =
      v*ramp 1 t-ramp 1 t^2-
      2*(1-v)*ramp (2-v) t+2*ramp (2-v) t^2-
      2*(1-v)*ramp 2 t-2*ramp 2 t^2+
      v*ramp (3-v) t+ramp (3-v) t^2 := by
  by_cases h1 : t ≤ 1
  · rw [tent_eq_zero_of_le h1,
      ramp_eq_sub h1, ramp_eq_sub (by linarith [hv.2] : t ≤ 2-v),
      ramp_eq_sub (by linarith : t ≤ 2),
      ramp_eq_sub (by linarith [hv.2] : t ≤ 3-v)]
    ring

  by_cases h2 : t ≤ 2-v
  · rw [tent_eq_left (by linarith) (by linarith [hv.1]),
      tent_eq_left (by linarith [hv.1]) (by linarith),
      ramp_eq_zero (by linarith : 1 ≤ t), ramp_eq_sub h2,
      ramp_eq_sub (by linarith [hv.1] : t ≤ 2),
      ramp_eq_sub (by linarith : t ≤ 3-v)]
    ring
  by_cases h3 : t ≤ 2
  · rw [tent_eq_left (by linarith) h3,
      tent_eq_right (by linarith) (by linarith [hv.2]),
      ramp_eq_zero (by linarith : 1 ≤ t),
      ramp_eq_zero (by linarith : 2-v ≤ t), ramp_eq_sub h3,
      ramp_eq_sub (by linarith [hv.2] : t ≤ 3-v)]
    ring
  by_cases h4 : t ≤ 3-v
  · rw [tent_eq_right (by linarith) (by linarith [hv.1]),
      tent_eq_right (by linarith [hv.1]) (by linarith),
      ramp_eq_zero (by linarith : 1 ≤ t),
      ramp_eq_zero (by linarith [hv.1] : 2-v ≤ t),
      ramp_eq_zero (by linarith : 2 ≤ t), ramp_eq_sub h4]
    ring
  · rw [tent_eq_zero_of_ge (by linarith : 3 ≤ t+v),
      ramp_eq_zero (by linarith [hv.2] : 1 ≤ t),
      ramp_eq_zero (by linarith : 2-v ≤ t),
      ramp_eq_zero (by linarith [hv.2] : 2 ≤ t),
      ramp_eq_zero (by linarith : 3-v ≤ t)]
    ring

/-- The lag overlap, with the original positive grid and every endpoint. -/
def overlapSum (v step : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊3/step⌋₊+1),
    tent ((n : ℝ)*step)*tent ((n : ℝ)*step+v)

/-- Polynomial overlap integral for lags between zero and one. -/
def smallOverlapIntegral (v : ℝ) : ℝ := 2/3-v^2+v^3/2

/-- Exact Bernoulli grid correction on the small-lag branch. -/
def smallOverlapError (v step : ℝ) : ℝ :=
  -step/2*(v*bernoulliTwo (remainderShare 1 step)-
    2*(1-v)*bernoulliTwo (remainderShare (2-v) step)-
    2*(1-v)*bernoulliTwo (remainderShare 2 step)+
    v*bernoulliTwo (remainderShare (3-v) step))-
  step^2/3*(-bernoulliThree (remainderShare 1 step)+
    2*bernoulliThree (remainderShare (2-v) step)-
    2*bernoulliThree (remainderShare 2 step)+
    bernoulliThree (remainderShare (3-v) step))

private theorem ramp_sum {a step : ℝ} (ha : 0 ≤ a) (ha3 : a ≤ 3)
    (hs : 0 < step) {j : ℕ} (hj : 0 < j) :
    (∑ n ∈ Finset.range (⌊3/step⌋₊+1), ramp a ((n : ℝ)*step)^j) =
      rampPrefix j a step := by
  have hsub : Finset.range (⌊a/step⌋₊+1) ⊆ Finset.range (⌊3/step⌋₊+1) := by
    apply Finset.range_mono
    exact Nat.add_le_add_right (Nat.floor_mono (by gcongr)) 1
  have he := Finset.sum_subset hsub
    (f := fun n : ℕ => ramp a ((n : ℝ)*step)^j) (fun n _ hn => ?_)
  · rw [← he]
    unfold rampPrefix
    apply Finset.sum_congr rfl
    intro n hn
    rw [ramp_eq_sub]
    have hnf : n ≤ ⌊a/step⌋₊ := by have := Finset.mem_range.mp hn; omega
    have he := (Nat.cast_le.mpr hnf : (n : ℝ) ≤ (⌊a/step⌋₊ : ℝ)).trans
      (Nat.floor_le (show 0 ≤ a/step by positivity))
    exact (le_div_iff₀ hs).mp he
  · have hnf : ⌊a/step⌋₊+1 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    have he := (Nat.lt_floor_add_one (a/step)).trans_le
      (show (⌊a/step⌋₊ : ℝ)+1 ≤ (n : ℝ) by exact_mod_cast hnf)
    rw [ramp_eq_zero (le_of_lt ((div_lt_iff₀ hs).mp he)), zero_pow hj.ne']

/-- Exact ordinary lag quadrature. It does not yet assert the infinite
alternating lag identity at the boundary exponent. -/
theorem overlapSum_eq_small {v step : ℝ} (hv : v ∈ Icc 0 1) (hs : 0 < step) :
    overlapSum v step = smallOverlapIntegral v/step+smallOverlapError v step := by
  unfold overlapSum
  simp_rw [tent_product_small hv]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  rw [ramp_sum (by norm_num : (0 : ℝ) ≤ 1) (by norm_num) hs (by norm_num : 0 < 2),
    ramp_sum (by linarith [hv.2] : 0 ≤ 2-v) (by linarith [hv.1]) hs
      (by norm_num : 0 < 2),
    ramp_sum (by norm_num : (0 : ℝ) ≤ 2) (by norm_num) hs (by norm_num : 0 < 2),
    ramp_sum (by linarith [hv.2] : 0 ≤ 3-v) (by linarith [hv.1]) hs
      (by norm_num : 0 < 2)]
  have ho (a : ℝ) (ha : 0 ≤ a) (ha3 : a ≤ 3) :
      (∑ n ∈ Finset.range (⌊3/step⌋₊+1), ramp a ((n : ℝ)*step)) =
        rampPrefix 1 a step := by simpa using ramp_sum ha ha3 hs (by norm_num : 0 < 1)
  rw [ho 1 (by norm_num) (by norm_num),
    ho (2-v) (by linarith [hv.2]) (by linarith [hv.1]),
    ho 2 (by norm_num) (by norm_num),
    ho (3-v) (by linarith [hv.2]) (by linarith [hv.1])]
  simp_rw [rampPrefix_one hs, rampPrefix_two hs]
  unfold smallOverlapIntegral smallOverlapError
  field_simp [hs.ne']
  ring

theorem smallOverlapError_abs_le {v step : ℝ} (hv : v ∈ Icc 0 1)
    (hs : 0 < step) :
    |smallOverlapError v step| ≤ step/3+step^2 := by
  have h2 (a : ℝ) (ha : 0 ≤ a) :
      |bernoulliTwo (remainderShare a step)| ≤ 1/6 :=
    bernoulliTwo_abs_le ⟨(remainderShare_bounds ha hs).1,
      (remainderShare_bounds ha hs).2.le⟩
  have h3 (a : ℝ) (ha : 0 ≤ a) :
      |bernoulliThree (remainderShare a step)| ≤ 1/2 :=
    bernoulliThree_abs_le ⟨(remainderShare_bounds ha hs).1,
      (remainderShare_bounds ha hs).2.le⟩
  have he2 : |v*bernoulliTwo (remainderShare 1 step)-
      2*(1-v)*bernoulliTwo (remainderShare (2-v) step)-
      2*(1-v)*bernoulliTwo (remainderShare 2 step)+
      v*bernoulliTwo (remainderShare (3-v) step)| ≤ 2/3 := by
    apply ((abs_add_le _ _).trans
      (add_le_add ((abs_sub _ _).trans
        (add_le_add ((abs_sub _ _).trans (add_le_add le_rfl le_rfl)) le_rfl)) le_rfl)).trans
    simp only [abs_mul, abs_of_nonneg hv.1,
      abs_of_nonneg (show 0 ≤ 2*(1-v) by linarith [hv.2])]
    calc
      _ ≤ v*(1/6)+2*(1-v)*(1/6)+2*(1-v)*(1/6)+v*(1/6) :=
        add_le_add (add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left (h2 1 (by norm_num)) hv.1)
            (mul_le_mul_of_nonneg_left (h2 (2-v) (by linarith [hv.2]))
              (by linarith [hv.2])))
          (mul_le_mul_of_nonneg_left (h2 2 (by norm_num)) (by linarith [hv.2])))
          (mul_le_mul_of_nonneg_left (h2 (3-v) (by linarith [hv.2])) hv.1)
      _ ≤ _ := by linarith [hv.1]
  have he3 : |-bernoulliThree (remainderShare 1 step)+
      2*bernoulliThree (remainderShare (2-v) step)-
      2*bernoulliThree (remainderShare 2 step)+
      bernoulliThree (remainderShare (3-v) step)| ≤ 3 := by
    apply ((abs_add_le _ _).trans
      (add_le_add ((abs_sub _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)).trans
    simp only [abs_neg, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    exact (add_le_add (add_le_add (add_le_add
      (h3 1 (by norm_num))
      (mul_le_mul_of_nonneg_left (h3 (2-v) (by linarith [hv.2])) (by norm_num)))
      (mul_le_mul_of_nonneg_left (h3 2 (by norm_num)) (by norm_num)))
      (h3 (3-v) (by linarith [hv.2]))).trans_eq (by norm_num)

  unfold smallOverlapError
  apply (abs_sub _ _).trans
  simp only [abs_mul, abs_div, abs_neg, abs_pow, abs_of_nonneg hs.le,
    show |(2 : ℝ)| = 2 by norm_num, show |(3 : ℝ)| = 3 by norm_num]
  exact (add_le_add (mul_le_mul_of_nonneg_left he2 (by positivity))
    (mul_le_mul_of_nonneg_left he3 (by positivity))).trans_eq (by ring)

/-- The sampled overlap approaches its density with a summable
O(v/h) remainder; the outer alternating sign is not norm-paid. -/
theorem lag_overlap_error {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    {h : ℕ} (hh : 0 < h) :
    |overlapSum v (v/(h : ℝ))-(h : ℝ)/v*smallOverlapIntegral v| ≤
      2*v/(h : ℝ) := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hs : 0 < v/(h : ℝ) := by positivity
  rw [overlapSum_eq_small ⟨hv.le,hv1⟩ hs]
  have he : smallOverlapIntegral v/(v/(h : ℝ)) =
      (h : ℝ)/v*smallOverlapIntegral v := by field_simp
  rw [he, add_sub_cancel_left]
  apply (smallOverlapError_abs_le ⟨hv.le,hv1⟩ hs).trans
  have hs1 : v/(h : ℝ) ≤ 1 := by
    apply (div_le_one hh').mpr
    exact hv1.trans (by exact_mod_cast hh)
  have hsq : (v/(h : ℝ))^2 ≤ v/(h : ℝ) := by
    nlinarith [hs.le]
  rw [show 2*v/(h : ℝ) = 2*(v/(h : ℝ)) by ring]
  nlinarith

/-- The two-knot overlap on the other half of the same tent support. -/
theorem tent_product_large {v : ℝ} (hv : v ∈ Icc 1 2) (t : ℝ) :
    tent t*tent (t+v) =
      (2-v)*ramp 1 t+ramp 1 t^2+
      (2-v)*ramp (3-v) t-ramp (3-v) t^2 := by
  by_cases h1 : t ≤ 1
  · rw [tent_eq_zero_of_le h1, ramp_eq_sub h1,
      ramp_eq_sub (by linarith [hv.2] : t ≤ 3-v)]
    ring
  by_cases h2 : t ≤ 3-v
  · rw [tent_eq_left (by linarith) (by linarith [hv.1]),
      tent_eq_right (by linarith [hv.1]) (by linarith),
      ramp_eq_zero (by linarith : 1 ≤ t), ramp_eq_sub h2]
    ring
  · rw [tent_eq_zero_of_ge (by linarith : 3 ≤ t+v),
      ramp_eq_zero (by linarith : 1 ≤ t),
      ramp_eq_zero (by linarith : 3-v ≤ t)]
    ring

/-- Polynomial overlap integral for lags between one and two. -/
def largeOverlapIntegral (v : ℝ) : ℝ := (2-v)^3/6

/-- Exact Bernoulli grid correction on the large-lag branch. -/
def largeOverlapError (v step : ℝ) : ℝ :=
  -step/2*((2-v)*bernoulliTwo (remainderShare 1 step)+
    (2-v)*bernoulliTwo (remainderShare (3-v) step))-
  step^2/3*(bernoulliThree (remainderShare 1 step)-
    bernoulliThree (remainderShare (3-v) step))

theorem overlapSum_eq_large {v step : ℝ} (hv : v ∈ Icc 1 2) (hs : 0 < step) :
    overlapSum v step = largeOverlapIntegral v/step+largeOverlapError v step := by
  unfold overlapSum
  simp_rw [tent_product_large hv]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [ramp_sum (by norm_num : (0 : ℝ) ≤ 1) (by norm_num) hs (by norm_num : 0 < 2),
    ramp_sum (by linarith [hv.2] : 0 ≤ 3-v) (by linarith [hv.1]) hs
      (by norm_num : 0 < 2)]
  have ho (a : ℝ) (ha : 0 ≤ a) (ha3 : a ≤ 3) :
      (∑ n ∈ Finset.range (⌊3/step⌋₊+1), ramp a ((n : ℝ)*step)) =
        rampPrefix 1 a step := by simpa using ramp_sum ha ha3 hs (by norm_num : 0 < 1)
  rw [ho 1 (by norm_num) (by norm_num),
    ho (3-v) (by linarith [hv.2]) (by linarith [hv.1])]
  simp_rw [rampPrefix_one hs, rampPrefix_two hs]
  unfold largeOverlapIntegral largeOverlapError
  field_simp [hs.ne']
  ring

theorem largeOverlapError_abs_le {v step : ℝ} (hv : v ∈ Icc 1 2)
    (hs : 0 < step) :
    |largeOverlapError v step| ≤ step/6+step^2/3 := by
  have h2 (a : ℝ) (ha : 0 ≤ a) :
      |bernoulliTwo (remainderShare a step)| ≤ 1/6 :=
    bernoulliTwo_abs_le ⟨(remainderShare_bounds ha hs).1,
      (remainderShare_bounds ha hs).2.le⟩
  have h3 (a : ℝ) (ha : 0 ≤ a) :
      |bernoulliThree (remainderShare a step)| ≤ 1/2 :=
    bernoulliThree_abs_le ⟨(remainderShare_bounds ha hs).1,
      (remainderShare_bounds ha hs).2.le⟩
  have e2 : |(2-v)*bernoulliTwo (remainderShare 1 step)+
      (2-v)*bernoulliTwo (remainderShare (3-v) step)| ≤ 1/3 := by
    apply (abs_add_le _ _).trans
    simp only [abs_mul, abs_of_nonneg (show 0 ≤ 2-v by linarith [hv.2])]
    calc
      _ ≤ (2-v)*(1/6)+(2-v)*(1/6) := add_le_add
        (mul_le_mul_of_nonneg_left (h2 1 (by norm_num)) (by linarith [hv.2]))
        (mul_le_mul_of_nonneg_left (h2 (3-v) (by linarith [hv.2]))
          (by linarith [hv.2]))
      _ ≤ _ := by linarith [hv.1]
  have e3 : |bernoulliThree (remainderShare 1 step)-
      bernoulliThree (remainderShare (3-v) step)| ≤ 1 := by
    exact ((abs_sub _ _).trans (add_le_add (h3 1 (by norm_num))
      (h3 (3-v) (by linarith [hv.2])))).trans_eq (by norm_num)
  unfold largeOverlapError
  apply (abs_sub _ _).trans
  simp only [abs_mul, abs_div, abs_neg, abs_pow, abs_of_nonneg hs.le,
    show |(2 : ℝ)| = 2 by norm_num, show |(3 : ℝ)| = 3 by norm_num]
  exact (add_le_add (mul_le_mul_of_nonneg_left e2 (by positivity))
    (mul_le_mul_of_nonneg_left e3 (by positivity))).trans_eq (by ring)

theorem overlapSum_eq_zero {v step : ℝ} (hv : 2 ≤ v) : overlapSum v step = 0 := by
  apply Finset.sum_eq_zero
  intro n _
  by_cases ht : (n : ℝ)*step ≤ 1
  · rw [tent_eq_zero_of_le ht, zero_mul]
  · rw [tent_eq_zero_of_ge (by linarith : 3 ≤ (n : ℝ)*step+v), mul_zero]

/-- Piecewise polynomial autocorrelation of the original tent. -/
def overlapIntegral (v : ℝ) : ℝ :=
  if v ≤ 1 then smallOverlapIntegral v else if v ≤ 2 then largeOverlapIntegral v else 0

/-- Difference between the literal lag grid and its overlap integral. -/
def lagRemainder (v : ℝ) (h : ℕ) : ℝ :=
  overlapSum v (v/(h : ℝ))-(h : ℝ)/v*overlapIntegral v

/-- The complete positive lag range has an absolutely summable
quadrature remainder. This includes the support endpoint v=2. -/
theorem lagRemainder_abs_le {v : ℝ} (hv : 0 < v) {h : ℕ} (hh : 0 < h) :
    |lagRemainder v h| ≤ 2*v/(h : ℝ) := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  unfold lagRemainder overlapIntegral
  split_ifs with hv1 hv2
  · exact lag_overlap_error hv hv1 hh
  · have he : largeOverlapIntegral v/(v/(h : ℝ)) =
        (h : ℝ)/v*largeOverlapIntegral v := by field_simp
    rw [overlapSum_eq_large ⟨by linarith,hv2⟩ (by positivity), he,
      add_sub_cancel_left]
    apply (largeOverlapError_abs_le ⟨by linarith,hv2⟩ (by positivity)).trans
    have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have hb : v/(h : ℝ) ≤ 2 := (div_le_iff₀ hh').mpr (by nlinarith)
    have hn : 0 ≤ v/(h : ℝ) := by positivity
    have hs : (v/(h : ℝ))^2 ≤ 2*(v/(h : ℝ)) := by nlinarith
    rw [show 2*v/(h : ℝ) = 2*(v/(h : ℝ)) by ring]
    nlinarith
  · rw [overlapSum_eq_zero (by linarith), mul_zero, sub_self, abs_zero]
    positivity

end
end RiemannGaussian.SuzukiCarryPhaseQuadrature
