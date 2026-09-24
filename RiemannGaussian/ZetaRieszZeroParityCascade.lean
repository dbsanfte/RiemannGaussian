/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszContinuumCascade
import RiemannGaussian.ZetaRieszFullParityPacket
import RiemannGaussian.ZetaRieszRectanglePhase

/-!
# The simple-zero parity cascade and its support gap

The largest prime supplies one additional negative phase. This changes the
nonempty count transform to `(1-exp(-J))/z^2`. At zero cutoff its inverse
representative is the indicator of `s <= d`, rather than a constant.
These are exact continuum and support identities; a masked arithmetic
prime-product replacement is a separate obligation.
-/

namespace RiemannGaussian.ZetaRieszZeroParityCascade
noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators Classical
open ZetaRieszContinuumCascade ZetaRieszParityPacket ZetaRieszMatchedMiddle

/-- One phase for the largest prime and one for every cofactor prime. -/
def parityCountTransform (r : ℝ) (k : ℕ) (w z : ℝ) : ℂ :=
  (-1 : ℂ)^(k+1)*countTransform r k w z

/-- All nonempty cofactor counts with their simple-zero phases retained. -/
def parityTransform (r w z : ℝ) : ℂ :=
  ∑' k : ℕ, parityCountTransform r (k+1) w z

/-- The sign follows from the extra largest-prime leg, not from an
alteration of the signed Riesz coefficient. -/
theorem parityCountTransform_eq {r w z : ℝ} (hr : 0 ≤ r) (hz : 0 < z) (k : ℕ) :
    parityCountTransform r k w z =
      -(-(primeIntegral r w z : ℂ))^k/((k.factorial : ℂ)*(z : ℂ)^2) := by
  rw [parityCountTransform, countTransform_eq hr hz, pow_succ, neg_pow]
  ring

/-- An actual convergent count sum; the empty-cofactor term is removed. -/
theorem hasSum_parityCountTransform {r w z : ℝ} (hr : 0 ≤ r) (hz : 0 < z) :
    HasSum (fun k : ℕ => parityCountTransform r (k+1) w z)
      ((1-Complex.exp (-(primeIntegral r w z : ℂ)))/(z : ℂ)^2) := by
  have he : HasSum (fun k : ℕ => (-(primeIntegral r w z : ℂ))^k/(k.factorial : ℂ))
      (Complex.exp (-(primeIntegral r w z : ℂ))) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have ht := (hasSum_nat_add_iff' 1).mpr he
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at ht
  simpa only [parityCountTransform_eq hr hz, div_div, neg_div, neg_sub] using
    ht.neg.div_const ((z : ℂ)^2)

theorem parityTransform_eq {r w z : ℝ} (hr : 0 ≤ r) (hz : 0 < z) :
    parityTransform r w z = (1-Complex.exp (-(primeIntegral r w z : ℂ)))/(z : ℂ)^2 :=
  (hasSum_parityCountTransform hr hz).tsum_eq

/-- The signed, evaluated count series is absolutely summable. -/
theorem summable_norm_parityCountTransform {r w z : ℝ} (hr : 0 ≤ r) (hz : 0 < z) :
    Summable (fun k : ℕ => ‖parityCountTransform r (k+1) w z‖) :=
  (hasSum_parityCountTransform hr hz).summable.norm

/-- The simple-zero parity gives the lower-triangular support transform. -/
theorem parityTransform_zero {w z : ℝ} (hw : 0 < w) (hz : 0 < z) :
    parityTransform 0 w z = 1/((z : ℂ)*((w : ℂ)+z)) := by
  rw [parityTransform_eq (by norm_num) hz, primeIntegral, integral_primeFactor hw hz.le,
    Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log (div_pos (by linarith) hw)]
  push_cast
  have hwc : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  have hzc : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hwzc : (w : ℂ)+z ≠ 0 := by
    exact_mod_cast (show w+z ≠ 0 by linarith)
  field_simp
  ring

/-- The diagonal value is immaterial to the Laplace transform. We use
the closed support requested for the inverse representative. -/
def supportKernel (s d : ℝ) : ℝ := if s ≤ d then 1 else 0

theorem supportKernel_eq_zero {s d : ℝ} (h : d < s) : supportKernel s d = 0 :=
  if_neg (not_le.mpr h)

theorem integral_supportKernel {s z : ℝ} (hs : 0 < s) (hz : 0 < z) :
    (∫ d : ℝ in Ioi 0, Complex.exp (-(z : ℂ)*d)*(supportKernel s d : ℝ)) =
      Complex.exp (-(z : ℂ)*s)/(z : ℂ) := by
  have he (d : ℝ) : Complex.exp (-(z : ℂ)*d)*(supportKernel s d : ℝ) =
      (Ici s).indicator (fun d : ℝ => Complex.exp (-(z : ℂ)*d)) d := by
    by_cases hd : s ≤ d <;> simp [supportKernel, hd]
  simp_rw [he]
  rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    show Ici s ∩ Ioi (0 : ℝ) = Ici s from inter_eq_left.mpr (fun _ h => hs.trans_le h),
    integral_Ici_eq_integral_Ioi,
    integral_exp_mul_complex_Ioi (by simpa using (neg_neg_of_pos hz))]
  simp

/-- A direct transform verification of the inverse representative,
without inferring a pointwise count-sum identity from injectivity. -/
theorem supportKernel_transform {w z : ℝ} (hw : 0 < w) (hz : 0 < z) :
    (∫ s : ℝ in Ioi 0, Complex.exp (-(w : ℂ)*s)*
      (∫ d : ℝ in Ioi 0, Complex.exp (-(z : ℂ)*d)*(supportKernel s d : ℝ))) =
        parityTransform 0 w z := by
  have he : (fun s : ℝ => Complex.exp (-(w : ℂ)*s)*
      (∫ d : ℝ in Ioi 0, Complex.exp (-(z : ℂ)*d)*(supportKernel s d : ℝ))) =ᵐ[volume.restrict (Ioi 0)]
      (fun s : ℝ => Complex.exp (-((w : ℂ)+z)*s)/(z : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [integral_supportKernel hs hz, ← mul_div_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [integral_congr_ae he, integral_div,
    integral_exp_mul_complex_Ioi (by simp; linarith), parityTransform_zero hw hz]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_div, neg_neg]
  rw [div_div, mul_comm]

/-- An exact uniform support gap for the literal floor-defined length.
The bound implies that ten omitted shares <=7/250 cannot reach the diagonal. -/
theorem core_support_gap {u : ℝ} (hu : 1/2 ≤ u) {N K n : ℕ}
    (hN : 2 ≤ N) (hn : n ∈ coreBand u N K) :
    7/25 < 1-SquarefreeVaughanLogSource.length u N/Real.log n := by
  have hnlo := (Finset.mem_filter.mp hn).2.1
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log n := by linarith
  have hL := ZetaRieszHeadOrders.length_le_two_log_two hu hN
  have htwo : 2*Real.log 2 ≤ (7/5 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hlength : SquarefreeVaughanLogSource.length u N ≤ (7/5 : ℝ)*N :=
    hL.trans (mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg _))
  have hh : SquarefreeVaughanLogSource.length u N/Real.log n < (18/25 : ℝ) := by
    apply (div_lt_iff₀ hlog).mpr
    linarith
  linarith

/-- The zero-cutoff inverse representative vanishes throughout the
actual core packet, with its moving length and any largest-prime share. -/
theorem supportKernel_core {u : ℝ} (hu : 1/2 ≤ u) {N K n : ℕ}
    (hN : 2 ≤ N) (hn : n ∈ coreBand u N K) (p : ℝ) :
    supportKernel (1-p) (SquarefreeVaughanLogSource.length u N/Real.log n-p) = 0 := by
  apply supportKernel_eq_zero
  linarith [core_support_gap hu hN hn]

/-- The existing actual finite-prime theorem supplies one negative sign
on each leg when every individual order satisfies its proved range. -/
theorem simple_zero_product_phase (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (huU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hsimple : analyticZetaZeroMultiplicity rho = 1)
    (k : ℕ) (orders : Fin (k+1) → ℕ → ℕ)
    (horders : ∀ i, ∀ᶠ N : ℕ in atTop,
      N ≤ 100*orders i N ∧ 40*orders i N ≤ 27*N) :
    Tendsto (fun N => ∏ i, weightedFinite (3/2-rho.1.re) rho.1.im N (orders i N))
      atTop (𝓝 ((-1 : ℂ)^(k+1))) := by
  have hi (i : Fin (k+1)) := ZetaRieszSkewAllocation.tendsto_rectangle_weighted_finite
    rho hrho hexposed huU (orders i) (horders i)
  simp only [hsimple, Nat.cast_one] at hi
  simpa using tendsto_finsetProd Finset.univ (fun i _ => hi i)

/-- The exact cutoff defect keeps the empty-cofactor boundary term.
This is the renewal for the parity-weighted transform. -/
theorem parityTransform_cutoff_renewal {a b w z : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hw : 0 < w) (hz : 0 < z) :
    parityTransform b w z-parityTransform a w z =
      (Complex.exp ((∫ x in a..b, primeFactor w z x) : ℝ)-1)*
        (parityTransform a w z-1/(z : ℂ)^2) := by
  have hi := intervalIntegral.integral_Ioi_sub_Ioi
    ((integrable_primeFactor hw hz.le).mono_set (Ioi_subset_Ioi ha)) hab
  have hj : -(primeIntegral b w z) = -(primeIntegral a w z)+
      ∫ x in a..b, primeFactor w z x := by
    unfold primeIntegral
    linarith [hi]
  rw [parityTransform_eq (ha.trans hab) hz, parityTransform_eq ha hz,
    ← Complex.ofReal_neg, hj, Complex.ofReal_add, Complex.ofReal_neg, Complex.exp_add]
  ring

/-- Applying the omitted-prime differences to the supported inverse
kernel, retaining every subset sign and the shift of the total log. -/
def insertedSupport {ι : Type*} (S : Finset ι) (x : ι → ℝ) (s d : ℝ) : ℝ :=
  ∑ A ∈ S.powerset, (-1 : ℝ)^A.card*
    supportKernel (s-∑ i ∈ S, x i) (d-∑ i ∈ A, x i)

/-- No insertion contribution reaches the support before its total
omitted log mass reaches the diagonal gap. -/
theorem insertedSupport_eq_zero {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) {s d : ℝ}
    (hgap : ∑ i ∈ S, x i < s-d) : insertedSupport S x s d = 0 := by
  apply Finset.sum_eq_zero
  intro A hA
  have hnonneg : 0 ≤ ∑ i ∈ A, x i := Finset.sum_nonneg
    (fun i hi => hx i (Finset.mem_powerset.mp hA hi))
  rw [supportKernel_eq_zero (by linarith), mul_zero]

/-- A finite, literal support test: up to ten omitted shares cannot
reach the nonzero inverse kernel anywhere in the selected core. -/
theorem ten_insertions_vanish {u : ℝ} (hu : 1/2 ≤ u) {N K n : ℕ}
    (hN : 2 ≤ N) (hn : n ∈ coreBand u N K)
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i ∧ x i ≤ 7/250) (hc : S.card ≤ 10) (p : ℝ) :
    insertedSupport S x (1-p) (SquarefreeVaughanLogSource.length u N/Real.log n-p) = 0 := by
  apply insertedSupport_eq_zero S x (fun i hi => (hx i hi).1)
  have hs := Finset.sum_le_sum (fun i hi => (hx i hi).2)
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hcr : (S.card : ℝ) ≤ 10 := by exact_mod_cast hc
  linarith [core_support_gap hu hN hn]

/-- Any nonzero insertion in this core requires at least eleven
omitted small primes. No bound for the remaining insertion tail is asserted. -/
theorem nonzero_insertion_count {u : ℝ} (hu : 1/2 ≤ u) {N K n : ℕ}
    (hN : 2 ≤ N) (hn : n ∈ coreBand u N K)
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i ∧ x i ≤ 7/250) (p : ℝ)
    (hne : insertedSupport S x (1-p)
      (SquarefreeVaughanLogSource.length u N/Real.log n-p) ≠ 0) : 11 ≤ S.card := by
  by_contra h
  exact hne (ten_insertions_vanish hu hN hn S x hx (by omega) p)

end
end RiemannGaussian.ZetaRieszZeroParityCascade
