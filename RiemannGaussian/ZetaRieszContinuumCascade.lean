/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldPrimeKernel
import RiemannGaussian.ZetaRieszFixedCofactor
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The exact all-count continuum Riesz functional

The finite-difference kernel retains every subset sign. Its Laplace
transform is evaluated before summing over counts. All counts are
included with their factorial symmetry factors; the empty cofactor is
excluded explicitly. These continuum identities do not supply a bound
for the discrete arithmetic carrier.
-/

namespace RiemannGaussian.ZetaRieszContinuumCascade
noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators Classical

/-- The exact signed Riesz difference over a finite set of log coordinates. -/
def kernel {ι : Type*} (S : Finset ι) (x : ι → ℝ) (d : ℝ) : ℝ :=
  ∑ A ∈ S.powerset, (-1 : ℝ)^A.card * max 0 (d-∑ i ∈ A, x i)

/-- Prime insertion is exactly one cutoff difference, with its sign retained. -/
theorem kernel_insert {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → ℝ) (d : ℝ)
    {i : ι} (hi : i ∉ S) :
    kernel (insert i S) x d = kernel S x d-kernel S x (d-x i) := by
  unfold kernel
  rw [Finset.sum_powerset_insert hi]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  have hiA : i ∉ A := fun h => hi (Finset.mem_powerset.mp hA h)
  rw [Finset.card_insert_of_notMem hiA, Finset.sum_insert hiA, pow_succ]
  have he : d-(x i+∑ j ∈ A, x j) = d-x i-∑ j ∈ A, x j := by ring
  rw [he]
  ring

private theorem kernel_singleton {ι : Type*} [DecidableEq ι] (i : ι) (x : ι → ℝ) (d : ℝ) :
    kernel {i} x d = max 0 d-max 0 (d-x i) := by
  simpa [kernel] using kernel_insert (∅ : Finset ι) x d (i := i) (by simp)

/-- The two-cofactor-prime section of the first variation has exact
unit response after dividing by the small-prime density denominator. -/
theorem kernel_pair (x r d : ℝ) (hr : 0 ≤ r) (hrd : r ≤ d) (hdx : d ≤ x) :
    kernel (Finset.univ : Finset (Fin 2)) ![x,r] d = r := by
  have h1 : 0 ≤ d := hr.trans hrd
  have h2 : 0 ≤ d-r := sub_nonneg.mpr hrd
  have h3 : d-x ≤ 0 := sub_nonpos.mpr hdx
  have h4 : d-x-r ≤ 0 := by linarith
  rw [show (Finset.univ : Finset (Fin 2)) = insert 0 {1} by decide,
    kernel_insert _ _ _ (by decide), kernel_singleton, kernel_singleton]
  norm_num [max_eq_right h1, max_eq_right h2, max_eq_left h3, max_eq_left h4]

/-- If the residual cofactor log is below twice its least-prime cutoff,
no two-or-more-prime count can enter that section of a first variation. -/
theorem small_cofactor_count_le_one {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {r : ℝ} (hr : 0 < r) (hx : ∀ i ∈ S, r ≤ x i)
    (hs : ∑ i ∈ S, x i < 2*r) : S.card ≤ 1 := by
  have hh := Finset.sum_le_sum hx
  simp only [Finset.sum_const, nsmul_eq_mul] at hh
  by_contra hc
  have hcR : (2 : ℝ) ≤ S.card := by exact_mod_cast (by omega : 2 ≤ S.card)
  nlinarith

/-- A whole rational interior strip retains this response: deleting the
middle-prime leg leaves room for exactly one prime, so no higher count
can cancel that same first-variation fibre. This is a kernel/support
identity, not a bound or sign assertion for the actual prime discrepancy. -/
theorem interior_variation_fibre {p v d : ℝ}
    (hp : p ≤ 9/16) (hv0 : 9/500 ≤ v) (hv1 : v ≤ 11/500)
    (hd0 : 3/25 ≤ d) (hd1 : d ≤ 4/25) :
    kernel (Finset.univ : Finset (Fin 2)) ![1-p-v,v] d/v = 1 ∧
      ∀ (ι : Type) (S : Finset ι) (x : ι → ℝ),
        (∀ i ∈ S, (3/250 : ℝ) ≤ x i) → (∑ i ∈ S, x i) = v → S.card = 1 := by
  have hv : 0 < v := by linarith
  constructor
  · rw [kernel_pair _ _ _ hv.le (by linarith) (by linarith), div_self hv.ne']
  · intro ι S x hx hs
    have hc := small_cofactor_count_le_one S x (by norm_num : (0 : ℝ) < 3/250)
      hx (by rw [hs]; linarith)
    have hn : S.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hs
      linarith
    have hpos := Finset.card_pos.mpr hn
    omega

/-- The continuum subset kernel has precisely the repository's literal
Möbius/Riesz normalization on every squarefree prime product. -/
theorem kernel_eq_riesz_prime_product (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (d : ℝ) :
    kernel S (fun p => Real.log p) d = VaughanLogAverage.riesz d (∏ p ∈ S, p) := by
  induction S using Finset.induction_on generalizing d with
  | empty => simp [kernel, VaughanLogAverage.riesz]
  | @insert p S hp ih =>
      have hprime := hS p (Finset.mem_insert_self _ _)
      have hn : ¬p ∣ ∏ q ∈ S, q := by
        intro h
        obtain ⟨q, hq, hpq⟩ := (hprime.prime.dvd_finsetProd_iff _).mp h
        have hqprime := hS q (Finset.mem_insert_of_mem hq)
        have he : q = p := (hqprime.dvd_iff_eq hprime.ne_one).mp hpq
        exact hp (he ▸ hq)
      calc
        _ = kernel S (fun q : ℕ => Real.log q) d -
            kernel S (fun q : ℕ => Real.log q) (d-Real.log p) := kernel_insert S _ d hp
        _ = _ := by
          rw [Finset.prod_insert hp, ZetaSquarefreeRieszWindows.riesz_prime_mul d hprime hn,
            ih (fun q hq => hS q (Finset.mem_insert_of_mem hq)),
            ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))]

theorem kernel_primeFactors {a : ℕ} (ha : Squarefree a) (d : ℝ) :
    kernel a.primeFactors (fun p => Real.log p) d = VaughanLogAverage.riesz d a := by
  rw [kernel_eq_riesz_prime_product _ (fun p hp => Nat.prime_of_mem_primeFactors hp),
    Nat.prod_primeFactors_of_squarefree ha]

/-- Exact arithmetic orientation on a saturated largest-prime fibre.
The cofactor kernel occurs with a PLUS sign in the repository coefficient. -/
theorem coefficient_saturated_prime {p a : ℕ} (hp : p.Prime) (hpa : ¬p ∣ a)
    (ha : Squarefree a) (ha1 : a ≠ 1) (hap : ¬a.Prime)
    (hn : Squarefree (p*a) ∧ ¬(p*a).Prime) {L : ℝ} (hL : Real.log a ≤ L) :
    SquarefreeVaughanLogSource.coefficient L (p*a) =
      ((Real.log (p*a : ℕ)/L *
        kernel a.primeFactors (fun q => Real.log q) (L-Real.log p) : ℝ) : ℂ) := by
  rw [SquarefreeVaughanLogSource.coefficient, if_pos hn,
    ZetaSquarefreeRieszWindows.riesz_prime_mul L hp hpa,
    ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated ha ha1 hap hL,
    kernel_primeFactors ha]
  push_cast
  ring

/-- The absolutely integrable one-prime factor in the double transform. -/
def primeFactor (w z x : ℝ) : ℝ :=
  x⁻¹*(Real.exp (-(w*x))-Real.exp (-((w+z)*x)))

theorem primeFactor_bounds {w z x : ℝ} (hz : 0 ≤ z) (hx : 0 < x) :
    0 ≤ primeFactor w z x ∧ primeFactor w z x ≤ z*Real.exp (-(w*x)) := by
  have he : Real.exp (-((w+z)*x)) = Real.exp (-(w*x))*Real.exp (-(z*x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hzexp : Real.exp (-(z*x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  unfold primeFactor
  rw [he]
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hx.le) (by nlinarith [Real.exp_pos (-(w*x))])
  · apply (mul_le_mul_iff_right₀ hx).mp
    field_simp
    linarith [Real.add_one_le_exp (-(x*z))]

theorem integrable_primeFactor {w z : ℝ} (hw : 0 < w) (hz : 0 ≤ z) :
    IntegrableOn (primeFactor w z) (Ioi 0) := by
  have hh := integrableOn_exp_mul_Ioi (a := -w) (by linarith) 0
  have he : IntegrableOn (fun x : ℝ => z*Real.exp (-(w*x))) (Ioi 0) := by
    simpa only [IntegrableOn, neg_mul] using hh.const_mul z
  apply he.mono' (by unfold primeFactor; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hb := primeFactor_bounds (w := w) hz hx
  simpa only [Real.norm_of_nonneg hb.1] using hb.2

/-- Frullani's integral with genuine absolute integrability, rather than
an assumed improper-integral convention. -/
theorem integral_primeFactor {w z : ℝ} (hw : 0 < w) (hz : 0 ≤ z) :
    (∫ x in Ioi 0, primeFactor w z x) = Real.log ((w+z)/w) := by
  have hf : LocallyIntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) :=
    (Real.continuous_exp.comp continuous_neg).continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hzero : Tendsto (fun x : ℝ => Real.exp (-x)) (𝓝[>] 0) (𝓝 1) := by
    have hc := (Real.continuous_exp.comp continuous_neg).continuousAt.continuousWithinAt
      (s := Ioi (0 : ℝ)) (x := 0)
    simpa only [ContinuousWithinAt, Function.comp_def, neg_zero, Real.exp_zero] using hc
  simpa only [primeFactor, smul_eq_mul, sub_zero, mul_one] using
    Frullani.integral_Ioi_eq hf hw (by linarith : 0 < w+z) hzero
      Real.tendsto_exp_neg_atTop_nhds_zero (integrable_primeFactor hw hz)

private theorem integrable_max_hinge {z : ℂ} (hz : 0 < z.re) {b : ℝ} (hb : 0 ≤ b) :
    IntegrableOn (fun d : ℝ => Complex.exp (-z*d)*(max 0 (d-b) : ℝ)) (Ioi 0) := by
  apply (RosserSchoenfeldPrimeKernel.integrable_time_exponential hz).norm.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with d hd
  have hd0 : 0 < d := hd
  have hmax : max 0 (d-b) ≤ d := max_le hd0.le (by linarith)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_max_left _ _),
    norm_mul, Complex.norm_real, Real.norm_of_nonneg hd0.le]
  nlinarith [norm_nonneg (Complex.exp (-z*d))]

private theorem integral_max_hinge {z : ℂ} (hz : 0 < z.re) {b : ℝ} (hb : 0 ≤ b) :
    (∫ d : ℝ in Ioi 0, Complex.exp (-z*d)*(max 0 (d-b) : ℝ)) =
      Complex.exp (-z*b)/z^2 := by
  have he (d : ℝ) : Complex.exp (-z*d)*(max 0 (d-b) : ℝ) =
      (Ioi b).indicator (fun t : ℝ => Complex.exp (-z*t)*((t-b : ℝ) : ℂ)) d := by
    by_cases hd : b < d
    · simp [hd, max_eq_right (by linarith : 0 ≤ d-b)]
    · simp [hd, max_eq_left (by linarith : d-b ≤ 0)]
  simp_rw [he]
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  rw [show Ioi b ∩ Ioi (0 : ℝ) = Ioi b from inter_eq_left.mpr (Ioi_subset_Ioi hb)]
  exact RosserSchoenfeldPrimeKernel.integral_hinge hz hb

/-- Exact Laplace transform of the entire finite signed kernel. No
absolute values are inserted into the subset sum. -/
theorem integral_kernel {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) {z : ℂ} (hz : 0 < z.re) :
    (∫ d : ℝ in Ioi 0, Complex.exp (-z*d)*(kernel S x d : ℝ)) =
      (∏ i ∈ S, (1-Complex.exp (-z*x i)))/z^2 := by
  have hb (A : Finset ι) (hA : A ∈ S.powerset) : 0 ≤ ∑ i ∈ A, x i :=
    Finset.sum_nonneg (fun i hi => hx i (Finset.mem_powerset.mp hA hi))
  have he (d : ℝ) : Complex.exp (-z*d)*(kernel S x d : ℝ) =
      ∑ A ∈ S.powerset, (-1 : ℂ)^A.card *
        (Complex.exp (-z*d)*(max 0 (d-∑ i ∈ A, x i) : ℝ)) := by
    unfold kernel
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun A hA => (integrable_max_hinge hz (hb A hA)).const_mul _)]
  simp_rw [integral_const_mul]
  have hval : (∑ A ∈ S.powerset, (-1 : ℂ)^A.card *
        (∫ d : ℝ in Ioi 0, Complex.exp (-z*d)*(max 0 (d-∑ i ∈ A, x i) : ℝ))) =
      ∑ A ∈ S.powerset, (-1 : ℂ)^A.card * Complex.exp (-z*(∑ i ∈ A, x i : ℝ))/z^2 := by
    apply Finset.sum_congr rfl
    intro A hA
    rw [integral_max_hinge hz (hb A hA)]
    ring
  rw [hval, ← Finset.sum_div]
  congr 1
  have hp := Finset.prod_sub (fun _ : ι => (1 : ℂ)) (fun i => Complex.exp (-z*x i)) S
  simp only [Finset.prod_const_one, mul_one] at hp
  rw [hp]
  apply Finset.sum_congr rfl
  intro A _
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

/-- The cutoff one-prime integral in the all-count transform. -/
def primeIntegral (r w z : ℝ) : ℝ := ∫ x in Ioi r, primeFactor w z x

/-- The actual iterated double-Laplace functional at cofactor count k.
The integration over total log s is performed by s=sum(x); the remaining
integral is over d. The factorial is the symmetry factor, not a parity cut. -/
def countTransform (r : ℝ) (k : ℕ) (w z : ℝ) : ℂ :=
  ((k.factorial : ℂ)⁻¹) * ∫ x : (Fin k → ℝ),
      ((∏ i, (x i : ℂ)⁻¹) * Complex.exp (-(w : ℂ)*(∑ i, x i : ℝ)) *
        ∫ d : ℝ in Ioi 0, Complex.exp (-(z : ℂ)*d)*(kernel Finset.univ x d : ℝ))
      ∂Measure.pi (fun _ => volume.restrict (Ioi r))

private theorem primeFactor_complex (w z x : ℝ) :
    (primeFactor w z x : ℂ) =
      (x : ℂ)⁻¹*Complex.exp (-(w : ℂ)*x)*(1-Complex.exp (-(z : ℂ)*x)) := by
  have he : Real.exp (-((w+z)*x)) = Real.exp (-(w*x))*Real.exp (-(z*x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold primeFactor
  rw [he]
  push_cast
  ring_nf

private theorem count_integrand_ae {r w z : ℝ} (hr : 0 ≤ r) (hz : 0 < z) (k : ℕ) :
    ∀ᵐ x : Fin k → ℝ ∂Measure.pi (fun _ => volume.restrict (Ioi r)),
      (∏ i, (x i : ℂ)⁻¹) * Complex.exp (-(w : ℂ)*(∑ i, x i : ℝ)) *
        (∫ d : ℝ in Ioi 0, Complex.exp (-(z : ℂ)*d)*(kernel Finset.univ x d : ℝ)) =
      (∏ i, (primeFactor w z (x i) : ℂ))/(z : ℂ)^2 := by
  have hx : ∀ᵐ x : Fin k → ℝ ∂Measure.pi (fun _ => volume.restrict (Ioi r)),
      ∀ i, 0 ≤ x i := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [(Measure.tendsto_eval_ae_ae (i := i)).eventually
      (ae_restrict_mem measurableSet_Ioi)] with x hx
    exact hr.trans hx.le
  filter_upwards [hx] with x hx
  rw [integral_kernel _ x (fun i _ => hx i) (by simpa using hz)]
  simp_rw [primeFactor_complex]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have he : (∏ i, Complex.exp (-(w : ℂ)*x i)) =
      Complex.exp (-(w : ℂ)*(∑ i, x i : ℝ)) := by
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum]
  rw [he]
  ring

/-- The outer integral is genuinely integrable on the Laplace domain,
after evaluating the signed inner cutoff integral. -/
theorem integrable_countTransform_integrand {r w z : ℝ}
    (hr : 0 ≤ r) (hw : 0 < w) (hz : 0 < z) (k : ℕ) :
    Integrable (fun x : Fin k → ℝ =>
      (∏ i, (x i : ℂ)⁻¹) * Complex.exp (-(w : ℂ)*(∑ i, x i : ℝ)) *
        (∫ d : ℝ in Ioi 0, Complex.exp (-(z : ℂ)*d)*(kernel Finset.univ x d : ℝ)))
      (Measure.pi (fun _ => volume.restrict (Ioi r))) := by
  have hf := ((integrable_primeFactor hw hz.le).mono_set (Ioi_subset_Ioi hr)).ofReal (𝕜 := ℂ)
  have hp := Integrable.fintype_prod (fun _ : Fin k => hf)
  apply (hp.div_const ((z : ℂ)^2)).congr
  filter_upwards [count_integrand_ae (w := w) hr hz k] with x hx
  exact hx.symm

/-- Every fixed count factors exactly, after the signed Riesz transform
has been evaluated. No norm is taken over the count or subset labels. -/
theorem countTransform_eq {r w z : ℝ} (hr : 0 ≤ r) (hz : 0 < z) (k : ℕ) :
    countTransform r k w z = (primeIntegral r w z : ℂ)^k / ((k.factorial : ℂ)*(z : ℂ)^2) := by
  unfold countTransform
  have hp := integral_fintype_prod_eq_pow (ι := Fin k)
    (μ := volume.restrict (Ioi r)) (fun x : ℝ => (primeFactor w z x : ℂ))
  rw [integral_congr_ae (count_integrand_ae hr hz k), integral_div, hp]
  rw [integral_complex_ofReal]
  change (k.factorial : ℂ)⁻¹*((primeIntegral r w z : ℂ)^Fintype.card (Fin k)/(z : ℂ)^2) = _
  simp only [Fintype.card_fin]
  ring

/-- The continuum cascade includes every nonempty prime count. The
omitted empty-cofactor atom would contribute 1/z^2 to this transform. -/
def cascadeTransform (r w z : ℝ) : ℂ := ∑' k : ℕ, countTransform r (k+1) w z

/-- The nonempty exponential formula is an actual convergent count sum.
The minus one removes precisely the empty-cofactor boundary atom. -/
theorem hasSum_countTransform {r w z : ℝ} (hr : 0 ≤ r) (hz : 0 < z) :
    HasSum (fun k : ℕ => countTransform r (k+1) w z)
      ((Complex.exp (primeIntegral r w z)-1)/(z : ℂ)^2) := by
  have he : HasSum (fun k : ℕ => (primeIntegral r w z : ℂ)^k/(k.factorial : ℂ))
      (Complex.exp (primeIntegral r w z)) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have ht := (hasSum_nat_add_iff' 1).mpr he
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at ht
  simpa only [countTransform_eq hr hz, div_div] using ht.div_const ((z : ℂ)^2)

theorem cascadeTransform_eq {r w z : ℝ} (hr : 0 ≤ r) (hz : 0 < z) :
    cascadeTransform r w z = (Complex.exp (primeIntegral r w z)-1)/(z : ℂ)^2 :=
  (hasSum_countTransform hr hz).tsum_eq

/-- The evaluated count transforms are absolutely summable, with no
finite prime-count truncation hidden in the exponential formula. -/
theorem summable_norm_countTransform {r w z : ℝ} (hr : 0 ≤ r) (hz : 0 < z) :
    Summable (fun k : ℕ => ‖countTransform r (k+1) w z‖) :=
  (hasSum_countTransform hr hz).summable.norm

/-- The exact double-Laplace normalization of the unrestricted cascade.
This is the transform of the constant one on positive total log and cutoff.
It is a continuum identity, not a discrete carrier estimate. -/
theorem cascadeTransform_zero {w z : ℝ} (hw : 0 < w) (hz : 0 < z) :
    cascadeTransform 0 w z = 1/((w : ℂ)*(z : ℂ)) := by
  rw [cascadeTransform_eq (by norm_num) hz, primeIntegral, integral_primeFactor hw hz.le,
    ← Complex.ofReal_exp, Real.exp_log (div_pos (by linarith) hw)]
  push_cast
  have hwc : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  have hzc : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  field_simp
  ring

/-- Integrated cutoff renewal with its empty-cofactor boundary source
retained. Dropping `1/z^2` would be an incorrect global renewal equation. -/
theorem cascadeTransform_cutoff_renewal {a b w z : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hw : 0 < w) (hz : 0 < z) :
    cascadeTransform a w z-cascadeTransform b w z =
      (Complex.exp ((∫ x in a..b, primeFactor w z x) : ℝ)-1)*
        (cascadeTransform b w z+1/(z : ℂ)^2) := by
  have hi := intervalIntegral.integral_Ioi_sub_Ioi
    ((integrable_primeFactor hw hz.le).mono_set (Ioi_subset_Ioi ha)) hab
  have hj : primeIntegral a w z = primeIntegral b w z+
      ∫ x in a..b, primeFactor w z x := by
    unfold primeIntegral
    linarith [hi]
  rw [cascadeTransform_eq ha hz, cascadeTransform_eq (ha.trans hab) hz, hj,
    Complex.ofReal_add, Complex.exp_add]
  ring

theorem hasDerivAt_primeIntegral {r w z : ℝ} (hr : 0 < r) (hw : 0 < w) (hz : 0 ≤ z) :
    HasDerivAt (fun a => primeIntegral a w z) (-primeFactor w z r) r := by
  have hi := integrable_primeFactor hw hz
  have hint : IntervalIntegrable (primeFactor w z) volume 0 r :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).mpr (hi.mono_set Ioc_subset_Ioi_self)
  have hc (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : ContinuousAt (primeFactor w z) x := by
    have hx0 : x ≠ 0 := hx.ne'
    unfold primeFactor
    fun_prop
  have hd := intervalIntegral.integral_hasDerivAt_right hint
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi hc r hr) (hc r hr)
  have hh := hd.const_sub (primeIntegral 0 w z)
  apply hh.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hr] with a ha
  have he := intervalIntegral.integral_Ioi_sub_Ioi hi ha.le
  change primeIntegral a w z = primeIntegral 0 w z-∫ x in 0..a, primeFactor w z x
  unfold primeIntegral
  linarith [he]

/-- Differential cutoff renewal in transform form, including the source
from inserting the first cofactor prime. -/
theorem hasDerivAt_cascadeTransform {r w z : ℝ} (hr : 0 < r) (hw : 0 < w) (hz : 0 < z) :
    HasDerivAt (fun a => cascadeTransform a w z)
      (-(primeFactor w z r : ℂ)*(cascadeTransform r w z+1/(z : ℂ)^2)) r := by
  have hd := (((hasDerivAt_primeIntegral hr hw hz.le).ofReal_comp.cexp).sub_const 1).div_const
    ((z : ℂ)^2)
  have hh : HasDerivAt (fun a : ℝ => (Complex.exp (primeIntegral a w z)-1)/(z : ℂ)^2)
      (-(primeFactor w z r : ℂ)*(cascadeTransform r w z+1/(z : ℂ)^2)) r := by
    apply hd.congr_deriv
    rw [cascadeTransform_eq hr.le hz, Complex.ofReal_neg]
    ring
  apply hh.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hr] with a ha
  exact cascadeTransform_eq ha.le hz

/-- All-count cancellation does not annihilate an arbitrary perturbation
of the prime measure. This is the exact first variation of the already
summed exponential formula at the zero-cutoff continuous prime density. -/
theorem zero_cutoff_prime_variation {w z : ℝ} (hw : 0 < w) (hz : 0 < z) (h : ℂ) :
    HasDerivAt (fun e : ℝ =>
      (Complex.exp ((primeIntegral 0 w z : ℂ)+(e : ℂ)*h)-1)/(z : ℂ)^2)
      (((w+z : ℝ) : ℂ)*h/((w : ℂ)*(z : ℂ)^2)) 0 := by
  have hd := (((((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const h).const_add
    (primeIntegral 0 w z : ℂ)).cexp).sub_const 1).div_const ((z : ℂ)^2)
  apply hd.congr_deriv
  simp only [id_eq, Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero]
  rw [primeIntegral, integral_primeFactor hw hz.le, ← Complex.ofReal_exp,
    Real.exp_log (div_pos (by linarith) hw), Complex.ofReal_div]
  ring

theorem zero_cutoff_prime_variation_ne_zero {w z : ℝ} (hw : 0 < w) (hz : 0 < z)
    {h : ℂ} (hh : h ≠ 0) : ((w+z : ℝ) : ℂ)*h/((w : ℂ)*(z : ℂ)^2) ≠ 0 := by
  apply div_ne_zero
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith : w+z ≠ 0)) hh
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hw.ne')
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hz.ne'))

/-- The positive-cutoff contrast is not identically annihilated by the
complete count sum. This is a transform statement, not a pointwise sign
claim for the least-prime packet. -/
theorem cutoff_contrast_ne_zero {a b w z : ℝ} (ha : 0 < a) (hab : a < b)
    (hw : 0 < w) (hz : 0 < z) : cascadeTransform a w z-cascadeTransform b w z ≠ 0 := by
  have hpos (x : ℝ) (hx : 0 < x) : 0 < primeFactor w z x := by
    unfold primeFactor
    apply mul_pos (inv_pos.mpr hx)
    apply sub_pos.mpr
    apply Real.exp_lt_exp.mpr
    nlinarith
  have hc : ContinuousOn (primeFactor w z) (Icc a b) := by
    intro x hx
    have hx0 : x ≠ 0 := (ha.trans_le hx.1).ne'
    apply ContinuousAt.continuousWithinAt
    unfold primeFactor
    fun_prop
  have hi := intervalIntegral.integral_pos hab hc
    (fun x hx => (hpos x (ha.trans hx.1)).le) ⟨a, ⟨le_rfl, hab.le⟩, hpos a ha⟩
  have he := intervalIntegral.integral_Ioi_sub_Ioi
    ((integrable_primeFactor hw hz.le).mono_set (Ioi_subset_Ioi ha.le)) hab.le
  have hj : primeIntegral b w z < primeIntegral a w z := by
    unfold primeIntegral
    linarith
  have hreal : 0 < (Real.exp (primeIntegral a w z)-Real.exp (primeIntegral b w z))/z^2 :=
    div_pos (sub_pos.mpr (Real.exp_lt_exp.mpr hj)) (sq_pos_of_pos hz)
  have hval : cascadeTransform a w z-cascadeTransform b w z =
      (((Real.exp (primeIntegral a w z)-Real.exp (primeIntegral b w z))/z^2 : ℝ) : ℂ) := by
    rw [cascadeTransform_eq ha.le hz, cascadeTransform_eq (ha.trans hab).le hz]
    push_cast
    ring
  rw [hval]
  exact Complex.ofReal_ne_zero.mpr hreal.ne'

/-- Even after taking a least-prime cutoff difference, a shared prime
perturbation above both cutoffs remains. Its multiplier is the full signed
contrast, not a sum of absolute contributions of separate prime counts. -/
theorem cutoff_contrast_prime_variation {a b w z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hz : 0 < z) (h : ℂ) :
    HasDerivAt (fun e : ℝ =>
      (Complex.exp ((primeIntegral a w z : ℂ)+(e : ℂ)*h)-
        Complex.exp ((primeIntegral b w z : ℂ)+(e : ℂ)*h))/(z : ℂ)^2)
      (h*(cascadeTransform a w z-cascadeTransform b w z)) 0 := by
  have hdA := ((((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const h).const_add
    (primeIntegral a w z : ℂ)).cexp)
  have hdB := ((((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const h).const_add
    (primeIntegral b w z : ℂ)).cexp)
  apply ((hdA.sub hdB).div_const ((z : ℂ)^2)).congr_deriv
  simp only [id_eq, Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero]
  rw [cascadeTransform_eq ha hz, cascadeTransform_eq hb hz]
  ring

theorem cutoff_contrast_prime_variation_ne_zero {a b w z : ℝ} (ha : 0 < a)
    (hab : a < b) (hw : 0 < w) (hz : 0 < z) {h : ℂ} (hh : h ≠ 0) :
    h*(cascadeTransform a w z-cascadeTransform b w z) ≠ 0 :=
  mul_ne_zero hh (cutoff_contrast_ne_zero ha hab hw hz)

end
end RiemannGaussian.ZetaRieszContinuumCascade
