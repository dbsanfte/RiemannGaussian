import RiemannGaussian.RiemannXiSuzukiCarrierCayleySpectralKernel

/-!
# Laplace energy realization of the off-axis Cayley frontier

The spectral Cauchy kernel is realized here as an exact Paley--Wiener Gram
integral. Upper-half-plane nodes use the positive-time modes
`sqrt(2) * exp(i*z*s)`; lower-half-plane nodes use
`sqrt(2) * exp(-i*z*s)`. Their half-line inner products are respectively
`2*i/(w-conj z)` and `-2*i/(w-conj z)`.

For every finite off-axis coefficient family, Lean expands the complete
spectral quadratic into the sum of two nonnegative real half-line energies.
This is then specialized to the genuine Suzuki coefficient-window tails.
Consequently the open off-axis Gram-vanishing condition is proved equivalent
to the two separate Laplace-energy vanishing conditions. Together with the
already isolated real-axis remainder, those conditions imply the original
coefficient-tail frontier. No energy decay is asserted in this file.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-- The normalized positive-time exponential mode attached to an
upper-half-plane spectral coordinate. -/
def suzukiXiCarrierUpperLaplaceFeature (z : ℂ) (s : ℝ) : ℂ :=
  (Real.sqrt 2 : ℂ) * Complex.exp (Complex.I * z * (s : ℂ))

private theorem upperLaplaceFeature_mul (z w : ℂ) (s : ℝ) :
    conj (suzukiXiCarrierUpperLaplaceFeature z s) * suzukiXiCarrierUpperLaplaceFeature w s =
      2 * Complex.exp ((Complex.I * (w - conj z)) * (s : ℂ)) := by
  unfold suzukiXiCarrierUpperLaplaceFeature
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  simp only [map_mul, conj_I, Complex.conj_ofReal]
  have hsqrt : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  calc
    (Real.sqrt 2 : ℂ) *
          Complex.exp (-Complex.I * conj z * (s : ℂ)) *
        ((Real.sqrt 2 : ℂ) *
          Complex.exp (Complex.I * w * (s : ℂ))) =
        (Real.sqrt 2 : ℂ) ^ 2 *
          (Complex.exp (-Complex.I * conj z * (s : ℂ)) *
            Complex.exp (Complex.I * w * (s : ℂ))) := by ring
    _ = 2 * Complex.exp
          ((-Complex.I * conj z * (s : ℂ)) +
            (Complex.I * w * (s : ℂ))) := by
      rw [hsqrt, Complex.exp_add]
    _ = 2 * Complex.exp
          ((Complex.I * (w - conj z)) * (s : ℂ)) := by
      congr 2
      ring

/-- The product of two upper exponential modes is integrable on the positive
half-line. -/
theorem integrableOn_conj_suzukiXiCarrierUpperLaplaceFeature_mul
    {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    IntegrableOn
      (fun s : ℝ ↦ conj (suzukiXiCarrierUpperLaplaceFeature z s) *
        suzukiXiCarrierUpperLaplaceFeature w s) (Ioi 0) := by
  have ha : (Complex.I * (w - conj z)).re < 0 := by
    simp only [mul_re, I_re, sub_re, conj_re, zero_mul, I_im,
      sub_im, conj_im, one_mul]
    linarith
  refine ((integrableOn_exp_mul_complex_Ioi ha 0).const_mul 2).congr ?_
  filter_upwards with s
  exact (upperLaplaceFeature_mul z w s).symm

/-- The half-line Gram integral of two upper exponential modes is exactly the
upper spectral Cauchy kernel. -/
theorem integral_conj_suzukiXiCarrierUpperLaplaceFeature_mul
    {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    (∫ s : ℝ in Ioi 0,
      conj (suzukiXiCarrierUpperLaplaceFeature z s) * suzukiXiCarrierUpperLaplaceFeature w s) =
      2 * Complex.I / (w - conj z) := by
  have ha : (Complex.I * (w - conj z)).re < 0 := by
    simp only [mul_re, I_re, sub_re, conj_re, zero_mul, I_im,
      sub_im, conj_im, one_mul]
    linarith
  rw [MeasureTheory.integral_congr_ae
    (ae_of_all _ (upperLaplaceFeature_mul z w))]
  rw [MeasureTheory.integral_const_mul,
    integral_exp_mul_complex_Ioi ha 0]
  simp only [ofReal_zero, mul_zero, exp_zero, neg_div]
  have hden : w - conj z ≠ 0 := by
    intro hzero
    have h := congrArg Complex.im hzero
    simp only [sub_im, conj_im, zero_im] at h
    linarith
  field_simp [hden]
  rw [pow_two, Complex.I_mul_I]

/-- The normalized positive-time exponential mode attached to a
lower-half-plane spectral coordinate, with reversed oscillatory sign. -/
def suzukiXiCarrierLowerLaplaceFeature (z : ℂ) (s : ℝ) : ℂ :=
  (Real.sqrt 2 : ℂ) * Complex.exp (-Complex.I * z * (s : ℂ))

private theorem lowerLaplaceFeature_mul (z w : ℂ) (s : ℝ) :
    conj (suzukiXiCarrierLowerLaplaceFeature z s) * suzukiXiCarrierLowerLaplaceFeature w s =
      2 * Complex.exp ((-Complex.I * (w - conj z)) * (s : ℂ)) := by
  unfold suzukiXiCarrierLowerLaplaceFeature
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  simp only [map_mul, map_neg, conj_I, neg_neg, Complex.conj_ofReal]
  have hsqrt : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  calc
    (Real.sqrt 2 : ℂ) *
          Complex.exp (Complex.I * conj z * (s : ℂ)) *
        ((Real.sqrt 2 : ℂ) *
          Complex.exp (-Complex.I * w * (s : ℂ))) =
        (Real.sqrt 2 : ℂ) ^ 2 *
          (Complex.exp (Complex.I * conj z * (s : ℂ)) *
            Complex.exp (-Complex.I * w * (s : ℂ))) := by ring
    _ = 2 * Complex.exp
          ((Complex.I * conj z * (s : ℂ)) +
            (-Complex.I * w * (s : ℂ))) := by
      rw [hsqrt, Complex.exp_add]
    _ = 2 * Complex.exp
          ((-Complex.I * (w - conj z)) * (s : ℂ)) := by
      congr 2
      ring

/-- The product of two lower exponential modes is integrable on the positive
half-line. -/
theorem integrableOn_conj_suzukiXiCarrierLowerLaplaceFeature_mul
    {z w : ℂ} (hz : z.im < 0) (hw : w.im < 0) :
    IntegrableOn
      (fun s : ℝ ↦ conj (suzukiXiCarrierLowerLaplaceFeature z s) *
        suzukiXiCarrierLowerLaplaceFeature w s) (Ioi 0) := by
  have ha : (-Complex.I * (w - conj z)).re < 0 := by
    simp only [neg_mul, mul_re, neg_re, I_re, sub_re, conj_re, zero_mul,
      I_im, sub_im, conj_im, one_mul]
    linarith
  refine ((integrableOn_exp_mul_complex_Ioi ha 0).const_mul 2).congr ?_
  filter_upwards with s
  exact (lowerLaplaceFeature_mul z w s).symm

/-- The half-line Gram integral of two lower exponential modes is exactly the
signed lower spectral Cauchy kernel. -/
theorem integral_conj_suzukiXiCarrierLowerLaplaceFeature_mul
    {z w : ℂ} (hz : z.im < 0) (hw : w.im < 0) :
    (∫ s : ℝ in Ioi 0,
      conj (suzukiXiCarrierLowerLaplaceFeature z s) * suzukiXiCarrierLowerLaplaceFeature w s) =
      (-2 * Complex.I) / (w - conj z) := by
  have ha : (-Complex.I * (w - conj z)).re < 0 := by
    simp only [neg_mul, mul_re, neg_re, I_re, sub_re, conj_re, zero_mul,
      I_im, sub_im, conj_im, one_mul]
    linarith
  rw [MeasureTheory.integral_congr_ae
    (ae_of_all _ (lowerLaplaceFeature_mul z w))]
  rw [MeasureTheory.integral_const_mul,
    integral_exp_mul_complex_Ioi ha 0]
  simp only [ofReal_zero, mul_zero, exp_zero, neg_div]
  have hden : w - conj z ≠ 0 := by
    intro hzero
    have h := congrArg Complex.im hzero
    simp only [sub_im, conj_im, zero_im] at h
    linarith
  field_simp [hden]
  rw [pow_two, Complex.I_mul_I]
  simp

/-- One weighted upper-half-plane Laplace summand, totalized to zero for every
other node. -/
def suzukiXiCarrierCayleyUpperLaplaceSummand
    (c : NontrivialZetaZero →₀ ℂ)
    (rho : NontrivialZetaZero) (s : ℝ) : ℂ :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    suzukiXiCarrierCayleyOffAxisWeightedCoefficient c rho *
      suzukiXiCarrierUpperLaplaceFeature (zetaSpectralCoordinate rho.1) s
  else 0

/-- One weighted lower-half-plane Laplace summand, totalized to zero for every
other node. -/
def suzukiXiCarrierCayleyLowerLaplaceSummand
    (c : NontrivialZetaZero →₀ ℂ)
    (rho : NontrivialZetaZero) (s : ℝ) : ℂ :=
  if (zetaSpectralCoordinate rho.1).im < 0 then
    suzukiXiCarrierCayleyOffAxisWeightedCoefficient c rho *
      suzukiXiCarrierLowerLaplaceFeature (zetaSpectralCoordinate rho.1) s
  else 0

/-- The finite upper-half-plane exponential synthesis of a coefficient
family. -/
def suzukiXiCarrierCayleyUpperLaplaceSynthesis
    (c : NontrivialZetaZero →₀ ℂ) (s : ℝ) : ℂ :=
  ∑ rho ∈ c.support, suzukiXiCarrierCayleyUpperLaplaceSummand c rho s

/-- The finite lower-half-plane exponential synthesis of a coefficient
family. -/
def suzukiXiCarrierCayleyLowerLaplaceSynthesis
    (c : NontrivialZetaZero →₀ ℂ) (s : ℝ) : ℂ :=
  ∑ rho ∈ c.support, suzukiXiCarrierCayleyLowerLaplaceSummand c rho s

private theorem upperLaplaceSynthesis_normSq_expand
    (c : NontrivialZetaZero →₀ ℂ) (s : ℝ) :
    conj (suzukiXiCarrierCayleyUpperLaplaceSynthesis c s) * suzukiXiCarrierCayleyUpperLaplaceSynthesis c s =
      ∑ rho ∈ c.support, ∑ sigma ∈ c.support,
        conj (suzukiXiCarrierCayleyUpperLaplaceSummand c rho s) *
          suzukiXiCarrierCayleyUpperLaplaceSummand c sigma s := by
  unfold suzukiXiCarrierCayleyUpperLaplaceSynthesis
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem lowerLaplaceSynthesis_normSq_expand
    (c : NontrivialZetaZero →₀ ℂ) (s : ℝ) :
    conj (suzukiXiCarrierCayleyLowerLaplaceSynthesis c s) * suzukiXiCarrierCayleyLowerLaplaceSynthesis c s =
      ∑ rho ∈ c.support, ∑ sigma ∈ c.support,
        conj (suzukiXiCarrierCayleyLowerLaplaceSummand c rho s) *
          suzukiXiCarrierCayleyLowerLaplaceSummand c sigma s := by
  unfold suzukiXiCarrierCayleyLowerLaplaceSynthesis
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem integrableOn_upperLaplaceSummand_mul
    (c : NontrivialZetaZero →₀ ℂ)
    (rho sigma : NontrivialZetaZero) :
    IntegrableOn (fun s : ℝ ↦
      conj (suzukiXiCarrierCayleyUpperLaplaceSummand c rho s) *
        suzukiXiCarrierCayleyUpperLaplaceSummand c sigma s) (Ioi 0) := by
  by_cases hrho : 0 < (zetaSpectralCoordinate rho.1).im
  · by_cases hsigma : 0 < (zetaSpectralCoordinate sigma.1).im
    · have hbase := integrableOn_conj_suzukiXiCarrierUpperLaplaceFeature_mul hrho hsigma
      have hscaled : IntegrableOn (fun s : ℝ ↦
          (conj (suzukiXiCarrierCayleyOffAxisWeightedCoefficient c rho) *
            suzukiXiCarrierCayleyOffAxisWeightedCoefficient c sigma) *
              (conj (suzukiXiCarrierUpperLaplaceFeature
                  (zetaSpectralCoordinate rho.1) s) *
                suzukiXiCarrierUpperLaplaceFeature
                  (zetaSpectralCoordinate sigma.1) s)) (Ioi 0) :=
        hbase.const_mul
          (conj (suzukiXiCarrierCayleyOffAxisWeightedCoefficient c rho) *
            suzukiXiCarrierCayleyOffAxisWeightedCoefficient c sigma)
      refine hscaled.congr ?_
      filter_upwards with s
      unfold suzukiXiCarrierCayleyUpperLaplaceSummand
      simp only [if_pos hrho, if_pos hsigma, map_mul]
      ring
    · unfold suzukiXiCarrierCayleyUpperLaplaceSummand
      simp only [if_pos hrho, if_neg hsigma, map_mul, mul_zero]
      exact integrableOn_zero
  · unfold suzukiXiCarrierCayleyUpperLaplaceSummand
    simp only [if_neg hrho, map_zero, zero_mul]
    exact integrableOn_zero

private theorem integrableOn_lowerLaplaceSummand_mul
    (c : NontrivialZetaZero →₀ ℂ)
    (rho sigma : NontrivialZetaZero) :
    IntegrableOn (fun s : ℝ ↦
      conj (suzukiXiCarrierCayleyLowerLaplaceSummand c rho s) *
        suzukiXiCarrierCayleyLowerLaplaceSummand c sigma s) (Ioi 0) := by
  by_cases hrho : (zetaSpectralCoordinate rho.1).im < 0
  · by_cases hsigma : (zetaSpectralCoordinate sigma.1).im < 0
    · have hbase := integrableOn_conj_suzukiXiCarrierLowerLaplaceFeature_mul hrho hsigma
      have hscaled : IntegrableOn (fun s : ℝ ↦
          (conj (suzukiXiCarrierCayleyOffAxisWeightedCoefficient c rho) *
            suzukiXiCarrierCayleyOffAxisWeightedCoefficient c sigma) *
              (conj (suzukiXiCarrierLowerLaplaceFeature
                  (zetaSpectralCoordinate rho.1) s) *
                suzukiXiCarrierLowerLaplaceFeature
                  (zetaSpectralCoordinate sigma.1) s)) (Ioi 0) :=
        hbase.const_mul
          (conj (suzukiXiCarrierCayleyOffAxisWeightedCoefficient c rho) *
            suzukiXiCarrierCayleyOffAxisWeightedCoefficient c sigma)
      refine hscaled.congr ?_
      filter_upwards with s
      unfold suzukiXiCarrierCayleyLowerLaplaceSummand
      simp only [if_pos hrho, if_pos hsigma, map_mul]
      ring
    · unfold suzukiXiCarrierCayleyLowerLaplaceSummand
      simp only [if_pos hrho, if_neg hsigma, map_mul, mul_zero]
      exact integrableOn_zero
  · unfold suzukiXiCarrierCayleyLowerLaplaceSummand
    simp only [if_neg hrho, map_zero, zero_mul]
    exact integrableOn_zero

private theorem integral_upperLaplaceSummand_mul
    (c : NontrivialZetaZero →₀ ℂ)
    (rho sigma : NontrivialZetaZero) :
    (∫ s : ℝ in Ioi 0,
      conj (suzukiXiCarrierCayleyUpperLaplaceSummand c rho s) *
        suzukiXiCarrierCayleyUpperLaplaceSummand c sigma s) =
      if 0 < (zetaSpectralCoordinate rho.1).im then
        if 0 < (zetaSpectralCoordinate sigma.1).im then
          conj (suzukiXiCarrierCayleyOffAxisWeightedCoefficient c rho) *
            suzukiXiCarrierCayleyOffAxisWeightedCoefficient c sigma *
              (2 * Complex.I /
                (zetaSpectralCoordinate sigma.1 -
                  conj (zetaSpectralCoordinate rho.1)))
        else 0
      else 0 := by
  by_cases hrho : 0 < (zetaSpectralCoordinate rho.1).im
  · by_cases hsigma : 0 < (zetaSpectralCoordinate sigma.1).im
    · simp only [if_pos hrho, if_pos hsigma]
      calc
        (∫ s : ℝ in Ioi 0,
            conj (suzukiXiCarrierCayleyUpperLaplaceSummand c rho s) *
              suzukiXiCarrierCayleyUpperLaplaceSummand c sigma s) =
            ∫ s : ℝ in Ioi 0,
              (conj (suzukiXiCarrierCayleyOffAxisWeightedCoefficient c rho) *
                suzukiXiCarrierCayleyOffAxisWeightedCoefficient c sigma) *
                (conj (suzukiXiCarrierUpperLaplaceFeature
                    (zetaSpectralCoordinate rho.1) s) *
                  suzukiXiCarrierUpperLaplaceFeature
                    (zetaSpectralCoordinate sigma.1) s) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with s
          unfold suzukiXiCarrierCayleyUpperLaplaceSummand
          simp only [if_pos hrho, if_pos hsigma, map_mul]
          ring
        _ = (conj (suzukiXiCarrierCayleyOffAxisWeightedCoefficient c rho) *
              suzukiXiCarrierCayleyOffAxisWeightedCoefficient c sigma) *
            (∫ s : ℝ in Ioi 0,
              conj (suzukiXiCarrierUpperLaplaceFeature
                  (zetaSpectralCoordinate rho.1) s) *
                suzukiXiCarrierUpperLaplaceFeature
                  (zetaSpectralCoordinate sigma.1) s) := by
          rw [MeasureTheory.integral_const_mul]
        _ = _ := by rw [integral_conj_suzukiXiCarrierUpperLaplaceFeature_mul hrho hsigma]
    · simp only [if_pos hrho, if_neg hsigma]
      unfold suzukiXiCarrierCayleyUpperLaplaceSummand
      simp only [if_pos hrho, if_neg hsigma, map_mul, mul_zero,
        MeasureTheory.integral_zero]
  · simp only [if_neg hrho]
    unfold suzukiXiCarrierCayleyUpperLaplaceSummand
    simp only [if_neg hrho, map_zero, zero_mul,
      MeasureTheory.integral_zero]

private theorem integral_lowerLaplaceSummand_mul
    (c : NontrivialZetaZero →₀ ℂ)
    (rho sigma : NontrivialZetaZero) :
    (∫ s : ℝ in Ioi 0,
      conj (suzukiXiCarrierCayleyLowerLaplaceSummand c rho s) *
        suzukiXiCarrierCayleyLowerLaplaceSummand c sigma s) =
      if (zetaSpectralCoordinate rho.1).im < 0 then
        if (zetaSpectralCoordinate sigma.1).im < 0 then
          conj (suzukiXiCarrierCayleyOffAxisWeightedCoefficient c rho) *
            suzukiXiCarrierCayleyOffAxisWeightedCoefficient c sigma *
              ((-2 * Complex.I) /
                (zetaSpectralCoordinate sigma.1 -
                  conj (zetaSpectralCoordinate rho.1)))
        else 0
      else 0 := by
  by_cases hrho : (zetaSpectralCoordinate rho.1).im < 0
  · by_cases hsigma : (zetaSpectralCoordinate sigma.1).im < 0
    · simp only [if_pos hrho, if_pos hsigma]
      calc
        (∫ s : ℝ in Ioi 0,
            conj (suzukiXiCarrierCayleyLowerLaplaceSummand c rho s) *
              suzukiXiCarrierCayleyLowerLaplaceSummand c sigma s) =
            ∫ s : ℝ in Ioi 0,
              (conj (suzukiXiCarrierCayleyOffAxisWeightedCoefficient c rho) *
                suzukiXiCarrierCayleyOffAxisWeightedCoefficient c sigma) *
                (conj (suzukiXiCarrierLowerLaplaceFeature
                    (zetaSpectralCoordinate rho.1) s) *
                  suzukiXiCarrierLowerLaplaceFeature
                    (zetaSpectralCoordinate sigma.1) s) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with s
          unfold suzukiXiCarrierCayleyLowerLaplaceSummand
          simp only [if_pos hrho, if_pos hsigma, map_mul]
          ring
        _ = (conj (suzukiXiCarrierCayleyOffAxisWeightedCoefficient c rho) *
              suzukiXiCarrierCayleyOffAxisWeightedCoefficient c sigma) *
            (∫ s : ℝ in Ioi 0,
              conj (suzukiXiCarrierLowerLaplaceFeature
                  (zetaSpectralCoordinate rho.1) s) *
                suzukiXiCarrierLowerLaplaceFeature
                  (zetaSpectralCoordinate sigma.1) s) := by
          rw [MeasureTheory.integral_const_mul]
        _ = _ := by rw [integral_conj_suzukiXiCarrierLowerLaplaceFeature_mul hrho hsigma]
    · simp only [if_pos hrho, if_neg hsigma]
      unfold suzukiXiCarrierCayleyLowerLaplaceSummand
      simp only [if_pos hrho, if_neg hsigma, map_mul, mul_zero,
        MeasureTheory.integral_zero]
  · simp only [if_neg hrho]
    unfold suzukiXiCarrierCayleyLowerLaplaceSummand
    simp only [if_neg hrho, map_zero, zero_mul,
      MeasureTheory.integral_zero]

private theorem integral_upperLaplaceSynthesis_normSq
    (c : NontrivialZetaZero →₀ ℂ) :
    (∫ s : ℝ in Ioi 0,
      conj (suzukiXiCarrierCayleyUpperLaplaceSynthesis c s) * suzukiXiCarrierCayleyUpperLaplaceSynthesis c s) =
      ∑ rho ∈ c.support, ∑ sigma ∈ c.support,
        if 0 < (zetaSpectralCoordinate rho.1).im then
          if 0 < (zetaSpectralCoordinate sigma.1).im then
            conj (suzukiXiCarrierCayleyOffAxisWeightedCoefficient c rho) *
              suzukiXiCarrierCayleyOffAxisWeightedCoefficient c sigma *
                (2 * Complex.I /
                  (zetaSpectralCoordinate sigma.1 -
                    conj (zetaSpectralCoordinate rho.1)))
          else 0
        else 0 := by
  rw [MeasureTheory.integral_congr_ae (ae_of_all _ fun s ↦
    upperLaplaceSynthesis_normSq_expand c s)]
  rw [MeasureTheory.integral_finsetSum c.support]
  · apply Finset.sum_congr rfl
    intro rho hrho
    rw [MeasureTheory.integral_finsetSum c.support]
    · apply Finset.sum_congr rfl
      intro sigma hsigma
      exact integral_upperLaplaceSummand_mul c rho sigma
    · intro sigma hsigma
      exact integrableOn_upperLaplaceSummand_mul c rho sigma
  · intro rho hrho
    exact integrable_finsetSum c.support fun sigma hsigma ↦
      integrableOn_upperLaplaceSummand_mul c rho sigma

private theorem integral_lowerLaplaceSynthesis_normSq
    (c : NontrivialZetaZero →₀ ℂ) :
    (∫ s : ℝ in Ioi 0,
      conj (suzukiXiCarrierCayleyLowerLaplaceSynthesis c s) * suzukiXiCarrierCayleyLowerLaplaceSynthesis c s) =
      ∑ rho ∈ c.support, ∑ sigma ∈ c.support,
        if (zetaSpectralCoordinate rho.1).im < 0 then
          if (zetaSpectralCoordinate sigma.1).im < 0 then
            conj (suzukiXiCarrierCayleyOffAxisWeightedCoefficient c rho) *
              suzukiXiCarrierCayleyOffAxisWeightedCoefficient c sigma *
                ((-2 * Complex.I) /
                  (zetaSpectralCoordinate sigma.1 -
                    conj (zetaSpectralCoordinate rho.1)))
          else 0
        else 0 := by
  rw [MeasureTheory.integral_congr_ae (ae_of_all _ fun s ↦
    lowerLaplaceSynthesis_normSq_expand c s)]
  rw [MeasureTheory.integral_finsetSum c.support]
  · apply Finset.sum_congr rfl
    intro rho hrho
    rw [MeasureTheory.integral_finsetSum c.support]
    · apply Finset.sum_congr rfl
      intro sigma hsigma
      exact integral_lowerLaplaceSummand_mul c rho sigma
    · intro sigma hsigma
      exact integrableOn_lowerLaplaceSummand_mul c rho sigma
  · intro rho hrho
    exact integrable_finsetSum c.support fun sigma hsigma ↦
      integrableOn_lowerLaplaceSummand_mul c rho sigma

private theorem spectralGram_eq_laplace
    (c : NontrivialZetaZero →₀ ℂ)
    (hoffAxis : ∀ rho ∈ c.support,
      (zetaSpectralCoordinate rho.1).im ≠ 0) :
    suzukiXiCarrierCayleyOffAxisSpectralGramQuadratic c =
      (∫ s : ℝ in Ioi 0,
        conj (suzukiXiCarrierCayleyUpperLaplaceSynthesis c s) * suzukiXiCarrierCayleyUpperLaplaceSynthesis c s) +
      (∫ s : ℝ in Ioi 0,
        conj (suzukiXiCarrierCayleyLowerLaplaceSynthesis c s) * suzukiXiCarrierCayleyLowerLaplaceSynthesis c s) := by
  rw [integral_upperLaplaceSynthesis_normSq,
    integral_lowerLaplaceSynthesis_normSq]
  unfold suzukiXiCarrierCayleyOffAxisSpectralGramQuadratic
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  by_cases hrhoUpper : 0 < (zetaSpectralCoordinate rho.1).im
  · have hrhoNotLower : ¬(zetaSpectralCoordinate rho.1).im < 0 :=
      not_lt.mpr hrhoUpper.le
    by_cases hsigmaUpper : 0 < (zetaSpectralCoordinate sigma.1).im
    · have hsigmaNotLower :
          ¬(zetaSpectralCoordinate sigma.1).im < 0 :=
        not_lt.mpr hsigmaUpper.le
      simp only [suzukiXiCarrierCayleyOffAxisSpectralKernel,
        if_pos hrhoUpper, if_pos hsigmaUpper, if_neg hrhoNotLower,
        if_neg hsigmaNotLower, add_zero]
    · have hsigmaLower : (zetaSpectralCoordinate sigma.1).im < 0 :=
        lt_of_le_of_ne (not_lt.mp hsigmaUpper) (hoffAxis sigma hsigma)
      simp only [suzukiXiCarrierCayleyOffAxisSpectralKernel,
        if_pos hrhoUpper, if_neg hsigmaUpper, if_neg hrhoNotLower,
        if_pos hsigmaLower, mul_zero, zero_add]
  · have hrhoLower : (zetaSpectralCoordinate rho.1).im < 0 :=
      lt_of_le_of_ne (not_lt.mp hrhoUpper) (hoffAxis rho hrho)
    by_cases hsigmaUpper : 0 < (zetaSpectralCoordinate sigma.1).im
    · have hsigmaNotLower :
          ¬(zetaSpectralCoordinate sigma.1).im < 0 :=
        not_lt.mpr hsigmaUpper.le
      simp only [suzukiXiCarrierCayleyOffAxisSpectralKernel,
        if_neg hrhoUpper, if_pos hsigmaUpper, if_pos hrhoLower,
        if_neg hsigmaNotLower, mul_zero, add_zero]
    · have hsigmaLower : (zetaSpectralCoordinate sigma.1).im < 0 :=
        lt_of_le_of_ne (not_lt.mp hsigmaUpper) (hoffAxis sigma hsigma)
      simp only [suzukiXiCarrierCayleyOffAxisSpectralKernel,
        if_neg hrhoUpper, if_neg hsigmaUpper, if_pos hrhoLower,
        if_pos hsigmaLower, zero_add]

private theorem integrableOn_upperLaplaceSynthesis_normSq
    (c : NontrivialZetaZero →₀ ℂ) :
    IntegrableOn (fun s : ℝ ↦
      conj (suzukiXiCarrierCayleyUpperLaplaceSynthesis c s) * suzukiXiCarrierCayleyUpperLaplaceSynthesis c s)
      (Ioi 0) := by
  have hsum : IntegrableOn (fun s : ℝ ↦
      ∑ rho ∈ c.support, ∑ sigma ∈ c.support,
        conj (suzukiXiCarrierCayleyUpperLaplaceSummand c rho s) *
          suzukiXiCarrierCayleyUpperLaplaceSummand c sigma s) (Ioi 0) :=
    integrable_finsetSum c.support fun rho hrho ↦
      integrable_finsetSum c.support fun sigma hsigma ↦
        integrableOn_upperLaplaceSummand_mul c rho sigma
  refine hsum.congr ?_
  filter_upwards with s
  exact (upperLaplaceSynthesis_normSq_expand c s).symm

private theorem integrableOn_lowerLaplaceSynthesis_normSq
    (c : NontrivialZetaZero →₀ ℂ) :
    IntegrableOn (fun s : ℝ ↦
      conj (suzukiXiCarrierCayleyLowerLaplaceSynthesis c s) * suzukiXiCarrierCayleyLowerLaplaceSynthesis c s)
      (Ioi 0) := by
  have hsum : IntegrableOn (fun s : ℝ ↦
      ∑ rho ∈ c.support, ∑ sigma ∈ c.support,
        conj (suzukiXiCarrierCayleyLowerLaplaceSummand c rho s) *
          suzukiXiCarrierCayleyLowerLaplaceSummand c sigma s) (Ioi 0) :=
    integrable_finsetSum c.support fun rho hrho ↦
      integrable_finsetSum c.support fun sigma hsigma ↦
        integrableOn_lowerLaplaceSummand_mul c rho sigma
  refine hsum.congr ?_
  filter_upwards with s
  exact (lowerLaplaceSynthesis_normSq_expand c s).symm

/-- Every finite upper exponential synthesis has integrable squared norm on
the positive half-line. -/
theorem integrableOn_norm_sq_suzukiXiCarrierCayleyUpperLaplaceSynthesis
    (c : NontrivialZetaZero →₀ ℂ) :
    IntegrableOn (fun s : ℝ ↦ ‖suzukiXiCarrierCayleyUpperLaplaceSynthesis c s‖ ^ 2)
      (Ioi 0) := by
  refine (integrableOn_upperLaplaceSynthesis_normSq c).norm.congr ?_
  filter_upwards with s
  simp only [norm_mul, norm_conj, pow_two]

/-- Every finite lower exponential synthesis has integrable squared norm on
the positive half-line. -/
theorem integrableOn_norm_sq_suzukiXiCarrierCayleyLowerLaplaceSynthesis
    (c : NontrivialZetaZero →₀ ℂ) :
    IntegrableOn (fun s : ℝ ↦ ‖suzukiXiCarrierCayleyLowerLaplaceSynthesis c s‖ ^ 2)
      (Ioi 0) := by
  refine (integrableOn_lowerLaplaceSynthesis_normSq c).norm.congr ?_
  filter_upwards with s
  simp only [norm_mul, norm_conj, pow_two]

/-- The positive-half-line squared-norm energy of the upper exponential
synthesis. -/
def suzukiXiCarrierCayleyUpperLaplaceEnergy
    (c : NontrivialZetaZero →₀ ℂ) : ℝ :=
  ∫ s : ℝ in Ioi 0, ‖suzukiXiCarrierCayleyUpperLaplaceSynthesis c s‖ ^ 2

/-- The positive-half-line squared-norm energy of the lower exponential
synthesis. -/
def suzukiXiCarrierCayleyLowerLaplaceEnergy
    (c : NontrivialZetaZero →₀ ℂ) : ℝ :=
  ∫ s : ℝ in Ioi 0, ‖suzukiXiCarrierCayleyLowerLaplaceSynthesis c s‖ ^ 2

private theorem integral_upperLaplaceSynthesis_normSq_eq_energy
    (c : NontrivialZetaZero →₀ ℂ) :
    (∫ s : ℝ in Ioi 0,
      conj (suzukiXiCarrierCayleyUpperLaplaceSynthesis c s) * suzukiXiCarrierCayleyUpperLaplaceSynthesis c s) =
      (suzukiXiCarrierCayleyUpperLaplaceEnergy c : ℂ) := by
  calc
    (∫ s : ℝ in Ioi 0,
        conj (suzukiXiCarrierCayleyUpperLaplaceSynthesis c s) * suzukiXiCarrierCayleyUpperLaplaceSynthesis c s) =
        ∫ s : ℝ in Ioi 0,
          (‖suzukiXiCarrierCayleyUpperLaplaceSynthesis c s‖ ^ 2 : ℂ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with s
      rw [← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq]
      norm_cast
    _ = (suzukiXiCarrierCayleyUpperLaplaceEnergy c : ℂ) := by
      simp_rw [← ofReal_pow]
      simpa only [suzukiXiCarrierCayleyUpperLaplaceEnergy] using
        (integral_complex_ofReal
          (μ := volume.restrict (Ioi 0))
          (f := fun s : ℝ ↦ ‖suzukiXiCarrierCayleyUpperLaplaceSynthesis c s‖ ^ 2))

private theorem integral_lowerLaplaceSynthesis_normSq_eq_energy
    (c : NontrivialZetaZero →₀ ℂ) :
    (∫ s : ℝ in Ioi 0,
      conj (suzukiXiCarrierCayleyLowerLaplaceSynthesis c s) * suzukiXiCarrierCayleyLowerLaplaceSynthesis c s) =
      (suzukiXiCarrierCayleyLowerLaplaceEnergy c : ℂ) := by
  calc
    (∫ s : ℝ in Ioi 0,
        conj (suzukiXiCarrierCayleyLowerLaplaceSynthesis c s) * suzukiXiCarrierCayleyLowerLaplaceSynthesis c s) =
        ∫ s : ℝ in Ioi 0,
          (‖suzukiXiCarrierCayleyLowerLaplaceSynthesis c s‖ ^ 2 : ℂ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with s
      rw [← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq]
      norm_cast
    _ = (suzukiXiCarrierCayleyLowerLaplaceEnergy c : ℂ) := by
      simp_rw [← ofReal_pow]
      simpa only [suzukiXiCarrierCayleyLowerLaplaceEnergy] using
        (integral_complex_ofReal
          (μ := volume.restrict (Ioi 0))
          (f := fun s : ℝ ↦ ‖suzukiXiCarrierCayleyLowerLaplaceSynthesis c s‖ ^ 2))

/-- On any genuinely off-axis finite family, the explicit spectral Cauchy
quadratic is the real sum of the upper and lower Laplace energies. -/
theorem suzukiXiCarrierCayleyOffAxisSpectralGramQuadratic_eq_laplaceEnergy
    (c : NontrivialZetaZero →₀ ℂ)
    (hoffAxis : ∀ rho ∈ c.support,
      (zetaSpectralCoordinate rho.1).im ≠ 0) :
    suzukiXiCarrierCayleyOffAxisSpectralGramQuadratic c =
      ((suzukiXiCarrierCayleyUpperLaplaceEnergy c + suzukiXiCarrierCayleyLowerLaplaceEnergy c : ℝ) : ℂ) := by
  rw [spectralGram_eq_laplace c hoffAxis,
    integral_upperLaplaceSynthesis_normSq_eq_energy,
    integral_lowerLaplaceSynthesis_normSq_eq_energy]
  norm_cast

/-- Every finite upper Laplace energy is nonnegative. -/
theorem suzukiXiCarrierCayleyUpperLaplaceEnergy_nonneg
    (c : NontrivialZetaZero →₀ ℂ) : 0 ≤ suzukiXiCarrierCayleyUpperLaplaceEnergy c := by
  unfold suzukiXiCarrierCayleyUpperLaplaceEnergy
  exact MeasureTheory.integral_nonneg fun s ↦ sq_nonneg _

/-- Every finite lower Laplace energy is nonnegative. -/
theorem suzukiXiCarrierCayleyLowerLaplaceEnergy_nonneg
    (c : NontrivialZetaZero →₀ ℂ) : 0 ≤ suzukiXiCarrierCayleyLowerLaplaceEnergy c := by
  unfold suzukiXiCarrierCayleyLowerLaplaceEnergy
  exact MeasureTheory.integral_nonneg fun s ↦ sq_nonneg _

/-- The upper Laplace energy of one genuine off-axis Suzuki coefficient
tail. -/
def suzukiXiCoefficientTailCayleyUpperLaplaceEnergy
    (t T U : ℝ) : ℝ :=
  suzukiXiCarrierCayleyUpperLaplaceEnergy
    (suzukiXiCoefficientTailCayleyOffAxisFinsupp t T U)

/-- The lower Laplace energy of one genuine off-axis Suzuki coefficient
tail. -/
def suzukiXiCoefficientTailCayleyLowerLaplaceEnergy
    (t T U : ℝ) : ℝ :=
  suzukiXiCarrierCayleyLowerLaplaceEnergy
    (suzukiXiCoefficientTailCayleyOffAxisFinsupp t T U)

/-- The real genuine-tail spectral Gram quadratic is exactly the sum of its
two half-line Laplace energies. -/
theorem re_suzukiXiCoefficientTailCayleyOffAxisSpectralGramQuadratic_eq_laplaceEnergy
    (t T U : ℝ) :
    (suzukiXiCoefficientTailCayleyOffAxisSpectralGramQuadratic t T U).re =
      suzukiXiCoefficientTailCayleyUpperLaplaceEnergy t T U + suzukiXiCoefficientTailCayleyLowerLaplaceEnergy t T U := by
  unfold suzukiXiCoefficientTailCayleyOffAxisSpectralGramQuadratic
    suzukiXiCoefficientTailCayleyUpperLaplaceEnergy suzukiXiCoefficientTailCayleyLowerLaplaceEnergy
  rw [suzukiXiCarrierCayleyOffAxisSpectralGramQuadratic_eq_laplaceEnergy]
  · norm_cast
  · intro rho hrho
    exact suzukiXiCoefficientTailCayleyOffAxisFinsupp_support
      t T U rho hrho

/-- Vanishing of the upper Laplace energy along late pairs of genuine Suzuki
coefficient windows. -/
def SuzukiXiCoefficientTailCayleyUpperLaplaceEnergyVanishing
    (t : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ,
    ∀ T ≥ R, ∀ U ≥ R, suzukiXiCoefficientTailCayleyUpperLaplaceEnergy t T U < epsilon

/-- Vanishing of the lower Laplace energy along late pairs of genuine Suzuki
coefficient windows. -/
def SuzukiXiCoefficientTailCayleyLowerLaplaceEnergyVanishing
    (t : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ,
    ∀ T ≥ R, ∀ U ≥ R, suzukiXiCoefficientTailCayleyLowerLaplaceEnergy t T U < epsilon

/-- The off-axis spectral Gram frontier is equivalent to simultaneous upper
and lower Laplace-energy vanishing. -/
theorem suzukiXiCoefficientTailCayleyOffAxisSpectralGramVanishing_iff_laplaceEnergies
    (t : ℝ) :
    SuzukiXiCoefficientTailCayleyOffAxisSpectralGramVanishing t ↔
      SuzukiXiCoefficientTailCayleyUpperLaplaceEnergyVanishing t ∧ SuzukiXiCoefficientTailCayleyLowerLaplaceEnergyVanishing t := by
  constructor
  · intro hvanish
    constructor
    · intro epsilon hepsilon
      obtain ⟨R, hR⟩ := hvanish epsilon hepsilon
      refine ⟨R, ?_⟩
      intro T hT U hU
      calc
        suzukiXiCoefficientTailCayleyUpperLaplaceEnergy t T U ≤
            suzukiXiCoefficientTailCayleyUpperLaplaceEnergy t T U +
              suzukiXiCoefficientTailCayleyLowerLaplaceEnergy t T U :=
          le_add_of_nonneg_right (suzukiXiCarrierCayleyLowerLaplaceEnergy_nonneg _)
        _ = (suzukiXiCoefficientTailCayleyOffAxisSpectralGramQuadratic
              t T U).re := (re_suzukiXiCoefficientTailCayleyOffAxisSpectralGramQuadratic_eq_laplaceEnergy t T U).symm
        _ < epsilon := hR T hT U hU
    · intro epsilon hepsilon
      obtain ⟨R, hR⟩ := hvanish epsilon hepsilon
      refine ⟨R, ?_⟩
      intro T hT U hU
      calc
        suzukiXiCoefficientTailCayleyLowerLaplaceEnergy t T U ≤
            suzukiXiCoefficientTailCayleyUpperLaplaceEnergy t T U +
              suzukiXiCoefficientTailCayleyLowerLaplaceEnergy t T U :=
          le_add_of_nonneg_left (suzukiXiCarrierCayleyUpperLaplaceEnergy_nonneg _)
        _ = (suzukiXiCoefficientTailCayleyOffAxisSpectralGramQuadratic
              t T U).re := (re_suzukiXiCoefficientTailCayleyOffAxisSpectralGramQuadratic_eq_laplaceEnergy t T U).symm
        _ < epsilon := hR T hT U hU
  · rintro ⟨hupper, hlower⟩
    intro epsilon hepsilon
    obtain ⟨Rupper, hRupper⟩ := hupper (epsilon / 2) (by linarith)
    obtain ⟨Rlower, hRlower⟩ := hlower (epsilon / 2) (by linarith)
    refine ⟨max Rupper Rlower, ?_⟩
    intro T hT U hU
    have hTupper : Rupper ≤ T := (le_max_left _ _).trans hT
    have hUupper : Rupper ≤ U := (le_max_left _ _).trans hU
    have hTlower : Rlower ≤ T := (le_max_right _ _).trans hT
    have hUlower : Rlower ≤ U := (le_max_right _ _).trans hU
    rw [re_suzukiXiCoefficientTailCayleyOffAxisSpectralGramQuadratic_eq_laplaceEnergy]
    linarith [hRupper T hTupper U hUupper,
      hRlower T hTlower U hUlower]

/-- Upper and lower Laplace-energy decay, together with decay of the isolated
real-node remainder, proves the original coefficient-tail Gram frontier. -/
theorem coefficientTailGramVanishing_of_cayleyLaplaceEnergies_realAxisRemainder
    {t : ℝ} (hupper : SuzukiXiCoefficientTailCayleyUpperLaplaceEnergyVanishing t)
    (hlower : SuzukiXiCoefficientTailCayleyLowerLaplaceEnergyVanishing t)
    (hreal : SuzukiXiCoefficientTailCayleyRealAxisRemainderNormVanishing t) :
    SuzukiXiCoefficientTailGramVanishing t := by
  apply coefficientTailGramVanishing_of_cayleySpectralGram_realAxisRemainder
  · exact (suzukiXiCoefficientTailCayleyOffAxisSpectralGramVanishing_iff_laplaceEnergies t).2
      ⟨hupper, hlower⟩
  · exact hreal

end

end RiemannGaussian
