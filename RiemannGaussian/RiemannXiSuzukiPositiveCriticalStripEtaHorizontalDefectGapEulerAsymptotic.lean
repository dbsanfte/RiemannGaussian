import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaHorizontalDefectGapEulerBound

/-!
# Normalized sharp eta-gap asymptotics and comparability closure

The explicit Euler-tail estimate is normalized here to a genuine limit.  The
finite gap error, multiplied by its complex odd endpoint power, tends to
`-1/2`.  The same theorem at a functional-equation partner makes precise that
the two complementary raw-tail rates are compatible.

The second part isolates the genuinely additional input: eventual two-sided
comparability of the two unnormalized errors forces the complementary real
exponents to agree, hence forces the critical line.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The finite arithmetic-gap error normalized by its complex odd endpoint
power. -/
def pairedEtaGapNormalizedFiniteError (N : ℕ) (s : ℂ) : ℂ :=
  ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ s *
    (pairedEtaGapCorePartialSum N s - pairedEtaGapCore s)

/-- After endpoint normalization, the sharp finite-gap error differs from
`-1/2` by at most an explicit constant divided by the endpoint. -/
theorem norm_pairedEtaGapNormalizedFiniteError_add_half_le
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖pairedEtaGapNormalizedFiniteError N s + 1 / 2‖ ≤
      ‖s‖ * ‖s + 1‖ *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) := by
  let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hsharp :=
    norm_pairedEtaGapCorePartialSum_sub_core_add_half_endpoint_le hs N
  have hcancel : (x : ℂ) ^ s * (x : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add s (-s) hxne, add_neg_cancel, Complex.cpow_zero]
  have hrewrite : pairedEtaGapNormalizedFiniteError N s + 1 / 2 =
      (x : ℂ) ^ s *
        (pairedEtaGapCorePartialSum N s - pairedEtaGapCore s +
          (x : ℂ) ^ (-s) / 2) := by
    unfold pairedEtaGapNormalizedFiniteError
    change (x : ℂ) ^ s *
        (pairedEtaGapCorePartialSum N s - pairedEtaGapCore s) + 1 / 2 = _
    rw [mul_add, mul_div, hcancel]
  rw [hrewrite, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hsharp' :
      ‖pairedEtaGapCorePartialSum N s - pairedEtaGapCore s +
          (x : ℂ) ^ (-s) / 2‖ ≤
        ‖s‖ * ‖s + 1‖ * (x ^ (s.re + 1))⁻¹ := by
    simpa [x] using hsharp
  calc
    x ^ s.re *
        ‖pairedEtaGapCorePartialSum N s - pairedEtaGapCore s +
          (x : ℂ) ^ (-s) / 2‖ ≤
        x ^ s.re *
          (‖s‖ * ‖s + 1‖ * (x ^ (s.re + 1))⁻¹) :=
      mul_le_mul_of_nonneg_left hsharp' (Real.rpow_nonneg hx.le _)
    _ = ‖s‖ * ‖s + 1‖ * x ^ (-1 : ℝ) := by
      rw [← Real.rpow_neg hx.le]
      calc
        x ^ s.re * (‖s‖ * ‖s + 1‖ * x ^ (-(s.re + 1))) =
            (‖s‖ * ‖s + 1‖) *
              (x ^ s.re * x ^ (-(s.re + 1))) := by ring
        _ = (‖s‖ * ‖s + 1‖) *
            x ^ (s.re + -(s.re + 1)) := by
          rw [Real.rpow_add hx]
        _ = ‖s‖ * ‖s + 1‖ * x ^ (-1 : ℝ) := by
          congr 2
          ring
    _ = _ := rfl

/-- The normalized finite gap error tends to its sharp universal leading
coefficient `-1/2` throughout the positive half-plane. -/
theorem tendsto_pairedEtaGapNormalizedFiniteError_neg_half
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => pairedEtaGapNormalizedFiniteError N s)
      atTop (nhds (-1 / 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (g := fun N : ℕ =>
    ‖s‖ * ‖s + 1‖ * (((2 * N + 1 : ℕ) : ℝ) ^ (-1 : ℝ)))
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · exact Eventually.of_forall fun N => by
      rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, sub_neg_eq_add]
      exact norm_pairedEtaGapNormalizedFiniteError_add_half_le hs N
  · have hinv : Tendsto (fun N : ℕ =>
        ((2 * N + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) atTop (nhds 0) := by
      simpa using
        (tendsto_pairedEtaOddEndpoint_rpow_zero (s := (1 : ℂ)) (by norm_num))
    simpa only [mul_zero] using
      Filter.Tendsto.const_mul (‖s‖ * ‖s + 1‖) hinv

/-- At a nontrivial zeta zero the normalized finite error is expressed with
the forced gap value `1`. -/
theorem tendsto_nontrivialZetaZero_etaGapNormalizedFiniteError_neg_half
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ =>
      ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ rho.1 *
        (pairedEtaGapCorePartialSum N rho.1 - 1))
      atTop (nhds (-1 / 2)) := by
  simpa [pairedEtaGapNormalizedFiniteError,
    pairedEtaGapCore_eq_one_of_nontrivialZetaZero rho] using
    tendsto_pairedEtaGapNormalizedFiniteError_neg_half
      (NontrivialZetaZero.zero_lt_re rho)

/-- Taking norms of the normalized complex asymptotic gives a positive real
limit for the raw gap-error magnitude. -/
theorem tendsto_pairedEtaGapErrorNorm_mul_oddEndpoint_rpow_half
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) ^ s.re) *
        ‖pairedEtaGapCorePartialSum N s - pairedEtaGapCore s‖)
      atTop (nhds (1 / 2)) := by
  have hnorm := tendsto_norm.comp
    (tendsto_pairedEtaGapNormalizedFiniteError_neg_half hs)
  convert hnorm using 1
  · funext N
    unfold pairedEtaGapNormalizedFiniteError
    change (((2 * N + 1 : ℕ) : ℝ) ^ s.re) *
        ‖pairedEtaGapCorePartialSum N s - pairedEtaGapCore s‖ =
      ‖((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ s *
        (pairedEtaGapCorePartialSum N s - pairedEtaGapCore s)‖
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  · norm_num

/-- At a nontrivial zero, the scaled norm limit uses the exact forced gap
value one. -/
theorem tendsto_nontrivialZetaZero_etaGapErrorNorm_mul_oddEndpoint_rpow_half
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) ^ rho.1.re) *
        ‖pairedEtaGapCorePartialSum N rho.1 - 1‖)
      atTop (nhds (1 / 2)) := by
  simpa [pairedEtaGapCore_eq_one_of_nontrivialZetaZero rho] using
    tendsto_pairedEtaGapErrorNorm_mul_oddEndpoint_rpow_half
      (NontrivialZetaZero.zero_lt_re rho)

/-- Two sequences with nonzero odd-power-scaled limits cannot remain
multiplicatively comparable when their real decay exponents differ. -/
theorem eq_of_oddEndpoint_scaled_limits_of_eventually_comparable
    {sigma tau : ℝ} {a b : ℕ → ℝ}
    (ha : Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) ^ sigma) * a N)
      atTop (nhds (1 / 2)))
    (hb : Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) ^ tau) * b N)
      atTop (nhds (1 / 2)))
    (hcomp : ∃ cLower cUpper : ℝ,
      0 < cLower ∧ 0 < cUpper ∧
        ∀ᶠ N : ℕ in atTop,
          cLower * b N ≤ a N ∧ a N ≤ cUpper * b N) :
    sigma = tau := by
  rcases hcomp with ⟨cLower, cUpper, hcLower, hcUpper, hcomp⟩
  rcases lt_trichotomy sigma tau with hlt | heq | hgt
  · exfalso
    have hdecay : Tendsto (fun N : ℕ =>
        ((2 * N + 1 : ℕ) : ℝ) ^ (sigma - tau))
        atTop (nhds 0) := by
      simpa only [Complex.ofReal_re,
        show sigma - tau = -(tau - sigma) by ring] using
        (tendsto_pairedEtaOddEndpoint_rpow_zero
          (s := ((tau - sigma : ℝ) : ℂ)) (by simpa using hlt))
    have hright : Tendsto (fun N : ℕ =>
        cUpper *
          ((((2 * N + 1 : ℕ) : ℝ) ^ (sigma - tau)) *
            ((((2 * N + 1 : ℕ) : ℝ) ^ tau) * b N)))
        atTop (nhds 0) := by
      simpa only [zero_mul, mul_zero] using
        Filter.Tendsto.const_mul cUpper (hdecay.mul hb)
    have hevent : ∀ᶠ N : ℕ in atTop,
        (((2 * N + 1 : ℕ) : ℝ) ^ sigma) * a N ≤
          cUpper *
            ((((2 * N + 1 : ℕ) : ℝ) ^ (sigma - tau)) *
              ((((2 * N + 1 : ℕ) : ℝ) ^ tau) * b N)) := by
      filter_upwards [hcomp] with N hN
      let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
      have hx : 0 < x := by dsimp [x]; positivity
      calc
        x ^ sigma * a N ≤ x ^ sigma * (cUpper * b N) :=
          mul_le_mul_of_nonneg_left hN.2 (Real.rpow_nonneg hx.le _)
        _ = cUpper * (x ^ (sigma - tau) * (x ^ tau * b N)) := by
          rw [show x ^ (sigma - tau) * (x ^ tau * b N) =
            x ^ sigma * b N by
              rw [← mul_assoc, ← Real.rpow_add hx]
              congr 2
              ring]
          ring
    have hle := le_of_tendsto_of_tendsto ha hright hevent
    linarith
  · exact heq
  · exfalso
    have hdecay : Tendsto (fun N : ℕ =>
        ((2 * N + 1 : ℕ) : ℝ) ^ (tau - sigma))
        atTop (nhds 0) := by
      simpa only [Complex.ofReal_re,
        show tau - sigma = -(sigma - tau) by ring] using
        (tendsto_pairedEtaOddEndpoint_rpow_zero
          (s := ((sigma - tau : ℝ) : ℂ)) (by simpa using hgt))
    have hleft : Tendsto (fun N : ℕ =>
        cLower *
          ((((2 * N + 1 : ℕ) : ℝ) ^ tau) * b N))
        atTop (nhds (cLower * (1 / 2))) :=
      Filter.Tendsto.const_mul cLower hb
    have hright : Tendsto (fun N : ℕ =>
        (((2 * N + 1 : ℕ) : ℝ) ^ (tau - sigma)) *
          ((((2 * N + 1 : ℕ) : ℝ) ^ sigma) * a N))
        atTop (nhds 0) := by
      simpa only [zero_mul] using hdecay.mul ha
    have hevent : ∀ᶠ N : ℕ in atTop,
        cLower *
            ((((2 * N + 1 : ℕ) : ℝ) ^ tau) * b N) ≤
          (((2 * N + 1 : ℕ) : ℝ) ^ (tau - sigma)) *
            ((((2 * N + 1 : ℕ) : ℝ) ^ sigma) * a N) := by
      filter_upwards [hcomp] with N hN
      let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
      have hx : 0 < x := by dsimp [x]; positivity
      calc
        cLower * (x ^ tau * b N) = x ^ tau * (cLower * b N) := by ring
        _ ≤ x ^ tau * a N :=
          mul_le_mul_of_nonneg_left hN.1 (Real.rpow_nonneg hx.le _)
        _ = x ^ (tau - sigma) * (x ^ sigma * a N) := by
          rw [show x ^ (tau - sigma) * (x ^ sigma * a N) =
            x ^ tau * a N by
              rw [← mul_assoc, ← Real.rpow_add hx]
              congr 2
              ring]
    have hle := le_of_tendsto_of_tendsto hleft hright hevent
    linarith

/-- Eventual two-sided multiplicative comparability of the raw eta-gap errors
at a zero and its functional-equation partner. -/
def EtaGapComplementaryErrorsEventuallyComparable
    (rho : NontrivialZetaZero) : Prop :=
  ∃ cLower cUpper : ℝ,
      0 < cLower ∧ 0 < cUpper ∧
        ∀ᶠ N : ℕ in atTop,
          cLower *
              ‖pairedEtaGapCorePartialSum N
                (NontrivialZetaZero.conjugatePartner rho).1 - 1‖ ≤
            ‖pairedEtaGapCorePartialSum N rho.1 - 1‖ ∧
          ‖pairedEtaGapCorePartialSum N rho.1 - 1‖ ≤
            cUpper *
              ‖pairedEtaGapCorePartialSum N
                (NontrivialZetaZero.conjugatePartner rho).1 - 1‖

/-- Any independent eventual two-sided comparability of the complementary
finite eta-gap errors forces a nontrivial zeta zero onto the critical line. -/
theorem nontrivialZetaZero_re_eq_half_of_etaGapErrors_eventually_comparable
    (rho : NontrivialZetaZero)
    (hcomp : EtaGapComplementaryErrorsEventuallyComparable rho) :
    rho.1.re = 1 / 2 := by
  have heq := eq_of_oddEndpoint_scaled_limits_of_eventually_comparable
    (tendsto_nontrivialZetaZero_etaGapErrorNorm_mul_oddEndpoint_rpow_half rho)
    (tendsto_nontrivialZetaZero_etaGapErrorNorm_mul_oddEndpoint_rpow_half
      (NontrivialZetaZero.conjugatePartner rho))
    hcomp
  simp only [NontrivialZetaZero.conjugatePartner_coe,
    Complex.one_re, Complex.sub_re, Complex.conj_re] at heq
  linarith

/-- The global comparability principle whose missing unconditional proof
would close the eta-gap branch. -/
def AllEtaGapComplementaryErrorsEventuallyComparable : Prop :=
  ∀ rho : NontrivialZetaZero,
    EtaGapComplementaryErrorsEventuallyComparable rho

/-- Exact conditional endpoint: the global complementary-error comparability
principle implies Mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_allEtaGapComplementaryErrorsEventuallyComparable
    (hcomp : AllEtaGapComplementaryErrorsEventuallyComparable) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_spectralCoordinate_real]
  intro s hs hnontrivial hone
  let rho : NontrivialZetaZero := ⟨s, hs, hnontrivial, hone⟩
  exact (zetaSpectralCoordinate_im_eq_zero_iff s).2
    (nontrivialZetaZero_re_eq_half_of_etaGapErrors_eventually_comparable
      rho (hcomp rho))

/-- Under RH, each zero equals its critical-line-reflected partner, so the
two raw eta-gap error sequences are identically equal. -/
theorem allEtaGapComplementaryErrorsEventuallyComparable_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    AllEtaGapComplementaryErrorsEventuallyComparable := by
  intro rho
  have him : (zetaSpectralCoordinate rho.1).im = 0 :=
    (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
      rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
  have hre : rho.1.re = 1 / 2 :=
    (zetaSpectralCoordinate_im_eq_zero_iff rho.1).1 him
  have hpartner : NontrivialZetaZero.conjugatePartner rho = rho := by
    apply Subtype.ext
    apply Complex.ext
    · simp only [NontrivialZetaZero.conjugatePartner_coe,
        Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · simp only [NontrivialZetaZero.conjugatePartner_coe,
        Complex.sub_im, Complex.one_im, Complex.conj_im]
      ring
  rw [EtaGapComplementaryErrorsEventuallyComparable, hpartner]
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  exact Eventually.of_forall fun N => ⟨by simp, by simp⟩

/-- The global complementary eta-gap comparability principle is exactly
equivalent to RH. Its open direction is therefore conjecture-strength, not
a routine tail estimate. -/
theorem riemannHypothesis_iff_allEtaGapComplementaryErrorsEventuallyComparable :
    RiemannHypothesis ↔
      AllEtaGapComplementaryErrorsEventuallyComparable := by
  constructor
  · exact allEtaGapComplementaryErrorsEventuallyComparable_of_riemannHypothesis
  · exact riemannHypothesis_of_allEtaGapComplementaryErrorsEventuallyComparable

end

end RiemannGaussian
