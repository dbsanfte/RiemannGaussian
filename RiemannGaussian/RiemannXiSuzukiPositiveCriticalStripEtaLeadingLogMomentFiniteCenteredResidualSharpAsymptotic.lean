import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredTailSharpAsymptotic

/-!
# Sharp off-line asymptotics of the completed centered eta residual

The completed centered residual is exactly the sum of two literal eta tails,
evaluated at a nontrivial zero and its same-ordinate reflected partner.  The
sharp centered-tail theorem gives those two terms the horizontal rates
`Re rho` and `1 - Re rho`, with nonzero limiting constants.

If `Re rho > 1/2`, the partner tail is the slower term.  Scaling the exact
residual by that rate makes the original tail tend to zero while the partner
tail tends to a strictly positive norm.  Consequently the actual complex
residual, not just its upper envelope, is eventually nonzero.  This is an
unconditional rate-separation theorem for a hypothetical off-line zero; it
does not rule such a zero out without an additional arithmetic constraint on
the finite residual work law.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A centered tail scaled at any strictly smaller horizontal exponent tends
to zero. -/
theorem
    tendsto_oddEndpoint_smaller_rpow_mul_norm_pairedEtaLogLaplaceMomentCutoffCenteredTail_zero
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) {tau : ℝ} (htau : tau < s.re) :
    Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) ^ tau) *
        ‖pairedEtaLogLaplaceMomentCutoffCenteredTail k s N‖)
      atTop (nhds 0) := by
  have hdecay : Tendsto (fun N : ℕ =>
      ((2 * N + 1 : ℕ) : ℝ) ^ (tau - s.re))
      atTop (nhds 0) := by
    simpa only [Complex.ofReal_re,
      show tau - s.re = -(s.re - tau) by ring] using
      (tendsto_pairedEtaOddEndpoint_rpow_zero
        (s := ((s.re - tau : ℝ) : ℂ)) (by simpa using htau))
  have hsharp :=
    tendsto_oddEndpoint_rpow_mul_norm_pairedEtaLogLaplaceMomentCutoffCenteredTail
      k hs
  have hproduct := hdecay.mul hsharp
  simpa only [zero_mul] using hproduct.congr' (Eventually.of_forall fun N => by
    let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
    have hx : 0 < x := by dsimp [x]; positivity
    change x ^ (tau - s.re) *
        (x ^ s.re *
          ‖pairedEtaLogLaplaceMomentCutoffCenteredTail k s N‖) =
      x ^ tau *
        ‖pairedEtaLogLaplaceMomentCutoffCenteredTail k s N‖
    rw [← mul_assoc, ← Real.rpow_add hx]
    congr 2
    ring)

/-- The positive limiting magnitude of the partner term in the completed
centered residual. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualSharpLimit
    (rho : NontrivialZetaZero) : ℝ :=
  pairedEtaCompletionSpectralWeight
      (NontrivialZetaZero.conjugatePartner rho) *
    ‖(((analyticZetaZeroMultiplicity rho).factorial : ℕ) : ℂ) *
      ((NontrivialZetaZero.conjugatePartner rho).1 ^
        (analyticZetaZeroMultiplicity rho + 1))⁻¹ / 2‖

/-- The partner residual's sharp limiting magnitude is strictly positive. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualSharpLimit_pos
    (rho : NontrivialZetaZero) :
    0 <
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualSharpLimit
        rho := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualSharpLimit
  exact mul_pos
    (pairedEtaCompletionSpectralWeight_pos
      (NontrivialZetaZero.conjugatePartner rho))
    (pairedEtaCenteredTailAsymptoticValue_norm_pos
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho)))

/-- For a hypothetical zero strictly to the right of the critical line, the
actual completed centered residual has the slower partner-tail asymptotic with
a strictly positive limiting magnitude. -/
theorem
    tendsto_oddEndpoint_partner_rpow_mul_norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) ^
          (NontrivialZetaZero.conjugatePartner rho).1.re) *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N‖)
      atTop
      (nhds
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualSharpLimit
          rho)) := by
  let m : ℕ := analyticZetaZeroMultiplicity rho
  let partner : NontrivialZetaZero :=
    NontrivialZetaZero.conjugatePartner rho
  let dominant : ℕ → ℂ := fun N =>
    -(pairedEtaXiCompletionFactor partner.1 * partner.1 *
      pairedEtaLogLaplaceMomentCutoffCenteredTail m partner.1 N)
  let remainder : ℕ → ℂ := fun N =>
    (-1 : ℂ) ^ m *
      starRingEnd ℂ
        (pairedEtaXiCompletionFactor rho.1 * rho.1 *
          pairedEtaLogLaplaceMomentCutoffCenteredTail m rho.1 N)
  have hpartnerPos : 0 < partner.1.re := by
    exact NontrivialZetaZero.zero_lt_re partner
  have hpartnerLt : partner.1.re < rho.1.re := by
    have h : 1 - rho.1.re < rho.1.re := by linarith
    simpa [partner, NontrivialZetaZero.conjugatePartner_coe] using h
  have hdominantTail :=
    tendsto_oddEndpoint_rpow_mul_norm_pairedEtaLogLaplaceMomentCutoffCenteredTail
      m hpartnerPos
  have hdominant : Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) ^ partner.1.re) * ‖dominant N‖)
      atTop
      (nhds
        (pairedEtaCompletionSpectralWeight partner *
          ‖((m.factorial : ℕ) : ℂ) *
            (partner.1 ^ (m + 1))⁻¹ / 2‖)) := by
    have hweighted := Filter.Tendsto.const_mul
      (pairedEtaCompletionSpectralWeight partner) hdominantTail
    convert hweighted using 1
    funext N
    unfold dominant pairedEtaCompletionSpectralWeight
    simp only [norm_neg, norm_mul]
    ring
  have hremainderTail :=
    tendsto_oddEndpoint_smaller_rpow_mul_norm_pairedEtaLogLaplaceMomentCutoffCenteredTail_zero
      m (NontrivialZetaZero.zero_lt_re rho) hpartnerLt
  have hremainder : Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) ^ partner.1.re) * ‖remainder N‖)
      atTop (nhds 0) := by
    have hweighted := Filter.Tendsto.const_mul
      (pairedEtaCompletionSpectralWeight rho) hremainderTail
    simpa only [mul_zero] using hweighted.congr' (Eventually.of_forall fun N => by
      unfold remainder pairedEtaCompletionSpectralWeight
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        norm_conj]
      ring)
  have hresidual (N : ℕ) :
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N =
        dominant N + remainder N := by
    simpa only [m, partner, dominant, remainder] using
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_tails
        rho N
  have hlower (N : ℕ) :
      (((2 * N + 1 : ℕ) : ℝ) ^ partner.1.re) * ‖dominant N‖ -
          (((2 * N + 1 : ℕ) : ℝ) ^ partner.1.re) * ‖remainder N‖ ≤
        (((2 * N + 1 : ℕ) : ℝ) ^ partner.1.re) *
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N‖ := by
    let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
    have hx : 0 < x := by dsimp [x]; positivity
    have hreverse : ‖dominant N‖ - ‖remainder N‖ ≤
        ‖dominant N + remainder N‖ := by
      simpa only [norm_neg, sub_neg_eq_add] using
        (norm_sub_norm_le (dominant N) (-remainder N))
    calc
      x ^ partner.1.re * ‖dominant N‖ -
            x ^ partner.1.re * ‖remainder N‖ =
          x ^ partner.1.re * (‖dominant N‖ - ‖remainder N‖) := by ring
      _ ≤ x ^ partner.1.re * ‖dominant N + remainder N‖ :=
        mul_le_mul_of_nonneg_left hreverse (Real.rpow_nonneg hx.le _)
      _ = x ^ partner.1.re *
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N‖ := by
        rw [hresidual]
  have hupper (N : ℕ) :
      (((2 * N + 1 : ℕ) : ℝ) ^ partner.1.re) *
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N‖ ≤
        (((2 * N + 1 : ℕ) : ℝ) ^ partner.1.re) * ‖dominant N‖ +
          (((2 * N + 1 : ℕ) : ℝ) ^ partner.1.re) * ‖remainder N‖ := by
    let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
    have hx : 0 < x := by dsimp [x]; positivity
    rw [hresidual]
    calc
      x ^ partner.1.re * ‖dominant N + remainder N‖ ≤
          x ^ partner.1.re * (‖dominant N‖ + ‖remainder N‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _)
          (Real.rpow_nonneg hx.le _)
      _ = x ^ partner.1.re * ‖dominant N‖ +
          x ^ partner.1.re * ‖remainder N‖ := by ring
  have hlowerT : Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) ^ partner.1.re) * ‖dominant N‖ -
        (((2 * N + 1 : ℕ) : ℝ) ^ partner.1.re) * ‖remainder N‖)
      atTop
      (nhds
        (pairedEtaCompletionSpectralWeight partner *
          ‖((m.factorial : ℕ) : ℂ) *
            (partner.1 ^ (m + 1))⁻¹ / 2‖)) := by
    simpa only [sub_zero] using hdominant.sub hremainder
  have hupperT : Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) ^ partner.1.re) * ‖dominant N‖ +
        (((2 * N + 1 : ℕ) : ℝ) ^ partner.1.re) * ‖remainder N‖)
      atTop
      (nhds
        (pairedEtaCompletionSpectralWeight partner *
          ‖((m.factorial : ℕ) : ℂ) *
            (partner.1 ^ (m + 1))⁻¹ / 2‖)) := by
    simpa only [add_zero] using hdominant.add hremainder
  have hsqueezed := hlowerT.squeeze hupperT hlower hupper
  simpa only [sub_zero, add_zero, m, partner,
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualSharpLimit] using
    hsqueezed

/-- A hypothetical right-half off-line zero forces the actual completed
centered residual to be nonzero at every sufficiently large cutoff. -/
theorem
    eventually_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_ne_zero_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∀ᶠ N : ℕ in atTop,
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N ≠ 0 := by
  have hlimit :=
    tendsto_oddEndpoint_partner_rpow_mul_norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual
      rho hrho
  have hpositive := hlimit.eventually_const_lt
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualSharpLimit_pos
      rho)
  filter_upwards [hpositive] with N hN
  intro hzero
  rw [hzero, norm_zero, mul_zero] at hN
  exact (lt_irrefl 0 hN)

/-- If the original zero is strictly left of the critical line, the residual
sequence attached to its reflected right-half partner is eventually nonzero. -/
theorem
    eventually_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_conjugatePartner_ne_zero_of_re_lt_half
    (rho : NontrivialZetaZero) (hrho : rho.1.re < 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual
        (NontrivialZetaZero.conjugatePartner rho) N ≠ 0 := by
  apply
    eventually_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_ne_zero_of_half_lt_re
  have h : 1 / 2 < 1 - rho.1.re := by linarith
  simpa [NontrivialZetaZero.conjugatePartner_coe] using h

/-- Every complementary pair containing an off-critical-line zero has one
orientation whose actual completed centered residual is eventually nonzero. -/
theorem
    eventually_one_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_ne_zero_of_re_ne_half
    (rho : NontrivialZetaZero) (hrho : rho.1.re ≠ 1 / 2) :
    (∀ᶠ N : ℕ in atTop,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N ≠ 0) ∨
      (∀ᶠ N : ℕ in atTop,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual
          (NontrivialZetaZero.conjugatePartner rho) N ≠ 0) := by
  rcases lt_or_gt_of_ne hrho with hleft | hright
  · exact Or.inr
      (eventually_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_conjugatePartner_ne_zero_of_re_lt_half
        rho hleft)
  · exact Or.inl
      (eventually_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_ne_zero_of_half_lt_re
        rho hright)

end

end RiemannGaussian
