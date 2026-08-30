import RiemannGaussian.Hybrid.GeometricPhaseRigidity
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredTailSharpAsymptotic

/-!
# Geometric sampling of the complex eta-tail asymptotic

The sharp centered eta-tail theorem retains its full complex phase at every
odd arithmetic endpoint `2N+1`.  To expose those phases as geometric modes,
this module samples the cutoff at

`N_n = (q^n - 1) / 2`

for an odd natural base `q > 1`.  Lean proves both that these cutoffs tend to
infinity and that their odd endpoints are exactly `q^n`.  The sharp tail
asymptotic therefore becomes a genuine geometric normalization by
`((q : ℂ)^s)^n`.

At a nontrivial zeta zero, every eta moment below the analytic multiplicity
vanishes.  The corresponding finite centered prefix is consequently the
negative of the tail, so it inherits an explicit nonzero complex geometric
asymptotic.  This is the literal eta interface needed before applying finite
geometric-phase rigidity; no collision avoidance between different zeros is
asserted here.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RiemannGaussian

noncomputable section

/-- Cutoff whose odd endpoint is the `n`th power of an odd base. -/
def etaGeometricOddEndpointCutoff (q n : ℕ) : ℕ :=
  (q ^ n - 1) / 2

/-- For an odd base, the sampled cutoff has endpoint exactly `q^n`. -/
theorem etaGeometricOddEndpointCutoff_endpoint
    {q : ℕ} (hqOdd : Odd q) (n : ℕ) :
    2 * etaGeometricOddEndpointCutoff q n + 1 = q ^ n := by
  have hpow : Odd (q ^ n) := hqOdd.pow
  obtain ⟨r, hr⟩ := hpow
  unfold etaGeometricOddEndpointCutoff
  rw [hr]
  omega

/-- Geometrically sampled odd-endpoint cutoffs tend to infinity. -/
theorem tendsto_etaGeometricOddEndpointCutoff_atTop
    {q : ℕ} (hq : 1 < q) :
    Tendsto (etaGeometricOddEndpointCutoff q) atTop atTop := by
  unfold etaGeometricOddEndpointCutoff
  exact (Nat.tendsto_div_const_atTop (by norm_num : 2 ≠ 0)).comp
    ((tendsto_sub_atTop_nat 1).comp
      (tendsto_pow_atTop_atTop_of_one_lt hq))

/-- Complex odd-endpoint powers on the sampled cutoffs are literal powers of
one fixed geometric mode. -/
theorem etaGeometricOddEndpointCutoff_cpow
    {q : ℕ} (hqOdd : Odd q) (s : ℂ) (n : ℕ) :
    (((((2 * etaGeometricOddEndpointCutoff q n + 1 : ℕ) : ℝ) : ℂ)) ^ s) =
      (((q : ℂ) ^ s) ^ n) := by
  rw [etaGeometricOddEndpointCutoff_endpoint hqOdd n]
  norm_cast
  rw [Nat.cast_pow]
  rw [← Complex.natCast_cpow_natCast_mul q n s,
    Complex.cpow_nat_mul]

/-- The sharp complex eta-tail asymptotic sampled at geometric odd
endpoints.  Its normalization is now the `n`th power of one fixed complex
mode. -/
theorem
    tendsto_etaGeometricCutoff_cpow_mul_pairedEtaLogLaplaceMomentCutoffCenteredTail
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) {q : ℕ}
    (hqOdd : Odd q) (hq : 1 < q) :
    Tendsto (fun n : ℕ ↦
      (((q : ℂ) ^ s) ^ n) *
        pairedEtaLogLaplaceMomentCutoffCenteredTail k s
          (etaGeometricOddEndpointCutoff q n))
      atTop
      (nhds (((k.factorial : ℕ) : ℂ) * (s ^ (k + 1))⁻¹ / 2)) := by
  have htail :=
    (tendsto_oddEndpoint_cpow_mul_pairedEtaLogLaplaceMomentCutoffCenteredTail
      k hs).comp (tendsto_etaGeometricOddEndpointCutoff_atTop hq)
  convert htail using 1
  funext n
  simp only [Function.comp_apply]
  rw [etaGeometricOddEndpointCutoff_cpow hqOdd]

/-- The lower-moment geometric asymptotic constant at a nontrivial zero is
nonzero. -/
theorem pairedEtaLowerMomentGeometricAsymptoticValue_ne_zero
    (rho : NontrivialZetaZero) :
    -((((analyticZetaZeroMultiplicity rho - 1).factorial : ℕ) : ℂ) *
        (rho.1 ^ (analyticZetaZeroMultiplicity rho - 1 + 1))⁻¹ / 2) ≠ 0 := by
  apply neg_ne_zero.mpr
  exact norm_pos_iff.mp
    (pairedEtaCenteredTailAsymptoticValue_norm_pos
      (analyticZetaZeroMultiplicity rho - 1)
      (NontrivialZetaZero.zero_lt_re rho))

/-- At a zeta zero, the literal centered prefix one order below the analytic
multiplicity has a nonzero complex geometric asymptotic. -/
theorem
    tendsto_etaGeometricCutoff_cpow_mul_pairedEtaLowerMomentCenteredPartialSum
    (rho : NontrivialZetaZero) {q : ℕ}
    (hqOdd : Odd q) (hq : 1 < q) :
    Tendsto (fun n : ℕ ↦
      (((q : ℂ) ^ rho.1) ^ n) *
        pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
          (analyticZetaZeroMultiplicity rho - 1) rho.1
          (etaGeometricOddEndpointCutoff q n))
      atTop
      (nhds (-((((analyticZetaZeroMultiplicity rho - 1).factorial : ℕ) : ℂ) *
        (rho.1 ^ (analyticZetaZeroMultiplicity rho - 1 + 1))⁻¹ / 2))) := by
  have hk : analyticZetaZeroMultiplicity rho - 1 <
      analyticZetaZeroMultiplicity rho := by
    have hm := analyticZetaZeroMultiplicity_positive rho
    omega
  have htail :=
    tendsto_etaGeometricCutoff_cpow_mul_pairedEtaLogLaplaceMomentCutoffCenteredTail
      (analyticZetaZeroMultiplicity rho - 1)
      (NontrivialZetaZero.zero_lt_re rho) hqOdd hq
  have hneg := htail.neg
  convert hneg using 1
  · funext n
    rw [pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_neg_partial_of_lt_multiplicity
      rho hk (etaGeometricOddEndpointCutoff q n)]
    ring

end

end RiemannGaussian
