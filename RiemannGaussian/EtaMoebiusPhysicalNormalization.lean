import RiemannGaussian.EtaMoebiusSignedFamily
import RiemannGaussian.EtaOddPowerQuadrature

/-!
# Removing the individual endpoint powers from completed divisor terms

Each literal divisor endpoint lies within one divisor length of the physical
cutoff and above half that cutoff. The existing complex-power derivative
bound therefore compares its full phase to the common physical power.
Multiplying by the original completed term gives a uniform error for every
physical divisor, with its size and the cutoff retained.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Every actual divisor endpoint stays above half the physical cutoff
and differs from that cutoff by at most one divisor length. -/
theorem pairedEtaDivisorOddEndpoint_physical_bounds {M d : ℕ}
    (hd : d ∈ Finset.Icc 1 M) :
    (M : ℝ) / 2 ≤ (d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) ∧
      |(M : ℝ) - (d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ)| ≤ d := by
  obtain ⟨hdp, hdM⟩ := Finset.mem_Icc.mp hd
  have hq := pairedEtaUnpairedOddEndpoint_bounds (M / d)
  have hr := Nat.mod_lt M hdp
  have hsplit := Nat.div_add_mod M d
  have hlo : M ≤ d * pairedEtaUnpairedOddEndpoint (M / d) + d := by nlinarith
  have hhi : d * pairedEtaUnpairedOddEndpoint (M / d) ≤ M + d := by
    calc
      _ ≤ d * (M / d + 1) := Nat.mul_le_mul_left d hq.2.2
      _ = d * (M / d) + d := by ring
      _ ≤ M + d := Nat.add_le_add_right (Nat.mul_div_le M d) d
  constructor
  · have h := half_le_mul_nat_div hdp hdM
    have hm : (d * (M / d) : ℕ) ≤ (d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) :=
      Nat.mul_le_mul_left d hq.2.1
    push_cast at hm ⊢
    exact h.trans (by exact_mod_cast hm)
  · apply abs_le.mpr
    have hloR : (M : ℝ) ≤ (d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) + (d : ℝ) := by
      exact_mod_cast hlo
    have hhiR : (d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) ≤ (M : ℝ) + d := by
      exact_mod_cast hhi
    constructor <;> linarith

/-- The product of the complex-power derivative scale and the actual
term decay is at most twice the inverse physical cutoff. -/
theorem pairedEtaPhysicalEndpointPower_product_le (rho : NontrivialZetaZero)
    {M : ℕ} (hM : 1 ≤ M) :
    ((M : ℝ) / 2) ^ (rho.1.re - 1) * (M : ℝ) ^ (-rho.1.re) ≤ 2 / M := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have heq : ((M : ℝ) / 2) ^ (rho.1.re - 1) * (M : ℝ) ^ (-rho.1.re) =
      (2 : ℝ) ^ (1 - rho.1.re) / M := by
    rw [Real.div_rpow hMR.le (by norm_num), div_mul_eq_mul_div,
      ← Real.rpow_add hMR, show rho.1.re - 1 + -rho.1.re = -1 by ring, Real.rpow_neg_one,
      show rho.1.re - 1 = -(1 - rho.1.re) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
    ring
  rw [heq]
  apply div_le_div_of_nonneg_right _ hMR.le
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (show 1 - rho.1.re ≤ 1 by linarith [NontrivialZetaZero.zero_lt_re rho])
  simpa only [Real.rpow_one] using h

/-- The explicit coefficient for replacing every individual complex
endpoint power by the common physical-cutoff power. -/
def pairedEtaCompletedMoebiusPhysicalErrorConstant (rho : NontrivialZetaZero) : ℝ :=
  2 * ‖rho.1‖ * pairedEtaCompletedMoebiusTermConstant rho

/-- The actual physical normalization error coefficient is nonnegative. -/
theorem pairedEtaCompletedMoebiusPhysicalErrorConstant_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCompletedMoebiusPhysicalErrorConstant rho := by
  have h := (pairedEtaCompletedMoebiusTermConstant_pos rho).le
  unfold pairedEtaCompletedMoebiusPhysicalErrorConstant
  positivity

/-- The complex normalization difference is retained on the original
completed term before any norm is applied. -/
theorem pairedEtaCompletedMoebiusTerm_physical_sub_endpoint
    (rho : NontrivialZetaZero) (M d : ℕ) :
    (M : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusTerm rho M d -
      pairedEtaCompletedMoebiusEndpointPhase rho M d =
      ((M : ℂ) ^ rho.1 -
        ((d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) : ℂ) ^ rho.1) *
          pairedEtaCompletedMoebiusTerm rho M d := by
  unfold pairedEtaCompletedMoebiusEndpointPhase
  ring

/-- Every original completed divisor term can use the common physical
power with an explicit error proportional to `d/M`, over the full physical
divisor range. Both complex powers are compared before taking their norms. -/
theorem norm_pairedEtaCompletedMoebiusTerm_physical_sub_endpoint_le
    (rho : NontrivialZetaZero) {M d : ℕ} (hd : d ∈ Finset.Icc 1 M) :
    ‖(M : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusTerm rho M d -
      pairedEtaCompletedMoebiusEndpointPhase rho M d‖ ≤
      pairedEtaCompletedMoebiusPhysicalErrorConstant rho * d / M := by
  have hM : 1 ≤ M := (Finset.mem_Icc.mp hd).1.trans (Finset.mem_Icc.mp hd).2
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hb := pairedEtaDivisorOddEndpoint_physical_bounds hd
  have hp := norm_cpow_sub_cpow_le_above rho.1 (by positivity : (0 : ℝ) < (M : ℝ) / 2)
    (NontrivialZetaZero.re_lt_one rho).le hb.1 (by linarith : (M : ℝ) / 2 ≤ M)
  have hpow : ‖(M : ℂ) ^ rho.1 -
      ((d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) : ℂ) ^ rho.1‖ ≤
      ‖rho.1‖ * ((M : ℝ) / 2) ^ (rho.1.re - 1) * d := by
    apply le_trans (by simpa only [Complex.ofReal_natCast] using hp)
    exact mul_le_mul_of_nonneg_left hb.2 (by positivity)
  rw [pairedEtaCompletedMoebiusTerm_physical_sub_endpoint, norm_mul]
  calc
    _ ≤ (‖rho.1‖ * ((M : ℝ) / 2) ^ (rho.1.re - 1) * d) *
        (pairedEtaCompletedMoebiusTermConstant rho * (M : ℝ) ^ (-rho.1.re)) :=
      mul_le_mul hpow (norm_pairedEtaCompletedMoebiusTerm_le rho hd) (norm_nonneg _) (by positivity)
    _ = (‖rho.1‖ * pairedEtaCompletedMoebiusTermConstant rho * d) *
        (((M : ℝ) / 2) ^ (rho.1.re - 1) * (M : ℝ) ^ (-rho.1.re)) := by ring
    _ ≤ (‖rho.1‖ * pairedEtaCompletedMoebiusTermConstant rho * d) * (2 / M) := by
      have hC := (pairedEtaCompletedMoebiusTermConstant_pos rho).le
      exact mul_le_mul_of_nonneg_left (pairedEtaPhysicalEndpointPower_product_le rho hM) (by positivity)
    _ = _ := by unfold pairedEtaCompletedMoebiusPhysicalErrorConstant; ring

end

end RiemannGaussian
