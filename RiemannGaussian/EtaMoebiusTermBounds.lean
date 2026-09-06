import RiemannGaussian.EtaMoebiusCompletedTail

/-!
# Quantitative bounds for the actual Möbius-completed eta terms

Every summand retains its complex divisor phase, genuine completed tail,
and possible odd endpoint. The actual zero equation bounds an unpaired
prefix by its endpoint decay. The integer division inequalities then give
one explicit bound, uniform over all divisors at the same cutoff.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- At an actual zero, the unpaired eta prefix has endpoint decay,
including its possible last odd term. -/
theorem norm_pairedEtaUnpairedDirichletPrefix_le (rho : NontrivialZetaZero)
    {M : ℕ} (hM : 1 ≤ M) :
    ‖pairedEtaUnpairedDirichletPrefix M rho.1‖ ≤
      (‖rho.1‖ / rho.1.re + 1) * (M : ℝ) ^ (-rho.1.re) := by
  have hs := NontrivialZetaZero.zero_lt_re rho
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hep : (M : ℝ) ≤ (2 * (M / 2) + 1 : ℕ) := by
    exact_mod_cast (show M ≤ 2 * (M / 2) + 1 by omega)
  have hdecay := Real.rpow_le_rpow_of_nonpos hMp hep (neg_nonpos.mpr hs.le)
  have hp := norm_pairedEtaCorePartialSum_nontrivialZetaZero_le rho (M / 2)
  have ho : ‖(if Odd M then (M : ℂ) ^ (-rho.1) else 0)‖ ≤ (M : ℝ) ^ (-rho.1.re) := by
    split_ifs
    · exact (by simpa only [Complex.ofReal_natCast, Complex.neg_re] using
        (Complex.norm_cpow_eq_rpow_re_of_pos hMp (-rho.1)).le)
    · simpa using Real.rpow_nonneg hMp.le (-rho.1.re)
  rw [pairedEtaUnpairedDirichletPrefix_eq_paired_add_endpoint]
  calc
    _ ≤ ‖pairedEtaCorePartialSum (M / 2) rho.1‖ +
        ‖(if Odd M then (M : ℂ) ^ (-rho.1) else 0)‖ := norm_add_le _ _
    _ ≤ ‖rho.1‖ * (((2 * (M / 2) + 1 : ℕ) : ℝ) ^ (-rho.1.re) / rho.1.re) +
        (M : ℝ) ^ (-rho.1.re) := add_le_add hp ho
    _ ≤ ‖rho.1‖ * ((M : ℝ) ^ (-rho.1.re) / rho.1.re) +
        (M : ℝ) ^ (-rho.1.re) :=
      add_le_add (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hdecay hs.le) (norm_nonneg _)) le_rfl
    _ = _ := by ring

/-- The original signed complex divisor term, before any norm or
quadratic compression. Its divided cutoff and odd endpoint are literal. -/
def pairedEtaCompletedMoebiusTerm (rho : NontrivialZetaZero) (M d : ℕ) : ℂ :=
  (μ d : ℂ) * (d : ℂ) ^ (-rho.1) *
    (-pairedEtaCompletedMomentTail rho ((M / d) / 2) 0 + pairedEtaCompletedOddEndpoint rho (M / d))

/-- The genuine tail term is exactly the completion-weighted unpaired
eta prefix, with the same complex Möbius weight. -/
theorem pairedEtaCompletedMoebiusTerm_eq_completed_prefix (rho : NontrivialZetaZero) (M d : ℕ) :
    pairedEtaCompletedMoebiusTerm rho M d =
      (μ d : ℂ) * (d : ℂ) ^ (-rho.1) *
        (pairedEtaXiCompletionFactor rho.1 * pairedEtaUnpairedDirichletPrefix (M / d) rho.1) := by
  rw [pairedEtaUnpairedDirichletPrefix_eq_paired_add_endpoint]
  unfold pairedEtaCompletedMoebiusTerm
  rw [← pairedEtaFiniteCompletedMoment_eq_neg_tail rho (analyticZetaZeroMultiplicity_positive rho),
    pairedEtaFiniteCompletedMoment_zero_eq_completed_prefix]
  unfold pairedEtaCompletedOddEndpoint
  ring

/-- The retained divisor terms sum to the existing actual tail aggregate. -/
theorem sum_pairedEtaCompletedMoebiusTerm (rho : NontrivialZetaZero) (M : ℕ) :
    (∑ d ∈ Finset.Icc 1 M, pairedEtaCompletedMoebiusTerm rho M d) =
      pairedEtaCompletedMoebiusTailAggregate rho M := rfl

/-- The product of a divisor and its positive divided cutoff is at least
half the original cutoff. This includes every endpoint divisor. -/
theorem half_le_mul_nat_div {M d : ℕ} (hd : 1 ≤ d) (hdM : d ≤ M) :
    (M : ℝ) / 2 ≤ (d : ℝ) * (M / d : ℕ) := by
  have hq : 1 ≤ M / d := (Nat.le_div_iff_mul_le hd).2 (by simpa using hdM)
  have hr := Nat.mod_lt M hd
  have hsplit := Nat.div_add_mod M d
  have hnat : M ≤ 2 * (d * (M / d)) := by nlinarith
  have hreal : (M : ℝ) ≤ 2 * ((d : ℝ) * (M / d : ℕ)) := by exact_mod_cast hnat
  linarith

/-- An explicit cutoff-independent coefficient for all original completed
Möbius terms at a fixed actual zero. -/
def pairedEtaCompletedMoebiusTermConstant (rho : NontrivialZetaZero) : ℝ :=
  ‖pairedEtaXiCompletionFactor rho.1‖ * (‖rho.1‖ / rho.1.re + 1) * (2 : ℝ) ^ rho.1.re

/-- The divisor-term coefficient is strictly positive at an actual zero. -/
theorem pairedEtaCompletedMoebiusTermConstant_pos (rho : NontrivialZetaZero) :
    0 < pairedEtaCompletedMoebiusTermConstant rho := by
  have hs := NontrivialZetaZero.zero_lt_re rho
  have hX := norm_pos_iff.mpr
    (pairedEtaXiCompletionFactor_ne_zero hs (NontrivialZetaZero.re_lt_one rho))
  unfold pairedEtaCompletedMoebiusTermConstant
  positivity

/-- Every literal completed divisor term decays at the original cutoff
scale, uniformly in the divisor. The zero equation, complex-power norm,
and integer division estimate discharge all analytic and arithmetic inputs. -/
theorem norm_pairedEtaCompletedMoebiusTerm_le (rho : NontrivialZetaZero)
    {M d : ℕ} (hd : d ∈ Finset.Icc 1 M) :
    ‖pairedEtaCompletedMoebiusTerm rho M d‖ ≤
      pairedEtaCompletedMoebiusTermConstant rho * (M : ℝ) ^ (-rho.1.re) := by
  obtain ⟨hdp, hdM⟩ := Finset.mem_Icc.mp hd
  have hq : 1 ≤ M / d := (Nat.le_div_iff_mul_le hdp).2 (by simpa using hdM)
  have hs := NontrivialZetaZero.zero_lt_re rho
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdp
  have hqR : (0 : ℝ) < (M / d : ℕ) := by exact_mod_cast hq
  have hMR : (0 : ℝ) < M := by exact_mod_cast (hdp.trans hdM)
  have hmu : ‖(μ d : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_intCast] using
      (show (|μ d| : ℝ) ≤ 1 by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d)))
  have hpow : ‖(d : ℂ) ^ (-rho.1)‖ = (d : ℝ) ^ (-rho.1.re) := by
    simpa only [Complex.ofReal_natCast, Complex.neg_re] using
      Complex.norm_cpow_eq_rpow_re_of_pos hdR (-rho.1)
  have hprod : (d : ℝ) ^ (-rho.1.re) * ((M / d : ℕ) : ℝ) ^ (-rho.1.re) ≤
      (2 : ℝ) ^ rho.1.re * (M : ℝ) ^ (-rho.1.re) := by
    rw [← Real.mul_rpow hdR.le hqR.le]
    calc
      _ ≤ ((M : ℝ) / 2) ^ (-rho.1.re) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (half_le_mul_nat_div hdp hdM) (neg_nonpos.mpr hs.le)
      _ = _ := by
        rw [Real.div_rpow hMR.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
        ring
  rw [pairedEtaCompletedMoebiusTerm_eq_completed_prefix, norm_mul, norm_mul, norm_mul, hpow]
  calc
    _ ≤ 1 * (d : ℝ) ^ (-rho.1.re) *
        (‖pairedEtaXiCompletionFactor rho.1‖ *
          ((‖rho.1‖ / rho.1.re + 1) * ((M / d : ℕ) : ℝ) ^ (-rho.1.re))) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hmu (Real.rpow_nonneg hdR.le _))
        (mul_le_mul_of_nonneg_left (norm_pairedEtaUnpairedDirichletPrefix_le rho hq) (norm_nonneg _))
        (by positivity) (by positivity)
    _ = (‖pairedEtaXiCompletionFactor rho.1‖ * (‖rho.1‖ / rho.1.re + 1)) *
        ((d : ℝ) ^ (-rho.1.re) * ((M / d : ℕ) : ℝ) ^ (-rho.1.re)) := by ring
    _ ≤ (‖pairedEtaXiCompletionFactor rho.1‖ * (‖rho.1‖ / rho.1.re + 1)) *
        ((2 : ℝ) ^ rho.1.re * (M : ℝ) ^ (-rho.1.re)) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by unfold pairedEtaCompletedMoebiusTermConstant; ring

end

end RiemannGaussian
