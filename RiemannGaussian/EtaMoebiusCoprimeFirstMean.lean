import RiemannGaussian.EtaMoebiusQuarterQuotientMean
import RiemannGaussian.EtaMoebiusCoprimeGrowth

/-!
# Growing prime exclusion in the quartic complex mean

The direct parity estimate survives every divided window of the odd-prime
sieve. The full low sieve has complex first mean bounded by
`C_rho * P^2 * u^(2-4*Re(rho))` on `D=u^3`, `A=L=u^4` when `P` divides `u`.
The existing explicit growing modulus and scale make this allowance tend
to zero at a hypothetical right-half zero. Thus the surviving complex
first mean still tends to the original nonzero source. These are first-mean
statements; no mean-square or mean-absolute-value extension is inferred.
-/

open Complex Filter
open scoped Classical Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

private theorem selected_divided_firstMean_eq
    (rho : NontrivialZetaZero) {e : ℕ} (he : 0 < e) (S : Finset ℕ) (A : ℕ) :
    (∑ t ∈ Finset.range (e * A), (e : ℂ) ^ (-rho.1) *
      pairedEtaCompletedMoebiusSelectedAggregate rho S ((e * A + t) / e)) / (e * A : ℕ) =
        (e : ℂ) ^ (-rho.1) * pairedEtaCompletedMoebiusSelectedFirstMean rho S A := by
  have hdiv (t : ℕ) : (e * A + t) / e = A + t / e := by
    rw [Nat.add_comm, Nat.add_mul_div_left t A he, Nat.add_comm]
  simp_rw [hdiv]
  rw [← Finset.mul_sum, sum_range_div_blocks
    (fun t ↦ pairedEtaCompletedMoebiusSelectedAggregate rho S (A + t)) he A, nsmul_eq_mul]
  unfold pairedEtaCompletedMoebiusSelectedFirstMean
  push_cast
  by_cases hA : A = 0
  · simp [hA]
  · have heC : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
    have hAC : (A : ℂ) ≠ 0 := by exact_mod_cast hA
    field_simp

/-- Every divided quartic window retains its exact complex dilation, with only a linear cost in the dividing integer. -/
theorem norm_pairedEtaCompletedMoebiusSelectedFirstMean_divided_quartic_le
    (rho : NontrivialZetaZero) {e u : ℕ} (he : 1 ≤ e) (hu : 1 ≤ u) (heu : e ∣ u)
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 (u ^ 3)) :
    ‖(∑ t ∈ Finset.range (u ^ 4), (e : ℂ) ^ (-rho.1) *
      pairedEtaCompletedMoebiusSelectedAggregate rho S ((u ^ 4 + t) / e)) / (u ^ 4 : ℕ)‖ ≤
        pairedEtaMoebiusFirstMeanConstant rho * e * (u : ℝ) ^ (2 - 4 * rho.1.re) := by
  let A := u ^ 4 / e
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have heu' : e ≤ u := Nat.le_of_dvd hu heu
  have hdvd : e ∣ u ^ 4 := dvd_trans heu ⟨u ^ 3, by ring⟩
  have hA : u ^ 4 = e * A := (Nat.mul_div_cancel' hdvd).symm
  have hDA : u ^ 3 ≤ A := by
    apply (Nat.le_div_iff_mul_le he).mpr
    nlinarith [Nat.mul_le_mul_left (u ^ 3) heu']
  have hAp : 1 ≤ A := (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 3 (by omega))).trans hDA
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hAp
  have hAc : (A : ℝ) = (u : ℝ) ^ 4 / e := by
    apply (eq_div_iff he0.ne').mpr
    have hh : (u : ℝ) ^ 4 = (e : ℝ) * A := by exact_mod_cast hA
    linarith
  have heq := selected_divided_firstMean_eq rho he S A
  rw [← hA] at heq
  rw [heq, norm_mul, Complex.norm_natCast_cpow_of_pos he, Complex.neg_re]
  have hb := norm_pairedEtaCompletedMoebiusSelectedFirstMean_le rho hS hAp hDA
  apply (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (e : ℝ) ^ (-rho.1.re))).trans_eq
  have hpower : (e : ℝ) ^ (-rho.1.re) * (A : ℝ) ^ (-rho.1.re) =
      (u : ℝ) ^ (-4 * rho.1.re) := by
    rw [← Real.mul_rpow he0.le hA0.le]
    have hh : (e : ℝ) * A = (u : ℝ) ^ 4 := by exact_mod_cast hA.symm
    rw [hh, ← Real.rpow_natCast_mul hu0.le]
    congr 1
    ring
  rw [Real.rpow_sub hA0, Real.rpow_one]
  calc
    _ = pairedEtaMoebiusFirstMeanConstant rho * (u : ℝ) ^ 6 *
        ((e : ℝ) ^ (-rho.1.re) * (A : ℝ) ^ (-rho.1.re)) / A := by
      simp only [Nat.cast_pow]
      ring
    _ = pairedEtaMoebiusFirstMeanConstant rho * e *
        ((u : ℝ) ^ 2 * (u : ℝ) ^ (-4 * rho.1.re)) := by
      rw [hpower, hAc]
      field_simp
    _ = _ := by
      rw [show 2 - 4 * rho.1.re = 2 + (-4 * rho.1.re) by ring,
        Real.rpow_add hu0, Real.rpow_ofNat]

/-- The full complex first mean of the coprime low family on the quartic physical window. -/
def pairedEtaMoebiusCoprimeLowQuarticFirstMean
    (rho : NontrivialZetaZero) (P u : ℕ) : ℂ :=
  (∑ t ∈ Finset.range (u ^ 4),
    pairedEtaCompletedMoebiusCoprimeLowAggregate rho P (u ^ 3) (u ^ 4 + t)) / (u ^ 4 : ℕ)

/-- All sieve intersections are bounded together, retaining their actual divisor sum as the first-mean cost. -/
theorem norm_pairedEtaMoebiusCoprimeLowQuarticFirstMean_le_divisors
    (rho : NontrivialZetaZero) {P u : ℕ} (hP : 0 < P) (hodd : Odd P)
    (hu : 1 ≤ u) (hPu : P ∣ u) :
    ‖pairedEtaMoebiusCoprimeLowQuarticFirstMean rho P u‖ ≤
      pairedEtaMoebiusFirstMeanConstant rho * (∑ e ∈ P.divisors, (e : ℝ)) *
        (u : ℝ) ^ (2 - 4 * rho.1.re) := by
  let S := pairedEtaMoebiusCoprimeDivisors P (u ^ 3)
  let f : ℕ → ℕ → ℂ := fun e t ↦ (e : ℂ) ^ (-rho.1) *
    pairedEtaCompletedMoebiusSelectedAggregate rho S ((u ^ 4 + t) / e)
  have heq : pairedEtaMoebiusCoprimeLowQuarticFirstMean rho P u =
      ∑ e ∈ P.divisors, (μ e : ℂ) * ((∑ t ∈ Finset.range (u ^ 4), f e t) / (u ^ 4 : ℕ)) := by
    unfold pairedEtaMoebiusCoprimeLowQuarticFirstMean
    simp_rw [pairedEtaCompletedMoebiusCoprimeLowAggregate_eq_sieve rho hP hodd]
    rw [Finset.sum_comm, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e _
    dsimp only [f, S]
    rw [← mul_div_assoc, Finset.mul_sum]
    simp only [mul_assoc]
  rw [heq]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ e ∈ P.divisors, pairedEtaMoebiusFirstMeanConstant rho * e *
        (u : ℝ) ^ (2 - 4 * rho.1.re) := by
      apply Finset.sum_le_sum
      intro e he
      have hm : ‖(μ e : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := e)
      rw [norm_mul]
      apply (mul_le_mul_of_nonneg_right hm (norm_nonneg _)).trans
      rw [one_mul]
      exact norm_pairedEtaCompletedMoebiusSelectedFirstMean_divided_quartic_le rho
        (Nat.pos_of_mem_divisors he) hu ((Nat.dvd_of_mem_divisors he).trans hPu)
        (pairedEtaMoebiusCoprimeDivisors_subset P (u ^ 3))
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- The complex low mean pays at most a quadratic modulus cost, uniformly in the modulus and physical cutoff. -/
theorem norm_pairedEtaMoebiusCoprimeLowQuarticFirstMean_le
    (rho : NontrivialZetaZero) {P u : ℕ} (hP : 0 < P) (hodd : Odd P)
    (hu : 1 ≤ u) (hPu : P ∣ u) :
    ‖pairedEtaMoebiusCoprimeLowQuarticFirstMean rho P u‖ ≤
      pairedEtaMoebiusFirstMeanConstant rho * (P : ℝ) ^ 2 * (u : ℝ) ^ (2 - 4 * rho.1.re) := by
  have hc : (P.divisors.card : ℝ) ≤ P := by exact_mod_cast Nat.card_divisors_le_self P
  have hs : (∑ e ∈ P.divisors, (e : ℝ)) ≤ (P : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _e ∈ P.divisors, (P : ℝ) := by
        apply Finset.sum_le_sum
        intro e he
        exact_mod_cast Nat.le_of_dvd hP (Nat.dvd_of_mem_divisors he)
      _ = (P.divisors.card : ℝ) * P := by simp
      _ ≤ (P : ℝ) ^ 2 := by nlinarith
  apply (norm_pairedEtaMoebiusCoprimeLowQuarticFirstMean_le_divisors rho hP hodd hu hPu).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (pairedEtaMoebiusFirstMeanConstant_nonneg rho)) (by positivity)

/-- The same explicit scale already used by the quadratic sieve also pays the entire quartic first-mean modulus cost. -/
theorem pairedEtaCoprimeScalePower_firstMean_rate_neg
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    2 + (pairedEtaCoprimeScalePower rho : ℝ) * (2 - 4 * rho.1.re) < 0 := by
  nlinarith [pairedEtaCoprimeScalePower_rate_neg rho hrho]

/-- The full growing low sieve has an explicit power allowance on the quartic window, with every intersection cost included. -/
theorem norm_pairedEtaMoebiusCoprimeLowQuarticFirstMean_growing_le
    (rho : NontrivialZetaZero) (v : ℕ) :
    ‖pairedEtaMoebiusCoprimeLowQuarticFirstMean rho
      (pairedEtaOddSieveModulus v) (pairedEtaCoprimeScale rho v)‖ ≤
        pairedEtaMoebiusFirstMeanConstant rho * (pairedEtaOddSieveModulus v : ℝ) ^
          (2 + (pairedEtaCoprimeScalePower rho : ℝ) * (2 - 4 * rho.1.re)) := by
  apply (norm_pairedEtaMoebiusCoprimeLowQuarticFirstMean_le rho
    (pairedEtaOddSieveModulus_pos v) (pairedEtaOddSieveModulus_odd v)
    (pairedEtaCoprimeScale_pos rho v) (pairedEtaOddSieveModulus_dvd_scale rho v)).trans_eq
  have hP : (0 : ℝ) < pairedEtaOddSieveModulus v := by
    exact_mod_cast pairedEtaOddSieveModulus_pos v
  simp only [pairedEtaCoprimeScale, Nat.cast_pow]
  rw [Real.rpow_add hP, Real.rpow_ofNat, Real.rpow_natCast_mul hP.le]
  ring

/-- The whole low complex mean vanishes while every fixed odd prime is eventually excluded along the quartic physical windows. -/
theorem pairedEtaMoebiusCoprimeLowQuarticFirstMean_growing_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun v ↦ pairedEtaMoebiusCoprimeLowQuarticFirstMean rho
      (pairedEtaOddSieveModulus v) (pairedEtaCoprimeScale rho v)) atTop (𝓝 0) := by
  let a := 2 + (pairedEtaCoprimeScalePower rho : ℝ) * (2 - 4 * rho.1.re)
  have ha : a < 0 := pairedEtaCoprimeScalePower_firstMean_rate_neg rho hrho
  have ht : Tendsto (fun v ↦ (pairedEtaOddSieveModulus v : ℝ) ^ a) atTop (𝓝 0) := by
    simpa only [neg_neg, Function.comp_def] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr ha)).comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp pairedEtaOddSieveModulus_tendsto_atTop)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ norm_nonneg _)
    (norm_pairedEtaMoebiusCoprimeLowQuarticFirstMean_growing_le rho)
  simpa only [mul_zero] using ht.const_mul (pairedEtaMoebiusFirstMeanConstant rho)

/-- The unchanged coprime product prefix is averaged as one complex sum over the entire quartic window. -/
def pairedEtaMoebiusCoprimeQuarticFirstMean
    (rho : NontrivialZetaZero) (P u : ℕ) : ℂ :=
  (∑ t ∈ Finset.range (u ^ 4),
    pairedEtaCompletedMoebiusCoprimeAggregate rho P (u ^ 3) (u ^ 4 + t)) / (u ^ 4 : ℕ)

/-- All prime exclusions preserve the original source in the complex mean, with the actual low sieve subtracted exactly. -/
theorem pairedEtaMoebiusCoprimeQuarticFirstMean_eq_source_sub
    (rho : NontrivialZetaZero) {P u : ℕ} (hodd : Odd P) (hu : 2 ≤ u) :
    pairedEtaMoebiusCoprimeQuarticFirstMean rho P u = pairedEtaCompletedMoebiusSource rho -
      pairedEtaMoebiusCoprimeLowQuarticFirstMean rho P u := by
  have huC : ((u ^ 4 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 4 (by omega : u ≠ 0)
  have hM : 2 ≤ u ^ 4 := hu.trans (Nat.le_self_pow (by decide : 4 ≠ 0) u)
  have hD : u ^ 3 ≤ u ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hh : pairedEtaMoebiusCoprimeLowQuarticFirstMean rho P u +
      pairedEtaMoebiusCoprimeQuarticFirstMean rho P u = pairedEtaCompletedMoebiusSource rho := by
    unfold pairedEtaMoebiusCoprimeLowQuarticFirstMean pairedEtaMoebiusCoprimeQuarticFirstMean
    rw [← add_div, ← Finset.sum_add_distrib]
    simp_rw [pairedEtaCompletedMoebiusCoprimeLow_add_coprime_eq_source rho hodd
      (hM.trans (Nat.le_add_right _ _)) (hD.trans (Nat.le_add_right _ _))]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  linear_combination hh

/-- The source error for the whole surviving first mean has the explicit uniform quadratic modulus budget. -/
theorem norm_pairedEtaMoebiusCoprimeQuarticFirstMean_sub_source_le
    (rho : NontrivialZetaZero) {P u : ℕ} (hP : 0 < P) (hodd : Odd P)
    (hu : 2 ≤ u) (hPu : P ∣ u) :
    ‖pairedEtaMoebiusCoprimeQuarticFirstMean rho P u - pairedEtaCompletedMoebiusSource rho‖ ≤
      pairedEtaMoebiusFirstMeanConstant rho * (P : ℝ) ^ 2 * (u : ℝ) ^ (2 - 4 * rho.1.re) := by
  rw [pairedEtaMoebiusCoprimeQuarticFirstMean_eq_source_sub rho hodd hu,
    sub_sub_cancel_left, norm_neg]
  exact norm_pairedEtaMoebiusCoprimeLowQuarticFirstMean_le rho hP hodd (by omega) hPu

/-- The surviving complex first mean still tends to the nonzero source after a simultaneous growing prime sieve on quartic windows. -/
theorem pairedEtaMoebiusCoprimeQuarticFirstMean_growing_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun v ↦ pairedEtaMoebiusCoprimeQuarticFirstMean rho
      (pairedEtaOddSieveModulus v) (pairedEtaCoprimeScale rho v))
        atTop (𝓝 (pairedEtaCompletedMoebiusSource rho)) := by
  have ht := (tendsto_const_nhds (x := pairedEtaCompletedMoebiusSource rho)).sub
    (pairedEtaMoebiusCoprimeLowQuarticFirstMean_growing_tendsto_zero rho hrho)
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [(pairedEtaCoprimeScale_tendsto_atTop rho).eventually (eventually_ge_atTop 2)] with v hv
  exact (pairedEtaMoebiusCoprimeQuarticFirstMean_eq_source_sub rho (pairedEtaOddSieveModulus_odd v) hv).symm

/-- Removing the entire growing prime family changes the original quartic first mean by a quantity tending to zero; this assertion concerns the complex mean alone. -/
theorem pairedEtaCompletedMoebiusLargeFirstMean_sub_growingCoprime_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun v ↦ pairedEtaCompletedMoebiusLargeFirstMean rho
        ((pairedEtaCoprimeScale rho v) ^ 4) ((pairedEtaCoprimeScale rho v) ^ 3) -
      pairedEtaMoebiusCoprimeQuarticFirstMean rho
        (pairedEtaOddSieveModulus v) (pairedEtaCoprimeScale rho v)) atTop (𝓝 0) := by
  simpa only [sub_self, Function.comp_def] using
    ((pairedEtaCompletedMoebiusLargeFirstMean_quartic_tendsto_source rho hrho).comp
      (pairedEtaCoprimeScale_tendsto_atTop rho)).sub
      (pairedEtaMoebiusCoprimeQuarticFirstMean_growing_tendsto_source rho hrho)

end

end RiemannGaussian
