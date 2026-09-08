import RiemannGaussian.EtaMoebiusPrimeFirstMean
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Exact harmonic-normalized prime weights

The explicit real weights `p / ((p-1)*(1+H_R))`, with
`H_R = sum_(p<=R, p odd prime) 1/(p-1)`, lie between zero and one.
Their common harmonic normalization tends to infinity. This permits
the growing prime cutoff `floor(u^(2*Re(rho)-1))` at the endpoint of
the direct quadratic cutoff allowance: the weighted prime-class first
mean has norm at most `2*C_rho/(1+H_R)`, which tends to zero.

The full residual keeps every product overlap and still tends to the
original source. These estimates pay for a larger weighted prime family;
they do not bound the remaining signed Moebius residual below the source.
-/

open Complex Filter
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The exact odd-prime harmonic normalizer for the density weights. -/
def pairedEtaPrimeSieveHarmonicMass (R : ℕ) : ℝ :=
  ∑ p ∈ pairedEtaMoebiusOddPrimeMeanFamily R, 1 / ((p : ℝ) - 1)

/-- Every term in the odd-prime harmonic normalizer is nonnegative. -/
theorem pairedEtaPrimeSieveHarmonicMass_nonneg (R : ℕ) :
    0 ≤ pairedEtaPrimeSieveHarmonicMass R := by
  apply Finset.sum_nonneg
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_lt
  positivity

private theorem odd_prime_harmonic_nonsummable :
    ¬ Summable (fun n : ℕ ↦ if n.Prime ∧ Odd n then (1 : ℝ) / ((n : ℝ) - 1) else 0) := by
  intro h
  have hsingle : Summable (fun n : ℕ ↦ if n = 2 then (1 / 2 : ℝ) else 0) := by
    exact (hasSum_ite_eq 2 (1 / 2 : ℝ)).summable
  apply not_summable_one_div_on_primes
  apply (h.add hsingle).of_nonneg_of_le
    (fun n ↦ Set.indicator_nonneg (fun _ _ ↦ by positivity) n)
  intro n
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  by_cases hp : n.Prime
  · rw [if_pos hp]
    rcases hp.eq_two_or_odd' with rfl | hodd
    · norm_num [show ¬Odd (2 : ℕ) by decide]
    · rw [if_pos (show n.Prime ∧ Odd n from ⟨hp, hodd⟩)]
      have hn1 : (1 : ℝ) < n := by exact_mod_cast hp.one_lt
      have hb : (1 : ℝ) / n ≤ 1 / ((n : ℝ) - 1) :=
        one_div_le_one_div_of_le (by linarith) (by linarith)
      exact hb.trans (le_add_of_nonneg_right (by split_ifs <;> positivity))
  · rw [if_neg hp]
    rw [if_neg (show ¬(n.Prime ∧ Odd n) from fun h ↦ hp h.1), zero_add]
    split_ifs <;> positivity

/-- The odd-prime harmonic normalizer diverges by the checked divergence of prime reciprocals. -/
theorem pairedEtaPrimeSieveHarmonicMass_tendsto_atTop :
    Tendsto pairedEtaPrimeSieveHarmonicMass atTop atTop := by
  let f : ℕ → ℝ := fun n ↦ if n.Prime ∧ Odd n then 1 / ((n : ℝ) - 1) else 0
  have hf (n : ℕ) : 0 ≤ f n := by
    dsimp only [f]
    split_ifs with hn
    · have hn1 : (1 : ℝ) < n := by exact_mod_cast hn.1.one_lt
      positivity
    · positivity
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf).mp odd_prime_harmonic_nonsummable
  have he (R : ℕ) : (∑ n ∈ Finset.range (R + 1), f n) = pairedEtaPrimeSieveHarmonicMass R := by
    induction R with
    | zero => simp [f, pairedEtaPrimeSieveHarmonicMass, pairedEtaMoebiusOddPrimeMeanFamily]
    | succ R ih =>
      rw [Finset.sum_range_succ, ih]
      unfold pairedEtaPrimeSieveHarmonicMass pairedEtaMoebiusOddPrimeMeanFamily
      rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_Icc_succ_top (by omega)]
  have ht' := ht.comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, he] using ht'

/-- Exact arithmetic prime weights with their common harmonic normalization. -/
def pairedEtaPrimeSieveWeight (R p : ℕ) : ℝ :=
  (p : ℝ) / (((p : ℝ) - 1) * (1 + pairedEtaPrimeSieveHarmonicMass R))

/-- The canonical weight is nonnegative on each selected odd prime. -/
theorem pairedEtaPrimeSieveWeight_nonneg {R p : ℕ}
    (hp : p ∈ pairedEtaMoebiusOddPrimeMeanFamily R) :
    0 ≤ pairedEtaPrimeSieveWeight R p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_lt
  have hH := pairedEtaPrimeSieveHarmonicMass_nonneg R
  unfold pairedEtaPrimeSieveWeight
  positivity

/-- The weight of every selected prime is at most one, with no fitted numerical coefficients. -/
theorem pairedEtaPrimeSieveWeight_le_one {R p : ℕ}
    (hp : p ∈ pairedEtaMoebiusOddPrimeMeanFamily R) :
    pairedEtaPrimeSieveWeight R p ≤ 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_lt
  have hH := pairedEtaPrimeSieveHarmonicMass_nonneg R
  have hterm : 1 / ((p : ℝ) - 1) ≤ pairedEtaPrimeSieveHarmonicMass R := by
    apply Finset.single_le_sum _ hp
    intro q hq
    have hq1 : (1 : ℝ) < q := by exact_mod_cast (Finset.mem_filter.mp hq).2.1.one_lt
    positivity
  rw [pairedEtaPrimeSieveWeight, div_le_one (by positivity)]
  have hh := (div_le_iff₀ (show (0 : ℝ) < p - 1 by linarith)).mp hterm
  nlinarith

/-- The common harmonic factor bounds every selected prime weight by `2/(1+H_R)`. -/
theorem pairedEtaPrimeSieveWeight_le_harmonic {R p : ℕ}
    (hp : p ∈ pairedEtaMoebiusOddPrimeMeanFamily R) :
    pairedEtaPrimeSieveWeight R p ≤ 2 / (1 + pairedEtaPrimeSieveHarmonicMass R) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.two_le
  have hH := pairedEtaPrimeSieveHarmonicMass_nonneg R
  rw [pairedEtaPrimeSieveWeight, div_mul_eq_div_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < p - 1)]
  linarith

/-- The full weighted prime family retains its exact harmonic gain in the first-mean estimate. -/
theorem norm_pairedEtaMoebiusWeightedPrimeFirstMean_harmonic_le
    (rho : NontrivialZetaZero) {u R : ℕ} (hu : 1 ≤ u) (hRu : R ≤ u) :
    ‖pairedEtaMoebiusWeightedPrimeFirstMean rho R (u ^ 4) (u ^ 3)
      (fun p ↦ (pairedEtaPrimeSieveWeight R p : ℂ))‖ ≤
        2 * pairedEtaMoebiusFirstMeanConstant rho * (R : ℝ) ^ 2 *
          (u : ℝ) ^ (2 - 4 * rho.1.re) / (1 + pairedEtaPrimeSieveHarmonicMass R) := by
  have hH := pairedEtaPrimeSieveHarmonicMass_nonneg R
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ pairedEtaMoebiusOddPrimeMeanFamily R,
        (2 / (1 + pairedEtaPrimeSieveHarmonicMass R)) *
          ‖pairedEtaMoebiusPrimeProductFirstMean rho p (u ^ 4) (u ^ 3)‖ := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pairedEtaPrimeSieveWeight_nonneg hp)]
      exact mul_le_mul_of_nonneg_right (pairedEtaPrimeSieveWeight_le_harmonic hp) (norm_nonneg _)
    _ ≤ (2 / (1 + pairedEtaPrimeSieveHarmonicMass R)) *
        (pairedEtaMoebiusFirstMeanConstant rho * (R : ℝ) ^ 2 *
          (u : ℝ) ^ (2 - 4 * rho.1.re)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (sum_norm_pairedEtaMoebiusPrimeProductFirstMean_quartic_le rho hu hRu) (by positivity)
    _ = _ := by ring

/-- The larger prime cutoff at the endpoint of the unnormalized quadratic cutoff budget. -/
def pairedEtaPrimeSieveEndpointCutoff (rho : NontrivialZetaZero) (u : ℕ) : ℕ :=
  ⌊(u : ℝ) ^ (2 * rho.1.re - 1)⌋₊

/-- The endpoint prime family grows without bound whenever the real part exceeds one half. -/
theorem pairedEtaPrimeSieveEndpointCutoff_tendsto_atTop
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (pairedEtaPrimeSieveEndpointCutoff rho) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by linarith : 0 < 2 * rho.1.re - 1)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))

/-- The chosen exact harmonic weights on the larger prime family, with the original quartic product and physical cutoffs. -/
def pairedEtaMoebiusHarmonicPrimeFirstMean (rho : NontrivialZetaZero) (u : ℕ) : ℂ :=
  pairedEtaMoebiusWeightedPrimeFirstMean rho (pairedEtaPrimeSieveEndpointCutoff rho u)
    (u ^ 4) (u ^ 3) (fun p ↦ (pairedEtaPrimeSieveWeight (pairedEtaPrimeSieveEndpointCutoff rho u) p : ℂ))

/-- At the larger cutoff all polynomial costs cancel, leaving only the inverse divergent harmonic mass. -/
theorem norm_pairedEtaMoebiusHarmonicPrimeFirstMean_le
    (rho : NontrivialZetaZero) {u : ℕ} (hu : 1 ≤ u) :
    ‖pairedEtaMoebiusHarmonicPrimeFirstMean rho u‖ ≤
      2 * pairedEtaMoebiusFirstMeanConstant rho /
        (1 + pairedEtaPrimeSieveHarmonicMass (pairedEtaPrimeSieveEndpointCutoff rho u)) := by
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hup : (0 : ℝ) < u := by linarith
  have hC := pairedEtaMoebiusFirstMeanConstant_nonneg rho
  have hH := pairedEtaPrimeSieveHarmonicMass_nonneg (pairedEtaPrimeSieveEndpointCutoff rho u)
  have hcut : (pairedEtaPrimeSieveEndpointCutoff rho u : ℝ) ≤
      (u : ℝ) ^ (2 * rho.1.re - 1) := Nat.floor_le (Real.rpow_nonneg hup.le _)
  have hRu : pairedEtaPrimeSieveEndpointCutoff rho u ≤ u := by
    exact_mod_cast hcut.trans (Real.rpow_le_self_of_one_le huR
      (by linarith [NontrivialZetaZero.re_lt_one rho]))
  have hpower : ((u : ℝ) ^ (2 * rho.1.re - 1)) ^ 2 *
      (u : ℝ) ^ (2 - 4 * rho.1.re) = 1 := by
    rw [← Real.rpow_mul_natCast hup.le, ← Real.rpow_add hup]
    convert Real.rpow_zero (u : ℝ) using 1
    congr 1
    norm_num
    ring
  apply (norm_pairedEtaMoebiusWeightedPrimeFirstMean_harmonic_le rho hu hRu).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ 2 * pairedEtaMoebiusFirstMeanConstant rho *
        ((u : ℝ) ^ (2 * rho.1.re - 1)) ^ 2 * (u : ℝ) ^ (2 - 4 * rho.1.re) := by
      gcongr
    _ = _ := by rw [mul_assoc (2 * pairedEtaMoebiusFirstMeanConstant rho), hpower, mul_one]

/-- The exact harmonic weights make the entire larger prime-family correction tend to zero. -/
theorem pairedEtaMoebiusHarmonicPrimeFirstMean_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (pairedEtaMoebiusHarmonicPrimeFirstMean rho) atTop (𝓝 0) := by
  have hH := pairedEtaPrimeSieveHarmonicMass_tendsto_atTop.comp
    (pairedEtaPrimeSieveEndpointCutoff_tendsto_atTop rho hrho)
  have hden := tendsto_atTop_add_const_left atTop 1 hH
  have hzero := (tendsto_const_nhds (x := 2 * pairedEtaMoebiusFirstMeanConstant rho)).div_atTop hden
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _))
    ((eventually_ge_atTop 1).mono fun _ hu ↦ norm_pairedEtaMoebiusHarmonicPrimeFirstMean_le rho hu)
    hzero

/-- The larger harmonically weighted sieve retains the original nonzero source in its exact signed residual. -/
theorem pairedEtaCompletedMoebiusLargeFirstMean_sub_harmonicPrime_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun u : ℕ ↦ pairedEtaCompletedMoebiusLargeFirstMean rho (u ^ 4) (u ^ 3) -
      pairedEtaMoebiusHarmonicPrimeFirstMean rho u) atTop (𝓝 (pairedEtaCompletedMoebiusSource rho)) := by
  simpa only [sub_zero] using
    (pairedEtaCompletedMoebiusLargeFirstMean_quartic_tendsto_source rho hrho).sub
      (pairedEtaMoebiusHarmonicPrimeFirstMean_tendsto_zero rho hrho)

end

end RiemannGaussian
