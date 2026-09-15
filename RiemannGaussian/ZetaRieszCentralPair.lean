/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPairedCorrection
import RiemannGaussian.ZetaRieszCentralWindow

/-!
# The complete central carrier with its prime head retained

The two finite components have the independent central-window transport
while the completed prime head remains whole. From order twenty the
central pair clip is exactly one. The nonzero unpaired support has at
least three distinct prime factors. The whole signed floor remains open.
-/

namespace RiemannGaussian.ZetaRieszCentralPair
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAnnulusJoint ZetaRieszRemainingPrefix ZetaRieszPairedCorrection
open ZetaRieszMixedPrefixTransport ZetaRieszCentralWindow

/-- The exact clipped correction is bounded by one logarithm before
the full product phase is applied, for every physical length and integer. -/
theorem norm_clipped_coefficient_le (u : ℝ) (N n : ℕ) :
    ‖((Real.log n * min 1 (Real.log n / SquarefreeVaughanLogSource.length u N) : ℝ) : ℂ)‖ ≤
      Real.log n := by
  have hn := Real.log_natCast_nonneg n
  have hm : 0 ≤ min 1 (Real.log n / SquarefreeVaughanLogSource.length u N) :=
    le_min (by norm_num) (div_nonneg hn (SquarefreeVaughanLogSource.length_pos u N).le)
  rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hn hm)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (min_le_left (1 : ℝ) _) hn

/-- The paired correction in the proved central logarithmic window,
with its exact clipped coefficient and unique integer product labels. -/
def centralPairResponse (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ centralBand (pairedLabels (intermediatePrimes u N)) N,
    ((Real.log n * min 1 (Real.log n / SquarefreeVaughanLogSource.length u N) : ℝ) : ℂ) *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- Both outer pieces of the complete paired correction vanish with
the independent central-window allowance. No zero or phase premise is used. -/
theorem tendsto_clippedPair_sub_central (P : Polynomial ℂ) (y : ℝ) {u : ℝ}
    (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (clippedPairResponse P u y N - centralPairResponse P u y N)) atTop (nhds 0) :=
  tendsto_sub_centralBand (fun N => pairedLabels (intermediatePrimes u N)) _
    (fun N n _ => (norm_clipped_coefficient_le u N n).trans (log_le_divisor_majorant n))
    P y hu huh

/-- The unchanged unpaired subcutoff coefficient on the central part of
its exact original support. No completion is made in this definition. -/
def centralUnpairedResponse (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ centralBand (((ZetaRieszPhysicalAnnulus.annulusBand u N).filter (fun n =>
      ∀ p ∈ n.primeFactors, p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)) \
        pairedLabels (intermediatePrimes u N)) N,
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- The unpaired part has its own valid central deletion, preserving all
the inherited masks and using only the original divisor majorant. -/
theorem tendsto_unpaired_sub_central (P : Polynomial ℂ) (y : ℝ) {u : ℝ}
    (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (unpairedSubcutoffResponse P u y N - centralUnpairedResponse P u y N)) atTop (nhds 0) :=
  tendsto_sub_centralBand _ _
    (fun N n _ => SquarefreeVaughanLogSource.norm_coefficient_le
      (SquarefreeVaughanLogSource.length_pos u N) n) P y hu huh

/-- The central completed representation leaves the infinite prime head
whole and cuts only the two finite components with proved independent errors. -/
def centralJoint (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  centralUnpairedResponse P u y N +
    ZetaPrimeCofactorCompletion.completedCofactorHead (intermediatePrimes u N) P N
      (3 / 2 + Complex.I * y) (SquarefreeVaughanLogSource.length u N) +
    centralPairResponse P u y N

/-- The complete central transport loses only the two independently
bounded finite corrections; it imposes no bound or mask on the completed head. -/
theorem tendsto_refined_sub_centralJoint (P : Polynomial ℂ) (y : ℝ) {u : ℝ}
    (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (refinedJoint P u y N - centralJoint P u y N)) atTop (nhds 0) := by
  have hu0 : 0 < u := by linarith
  have h := (tendsto_unpaired_sub_central P y hu0 huh).add
    (tendsto_clippedPair_sub_central P y hu0 huh)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_refinedJoint_eq_clipped_split P y hu huh] with N he
  rw [he, centralJoint]
  ring

/-- The whole central completed representation retains the original
negative multiplicity source. Its three terms still require joint control. -/
theorem tendsto_centralJoint_exposed (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      centralJoint 1 (3 / 2 - rho.1.re) rho.1.im N)
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : (1 / 2 : ℝ) ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (tendsto_refinedJoint_exposed rho hrho hexposed huh).sub
    (tendsto_refined_sub_centralJoint 1 rho.1.im hu huh)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  ring

/-- The central transport has a fully explicit two-rate error, uniform
in height. The factor two pays the two finite corrections separately;
the completed prime head is kept whole and its phases are never normed. -/
theorem eventually_norm_refined_sub_centralJoint_le (P : Polynomial ℂ) (y : ℝ) {u : ℝ}
    (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop,
      ‖(u : ℂ) ^ (N + 1) * (refinedJoint P u y N - centralJoint P u y N)‖ ≤
        2 * (centralLowerRate ^ N * (u * ZetaArithmeticLogWindow.tiltConstant P (2 / 3) (257 / 256)) +
          centralUpperRate ^ N * (u * ZetaArithmeticLogWindow.tiltConstant P (3 / 8) (257 / 256))) := by
  have hu0 : 0 < u := by linarith
  filter_upwards [eventually_refinedJoint_eq_clipped_split P y hu huh] with N he
  have hp := norm_sub_centralBand_le (pairedLabels (intermediatePrimes u N)) _
    (fun n _ => (norm_clipped_coefficient_le u N n).trans (log_le_divisor_majorant n)) P N y hu0 huh
  have hs : ‖(u : ℂ) ^ (N + 1) *
      (unpairedSubcutoffResponse P u y N - centralUnpairedResponse P u y N)‖ ≤
      centralLowerRate ^ N * (u * ZetaArithmeticLogWindow.tiltConstant P (2 / 3) (257 / 256)) +
        centralUpperRate ^ N * (u * ZetaArithmeticLogWindow.tiltConstant P (3 / 8) (257 / 256)) :=
    norm_sub_centralBand_le _ _
      (fun n _ => SquarefreeVaughanLogSource.norm_coefficient_le
        (SquarefreeVaughanLogSource.length_pos u N) n) P N y hu0 huh
  rw [show (u : ℂ) ^ (N + 1) * (refinedJoint P u y N - centralJoint P u y N) =
      (u : ℂ) ^ (N + 1) * (unpairedSubcutoffResponse P u y N - centralUnpairedResponse P u y N) +
      (u : ℂ) ^ (N + 1) * (clippedPairResponse P u y N - centralPairResponse P u y N) by
        rw [he, centralJoint]; ring]
  exact (norm_add_le _ _).trans ((add_le_add hs hp).trans_eq (by ring))

/-- For every exposed-zero scale, the original physical logarithm lies
below the central lower edge from the explicit order twenty onward. -/
theorem length_le_central_lower {u : ℝ} (hu : 1 / 2 ≤ u) {N : ℕ} (hN : 20 ≤ N) :
    SquarefreeVaughanLogSource.length u N ≤ (3 / 2 : ℝ) * N := by
  have hu0 : 0 < u := by linarith
  have hinv : u⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hu0).mpr (by linarith)
  have hfloor : (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) ≤
      u⁻¹ ^ N / (N + 1) := Nat.floor_le (by positivity)
  have hD : (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) ≤ (2 : ℝ) ^ N := by
    calc
      _ ≤ u⁻¹ ^ N / (N + 1) := hfloor
      _ ≤ u⁻¹ ^ N := div_le_self (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) N])
      _ ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) hinv N
  have hbase : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ) ≤ 3 * (2 : ℝ) ^ N := by
    have hp : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    linarith
  have hlog := Real.log_le_log (by positivity) hbase
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
  have hgap : 0 < (3 / 2 : ℝ) - 2 * Real.log 2 := by linarith [Real.log_two_lt_d9]
  have hmargin : 2 * Real.log 3 ≤ (20 : ℝ) * (3 / 2 - 2 * Real.log 2) := by
    linarith [Real.log_three_lt_d9, Real.log_two_lt_d9]
  have hN' : (20 : ℝ) ≤ N := by exact_mod_cast hN
  have hm := mul_le_mul_of_nonneg_right hN' hgap.le
  unfold SquarefreeVaughanLogSource.length
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith

/-- On the surviving central paired support the clip is identically one.
The full paired correction therefore has the literal logarithmic weight,
while its original complex product phase remains coupled to the head. -/
theorem centralPairResponse_eq_log_sum (P : Polynomial ℂ) (y : ℝ) {u : ℝ}
    (hu : 1 / 2 ≤ u) {N : ℕ} (hN : 20 ≤ N) :
    centralPairResponse P u y N =
      ∑ n ∈ centralBand (pairedLabels (intermediatePrimes u N)) N,
        (Real.log n : ℂ) * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  apply Finset.sum_congr rfl
  intro n hn
  have hlog : SquarefreeVaughanLogSource.length u N ≤ Real.log n :=
    (length_le_central_lower hu hN).trans (Finset.mem_filter.mp hn).2.1.le
  have hr : 1 ≤ Real.log n / SquarefreeVaughanLogSource.length u N :=
    (le_div_iff₀ (SquarefreeVaughanLogSource.length_pos u N)).mpr (by simpa using hlog)
  rw [min_eq_left hr, mul_one]

/-- The nonzero unpaired subcutoff carrier contains at least three
distinct prime factors. The previously proved two-intermediate-prime
support rules out all remaining degree-two labels exactly. -/
theorem three_le_primeFactors_of_unpaired {u : ℝ} {N n : ℕ}
    (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hNX : N ^ 2 < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hn : n ∈ (ZetaRieszPhysicalAnnulus.annulusBand u N).filter (fun n =>
      ∀ p ∈ n.primeFactors, p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2))
    (hpair : n ∉ pairedLabels (intermediatePrimes u N))
    (hc : SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n ≠ 0) :
    3 ≤ n.primeFactors.card := by
  obtain ⟨hann, hsmall⟩ := Finset.mem_filter.mp hn
  have hsemi := ZetaRieszNarrowCarrier.residualBand_subset u N
    (ZetaRieszFourExtremeDeletion.fourResidualBand_subset u N
      (ZetaRieszLowerDegreeDeletion.degreeResidualBand_subset u N
        (ZetaRieszPhysicalAnnulus.annulusBand_subset u N hann)))
  obtain ⟨p, r, hp, hr, hpr, hpn, hrn, hNp, hNr⟩ :=
    ZetaRieszSemiprimeDeletion.surviving_two_large_primes
      (huh.trans (Real.exp_lt_exp.mpr (by norm_num))) hNX hsemi hc
  have hsq : Squarefree n := by
    by_contra hs
    exact hc (by simp [SquarefreeVaughanLogSource.coefficient, hs])
  have hpF := Nat.mem_primeFactors.mpr ⟨hp, hpn, hsq.ne_zero⟩
  have hrF := Nat.mem_primeFactors.mpr ⟨hr, hrn, hsq.ne_zero⟩
  have hsub : ({p, r} : Finset ℕ) ⊆ n.primeFactors := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> assumption
  by_contra hcard
  have he : n.primeFactors = {p, r} :=
    (Finset.eq_of_subset_of_card_le hsub (by simpa [hpr] using (show n.primeFactors.card ≤ 2 by omega))).symm
  have hprod : p * r = n := by
    simpa [he, hpr] using Nat.prod_primeFactors_of_squarefree hsq
  apply hpair
  exact Finset.mem_image.mpr ⟨(p, r), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨(mem_intermediatePrimes u N p).mpr ⟨hp, hNp, hsmall p hpF⟩,
      (mem_intermediatePrimes u N r).mpr ⟨hr, hNr, hsmall r hrF⟩⟩, hpr⟩, hprod⟩

/-- The physical-head comparison is eventually automatic, so every
nonzero central unpaired label has at least three distinct prime factors. -/
theorem eventually_centralUnpaired_three_primes {u : ℝ}
    (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ n ∈ centralBand
      (((ZetaRieszPhysicalAnnulus.annulusBand u N).filter (fun n =>
        ∀ p ∈ n.primeFactors, p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)) \
          pairedLabels (intermediatePrimes u N)) N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n ≠ 0 →
      3 ≤ n.primeFactors.card := by
  have hu1 : u < 1 := huh.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  filter_upwards [ZetaRieszSemiprimeSupport.eventually_quadratic_head_lt_physical hu hu1]
    with N hNX
  intro n hn hc
  have hparts := Finset.mem_sdiff.mp (Finset.mem_filter.mp hn).1
  exact three_le_primeFactors_of_unpaired huh hNX hparts.1 hparts.2 hc

end

end RiemannGaussian.ZetaRieszCentralPair
