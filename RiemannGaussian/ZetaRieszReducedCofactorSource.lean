/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeClasses

/-!
# Reduced arithmetic source after finite cofactor deletion

The entire composite-cofactor head over the small-prime universe is proved
negligible in one original-band sum. Its literal complement retains the
hypothetical-zero source, and its arithmetic support is classified exactly.
A final conditional closure audit identifies the remaining cofinal floor
premise needed for Mathlib RH; that arithmetic premise is not proved here.
-/

namespace RiemannGaussian.ZetaRieszReducedCofactorSource
noncomputable section
open scoped BigOperators Classical Topology
open Filter ZetaRieszFixedCofactor

/-- Every prime insertion with a composite cofactor in the fixed small
prime universe. No completion outside the original band is introduced. -/
def compositeHeadInsertion (n : ℕ) : Prop :=
  ∃ a ∈ (30030 : ℕ).divisors, a ≠ 1 ∧ ¬ a.Prime ∧
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ a ∧ n = p * a

/-- The complete finite allowance for every eligible fixed cofactor. -/
def headCost : ℝ := 2 * (∑ a ∈ (30030 : ℕ).divisors, divisorLogMass a) *
  (1 + Real.log 30030 / Real.log 4)

/-- All costs in the finite cofactor allowance are nonnegative. -/
theorem headCost_nonneg : 0 ≤ headCost := by
  have hB : 0 ≤ ∑ a ∈ (30030 : ℕ).divisors, divisorLogMass a :=
    Finset.sum_nonneg fun a _ => divisorLogMass_nonneg a
  have h4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have h30 := Real.log_pos (by norm_num : (1 : ℝ) < 30030)
  unfold headCost
  positivity

/-- The whole composite-head class, with the original finite band. -/
def compositeHeadBand (N : ℕ) : Finset ℕ :=
  (zetaPrimeLogBand N).filter compositeHeadInsertion

/-- A common compact part containing every nonzero composite-head term
once the logarithmic cutoff contains the fixed cofactor universe. -/
def clippedHeadBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  (compositeHeadBand N).filter fun n =>
    n ≤ 30030 * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2

/-- The literal coefficient on the common compact range has one fixed
bound after preserving each cofactor's signed prime difference. -/
theorem norm_clipped_head_coefficient_le (u : ℝ) (N : ℕ) {n : ℕ}
    (hn : n ∈ clippedHeadBand u N) :
    ‖SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n‖ ≤
      headCost := by
  obtain ⟨hnhead, hc⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnband, a, had, ha1, _hap, p, hp, hpa, rfl⟩ := Finset.mem_filter.mp hnhead
  have hnp := (Finset.mem_Icc.mp (Finset.mem_filter.mp hnband).1).1
  have hb := norm_coefficient_prime_mul_le (SquarefreeVaughanLogSource.length_pos u N)
    (Real.log_pos (by norm_num)) (length_ge_log_four u N) ha1 hp hpa
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 30030))
    (log_le_length_add_log (by norm_num : 0 < (30030 : ℕ)) hnp u N hc)
  have hB : divisorLogMass a ≤ ∑ d ∈ (30030 : ℕ).divisors, divisorLogMass d :=
    Finset.single_le_sum (fun d _ => divisorLogMass_nonneg d) had
  apply hb.trans
  unfold headCost
  apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB (by norm_num))
  have h4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have h30 := Real.log_pos (by norm_num : (1 : ℝ) < 30030)
  positivity

/-- All composite-head coefficients in their common compact part
vanish at the original source scale with the complete factorial filter. -/
theorem tendsto_clipped_head_band (P : Polynomial ℂ) (y : ℝ) {u : ℝ}
    (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) *
      ∑ n ∈ clippedHeadBand u N,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  refine tendsto_sum_filter_square_cutoff P 30030 y (clippedHeadBand u)
    (fun N => SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N))
    headCost_nonneg hu hu1 ?_ ?_
  · intro N n hn
    obtain ⟨hc, hnle⟩ := Finset.mem_filter.mp hn
    have hb := (Finset.mem_filter.mp hc).1
    exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1, hnle⟩
  · exact fun N _ hn => norm_clipped_head_coefficient_le u N hn

/-- Above the common compact range every composite-head coefficient
is exactly zero after the fixed head is inside the common cutoff. -/
theorem coefficient_head_eq_zero_above (u : ℝ) (N : ℕ) {n : ℕ}
    (hn : compositeHeadInsertion n)
    (hL : Real.log 30030 ≤ SquarefreeVaughanLogSource.length u N)
    (hc : ¬ n ≤ 30030 * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n = 0 := by
  obtain ⟨a, had, ha1, hap, p, hp, hpa, rfl⟩ := hn
  have hadvd := Nat.dvd_of_mem_divisors had
  have ha : Squarefree a := (squarefree_primorial 15).squarefree_of_dvd
    (ZetaRieszPrimeClasses.primorial_fifteen ▸ hadvd)
  have hale : a ≤ 30030 := Nat.le_of_dvd (by norm_num) hadvd
  have hLa : Real.log a ≤ SquarefreeVaughanLogSource.length u N :=
    (Real.log_le_log (by exact_mod_cast Nat.pos_of_mem_divisors had : (0 : ℝ) < a)
      (by exact_mod_cast hale)).trans hL
  have hpa' : a * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < p * a :=
    (Nat.mul_le_mul_right _ hale).trans_lt (Nat.lt_of_not_ge hc)
  have hgt : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < p := by
    nlinarith [Nat.pos_of_mem_divisors had]
  have hLp : SquarefreeVaughanLogSource.length u N ≤ Real.log p := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hgt.le
  exact coefficient_prime_mul_eq_zero_of_large ha ha1 hap hp hpa hLa hLp

/-- All finitely many fixed composite cofactors are removed together
inside one original-band sum, without double counting their overlaps. -/
theorem head_band_eq_clipped (P : Polynomial ℂ) (y u : ℝ) (N : ℕ)
    (hL : Real.log 30030 ≤ SquarefreeVaughanLogSource.length u N) :
    (∑ n ∈ compositeHeadBand N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
    ∑ n ∈ clippedHeadBand u N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  rw [clippedHeadBand, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs with hc
  · rfl
  · rw [coefficient_head_eq_zero_above u N (Finset.mem_filter.mp hn).2 hL hc, zero_mul]

/-- The entire finite composite-head union has an independent vanishing
bound at the original source scale. All original arithmetic restrictions
and the complete factorial polynomial filter remain in the statement. -/
theorem tendsto_composite_head_band (P : Polynomial ℂ) (y : ℝ) {u : ℝ}
    (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) *
      ∑ n ∈ compositeHeadBand N,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  apply (tendsto_clipped_head_band P y hu hu1).congr'
  filter_upwards [(tendsto_length hu hu1).eventually_ge_atTop (Real.log 30030)] with N hN
  rw [head_band_eq_clipped P y u N hN]

/-- The exact original band after removing only the paid composite-head
labels. The surviving coefficient and factorial filter are not redefined. -/
def reducedHeadBand (N : ℕ) : Finset ℕ :=
  (zetaPrimeLogBand N).filter fun n => ¬ compositeHeadInsertion n

/-- The original carrier is the sum of the paid finite-head class and
its literal complement, with every original sign and phase retained. -/
theorem actual_band_eq_head_add_reduced (P : Polynomial ℂ) (N : ℕ) (y L : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y =
      (∑ n ∈ compositeHeadBand N,
        SquarefreeVaughanLogSource.coefficient L n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) +
      ∑ n ∈ reducedHeadBand N,
        SquarefreeVaughanLogSource.coefficient L n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  exact (Finset.sum_filter_add_sum_filter_not (zetaPrimeLogBand N)
    compositeHeadInsertion (fun n => SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)).symm

/-- The exact remaining band retains the original negative-multiplicity
source after subtracting the independently vanishing finite cofactor class. -/
theorem tendsto_reduced_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N => (3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
      ∑ n ∈ reducedHeadBand N,
        SquarefreeVaughanLogSource.coefficient
           (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) n *
          zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N
            (3 / 2 + Complex.I * rho.1.im) n)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 0 < (3 / 2 - rho.1.re : ℝ) := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  have h := (SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho).sub
    (tendsto_composite_head_band (zetaRightHalfPoleJetFilter rho hrho) rho.1.im hu hu1)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  have hcast : ((3 / 2 - rho.1.re : ℝ) : ℂ) = (3 / 2 - rho.1.re : ℂ) := by
    push_cast
    rfl
  rw [hcast, actual_band_eq_head_add_reduced, mul_add, add_sub_cancel_left]

/-- Every surviving squarefree composite either has at least two large
prime factors or is a semiprime with one of the six small prime cofactors.
This classifies the literal reduced source support, not an Euler model. -/
theorem reduced_support {N n : ℕ} (hN : 60 ≤ N) (hb : n ∈ reducedHeadBand N)
    (hn : Squarefree n) (hnp : ¬ n.Prime) :
    2 ≤ ZetaRieszPrimeClasses.largePrimeCount n ∨
      ∃ a ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ), a.Prime ∧
        ∃ p : ℕ, p.Prime ∧ 16 ≤ p ∧ ¬ p ∣ a ∧ n = p * a := by
  obtain ⟨hband, hnot⟩ := Finset.mem_filter.mp hb
  have hpos := ZetaRieszPrimeClasses.largePrimeCount_pos_of_mem_band hN hn hband
  by_cases hc : 2 ≤ ZetaRieszPrimeClasses.largePrimeCount n
  · exact Or.inl hc
  · have h1 : ZetaRieszPrimeClasses.largePrimeCount n = 1 := by omega
    obtain ⟨a, p, had, ha1, _hasf, hp, hp16, hpa, he⟩ :=
      ZetaRieszPrimeClasses.one_large_prime_factorization hn hnp h1
    have hap : a.Prime := by
      by_contra hap
      exact hnot ⟨a, Nat.mem_divisors.mpr ⟨had, by norm_num⟩, by omega, hap,
        p, hp, hpa, he⟩
    exact Or.inr ⟨a, ZetaRieszPrimeClasses.prime_divisor_small_product hap had,
      hap, p, hp, hp16, hpa, he⟩

/-- The same strict cofinal floor suffices after the paid cofactor
union has been removed. The floor is explicitly an unproved premise. -/
theorem false_of_reduced_cofinal_floor (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {c : ℝ} (hc : c < 1)
    (hfloor : ∃ᶠ N in atTop,
      -c ≤ ((3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
        ∑ n ∈ reducedHeadBand N,
          SquarefreeVaughanLogSource.coefficient
            (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) n *
              zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N
                (3 / 2 + Complex.I * rho.1.im) n).re) : False := by
  have hsource := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_reduced_source rho hrho)
  have hf := ge_of_tendsto_of_frequently hsource hfloor
  simp only [Complex.neg_re, Complex.natCast_re] at hf
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

/-- Logical closure audit: a proved strict cofinal floor for each actual
hypothetical right-half zero would give Mathlib's RH by reflection. The
arithmetic floor is a hypothesis here; this is not an unconditional RH proof. -/
theorem rh_of_reduced_cofinal_floors
    (hfloor : ∀ (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re),
      ∃ c : ℝ, c < 1 ∧ ∃ᶠ N in atTop,
        -c ≤ ((3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
          ∑ n ∈ reducedHeadBand N,
            SquarefreeVaughanLogSource.coefficient
              (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) n *
                zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N
                  (3 / 2 + Complex.I * rho.1.im) n).re) : RiemannHypothesis := by
  have hright (rho : NontrivialZetaZero) : rho.1.re ≤ 1 / 2 := by
    apply le_of_not_gt
    intro hrho
    obtain ⟨c, hc, hf⟩ := hfloor rho hrho
    exact false_of_reduced_cofinal_floor rho hrho hc hf
  intro s hs htriv hone
  let rho : NontrivialZetaZero := ⟨s, hs, htriv, hone⟩
  have hupper := hright rho
  have hlower := hright (NontrivialZetaZero.functionalPartner rho)
  simp only [NontrivialZetaZero.functionalPartner_coe, Complex.sub_re,
    Complex.one_re] at hlower
  change s.re ≤ 1 / 2 at hupper
  change 1 - s.re ≤ 1 / 2 at hlower
  linarith

end
end RiemannGaussian.ZetaRieszReducedCofactorSource
