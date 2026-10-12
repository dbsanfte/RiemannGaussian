/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorSuccessorSourceAudit

/-!
# A linear Mellin source does not determine a successor quadratic

The smooth matched row and its even-row concentration have exactly the
same nonzero Mellin residue, and neither has a density pole at one in
the campaign strip. The smooth row has a positive source-scale quadratic;
the even row has successor quadratic exactly zero. Both are literal
integer arrays, realizable by divisor incidence, but NOT actual Mangoldt
data satisfying the complete Gamma identities. This forbids deriving the
nonlinear source gate from the linear zero residue alone. It is not an
impossibility theorem for an additional prime-specific correlation input.
-/

namespace RiemannGaussian.ArithmeticOperatorNonlinearSourceAudit
noncomputable section
open Complex Filter ArithmeticOperatorSuccessorSourceAudit
open ArithmeticOperatorIncidenceFreedom ArithmeticOperatorKummerCutoff
open scoped Topology BigOperators ComplexConjugate

/-- Same matched power, concentrated on even physical rows. -/
def evenRow (v : ℂ) (beta : ℝ) (n : ℕ) : ℂ :=
  if 2 ∣ n then 2*matchedRow v beta n else 0

/-- Exact density/pole scale factor of the arithmetic concentration. -/
def evenFactor (beta : ℝ) (s : ℂ) : ℂ :=
  2*((2 : ℝ)^(beta-1) : ℝ)/(2 : ℂ)^s

/-- The matched smooth row's exact meromorphic continuation. -/
def smoothResponse (v : ℂ) (beta : ℝ) (s : ℂ) : ℂ :=
  v*riemannZeta (s-(beta-1 : ℝ))

/-- Same continuation for the even-row model, without dropping parity. -/
def evenResponse (v : ℂ) (beta : ℝ) (s : ℂ) : ℂ :=
  evenFactor beta s*smoothResponse v beta s

private theorem matched_term (v : ℂ) (beta : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (matchedRow v beta) s n =
      v*LSeries.term (1 : ℕ → ℂ) (s-(beta-1 : ℝ)) n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    simp only [matchedRow, Pi.one_apply]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.cpow_sub _ _
      (Nat.cast_ne_zero.mpr hn)]
    simp only [one_mul, div_eq_mul_inv, Complex.ofReal_natCast, mul_inv_rev, inv_inv]
    ring

/-- Exact Euler-series identity on its genuine convergence half-plane.
There is no claim that a divergent series equals its continuation. -/
theorem smooth_euler_response (v : ℂ) (beta : ℝ) {s : ℂ} (hs : beta < s.re) :
    LSeries (matchedRow v beta) s = smoothResponse v beta s := by
  have ht : 1 < (s-(beta-1 : ℝ)).re := by simp; linarith
  unfold LSeries smoothResponse
  simp_rw [matched_term]
  rw [tsum_mul_left]
  exact congrArg (v*·) (LSeries_one_eq_riemannZeta ht)

theorem matched_summable (v : ℂ) (beta : ℝ) {s : ℂ} (hs : beta < s.re) :
    LSeriesSummable (matchedRow v beta) s := by
  have ht : 1 < (s-(beta-1 : ℝ)).re := by simp; linarith
  change Summable (fun n => LSeries.term (matchedRow v beta) s n)
  apply Summable.congr ((LSeriesSummable_one_iff.mpr ht).mul_left v)
  intro n
  exact (matched_term v beta s n).symm

private theorem even_term (v : ℂ) (beta : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (evenRow v beta) s (2*n) =
      evenFactor beta s*LSeries.term (matchedRow v beta) s n := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn2 : 2*n ≠ 0 := by omega
    rw [LSeries.term_of_ne_zero hn2, LSeries.term_of_ne_zero hn]
    simp only [evenRow, dvd_mul_right, ite_true, matchedRow, Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg n), Complex.ofReal_mul]
    have hc : (2*(n : ℂ))^s = (2 : ℂ)^s*(n : ℂ)^s :=
      Complex.natCast_mul_natCast_cpow 2 n s
    rw [hc]
    unfold evenFactor
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

private theorem odd_term (v : ℂ) (beta : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (evenRow v beta) s (2*n+1) = 0 := by
  rw [LSeries.term_of_ne_zero (by omega)]
  simp only [evenRow, ite_eq_right (Nat.not_two_dvd_bit1 n), zero_div]

theorem even_summable (v : ℂ) (beta : ℝ) {s : ℂ} (hs : beta < s.re) :
    LSeriesSummable (evenRow v beta) s := by
  have he : Summable (fun n : ℕ => LSeries.term (evenRow v beta) s (2*n)) := by
    simp_rw [even_term]
    exact (matched_summable v beta hs).mul_left _
  have ho : Summable (fun n : ℕ => LSeries.term (evenRow v beta) s (2*n+1)) := by
    simp only [odd_term]
    exact summable_zero
  exact he.even_add_odd ho

/-- The even concentration preserves the Mellin pole exactly, not just
the order of growth of a finite diagnostic sum. -/
theorem even_euler_response (v : ℂ) (beta : ℝ) {s : ℂ} (hs : beta < s.re) :
    LSeries (evenRow v beta) s = evenResponse v beta s := by
  have he : Summable (fun n : ℕ => LSeries.term (evenRow v beta) s (2*n)) := by
    simp_rw [even_term]
    exact (matched_summable v beta hs).mul_left _
  have ho : Summable (fun n : ℕ => LSeries.term (evenRow v beta) s (2*n+1)) := by
    simp only [odd_term]
    exact summable_zero
  unfold LSeries evenResponse
  rw [← tsum_even_add_odd he ho]
  simp only [even_term, odd_term, tsum_zero, add_zero, tsum_mul_left]
  exact congrArg (evenFactor beta s*·) (smooth_euler_response v beta hs)

theorem evenFactor_at_source (beta : ℝ) : evenFactor beta (beta : ℂ) = 1 := by
  unfold evenFactor
  rw [Complex.ofReal_cpow (by norm_num)]
  norm_num only [Complex.ofReal_ofNat]
  have he : (2 : ℂ)*2^((beta-1 : ℝ) : ℂ) = 2^(beta : ℂ) := by
    rw [show (beta : ℂ) = (1 : ℂ)+(beta-1 : ℝ) by push_cast; ring,
      Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
  rw [he, div_self (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))]

private theorem continuous_evenFactor (beta : ℝ) : Continuous (evenFactor beta) := by
  unfold evenFactor
  exact continuous_const.div (continuous_const_cpow 2)
    (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))

/-- Exact nonzero matched residue for the smooth row. -/
theorem tendsto_smooth_source (v : ℂ) (beta : ℝ) :
    Tendsto (fun s : ℂ => (s-(beta : ℂ))*smoothResponse v beta s)
      (𝓝[≠] (beta : ℂ)) (𝓝 v) := by
  have ht : Tendsto (fun s : ℂ => s-(beta-1 : ℝ))
      (𝓝[≠] (beta : ℂ)) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hh : Tendsto (fun s : ℂ => s-(beta-1 : ℝ)) (𝓝 (beta : ℂ))
          (𝓝 ((beta : ℂ)-(beta-1 : ℝ))) :=
        (continuous_id.sub continuous_const).tendsto (beta : ℂ)
      have he : (beta : ℂ)-(beta-1 : ℝ) = 1 := by push_cast; ring
      rw [he] at hh
      exact hh.mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro hh
      apply hs
      push_cast at hh
      linear_combination hh
  have hh := (riemannZeta_residue_one.comp ht).const_mul v
  simp only [mul_one] at hh
  convert hh using 1
  funext s
  dsimp only [smoothResponse, Function.comp_def]
  rw [Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- Same EXACT matched residue, despite zero successor response below. -/
theorem tendsto_even_source (v : ℂ) (beta : ℝ) :
    Tendsto (fun s : ℂ => (s-(beta : ℂ))*evenResponse v beta s)
      (𝓝[≠] (beta : ℂ)) (𝓝 v) := by
  have hf : Tendsto (evenFactor beta) (𝓝[≠] (beta : ℂ))
      (𝓝 (evenFactor beta (beta : ℂ))) :=
    (continuous_evenFactor beta).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [evenFactor_at_source] at hf
  have hh := hf.mul (tendsto_smooth_source v beta)
  simp only [one_mul] at hh
  convert hh using 1
  funext s
  unfold evenResponse
  ring

/-- Both density-free continuations are regular at one when beta<1.
Their common matched pole is therefore not a leftover pole mode. -/
theorem analyticAt_density (v : ℂ) {beta : ℝ} (hb : beta < 1) :
    AnalyticAt ℂ (smoothResponse v beta) 1 ∧
      AnalyticAt ℂ (evenResponse v beta) 1 := by
  have ht : (1 : ℂ)-(beta-1 : ℝ) ≠ 1 := by
    intro hh
    have hr := congrArg Complex.re hh
    norm_num at hr
    linarith
  have ha : AnalyticAt ℂ (fun s : ℂ => riemannZeta (s-(beta-1 : ℝ))) 1 :=
    AnalyticAt.comp (g := riemannZeta) (f := fun s : ℂ => s-(beta-1 : ℝ))
      (x := 1) (analyticOn_riemannZeta _ ht) (by fun_prop)
  have hs : AnalyticAt ℂ (smoothResponse v beta) 1 := by
    unfold smoothResponse
    exact analyticAt_const.mul ha
  refine ⟨hs,?_⟩
  unfold evenResponse
  apply AnalyticAt.mul ?_ hs
  unfold evenFactor
  rw [show (fun s : ℂ => 2*((2 : ℝ)^(beta-1) : ℝ)/(2 : ℂ)^s) =
      fun s => 2*((2 : ℝ)^(beta-1) : ℝ)/Complex.exp (Complex.log 2*s) by
        funext s; rw [Complex.cpow_def_of_ne_zero (by norm_num)]]
  exact analyticAt_const.div (by fun_prop) (Complex.exp_ne_zero _)

/-- Parity kills every adjacent physical product exactly, at every
cutoff, before any norm or asymptotic payment. -/
theorem even_successor_zero (v : ℂ) (beta : ℝ) (X : ℕ) :
    successor X (evenRow v beta) = 0 := by
  unfold successor
  apply Finset.sum_eq_zero
  intro n _
  by_cases hn : 2 ∣ n
  · have hh : ¬2 ∣ n+1 := by
      intro he
      have hd : 2 ∣ 1 := (Nat.dvd_add_iff_right hn).mpr he
      norm_num at hd
    simp only [evenRow, ite_eq_right hh, map_zero, mul_zero]
  · simp only [evenRow, ite_eq_right hn, zero_mul]

/-- The source-preserving parity model also lives on literal divisor
incidence for EVERY positive physical row, not only one test matrix. -/
theorem evenRow_divisor_realization (v : ℂ) (beta : ℝ) {n : ℕ} (hn : 0 < n) :
    divisorObservation (inverseRows (evenRow v beta)) n = evenRow v beta n :=
  observation_inverseRows _ hn

/-- A genuine convergent Euler series with a nonzero matched residue,
after the density pole has been removed. No arithmetic assumptions on
the coefficient array are concealed in this diagnostic predicate. -/
def HasDensityFreeSource (g : ℕ → ℂ) (beta : ℝ) (v : ℂ) : Prop :=
  v ≠ 0 ∧ ∃ F : ℂ → ℂ,
    (∀ s : ℂ, beta < s.re → LSeriesSummable g s) ∧
    (∀ s : ℂ, beta < s.re → LSeries g s = F s) ∧
    AnalyticAt ℂ F 1 ∧
    Tendsto (fun s : ℂ => (s-(beta : ℂ))*F s) (𝓝[≠] (beta : ℂ)) (𝓝 v)

theorem smooth_has_density_free_source {v : ℂ} (hv : v ≠ 0)
    {beta : ℝ} (hb : beta < 1) :
    HasDensityFreeSource (matchedRow v beta) beta v := by
  exact ⟨hv,smoothResponse v beta,fun _ hs => matched_summable v beta hs,
    fun _ hs => smooth_euler_response v beta hs,
    (analyticAt_density v hb).1,tendsto_smooth_source v beta⟩

theorem even_has_density_free_source {v : ℂ} (hv : v ≠ 0)
    {beta : ℝ} (hb : beta < 1) : HasDensityFreeSource (evenRow v beta) beta v := by
  exact ⟨hv,evenResponse v beta,fun _ hs => even_summable v beta hs,
    fun _ hs => even_euler_response v beta hs,
    (analyticAt_density v hb).2,tendsto_even_source v beta⟩

/-- Reusable source-gate no-go: even an exact nonzero Mellin residue,
genuine Euler convergence, and absence of the density pole do not force
ANY nonzero successor response. Additional prime information is needed. -/
theorem source_does_not_force_successor {v : ℂ} (hv : v ≠ 0)
    {beta : ℝ} (hb : beta < 1) :
    ¬(∀ g : ℕ → ℂ, HasDensityFreeSource g beta v →
      ∃ X : ℕ, successor X g ≠ 0) := by
  intro h
  obtain ⟨X,hX⟩ := h (evenRow v beta) (even_has_density_free_source hv hb)
  exact hX (even_successor_zero v beta X)

/-- This obstruction applies to the exact linear matched residue of
every actual zero, retaining its analytic multiplicity. The countermodel
is still NOT the actual arithmetic prime row. -/
theorem matched_zero_residue_does_not_force_successor (rho : NontrivialZetaZero) :
    ¬(∀ g : ℕ → ℂ,
      HasDensityFreeSource g rho.1.re
        (-(analyticZetaZeroMultiplicity rho : ℂ)*riemannZeta (rho.1.re : ℂ)) →
      ∃ X : ℕ, successor X g ≠ 0) :=
  source_does_not_force_successor
    (ArithmeticOperatorTwistSourceAudit.commutator_source_ne_zero rho)
    (NontrivialZetaZero.re_lt_one rho)

end
end RiemannGaussian.ArithmeticOperatorNonlinearSourceAudit
