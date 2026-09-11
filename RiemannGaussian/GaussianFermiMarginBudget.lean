/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaFermiGlobalMargin

/-!
# Feeding proved zero-free margins back into the Fermi budget

The interior line can use any proved common margin of the actual height
band. Increasing that margin decreases the existing derivative cost, so
the original whole-divisor allowance still pays for the complete outside
sum. The exact prime phase recombination and all selected zero
multiplicities survive the transport. The final theorem instantiates the
general budget with the already proved global Fermi margin.
-/

namespace RiemannGaussian.GaussianFermiMarginBudget
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology Classical
open GaussianFermiDerivativeBounds GaussianFermiZeroPair GaussianFermiZeroTail
open GaussianFermiMovingAllowance GaussianFermiPhaseBudget GaussianFermiPoleFormula
open GaussianFermiPrimeFormula
open GaussianFermiGammaBound GaussianFermiLaplaceOrder GaussianFermiResonantBudget

/-- The explicit derivative cost decreases as the interior margin grows
through the range used by the actual zero budget. The Gaussian scale is
kept fixed in this exact comparison. -/
theorem integralCost_antitone_margin {d m : ℝ} (hdm : d ≤ m) (hmu : m ≤ 1 / 4)
    (B : ℝ) :
    integralCost (1 - 2 * m) B m ≤ integralCost (1 - 2 * d) B d := by
  have hs : (2 * (1 - 2 * m) + m) ^ 2 ≤ (2 * (1 - 2 * d) + d) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith) (by linarith) 2
  unfold integralCost amplitudeCost
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  linarith

/-- Any larger admissible margin has a whole-divisor error no larger than
the existing allowance. No new summability or tail hypothesis is needed. -/
theorem outside_cost_le_allowance {m H : ℝ}
    (hm : zetaPoleReserveZeroMargin H ≤ m) (hmu : m ≤ 1 / 4) (B : ℝ) :
    4 * integralCost (1 - 2 * m) B m * divisorTail H ≤ allowance B H := by
  have ht : 0 ≤ divisorTail H := by
    apply tsum_nonneg
    intro ρ
    split_ifs <;> positivity [divisorWeight_nonneg ρ]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (integralCost_antitone_margin hm hmu B) (by norm_num)) ht

/-- The same-phase contribution of an actual zero is nonnegative whenever
the chosen interior line encloses both of its horizontal partners. -/
theorem contribution_nonneg_of_strip {B m : ℝ} (hB : 0 < B) (hmu : m ≤ 1 / 4)
    (t : ℝ) (ρ : NontrivialZetaZero) (hl : m ≤ ρ.1.re) (hr : ρ.1.re ≤ 1 - m) :
    0 ≤ contribution B (1 - m) t ρ := by
  unfold contribution
  apply mul_nonneg (by positivity)
  exact reflected_point_pair_re_nonneg hB (by linarith) t (by linarith) hr

/-- A selected finite zero set is retained at any proved larger band
margin, with the same full outside allowance as in the original budget. -/
theorem selected_zero_sum_le_full_add_allowance {B m H t : ℝ} (hB : 0 < B)
    (ht : 2 * |t| ≤ H) (hH : 1 ≤ H)
    (hm : zetaPoleReserveZeroMargin H ≤ m) (hmu : m ≤ 1 / 4) (hscale : m ^ 2 ≤ B)
    (hzeros : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H → m ≤ ρ.1.re ∧ ρ.1.re ≤ 1 - m)
    (S : Finset NontrivialZetaZero) (hS : ∀ ρ ∈ S, |ρ.1.im| ≤ H) :
    (∑ ρ ∈ S, contribution B (1 - m) t ρ) ≤
      (∑' ρ : NontrivialZetaZero, contribution B (1 - m) t ρ) + allowance B H := by
  let σ := 1 - m
  have hmpos := (zetaPoleReserveZeroMargin_bounds H).1.trans_le hm
  have hσ0 : 1 / 2 ≤ σ := by dsimp [σ]; linarith
  have hσ1 : σ ≤ 1 := by dsimp [σ]; linarith
  have hscale' : (1 - σ) ^ 2 ≤ B := by simpa [σ] using hscale
  have hin : Summable (inside B σ t H) :=
    summable_of_hasFiniteSupport (finite_support_inside B σ t (by linarith))
  have hn (ρ : NontrivialZetaZero) : 0 ≤ inside B σ t H ρ := by
    unfold inside
    split_ifs with hρ
    · exact contribution_nonneg_of_strip hB hmu t ρ (hzeros ρ hρ).1 (hzeros ρ hρ).2
    · exact le_rfl
  have hsel : (∑ ρ ∈ S, contribution B σ t ρ) ≤
      ∑' ρ : NontrivialZetaZero, inside B σ t H ρ := by
    calc
      _ = ∑ ρ ∈ S, inside B σ t H ρ := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        simp only [inside, if_pos (hS ρ hρ)]
      _ ≤ _ := hin.sum_le_tsum S (fun ρ _ => hn ρ)
  have htail := (abs_le.mp (abs_tsum_outside_le hB hσ0 hσ1 hscale' ht hH)).1
  have hcost : 4 * integralCost (2 * σ - 1) B (1 - σ) * divisorTail H ≤ allowance B H := by
    dsimp [σ]
    rw [show 2 * (1 - m) - 1 = 1 - 2 * m by ring, sub_sub_cancel]
    exact outside_cost_le_allowance hm hmu B
  have hsplit := zero_sum_eq_inside_add_outside hB hσ0 hσ1 hscale' ht hH
  change (∑ ρ ∈ S, contribution B σ t ρ) ≤ _
  change _ ≤ (∑' ρ : NontrivialZetaZero, contribution B σ t ρ) + allowance B H
  linarith

/-- The literal signed prime combination is retained alongside every
selected zero at the improved interior margin. No nonnegativity of the
cosine test is needed until this arithmetic term is estimated. -/
theorem selected_zero_phase_budget_with_prime {ι : Type*} (J : Finset ι) (w ω : ι → ℝ)
    (hw : ∀ j ∈ J, 0 ≤ w j)
    {m H b c t : ℝ} (hH : 1 ≤ H) (hb : 0 < b) (hc : 0 < c)
    (hm : zetaPoleReserveZeroMargin H ≤ m) (hmu : m ≤ 1 / 4) (hscale : m ^ 2 ≤ b + c)
    (hzeros : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H → m ≤ ρ.1.re ∧ ρ.1.re ≤ 1 - m)
    (ht : ∀ j ∈ J, 2 * |ω j * t| ≤ H)
    (S : Finset NontrivialZetaZero) (hS : ∀ ρ ∈ S, |ρ.1.im| ≤ H) :
    let σ := 1 - m;
    (∑ j ∈ J, w j * (∑ ρ ∈ S, contribution (b + c) σ (ω j * t) ρ)) +
      (∑ j ∈ J, w j * primeSum (2 * σ - 1) (b + c) (ω j * t)) ≤
      (∑ j ∈ J, w j * (polePair (b + c) σ (ω j * t) - Real.log Real.pi / 4 +
        digammaAverage (2 * σ - 1) b c (ω j * t))) +
      (∑ j ∈ J, w j) * allowance (b + c) H := by
  let σ := 1 - m
  change (∑ j ∈ J, w j * (∑ ρ ∈ S, contribution (b + c) σ (ω j * t) ρ)) +
    (∑ j ∈ J, w j * primeSum (2 * σ - 1) (b + c) (ω j * t)) ≤ _
  have hσ : 1 / 2 ≤ σ := by dsimp [σ]; linarith
  have hbound : (∑ j ∈ J, w j * (∑ ρ ∈ S, contribution (b + c) σ (ω j * t) ρ)) ≤
      ∑ j ∈ J, w j * ((∑' ρ : NontrivialZetaZero, contribution (b + c) σ (ω j * t) ρ) +
        allowance (b + c) H) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (selected_zero_sum_le_full_add_allowance (add_pos hb hc) (ht j hj) hH hm hmu hscale
        hzeros S hS) (hw j hj)
  simp_rw [zero_side_eq_poles_digamma_sub_prime hb hc hσ, mul_add, mul_sub] at hbound
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul] at hbound
  linarith

/-- Applying the proved prime sign to the richer budget gives the
nonnegative-test version. The full signed prime expression remains in
`selected_zero_phase_budget_with_prime` for stronger arithmetic estimates. -/
theorem selected_zero_phase_budget {ι : Type*} (J : Finset ι) (w ω : ι → ℝ)
    (hw : ∀ j ∈ J, 0 ≤ w j)
    (hphase : ∀ x : ℝ, 0 ≤ ∑ j ∈ J, w j * Real.cos (ω j * x))
    {m H b c t : ℝ} (hH : 1 ≤ H) (hb : 0 < b) (hc : 0 < c)
    (hm : zetaPoleReserveZeroMargin H ≤ m) (hmu : m ≤ 1 / 4) (hscale : m ^ 2 ≤ b + c)
    (hzeros : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H → m ≤ ρ.1.re ∧ ρ.1.re ≤ 1 - m)
    (ht : ∀ j ∈ J, 2 * |ω j * t| ≤ H)
    (S : Finset NontrivialZetaZero) (hS : ∀ ρ ∈ S, |ρ.1.im| ≤ H) :
    let σ := 1 - m;
    (∑ j ∈ J, w j * (∑ ρ ∈ S, contribution (b + c) σ (ω j * t) ρ)) ≤
      (∑ j ∈ J, w j * (polePair (b + c) σ (ω j * t) - Real.log Real.pi / 4 +
        digammaAverage (2 * σ - 1) b c (ω j * t))) +
      (∑ j ∈ J, w j) * allowance (b + c) H := by
  have h := selected_zero_phase_budget_with_prime J w ω hw hH hb hc hm hmu hscale hzeros ht S hS
  have hp := prime_phase_nonneg J w ω (by linarith : 0 ≤ 2 * (1 - m) - 1)
    (add_pos hb hc) hphase t
  dsimp only at h ⊢
  linarith

/-- The full resonant pair budget works for every proved larger common
margin and every admissible finite phase family. The genuine multiplicity
and both distinct horizontal partners are retained in the source. -/
theorem resonant_pair_phase_bound {ι : Type*} (J : Finset ι) (w ω : ι → ℝ)
    (hw : ∀ j ∈ J, 0 ≤ w j)
    (hphase : ∀ x : ℝ, 0 ≤ ∑ j ∈ J, w j * Real.cos (ω j * x))
    {m H b c : ℝ} (hH : 1 ≤ H) (hb : 0 < b) (hc : 0 < c)
    (hm : zetaPoleReserveZeroMargin H ≤ m) (hmu : m ≤ 1 / 4)
    (hscale : m ^ 2 ≤ b + c) (hupper : b + c ≤ 1)
    (hzeros : ∀ η : NontrivialZetaZero, |η.1.im| ≤ H → m ≤ η.1.re ∧ η.1.re ≤ 1 - m)
    (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re) (hheight : |ρ.1.im| ≤ H)
    (ht : ∀ j ∈ J, 2 * |ω j * ρ.1.im| ≤ H)
    (j₀ : ι) (hj₀ : j₀ ∈ J) (hω : ω j₀ = 1) :
    let σ := 1 - m;
    w j₀ * (analyticZetaZeroMultiplicity ρ : ℝ) * halfGaussian (b + c) (σ - ρ.1.re) ≤
      (∑ j ∈ J, w j * (poleUpper (b + c) σ (ω j * ρ.1.im) +
        (Real.log (5 / 4 + |ω j * ρ.1.im|) - Real.log Real.pi) / 4 +
        7 / (8 * (5 / 4 + |ω j * ρ.1.im|)))) +
          (∑ j ∈ J, w j) * allowance (b + c) H := by
  let σ := 1 - m
  let S : Finset NontrivialZetaZero := {ρ, NontrivialZetaZero.conjugatePartner ρ}
  have hS : ∀ η ∈ S, |η.1.im| ≤ H := by
    intro η hη
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hη
    rcases hη with rfl | rfl
    · exact hheight
    · simpa [NontrivialZetaZero.conjugatePartner_coe] using hheight
  have hmpos := (zetaPoleReserveZeroMargin_bounds H).1.trans_le hm
  have hσ0 : 1 / 2 ≤ σ := by dsimp [σ]; linarith
  have hσ1 : σ ≤ 1 := by dsimp [σ]; linarith
  have hσscale : (1 - σ) ^ 2 ≤ b + c := by simpa [σ] using hscale
  have hB : 0 < b + c := add_pos hb hc
  have hre : ρ.1.re ≤ σ := (hzeros ρ hheight).2
  have hn (j : ι) (hj : j ∈ J) :
      0 ≤ w j * ∑ η ∈ S, contribution (b + c) σ (ω j * ρ.1.im) η := by
    apply mul_nonneg (hw j hj)
    apply Finset.sum_nonneg
    intro η hη
    exact contribution_nonneg_of_strip hB hmu (ω j * ρ.1.im) η
      (hzeros η (hS η hη)).1 (hzeros η (hS η hη)).2
  have hsource : w j₀ * (analyticZetaZeroMultiplicity ρ : ℝ) *
      halfGaussian (b + c) (σ - ρ.1.re) ≤
      w j₀ * ∑ η ∈ S, contribution (b + c) σ (ω j₀ * ρ.1.im) η := by
    rw [hω, one_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (halfGaussian_le_partner_pair hB ρ hρ hre) (hw j₀ hj₀)
  have hphasebudget := selected_zero_phase_budget J w ω hw hphase hH hb hc hm hmu
    hscale hzeros ht S hS
  have ha : 0 < 2 * σ - 1 := by dsimp [σ]; linarith
  have hau : 2 * σ - 1 ≤ 1 := by linarith
  apply (hsource.trans (Finset.single_le_sum hn hj₀)).trans
  apply hphasebudget.trans
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (hw j hj)
  have hp := polePair_le_poleUpper hB hσ0 hσ1 hσscale (ω j * ρ.1.im)
  have hg := digammaAverage_le_uniform_quarter_log ha hau hb hc hupper (ω j * ρ.1.im)
  change polePair (b + c) σ (ω j * ρ.1.im) - Real.log Real.pi / 4 +
    digammaAverage (2 * σ - 1) b c (ω j * ρ.1.im) ≤ _
  linarith

/-- The already proved global Fermi margin discharges every zero-strip
premise of the general budget. The larger interior shift has the same
uniformly vanishing outside allowance, for all finite phase families. -/
theorem fermi_resonant_pair_phase_bound {ι : Type*} (J : Finset ι) (w ω : ι → ℝ)
    (hw : ∀ j ∈ J, 0 ≤ w j)
    (hphase : ∀ x : ℝ, 0 ≤ ∑ j ∈ J, w j * Real.cos (ω j * x))
    {H b c : ℝ} (hH : 1 ≤ H) (hb : 0 < b) (hc : 0 < c)
    (hscale : zetaFermiZeroMargin H ^ 2 ≤ b + c) (hupper : b + c ≤ 1)
    (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re) (hheight : |ρ.1.im| ≤ H)
    (ht : ∀ j ∈ J, 2 * |ω j * ρ.1.im| ≤ H)
    (j₀ : ι) (hj₀ : j₀ ∈ J) (hω : ω j₀ = 1) :
    let σ := 1 - zetaFermiZeroMargin H;
    w j₀ * (analyticZetaZeroMultiplicity ρ : ℝ) * halfGaussian (b + c) (σ - ρ.1.re) ≤
      (∑ j ∈ J, w j * (poleUpper (b + c) σ (ω j * ρ.1.im) +
        (Real.log (5 / 4 + |ω j * ρ.1.im|) - Real.log Real.pi) / 4 +
        7 / (8 * (5 / 4 + |ω j * ρ.1.im|)))) +
          (∑ j ∈ J, w j) * allowance (b + c) H := by
  apply resonant_pair_phase_bound J w ω hw hphase hH hb hc
    (zetaPoleReserve_margin_le_fermi H) (zetaFermiZeroMargin_bounds H).2.le
    hscale hupper ?_ ρ hρ hheight ht j₀ hj₀ hω
  intro η hη
  have hm := zetaFermiZeroMargin_antitone_abs
    (show |η.1.im| ≤ |H| by rwa [abs_of_nonneg (by linarith : 0 ≤ H)])
  have hz := nontrivialZetaZero_mem_fermi_strip η
  exact ⟨hm.trans hz.1.le, by linarith [hz.2]⟩

end
end RiemannGaussian.GaussianFermiMarginBudget
