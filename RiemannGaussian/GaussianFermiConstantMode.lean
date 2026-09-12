/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiFisherTail

/-!
# Removing the leading constant-mode pole with its actual prime sum

The closed-strip curvature bound controls the entire bounded-height zero
sum at evaluation frequency zero independently of Gaussian width. The
new uniform outside allowance pays for the remaining divisor. In the exact
formula, the nonoscillatory prime term therefore cancels the constant-mode
pole and gamma term up to a bounded divisor cost and the vanishing allowance.
The nonconstant signed prime combination remains explicit in the phase budget.
-/

namespace RiemannGaussian.GaussianFermiConstantMode
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology Classical
open GaussianFermiZeroPair GaussianFermiZeroTail GaussianFermiMovingAllowance
open FermiLaplaceReflection GaussianFermiFisherBound GaussianFermiMarginBudget
open GaussianFermiPoleFormula GaussianFermiPrimeFormula
open GaussianFermiPhaseBudget
open GaussianFermiFisherTail

/-- The finite total divisor allowance at zero evaluation frequency. It
contains every genuine analytic multiplicity and no Gaussian width. -/
def divisorCost : ℝ := (4 * Real.sqrt Real.pi + 2) * ∑' ρ : NontrivialZetaZero, divisorWeight ρ

/-- The constant-mode divisor allowance has nonnegative sign. -/
theorem divisorCost_nonneg : 0 ≤ divisorCost :=
  mul_nonneg (by positivity) (tsum_nonneg divisorWeight_nonneg)

/-- Every enclosed actual zero has a width-independent contribution bound
at frequency zero. The original factor of one half is retained. -/
theorem abs_contribution_zero_le {B σ : ℝ} (hB : 0 < B) (hBu : B ≤ 1)
    (hσ : 1 / 2 < σ) (hσu : σ ≤ 1) (ρ : NontrivialZetaZero)
    (hl : 1 - σ ≤ ρ.1.re) (hr : ρ.1.re ≤ σ) :
    |contribution B σ 0 ρ| ≤ (4 * Real.sqrt Real.pi + 2) * divisorWeight ρ := by
  have him := nontrivialZetaZero_im_sq_gt_three ρ
  have hne : -ρ.1.im ≠ 0 := by intro h; nlinarith
  have he : ((2 * σ - 1 : ℝ) : ℂ) - starRingEnd ℂ ((σ : ℂ) - ρ.1) =
      (σ : ℂ) - (1 - starRingEnd ℂ ρ.1) := by
    push_cast
    simp only [map_sub, Complex.conj_ofReal]
    ring
  have hp := abs_physical_pair_re_le_uniform (a := 2 * σ - 1) (z := (σ : ℂ) - ρ.1)
    (by linarith) (by linarith) hB hBu (by simpa using hr) (by simp; linarith) (by simpa using hne)
  simp only [he, Complex.sub_im, Complex.ofReal_im, zero_sub, neg_sq] at hp
  have hm : 0 ≤ (analyticZetaZeroMultiplicity ρ : ℝ) := Nat.cast_nonneg _
  have hm2 : 0 ≤ (analyticZetaZeroMultiplicity ρ : ℝ) / 2 := by positivity
  have hC : 0 ≤ 4 * Real.sqrt Real.pi + 2 := by positivity
  unfold contribution
  simp only [Complex.ofReal_zero, zero_mul, add_zero, abs_mul,
    abs_of_nonneg hm2]
  apply (mul_le_mul_of_nonneg_left hp hm2).trans
  unfold divisorWeight
  rw [div_mul_div_comm, ← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * ρ.1.im ^ 2) (by positivity)).mpr
  have hd : 1 + ρ.1.im ^ 2 ≤ 2 * ρ.1.im ^ 2 := by linarith
  exact (mul_le_mul_of_nonneg_left hd (mul_nonneg hm hC)).trans_eq (by ring)

/-- The complete inside-band zero sum at frequency zero has one bound for
all positive widths at most one and every valid common band margin. -/
theorem abs_tsum_inside_zero_le {B m H : ℝ} (hB : 0 < B) (hBu : B ≤ 1)
    (hm : 0 ≤ m) (hmu : m ≤ 1 / 4) (hH : 0 ≤ H)
    (hzeros : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H → m ≤ ρ.1.re ∧ ρ.1.re ≤ 1 - m) :
    |∑' ρ : NontrivialZetaZero, inside B (1 - m) 0 H ρ| ≤ divisorCost := by
  have hi : Summable (inside B (1 - m) 0 H) :=
    summable_of_hasFiniteSupport (finite_support_inside B (1 - m) 0 hH)
  have hp (ρ : NontrivialZetaZero) : |inside B (1 - m) 0 H ρ| ≤
      (4 * Real.sqrt Real.pi + 2) * divisorWeight ρ := by
    unfold inside
    split_ifs with hρ
    · exact abs_contribution_zero_le hB hBu (by linarith) (by linarith) ρ
        (by simpa using (hzeros ρ hρ).1) (hzeros ρ hρ).2
    · simpa using mul_nonneg (by positivity : 0 ≤ 4 * Real.sqrt Real.pi + 2) (divisorWeight_nonneg ρ)
  calc
    _ ≤ ∑' ρ : NontrivialZetaZero, |inside B (1 - m) 0 H ρ| := norm_tsum_le_tsum_norm hi.norm
    _ ≤ ∑' ρ : NontrivialZetaZero, (4 * Real.sqrt Real.pi + 2) * divisorWeight ρ :=
      hi.norm.tsum_le_tsum hp (summable_divisorWeight.mul_left _)
    _ = _ := by rw [tsum_mul_left]; rfl

/-- The entire zero sum, including the outside divisor, is bounded at
zero frequency by a width-independent constant plus the improved allowance. -/
theorem abs_zero_side_zero_le {B m H : ℝ} (hB : 0 < B) (hBu : B ≤ 1) (hH : 1 ≤ H)
    (hm : 0 ≤ m) (hmu : m ≤ 1 / 4) (hscale : m ^ 2 ≤ B)
    (hzeros : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H → m ≤ ρ.1.re ∧ ρ.1.re ≤ 1 - m) :
    |∑' ρ : NontrivialZetaZero, contribution B (1 - m) 0 ρ| ≤ divisorCost + tailAllowance H := by
  have hσ : 1 / 2 ≤ 1 - m := by linarith
  have hσu : 1 - m ≤ 1 := by linarith
  have hs : (1 - (1 - m)) ^ 2 ≤ B := by simpa using hscale
  have ht : 2 * |(0 : ℝ)| ≤ H := by simpa using (show 0 ≤ H by linarith)
  have hi := abs_tsum_inside_zero_le hB hBu hm hmu (by linarith) hzeros
  have ho := abs_tsum_outside_le_uniform hB hBu (by linarith : 1 / 2 < 1 - m) hσu hs ht hH
  rw [zero_sum_eq_inside_add_outside hB hσ hσu hs ht hH]
  exact (abs_add_le _ _).trans (add_le_add hi ho)

/-- The nonoscillatory prime term cancels its exact pole and gamma terms,
up to a bounded divisor allowance and the improved outside-band error. -/
theorem abs_constant_prime_residual_le {m H b c : ℝ} (hH : 1 ≤ H)
    (hb : 0 < b) (hc : 0 < c) (hu : b + c ≤ 1)
    (hm : 0 ≤ m) (hmu : m ≤ 1 / 4) (hscale : m ^ 2 ≤ b + c)
    (hzeros : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H → m ≤ ρ.1.re ∧ ρ.1.re ≤ 1 - m) :
    |polePair (b + c) (1 - m) 0 - Real.log Real.pi / 4 +
      digammaAverage (1 - 2 * m) b c 0 - primeSum (1 - 2 * m) (b + c) 0| ≤
        divisorCost + tailAllowance H := by
  have he := zero_side_eq_poles_digamma_sub_prime hb hc (by linarith : 1 / 2 ≤ 1 - m) 0
  rw [show 2 * (1 - m) - 1 = 1 - 2 * m by ring] at he
  rw [← he]
  exact abs_zero_side_zero_le (add_pos hb hc) hu hH hm hmu hscale hzeros

/-- The proved global Fermi margin discharges all zero-location premises
of the constant-mode arithmetic cancellation. -/
theorem abs_fermi_constant_prime_residual_le {H b c : ℝ} (hH : 1 ≤ H)
    (hb : 0 < b) (hc : 0 < c) (hu : b + c ≤ 1)
    (hs : zetaFermiZeroMargin H ^ 2 ≤ b + c) :
    let m := zetaFermiZeroMargin H;
    |polePair (b + c) (1 - m) 0 - Real.log Real.pi / 4 +
      digammaAverage (1 - 2 * m) b c 0 - primeSum (1 - 2 * m) (b + c) 0| ≤
        divisorCost + tailAllowance H := by
  apply abs_constant_prime_residual_le hH hb hc hu (zetaFermiZeroMargin_bounds H).1.le
    (zetaFermiZeroMargin_bounds H).2.le hs
  intro ρ hρ
  have hm := zetaFermiZeroMargin_antitone_abs
    (show |ρ.1.im| ≤ |H| by rwa [abs_of_nonneg (by linarith : 0 ≤ H)])
  have hz := nontrivialZetaZero_mem_fermi_strip ρ
  exact ⟨hm.trans hz.1.le, by linarith [hz.2]⟩

/-- Retaining the constant-frequency prime term removes its entire pole
and gamma cost from the general phase budget. The remaining signed prime
combination is kept intact; no favorable sign for it is assumed. -/
theorem selected_budget_without_constant_pole {ι : Type*} (J : Finset ι) (w ω : ι → ℝ)
    (hw : ∀ j ∈ J, 0 ≤ w j) (j₀ : ι) (hj₀ : j₀ ∈ J) (hω₀ : ω j₀ = 0)
    {m H b c t : ℝ} (hH : 1 ≤ H) (hb : 0 < b) (hc : 0 < c) (hu : b + c ≤ 1)
    (hm : 0 ≤ m) (hmu : m ≤ 1 / 4) (hscale : m ^ 2 ≤ b + c)
    (hzeros : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H → m ≤ ρ.1.re ∧ ρ.1.re ≤ 1 - m)
    (ht : ∀ j ∈ J, 2 * |ω j * t| ≤ H)
    (S : Finset NontrivialZetaZero) (hS : ∀ ρ ∈ S, |ρ.1.im| ≤ H) :
    (∑ j ∈ J, w j * ∑ ρ ∈ S, contribution (b + c) (1 - m) (ω j * t) ρ) +
      (∑ j ∈ J.erase j₀, w j * primeSum (1 - 2 * m) (b + c) (ω j * t)) ≤
      (∑ j ∈ J.erase j₀, w j * (polePair (b + c) (1 - m) (ω j * t) -
        Real.log Real.pi / 4 + digammaAverage (1 - 2 * m) b c (ω j * t))) +
      w j₀ * divisorCost + ((∑ j ∈ J, w j) + w j₀) * tailAllowance H := by
  have h := selected_zero_phase_budget_with_uniform_tail J w ω hw hH hb hc hu
    hm hmu hscale hzeros ht S hS
  have hp := Finset.sum_erase_add J
    (fun j => w j * primeSum (1 - 2 * m) (b + c) (ω j * t)) hj₀
  have hk := Finset.sum_erase_add J
    (fun j => w j * (polePair (b + c) (1 - m) (ω j * t) - Real.log Real.pi / 4 +
      digammaAverage (1 - 2 * m) b c (ω j * t))) hj₀
  simp only [hω₀, zero_mul] at hp hk
  have hzero := (abs_le.mp (abs_constant_prime_residual_le hH hb hc hu hm hmu hscale hzeros)).2
  have hwzero := mul_le_mul_of_nonneg_left hzero (hw j₀ hj₀)
  nlinarith

/-- The original global Fermi margin instantiates the phase budget with
the leading constant-mode pole removed, for every finite phase family. -/
theorem fermi_selected_budget_without_constant_pole {ι : Type*} (J : Finset ι) (w ω : ι → ℝ)
    (hw : ∀ j ∈ J, 0 ≤ w j) (j₀ : ι) (hj₀ : j₀ ∈ J) (hω₀ : ω j₀ = 0)
    {H b c t : ℝ} (hH : 1 ≤ H) (hb : 0 < b) (hc : 0 < c) (hu : b + c ≤ 1)
    (hscale : zetaFermiZeroMargin H ^ 2 ≤ b + c)
    (ht : ∀ j ∈ J, 2 * |ω j * t| ≤ H)
    (S : Finset NontrivialZetaZero) (hS : ∀ ρ ∈ S, |ρ.1.im| ≤ H) :
    let m := zetaFermiZeroMargin H;
    (∑ j ∈ J, w j * ∑ ρ ∈ S, contribution (b + c) (1 - m) (ω j * t) ρ) +
      (∑ j ∈ J.erase j₀, w j * primeSum (1 - 2 * m) (b + c) (ω j * t)) ≤
      (∑ j ∈ J.erase j₀, w j * (polePair (b + c) (1 - m) (ω j * t) -
        Real.log Real.pi / 4 + digammaAverage (1 - 2 * m) b c (ω j * t))) +
      w j₀ * divisorCost + ((∑ j ∈ J, w j) + w j₀) * tailAllowance H := by
  apply selected_budget_without_constant_pole J w ω hw j₀ hj₀ hω₀ hH hb hc hu
    (zetaFermiZeroMargin_bounds H).1.le (zetaFermiZeroMargin_bounds H).2.le hscale ?_ ht S hS
  intro ρ hρ
  have hm := zetaFermiZeroMargin_antitone_abs
    (show |ρ.1.im| ≤ |H| by rwa [abs_of_nonneg (by linarith : 0 ≤ H)])
  have hz := nontrivialZetaZero_mem_fermi_strip ρ
  exact ⟨hm.trans hz.1.le, by linarith [hz.2]⟩

/-- Beyond one proved height, every admissible Gaussian split has a
constant-mode residual below the same finite divisor cost plus any prescribed
positive tolerance. The height is independent of the chosen split. -/
theorem eventually_constant_prime_residual_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ b c : ℝ, 0 < b → 0 < c → b + c ≤ 1 →
      zetaFermiZeroMargin H ^ 2 ≤ b + c →
      let m := zetaFermiZeroMargin H;
      |polePair (b + c) (1 - m) 0 - Real.log Real.pi / 4 +
        digammaAverage (1 - 2 * m) b c 0 - primeSum (1 - 2 * m) (b + c) 0| <
          divisorCost + ε := by
  filter_upwards [tendsto_tailAllowance.eventually (gt_mem_nhds hε),
    eventually_ge_atTop (1 : ℝ)] with H htail hH
  intro b c hb hc hu hs
  exact (abs_fermi_constant_prime_residual_le hH hb hc hu hs).trans_lt
    (add_lt_add_right htail divisorCost)

end
end RiemannGaussian.GaussianFermiConstantMode
