/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorGcdAudit
import RiemannGaussian.ZetaPrimeWindow
import RiemannGaussian.EtaZetaPrimeProduct

/-!
# Twisted Gaussian/GCD positivity fails beyond every head, at every height

The earlier negative diagonal used one specially chosen height and prime two.
Here the existing unconditional prime-window theorem gives actual primes in
cofinal negative phase bands for EVERY fixed nonzero height. A unit-diagonal
Gaussian Schur multiplier cannot remove those diagonals. This rejects bulk
PSD based on head deletion; it does not estimate any joined signed statistic.
-/

namespace RiemannGaussian.ArithmeticOperatorTwistedBulkAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorGcdAudit SuzukiCarryCorrelation PrimeWindow
open scoped BigOperators Topology

/-- Left endpoint of a negative half-cycle, with its literal height kept. -/
def phaseScale (y : ℝ) (J : ℕ) : ℝ :=
  Real.exp (((J : ℝ)*(2*Real.pi)+Real.pi)/|y|)

/-- Fixed multiplicative width of one radian in logarithmic coordinates. -/
def phaseWidth (y : ℝ) : ℝ := Real.exp (1/|y|)

theorem phaseScale_tendsto {y : ℝ} (hy : y ≠ 0) :
    Tendsto (phaseScale y) atTop atTop := by
  have ha : 0 < |y| := abs_pos.mpr hy
  have ht : Tendsto (fun J : ℕ => (J : ℝ)*((2*Real.pi)/|y|)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const
      (div_pos (by positivity : 0 < 2*Real.pi) ha)
  unfold phaseScale
  convert Real.tendsto_exp_atTop.comp
    (tendsto_atTop_add_const_right atTop (Real.pi/|y|) ht) using 1
  funext J
  congr 1
  ring

/-- Every sufficiently late literal phase band has an actual prime.
The prime theorem is used only for a counterexample to positivity. -/
theorem eventually_prime_in_phaseBand {y : ℝ} (hy : y ≠ 0) :
    ∀ᶠ J : ℕ in atTop, ∃ p ∈ primesInWindow (phaseScale y J) (phaseWidth y), True := by
  have ha : 1 < phaseWidth y := by
    unfold phaseWidth
    exact Real.one_lt_exp_iff.mpr (div_pos zero_lt_one (abs_pos.mpr hy))
  have ht := (theta_interval_div_tendsto (zero_lt_one.trans ha)).comp
    (phaseScale_tendsto hy)
  have hp := ht.eventually (eventually_gt_nhds (by linarith : (0 : ℝ) < phaseWidth y-1))
  filter_upwards [hp] with J hJ
  have hpos : 0 < phaseScale y J := Real.exp_pos _
  have hd := (lt_div_iff₀ hpos).mp hJ
  rw [zero_mul] at hd
  have hs := sum_log_primesInWindow hpos.le ha.le
  have hn : (primesInWindow (phaseScale y J) (phaseWidth y)).Nonempty := by
    by_contra hh
    rw [Finset.not_nonempty_iff_eq_empty.mp hh, Finset.sum_empty] at hs
    linarith
  obtain ⟨p,hp⟩ := hn
  exact ⟨p,hp, trivial⟩

/-- This is the exact phase window, not a rounded or sampled phase. -/
theorem phaseBand_cos_le {y : ℝ} (hy : y ≠ 0) {J p : ℕ}
    (hp : p ∈ primesInWindow (phaseScale y J) (phaseWidth y)) :
    Real.cos (y*Real.log p) ≤ -(1/2 : ℝ) := by
  have ha : 0 < |y| := abs_pos.mpr hy
  obtain ⟨hlo,hup,hprime⟩ := mem_primesInWindow_bounds (Real.exp_pos _).le
    (Real.exp_pos _).le hp
  have hl := Real.log_lt_log (Real.exp_pos _) hlo
  have hu := Real.log_le_log (by exact_mod_cast hprime.pos) hup
  rw [Real.log_exp] at hl
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_exp] at hu
  have hl' := (div_lt_iff₀ ha).mp hl
  have hu' := (mul_le_mul_of_nonneg_left hu ha.le)
  have hb : |y| * (1/|y|+((J : ℝ)*(2*Real.pi)+Real.pi)/|y|) =
      1+(J : ℝ)*(2*Real.pi)+Real.pi := by field_simp; ring
  rw [hb] at hu'
  let v : ℝ := |y| * Real.log p-((J : ℝ)*(2*Real.pi)+Real.pi)
  have hv0 : 0 ≤ v := by dsimp [v]; linarith
  have hv1 : v ≤ 1 := by dsimp [v]; linarith
  have hc : (1/2 : ℝ) ≤ Real.cos v := by
    have hs : v^2 ≤ 1 := by nlinarith
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := v)]
  have he : |y| * Real.log p = (v+Real.pi)+(J : ℝ)*(2*Real.pi) := by dsimp [v]; ring
  have hcos : Real.cos (y*Real.log p) = Real.cos (|y| * Real.log p) := by
    rcases le_total 0 y with hy0 | hy0
    · rw [abs_of_nonneg hy0]
    · rw [abs_of_nonpos hy0, neg_mul, Real.cos_neg]
  rw [hcos, he, Real.cos_add_nat_mul_two_pi, Real.cos_add_pi]
  linarith

/-- At an ordinary prime the diagonal retains its entire actual weight
and phase. Proper powers are absent because they do not divide that row. -/
theorem prime_diagonal_re {p : ℕ} (hp : p.Prime) (y : ℝ) :
    (gcdKernel (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d) p p).re =
      Real.log p*Real.cos (y*Real.log p) := by
  rw [gcdKernel, Nat.gcd_self, hp.divisors]
  simp only [Finset.sum_pair hp.ne_one.symm,
    ArithmeticFunction.vonMangoldt_apply_prime hp,
    ArithmeticFunction.vonMangoldt_apply_one, Complex.ofReal_zero, zero_mul]
  simp only [primePhase, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_re, Complex.neg_re, Complex.neg_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, one_mul, zero_add,
    sub_zero, neg_zero, neg_mul, Real.exp_zero, Real.cos_neg]

/-- There is no paid-head rescue of unrestricted twisted bulk PSD:
negative actual-prime diagonals persist at every fixed nonzero height. -/
theorem exists_negative_prime_diagonal_above {y : ℝ} (hy : y ≠ 0) (H : ℕ) :
    ∃ p : ℕ, H < p ∧ p.Prime ∧
      (gcdKernel (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d) p p).re < 0 := by
  have hbig := (phaseScale_tendsto hy).eventually (eventually_gt_atTop (H : ℝ))
  obtain ⟨J,hJ,hH⟩ := ((eventually_prime_in_phaseBand hy).and hbig).exists
  obtain ⟨p,hp,_⟩ := hJ
  obtain ⟨hlo,_,hprime⟩ := mem_primesInWindow_bounds (Real.exp_pos _).le
    (Real.exp_pos _).le hp
  refine ⟨p,by exact_mod_cast hH.trans hlo, hprime, ?_⟩
  rw [prime_diagonal_re hprime]
  have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
  have hc := phaseBand_cos_le hy hp
  nlinarith

/-- A usual Gaussian Schur factor has unit diagonal. At every height,
no fixed head deletion makes the full twisted matrix positive. -/
theorem exists_negative_schur_diagonal_above {y : ℝ} (hy : y ≠ 0)
    (H : ℕ) (g : ℕ → ℕ → ℂ) (hg : ∀ p, H < p → p.Prime → g p p = 1) :
    ∃ p : ℕ, H < p ∧ p.Prime ∧
      (g p p*gcdKernel (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d) p p).re < 0 := by
  obtain ⟨p,hH,hp,hn⟩ := exists_negative_prime_diagonal_above hy H
  exact ⟨p,hH,hp,by simpa only [hg p hH hp, one_mul] using hn⟩

/-- In particular the obstruction is present at every actual or
hypothetical nontrivial-zero ordinate, not merely a synthetic height. -/
theorem exists_negative_diagonal_at_zero_height (rho : NontrivialZetaZero) (H : ℕ) :
    ∃ p : ℕ, H < p ∧ p.Prime ∧
      (gcdKernel (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase rho.1.im d) p p).re < 0 :=
  exists_negative_prime_diagonal_above (NontrivialZetaZero.im_ne_zero_of_eta_mass rho) H

/-- The failed claim is unrestricted bulk positivity, not the sign
of a particular joined signed packet. No zero is excluded here. -/
theorem not_all_bulk_prime_diagonals_nonnegative {y : ℝ} (hy : y ≠ 0) (H : ℕ) :
    ¬ ∀ p : ℕ, H < p → p.Prime →
      0 ≤ (gcdKernel (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d) p p).re := by
  obtain ⟨p,hH,hp,hn⟩ := exists_negative_prime_diagonal_above hy H
  exact fun hh => (not_lt_of_ge (hh p hH hp)) hn

end
end RiemannGaussian.ArithmeticOperatorTwistedBulkAudit
