/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerBoundaryControl
import RiemannGaussian.ZetaRegularCorrectionVariation
import RiemannGaussian.ZetaLogLogZeroFree

/-!
# Small signed Euler responses from the actual log-log zero-free gap

Horizontal Poisson differences retain their exact numerator before estimation.
Near atoms use the actual zero-free gap; far atoms have a favorable signed
change and are dominated by the complete mass on the fixed line `3/2`.
All zero multiplicities and both signs of the total difference are retained.

The proved log-log region supplies arbitrarily large fixed reciprocal-logarithm
gaps at sufficiently large heights. A tunable Euler shift then gives, for every
positive epsilon, an eventual `epsilon * log(abs(t)+26)` bound for the real
pole-removed logarithmic derivative, uniformly on `1 <= sigma <= 3`.
The height threshold depends on epsilon and is not numerically evaluated.
This is a consequence of the existing region, not a new zero-free region or RH.
-/

namespace RiemannGaussian.ZetaEulerPoissonDifference
noncomputable section
open Complex Filter
open scoped Topology

/-- The real Poisson atom, with its horizontal and vertical coordinates separate. -/
def atom (a r : ℝ) : ℝ := a / (a ^ 2 + r ^ 2)

/-- A nonnegative horizontal coordinate gives a nonnegative Poisson atom. -/
theorem atom_nonneg {a : ℝ} (ha : 0 ≤ a) (r : ℝ) : 0 ≤ atom a r := by
  unfold atom
  positivity

/-- The exact signed horizontal difference before any absolute value or zero sum. -/
theorem atom_difference {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) (r : ℝ) :
    atom (a + h) r - atom a r =
      h * (r ^ 2 - a * (a + h)) /
        ((a ^ 2 + r ^ 2) * ((a + h) ^ 2 + r ^ 2)) := by
  have h₁ : a ^ 2 + r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have h₂ : (a + h) ^ 2 + r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold atom
  field_simp
  ring

/-- Both signs of the horizontal change are bounded by the relative shift times the shifted atom. -/
theorem abs_atom_difference_le {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) (r : ℝ) :
    |atom (a + h) r - atom a r| ≤ (h / a) * atom (a + h) r := by
  have hb : 0 < a + h := by linarith
  have h₁ : 0 < a ^ 2 + r ^ 2 := by positivity
  have h₂ : 0 < (a + h) ^ 2 + r ^ 2 := by positivity
  rw [atom_difference ha hh, abs_div, abs_of_pos (mul_pos h₁ h₂),
    abs_mul, abs_of_nonneg hh]
  unfold atom
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (mul_pos h₁ h₂) (mul_pos ha h₂)).mpr
  have he : a * |r ^ 2 - a * (a + h)| ≤ (a + h) * (a ^ 2 + r ^ 2) := by
    have he' : |a * (r ^ 2 - a * (a + h))| ≤ (a + h) * (a ^ 2 + r ^ 2) := by
      rw [abs_le]
      constructor <;> nlinarith [mul_nonneg hh (sq_nonneg r),
        mul_nonneg ha.le (sq_nonneg r), mul_nonneg hb.le (sq_nonneg a)]
    simpa only [abs_mul, abs_of_pos ha] using he'
  have hm := mul_le_mul_of_nonneg_left he (mul_nonneg hh h₂.le)
  nlinarith only [hm]

/-- Beyond the geometric turning point the atom increases under the horizontal shift. -/
theorem far_atom_difference {a h r : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (hfar : a * (a + h) ≤ r ^ 2) :
    0 ≤ atom (a + h) r - atom a r := by
  rw [atom_difference ha hh]
  positivity

/-- The signed increase is bounded by the shift times the inverse squared vertical distance. -/
theorem far_atom_difference_le {a h r : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (hr : 0 < r ^ 2) : atom (a + h) r - atom a r ≤ h / r ^ 2 := by
  have h₁ : 0 < a ^ 2 + r ^ 2 := by positivity
  have h₂ : 0 < (a + h) ^ 2 + r ^ 2 := by positivity
  rw [atom_difference ha hh]
  apply (div_le_div_iff₀ (mul_pos h₁ h₂) hr).mpr
  have hb : 0 ≤ a + h := by linarith
  have hs := mul_nonneg (sq_nonneg a) (sq_nonneg (a + h))
  have hq := mul_nonneg (sq_nonneg a) hr.le
  have ht := mul_nonneg (sq_nonneg (a + h)) hr.le
  have hu := mul_nonneg (mul_nonneg ha.le hb) hr.le
  have he : (r ^ 2 - a * (a + h)) * r ^ 2 ≤
      (a ^ 2 + r ^ 2) * ((a + h) ^ 2 + r ^ 2) := by
    nlinarith only [hs, hq, ht, hu]
  nlinarith only [mul_le_mul_of_nonneg_left he hh]

/-- A far inverse-square tail is dominated by a reference atom with horizontal coordinate between one half and three halves. -/
theorem far_reciprocal_le_atom {a r : ℝ} (ha : 1 / 2 ≤ a)
    (ha' : a ≤ 3 / 2) (hr : 4 < |r|) : 1 / r ^ 2 ≤ 4 * atom a r := by
  have hr16 : 16 < r ^ 2 := by nlinarith [sq_abs r]
  have hap : 0 < a := by linarith
  unfold atom
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
  have ha2 : a ^ 2 ≤ 9 / 4 := by nlinarith
  nlinarith [mul_nonneg (show 0 ≤ 4 * a - 2 by linarith) (sq_nonneg r)]

/-- The actual global zero summand is precisely its full multiplicity times the real Poisson atom. -/
theorem summand_eq_atom (σ t : ℝ) (ρ : NontrivialZetaZero) :
    zetaGlobalPoissonSummand ((σ : ℂ) + I * t) ρ =
      (analyticZetaZeroMultiplicity ρ : ℝ) * atom (σ - ρ.1.re) (t - ρ.1.im) := by
  unfold zetaGlobalPoissonSummand atom
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul, add_zero, zero_add, sub_zero]
  ring

/-- A local zero gap controls nearby atoms; exact far-atom geometry controls the rest. The complete multiplicity remains in each term. -/
theorem abs_summand_difference_le (ρ : NontrivialZetaZero)
    {σ t h d : ℝ} (hσ : 1 ≤ σ) (hσ3 : σ ≤ 3) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hd : 0 < d) (hgap : |t - ρ.1.im| ≤ 4 → d ≤ 1 - ρ.1.re) :
    |zetaGlobalPoissonSummand (((σ + h : ℝ) : ℂ) + I * t) ρ -
        zetaGlobalPoissonSummand ((σ : ℂ) + I * t) ρ| ≤
      (h / d) * zetaGlobalPoissonSummand (((σ + h : ℝ) : ℂ) + I * t) ρ +
        4 * h * zetaGlobalPoissonSummand (((3 / 2 : ℝ) : ℂ) + I * t) ρ := by
  let a := σ - ρ.1.re
  let r := t - ρ.1.im
  let b := 3 / 2 - ρ.1.re
  have ha : 0 < a := by dsimp [a]; linarith [NontrivialZetaZero.re_lt_one ρ]
  have ha3 : a ≤ 3 := by dsimp [a]; linarith [NontrivialZetaZero.zero_lt_re ρ]
  have hb : 1 / 2 ≤ b := by dsimp [b]; linarith [NontrivialZetaZero.re_lt_one ρ]
  have hb3 : b ≤ 3 / 2 := by dsimp [b]; linarith [NontrivialZetaZero.zero_lt_re ρ]
  have he : |atom (a + h) r - atom a r| ≤
      (h / d) * atom (a + h) r + 4 * h * atom b r := by
    by_cases hnear : |r| ≤ 4
    · have hda : d ≤ a := by have hg := hgap hnear; dsimp [a]; linarith
      have hi := div_le_div_of_nonneg_left hh hd hda
      have hh' := (abs_atom_difference_le ha hh r).trans
        (mul_le_mul_of_nonneg_right hi (atom_nonneg (by linarith) r))
      have hp := atom_nonneg (by linarith : 0 ≤ b) r
      nlinarith
    · have hr : 4 < |r| := lt_of_not_ge hnear
      have hr16 : 16 < r ^ 2 := by nlinarith [sq_abs r]
      have hab : a * (a + h) ≤ r ^ 2 := by
        have hp := mul_le_mul ha3 (show a + h ≤ 4 by linarith)
          (by linarith : 0 ≤ a + h) (by norm_num : (0 : ℝ) ≤ 3)
        linarith
      rw [abs_of_nonneg (far_atom_difference ha hh hab)]
      have hdif := far_atom_difference_le ha hh (by linarith : 0 < r ^ 2)
      have href := mul_le_mul_of_nonneg_left (far_reciprocal_le_atom hb hb3 hr) hh
      rw [mul_one_div] at href
      have hpos : 0 ≤ (h / d) * atom (a + h) r :=
        mul_nonneg (div_nonneg hh hd.le) (atom_nonneg (by linarith) r)
      nlinarith
  simp only [summand_eq_atom, ← mul_sub, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg (analyticZetaZeroMultiplicity ρ) : (0 : ℝ) ≤ _)]
  have hm := mul_le_mul_of_nonneg_left he
    (Nat.cast_nonneg (analyticZetaZeroMultiplicity ρ) : (0 : ℝ) ≤ _)
  dsimp only [a, b, r] at hm
  rw [show σ + h - ρ.1.re = σ - ρ.1.re + h by ring]
  nlinarith only [hm]

/-- The two-sided difference of complete actual zero masses has a tunable near-gap cost and a fixed-line far cost. Both series are genuinely summable. -/
theorem abs_mass_difference_le {σ t h d : ℝ}
    (hσ : 1 ≤ σ) (hσ3 : σ ≤ 3) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hd : 0 < d)
    (hgap : ∀ ρ : NontrivialZetaZero, |t - ρ.1.im| ≤ 4 → d ≤ 1 - ρ.1.re) :
    |(∑' ρ : NontrivialZetaZero,
        zetaGlobalPoissonSummand (((σ + h : ℝ) : ℂ) + I * t) ρ) -
      ∑' ρ : NontrivialZetaZero, zetaGlobalPoissonSummand ((σ : ℂ) + I * t) ρ| ≤
      (h / d) * (∑' ρ : NontrivialZetaZero,
        zetaGlobalPoissonSummand (((σ + h : ℝ) : ℂ) + I * t) ρ) +
      4 * h * (∑' ρ : NontrivialZetaZero,
        zetaGlobalPoissonSummand (((3 / 2 : ℝ) : ℂ) + I * t) ρ) := by
  have hs := summable_zetaGlobalPoissonSummand
    (s := (σ : ℂ) + I * t) (by simpa using hσ)
  have hsh := summable_zetaGlobalPoissonSummand
    (s := ((σ + h : ℝ) : ℂ) + I * t) (by simpa using (show 1 ≤ σ + h by linarith))
  have hsref := summable_zetaGlobalPoissonSummand
    (s := ((3 / 2 : ℝ) : ℂ) + I * t) (by norm_num)
  rw [← hsh.tsum_sub hs]
  calc
    _ ≤ ∑' ρ : NontrivialZetaZero,
        |zetaGlobalPoissonSummand (((σ + h : ℝ) : ℂ) + I * t) ρ -
          zetaGlobalPoissonSummand ((σ : ℂ) + I * t) ρ| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (hsh.sub hs).norm
    _ ≤ ∑' ρ : NontrivialZetaZero,
        ((h / d) * zetaGlobalPoissonSummand (((σ + h : ℝ) : ℂ) + I * t) ρ +
          4 * h * zetaGlobalPoissonSummand (((3 / 2 : ℝ) : ℂ) + I * t) ρ) := by
      exact (hsh.sub hs).abs.tsum_le_tsum
        (fun ρ => abs_summand_difference_le ρ hσ hσ3 hh hh1 hd (hgap ρ))
        ((hsh.mul_left _).add (hsref.mul_left _))
    _ = _ := by rw [Summable.tsum_add (hsh.mul_left _) (hsref.mul_left _),
        tsum_mul_left, tsum_mul_left]

/-- The already proved log-log region supplies every fixed positive reciprocal-logarithm gap for actual zeros in the four-unit comparison window, above its own threshold. -/
theorem exists_eventual_local_gap {B : ℝ} (hB : 0 < B) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ t : ℝ, T ≤ |t| →
      ∀ ρ : NontrivialZetaZero, |t - ρ.1.im| ≤ 4 →
        B / zetaEulerLogHeight t ≤ 1 - ρ.1.re := by
  let A := ZetaLogLogZeroFree.coefficientLimit / 2
  have hA : 0 < A := half_pos ZetaLogLogZeroFree.coefficientLimit_pos
  have hAlim : A < ZetaLogLogZeroFree.coefficientLimit := by
    dsimp [A]
    linarith [ZetaLogLogZeroFree.coefficientLimit_pos]
  obtain ⟨T₀, _, hmargin⟩ := ZetaLogLogZeroFree.exists_eventual_common_margin hA hAlim
  obtain ⟨T₁, hdom⟩ := eventually_atTop.mp
    (ZetaLogLogWidth.eventually_dominates_logarithmic hA B)
  refine ⟨max 2 (max T₀ T₁), le_max_left _ _, ?_⟩
  intro t ht ρ hnear
  have ht2 : 2 ≤ |t| := (le_max_left _ _).trans ht
  have hT₀ : T₀ ≤ |t| + 4 := by linarith [le_max_left T₀ T₁, le_max_right 2 (max T₀ T₁)]
  have hT₁ : T₁ ≤ |t| + 4 := by linarith [le_max_right T₀ T₁, le_max_right 2 (max T₀ T₁)]
  have hγ : |ρ.1.im| ≤ |t| + 4 := by
    have hh := abs_sub_comm t ρ.1.im
    have htri := abs_add_le (ρ.1.im - t) t
    rw [sub_add_cancel, ← hh] at htri
    linarith
  have hz := (hmargin (|t| + 4) hT₀).2.2 ρ hγ
  have hlog : Real.log (|t| + 4) ≤ zetaEulerLogHeight t :=
    Real.log_le_log (by positivity) (by linarith)
  exact (div_le_div_of_nonneg_left hB.le
    (Real.log_pos (by linarith : 1 < |t| + 4)) hlog).trans
      ((hdom (|t| + 4) hT₁).trans (by linarith [hz.2])).le

/-- The complete shifted zero mass is bounded using the actual Euler series and completion, with an arbitrary positive shift at most one. -/
theorem shifted_mass_le {σ t h : ℝ} (hσ : 1 ≤ σ) (hσ3 : σ ≤ 3)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    (∑' ρ : NontrivialZetaZero,
      zetaGlobalPoissonSummand (((σ + h : ℝ) : ℂ) + I * t) ρ) ≤
      2 / h + 5 + zetaEulerLogHeight t := by
  let u := σ + h
  have hu : 1 < u := by dsimp [u]; linarith
  have hu4 : u ≤ 4 := by dsimp [u]; linarith
  have hi : 1 / (u - 1) ≤ 1 / h :=
    one_div_le_one_div_of_le hh (by dsimp [u]; linarith)
  have hl : Real.log u ≤ 3 := by
    have he := Real.log_le_sub_one_of_pos (by linarith : 0 < u)
    linarith
  have hd := norm_neg_logDeriv_riemannZeta_re_le_real_axis hu t
  rw [Real.norm_eq_abs] at hd
  have hdl := (abs_le.mp hd).1
  have heuler := neg_logDeriv_riemannZeta_real_le_global hu
  have hlog : Real.log (u + |t|) ≤ zetaEulerLogHeight t :=
    Real.log_le_log (by positivity) (by linarith)
  have hp : (u - 1) / ((u - 1) ^ 2 + t ^ 2) ≤ 1 / h := by
    calc
      _ ≤ (u - 1) / (u - 1) ^ 2 := div_le_div_of_nonneg_left (by linarith)
        (sq_pos_of_pos (by linarith)) (by nlinarith [sq_nonneg t])
      _ = 1 / (u - 1) := by field_simp
      _ ≤ 1 / h := hi
  have hmass := zeta_global_vertical_budget_le (by linarith : 0 < u - 1) t
  rw [show 1 + (u - 1) = u by ring] at hmass
  change (∑' ρ : NontrivialZetaZero, zetaGlobalPoissonSummand ((u : ℂ) + I * t) ρ) ≤ _
  linarith [show (2 : ℝ) / h = 2 * (1 / h) by ring]

/-- The real pole-removed response on the shifted Euler line has a height-independent pole bound. -/
theorem shifted_poleRemoved_le {σ t h : ℝ} (hσ : 1 ≤ σ) (hσ3 : σ ≤ 3)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    |(logDeriv riemannZeta₁ (((σ + h : ℝ) : ℂ) + I * t)).re| ≤ 2 / h + 4 := by
  let u := σ + h
  have hu : 1 < u := by dsimp [u]; linarith
  have hu4 : u ≤ 4 := by dsimp [u]; linarith
  have hi : 1 / (u - 1) ≤ 1 / h :=
    one_div_le_one_div_of_le hh (by dsimp [u]; linarith)
  have hl : Real.log u ≤ 3 := by
    have he := Real.log_le_sub_one_of_pos (by linarith : 0 < u)
    linarith
  have hd := norm_neg_logDeriv_riemannZeta_re_le_real_axis hu t
  rw [Real.norm_eq_abs] at hd
  have heuler := neg_logDeriv_riemannZeta_real_le_global hu
  have hs : 1 < (((u : ℂ) + I * t) : ℂ).re := by simpa using hu
  have he := congrArg Complex.re (neg_logDeriv_riemannZeta_eq_pole_sub
    (show (u : ℂ) + I * t ≠ 1 by
      intro hh
      have hhre := congrArg Complex.re hh
      simp at hhre
      linarith) (riemannZeta_ne_zero_of_one_le_re hs.le))
  simp only [Complex.sub_re] at he
  have hp : |(1 / ((u : ℂ) + I * t - 1) : ℂ).re| ≤ 1 / h := by
    have heq : (1 / ((u : ℂ) + I * t - 1) : ℂ).re =
        (u - 1) / ((u - 1) ^ 2 + t ^ 2) := by simp [Complex.normSq_apply, pow_two]
    rw [heq, abs_of_nonneg (by positivity)]
    calc
      _ ≤ (u - 1) / (u - 1) ^ 2 := div_le_div_of_nonneg_left (by linarith)
        (sq_pos_of_pos (by linarith)) (by nlinarith [sq_nonneg t])
      _ = 1 / (u - 1) := by field_simp
      _ ≤ 1 / h := hi
  have ht := abs_sub (1 / ((u : ℂ) + I * t - 1) : ℂ).re
    (-logDeriv riemannZeta ((u : ℂ) + I * t)).re
  change |(logDeriv riemannZeta₁ ((u : ℂ) + I * t)).re| ≤ _
  rw [show (logDeriv riemannZeta₁ ((u : ℂ) + I * t)).re =
    (1 / ((u : ℂ) + I * t - 1) : ℂ).re -
      (-logDeriv riemannZeta ((u : ℂ) + I * t)).re by linarith]
  linarith [show (2 : ℝ) / h = 2 * (1 / h) by ring]

/-- The signed mass difference and the full regular completion variation control both signs of the actual pole-removed response. -/
theorem abs_poleRemoved_le_of_local_gap {σ t h d : ℝ}
    (hσ : 1 ≤ σ) (hσ3 : σ ≤ 3) (hh : 0 < h) (hh1 : h ≤ 1)
    (hd : 0 < d)
    (hgap : ∀ ρ : NontrivialZetaZero, |t - ρ.1.im| ≤ 4 → d ≤ 1 - ρ.1.re) :
    |(logDeriv riemannZeta₁ ((σ : ℂ) + I * t)).re| ≤
      2 / h + 4 + (h / d) * (2 / h + 5 + zetaEulerLogHeight t) +
        4 * h * (9 + zetaEulerLogHeight t) + h := by
  have he := zeta_poleRemoved_global_real_budget
    (s := (σ : ℂ) + I * t) (by simpa using hσ)
  have heh := zeta_poleRemoved_global_real_budget
    (s := ((σ + h : ℝ) : ℂ) + I * t) (by simpa using (show 1 ≤ σ + h by linarith))
  simp only [Complex.neg_re] at he heh
  have hdif := abs_mass_difference_le hσ hσ3 hh.le hh1 hd hgap
  have hmass := shifted_mass_le (t := t) hσ hσ3 hh hh1
  have href := shifted_mass_le (σ := 1) (t := t) (h := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num only [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num,
    show (2 : ℝ) / (1 / 2) + 5 = 9 by norm_num] at href
  have hc := (Complex.abs_re_le_norm
    (zetaGlobalRegularCorrection (((σ + h : ℝ) : ℂ) + I * t) -
      zetaGlobalRegularCorrection ((σ : ℂ) + I * t))).trans
    (norm_zetaGlobalRegularCorrection_sub_le
      (s := (σ : ℂ) + I * t) (w := ((σ + h : ℝ) : ℂ) + I * t)
      (by simpa using (show 0 < σ by linarith))
      (by simpa using (show 0 < σ + h by linarith)))
  have hz : (((σ + h : ℝ) : ℂ) + I * t) - ((σ : ℂ) + I * t) = (h : ℂ) := by
    push_cast
    ring
  rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, Complex.sub_re] at hc
  have hb := shifted_poleRemoved_le (t := t) hσ hσ3 hh hh1
  have hdm := mul_le_mul_of_nonneg_left hmass (div_nonneg hh.le hd.le)
  have hrm := mul_le_mul_of_nonneg_left href (by positivity : 0 ≤ 4 * h)
  have hde := abs_le.mp hdif
  have hce := abs_le.mp hc
  have hbe := abs_le.mp hb
  rw [abs_le]
  constructor <;> linarith

/-- A shift and a local gap scaled by logarithmic height give a tunable leading coefficient and a fixed additive remainder. -/
theorem poleRemoved_le_tuned_gap {σ t c B : ℝ}
    (hσ : 1 ≤ σ) (hσ3 : σ ≤ 3) (hc : 0 < c) (hB : 0 < B)
    (hcL : c ≤ zetaEulerLogHeight t)
    (hgap : ∀ ρ : NontrivialZetaZero, |t - ρ.1.im| ≤ 4 →
      B / zetaEulerLogHeight t ≤ 1 - ρ.1.re) :
    |(logDeriv riemannZeta₁ ((σ : ℂ) + I * t)).re| ≤
      (2 / c + (2 + c) / B) * zetaEulerLogHeight t + 41 + 4 * c + 5 * c / B := by
  let L := zetaEulerLogHeight t
  have hL : 0 < L := by dsimp [L]; linarith [three_lt_zetaEulerLogHeight t]
  have hh : c / L ≤ 1 := (div_le_one hL).mpr hcL
  have he := abs_poleRemoved_le_of_local_gap hσ hσ3 (div_pos hc hL) hh (div_pos hB hL) hgap
  have halg : 2 / (c / L) + 4 + (c / L / (B / L)) * (2 / (c / L) + 5 + L) +
      4 * (c / L) * (9 + L) + c / L =
      (2 / c + (2 + c) / B) * L + 4 + 4 * c + 5 * c / B + 37 * (c / L) := by
    field_simp
    ring
  change |(logDeriv riemannZeta₁ ((σ : ℂ) + I * t)).re| ≤
    (2 / c + (2 + c) / B) * L + 41 + 4 * c + 5 * c / B
  change |(logDeriv riemannZeta₁ ((σ : ℂ) + I * t)).re| ≤
    2 / (c / L) + 4 + (c / L / (B / L)) * (2 / (c / L) + 5 + L) +
      4 * (c / L) * (9 + L) + c / L at he
  rw [halg] at he
  linarith

/-- Every positive logarithmic coefficient eventually bounds the absolute real pole-removed Euler response, uniformly throughout the closed strip from one to three. The actual zero-free hypotheses are discharged. -/
theorem exists_eventual_small_log_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 3 → T ≤ |t| →
      |(logDeriv riemannZeta₁ ((σ : ℂ) + I * t)).re| ≤ ε * zetaEulerLogHeight t := by
  let c := 8 / ε
  let B := 4 * (2 + c) / ε
  let R := 41 + 4 * c + 5 * c / B
  have hc : 0 < c := by dsimp [c]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨T₀, hT₀, hgap⟩ := exists_eventual_local_gap hB
  refine ⟨max T₀ (Real.exp (max c (2 * R / ε))), hT₀.trans (le_max_left _ _), ?_⟩
  intro σ t hσ hσ3 ht
  have ht2 : 2 ≤ |t| := hT₀.trans ((le_max_left _ _).trans ht)
  have hlog := Real.log_le_log (Real.exp_pos (max c (2 * R / ε)))
    ((le_max_right _ _).trans ht)
  rw [Real.log_exp] at hlog
  have hl : Real.log |t| ≤ zetaEulerLogHeight t :=
    Real.log_le_log (by linarith) (by linarith)
  have hcL : c ≤ zetaEulerLogHeight t := (le_max_left _ _).trans (hlog.trans hl)
  have hRL : 2 * R / ε ≤ zetaEulerLogHeight t := (le_max_right _ _).trans (hlog.trans hl)
  have hR := (div_le_iff₀ hε).mp hRL
  have he := poleRemoved_le_tuned_gap hσ hσ3 hc hB hcL
    (hgap t ((le_max_left _ _).trans ht))
  have hcoeff : 2 / c + (2 + c) / B = ε / 2 := by
    dsimp [B, c]
    field_simp
    ring
  rw [hcoeff] at he
  dsimp only [R] at hR
  linarith

/-- Every positive logarithmic coefficient bounds the real response at all heights after adding one fixed finite constant, uniform over the closed Euler three-strip. -/
theorem exists_affine_small_log_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 3 →
      |(logDeriv riemannZeta₁ ((σ : ℂ) + I * t)).re| ≤ ε * zetaEulerLogHeight t + K := by
  obtain ⟨T, hT, ht⟩ := exists_eventual_small_log_bound hε
  obtain ⟨C, hC, hc⟩ := exists_re_logDeriv_riemannZeta₁_euler_bound
  have hLT : 0 < zetaEulerLogHeight T := by linarith [three_lt_zetaEulerLogHeight T]
  refine ⟨C * zetaEulerLogHeight T, mul_pos hC hLT, ?_⟩
  intro σ t hσ hσ3
  have hL : 0 < zetaEulerLogHeight t := by linarith [three_lt_zetaEulerLogHeight t]
  by_cases htt : T ≤ |t|
  · have hh := ht σ t hσ hσ3 htt
    linarith [mul_pos hC hLT]
  · have hh := hc σ hσ hσ3 t
    have hl : zetaEulerLogHeight t ≤ zetaEulerLogHeight T := by
      unfold zetaEulerLogHeight
      rw [abs_of_pos (by linarith : 0 < T)]
      exact Real.log_le_log (by positivity) (by linarith)
    have hm := mul_le_mul_of_nonneg_left hl hC.le
    linarith [mul_pos hε hL]

end
end RiemannGaussian.ZetaEulerPoissonDifference
