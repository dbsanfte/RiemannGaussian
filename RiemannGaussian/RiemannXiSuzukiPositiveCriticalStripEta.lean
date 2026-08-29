import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaUpper

/-!
# Paired eta throughout the positive critical half-strip

The paired Dirichlet eta series was already constructed and proved analytic
on `0 < re s`, while its zeta factorization was continued only through the
upper-right quadrant. This module removes that quadrant restriction.

Conjugation gives the lower-half-plane identity term by term. On the real
axis, both sides are continuous away from `s = 1`; an explicit closure
argument approaches the axis from the upper-right quadrant. Consequently the
factorization holds on the entire positive half-plane except at `s = 1`.

In particular, throughout `1 / 2 < re s < 1`, an absolutely convergent paired
arithmetic series represents the eta factor times zeta. The elementary eta
factor cannot vanish there, so this convergent series retains exactly the
zeta divisor. This is an arithmetic representative, not a zero-free result.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Each paired eta summand respects complex conjugation. -/
lemma pairedEtaCoreSummand_conj (s : ℂ) (n : ℕ) :
    pairedEtaCoreSummand ((starRingEnd ℂ) s) n =
      (starRingEnd ℂ) (pairedEtaCoreSummand s n) := by
  unfold pairedEtaCoreSummand
  rw [map_sub]
  congr 1
  · simpa only [map_neg, Complex.conj_ofReal] using
      (Complex.cpow_conj
        ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) (-s)
        (by
          rw [Complex.arg_ofReal_of_nonneg (by positivity)]
          exact Real.pi_ne_zero.symm))
  · simpa only [map_neg, Complex.conj_ofReal] using
      (Complex.cpow_conj
        ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) (-s)
        (by
          rw [Complex.arg_ofReal_of_nonneg (by positivity)]
          exact Real.pi_ne_zero.symm))

/-- The paired eta function respects complex conjugation. -/
lemma pairedEtaCore_conj (s : ℂ) :
    pairedEtaCore ((starRingEnd ℂ) s) = (starRingEnd ℂ) (pairedEtaCore s) := by
  unfold pairedEtaCore
  calc
    ∑' n : ℕ, pairedEtaCoreSummand ((starRingEnd ℂ) s) n =
        ∑' n : ℕ, (starRingEnd ℂ) (pairedEtaCoreSummand s n) := by
      apply tsum_congr
      exact pairedEtaCoreSummand_conj s
    _ = (starRingEnd ℂ) (∑' n : ℕ, pairedEtaCoreSummand s n) :=
      (Complex.conj_tsum _).symm

/-- Conjugating the exponent in the elementary eta power conjugates its
value. -/
lemma two_cpow_neg_conj (s : ℂ) :
    (2 : ℂ) ^ (-((starRingEnd ℂ) s)) =
      (starRingEnd ℂ) ((2 : ℂ) ^ (-s)) := by
  simpa only [map_neg, map_ofNat] using
    (Complex.cpow_conj (2 : ℂ) (-s)
      (by
        change (((2 : ℕ) : ℂ)).arg ≠ Real.pi
        rw [Complex.natCast_arg]
        exact Real.pi_ne_zero.symm))

/-- The paired eta factorization in the lower-right quadrant, obtained by
conjugating the checked upper-right identity. -/
lemma pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_neg
    {s : ℂ} (hsre : 0 < s.re) (hsim : s.im < 0) :
    pairedEtaCore s =
      (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  have h := pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_pos
    (s := (starRingEnd ℂ) s) (by simpa using hsre) (by simpa using hsim)
  have hc := congrArg (starRingEnd ℂ) h
  simpa [pairedEtaCore_conj, two_cpow_neg_conj,
    starRingEnd_self_apply, map_ofNat] using hc

/-- The paired eta factorization on the positive real axis away from `s = 1`.
The proof approaches each axis point through the upper-right quadrant. -/
lemma pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_eq_zero
    {s : ℂ} (hsre : 0 < s.re) (hsim : s.im = 0) (hsone : s ≠ 1) :
    pairedEtaCore s =
      (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  let rhs : ℂ → ℂ := fun w =>
    (1 - 2 * (2 : ℂ) ^ (-w)) * riemannZeta w
  let t : Set ℂ := pairedEtaUpperRightDomain ∪ {s}
  have heq : Set.EqOn pairedEtaCore rhs pairedEtaUpperRightDomain := by
    intro w hw
    exact pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_pos hw.1 hw.2
  have htpos : t ⊆ {w : ℂ | 0 < w.re} := by
    intro w hw
    rcases hw with hw | hw
    · exact hw.1
    · simpa only [mem_singleton_iff] using hw ▸ hsre
  have hlhs : ContinuousOn pairedEtaCore t :=
    (analyticOnNhd_pairedEtaCore.mono htpos).continuousOn
  have hrhs : ContinuousOn rhs t := by
    intro w hw
    have hwone : w ≠ 1 := by
      rcases hw with hw | hw
      · intro h
        subst w
        simpa [pairedEtaUpperRightDomain] using hw.2
      · simpa only [mem_singleton_iff] using hw ▸ hsone
    have hfactor : DifferentiableAt ℂ
        (fun u : ℂ => 1 - 2 * (2 : ℂ) ^ (-u)) w := by
      fun_prop (disch := norm_num)
    exact
      (hfactor.mul
        (differentiableAt_riemannZeta hwone)).continuousAt.continuousWithinAt
  have hsclosure : s ∈ closure pairedEtaUpperRightDomain := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨s + ((ε / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · constructor
      · simpa [pairedEtaUpperRightDomain] using hsre
      · simp [hsim]
        positivity
    · rw [dist_eq_norm]
      simp [Real.norm_eq_abs, abs_of_pos hε]
      linarith
  have htclosure : t ⊆ closure pairedEtaUpperRightDomain := by
    intro w hw
    rcases hw with hw | hw
    · exact subset_closure hw
    · simpa only [mem_singleton_iff] using hw ▸ hsclosure
  have hall := heq.of_subset_closure hlhs hrhs subset_union_left htclosure
  exact hall (by simp [t])

/-- The paired eta factorization on the full positive half-plane away from
`s = 1`. -/
lemma pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
    {s : ℂ} (hsre : 0 < s.re) (hsone : s ≠ 1) :
    pairedEtaCore s =
      (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  rcases lt_trichotomy s.im 0 with hsim | hsim | hsim
  · exact pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_neg hsre hsim
  · exact pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_eq_zero
      hsre hsim hsone
  · exact pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_pos hsre hsim

/-- Every zero of the elementary eta factor has real part one. -/
lemma pairedEtaFactor_eq_zero_implies_re_eq_one
    {s : ℂ} (hfactor : 1 - (2 : ℂ) * (2 : ℂ) ^ (-s) = 0) :
    s.re = 1 := by
  have heq : (2 : ℂ) * (2 : ℂ) ^ (-s) = 1 :=
    (sub_eq_zero.mp hfactor).symm
  have hcpow : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
    change ‖((2 : ℝ) : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp
  have hrpow : (2 : ℝ) ^ (1 - s.re) = (2 : ℝ) ^ (0 : ℝ) := by
    calc
      (2 : ℝ) ^ (1 - s.re) =
          (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-s.re) := by
        rw [show 1 - s.re = (1 : ℝ) + (-s.re) by ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = 2 * ‖(2 : ℂ) ^ (-s)‖ := by
        rw [Real.rpow_one, hcpow]
      _ = ‖(2 : ℂ) * (2 : ℂ) ^ (-s)‖ := by
        rw [norm_mul]
        norm_num
      _ = 1 := by rw [heq]; norm_num
      _ = (2 : ℝ) ^ (0 : ℝ) := by norm_num
  have hexponent : 1 - s.re = 0 :=
    (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
      hrpow
  linarith

/-- The elementary eta factor is nonzero strictly to the left of `re s = 1`. -/
lemma pairedEtaFactor_ne_zero_of_re_lt_one
    {s : ℂ} (hs : s.re < 1) :
    1 - (2 : ℂ) * (2 : ℂ) ^ (-s) ≠ 0 := by
  intro hfactor
  linarith [pairedEtaFactor_eq_zero_implies_re_eq_one hfactor]

/-- In the positive critical half-strip, the absolutely convergent paired eta
series sums exactly to the eta factor times zeta. -/
theorem hasSum_pairedEtaCoreSummand_factor_riemannZeta_of_half_lt_re_of_re_lt_one
    {s : ℂ} (hlower : 1 / 2 < s.re) (hupper : s.re < 1) :
    HasSum (pairedEtaCoreSummand s)
      ((1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s) := by
  rw [← pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
    (by linarith) (by intro h; subst s; norm_num at hupper)]
  exact (summable_pairedEtaCoreSummand (by linarith)).hasSum

/-- The convergent paired eta representative has exactly the zeta zeros in
the positive critical half-strip. -/
theorem pairedEtaCore_eq_zero_iff_riemannZeta_eq_zero_of_half_lt_re_of_re_lt_one
    {s : ℂ} (hlower : 1 / 2 < s.re) (hupper : s.re < 1) :
    pairedEtaCore s = 0 ↔ riemannZeta s = 0 := by
  rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
    (by linarith) (by intro h; subst s; norm_num at hupper), mul_eq_zero]
  simp [pairedEtaFactor_ne_zero_of_re_lt_one hupper]

end
end RiemannGaussian
