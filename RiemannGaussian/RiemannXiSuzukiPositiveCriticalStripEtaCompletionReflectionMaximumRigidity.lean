import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaCompletionReflectionBoundaryRigidity
import Mathlib.Analysis.Complex.AbsMax

/-!
# Height-free maximum-modulus rigidity of the eta reflection multiplier

The explicit eta reflection multiplier has poles on the outer boundary at
the dyadic resonances, so its norm cannot be fed directly to a closed-strip
maximum principle.  This module constructs a holomorphic reciprocal extension

`F(s) = (2*pi/s) * (Gammaℝ(3-s)/Gammaℝ(s)) *
  (pairedEtaFactor(s)/pairedEtaFactor(1-s))`.

Inside the critical strip, `F(s) = B(s)⁻¹`.  On `Re s = 1`, the zeros of the
eta factor fill in every apparent reciprocal singularity: `F` vanishes at the
resonances and has norm strictly below one everywhere else.  The preceding
high-ordinate theorem controls the horizontal sides of the remaining compact
rectangle.  The maximum-modulus principle then gives `‖F‖ ≤ 1` there, and its
strong form makes the inequality strict in the interior because `F(1) = 0`.

Consequently, at every height in the open critical strip, `‖B(s)‖` is below
one left of the critical line, equal to one exactly on it, and above one to
its right.  This removes the former low-ordinate rigidity gap.  It does not
force `B` to have unit norm at a zeta zero; that independent arithmetic or
phase statement remains the conjecture-strength obstruction.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Holomorphic continuation of the reciprocal eta reflection multiplier
across the outer boundary of the critical strip. -/
def pairedEtaLaplaceReflectionReciprocalExtension (s : ℂ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) / s *
    (Complex.Gammaℝ (3 - s) / Complex.Gammaℝ s) *
    (pairedEtaFactor s / pairedEtaFactor (1 - s))

/-- The reciprocal extension agrees with `B(s)⁻¹` whenever all factors in the
explicit multiplier formula are nonzero. -/
theorem pairedEtaLaplaceReflectionReciprocalExtension_eq_inv_of_ne
    {s : ℂ} (hs0 : s ≠ 0) (h1s : 1 - s ≠ 0)
    (hetaS : pairedEtaFactor s ≠ 0)
    (hetaPartner : pairedEtaFactor (1 - s) ≠ 0)
    (hgammaS : Complex.Gammaℝ s ≠ 0)
    (hgammaPartner : Complex.Gammaℝ (1 - s) ≠ 0) :
    pairedEtaLaplaceReflectionReciprocalExtension s =
      (pairedEtaLaplaceReflectionMultiplier s)⁻¹ := by
  have hgammaShift := Complex.Gammaℝ_add_two h1s
  rw [show (1 - s) + 2 = 3 - s by ring] at hgammaShift
  have hrec : (((2 * Real.pi : ℝ) : ℂ)) * Complex.Gammaℝ (3 - s) =
      Complex.Gammaℝ (1 - s) * (1 - s) := by
    rw [hgammaShift]
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [pairedEtaLaplaceReflectionMultiplier_eq_explicit_of_ne
    hs0 h1s hetaS hetaPartner hgammaPartner]
  unfold pairedEtaLaplaceReflectionReciprocalExtension
  field_simp [hs0, h1s, hgammaS, hgammaPartner, hetaS, hetaPartner]
  rw [hrec]
  ring

/-- Throughout the open critical strip, the extension is exactly the
reciprocal of the eta reflection multiplier. -/
theorem pairedEtaLaplaceReflectionReciprocalExtension_eq_inv
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    pairedEtaLaplaceReflectionReciprocalExtension s =
      (pairedEtaLaplaceReflectionMultiplier s)⁻¹ := by
  apply pairedEtaLaplaceReflectionReciprocalExtension_eq_inv_of_ne
  · intro hs
    subst s
    norm_num at hspos
  · intro h
    have hs1 : s = 1 := by linear_combination -h
    subst s
    norm_num at hslt
  · exact pairedEtaFactor_ne_zero_of_re_lt_one hslt
  · exact pairedEtaFactor_ne_zero_of_re_lt_one (by
      simpa using sub_lt_self (1 : ℝ) hspos)
  · exact Gammaℝ_ne_zero_of_re_pos hspos
  · exact Gammaℝ_ne_zero_of_re_pos (by simpa using sub_pos.mpr hslt)

/-- The reciprocal extension is complex differentiable on `0 < Re s < 3`. -/
theorem differentiableAt_pairedEtaLaplaceReflectionReciprocalExtension
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 3) :
    DifferentiableAt ℂ pairedEtaLaplaceReflectionReciprocalExtension s := by
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hspos
  have hgammaS : Complex.Gammaℝ s ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos hspos
  have hetaPartner : pairedEtaFactor (1 - s) ≠ 0 :=
    pairedEtaFactor_ne_zero_of_re_lt_one (by
      simpa using sub_lt_self (1 : ℝ) hspos)
  have hgammaSdiff : DifferentiableAt ℂ Complex.Gammaℝ s :=
    differentiableAt_Gammaℝ_of_re_pos hspos
  have hgammaPartnerDiff : DifferentiableAt ℂ Complex.Gammaℝ (3 - s) :=
    differentiableAt_Gammaℝ_of_re_pos (by simpa using sub_pos.mpr hslt)
  have hsubThree : DifferentiableAt ℂ (fun z : ℂ => 3 - z) s := by fun_prop
  have hsubOne : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s := by fun_prop
  unfold pairedEtaLaplaceReflectionReciprocalExtension
  exact
    (((differentiableAt_const (c := (((2 * Real.pi : ℝ) : ℂ)))).div
        differentiableAt_id hs0).mul
      ((hgammaPartnerDiff.comp s hsubThree).div hgammaSdiff hgammaS)).mul
      ((hasDerivAt_pairedEtaFactor s).differentiableAt.div
        ((hasDerivAt_pairedEtaFactor (1 - s)).differentiableAt.comp s hsubOne)
        hetaPartner)

/-- The reciprocal extension is analytic on `0 < Re s < 3`. -/
theorem analyticAt_pairedEtaLaplaceReflectionReciprocalExtension
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 3) :
    AnalyticAt ℂ pairedEtaLaplaceReflectionReciprocalExtension s := by
  let S : Set ℂ := {z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 3}
  have hSopen : IsOpen S :=
    (Complex.isOpen_re_gt 0).inter (Complex.isOpen_re_lt 3)
  have hSdiff : DifferentiableOn ℂ pairedEtaLaplaceReflectionReciprocalExtension S := by
    intro z hz
    exact (differentiableAt_pairedEtaLaplaceReflectionReciprocalExtension hz.1 hz.2).differentiableWithinAt
  exact hSdiff.analyticAt (hSopen.mem_nhds ⟨hspos, hslt⟩)

private theorem pairedEtaLaplaceReflectionReciprocalExtension_one_add_mul_I_eq_inv
    {t : ℝ} (ht : t ≠ 0)
    (heta : Real.cos (t * Real.log 2) ≠ 1) :
    pairedEtaLaplaceReflectionReciprocalExtension (1 + (t : ℂ) * Complex.I) =
      (pairedEtaLaplaceReflectionMultiplier
        (1 + (t : ℂ) * Complex.I))⁻¹ := by
  apply pairedEtaLaplaceReflectionReciprocalExtension_eq_inv_of_ne
  · intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [Complex.mul_re] at hre
  · simpa using
      (mul_ne_zero (neg_ne_zero.mpr (ofReal_ne_zero.mpr ht))
        Complex.I_ne_zero)
  · exact (pairedEtaFactor_one_add_mul_I_ne_zero_iff t).2 heta
  · simpa using pairedEtaFactor_neg_mul_I_ne_zero t
  · apply Gammaℝ_ne_zero_of_re_pos
    norm_num [Complex.mul_re]
  · simpa using Gammaℝ_neg_mul_I_ne_zero ht

/-- On `Re s = 1`, every dyadic resonance becomes a zero of the reciprocal
extension, including the central boundary point `s = 1`. -/
theorem pairedEtaLaplaceReflectionReciprocalExtension_one_add_mul_I_eq_zero_of_resonance
    {t : ℝ} (heta : Real.cos (t * Real.log 2) = 1) :
    pairedEtaLaplaceReflectionReciprocalExtension (1 + (t : ℂ) * Complex.I) = 0 := by
  have hfactor : pairedEtaFactor (1 + (t : ℂ) * Complex.I) = 0 := by
    by_contra hne
    exact (pairedEtaFactor_one_add_mul_I_ne_zero_iff t).1 hne heta
  unfold pairedEtaLaplaceReflectionReciprocalExtension
  rw [hfactor]
  simp

/-- The squared norm of the reciprocal extension is strictly below one at
every point of the outer boundary `Re s = 1`. -/
theorem normSq_pairedEtaLaplaceReflectionReciprocalExtension_one_add_mul_I_lt_one (t : ℝ) :
    Complex.normSq
        (pairedEtaLaplaceReflectionReciprocalExtension (1 + (t : ℂ) * Complex.I)) < 1 := by
  by_cases heta : Real.cos (t * Real.log 2) = 1
  · rw [pairedEtaLaplaceReflectionReciprocalExtension_one_add_mul_I_eq_zero_of_resonance heta, Complex.normSq_zero]
    norm_num
  · have ht : t ≠ 0 := by
      intro ht
      subst t
      simp at heta
    rw [pairedEtaLaplaceReflectionReciprocalExtension_one_add_mul_I_eq_inv ht heta, Complex.normSq_inv]
    exact inv_lt_one_of_one_lt₀
      (normSq_pairedEtaLaplaceReflectionMultiplier_one_add_mul_I_gt_one
        ht heta)

/-- Norm form of strict reciprocal-extension contraction on `Re s = 1`. -/
theorem norm_pairedEtaLaplaceReflectionReciprocalExtension_one_add_mul_I_lt_one (t : ℝ) :
    ‖pairedEtaLaplaceReflectionReciprocalExtension (1 + (t : ℂ) * Complex.I)‖ < 1 := by
  have h := normSq_pairedEtaLaplaceReflectionReciprocalExtension_one_add_mul_I_lt_one t
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg
    (pairedEtaLaplaceReflectionReciprocalExtension (1 + (t : ℂ) * Complex.I))]

private theorem norm_pairedEtaLaplaceReflectionReciprocalExtension_half_add_mul_I (y : ℝ) :
    ‖pairedEtaLaplaceReflectionReciprocalExtension
      (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ = 1 := by
  let s : ℂ := (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
  have hspos : 0 < s.re := by norm_num [s, Complex.mul_re]
  have hslt : s.re < 1 := by norm_num [s, Complex.mul_re]
  have hext := pairedEtaLaplaceReflectionReciprocalExtension_eq_inv hspos hslt
  have hsq := normSq_pairedEtaLaplaceReflectionMultiplier_eq_one_of_re_eq_half
    (s := s) (by norm_num [s, Complex.mul_re])
  have hnorm : ‖pairedEtaLaplaceReflectionMultiplier s‖ = 1 := by
    rw [Complex.normSq_eq_norm_sq] at hsq
    nlinarith [norm_nonneg (pairedEtaLaplaceReflectionMultiplier s)]
  change ‖pairedEtaLaplaceReflectionReciprocalExtension s‖ = 1
  rw [hext, norm_inv, hnorm, inv_one]

private theorem norm_pairedEtaLaplaceReflectionReciprocalExtension_le_one_of_eight_le_abs
    {sigma y : ℝ} (hhalf : 1 / 2 ≤ sigma) (hsone : sigma ≤ 1)
    (hy : 8 ≤ |y|) :
    ‖pairedEtaLaplaceReflectionReciprocalExtension
      ((sigma : ℂ) + (y : ℂ) * Complex.I)‖ ≤ 1 := by
  rcases hsone.eq_or_lt with hsigma | hslt
  · subst sigma
    exact (norm_pairedEtaLaplaceReflectionReciprocalExtension_one_add_mul_I_lt_one y).le
  rcases hhalf.eq_or_lt with hsigma | hhalfStrict
  · subst sigma
    exact le_of_eq (norm_pairedEtaLaplaceReflectionReciprocalExtension_half_add_mul_I y)
  · have hspos : 0 < sigma := by linarith
    have hext := pairedEtaLaplaceReflectionReciprocalExtension_eq_inv
      (s := (sigma : ℂ) + (y : ℂ) * Complex.I)
      (by simpa [Complex.mul_re] using hspos)
      (by simpa [Complex.mul_re] using hslt)
    have hlog :=
      pairedEtaLaplaceReflectionLogNorm_pos_of_half_lt_of_eight_le_abs
        hhalfStrict hslt hy
    have hnorm : 1 < ‖pairedEtaLaplaceReflectionMultiplier
        ((sigma : ℂ) + (y : ℂ) * Complex.I)‖ := by
      exact (Real.log_pos_iff (norm_nonneg _)).mp hlog
    rw [hext, norm_inv]
    exact (inv_lt_one_of_one_lt₀ hnorm).le

private def etaReflectionLowRectangle : Set ℂ :=
  Set.Ioo (1 / 2 : ℝ) 1 ×ℂ Set.Ioo (-8 : ℝ) 8

private theorem diffContOnCl_pairedEtaLaplaceReflectionReciprocalExtension_lowRectangle :
    DiffContOnCl ℂ pairedEtaLaplaceReflectionReciprocalExtension etaReflectionLowRectangle := by
  apply DifferentiableOn.diffContOnCl
  intro z hz
  rw [etaReflectionLowRectangle, closure_reProdIm,
    closure_Ioo (by norm_num : (1 / 2 : ℝ) ≠ 1),
    closure_Ioo (by norm_num : (-8 : ℝ) ≠ 8)] at hz
  exact (differentiableAt_pairedEtaLaplaceReflectionReciprocalExtension (by linarith [hz.1.1])
    (by linarith [hz.1.2])).differentiableWithinAt

private theorem norm_pairedEtaLaplaceReflectionReciprocalExtension_le_one_on_lowRectangle_frontier
    {z : ℂ} (hz : z ∈ frontier etaReflectionLowRectangle) :
    ‖pairedEtaLaplaceReflectionReciprocalExtension z‖ ≤ 1 := by
  rw [etaReflectionLowRectangle, frontier_reProdIm,
    closure_Ioo (by norm_num : (1 / 2 : ℝ) ≠ 1),
    frontier_Ioo (by norm_num : (-8 : ℝ) < 8),
    closure_Ioo (by norm_num : (-8 : ℝ) ≠ 8),
    frontier_Ioo (by norm_num : (1 / 2 : ℝ) < 1)] at hz
  rcases hz with hzHorizontal | hzVertical
  · have hy : 8 ≤ |z.im| := by
      rcases hzHorizontal.2 with him | him
      · rw [him]
        norm_num
      · rw [him]
        norm_num
    have h := norm_pairedEtaLaplaceReflectionReciprocalExtension_le_one_of_eight_le_abs hzHorizontal.1.1 hzHorizontal.1.2 hy
    rw [Complex.re_add_im] at h
    exact h
  · rcases hzVertical.1 with hre | hre
    · have h := norm_pairedEtaLaplaceReflectionReciprocalExtension_half_add_mul_I z.im
      have hcoord :
          (((1 / 2 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I) = z := by
        apply Complex.ext
        · simpa [Complex.mul_re] using hre.symm
        · simp [Complex.mul_im]
      rw [hcoord] at h
      exact h.le
    · have h := norm_pairedEtaLaplaceReflectionReciprocalExtension_one_add_mul_I_lt_one z.im
      have hre' : z.re = 1 := by
        simpa only [Set.mem_singleton_iff] using hre
      have hcoord : (1 : ℂ) + (z.im : ℂ) * Complex.I = z := by
        apply Complex.ext
        · simpa [Complex.mul_re] using hre'.symm
        · simp [Complex.mul_im]
      rw [hcoord] at h
      exact h.le

private theorem norm_pairedEtaLaplaceReflectionReciprocalExtension_le_one_of_lowRectangleClosure
    {z : ℂ} (hhalf : 1 / 2 ≤ z.re) (hsone : z.re ≤ 1)
    (hy : |z.im| ≤ 8) :
    ‖pairedEtaLaplaceReflectionReciprocalExtension z‖ ≤ 1 := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    ((isBounded_Ioo (1 / 2 : ℝ) 1).reProdIm
      (isBounded_Ioo (-8 : ℝ) 8))
    diffContOnCl_pairedEtaLaplaceReflectionReciprocalExtension_lowRectangle (fun z hz => norm_pairedEtaLaplaceReflectionReciprocalExtension_le_one_on_lowRectangle_frontier hz)
  show z ∈ closure etaReflectionLowRectangle
  unfold etaReflectionLowRectangle
  rw [closure_reProdIm,
    closure_Ioo (by norm_num : (1 / 2 : ℝ) ≠ 1),
    closure_Ioo (by norm_num : (-8 : ℝ) ≠ 8)]
  exact ⟨⟨hhalf, hsone⟩, abs_le.mp hy⟩

private theorem norm_pairedEtaLaplaceReflectionReciprocalExtension_lt_one_of_lowRectangle
    {z : ℂ} (hhalf : 1 / 2 < z.re) (hsone : z.re < 1)
    (hy : |z.im| < 8) :
    ‖pairedEtaLaplaceReflectionReciprocalExtension z‖ < 1 := by
  have hle : ‖pairedEtaLaplaceReflectionReciprocalExtension z‖ ≤ 1 :=
    norm_pairedEtaLaplaceReflectionReciprocalExtension_le_one_of_lowRectangleClosure hhalf.le hsone.le hy.le
  by_contra hnot
  have heq : ‖pairedEtaLaplaceReflectionReciprocalExtension z‖ = 1 :=
    le_antisymm hle (le_of_not_gt hnot)
  have hzU : z ∈ etaReflectionLowRectangle := by
    exact ⟨⟨hhalf, hsone⟩, abs_lt.mp hy⟩
  have hmax : IsMaxOn (norm ∘ pairedEtaLaplaceReflectionReciprocalExtension)
      etaReflectionLowRectangle z := by
    intro w hw
    change ‖pairedEtaLaplaceReflectionReciprocalExtension w‖ ≤ ‖pairedEtaLaplaceReflectionReciprocalExtension z‖
    rw [heq]
    exact norm_pairedEtaLaplaceReflectionReciprocalExtension_le_one_of_lowRectangleClosure hw.1.1.le hw.1.2.le
      (abs_lt.mpr hw.2).le
  have hopen : IsOpen etaReflectionLowRectangle := by
    unfold etaReflectionLowRectangle
    exact isOpen_Ioo.reProdIm isOpen_Ioo
  have hpre : IsPreconnected etaReflectionLowRectangle := by
    apply Convex.isPreconnected
    unfold etaReflectionLowRectangle Complex.reProdIm
    exact ((convex_Ioo (1 / 2 : ℝ) 1).linear_preimage
      Complex.reCLM.toLinearMap).inter
        ((convex_Ioo (-8 : ℝ) 8).linear_preimage
          Complex.imCLM.toLinearMap)
  have hconst := Complex.eqOn_closure_of_isPreconnected_of_isMaxOn_norm
    hpre hopen diffContOnCl_pairedEtaLaplaceReflectionReciprocalExtension_lowRectangle hzU hmax
  have hone : (1 : ℂ) ∈ closure etaReflectionLowRectangle := by
    unfold etaReflectionLowRectangle
    rw [closure_reProdIm,
      closure_Ioo (by norm_num : (1 / 2 : ℝ) ≠ 1),
      closure_Ioo (by norm_num : (-8 : ℝ) ≠ 8)]
    exact ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  have hvalue := hconst hone
  simp only [Function.const_apply] at hvalue
  have hzero : pairedEtaLaplaceReflectionReciprocalExtension (1 : ℂ) = 0 := by
    simpa using pairedEtaLaplaceReflectionReciprocalExtension_one_add_mul_I_eq_zero_of_resonance (t := 0) (by simp)
  rw [hzero] at hvalue
  have hzZero : pairedEtaLaplaceReflectionReciprocalExtension z = 0 := hvalue.symm
  rw [hzZero, norm_zero] at heq
  norm_num at heq

/-- The reciprocal extension has norm strictly below one everywhere between
the critical line and the outer boundary. -/
theorem norm_pairedEtaLaplaceReflectionReciprocalExtension_lt_one_of_half_lt_re
    {s : ℂ} (hhalf : 1 / 2 < s.re) (hsone : s.re < 1) :
    ‖pairedEtaLaplaceReflectionReciprocalExtension s‖ < 1 := by
  by_cases hy : |s.im| < 8
  · exact norm_pairedEtaLaplaceReflectionReciprocalExtension_lt_one_of_lowRectangle hhalf hsone hy
  · have hy8 : 8 ≤ |s.im| := le_of_not_gt hy
    have hspos : 0 < s.re := by linarith
    have hext := pairedEtaLaplaceReflectionReciprocalExtension_eq_inv hspos hsone
    have hlog :=
      pairedEtaLaplaceReflectionLogNorm_pos_of_half_lt_of_eight_le_abs
        hhalf hsone hy8
    have hnorm : 1 < ‖pairedEtaLaplaceReflectionMultiplier s‖ := by
      unfold pairedEtaLaplaceReflectionLogNorm at hlog
      rw [Complex.re_add_im] at hlog
      exact (Real.log_pos_iff (norm_nonneg _)).mp hlog
    rw [hext, norm_inv]
    exact inv_lt_one_of_one_lt₀ hnorm

/-- The eta reflection multiplier has norm strictly above one everywhere to
the right of the critical line in the open strip. -/
theorem norm_pairedEtaLaplaceReflectionMultiplier_gt_one_of_half_lt_re
    {s : ℂ} (hhalf : 1 / 2 < s.re) (hsone : s.re < 1) :
    1 < ‖pairedEtaLaplaceReflectionMultiplier s‖ := by
  have hspos : 0 < s.re := by linarith
  have hext := pairedEtaLaplaceReflectionReciprocalExtension_eq_inv hspos hsone
  have hlt := norm_pairedEtaLaplaceReflectionReciprocalExtension_lt_one_of_half_lt_re hhalf hsone
  rw [hext, norm_inv] at hlt
  exact (inv_lt_one₀
    (norm_pos_iff.mpr
      (pairedEtaLaplaceReflectionMultiplier_ne_zero hspos hsone))).mp hlt

/-- The eta reflection multiplier has norm strictly below one everywhere to
the left of the critical line in the open strip. -/
theorem norm_pairedEtaLaplaceReflectionMultiplier_lt_one_of_re_lt_half
    {s : ℂ} (hspos : 0 < s.re) (hhalf : s.re < 1 / 2) :
    ‖pairedEtaLaplaceReflectionMultiplier s‖ < 1 := by
  have hsone : s.re < 1 := by linarith
  have hpartnerHalf : 1 / 2 < 1 - s.re := by linarith
  have hpartnerOne : 1 - s.re < 1 := by linarith
  let y := s.im
  have hpartner := norm_pairedEtaLaplaceReflectionMultiplier_gt_one_of_half_lt_re
    (s := (((1 - s.re : ℝ) : ℂ) + (y : ℂ) * Complex.I))
    (by simpa [Complex.mul_re] using hpartnerHalf)
    (by simpa [Complex.mul_re] using hpartnerOne)
  have hpartnerLog :
      0 < pairedEtaLaplaceReflectionLogNorm (1 - s.re) y := by
    exact Real.log_pos hpartner
  have hsym := pairedEtaLaplaceReflectionLogNorm_one_sub
    (sigma := s.re) (y := y) hspos hsone
  have hselfLog : pairedEtaLaplaceReflectionLogNorm s.re y < 0 := by
    linarith
  unfold pairedEtaLaplaceReflectionLogNorm at hselfLog
  rw [Complex.re_add_im] at hselfLog
  exact (Real.log_neg_iff
    (norm_pos_iff.mpr
      (pairedEtaLaplaceReflectionMultiplier_ne_zero hspos hsone))).mp hselfLog

/-- Height-free horizontal rigidity: in the complete open critical strip,
the reflection multiplier has unit squared norm exactly on `Re s = 1/2`. -/
theorem normSq_pairedEtaLaplaceReflectionMultiplier_eq_one_iff_re_eq_half
    {s : ℂ} (hspos : 0 < s.re) (hsone : s.re < 1) :
    Complex.normSq (pairedEtaLaplaceReflectionMultiplier s) = 1 ↔
      s.re = 1 / 2 := by
  rw [Complex.normSq_eq_norm_sq]
  constructor
  · intro hsq
    rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
    · have hnorm := norm_pairedEtaLaplaceReflectionMultiplier_lt_one_of_re_lt_half hspos hlt
      nlinarith [norm_nonneg (pairedEtaLaplaceReflectionMultiplier s)]
    · exact heq
    · have hnorm := norm_pairedEtaLaplaceReflectionMultiplier_gt_one_of_half_lt_re hgt hsone
      nlinarith [norm_nonneg (pairedEtaLaplaceReflectionMultiplier s)]
  · intro hre
    have hsq := normSq_pairedEtaLaplaceReflectionMultiplier_eq_one_of_re_eq_half hre
    simpa [Complex.normSq_eq_norm_sq] using hsq

/-- At every nontrivial zeta zero, vanishing of the first actual localized
completion-distortion coefficient is equivalent to the critical-line
equation.  This theorem does not assert that the coefficient vanishes. -/
theorem pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_sub_conjugatePartner_eq_zero_iff_re_eq_half (rho : NontrivialZetaZero) :
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho -
          pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
            (NontrivialZetaZero.conjugatePartner rho) = 0 ↔
      rho.1.re = 1 / 2 := by
  rw [
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_sub_conjugatePartner_eq_zero_iff_reflectionMultiplier_normSq_eq_one]
  exact normSq_pairedEtaLaplaceReflectionMultiplier_eq_one_iff_re_eq_half
    (NontrivialZetaZero.zero_lt_re rho)
    (NontrivialZetaZero.re_lt_one rho)

end
end RiemannGaussian
