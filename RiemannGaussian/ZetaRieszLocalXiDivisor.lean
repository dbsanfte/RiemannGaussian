/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszInfiniteModeAudit
import RiemannGaussian.ZetaHalfStripSource

/-!
# A finite genuine local xi divisor and one analytic remainder

Only the adaptive radius is reused. Every pole below is an actual zeta
zero with its analytic multiplicity; no reflected mode or infinite-mode
inverse enters. The finite singular inverse retains all boundary jets.
-/

namespace RiemannGaussian.ZetaRieszLocalXiDivisor
noncomputable section
open Complex Filter Metric Set Topology
open scoped BigOperators Classical
open ZetaRieszShiftedCenter

/-- The existing adaptive zero-free sphere, without its canonical factors. -/
def radius (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) : ℝ :=
  adaptiveZetaCanonicalRadius (zetaRightHalfDiscParameter rho hrho) rho.1.im

theorem source_pos (rho : NontrivialZetaZero) : 0 < 3/2-rho.1.re := by
  linarith [NontrivialZetaZero.re_lt_one rho]

theorem radius_bounds (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) :
    (1+(3/2-rho.1.re))/2 < radius rho hrho ∧ radius rho hrho < 1 := by
  have h := adaptiveZetaCanonicalRadius_spec (zetaRightHalfDiscParameter rho hrho) rho.1.im
  constructor
  · have hlow := h.1
    change 5/4-rho.1.re/2 < _ at hlow
    dsimp only [radius]
    linarith
  · exact h.2.1

theorem radius_pos (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) :
    0 < radius rho hrho := by
  have h := (radius_bounds rho hrho).1
  linarith [source_pos rho]

/-- A uniform normalized disk, with room beyond 4/3 for Cauchy estimates. -/
theorem normalized_radius_bounds (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re)
    (hu : 3/2-rho.1.re ≤ 10001/20000) :
    4/3 < radius rho hrho/(3/2-rho.1.re) ∧
      radius rho hrho/(3/2-rho.1.re) < 2 := by
  have h := radius_bounds rho hrho
  constructor
  · apply (lt_div_iff₀ (source_pos rho)).mpr
    linarith
  · apply (div_lt_iff₀ (source_pos rho)).mpr
    linarith [NontrivialZetaZero.re_lt_one rho]

theorem radius_sphere_nonzero (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re)
    {s : ℂ} (hs : ‖s-center rho.1.im‖ = radius rho hrho) : riemannXi s ≠ 0 := by
  intro hz
  have ht := (riemannXi_eq_zero_iff_isNontrivialZetaZero s).mp hz
  have h := (adaptiveZetaCanonicalRadius_spec
    (zetaRightHalfDiscParameter rho hrho) rho.1.im).2.2 (s-center rho.1.im) hs
  apply h
  change riemannZeta₁ (center rho.1.im+(s-center rho.1.im)) = 0
  rw [add_sub_cancel, riemannZeta₁_eq_sub_one_mul ht.2.2, ht.1, mul_zero]

/-- Exactly the genuine nontrivial zeros in the open local disk. -/
def localDivisor (y R : ℝ) : Finset NontrivialZetaZero :=
  (spectralZetaZeroWindow (|y|+R)).filter (fun tau => ‖center y-tau.1‖ < R)

theorem mem_localDivisor {y R : ℝ} (hR : 0 ≤ R) (tau : NontrivialZetaZero) :
    tau ∈ localDivisor y R ↔ ‖center y-tau.1‖ < R := by
  rw [localDivisor, Finset.mem_filter]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rw [mem_spectralZetaZeroWindow (by positivity), zetaSpectralCoordinate_re]
  have hi := Complex.abs_im_le_norm (center y-tau.1)
  have hc : (center y-tau.1).im = y-tau.1.im := by simp [ZetaRieszShiftedCenter.center]
  rw [hc] at hi
  have ha : |tau.1.im| ≤ |y|+|y-tau.1.im| := by
    simpa only [sub_sub_cancel] using abs_sub y (y-tau.1.im)
  linarith

theorem selected_mem (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) :
    rho ∈ localDivisor rho.1.im (radius rho hrho) := by
  rw [mem_localDivisor (radius_pos rho hrho).le]
  have he : center rho.1.im-rho.1 = ((3/2-rho.1.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [ZetaRieszShiftedCenter.center]
  rw [he, Complex.norm_real, Real.norm_of_nonneg (source_pos rho).le]
  linarith [(radius_bounds rho hrho).1]

/-- The literal finite sum of principal parts, with actual multiplicities. -/
def principalSum (W : Finset NontrivialZetaZero) (s : ℂ) : ℂ :=
  ∑ tau ∈ W, (analyticZetaZeroMultiplicity tau : ℂ)/(s-tau.1)

private theorem principal_analytic (tau : NontrivialZetaZero) {s : ℂ} (hs : s ≠ tau.1) :
    AnalyticAt ℂ (fun z => (analyticZetaZeroMultiplicity tau : ℂ)/(z-tau.1)) s :=
  analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs)

/-- Removable singularities give one analytic representative on the
whole disk, without separating canonical reflected terms. -/
theorem exists_localXiLogRemainder (y R : ℝ) (hR : 0 ≤ R) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball (center y) R) ∧
      ∀ s, riemannXi s ≠ 0 →
        logDeriv riemannXi s = principalSum (localDivisor y R) s+H s := by
  let W := localDivisor y R
  let S := W.image (fun tau => (tau.1 : ℂ))
  let raw := fun s => logDeriv riemannXi s-principalSum W s
  obtain ⟨H, hH, hraw⟩ := exists_analyticAtOn_of_finite_removable
    (ball (center y) R) S raw (by
      intro s hs
      obtain ⟨tau, htau, rfl⟩ := Finset.mem_image.mp hs
      simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using
        (mem_localDivisor hR tau).mp htau) (by
      intro s hs hsS
      have hxi : riemannXi s ≠ 0 := by
        intro hz
        let tau : NontrivialZetaZero :=
          ⟨s, (riemannXi_eq_zero_iff_isNontrivialZetaZero s).mp hz⟩
        apply hsS
        apply Finset.mem_image.mpr
        refine ⟨tau, (mem_localDivisor hR tau).mpr ?_, rfl⟩
        simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hs
      apply ((analyticAt_riemannXi s).deriv.div (analyticAt_riemannXi s) hxi).sub
      apply Finset.analyticAt_fun_sum
      intro tau htau
      exact principal_analytic tau (fun he => hsS (Finset.mem_image.mpr ⟨tau, htau, he.symm⟩))) (by
      intro s hs
      obtain ⟨tau, htau, rfl⟩ := Finset.mem_image.mp hs
      have hfinite : analyticOrderAt riemannXi tau.1 ≠ ⊤ := by
        rw [analyticOrderAt_riemannXi_eq_riemannZeta]
        exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top tau
      obtain ⟨k, hk, he⟩ := AnalyticAt.exists_logDeriv_eq_principalPart_add_analytic
        (analyticAt_riemannXi tau.1) hfinite
      rw [analyticOrderNatAt_riemannXi_eq_analyticZetaZeroMultiplicity] at he
      have ho : AnalyticAt ℂ (principalSum (W.erase tau)) tau.1 := by
        apply Finset.analyticAt_fun_sum
        intro sigma hsigma
        exact principal_analytic sigma (fun h =>
          (Finset.mem_erase.mp hsigma).1 (Subtype.ext h.symm))
      refine ⟨fun z => k z-principalSum (W.erase tau) z, hk.sub ho, ?_⟩
      filter_upwards [he] with z hz
      dsimp [raw]
      rw [hz, principalSum, ← W.add_sum_erase _ htau]
      dsimp [principalSum]
      ring)
  refine ⟨H, hH, fun s hs => ?_⟩
  have hsS : s ∉ S := by
    intro hm
    obtain ⟨tau, _, rfl⟩ := Finset.mem_image.mp hm
    exact hs ((riemannXi_eq_zero_iff_isNontrivialZetaZero tau.1).mpr tau.2)
  rw [hraw s hsS]
  dsimp [raw, W]
  ring

/-- The filled analytic local logarithmic-derivative remainder. -/
def localXiLogRemainder (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) : ℂ → ℂ :=
  Classical.choose (exists_localXiLogRemainder rho.1.im (radius rho hrho) (radius_pos rho hrho).le)

theorem localXiLogRemainder_spec (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) :
    AnalyticOnNhd ℂ (localXiLogRemainder rho hrho) (ball (center rho.1.im) (radius rho hrho)) ∧
    ∀ s, riemannXi s ≠ 0 → logDeriv riemannXi s =
      principalSum (localDivisor rho.1.im (radius rho hrho)) s+localXiLogRemainder rho hrho s :=
  Classical.choose_spec (exists_localXiLogRemainder rho.1.im (radius rho hrho) (radius_pos rho hrho).le)

/-- One analytic remainder after the finite genuine local modes are removed. -/
def analyticRemainder (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) (t : ℂ) : ℂ :=
  -((3/2-rho.1.re : ℝ) : ℂ)*localXiLogRemainder rho hrho
    (center rho.1.im-((3/2-rho.1.re : ℝ) : ℂ)*t)+regularGenerating (3/2-rho.1.re) rho.1.im t

/-- The selected zero and all competing local zeros keep the same negative sign. -/
def singularGenerating (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) (t : ℂ) : ℂ :=
  -∑ tau ∈ localDivisor rho.1.im (radius rho hrho),
    (analyticZetaZeroMultiplicity tau : ℂ)*((3/2-rho.1.re : ℝ) : ℂ)/
      (center rho.1.im-tau.1-((3/2-rho.1.re : ℝ) : ℂ)*t)

private theorem affine_mem (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re)
    {t : ℂ} (ht : ‖t‖ < radius rho hrho/(3/2-rho.1.re)) :
    center rho.1.im-((3/2-rho.1.re : ℝ) : ℂ)*t ∈ ball (center rho.1.im) (radius rho hrho) := by
  rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (source_pos rho).le]
  simpa only [mul_comm] using (lt_div_iff₀ (source_pos rho)).mp ht

theorem analyticOnNhd_analyticRemainder (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re)
    (hu : 3/2-rho.1.re ≤ 10001/20000) :
    AnalyticOnNhd ℂ (analyticRemainder rho hrho)
      (ball 0 (radius rho hrho/(3/2-rho.1.re))) := by
  intro t ht
  have ht' : ‖t‖ < radius rho hrho/(3/2-rho.1.re) := by simpa using ht
  have hlocal := (localXiLogRemainder_spec rho hrho).1 _ (affine_mem rho hrho ht')
  have hcompose := hlocal.comp (f := fun t : ℂ => center rho.1.im-((3/2-rho.1.re : ℝ) : ℂ)*t)
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
  have hold := analyticOnNhd_regularGenerating (source_pos rho).le hu
    (height_gt_fiftyFour rho hrho) t (by
      simpa using (ht'.trans (normalized_radius_bounds rho hrho hu).2).le)
  exact (analyticAt_const.mul hcompose).add hold

theorem fullGenerating_local (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re)
    (hu : 3/2-rho.1.re ≤ 10001/20000) {t : ℂ}
    (ht : ‖t‖ < radius rho hrho/(3/2-rho.1.re))
    (h1 : center rho.1.im-((3/2-rho.1.re : ℝ) : ℂ)*t ≠ 1)
    (hz : riemannZeta (center rho.1.im-((3/2-rho.1.re : ℝ) : ℂ)*t) ≠ 0) :
    fullGenerating (3/2-rho.1.re) rho.1.im t =
      singularGenerating rho hrho t+analyticRemainder rho hrho t := by
  have hxi : riemannXi (center rho.1.im-((3/2-rho.1.re : ℝ) : ℂ)*t) ≠ 0 := by
    intro h
    exact hz ((riemannXi_eq_zero_iff_isNontrivialZetaZero _).mp h).1
  rw [global_decomposition (source_pos rho).le hu (height_gt_fiftyFour rho hrho)
    (ht.trans (normalized_radius_bounds rho hrho hu).2).le h1 hz,
    (localXiLogRemainder_spec rho hrho).2 _ hxi]
  simp only [analyticRemainder, singularGenerating, principalSum, mul_add, Finset.mul_sum, add_assoc]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro tau _
  have he : center rho.1.im-((3/2-rho.1.re : ℝ) : ℂ)*t-tau.1 =
      center rho.1.im-tau.1-((3/2-rho.1.re : ℝ) : ℂ)*t := by ring
  rw [he]
  ring

/-- Cauchy's estimate on the fixed closed disk used in this local test. -/
theorem coefficient_bound_of_analytic {f : ℂ → ℂ}
    (ha : AnalyticOnNhd ℂ f (closedBall 0 (4/3 : ℝ))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      ‖signedTaylorMoment n f 0‖ ≤ M*(3/4 : ℝ)^n := by
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : ℂ) (4/3 : ℝ)).image_of_continuousOn
    ha.continuousOn).isBounded.exists_norm_le
  refine ⟨M, (norm_nonneg _).trans (hM _ ⟨0, mem_closedBall_self (by norm_num), rfl⟩), fun n => ?_⟩
  have hd : DiffContOnCl ℂ f (ball 0 (4/3 : ℝ)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by norm_num : (4/3 : ℝ) ≠ 0)]
    exact ha.differentiableOn
  have h := norm_signedTaylorMoment_le (by norm_num : (0 : ℝ) < 4/3) hd
    (fun z hz => hM _ ⟨z, sphere_subset_closedBall hz, rfl⟩) n
  rw [div_eq_mul_inv, ← inv_pow] at h
  norm_num only [inv_div] at h
  exact h

/-- A geometric coefficient bound for the single combined local remainder. -/
theorem analyticRemainder_coefficient_bound (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) (hu : 3/2-rho.1.re ≤ 10001/20000) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      ‖signedTaylorMoment n (analyticRemainder rho hrho) 0‖ ≤ M*(3/4 : ℝ)^n := by
  apply coefficient_bound_of_analytic
  exact (analyticOnNhd_analyticRemainder rho hrho hu).mono
    (closedBall_subset_ball (normalized_radius_bounds rho hrho hu).1)

/-- Exponentiating the analytic remainder alone retains a geometric
coefficient radius. Multiplication by the singular count factor is separate. -/
theorem exp_analyticRemainder_coefficient_bound (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) (hu : 3/2-rho.1.re ≤ 10001/20000) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      ‖signedTaylorMoment n (fun t => Complex.exp (analyticRemainder rho hrho t)-1) 0‖ ≤
        M*(3/4 : ℝ)^n := by
  apply coefficient_bound_of_analytic
  intro t ht
  have h := analyticOnNhd_analyticRemainder rho hrho hu t
    (closedBall_subset_ball (normalized_radius_bounds rho hrho hu).1 ht)
  exact h.cexp.sub analyticAt_const

/-- The finite local singular count response misses the literal core,
with actual multiplicities and every normal-derivative channel retained. -/
theorem local_singular_core (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re)
    (r : ℕ) {N K n : ℕ} (hN : 2 ≤ N)
    (hn : n ∈ ZetaRieszParityPacket.coreBand (3/2-rho.1.re) N K)
    (p : ℝ) {f : ZetaRieszNegativeModeSupport.Test}
    (hf : ∀ x ∈ tsupport (Function.uncurry f), |x.1-(1-p)| ≤ 7/100 ∧
      |x.2-(SquarefreeVaughanLogSource.length (3/2-rho.1.re) N/Real.log n-p)| ≤ 7/100) :
    ZetaRieszNegativeModeSupport.inversePrimitive r
      (ZetaRieszInfiniteModeAudit.zeroCopies (localDivisor rho.1.im (radius rho hrho)))
      (fun i => i.1.1-center rho.1.im) f = 0 := by
  exact ZetaRieszNegativeModeSupport.inversePrimitive_core_patch _ _ _
    (by linarith [NontrivialZetaZero.re_lt_one rho]) hN hn p hf

end
end RiemannGaussian.ZetaRieszLocalXiDivisor
