/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticHorizontalBoundary
import RiemannGaussian.SuzukiCarrierFiniteGram
import RiemannGaussian.SuzukiCarrierPrincipalValue

/-!
# The actual finite real boundary of Suzuki's mixed carrier

For any ordered pair without a repeated real node, the complete Laurent
principal part at each real singularity is zero. Finite regularization
therefore supplies an analytic representative along every compact real
segment. The literal horizontal integral, with its original totalized
values, is continuous as the displacement tends to zero.

The no-real-collision condition includes every pair of off-axis zeros.
The repeated real-node channel has a principal-value boundary correction
and is not covered by the separated-channel limit proved here.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Topology Interval
namespace RiemannGaussian
noncomputable section

/-- Every real zero of the actual carrier denominator is a xi zero.
Thus no genuine carrier pole survives on the real axis. -/
theorem riemannXiSpectral_eq_zero_of_suzukiXiEValue_ofReal_eq_zero
    {x : ℝ} (hE : suzukiXiEValue (x : ℂ) = 0) : riemannXiSpectral (x : ℂ) = 0 := by
  apply Complex.ext _ (riemannXiSpectral_ofReal_im x)
  rw [← suzukiXiEValue_ofReal_re, hE]

/-- The no-real-collision condition is preserved by exchanging the
mixed indices, including the conjugation in the first denominator. -/
theorem suzukiXiMixed_no_real_collision_symm (rho sigma : NontrivialZetaZero)
    (h : starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ zetaSpectralCoordinate sigma.1 ∨
      (zetaSpectralCoordinate sigma.1).im ≠ 0) :
    starRingEnd ℂ (zetaSpectralCoordinate sigma.1) ≠ zetaSpectralCoordinate rho.1 ∨
      (zetaSpectralCoordinate rho.1).im ≠ 0 := by
  by_contra hn
  push Not at hn
  have he : starRingEnd ℂ (zetaSpectralCoordinate rho.1) = zetaSpectralCoordinate sigma.1 := by
    simpa using congrArg (starRingEnd ℂ) hn.1.symm
  rcases h with hne | him
  · exact hne he
  · apply him
    rw [← he, conj_im, hn.2, neg_zero]

/-- At a real xi node, the full principal part of a noncolliding mixed
channel vanishes identically, not just its residue or its norm. -/
theorem suzukiXiMixedCarrierLocalPrincipalPart_eq_zero_ofReal
    (rho sigma : NontrivialZetaZero)
    (h : starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ zetaSpectralCoordinate sigma.1 ∨
      (zetaSpectralCoordinate sigma.1).im ≠ 0)
    {x : ℝ} (hx : riemannXiSpectral (x : ℂ) = 0) (z : ℂ) :
    poleTaylorPrincipalPart (suzukiXiMixedCarrierLocalOrder (x : ℂ))
      (suzukiXiMixedCarrierLocalNumerator rho sigma (x : ℂ)) (x : ℂ) z = 0 := by
  have hcollision : ¬(starRingEnd ℂ (zetaSpectralCoordinate rho.1) = (x : ℂ) ∧
      zetaSpectralCoordinate sigma.1 = (x : ℂ)) := by
    rintro ⟨ha, hb⟩
    rcases h with hne | him
    · exact hne (ha.trans hb.symm)
    · exact him (by rw [hb]; rfl)
  have hn : suzukiXiMixedCarrierLocalNumerator rho sigma (x : ℂ) (x : ℂ) = 0 := by
    have hr := suzukiXiMixedCarrierLocalResidue_at_xi_node rho sigma hx
    simpa only [suzukiXiMixedCarrierLocalResidue, suzukiXiMixedCarrierLocalOrder, if_pos hx,
      poleTaylorResidue, one_ne_zero, if_false, Nat.sub_self, iteratedDeriv_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, suzukiXiMixedXiNodeResidue, if_neg hcollision] using hr
  simp [suzukiXiMixedCarrierLocalOrder, hx, poleTaylorPrincipalPart, hn]

/-- Every actual noncolliding mixed channel has an analytic representative
along any compact real interval, differing only on one explicit finite
window of its genuine xi and carrier-denominator singularities. -/
theorem exists_suzukiXiMixedCarrier_real_segment_regularization
    (rho sigma : NontrivialZetaZero)
    (h : starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ zetaSpectralCoordinate sigma.1 ∨
      (zetaSpectralCoordinate sigma.1).im ≠ 0) (l r : ℝ) :
    ∃ F : ℂ → ℂ, (∀ x ∈ uIcc l r, AnalyticAt ℂ F (x : ℂ)) ∧
      ∀ z ∉ suzukiXiCarrierPoleWindow l r (-1) 1, F z = suzukiXiMixedCarrierChannel rho sigma z := by
  let U : Set ℂ := Complex.Rectangle ((l : ℂ) + ((-1 : ℝ) : ℂ) * I) ((r : ℂ) + (1 : ℂ) * I)
  let S := suzukiXiCarrierPoleWindow l r (-1) 1
  obtain ⟨H, hHU, hHoff⟩ := exists_finitePole_analytic_regularization U S
    (suzukiXiMixedCarrierChannel rho sigma) suzukiXiMixedCarrierLocalOrder
    (suzukiXiMixedCarrierLocalNumerator rho sigma)
    (fun c hc => (mem_suzukiXiCarrierPoleWindow.mp hc).1)
    (fun z hz hn => analyticAt_suzukiXiMixedCarrierChannel_of_not_mem rho sigma
      (fun hb => hn (mem_suzukiXiCarrierPoleWindow.mpr ⟨hz, hb⟩)))
    (fun c _ => analyticAt_suzukiXiMixedCarrierLocalNumerator rho sigma c)
    (fun c _ => suzukiXiMixedCarrierChannel_eventually_eq_local_model rho sigma c)
  let P := finitePolePrincipalSum S suzukiXiMixedCarrierLocalOrder
    (suzukiXiMixedCarrierLocalNumerator rho sigma)
  refine ⟨fun z => H z + P z, ?_, ?_⟩
  · intro x hx
    have hxU : (x : ℂ) ∈ U := by
      simpa [U, Complex.Rectangle, Complex.mem_reProdIm] using And.intro hx
        (show (0 : ℝ) ∈ uIcc (-1) 1 by norm_num)
    apply (hHU _ hxU).add
    apply Finset.analyticAt_fun_sum
    intro c hc
    by_cases hxc : (x : ℂ) = c
    · subst c
      have hxi : riemannXiSpectral (x : ℂ) = 0 := by
        rcases (mem_suzukiXiCarrierPoleWindow.mp hc).2 with hxi | hE
        · exact hxi
        · exact riemannXiSpectral_eq_zero_of_suzukiXiEValue_ofReal_eq_zero hE
      have he : poleTaylorPrincipalPart (suzukiXiMixedCarrierLocalOrder (x : ℂ))
          (suzukiXiMixedCarrierLocalNumerator rho sigma (x : ℂ)) (x : ℂ) = fun _ => 0 :=
        funext (suzukiXiMixedCarrierLocalPrincipalPart_eq_zero_ofReal rho sigma h hxi)
      rw [he]
      exact analyticAt_const
    · exact analyticAt_poleTaylorPrincipalPart_of_ne _ _ hxc
  · intro z hz
    change H z + P z = _
    rw [hHoff z hz]
    exact sub_add_cancel _ _

/-- The literal mixed bottom integral is continuous through height zero
for every pair without a repeated real node. No denominator exclusions or
boundary convergence premises remain for this finite-interval result. -/
theorem continuousAt_suzukiXiMixedCarrierBottomIntegral_of_no_real_collision
    (rho sigma : NontrivialZetaZero)
    (h : starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ zetaSpectralCoordinate sigma.1 ∨
      (zetaSpectralCoordinate sigma.1).im ≠ 0) (l r : ℝ) :
    ContinuousAt (suzukiXiMixedCarrierBottomIntegral rho sigma l r) 0 := by
  obtain ⟨F, hF, he⟩ := exists_suzukiXiMixedCarrier_real_segment_regularization rho sigma h l r
  exact continuousAt_horizontalIntervalIntegral_of_finite_regularization
    (suzukiXiCarrierPoleWindow l r (-1) 1) l r hF he

/-- The genuine common-carrier Gram entry on a finite real interval,
with both mixed nodes and the original endpoint orientation retained. -/
def suzukiXiTruncatedBoundaryCarrierGramKernel
    (rho sigma : NontrivialZetaZero) (l r : ℝ) : ℂ :=
  ∫ x : ℝ in l..r, suzukiXiBoundaryCarrierGramIntegrand rho sigma x

/-- The actual truncated Gram has the same signed continuation integrand
as the whole-axis Gram, including at all exceptional points almost everywhere. -/
theorem suzukiXiTruncatedBoundaryCarrierGramKernel_eq_continuation_integral
    (rho sigma : NontrivialZetaZero) (l r : ℝ) :
    suzukiXiTruncatedBoundaryCarrierGramKernel rho sigma l r =
      ∫ x : ℝ in l..r, suzukiXiCarrierGramContinuation rho sigma (x : ℂ) := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [suzukiRealAxisXiZeroCarrier_ae_quadratic_eq_signed] with x hx
  intro _
  unfold suzukiXiBoundaryCarrierGramIntegrand suzukiXiCarrierGramContinuation
  rw [hx, div_div]
  simp only [suzukiRealAxisXiZeroCarrier, suzukiXiSharpCarrier_ofReal]

/-- The original first mixed channel is absolutely integrable on the
whole real axis when it has no repeated real node. -/
theorem integrable_suzukiXiMixedCarrierChannel_ofReal_of_no_real_collision
    (rho sigma : NontrivialZetaZero)
    (h : starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ zetaSpectralCoordinate sigma.1 ∨
      (zetaSpectralCoordinate sigma.1).im ≠ 0) :
    Integrable (fun x : ℝ => suzukiXiMixedCarrierChannel rho sigma (x : ℂ)) := by
  have hp := integrable_suzukiXiCarrier_two_resolvents_of_no_real_collision
    rho.conjugatePartner sigma
    (by simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner] using h)
  simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner,
    suzukiXiMixedCarrierChannel, suzukiRealAxisXiZeroCarrier] using hp

private lemma mixed_sub_conjugate_transpose (rho sigma : NontrivialZetaZero) (x : ℝ) :
    (suzukiXiMixedCarrierChannel rho sigma (x : ℂ) -
      starRingEnd ℂ (suzukiXiMixedCarrierChannel sigma rho (x : ℂ))) / (2 * I) =
        suzukiXiCarrierGramContinuation rho sigma (x : ℂ) := by
  unfold suzukiXiMixedCarrierChannel suzukiXiCarrierGramContinuation
  simp only [map_mul, map_sub, conj_ofReal, starRingEnd_self_apply, map_inv₀,
    suzukiXiSharpCarrier_ofReal, suzukiRealAxisXiZeroCarrier, div_eq_mul_inv, mul_inv]
  ring

/-- At height zero the displaced signed matrix is exactly the actual
truncated Gram whenever its two separated channels are integrable. -/
theorem suzukiXiDisplacedBottomGram_zero_eq_truncatedGram
    (rho sigma : NontrivialZetaZero)
    (h : starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ zetaSpectralCoordinate sigma.1 ∨
      (zetaSpectralCoordinate sigma.1).im ≠ 0) (l r : ℝ) :
    suzukiXiDisplacedBottomGram rho sigma l r 0 =
      suzukiXiTruncatedBoundaryCarrierGramKernel rho sigma l r := by
  have hi := (integrable_suzukiXiMixedCarrierChannel_ofReal_of_no_real_collision rho sigma h).intervalIntegrable
    (a := l) (b := r)
  have hj := (integrable_suzukiXiMixedCarrierChannel_ofReal_of_no_real_collision sigma rho
    (suzukiXiMixed_no_real_collision_symm rho sigma h)).intervalIntegrable (a := l) (b := r)
  have hjc : IntervalIntegrable (fun x : ℝ =>
      starRingEnd ℂ (suzukiXiMixedCarrierChannel sigma rho (x : ℂ))) volume l r :=
    ⟨(Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hj.1,
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hj.2⟩
  rw [suzukiXiTruncatedBoundaryCarrierGramKernel_eq_continuation_integral]
  unfold suzukiXiDisplacedBottomGram suzukiXiMixedCarrierBottomIntegral
  simp only [ofReal_zero, zero_mul, add_zero]
  rw [← intervalIntegral.intervalIntegral_conj, ← intervalIntegral.integral_sub hi hjc,
    ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro x _
  exact mixed_sub_conjugate_transpose rho sigma x

/-- The genuine displaced signed mixed matrix converges to the actual
truncated boundary Gram. Conjugation exchanges the indices before the limit;
no pole correction or cross term is dropped. -/
theorem tendsto_suzukiXiDisplacedBottomGram_truncatedGram
    (rho sigma : NontrivialZetaZero)
    (h : starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ zetaSpectralCoordinate sigma.1 ∨
      (zetaSpectralCoordinate sigma.1).im ≠ 0) (l r : ℝ) :
    Tendsto (suzukiXiDisplacedBottomGram rho sigma l r) (𝓝 (0 : ℝ))
      (𝓝 (suzukiXiTruncatedBoundaryCarrierGramKernel rho sigma l r)) := by
  have hi := continuousAt_suzukiXiMixedCarrierBottomIntegral_of_no_real_collision rho sigma h l r
  have hj := continuousAt_suzukiXiMixedCarrierBottomIntegral_of_no_real_collision sigma rho
    (suzukiXiMixed_no_real_collision_symm rho sigma h) l r
  have hc : ContinuousAt (suzukiXiDisplacedBottomGram rho sigma l r) 0 :=
    (hi.sub hj.star).div_const _
  simpa only [suzukiXiDisplacedBottomGram_zero_eq_truncatedGram rho sigma h] using hc.tendsto

/-- Exhausting the real axis by any two endpoint sequences recovers the
complete genuine Gram entry. This needs no node-separation hypothesis and
does not assert a rate for the truncation error. -/
theorem tendsto_suzukiXiTruncatedBoundaryCarrierGramKernel
    (rho sigma : NontrivialZetaZero) {ι : Type*} {p : Filter ι} [IsCountablyGenerated p]
    {l r : ι → ℝ} (hl : Tendsto l p atBot) (hr : Tendsto r p atTop) :
    Tendsto (fun k => suzukiXiTruncatedBoundaryCarrierGramKernel rho sigma (l k) (r k)) p
      (𝓝 (suzukiXiBoundaryCarrierGramKernel rho sigma)) :=
  intervalIntegral_tendsto_integral (integrable_suzukiXiBoundaryCarrierGramIntegrand rho sigma) hl hr

end
end RiemannGaussian
