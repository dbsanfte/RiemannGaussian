/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaStripBoundaryConstraint
import RiemannGaussian.ZetaGaussianNearCancellation

/-!
# A strip bound retaining every selected zero and its ordinate

Any finite group of actual zeros in the physical strip retains its complete
multiplicity-weighted cotangent source in the limiting boundary inequality.
The group need not share an ordinate. In particular, the entire nearby ball
used by the Gaussian compensation has this bound, with no omitted nearby
zero contribution and no exchange of an infinite divisor sum with a limit.
-/

namespace RiemannGaussian.ZetaStripFiniteSource
noncomputable section
open Complex Filter Metric Set MeromorphicOn
open AnalyticStripDisc AnalyticDiscSignedDerivative AnalyticDiscBoundaryMoment
open ZetaStripDisc ZetaStripCotangentSource ZetaStripBoundaryConstraint
open CotangentRegularization (frequency)
open scoped Topology Classical

/-- The physical complex cotangent source with the actual analytic multiplicity. -/
def cotangent (η : ℝ) (c : ℂ) (ρ : NontrivialZetaZero) : ℂ :=
  (analyticZetaZeroMultiplicity ρ : ℂ) * (frequency η : ℂ) *
    Complex.cot ((frequency η : ℂ) * (c - ρ.1))

/-- Distinct actual zeros in the physical strip have distinct disc coordinates. -/
theorem coordinate_inj {c : ℂ} {η : ℝ} (hη : 0 < η)
    {ρ τ : NontrivialZetaZero} (hρ : ρ.1 ∈ strip c η) (hτ : τ.1 ∈ strip c η)
    (he : coordinate c η ρ.1 = coordinate c η τ.1) : ρ = τ := by
  apply Subtype.ext
  have h := congrArg (AnalyticStripMap.map c η) he
  simpa only [coordinate, AnalyticStripMap.map_tan c hη hρ,
    AnalyticStripMap.map_tan c hη hτ] using h

/-- Every selected finite group is bounded by the complete favorable divisor,
without merging coordinates or discarding any selected multiplicity. -/
theorem finite_source_le (S : Finset NontrivialZetaZero) {c : ℂ} {η r : ℝ}
    (hc : 1 < c.re) (hη : 0 < η) (hleft : η < c.re) (hr : 0 < r) (hr1 : r < 1)
    (hS : ∀ ρ ∈ S, ρ.1 ∈ strip c η)
    (hmem : ∀ ρ ∈ S, coordinate c η ρ.1 ∈ ball 0 r) :
    (∑ ρ ∈ S, (analyticZetaZeroMultiplicity ρ : ℝ) *
      (kernel r (coordinate c η ρ.1)).re) ≤ (source c η r).re := by
  have hd := (analyticOnNhd_carrier hη hleft hr1).meromorphicOn.divisor_ball_support_finite
  have hf : (fun w => (divisor (carrier c η) (ball 0 r) w : ℝ) *
      (kernel r w).re).HasFiniteSupport :=
    hd.subset (by intro w hw hdw; exact hw (by simp [hdw]))
  have hsum : Summable (fun w => (divisor (carrier c η) (ball 0 r) w : ℝ) *
      (kernel r w).re) := summable_of_hasFiniteSupport hf
  have h := hsum.sum_le_tsum
    (S.image fun ρ => coordinate c η ρ.1) (fun w _ => term_nonneg hc hη hleft hr hr1 w)
  rw [tsum_eq_finsum hf, ← source_re hη hleft hr1,
    Finset.sum_image (fun ρ hρ τ hτ he => coordinate_inj hη (hS ρ hρ) (hS τ hτ) he)] at h
  convert! h using 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [divisor_at_zero ρ hη hleft hr1 (hS ρ hρ) (hmem ρ hρ), Int.cast_natCast]

/-- The exact finite physical inequality carries an arbitrary selected group
beside the original logarithmic derivative and rational pole correction. -/
theorem normalized_finite_constraint (S : Finset NontrivialZetaZero) {c : ℂ} {η r : ℝ}
    (hc : 1 < c.re) (hη : 0 < η) (hleft : η < c.re) (hr : 0 < r) (hr1 : r < 1)
    (hs : ∀ w : ℂ, ‖w‖ = r → carrier c η w ≠ 0)
    (hS : ∀ ρ ∈ S, ρ.1 ∈ strip c η)
    (hmem : ∀ ρ ∈ S, coordinate c η ρ.1 ∈ ball 0 r) :
    (-logDeriv riemannZeta c).re +
      (∑ ρ ∈ S, (Real.pi / (4 * η)) * (analyticZetaZeroMultiplicity ρ : ℝ) *
        (kernel r (coordinate c η ρ.1)).re) ≤
      (Real.pi / (4 * η)) * (-moment (carrier c η) r).re +
        (1 / (c - 1) - 1 / (c + 1)).re := by
  have h := congrArg Complex.re (logarithmic_identity hc hη hleft hr hr1 hs)
  have hz := finite_source_le S hc hη hleft hr hr1 hS hmem
  have he : 4 * (η : ℂ) / Real.pi = ((4 * η / Real.pi : ℝ) : ℂ) := by push_cast; rfl
  rw [he] at h
  have hu : (4 * η / Real.pi) * (-logDeriv riemannZeta c).re +
      (∑ ρ ∈ S, (analyticZetaZeroMultiplicity ρ : ℝ) *
        (kernel r (coordinate c η ρ.1)).re) ≤
      (-moment (carrier c η) r).re +
        (4 * η / Real.pi) * (1 / (c - 1) - 1 / (c + 1)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.add_re, Complex.sub_re, Complex.neg_re] at h ⊢
    nlinarith
  have hu := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ Real.pi / (4 * η))
  have he : (Real.pi / (4 * η)) * (4 * η / Real.pi) = 1 := by field_simp
  simpa only [mul_add, Finset.mul_sum, ← mul_assoc, he, one_mul] using hu

/-- The physical limiting kernel is the full cotangent source, retaining
the imaginary displacement of the selected zero. -/
theorem normalized_kernel_one (ρ : NontrivialZetaZero) {c : ℂ} {η : ℝ}
    (hc : 1 < c.re) (hη : 0 < η) (hρ : ρ.1 ∈ strip c η) :
    (Real.pi / (4 * η)) * (analyticZetaZeroMultiplicity ρ : ℝ) *
      (kernel 1 (coordinate c η ρ.1)).re = (cotangent η c ρ).re := by
  rw [kernel_one_coordinate_re ρ hc hη hρ]
  have he : Real.pi * (ρ.1 - c) / (2 * (η : ℂ)) =
      -((frequency η : ℂ) * (c - ρ.1)) := by
    unfold frequency
    push_cast
    ring
  rw [he, Complex.cot_eq_cos_div_sin, Complex.cos_neg, Complex.sin_neg, div_neg]
  norm_num only [cotangent, Complex.cot_eq_cos_div_sin, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re,
    Complex.natCast_im, Complex.neg_im, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, mul_zero, sub_zero, zero_add]
  unfold frequency
  ring

/-- Each selected complex source has its exact physical limit, without
an ordinate-alignment hypothesis. -/
theorem source_tendsto (ρ : NontrivialZetaZero) {c : ℂ} {η : ℝ}
    (hc : 1 < c.re) (hη : 0 < η) (hρ : ρ.1 ∈ strip c η)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => (Real.pi / (4 * η)) * (analyticZetaZeroMultiplicity ρ : ℝ) *
      (kernel (r n) (coordinate c η ρ.1)).re) atTop (𝓝 (cotangent η c ρ).re) := by
  have h := ((Complex.continuous_re.tendsto _).comp
    (kernel_tendsto hr (coordinate c η ρ.1))).const_mul
      ((Real.pi / (4 * η)) * (analyticZetaZeroMultiplicity ρ : ℝ))
  rwa [normalized_kernel_one ρ hc hη hρ] at h

/-- The actual complete boundary bounds any finite group of strip zeros.
Every selected ordinate and multiplicity survives the limiting argument. -/
theorem finite_zero_constraint (S : Finset NontrivialZetaZero) {c : ℂ} {η M : ℝ}
    (hc : 1 < c.re) (hη : 0 < η) (hlo : (1 / 2 : ℝ) ≤ c.re - η)
    (hhi : c.re + η ≤ 3 / 2) (hM : 0 ≤ M)
    (hS : ∀ ρ ∈ S, ρ.1 ∈ strip c η) :
    (-logDeriv riemannZeta c).re + (∑ ρ ∈ S, (cotangent η c ρ).re) ≤
      boundary c η M + (1 / (c - 1) - 1 / (c + 1)).re := by
  obtain ⟨r, hr, hs⟩ := ZetaStripDisc.exists_sphere_tendsto hc hη (by linarith)
  have hsource := (tendsto_finsetSum S (fun ρ hρ => source_tendsto ρ hc hη (hS ρ hρ) hr)).const_add
    (-logDeriv riemannZeta c).re
  have hbound := (finite_boundary_tendsto hc hη hlo hhi hM hr
    (fun n => (hs n).1.le) (fun n => (hs n).2.1)).add_const (1 / (c - 1) - 1 / (c + 1)).re
  apply le_of_tendsto_of_tendsto hsource hbound
  have hmem : ∀ᶠ n in atTop, ∀ ρ ∈ S, coordinate c η ρ.1 ∈ ball 0 (r n) :=
    (eventually_all_finset S).mpr (fun ρ hρ => eventually_coordinate_mem ρ hη (hS ρ hρ) hr)
  filter_upwards [hmem] with n hn
  exact (normalized_finite_constraint S hc hη (by linarith) (hs n).1 (hs n).2.1
    (hs n).2.2 hS hn).trans
      (add_le_add (finite_boundary_le hc hη hlo hhi hM (hs n).1 (hs n).2.1 (hs n).2.2) le_rfl)

/-- The whole physical nearby ball contains only finitely many actual zeros. -/
theorem finite_near_zeros (η : ℝ) (c : ℂ) :
    {ρ : NontrivialZetaZero | ‖c - ρ.1‖ < η}.Finite := by
  simpa [Function.support, ZetaGaussianNearCancellation.nearRestrict] using
    ZetaGaussianNearCancellation.finite_support_nearRestrict η c (fun _ => 1)

/-- The complete finite nearby divisor, independent of any source's value. -/
def nearZeros (η : ℝ) (c : ℂ) : Finset NontrivialZetaZero := (finite_near_zeros η c).toFinset

/-- Membership in the nearby divisor is exactly the original open-ball test. -/
@[simp] theorem mem_nearZeros (η : ℝ) (c : ℂ) (ρ : NontrivialZetaZero) :
    ρ ∈ nearZeros η c ↔ ‖c - ρ.1‖ < η := Set.Finite.mem_toFinset _

/-- The infinite notation for the nearby cotangent carrier is exactly the
finite complex sum over the complete nearby divisor. -/
theorem tsum_nearCotangent (η : ℝ) (c : ℂ) :
    (∑' ρ : NontrivialZetaZero, ZetaGaussianNearCancellation.nearCotangent η c ρ) =
      ∑ ρ ∈ nearZeros η c, cotangent η c ρ := by
  rw [tsum_eq_sum (s := nearZeros η c) (fun ρ hρ => by
    simp only [mem_nearZeros] at hρ
    simp [ZetaGaussianNearCancellation.nearCotangent,
      ZetaGaussianNearCancellation.nearRestrict, hρ])]
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [mem_nearZeros] at hρ
  simp [ZetaGaussianNearCancellation.nearCotangent,
    ZetaGaussianNearCancellation.nearRestrict, hρ, cotangent]

/-- Every nearby zero belongs to the same physical strip used by its
cotangent correction, regardless of imaginary displacement. -/
theorem near_mem_strip {η : ℝ} {c : ℂ} {ρ : NontrivialZetaZero}
    (hρ : ρ ∈ nearZeros η c) : ρ.1 ∈ strip c η := by
  have h := (Complex.abs_re_le_norm (c - ρ.1)).trans_lt ((mem_nearZeros η c ρ).mp hρ)
  change |ρ.1.re - c.re| < η
  rw [abs_sub_comm]
  exact h

/-- The complete nearby cotangent sum is controlled by the same signed
strip boundary. This is the source needed by Gaussian compensation. -/
theorem near_zero_constraint {c : ℂ} {η M : ℝ}
    (hc : 1 < c.re) (hη : 0 < η) (hlo : (1 / 2 : ℝ) ≤ c.re - η)
    (hhi : c.re + η ≤ 3 / 2) (hM : 0 ≤ M) :
    (-logDeriv riemannZeta c).re +
      (∑' ρ : NontrivialZetaZero, ZetaGaussianNearCancellation.nearCotangent η c ρ).re ≤
      boundary c η M + (1 / (c - 1) - 1 / (c + 1)).re := by
  rw [tsum_nearCotangent, Complex.re_sum]
  exact finite_zero_constraint (nearZeros η c) hc hη hlo hhi hM (fun _ hρ => near_mem_strip hρ)

end
end RiemannGaussian.ZetaStripFiniteSource
