import RiemannGaussian.EtaThinStripPrefix
import RiemannGaussian.EtaThinStripFactor

/-!
# Small-power zeta control through all dyadic resonances

Height-adapted eta prefixes control the boundary of every variable-width
dyadic rectangle. Maximum modulus for the entire pole-removed zeta
function carries the same estimate through the interior, including the
dyadic factor's zeros and the removable point at one.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The actual height-adapted eta bound controls the pole-removed
function on each safe boundary of a thin dyadic rectangle. -/
theorem norm_riemannZeta₁_le_etaThinRectangle_envelope {s : ℂ} {epsilon y : ℝ}
    (he : 0 < epsilon) (hehi : epsilon ≤ 1 / 2)
    (hslo : 1 - epsilon ≤ s.re) (hshi : s.re ≤ 1 + epsilon)
    (him : |s.im - y| ≤ etaDyadicImaginaryPeriod)
    (hfactor : epsilon / 4 ≤ ‖1 - 2 * (2 : ℂ) ^ (-s)‖) :
    ‖riemannZeta₁ s‖ ≤ 24 * (|y| + 20) * (|y| + 20) ^ epsilon / epsilon ^ 2 := by
  have hspos : 0 < s.re := by linarith
  have himabs : |s.im| ≤ |y| + 16 := by
    have h := abs_add_le (s.im - y) y
    rw [sub_add_cancel] at h
    linarith [etaDyadicImaginaryPeriod_le_sixteen]
  have hreabs : |s.re| ≤ 3 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hreone : |s.re - 1| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hn : ‖s‖ ≤ |y| + 20 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    linarith
  have hn1 : ‖s - 1‖ ≤ |y| + 20 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h
    linarith
  have heta := norm_pairedEtaCore_le_thinStrip_height he hehi hslo
    (by linarith [abs_nonneg y] : 3 ≤ |y| + 20) hn
  have heq := congrArg norm (pairedEtaCore_mul_sub_one_eq_factor_riemannZeta₁ hspos)
  simp only [norm_mul] at heq
  have hm : epsilon / 4 * ‖riemannZeta₁ s‖ ≤
      6 * (|y| + 20) * (|y| + 20) ^ epsilon / epsilon := by
    calc
      _ ≤ ‖1 - 2 * (2 : ℂ) ^ (-s)‖ * ‖riemannZeta₁ s‖ :=
        mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
      _ = ‖pairedEtaCore s‖ * ‖s - 1‖ := heq.symm
      _ ≤ (6 * (|y| + 20) ^ epsilon / epsilon) * (|y| + 20) :=
        mul_le_mul heta hn1 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hm' := (le_div_iff₀ he).mp hm
  rw [le_div_iff₀ (pow_pos he 2)]
  nlinarith

/-- Pole-removed zeta has a small-power height bound on the full
closed thin strip; no exclusion of dyadic resonances is required. -/
theorem norm_riemannZeta₁_le_etaThinStrip {s : ℂ} {epsilon : ℝ}
    (he : 0 < epsilon) (hehi : epsilon ≤ 1 / 2)
    (hslo : 1 - epsilon ≤ s.re) (hshi : s.re ≤ 1 + epsilon) :
    ‖riemannZeta₁ s‖ ≤ 24 * (|s.im| + 20) * (|s.im| + 20) ^ epsilon / epsilon ^ 2 := by
  obtain ⟨n, hn⟩ := exists_etaDyadicRectangle_center s.im
  let a := etaDyadicImaginaryPeriod * n - etaDyadicImaginaryPeriod / 2
  let b := etaDyadicImaginaryPeriod * n + etaDyadicImaginaryPeriod / 2
  have hab : a < b := by dsimp [a, b]; linarith [etaDyadicImaginaryPeriod_pos]
  have hsab : s.im ∈ Icc a b := hn
  have hwidth : 1 - epsilon < 1 + epsilon := by linarith
  have hnear {y : ℝ} (hy : y ∈ Icc a b) : |y - s.im| ≤ etaDyadicImaginaryPeriod := by
    have hlen : b - a = etaDyadicImaginaryPeriod := by dsimp [a, b]; ring
    exact abs_le.mpr ⟨by linarith [hy.1, hsab.2], by linarith [hy.2, hsab.1]⟩
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    ((isBounded_Ioo (1 - epsilon) (1 + epsilon)).reProdIm (isBounded_Ioo a b))
    differentiable_riemannZeta₁.diffContOnCl
  · intro z hz
    rw [frontier_reProdIm, closure_Ioo hwidth.ne, frontier_Ioo hwidth,
      closure_Ioo hab.ne, frontier_Ioo hab] at hz
    rcases hz with hz | hz
    · have hzab : z.im = a ∨ z.im = b := by simpa using hz.2
      have hzmem : z.im ∈ Icc a b := by
        rcases hzab with hzab | hzab
        · rw [hzab]; exact ⟨le_rfl, hab.le⟩
        · rw [hzab]; exact ⟨hab.le, le_rfl⟩
      apply norm_riemannZeta₁_le_etaThinRectangle_envelope he hehi hz.1.1 hz.1.2 (hnear hzmem)
      exact (by linarith : epsilon / 4 ≤ 1).trans
        (one_le_norm_etaFactor_of_cos_eq_neg_one (cos_log_two_mul_etaDyadicRectangle_boundary n hzab))
    · have hzre : z.re = 1 - epsilon ∨ z.re = 1 + epsilon := by simpa using hz.1
      have hzlo : 1 - epsilon ≤ z.re := by rcases hzre with h | h <;> linarith
      have hzhi : z.re ≤ 1 + epsilon := by rcases hzre with h | h <;> linarith
      exact norm_riemannZeta₁_le_etaThinRectangle_envelope he hehi hzlo hzhi (hnear hz.2)
        (quarter_width_le_norm_etaFactor_of_re_boundary he hehi hzre)
  · rw [closure_reProdIm, closure_Ioo hwidth.ne, closure_Ioo hab.ne]
    exact ⟨⟨hslo, hshi⟩, hsab⟩

end

end RiemannGaussian
