import RiemannGaussian.MontgomeryVaughan.Final

/-!
# A separable tensor Montgomery--Vaughan bound

The cubic-holonomy calculation exposes two oriented logarithmic gaps.  The
four-cycle coefficients occurring before the final overlap integration are
separable in those two gaps.  This file proves that the checked bilinear
Montgomery--Vaughan theorem may then be applied in both coordinates, with no
triangle inequality between the two Hilbert kernels.

This is a finite theorem.  It introduces no analytic or arithmetic
hypothesis beyond the already-proved `MVHilbert` inequality.
-/

namespace RiemannGaussian

noncomputable section

open Complex Finset
open scoped BigOperators ComplexConjugate

/-- The off-diagonal Hilbert form in the exact binder shape used by
`MVHilbert`. -/
def finiteHilbertForm {ι : Type} [Fintype ι] [DecidableEq ι]
    (frequency : ι → ℝ) (x z : ι → ℂ) : ℂ :=
  ∑ r, ∑ s, if r = s then 0
    else x r * conj (z s) / ((frequency r - frequency s : ℝ) : ℂ)

/-- A separable four-cycle with one oriented reciprocal gap in each
coordinate. -/
def separableTensorHilbertForm
    {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (frequency₁ : ι → ℝ) (frequency₂ : κ → ℝ)
    (x₁ z₁ : ι → ℂ) (x₂ z₂ : κ → ℂ) : ℂ :=
  ∑ r, ∑ s, ∑ p, ∑ q,
    (if r = s then 0
      else x₁ r * conj (z₁ s) /
        ((frequency₁ r - frequency₁ s : ℝ) : ℂ)) *
    (if p = q then 0
      else x₂ p * conj (z₂ q) /
        ((frequency₂ p - frequency₂ q : ℝ) : ℂ))

/-- The separable tensor form is literally the product of its two Hilbert
forms.  This equality is what avoids an absolute-value loss inside the
four-cycle. -/
theorem separableTensorHilbertForm_eq_mul
    {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (frequency₁ : ι → ℝ) (frequency₂ : κ → ℝ)
    (x₁ z₁ : ι → ℂ) (x₂ z₂ : κ → ℂ) :
    separableTensorHilbertForm frequency₁ frequency₂ x₁ z₁ x₂ z₂ =
      finiteHilbertForm frequency₁ x₁ z₁ *
        finiteHilbertForm frequency₂ x₂ z₂ := by
  unfold separableTensorHilbertForm finiteHilbertForm
  simp_rw [Finset.sum_mul, Finset.mul_sum]

/-- Applying Montgomery--Vaughan in the two independent coordinates gives
the product constant `C₁*C₂`. -/
theorem separableTensorHilbertForm_norm_le
    {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁)
    (hMV₁ : MVHilbert C₁) (hMV₂ : MVHilbert C₂)
    (frequency₁ gap₁ : ι → ℝ) (frequency₂ gap₂ : κ → ℝ)
    (x₁ z₁ : ι → ℂ) (x₂ z₂ : κ → ℂ)
    (hinj₁ : Function.Injective frequency₁)
    (hinj₂ : Function.Injective frequency₂)
    (hgap₁ : ∀ r, 0 < gap₁ r) (hgap₂ : ∀ p, 0 < gap₂ p)
    (hsep₁ : ∀ r s, r ≠ s → gap₁ r ≤ |frequency₁ r - frequency₁ s|)
    (hsep₂ : ∀ p q, p ≠ q → gap₂ p ≤ |frequency₂ p - frequency₂ q|) :
    ‖separableTensorHilbertForm frequency₁ frequency₂ x₁ z₁ x₂ z₂‖ ≤
      (C₁ * C₂) *
        (Real.sqrt (∑ r, ‖x₁ r‖ ^ 2 / gap₁ r) *
          Real.sqrt (∑ r, ‖z₁ r‖ ^ 2 / gap₁ r)) *
        (Real.sqrt (∑ p, ‖x₂ p‖ ^ 2 / gap₂ p) *
          Real.sqrt (∑ p, ‖z₂ p‖ ^ 2 / gap₂ p)) := by
  rw [separableTensorHilbertForm_eq_mul, norm_mul]
  have h₁ := hMV₁ ι frequency₁ gap₁ x₁ z₁ hinj₁ hgap₁ hsep₁
  have h₂ := hMV₂ κ frequency₂ gap₂ x₂ z₂ hinj₂ hgap₂ hsep₂
  change ‖finiteHilbertForm frequency₁ x₁ z₁‖ ≤ _ at h₁
  change ‖finiteHilbertForm frequency₂ x₂ z₂‖ ≤ _ at h₂
  calc
    ‖finiteHilbertForm frequency₁ x₁ z₁‖ *
        ‖finiteHilbertForm frequency₂ x₂ z₂‖ ≤
      (C₁ * Real.sqrt (∑ r, ‖x₁ r‖ ^ 2 / gap₁ r) *
          Real.sqrt (∑ r, ‖z₁ r‖ ^ 2 / gap₁ r)) *
        (C₂ * Real.sqrt (∑ p, ‖x₂ p‖ ^ 2 / gap₂ p) *
          Real.sqrt (∑ p, ‖z₂ p‖ ^ 2 / gap₂ p)) :=
      mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
    _ = (C₁ * C₂) *
        (Real.sqrt (∑ r, ‖x₁ r‖ ^ 2 / gap₁ r) *
          Real.sqrt (∑ r, ‖z₁ r‖ ^ 2 / gap₁ r)) *
        (Real.sqrt (∑ p, ‖x₂ p‖ ^ 2 / gap₂ p) *
          Real.sqrt (∑ p, ‖z₂ p‖ ^ 2 / gap₂ p)) := by ring

/-- Concrete checked constant for the two-coordinate Hilbert kernel. -/
theorem separableTensorHilbertForm_norm_le_676
    {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (frequency₁ gap₁ : ι → ℝ) (frequency₂ gap₂ : κ → ℝ)
    (x₁ z₁ : ι → ℂ) (x₂ z₂ : κ → ℂ)
    (hinj₁ : Function.Injective frequency₁)
    (hinj₂ : Function.Injective frequency₂)
    (hgap₁ : ∀ r, 0 < gap₁ r) (hgap₂ : ∀ p, 0 < gap₂ p)
    (hsep₁ : ∀ r s, r ≠ s → gap₁ r ≤ |frequency₁ r - frequency₁ s|)
    (hsep₂ : ∀ p q, p ≠ q → gap₂ p ≤ |frequency₂ p - frequency₂ q|) :
    ‖separableTensorHilbertForm frequency₁ frequency₂ x₁ z₁ x₂ z₂‖ ≤
      676 *
        (Real.sqrt (∑ r, ‖x₁ r‖ ^ 2 / gap₁ r) *
          Real.sqrt (∑ r, ‖z₁ r‖ ^ 2 / gap₁ r)) *
        (Real.sqrt (∑ p, ‖x₂ p‖ ^ 2 / gap₂ p) *
          Real.sqrt (∑ p, ‖z₂ p‖ ^ 2 / gap₂ p)) := by
  simpa only [show (26 : ℝ) * 26 = 676 by norm_num] using
    separableTensorHilbertForm_norm_le (C₁ := 26) (C₂ := 26)
      (by norm_num)
      MontgomeryVaughan.mvHilbert_twentySix
      MontgomeryVaughan.mvHilbert_twentySix
      frequency₁ gap₁ frequency₂ gap₂ x₁ z₁ x₂ z₂
      hinj₁ hinj₂ hgap₁ hgap₂ hsep₁ hsep₂

end

end RiemannGaussian
