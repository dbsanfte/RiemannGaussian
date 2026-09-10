/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGlobalPoisson

/-!
# A reflected Poisson comparison for the entire zero strip

This is a parameterized version of the classical Stechkin comparison.
The two horizontally reflected contributions are combined before their
sign is estimated. The auxiliary abscissa and subtraction coefficient are
defined algebraically, without a search for coefficients.

For background see H. Kadiri, *Explicit zero-free regions for Dedekind zeta
functions*, Lemma 2.1 (2011). The proof below is an independent real-algebra
calculation. It neither assumes RH nor assigns a sign to an unpaired
horizontal difference.
-/

namespace RiemannGaussian
noncomputable section

/-- The two Poisson atoms belonging to a zero and its critical reflection,
before multiplication by the actual zero multiplicity. -/
def stechkinPoissonPair (σ β t : ℝ) : ℝ :=
  (σ - β) / ((σ - β) ^ 2 + t ^ 2) +
    (σ - 1 + β) / ((σ - 1 + β) ^ 2 + t ^ 2)

/-- The algebraically defined comparison abscissa. -/
def zetaStechkinAbscissa (σ : ℝ) : ℝ := (1 + Real.sqrt (1 + 4 * σ ^ 2)) / 2

/-- The subtraction coefficient keeps the full selected right-half source.
It is allowed to depend on the evaluation abscissa. -/
def zetaStechkinWeight (σ : ℝ) : ℝ := σ / (2 * zetaStechkinAbscissa σ - 1)

/-- The exact auxiliary quadratic identity. -/
theorem zetaStechkinAbscissa_quadratic (σ : ℝ) :
    zetaStechkinAbscissa σ * (zetaStechkinAbscissa σ - 1) = σ ^ 2 := by
  have h := Real.sq_sqrt (show 0 ≤ 1 + 4 * σ ^ 2 by positivity)
  unfold zetaStechkinAbscissa
  nlinarith

/-- The comparison line stays strictly inside the Euler half-plane and
strictly to the right of the original evaluation line. -/
theorem lt_zetaStechkinAbscissa {σ : ℝ} (hσ : 1 ≤ σ) : σ < zetaStechkinAbscissa σ := by
  have hs : 0 ≤ Real.sqrt (1 + 4 * σ ^ 2) := Real.sqrt_nonneg _
  have h := Real.sq_sqrt (show 0 ≤ 1 + 4 * σ ^ 2 by positivity)
  unfold zetaStechkinAbscissa
  nlinarith

/-- The subtraction coefficient is positive and below one, so the
comparison also preserves nonnegative prime-power weights. -/
theorem zetaStechkinWeight_mem_Ioo {σ : ℝ} (hσ : 1 ≤ σ) :
    zetaStechkinWeight σ ∈ Set.Ioo (0 : ℝ) 1 := by
  have ht := lt_zetaStechkinAbscissa hσ
  have hd : 0 < 2 * zetaStechkinAbscissa σ - 1 := by linarith
  constructor
  · exact div_pos (by linarith) hd
  · exact (div_lt_one hd).mpr (by linarith)

/-- The coefficient is at least the classical uniform Stechkin value on
the entire closed range `sigma >= 1`. -/
theorem classical_le_zetaStechkinWeight {σ : ℝ} (hσ : 1 ≤ σ) :
    1 / Real.sqrt 5 ≤ zetaStechkinWeight σ := by
  have h5 : 0 < Real.sqrt 5 := by positivity
  have hs : 0 < Real.sqrt (1 + 4 * σ ^ 2) := by positivity
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + 4 * σ ^ 2 by positivity)
  have h5sq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hσ0 : 0 < σ := by linarith
  have hb : (σ * Real.sqrt 5) ^ 2 = 5 * σ ^ 2 := by rw [mul_pow, h5sq]; ring
  have hle : Real.sqrt (1 + 4 * σ ^ 2) ≤ σ * Real.sqrt 5 := by
    nlinarith [sq_nonneg (σ - 1), mul_pos hσ0 h5]
  have hdiv : 1 / Real.sqrt 5 ≤ σ / Real.sqrt (1 + 4 * σ ^ 2) :=
    (div_le_div_iff₀ h5 hs).mpr (by simpa using hle)
  unfold zetaStechkinWeight zetaStechkinAbscissa
  convert hdiv using 1
  ring_nf

/-- The coefficient exactly uses the selected-source allowance. -/
theorem zetaStechkinWeight_mul {σ : ℝ} (hσ : 1 ≤ σ) :
    zetaStechkinWeight σ * (2 * zetaStechkinAbscissa σ - 1) = σ := by
  have ht := lt_zetaStechkinAbscissa hσ
  have hd : 2 * zetaStechkinAbscissa σ - 1 ≠ 0 := ne_of_gt (by linarith)
  exact div_mul_cancel₀ σ hd

/-- The combined rational numerator retains the reflection displacement
through its square. -/
theorem stechkinPoissonPair_eq {σ β : ℝ} (hσ : 1 ≤ σ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℝ) :
    stechkinPoissonPair σ β t =
      (2 * σ - 1) * (σ * (σ - 1) + β * (1 - β) + t ^ 2) /
        ((σ * (σ - 1) + β * (1 - β) + t ^ 2) ^ 2 +
          (2 * β - 1) ^ 2 * t ^ 2) := by
  have hu : 0 < σ - β := by linarith
  have hv : 0 < σ - 1 + β := by linarith
  have hx : 0 < σ * (σ - 1) + β * (1 - β) + t ^ 2 := by
    have h := mul_pos hβ0 (sub_pos.mpr hβ1)
    have hh := mul_nonneg (by linarith : 0 ≤ σ) (by linarith : 0 ≤ σ - 1)
    positivity
  unfold stechkinPoissonPair
  field_simp
  ring

private theorem ratio_le {x y q : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hq : 0 ≤ q) (hqxy : q ≤ x * y) :
    y / (y ^ 2 + q) ≤ x / (x ^ 2 + q) := by
  have hy : 0 < y := hx.trans_le hxy
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hqxy)]

/-- A uniform comparison over the entire open zero strip and every
vertical displacement. The condition is on the two abscissae, not on
unknown zero locations or zero correlations. -/
theorem stechkinPoissonPair_comparison {σ τ β c : ℝ}
    (hσ : 1 ≤ σ) (hστ : σ ≤ τ) (hquad : σ ^ 2 ≤ τ * (τ - 1))
    (hβ0 : 0 < β) (hβ1 : β < 1) (hc : c * (2 * τ - 1) ≤ 2 * σ - 1)
    (t : ℝ) : c * stechkinPoissonPair τ β t ≤ stechkinPoissonPair σ β t := by
  let x := σ * (σ - 1) + β * (1 - β) + t ^ 2
  let y := τ * (τ - 1) + β * (1 - β) + t ^ 2
  let q := (2 * β - 1) ^ 2 * t ^ 2
  have hσ0 : 0 ≤ σ := by linarith
  have hp : 0 < β * (1 - β) := mul_pos hβ0 (sub_pos.mpr hβ1)
  have hx : 0 < x := by dsimp [x]; positivity
  have hxy : x ≤ y := by dsimp [x, y]; nlinarith
  have hy : 0 < y := hx.trans_le hxy
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hbase : 0 ≤ σ * (σ - 1) + τ * (τ - 1) - 1 + 6 * β * (1 - β) := by
    nlinarith [sq_nonneg (σ - 1)]
  have hqxy : q ≤ x * y := by
    have hpσ : 0 ≤ σ * (σ - 1) + β * (1 - β) := by positivity
    have hpτ : 0 ≤ τ * (τ - 1) + β * (1 - β) := by nlinarith
    have hi : x * y - q =
        (σ * (σ - 1) + β * (1 - β)) * (τ * (τ - 1) + β * (1 - β)) +
        t ^ 2 * (σ * (σ - 1) + τ * (τ - 1) - 1 + 6 * β * (1 - β)) + t ^ 4 := by
      dsimp [x, y, q]
      ring
    have hh : 0 ≤ x * y - q := by rw [hi]; positivity
    linarith
  have hr := ratio_le hx hxy hq hqxy
  rw [stechkinPoissonPair_eq hσ hβ0 hβ1,
    stechkinPoissonPair_eq (hσ.trans hστ) hβ0 hβ1]
  change c * ((2 * τ - 1) * y / (y ^ 2 + q)) ≤ (2 * σ - 1) * x / (x ^ 2 + q)
  calc
    _ = (c * (2 * τ - 1)) * (y / (y ^ 2 + q)) := by ring
    _ ≤ (2 * σ - 1) * (y / (y ^ 2 + q)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ (2 * σ - 1) * (x / (x ^ 2 + q)) :=
      mul_le_mul_of_nonneg_left hr (by linarith)
    _ = _ := by ring

/-- At the selected zero's ordinate its reflected companion pays the
entire subtracted pair. The original source is left intact. -/
theorem stechkinPoissonPair_source {σ τ β c : ℝ}
    (hσ : 1 ≤ σ) (hστ : σ ≤ τ) (hquad : σ ^ 2 ≤ τ * (τ - 1))
    (hβ0 : 0 < β) (hβ1 : β < 1) (hc : c * (2 * τ - 1) ≤ σ) :
    1 / (σ - β) ≤ stechkinPoissonPair σ β 0 - c * stechkinPoissonPair τ β 0 := by
  have hu : 0 < σ - β := by linarith
  have hv : 0 < σ - 1 + β := by linarith
  have hw : 0 < τ - β := by linarith
  have hz : 0 < τ - 1 + β := by linarith
  have hp : 0 < τ * (τ - 1) + β * (1 - β) := by
    nlinarith [mul_pos hβ0 (sub_pos.mpr hβ1)]
  have hbound : c * (2 * τ - 1) / (τ * (τ - 1) + β * (1 - β)) ≤
      1 / (σ - 1 + β) := by
    apply (div_le_div_iff₀ hp hv).mpr
    have h := mul_le_mul_of_nonneg_right hc hv.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hβ1.le) (show 0 ≤ σ + β by linarith)]
  have he : stechkinPoissonPair σ β 0 - c * stechkinPoissonPair τ β 0 =
      1 / (σ - β) + (1 / (σ - 1 + β) -
        c * (2 * τ - 1) / (τ * (τ - 1) + β * (1 - β))) := by
    unfold stechkinPoissonPair
    simp only [zero_pow (by omega : 2 ≠ 0), add_zero]
    field_simp
    ring
  rw [he]
  linarith

end
end RiemannGaussian
