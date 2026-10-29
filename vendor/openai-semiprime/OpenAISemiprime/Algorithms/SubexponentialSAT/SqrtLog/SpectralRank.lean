import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.SpectralTail

namespace OAI.Algorithms

/-! The exponential binomial window applied to the actual universal matrix.
The field is arbitrary of characteristic different from two, and the number
of slots remains a free parameter. -/

namespace SubexponentialSAT.SqrtLog.Spectral

open Module
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.MatrixSupport SubexponentialSAT.Subexp.TensorSpectrum
open SubexponentialSAT.Subexp.SpectralRank

variable {K : Type*} [Field K] {r Q Δ R : ℕ}

/-- The actual universal swap matrix has small relative rank defect on the
explicit rational-floor interval. No condition bounds the slot count. -/
theorem centered_jointMatrix_rank_relative (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (ε : ℚ)
    (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hε : 0 < ε)
    (hwidth : 32 * ((Q - 1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ) ^ 2) :
    (finrank K (LinearMap.range (LinearMap.id -
      (jointMatrix i t g R (SubexponentialSAT.BinomialInterpolation.extendCoefficients
        (SubexponentialSAT.BinomialInterpolation.parityCoefficients (K := K)
          (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R))).mulVecLin)) : ℚ) ≤
      ε * (Fintype.card (Joint t g i) : ℚ) := by
  have hΔ : (Δ : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  have ht := centered_normalizedTail_le_of_sq ε hr hQ hR hsize hε hwidth
  have hcancel : (ε * (Δ : ℚ)) / (Δ : ℚ) = ε := by field_simp
  have ht' : normalizedTail r (Q - 1) (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R ≤
      (ε * (Δ : ℚ)) / (Δ : ℚ) := by simpa only [hcancel] using ht
  have hb := jointMatrix_parity_rank_relative_of_probability (K := K) h2 t g i
    (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R (ε * (Δ : ℚ)) ht'
  simpa only [hcancel] using hb

/-- A packaged interval interface: the very same A works at every node,
color, and slot, and fits within the available integer weights. -/
theorem exists_centered_rank_interval (h2 : (2 : K) ≠ 0) (ε : ℚ)
    (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hε : 0 < ε)
    (hwidth : 32 * ((Q - 1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ) ^ 2) :
    ∃ A : ℕ, A + R ≤ Q ∧
      ∀ (t : Fin Q) (g : Fin r) (i : Fin Δ),
        (finrank K (LinearMap.range (LinearMap.id -
          (jointMatrix i t g R (SubexponentialSAT.BinomialInterpolation.extendCoefficients
            (SubexponentialSAT.BinomialInterpolation.parityCoefficients (K := K) A R))).mulVecLin)) : ℚ) ≤
          ε * (Fintype.card (Joint t g i) : ℚ) := by
  refine ⟨SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R,
    SubexponentialSAT.Subexp.TailInterval.intervalStart_end_le hr hR hsize, ?_⟩
  intro t g i
  exact centered_jointMatrix_rank_relative h2 t g i ε hr hQ hR hsize hε hwidth

end SubexponentialSAT.SqrtLog.Spectral

end OAI.Algorithms
