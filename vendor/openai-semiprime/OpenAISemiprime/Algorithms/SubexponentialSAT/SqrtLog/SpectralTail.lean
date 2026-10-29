import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.SpectralBinomial
import OpenAISemiprime.Algorithms.SubexponentialSAT.Subexp.SpectralRank
import OpenAISemiprime.Algorithms.SubexponentialSAT.Subexp.TailInterval

namespace OAI.Algorithms

/-! Centered integer windows for the actual swap spectrum. The original
rational-floor interval is reused, so the numerical constant is deliberately
loose while the square-root/logarithmic dependence is retained. -/

namespace SubexponentialSAT.SqrtLog.Spectral

open scoped BigOperators
open SubexponentialSAT.SubexpSwapMultiplicity SubexponentialSAT.Subexp.SpectralRank

theorem normalizedTail_cast (r q A R : ℕ) (hr : 0 < r) :
    (normalizedTail r q A R : ℝ) =
      binomialMean (negativeProbability r : ℝ) q
        (fun w => if w ∉ Finset.Ico A (A + R) then 1 else 0) := by
  rw [normalizedTail_eq_binomial r q A R hr]
  unfold binomialMean
  push_cast
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hin : w ∈ Finset.Ico A (A + R)
  · simp [hin]
  · simp only [hin, not_false_eq_true, ite_true, ite_false, mul_one]
    push_cast
    ring

/-- Explicit exponential estimate for the already implemented interval.
The statement is uniform in all colors and every future layout arity. -/
theorem centered_normalizedTail_le_exp {r Q R : ℕ}
    (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q) :
    (normalizedTail r (Q - 1) (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R : ℝ) ≤
      2 * Real.exp (-((R : ℝ) ^ 2) / (32 * (Q - 1 : ℕ))) := by
  rw [normalizedTail_cast r (Q - 1) _ R (by omega)]
  have hprob := negativeProbability_bounds r hr
  have hθ0 : (0 : ℝ) ≤ (negativeProbability r : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ negativeProbability r by linarith [hprob.1])
  have hθ1 : (negativeProbability r : ℝ) ≤ 1 := by
    exact_mod_cast (show negativeProbability r ≤ (1 : ℚ) by linarith [hprob.2])
  have ht := binomial_tail_le (negativeProbability r : ℝ) hθ0 hθ1
    (Q - 1) (by omega) ((R : ℝ) / 4) (by positivity)
    (fun w => w ∉ Finset.Ico (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R)
      (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R + R)) (by
        intro w _ hw
        have hs := SubexponentialSAT.Subexp.TailInterval.intervalStart_deviation hr hR hsize hw
        have hsR : (R : ℝ) ^ 2 ≤ 16 *
            ((w : ℝ) - (Q - 1 : ℕ) * (negativeProbability r : ℝ)) ^ 2 := by
          exact_mod_cast hs
        have ha := abs_nonneg ((w : ℝ) - (Q - 1 : ℕ) * (negativeProbability r : ℝ))
        have he := sq_abs ((w : ℝ) - (Q - 1 : ℕ) * (negativeProbability r : ℝ))
        have hRp : (0 : ℝ) ≤ R := Nat.cast_nonneg R
        nlinarith)
  convert ht using 1 ; congr 2 ; ring

/-- A rational tail budget for the concrete interval, ready for the
audited rank theorem. This is an explicit numerical sufficient condition. -/
theorem centered_normalizedTail_le {r Q R : ℕ} (ε : ℚ)
    (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hbudget : 2 * Real.exp (-((R : ℝ) ^ 2) / (32 * (Q - 1 : ℕ))) ≤ (ε : ℝ)) :
    normalizedTail r (Q - 1) (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R ≤ ε := by
  have ht := (centered_normalizedTail_le_exp hr hQ hR hsize).trans hbudget
  exact_mod_cast ht

/-- A logarithmic square-width test discharges the exponential budget. -/
theorem exp_budget_of_sq {q R : ℕ} (hq : 0 < q) {ε : ℝ} (hε : 0 < ε)
    (hwidth : 32 * (q : ℝ) * Real.log (2 / ε) ≤ (R : ℝ) ^ 2) :
    2 * Real.exp (-((R : ℝ) ^ 2) / (32 * q)) ≤ ε := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hden : (0 : ℝ) < 32 * q := by positivity
  have hx : -((R : ℝ) ^ 2) / (32 * q) ≤ -Real.log (2 / ε) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have he := Real.exp_le_exp.mpr hx
  have hlog : Real.exp (-Real.log (2 / ε)) = ε / 2 := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  rw [hlog] at he
  linarith

theorem centered_normalizedTail_le_of_sq {r Q R : ℕ} (ε : ℚ)
    (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hε : 0 < ε)
    (hwidth : 32 * ((Q - 1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ) ^ 2) :
    normalizedTail r (Q - 1) (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R ≤ ε := by
  apply centered_normalizedTail_le ε hr hQ hR hsize
  exact exp_budget_of_sq (by omega) (by exact_mod_cast hε) hwidth

end SubexponentialSAT.SqrtLog.Spectral

end OAI.Algorithms
