import RiemannGaussian.MontgomeryVaughan.Final
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteGaussianGram

/-!
# Montgomery--Vaughan bounds for finite eta endpoint frequencies

The literal eta Dirichlet atoms use the logarithmic frequencies
`k ↦ log (k + 1)`.  This module proves a uniform admissible gap `1 / K` for
the first `K` such frequencies and specializes the checked bilinear
Montgomery--Vaughan inequality to that finite family.

This is a frequency-side estimate.  It does not identify the current
zero-pair endpoint ledger with a Hilbert kernel; that analytic/arithmetic
bridge remains a separate obligation.
-/

noncomputable section

open Complex Finset
open scoped BigOperators ComplexConjugate

namespace RiemannGaussian

/-- The constant gap weight `1 / K` for the first `K` logarithmic eta
frequencies. -/
def pairedEtaFiniteLogGap (K : ℕ) (_ : Fin K) : ℝ := (K : ℝ)⁻¹

/-- If `0 < a < b ≤ K`, then the logarithmic separation between `a` and `b`
is at least `1 / K`. -/
lemma inv_natCast_le_log_natCast_sub_log_natCast {a b K : ℕ}
    (ha : 0 < a) (hab : a < b) (hbK : b ≤ K) :
    (K : ℝ)⁻¹ ≤ Real.log (b : ℝ) - Real.log (a : ℝ) := by
  have haReal : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbNat : 0 < b := ha.trans hab
  have hbReal : 0 < (b : ℝ) := by exact_mod_cast hbNat
  have hKReal : 0 < (K : ℝ) := by
    exact_mod_cast hbNat.trans_le hbK
  have hbKReal : (b : ℝ) ≤ (K : ℝ) := by exact_mod_cast hbK
  have hInvK : (K : ℝ)⁻¹ ≤ (b : ℝ)⁻¹ :=
    (inv_le_inv₀ hKReal hbReal).2 hbKReal
  have hGapReal : (1 : ℝ) ≤ (b : ℝ) - (a : ℝ) := by
    have habReal : (a : ℝ) + 1 ≤ (b : ℝ) := by
      exact_mod_cast (Nat.add_one_le_iff.mpr hab)
    linarith
  have hInvB : (b : ℝ)⁻¹ ≤ 1 - (a : ℝ) / (b : ℝ) := by
    rw [show 1 - (a : ℝ) / (b : ℝ) = ((b : ℝ) - (a : ℝ)) / (b : ℝ) by
      field_simp]
    rw [inv_eq_one_div]
    exact (div_le_div_iff_of_pos_right hbReal).2 hGapReal
  have hLog := Real.one_sub_inv_le_log_of_pos (div_pos hbReal haReal)
  have hInvDiv : ((b : ℝ) / (a : ℝ))⁻¹ = (a : ℝ) / (b : ℝ) := by
    field_simp
  rw [hInvDiv, Real.log_div hbReal.ne' haReal.ne'] at hLog
  exact hInvK.trans (hInvB.trans hLog)

/-- The eta logarithmic frequency is injective on every finite prefix. -/
lemma pairedEtaLogFrequency_fin_injective (K : ℕ) :
    Function.Injective (fun r : Fin K => pairedEtaLogFrequency r.val) := by
  intro r s hrs
  apply Fin.ext
  have hrPos : 0 < (((r.val + 1 : ℕ) : ℝ)) := by positivity
  have hsPos : 0 < (((s.val + 1 : ℕ) : ℝ)) := by positivity
  have hrs' : Real.log (((r.val + 1 : ℕ) : ℝ)) =
      Real.log (((s.val + 1 : ℕ) : ℝ)) := by
    simpa [pairedEtaLogFrequency, Nat.cast_add, Nat.cast_one] using hrs
  have hCast : (((r.val + 1 : ℕ) : ℝ)) = (((s.val + 1 : ℕ) : ℝ)) := by
    calc
      (((r.val + 1 : ℕ) : ℝ)) = Real.exp (Real.log (((r.val + 1 : ℕ) : ℝ))) :=
        (Real.exp_log hrPos).symm
      _ = Real.exp (Real.log (((s.val + 1 : ℕ) : ℝ))) := by
        exact congrArg Real.exp hrs'
      _ = (((s.val + 1 : ℕ) : ℝ)) := Real.exp_log hsPos
  exact_mod_cast Nat.add_right_cancel (by exact_mod_cast hCast)

/-- Distinct frequencies in the first `K` eta atoms are separated by at
least `1 / K`. -/
lemma pairedEtaFiniteLogGap_le_abs_sub {K : ℕ} (r s : Fin K) (hrs : r ≠ s) :
    pairedEtaFiniteLogGap K r ≤
      |pairedEtaLogFrequency r.val - pairedEtaLogFrequency s.val| := by
  have hrsVal : r.val ≠ s.val := fun h => hrs (Fin.ext h)
  rcases lt_or_gt_of_ne hrsVal with hrsLt | hsrLt
  · have hLog := inv_natCast_le_log_natCast_sub_log_natCast
      (a := r.val + 1) (b := s.val + 1) (K := K) (by omega) (by omega) (by omega)
    have hLe : pairedEtaLogFrequency r.val ≤ pairedEtaLogFrequency s.val := by
      unfold pairedEtaLogFrequency
      apply Real.log_le_log
      · positivity
      · exact_mod_cast (Nat.add_le_add_right (Nat.le_of_lt hrsLt) 1)
    rw [abs_of_nonpos (sub_nonpos.mpr hLe), neg_sub]
    simpa [pairedEtaFiniteLogGap, pairedEtaLogFrequency] using hLog
  · have hLog := inv_natCast_le_log_natCast_sub_log_natCast
      (a := s.val + 1) (b := r.val + 1) (K := K) (by omega) (by omega) (by omega)
    have hLe : pairedEtaLogFrequency s.val ≤ pairedEtaLogFrequency r.val := by
      unfold pairedEtaLogFrequency
      apply Real.log_le_log
      · positivity
      · exact_mod_cast (Nat.add_le_add_right (Nat.le_of_lt hsrLt) 1)
    rw [abs_of_nonneg (sub_nonneg.mpr hLe)]
    simpa [pairedEtaFiniteLogGap, pairedEtaLogFrequency] using hLog

/-- The finite eta logarithmic frequencies with the constant weight `1 / K`
form an admissible Montgomery--Vaughan family. -/
theorem pairedEtaFiniteLog_admissible {K : ℕ} (hK : 0 < K) :
    MontgomeryVaughan.Adm
      (fun r : Fin K => pairedEtaLogFrequency r.val)
      (pairedEtaFiniteLogGap K) := by
  refine ⟨pairedEtaLogFrequency_fin_injective K, ?_, ?_⟩
  · intro r
    unfold pairedEtaFiniteLogGap
    positivity
  · intro r s hrs
    exact pairedEtaFiniteLogGap_le_abs_sub r s hrs

/-- The bilinear Montgomery--Vaughan inequality with explicit constant `26`
for the first `K` literal eta logarithmic frequencies. -/
theorem pairedEtaFiniteLog_mvHilbert_twentySix {K : ℕ} (hK : 0 < K)
    (x z : Fin K → ℂ) :
    ‖∑ r, ∑ s, if r = s then (0 : ℂ)
        else x r * conj (z s) /
          ((pairedEtaLogFrequency r.val - pairedEtaLogFrequency s.val : ℝ) : ℂ)‖
      ≤ 26 * Real.sqrt ((K : ℝ) * ∑ r, ‖x r‖ ^ 2) *
          Real.sqrt ((K : ℝ) * ∑ r, ‖z r‖ ^ 2) := by
  have hadm := pairedEtaFiniteLog_admissible hK
  have hmv := MontgomeryVaughan.mvHilbert_twentySix (Fin K)
    (fun r : Fin K => pairedEtaLogFrequency r.val)
    (pairedEtaFiniteLogGap K) x z hadm.inj hadm.pos hadm.le
  have hx : (∑ r, ‖x r‖ ^ 2 / pairedEtaFiniteLogGap K r) =
      (K : ℝ) * ∑ r, ‖x r‖ ^ 2 := by
    simp only [pairedEtaFiniteLogGap, div_eq_mul_inv, inv_inv]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hz : (∑ r, ‖z r‖ ^ 2 / pairedEtaFiniteLogGap K r) =
      (K : ℝ) * ∑ r, ‖z r‖ ^ 2 := by
    simp only [pairedEtaFiniteLogGap, div_eq_mul_inv, inv_inv]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [hx, hz] at hmv
  exact hmv

end RiemannGaussian

end
