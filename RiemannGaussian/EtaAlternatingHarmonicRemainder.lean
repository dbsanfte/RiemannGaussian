import RiemannGaussian.EtaMoebiusArithmeticSums
import RiemannGaussian.EtaDivisorParityGcd

/-!
# Exact parity and amplitude of the alternating harmonic remainder

The harmonic remainder is kept as its original parity sign times a
positive integral. The integral has a uniform explicit first-order
approximation. This supplies the amplitude information needed before
applying the existing quotient-parity sampling estimates to the actual
arithmetic residual; it does not assert the missing mean-square decay.
-/

open MeasureTheory Set

namespace RiemannGaussian

noncomputable section

/-- The positive amplitude of the exact alternating harmonic remainder. -/
def etaAlternatingHarmonicAmplitude (L : ℕ) : ℝ :=
  ∫ x : ℝ in (0 : ℝ)..1, x ^ L / (1 + x)

/-- The exact harmonic amplitude integrand is integrable on its full unit interval. -/
theorem intervalIntegrable_etaAlternatingHarmonicAmplitude (L : ℕ) :
    IntervalIntegrable (fun x : ℝ ↦ x ^ L / (1 + x)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  apply (continuous_id.pow L).continuousOn.div (continuous_const.add continuous_id).continuousOn
  intro x hx
  have hx0 : 0 ≤ x := by simpa using hx.1
  change 1 + x ≠ 0
  linarith

/-- The zeroth exact remainder amplitude is the original logarithmic constant. -/
theorem etaAlternatingHarmonicAmplitude_zero : etaAlternatingHarmonicAmplitude 0 = Real.log 2 := by
  unfold etaAlternatingHarmonicAmplitude
  simp only [pow_zero]
  rw [intervalIntegral.integral_comp_add_left (fun x : ℝ ↦ 1 / x) 1]
  norm_num [integral_one_div_of_pos]

/-- Adjacent positive remainder amplitudes add to the exact reciprocal endpoint. -/
theorem etaAlternatingHarmonicAmplitude_add_succ (L : ℕ) :
    etaAlternatingHarmonicAmplitude L + etaAlternatingHarmonicAmplitude (L + 1) = 1 / (L + 1 : ℝ) := by
  rw [etaAlternatingHarmonicAmplitude, etaAlternatingHarmonicAmplitude,
    ← intervalIntegral.integral_add (intervalIntegrable_etaAlternatingHarmonicAmplitude L)
      (intervalIntegrable_etaAlternatingHarmonicAmplitude (L + 1))]
  calc
    _ = ∫ x : ℝ in (0 : ℝ)..1, x ^ L := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx0 : 0 ≤ x := by simpa using hx.1
      have hp : 1 + x ≠ 0 := by linarith
      dsimp only
      rw [pow_succ]
      field_simp
    _ = _ := by rw [integral_pow]; simp

private theorem eta_sign_succ (L : ℕ) :
    (pairedEtaDirichletSign (L + 1) : ℝ) = -(pairedEtaDirichletSign L : ℝ) := by
  have h := pairedEtaDirichletSign_add_eq_neg_mul L 1
  norm_num [pairedEtaDirichletSign] at h
  exact_mod_cast h

/-- The original alternating harmonic remainder is exactly its original parity sign times its positive integral amplitude, including the empty prefix. -/
theorem pairedEtaArithmeticHarmonicPrefix_sub_log_two (L : ℕ) :
    pairedEtaArithmeticHarmonicPrefix L - Real.log 2 =
      (pairedEtaDirichletSign L : ℝ) * etaAlternatingHarmonicAmplitude L := by
  induction L with
  | zero => simp [pairedEtaArithmeticHarmonicPrefix, pairedEtaDirichletSign, etaAlternatingHarmonicAmplitude_zero]
  | succ L ih =>
    have hs : pairedEtaArithmeticHarmonicPrefix (L + 1) = pairedEtaArithmeticHarmonicPrefix L +
        (pairedEtaDirichletSign (L + 1) : ℝ) / (L + 1 : ℝ) := by
      simp only [pairedEtaArithmeticHarmonicPrefix, Finset.sum_Icc_succ_top (by omega : 1 ≤ L + 1),
        Nat.cast_add, Nat.cast_one]
    rw [hs, eta_sign_succ]
    calc
      _ = (pairedEtaArithmeticHarmonicPrefix L - Real.log 2) -
          (pairedEtaDirichletSign L : ℝ) * (1 / (L + 1 : ℝ)) := by ring
      _ = _ := by rw [ih, ← etaAlternatingHarmonicAmplitude_add_succ]; ring

/-- The exact positive remainder amplitude has a uniform first-order approximation with an explicit inverse-square error, including the empty prefix. -/
theorem etaAlternatingHarmonicAmplitude_bounds (L : ℕ) :
    1 / (2 * (L + 1 : ℝ)) ≤ etaAlternatingHarmonicAmplitude L ∧
      etaAlternatingHarmonicAmplitude L ≤ 1 / (2 * (L + 1 : ℝ)) +
        1 / (2 * (L + 1 : ℝ) * (L + 2 : ℝ)) := by
  have hpoly : IntervalIntegrable (fun x : ℝ ↦ x ^ L) volume 0 1 :=
    (continuous_id.pow L).intervalIntegrable _ _
  have hpoly' : IntervalIntegrable (fun x : ℝ ↦ x ^ (L + 1)) volume 0 1 :=
    (continuous_id.pow (L + 1)).intervalIntegrable _ _
  have hlow : (∫ x : ℝ in (0 : ℝ)..1, x ^ L / 2) = 1 / (2 * (L + 1 : ℝ)) := by
    rw [intervalIntegral.integral_div, integral_pow]
    simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
    field_simp
  have hupp : (∫ x : ℝ in (0 : ℝ)..1, x ^ L - x ^ (L + 1) / 2) =
      1 / (2 * (L + 1 : ℝ)) + 1 / (2 * (L + 1 : ℝ) * (L + 2 : ℝ)) := by
    rw [intervalIntegral.integral_sub hpoly (hpoly'.div_const 2),
      intervalIntegral.integral_div, integral_pow, integral_pow]
    simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero, Nat.cast_add, Nat.cast_one,
      add_assoc, one_add_one_eq_two]
    field_simp
    ring
  constructor
  · rw [← hlow]
    apply intervalIntegral.integral_mono_on (by norm_num) (hpoly.div_const 2)
      (intervalIntegrable_etaAlternatingHarmonicAmplitude L)
    intro x hx
    exact div_le_div_of_nonneg_left (pow_nonneg hx.1 _) (by linarith [hx.1] : 0 < 1 + x) (by linarith [hx.2])
  · rw [← hupp]
    apply intervalIntegral.integral_mono_on (by norm_num) (intervalIntegrable_etaAlternatingHarmonicAmplitude L)
      (hpoly.sub (hpoly'.div_const 2))
    intro x hx
    have hp : 0 < 1 + x := by linarith [hx.1]
    have hq : 1 / (1 + x) ≤ 1 - x / 2 := by
      apply (div_le_iff₀ hp).mpr
      nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
    have h := mul_le_mul_of_nonneg_left hq (pow_nonneg hx.1 L)
    calc
      _ = x ^ L * (1 / (1 + x)) := by ring
      _ ≤ x ^ L * (1 - x / 2) := h
      _ = _ := by rw [pow_succ]; ring

/-- At every positive physical cell and divisor, the exact quotient remainder has a common leading amplitude and an explicit error uniform in both indices. -/
theorem etaAlternatingHarmonicAmplitude_quotient_error_le {L n : ℕ}
    (hL : 0 < L) (hn : 0 < n) :
    |etaAlternatingHarmonicAmplitude (L / n) / n - 1 / (2 * (L : ℝ))| ≤
      n / (2 * (L : ℝ) ^ 2) := by
  let q : ℝ := (L / n : ℕ) + 1
  let T : ℝ := n * q
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : 0 < q := by dsimp [q]; positivity
  have hTp : 0 < T := mul_pos hnp hq
  have hprod : L / n * n ≤ L := Nat.div_mul_le_self L n
  have hrem : L % n < n := Nat.mod_lt L hn
  have heq := Nat.div_add_mod L n
  rw [Nat.mul_comm n (L / n)] at heq
  have hnext : L ≤ L / n * n + n := by omega
  have hlow : (L : ℝ) ≤ T := by
    have hh : (L : ℝ) ≤ (L / n : ℕ) * (n : ℝ) + n := by exact_mod_cast hnext
    dsimp [T, q]
    nlinarith
  have hupp : T ≤ L + n := by
    have hh : ((L / n : ℕ) : ℝ) * n ≤ L := by exact_mod_cast hprod
    dsimp [T, q]
    nlinarith
  have hb := etaAlternatingHarmonicAmplitude_bounds (L / n)
  have hbase : 1 / (2 * T) ≤ etaAlternatingHarmonicAmplitude (L / n) / n := by
    calc
      _ = (1 / (2 * q)) / n := by dsimp [T]; field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hb.1 hnp.le
  have htop : etaAlternatingHarmonicAmplitude (L / n) / n ≤
      1 / (2 * T) + n / (2 * T * (T + n)) := by
    calc
      _ ≤ (1 / (2 * q) + 1 / (2 * q * (q + 1))) / n := by
        simpa only [q, add_assoc, one_add_one_eq_two] using div_le_div_of_nonneg_right hb.2 hnp.le
      _ = _ := by dsimp [T]; field_simp
  have hbase_le : 1 / (2 * T) ≤ 1 / (2 * (L : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hbase_error : 1 / (2 * (L : ℝ)) - 1 / (2 * T) ≤ n / (2 * (L : ℝ) ^ 2) := by
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hupp hLp.le, mul_nonneg hnp.le (sub_nonneg.mpr hlow)]
  have htop_error : (n : ℝ) / (2 * T * (T + n)) ≤ n / (2 * (L : ℝ) ^ 2) := by
    apply div_le_div_of_nonneg_left hnp.le (by positivity)
    nlinarith [pow_le_pow_left₀ hLp.le hlow 2, mul_nonneg hTp.le hnp.le]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end

end RiemannGaussian
