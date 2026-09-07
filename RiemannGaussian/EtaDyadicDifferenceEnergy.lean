import RiemannGaussian.EtaDiscreteHardyTransform

/-!
# Full square-energy comparison for the actual dyadic difference

Duplicating each transformed arithmetic cell at its two children doubles
its full square energy exactly. The signed difference therefore has norm
comparable in both directions with universal constants. The exact signed
cross term is retained before either bound is taken.
-/

namespace RiemannGaussian

noncomputable section

/-- The signed dyadic difference at every literal integer cell. -/
def etaDyadicCellDifference (a : ℕ → ℝ) (n : ℕ) : ℝ := a n - a (n / 2)

/-- Each original parent appears at exactly two integer children, giving the full doubled square sum. -/
theorem hasSum_etaDyadicParent_sq {a : ℕ → ℝ} (ha : Summable (fun n ↦ a n ^ 2)) :
    HasSum (fun n : ℕ ↦ a (n / 2) ^ 2) (2 * ∑' n : ℕ, a n ^ 2) := by
  have he : HasSum (fun n : ℕ ↦ a (2 * n / 2) ^ 2) (∑' n : ℕ, a n ^ 2) := by
    simpa using ha.hasSum
  have ho : HasSum (fun n : ℕ ↦ a ((2 * n + 1) / 2) ^ 2) (∑' n : ℕ, a n ^ 2) := by
    simpa [show ∀ n : ℕ, (2 * n + 1) / 2 = n by intro n; omega] using ha.hasSum
  simpa only [two_mul] using HasSum.even_add_odd (f := fun n : ℕ ↦ a (n / 2) ^ 2) he ho

/-- The full signed dyadic cross term is genuinely summable for square-summable original cells. -/
theorem summable_etaDyadicCellCross {a : ℕ → ℝ} (ha : Summable (fun n ↦ a n ^ 2)) :
    Summable (fun n : ℕ ↦ a n * a (n / 2)) := by
  apply (ha.add (hasSum_etaDyadicParent_sq ha).summable).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|a n| - |a (n / 2)|), sq_abs (a n), sq_abs (a (n / 2))]

/-- The complete signed dyadic-difference square sum is genuinely summable. -/
theorem summable_etaDyadicCellDifference_sq {a : ℕ → ℝ} (ha : Summable (fun n ↦ a n ^ 2)) :
    Summable (fun n : ℕ ↦ etaDyadicCellDifference a n ^ 2) := by
  apply ((ha.mul_left 2).add ((hasSum_etaDyadicParent_sq ha).summable.mul_left 2)).of_nonneg_of_le
    (fun _ ↦ sq_nonneg _)
  intro n
  dsimp [etaDyadicCellDifference]
  nlinarith [sq_nonneg (a n + a (n / 2))]

/-- The full difference energy is exactly three times the parent energy minus its full signed parent-child cross moment. -/
theorem tsum_etaDyadicCellDifference_sq_eq_cross {a : ℕ → ℝ} (ha : Summable (fun n ↦ a n ^ 2)) :
    (∑' n : ℕ, etaDyadicCellDifference a n ^ 2) =
      3 * (∑' n : ℕ, a n ^ 2) - 2 * ∑' n : ℕ, a n * a (n / 2) := by
  have hpoint (n : ℕ) : etaDyadicCellDifference a n ^ 2 = a n ^ 2 + a (n / 2) ^ 2 - 2 * (a n * a (n / 2)) := by
    dsimp [etaDyadicCellDifference]
    ring
  simp_rw [hpoint]
  rw [(ha.add (hasSum_etaDyadicParent_sq ha).summable).tsum_sub
      ((summable_etaDyadicCellCross ha).mul_left 2),
    ha.tsum_add (hasSum_etaDyadicParent_sq ha).summable,
    (hasSum_etaDyadicParent_sq ha).tsum_eq,
    (summable_etaDyadicCellCross ha).tsum_mul_left]
  ring

/-- The actual dyadic difference preserves square energy up to universal positive constants in both directions; no arithmetic cancellation is assumed. -/
theorem etaDyadicCellDifferenceEnergy_bounds {a : ℕ → ℝ} (ha : Summable (fun n ↦ a n ^ 2)) :
    (∑' n : ℕ, a n ^ 2) / 6 ≤ ∑' n : ℕ, etaDyadicCellDifference a n ^ 2 ∧
      (∑' n : ℕ, etaDyadicCellDifference a n ^ 2) ≤ 6 * ∑' n : ℕ, a n ^ 2 := by
  have hp := hasSum_etaDyadicParent_sq ha
  have hd := summable_etaDyadicCellDifference_sq ha
  constructor
  · have hpoint (n : ℕ) : a (n / 2) ^ 2 ≤ (3 / 2 : ℝ) * a n ^ 2 + 3 * etaDyadicCellDifference a n ^ 2 := by
      dsimp [etaDyadicCellDifference]
      nlinarith [sq_nonneg (3 * a n - 2 * a (n / 2))]
    have h := hp.summable.tsum_le_tsum hpoint ((ha.mul_left (3 / 2)).add (hd.mul_left 3))
    rw [hp.tsum_eq, (ha.mul_left (3 / 2)).tsum_add (hd.mul_left 3),
      ha.tsum_mul_left, hd.tsum_mul_left] at h
    linarith
  · have hpoint (n : ℕ) : etaDyadicCellDifference a n ^ 2 ≤ 2 * a n ^ 2 + 2 * a (n / 2) ^ 2 := by
      dsimp [etaDyadicCellDifference]
      nlinarith [sq_nonneg (a n + a (n / 2))]
    have h := hd.tsum_le_tsum hpoint ((ha.mul_left 2).add (hp.summable.mul_left 2))
    rw [(ha.mul_left 2).tsum_add (hp.summable.mul_left 2),
      ha.tsum_mul_left, hp.summable.tsum_mul_left, hp.tsum_eq] at h
    linarith

end

end RiemannGaussian
