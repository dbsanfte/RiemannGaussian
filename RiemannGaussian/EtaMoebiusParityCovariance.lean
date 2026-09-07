import RiemannGaussian.EtaMoebiusExteriorParityEnergy

/-!
# The signed covariance of the actual parity differences

The discrete derivative is kept on the parity waves before expanding the
square. Every resulting covariance is integrated over the requested
physical interval with its original inverse-square weight. This is the
actual short-window kernel, not a complete-period gcd replacement; the
arithmetic estimate on this matrix remains open.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The exact difference of two adjacent integer parity waves occurring after summation by parts. -/
def etaUnitIntervalParityJump (m : ℕ) (z : ℝ) : ℝ :=
  etaUnitIntervalParity ((m + 2 : ℝ) * z) - etaUnitIntervalParity ((m + 1 : ℝ) * z)

/-- Adjacent parity differences are measurable, with their original endpoint convention retained. -/
theorem measurable_etaUnitIntervalParityJump (m : ℕ) : Measurable (etaUnitIntervalParityJump m) := by
  have hm (n : ℝ) : Measurable (fun z : ℝ ↦ etaUnitIntervalParity (n * z)) :=
    measurable_const.sub (measurable_const.mul
      (measurable_etaUnitIntervalColour.comp (measurable_const.mul measurable_id)))
  exact (hm _).sub (hm _)

/-- The actual parity difference is bounded by two; no estimate of its signed covariance follows from this envelope alone. -/
theorem abs_etaUnitIntervalParityJump_le (m : ℕ) (z : ℝ) : |etaUnitIntervalParityJump m z| ≤ 2 := by
  have h := abs_sub (etaUnitIntervalParity ((m + 2 : ℝ) * z))
    (etaUnitIntervalParity ((m + 1 : ℝ) * z))
  simpa only [etaUnitIntervalParityJump, abs_etaUnitIntervalParity, one_add_one_eq_two] using h

/-- The unchanged signed short-window covariance kernel after transferring both discrete derivatives onto their parity waves. -/
def pairedEtaParityJumpCovariance (a b : ℝ) (m n : ℕ) : ℝ :=
  ∫ z : ℝ in Ioc a b, etaUnitIntervalParityJump m z * etaUnitIntervalParityJump n z / z ^ 2

/-- Every signed covariance entry is genuinely integrable on the specified physical interval above zero. -/
theorem integrableOn_pairedEtaParityJumpCovariance {a : ℝ} (ha : 0 < a) (b : ℝ) (m n : ℕ) :
    IntegrableOn (fun z : ℝ ↦ etaUnitIntervalParityJump m z * etaUnitIntervalParityJump n z / z ^ 2)
      (Ioc a b) := by
  have hi : IntegrableOn (fun z : ℝ ↦ 1 / z ^ 2) (Ioi a) := by
    apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.rpow_neg (ha.trans hz).le, Real.rpow_two, one_div]
  have hb := (hi.mono_set (show Ioc a b ⊆ Ioi a from Ioc_subset_Ioi_self)).mul_bdd
    ((measurable_etaUnitIntervalParityJump m).mul (measurable_etaUnitIntervalParityJump n)).aestronglyMeasurable
    (Eventually.of_forall fun z ↦ by
      dsimp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (abs_etaUnitIntervalParityJump_le m z) (abs_etaUnitIntervalParityJump_le n z)
        (abs_nonneg _) (by norm_num))
  apply hb.congr
  exact Eventually.of_forall fun z ↦ by dsimp only [Pi.mul_apply]; ring

/-- The covariance kernel retains its exact symmetry on every physical interval. -/
theorem pairedEtaParityJumpCovariance_symm (a b : ℝ) (m n : ℕ) :
    pairedEtaParityJumpCovariance a b m n = pairedEtaParityJumpCovariance a b n m := by
  unfold pairedEtaParityJumpCovariance
  congr 1
  funext z
  ring

/-- The actual parity energy equals the complete signed covariance form of the original Möbius primitive, with all cross terms on the original short interval included. -/
theorem integral_pairedEtaMoebiusGridParitySum_sq_eq_covariance {d M : ℕ} (hMd : M ≤ d)
    (w : ℕ → ℝ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (∫ z : ℝ in Ioc a b, pairedEtaMoebiusGridParitySum d M w z ^ 2 / z ^ 2) =
      ∑ m ∈ Finset.range (d - 1), ∑ n ∈ Finset.range (d - 1),
        pairedEtaMoebiusTrialPrimitive M w ((d : ℝ) / (m + 2 : ℝ)) *
        pairedEtaMoebiusTrialPrimitive M w ((d : ℝ) / (n + 2 : ℝ)) *
        pairedEtaParityJumpCovariance a b m n := by
  let P := fun m : ℕ ↦ pairedEtaMoebiusTrialPrimitive M w ((d : ℝ) / (m + 2 : ℝ))
  have hp (z : ℝ) : pairedEtaMoebiusGridParitySum d M w z ^ 2 / z ^ 2 =
      ∑ m ∈ Finset.range (d - 1), ∑ n ∈ Finset.range (d - 1),
        (P m * P n) * (etaUnitIntervalParityJump m z * etaUnitIntervalParityJump n z / z ^ 2) := by
    rw [pairedEtaMoebiusGridParitySum_eq_primitive_differences hMd w z, pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [P, etaUnitIntervalParityJump]
    ring
  have hi (m n : ℕ) := (integrableOn_pairedEtaParityJumpCovariance ha b m n).const_mul (P m * P n)
  simp_rw [hp]
  rw [integral_finsetSum _ (fun m _ ↦ integrable_finsetSum _ (fun n _ ↦ hi m n))]
  apply Finset.sum_congr rfl
  intro m _
  rw [integral_finsetSum _ (fun n _ ↦ hi m n)]
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_const_mul]
  rfl

end

end RiemannGaussian
