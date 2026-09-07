import RiemannGaussian.EtaMoebiusTrialRefinement
import RiemannGaussian.EtaMoebiusTrialPenalty

/-!
# Vanishing full grid-refinement error for the exact Möbius candidates

Keep the original stage arithmetic cutoff `M_k=k+1` and logarithmic
weights while refining the `2^k` physical grid by any positive integer
factor. The entire critical square change is at most
`32*sqrt(2*(k+1)^5/2^k)` for `k≥7`, uniformly in that factor, and this
allowance tends to zero. Approximation of the target by the arithmetic
family, and decay of the canonical deficit, remain separate open targets.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The generic physical-grid combination is exactly the original dyadic Möbius candidate. -/
theorem pairedEtaMoebiusTrialGridCombination_eq_dyadic (k : ℕ) (t : ℝ) :
    pairedEtaMoebiusTrialGridCombination (pairedEtaDyadicTranslateDimension k) (k + 1)
      (pairedEtaMoebiusTrialLogWeight (k + 1)) t =
        pairedEtaTranslatedCombination (pairedEtaDyadicTranslate k)
          (fun j ↦ (pairedEtaDyadicMoebiusTrialCoefficient k j : ℂ)) t := by
  unfold pairedEtaMoebiusTrialGridCombination pairedEtaDyadicMoebiusTrialCoefficient
  congr 1
  funext j
  rw [pairedEtaMoebiusTrialGridPoint_eq_neg_log (by omega) (by omega)]
  simp only [pairedEtaDyadicTranslate, Nat.cast_add, Nat.cast_one]

/-- The entire change in the actual stage candidate under an arbitrary positive integer grid refinement. -/
def pairedEtaDyadicMoebiusTrialRefinementError (k q : ℕ) : ℝ :=
  pairedEtaMoebiusTrialRefinementError (pairedEtaDyadicTranslateDimension k) (k + 1) (q + 1)
    (pairedEtaMoebiusTrialLogWeight (k + 1))

/-- A full critical-square refinement allowance independent of the refinement factor. -/
def pairedEtaDyadicMoebiusTrialRefinementAllowance (k : ℕ) : ℝ :=
  32 * Real.sqrt (2 * (k + 1 : ℝ) ^ 5 / (2 : ℝ) ^ k)

/-- Every stage from seven onward meets the actual support-mismatch small-displacement condition. -/
theorem pairedEtaDyadicMoebiusTrialGrid_small {k : ℕ} (hk : 7 ≤ k) :
    2 * (k + 1 : ℝ) / pairedEtaDyadicTranslateDimension k ≤ 1 / 8 := by
  have hnat : 16 * (k + 1) ≤ 2 ^ k := by
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih => rw [pow_succ]; omega
  have hreal : 16 * (k + 1 : ℝ) ≤ pairedEtaDyadicTranslateDimension k := by
    exact_mod_cast hnat
  apply (div_le_iff₀ (show (0 : ℝ) < pairedEtaDyadicTranslateDimension k by
    exact_mod_cast pairedEtaDyadicTranslateDimension_pos k)).mpr
  nlinarith

/-- The original candidate's complete refinement error has a proved bound for every stage and every refinement beyond the explicit threshold. -/
theorem pairedEtaDyadicMoebiusTrialRefinementError_le {k : ℕ} (hk : 7 ≤ k) (q : ℕ) :
    pairedEtaDyadicMoebiusTrialRefinementError k q ≤ pairedEtaDyadicMoebiusTrialRefinementAllowance k := by
  have h := pairedEtaMoebiusTrialRefinementError_le
    (pairedEtaDyadicTranslateDimension_pos k) (pairedEtaDyadicMoebiusTrial_cutoff_le_dimension k)
    (Nat.succ_pos q) (fun _ hn ↦ abs_pairedEtaMoebiusTrialLogWeight_le hn)
    (by simpa only [Nat.cast_add, Nat.cast_one] using pairedEtaDyadicMoebiusTrialGrid_small hk)
  apply h.trans_eq
  unfold pairedEtaDyadicTranslateDimension pairedEtaDyadicMoebiusTrialRefinementAllowance
  push_cast
  have he := Real.sqrt_mul (sq_nonneg ((k + 1 : ℝ) ^ 2)) (2 * (k + 1 : ℝ) / (2 : ℝ) ^ k)
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)] at he
  rw [mul_assoc, ← he]
  congr 1
  congr 1
  ring

/-- The full critical-square refinement allowance tends to zero along the unchanged dyadic stages. -/
theorem pairedEtaDyadicMoebiusTrialRefinementAllowance_tendsto_zero :
    Tendsto pairedEtaDyadicMoebiusTrialRefinementAllowance atTop (𝓝 0) := by
  have h := ((tendsto_pow_const_div_const_pow_of_one_lt 5 (by norm_num : (1 : ℝ) < 2)).comp
    (tendsto_add_atTop_nat 1)).const_mul (2 : ℝ)
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, mul_zero] at h
  have hpoly : Tendsto (fun k : ℕ ↦ (k + 1 : ℝ) ^ 5 / (2 : ℝ) ^ k) atTop (𝓝 0) := by
    convert h using 1
    ext k
    rw [pow_succ]
    ring
  have htwice : Tendsto (fun k : ℕ ↦ 2 * ((k + 1 : ℝ) ^ 5 / (2 : ℝ) ^ k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpoly.const_mul (2 : ℝ)
  have hroot := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp htwice
  have hresult := hroot.const_mul (32 : ℝ)
  change Tendsto (fun k : ℕ ↦ 32 * Real.sqrt (2 * (k + 1 : ℝ) ^ 5 / (2 : ℝ) ^ k)) atTop (𝓝 0)
  simpa only [Function.comp_apply, mul_div_assoc,
    mul_zero, Real.sqrt_zero] using hresult

/-- A single stage threshold controls every positive integer refinement of the actual candidate. -/
theorem pairedEtaDyadicMoebiusTrialRefinementError_le_eventually :
    ∀ᶠ k : ℕ in atTop, ∀ q : ℕ,
      pairedEtaDyadicMoebiusTrialRefinementError k q ≤ pairedEtaDyadicMoebiusTrialRefinementAllowance k := by
  filter_upwards [eventually_ge_atTop 7] with k hk q
  exact pairedEtaDyadicMoebiusTrialRefinementError_le hk q

/-- The complete actual grid-refinement error tends to zero for every refinement schedule, with the arithmetic cutoff and logarithmic weights fixed at each stage. -/
theorem pairedEtaDyadicMoebiusTrialRefinementError_tendsto_zero (q : ℕ → ℕ) :
    Tendsto (fun k ↦ pairedEtaDyadicMoebiusTrialRefinementError k (q k)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun k ↦ pairedEtaMoebiusTrialRefinementError_nonneg _ _ _ _)
    _ pairedEtaDyadicMoebiusTrialRefinementAllowance_tendsto_zero
  filter_upwards [pairedEtaDyadicMoebiusTrialRefinementError_le_eventually] with k hk
  exact hk (q k)

end

end RiemannGaussian
