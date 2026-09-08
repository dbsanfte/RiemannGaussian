import RiemannGaussian.EtaGammaDampedMoebius

/-!
# Positive physical averages of the original Mobius carrier

Discrete Abel summation and complete quotient fibres identify gamma
smoothing with a positive average of the literal completed eta prefixes.
All series are summable and the infinite boundary is discharged. The
selected original low family has a cubic scale allowance. The full high
family equals the exact source minus that low average; both dyadic source
endpoints are retained. An independent high-family upper bound remains open.
-/

open Complex Filter MeasureTheory Set
open scoped Classical Topology Interval ArithmeticFunction.Moebius

namespace RiemannGaussian.EtaGammaSmoothing

noncomputable section

/-- The physical survival function decreases because its derivative is minus a positive density. -/
theorem antitone_gammaSurvival : Antitone gammaSurvival :=
  antitone_of_hasDerivAt_nonpos hasDerivAt_gammaSurvival (fun t ↦ neg_nonpos.mpr (gammaDensity_nonneg t))

/-- The source survival correction has an explicit cubic allowance, including the first physical endpoint. -/
theorem abs_gammaSurvival_sub_one_le {x : ℝ} (hx : 0 ≤ x) :
    |gammaSurvival x - 1| ≤ x ^ 3 / 6 := by
  have hc : Continuous gammaDensity := by unfold gammaDensity; fun_prop
  have hi : gammaSurvival x - 1 = ∫ t in (0 : ℝ)..x, -gammaDensity t := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hasDerivAt_gammaSurvival t) (hc.neg.intervalIntegrable 0 x)]
    norm_num [gammaSurvival]
  rw [hi, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ t in (0 : ℝ)..x, t ^ 2 / 2 := by
      apply intervalIntegral.norm_integral_le_of_norm_le hx
      · exact Eventually.of_forall fun t ht ↦ by
          rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (gammaDensity_nonneg t), gammaDensity]
          have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
          nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg t)]
      · exact ((continuous_id.pow 2).div_const 2).intervalIntegrable 0 x
    _ = _ := by rw [intervalIntegral.integral_div, integral_pow]; norm_num; ring

/-- The discrete physical weight is the exact mass between consecutive physical integers. -/
def gammaPhysicalWeight (x : ℝ) (M : ℕ) : ℝ :=
  gammaSurvival ((M : ℝ) * x) - gammaSurvival ((M + 1 : ℝ) * x)

/-- Each discrete physical weight is the literal integral of the positive gamma density over its physical interval. -/
theorem gammaPhysicalWeight_eq_integral (x : ℝ) (M : ℕ) :
    gammaPhysicalWeight x M =
      ∫ t in ((M : ℝ) * x)..((M + 1 : ℝ) * x), gammaDensity t := by
  have hc : Continuous gammaDensity := by unfold gammaDensity; fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_gammaSurvival t)
    (hc.neg.intervalIntegrable ((M : ℝ) * x) ((M + 1 : ℝ) * x))
  rw [intervalIntegral.integral_neg] at hi
  dsimp only [gammaPhysicalWeight]
  linarith

/-- Every physical weight is nonnegative and bounded by its original survival coefficient. -/
theorem gammaPhysicalWeight_bounds {x : ℝ} (hx : 0 ≤ x) (M : ℕ) :
    0 ≤ gammaPhysicalWeight x M ∧ gammaPhysicalWeight x M ≤ gammaSurvival ((M : ℝ) * x) := by
  constructor
  · exact sub_nonneg.mpr (antitone_gammaSurvival (by nlinarith : (M : ℝ) * x ≤ (M + 1 : ℝ) * x))
  · exact sub_le_self _ (gammaSurvival_nonneg (by positivity))

/-- The complete finite physical mass retains its upper survival endpoint exactly. -/
theorem sum_gammaPhysicalWeight (x : ℝ) (N : ℕ) :
    ∑ M ∈ Finset.range N, gammaPhysicalWeight x M = 1 - gammaSurvival ((N : ℝ) * x) := by
  induction N with
  | zero => norm_num [gammaSurvival]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, gammaPhysicalWeight]
    push_cast
    ring

/-- All positive physical weights form a genuinely summable probability mass function. -/
theorem hasSum_gammaPhysicalWeight {x : ℝ} (hx : 0 < x) :
    HasSum (gammaPhysicalWeight x) 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun M ↦ (gammaPhysicalWeight_bounds hx.le M).1) 1).mpr
  simp only [sum_gammaPhysicalWeight]
  simpa only [sub_zero] using
    (summable_gammaSurvival_nat_mul hx).tendsto_atTop_zero.const_sub 1

/-- A bounded complex carrier is absolutely integrable against the unchanged positive physical weights. -/
theorem summable_gammaPhysicalWeight_mul {x : ℝ} (hx : 0 < x) {F : ℕ → ℂ}
    {B : ℝ} (hF : ∀ M, ‖F M‖ ≤ B) :
    Summable (fun M ↦ (gammaPhysicalWeight x M : ℂ) * F M) := by
  apply Summable.of_norm
  apply ((hasSum_gammaPhysicalWeight hx).summable.mul_right B).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro M
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gammaPhysicalWeight_bounds hx.le M).1]
  exact mul_le_mul_of_nonneg_left (hF M) (gammaPhysicalWeight_bounds hx.le M).1

private theorem sum_gammaPhysicalWeight_mul (x : ℝ) (F : ℕ → ℂ) (hF0 : F 0 = 0) (N : ℕ) :
    (∑ M ∈ Finset.range N, (gammaPhysicalWeight x M : ℂ) * F M) =
      (∑ n ∈ Finset.range N, (gammaSurvival ((n + 1 : ℝ) * x) : ℂ) * (F (n + 1) - F n)) -
        (gammaSurvival ((N : ℝ) * x) : ℂ) * F N := by
  induction N with
  | zero => simp [hF0]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, gammaPhysicalWeight]
    push_cast
    ring

/-- Discrete Abel summation identifies the positive average from its literal prefix increments, with the infinite boundary discharged. -/
theorem hasSum_gammaPhysicalWeight_mul_of_increments {x : ℝ} (hx : 0 < x) {F : ℕ → ℂ}
    (hF0 : F 0 = 0) {B : ℝ} (hF : ∀ M, ‖F M‖ ≤ B) {z : ℂ}
    (hz : HasSum (fun n : ℕ ↦ (gammaSurvival ((n + 1 : ℝ) * x) : ℂ) * (F (n + 1) - F n)) z) :
    HasSum (fun M ↦ (gammaPhysicalWeight x M : ℂ) * F M) z := by
  have hboundary : Tendsto (fun N : ℕ ↦ (gammaSurvival ((N : ℝ) * x) : ℂ) * F N) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ ?_)
      (by simpa only [zero_mul] using (summable_gammaSurvival_nat_mul hx).tendsto_atTop_zero.mul_const B)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (gammaSurvival_nonneg (by positivity))]
    exact mul_le_mul_of_nonneg_left (hF N) (gammaSurvival_nonneg (by positivity))
  apply (hasSum_iff_tendsto_nat_of_summable_norm (summable_gammaPhysicalWeight_mul hx hF).norm).mpr
  simp only [sum_gammaPhysicalWeight_mul x F hF0]
  simpa only [sub_zero] using hz.tendsto_sum_nat.sub hboundary

/-- The repository's odd-positive sign agrees with the zero-based alternating series sign. -/
theorem pairedEtaDirichletSign_succ_eq (n : ℕ) :
    (pairedEtaDirichletSign (n + 1) : ℝ) = (-1 : ℝ) ^ n := by
  induction n with
  | zero => norm_num [pairedEtaDirichletSign]
  | succ n ih =>
    rw [pairedEtaDirichletSign_add_odd _ _ (by decide : Odd 1), Int.cast_neg, ih, pow_succ]
    ring

/-- Every genuine eta prefix at a nontrivial zero is bounded uniformly, including the empty prefix. -/
theorem norm_etaPrefix_le_constant (rho : NontrivialZetaZero) (M : ℕ) :
    ‖pairedEtaUnpairedDirichletPrefix M rho.1‖ ≤ ‖rho.1‖ / rho.1.re + 1 := by
  have hs := NontrivialZetaZero.zero_lt_re rho
  by_cases hM : M = 0
  · subst M
    simp only [pairedEtaUnpairedDirichletPrefix, Finset.Icc_eq_empty_of_lt (by decide : 0 < 1),
      Finset.sum_empty, norm_zero]
    positivity
  apply (norm_pairedEtaUnpairedDirichletPrefix_le rho (Nat.one_le_iff_ne_zero.mpr hM)).trans
  have hp : (M : ℝ) ^ (-rho.1.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM) (neg_nonpos.mpr hs.le)
  exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq (mul_one _)

/-- The cubic damped eta series is exactly a positive average of the literal unpaired eta prefixes. -/
theorem hasSum_gammaPhysicalWeight_etaPrefix (rho : NontrivialZetaZero) {x : ℝ} (hx : 0 < x) :
    HasSum (fun M ↦ (gammaPhysicalWeight x M : ℂ) * pairedEtaUnpairedDirichletPrefix M rho.1)
      (gammaDampedEta rho.1 x) := by
  apply hasSum_gammaPhysicalWeight_mul_of_increments hx
    (by simp [pairedEtaUnpairedDirichletPrefix]) (norm_etaPrefix_le_constant rho)
  have h := (hasSum_gammaDampedEta (NontrivialZetaZero.zero_lt_re rho) hx)
  rw [← gammaDampedEta_eq_mellin (NontrivialZetaZero.zero_lt_re rho) hx] at h
  convert! h using 1
  funext n
  rw [pairedEtaUnpairedDirichletPrefix_succ, add_sub_cancel_left]
  have he : (pairedEtaDirichletSign (n + 1) : ℂ) = ((-1 : ℝ) ^ n : ℝ) := by
    exact_mod_cast pairedEtaDirichletSign_succ_eq n
  simp only [he, gammaEtaCoefficient, Complex.ofReal_mul, Nat.cast_add, Nat.cast_one,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
  ring

/-- Every complete quotient fibre has exactly its coarser positive survival mass. -/
theorem sum_gammaPhysicalWeight_quotient (x : ℝ) (d q : ℕ) :
    (∑ r : Fin d, gammaPhysicalWeight x (q * d + r)) = gammaPhysicalWeight ((d : ℝ) * x) q := by
  rw [Fin.sum_univ_eq_sum_range (fun r ↦ gammaPhysicalWeight x (q * d + r)) d]
  have hh : (∑ r ∈ Finset.range d, gammaPhysicalWeight x (q * d + r)) =
      gammaSurvival (((q * d : ℕ) : ℝ) * x) -
        gammaSurvival (((q * d + d : ℕ) : ℝ) * x) := by
    convert! Finset.sum_range_sub'
      (fun r ↦ gammaSurvival (((q * d + r : ℕ) : ℝ) * x)) d using 1
    · apply Finset.sum_congr rfl
      intro r _
      simp only [gammaPhysicalWeight, Nat.cast_add, Nat.cast_one, add_assoc]
  rw [hh, gammaPhysicalWeight]
  push_cast
  congr 2 <;> ring

/-- Grouping the entire positive physical average by complete quotient fibres preserves the bounded complex carrier exactly. -/
theorem tsum_gammaPhysicalWeight_div {x : ℝ} (hx : 0 < x) {d : ℕ} (hd : 1 ≤ d)
    {F : ℕ → ℂ} {B : ℝ} (hF : ∀ q, ‖F q‖ ≤ B) :
    (∑' M : ℕ, (gammaPhysicalWeight x M : ℂ) * F (M / d)) =
      ∑' q : ℕ, (gammaPhysicalWeight ((d : ℝ) * x) q : ℂ) * F q := by
  let : NeZero d := ⟨by omega⟩
  let f : ℕ → ℂ := fun M ↦ (gammaPhysicalWeight x M : ℂ) * F (M / d)
  have hf : Summable f := summable_gammaPhysicalWeight_mul hx (fun M ↦ hF (M / d))
  have hp : Summable (f ∘ (Nat.divModEquiv d).symm) := (Nat.divModEquiv d).symm.summable_iff.mpr hf
  change (∑' M, f M) = _
  rw [← (Nat.divModEquiv d).symm.tsum_eq f]
  change (∑' p, (f ∘ (Nat.divModEquiv d).symm) p) = _
  rw [hp.tsum_prod]
  apply tsum_congr
  intro q
  simp only [Function.comp_apply, Nat.divModEquiv_symm_apply, f, tsum_fintype]
  have hdiv (r : Fin d) : (q * d + r.val) / d = q := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt r.is_lt, zero_add]
  simp only [hdiv, ← Finset.sum_mul, ← Complex.ofReal_sum, sum_gammaPhysicalWeight_quotient]

/-- The literal completed Möbius term has exactly the damped eta average at its divided physical scale. -/
theorem hasSum_gammaPhysicalWeight_moebiusTerm (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    {d : ℕ} (hd : 1 ≤ d) :
    HasSum (fun M ↦ (gammaPhysicalWeight A⁻¹ M : ℂ) * pairedEtaCompletedMoebiusTerm rho M d)
      (gammaMoebiusTerm rho A d) := by
  let c : ℂ := (μ d : ℂ) * (d : ℂ) ^ (-rho.1) * pairedEtaXiCompletionFactor rho.1
  have he (M : ℕ) : (gammaPhysicalWeight A⁻¹ M : ℂ) * pairedEtaCompletedMoebiusTerm rho M d =
      c * ((gammaPhysicalWeight A⁻¹ M : ℂ) * pairedEtaUnpairedDirichletPrefix (M / d) rho.1) := by
    rw [pairedEtaCompletedMoebiusTerm_eq_completed_prefix]
    dsimp only [c]
    ring
  have hx : 0 < A⁻¹ := inv_pos.mpr hA
  have hs := summable_gammaPhysicalWeight_mul hx (fun M ↦ norm_etaPrefix_le_constant rho (M / d))
  have hsum : (∑' M : ℕ, (gammaPhysicalWeight A⁻¹ M : ℂ) *
      pairedEtaUnpairedDirichletPrefix (M / d) rho.1) = gammaDampedEta rho.1 ((d : ℝ) / A) := by
    rw [tsum_gammaPhysicalWeight_div hx hd (norm_etaPrefix_le_constant rho)]
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    simpa only [div_eq_mul_inv] using
      (hasSum_gammaPhysicalWeight_etaPrefix rho (div_pos hdR hA)).tsum_eq
  have h := ((hs.hasSum_iff.mpr hsum).mul_left c)
  convert! h using 1
  · funext M
    exact he M
  · dsimp only [gammaMoebiusTerm, c]
    ring

/-- The full selected smoothed family equals a positive average of the original completed selected family. -/
theorem hasSum_gammaPhysicalWeight_moebiusSelected (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) {S : Finset ℕ} (hS : ∀ d ∈ S, 1 ≤ d) :
    HasSum (fun M ↦ (gammaPhysicalWeight A⁻¹ M : ℂ) *
      pairedEtaCompletedMoebiusSelectedAggregate rho S M) (gammaMoebiusSelected rho S A) := by
  have hh := hasSum_sum (fun d hd ↦ hasSum_gammaPhysicalWeight_moebiusTerm rho hA (hS d hd))
  simpa only [pairedEtaCompletedMoebiusSelectedAggregate, gammaMoebiusSelected, Finset.mul_sum] using hh

/-- The actual averaged Möbius source retains both finite physical survival endpoints. -/
def gammaMoebiusSource (rho : NontrivialZetaZero) (A : ℝ) : ℂ :=
  pairedEtaXiCompletionFactor rho.1 *
    ((gammaSurvival A⁻¹ : ℂ) - 2 * (2 : ℂ) ^ (-rho.1) * (gammaSurvival (2 / A) : ℂ))

private theorem moebiusTailAggregate_endpoints (rho : NontrivialZetaZero) (M : ℕ) :
    pairedEtaCompletedMoebiusTailAggregate rho M =
      pairedEtaCompletedMoebiusSource rho - (if M = 0 then pairedEtaCompletedMoebiusSource rho else 0) +
        (if M = 1 then pairedEtaXiCompletionFactor rho.1 - pairedEtaCompletedMoebiusSource rho else 0) := by
  by_cases h0 : M = 0
  · subst M
    simp [pairedEtaCompletedMoebiusTailAggregate]
  by_cases h1 : M = 1
  · subst M
    rw [← sum_pairedEtaCompletedMoebiusTerm]
    simp [pairedEtaCompletedMoebiusTerm_eq_completed_prefix, pairedEtaUnpairedDirichletPrefix,
      pairedEtaDirichletSign]
  simp only [if_neg h0, if_neg h1, sub_zero, add_zero]
  exact pairedEtaCompletedMoebiusTailAggregate_eq_source rho (by omega)

/-- Averaging the literal full Möbius aggregate gives the two original dyadic source terms with their correct survival weights. -/
theorem hasSum_gammaPhysicalWeight_moebiusSource (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) :
    HasSum (fun M ↦ (gammaPhysicalWeight A⁻¹ M : ℂ) * pairedEtaCompletedMoebiusTailAggregate rho M)
      (gammaMoebiusSource rho A) := by
  have hw := Complex.hasSum_ofReal.mpr (hasSum_gammaPhysicalWeight (inv_pos.mpr hA))
  have h0 := hasSum_ite_eq 0 ((gammaPhysicalWeight A⁻¹ 0 : ℂ) * pairedEtaCompletedMoebiusSource rho)
  have h1 := hasSum_ite_eq 1 ((gammaPhysicalWeight A⁻¹ 1 : ℂ) *
    (pairedEtaXiCompletionFactor rho.1 - pairedEtaCompletedMoebiusSource rho))
  convert! ((hw.mul_right (pairedEtaCompletedMoebiusSource rho)).sub h0).add h1 using 1
  · funext M
    rw [moebiusTailAggregate_endpoints]
    split_ifs with hM0 hM1 <;> simp_all only [sub_zero, add_zero]
    all_goals ring
  · simp only [gammaMoebiusSource, gammaPhysicalWeight, Nat.cast_zero, zero_mul,
      zero_add, one_mul, Nat.cast_one, pairedEtaCompletedMoebiusSource]
    norm_num only [gammaSurvival, Real.exp_zero, pow_zero, zero_div, add_zero,
      one_mul, Complex.ofReal_one]
    push_cast
    rw [div_eq_mul_inv]
    ring_nf

/-- The exact source approaches the original nonzero source with a cubic physical-scale allowance. -/
theorem norm_gammaMoebiusSource_sub_le (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A) :
    ‖gammaMoebiusSource rho A - pairedEtaCompletedMoebiusSource rho‖ ≤
      ‖pairedEtaXiCompletionFactor rho.1‖ * (1 + 16 * (2 : ℝ) ^ (-rho.1.re)) / (6 * A ^ 3) := by
  have he : gammaMoebiusSource rho A - pairedEtaCompletedMoebiusSource rho =
      pairedEtaXiCompletionFactor rho.1 *
        (((gammaSurvival A⁻¹ - 1 : ℝ) : ℂ) -
          2 * (2 : ℂ) ^ (-rho.1) * ((gammaSurvival (2 / A) - 1 : ℝ) : ℂ)) := by
    simp only [gammaMoebiusSource, pairedEtaCompletedMoebiusSource, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [he, norm_mul]
  apply (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)).trans
  have hpow : ‖(2 : ℂ) ^ (-rho.1)‖ = (2 : ℝ) ^ (-rho.1.re) := by
    simpa only [Complex.ofReal_ofNat, Complex.neg_re] using
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (-rho.1)
  rw [norm_mul, norm_mul, Complex.norm_ofNat,
    hpow,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have h0 := abs_gammaSurvival_sub_one_le (inv_nonneg.mpr hA.le)
  have h2 := abs_gammaSurvival_sub_one_le (show 0 ≤ 2 / A by positivity)
  apply (mul_le_mul_of_nonneg_left
    (add_le_add h0 (mul_le_mul_of_nonneg_left h2 (by positivity))) (norm_nonneg _)).trans_eq
  rw [div_pow, inv_pow]
  ring

private theorem moebiusTailAggregate_eq_selected_add_large (rho : NontrivialZetaZero) (M D : ℕ) :
    pairedEtaCompletedMoebiusTailAggregate rho M =
      pairedEtaCompletedMoebiusSelectedAggregate rho (Finset.Icc 1 D) M +
        pairedEtaCompletedMoebiusLargeAggregate rho M D := by
  by_cases hDM : D ≤ M
  · exact (pairedEtaCompletedMoebiusPartial_add_large rho hDM).symm
  have hlarge : pairedEtaCompletedMoebiusLargeAggregate rho M D = 0 := by
    simp only [pairedEtaCompletedMoebiusLargeAggregate, Finset.Ioc_eq_empty_of_le (by omega : M ≤ D),
      Finset.sum_empty]
  rw [hlarge, add_zero, ← sum_pairedEtaCompletedMoebiusTerm, pairedEtaCompletedMoebiusSelectedAggregate]
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right (by omega : M ≤ D))
  intro d hd hnot
  have hdM : M < d := by
    have hd1 := (Finset.mem_Icc.mp hd).1
    simp only [Finset.mem_Icc] at hnot
    omega
  rw [pairedEtaCompletedMoebiusTerm_eq_completed_prefix, Nat.div_eq_of_lt hdM]
  simp [pairedEtaUnpairedDirichletPrefix]

/-- The full high-divisor carrier has an absolutely convergent positive average equal to the exact source minus the complete selected low family. -/
theorem hasSum_gammaPhysicalWeight_moebiusLarge (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) (D : ℕ) :
    HasSum (fun M ↦ (gammaPhysicalWeight A⁻¹ M : ℂ) * pairedEtaCompletedMoebiusLargeAggregate rho M D)
      (gammaMoebiusSource rho A - gammaMoebiusSelected rho (Finset.Icc 1 D) A) := by
  have ht := hasSum_gammaPhysicalWeight_moebiusSource rho hA
  have hl := hasSum_gammaPhysicalWeight_moebiusSelected rho hA
    (fun _ hd ↦ (Finset.mem_Icc.mp hd).1 : ∀ d ∈ Finset.Icc 1 D, 1 ≤ d)
  convert! ht.sub hl using 1
  funext M
  rw [moebiusTailAggregate_eq_selected_add_large rho M D]
  ring

/-- The cubic divisor allowance holds for the positive average of the original selected completed carrier itself. -/
theorem norm_tsum_gammaPhysicalWeight_moebiusSelected_le (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) {S : Finset ℕ} {D : ℕ} (hS : S ⊆ Finset.Icc 1 D) :
    ‖∑' M : ℕ, (gammaPhysicalWeight A⁻¹ M : ℂ) * pairedEtaCompletedMoebiusSelectedAggregate rho S M‖ ≤
      gammaMoebiusConstant rho / A ^ 3 * (D : ℝ) ^ (4 - rho.1.re) := by
  rw [(hasSum_gammaPhysicalWeight_moebiusSelected rho hA (fun _ hd ↦ (Finset.mem_Icc.mp (hS hd)).1)).tsum_eq]
  exact norm_gammaMoebiusSelected_le rho hA hS

/-- All selected original low-divisor averages vanish on the sixth/fifth-power schedule, with summability and physical endpoints already discharged. -/
theorem tsum_gammaPhysicalWeight_moebiusSelected_sixth_tendsto_zero (rho : NontrivialZetaZero)
    (hrho : (2 : ℝ) / 5 < rho.1.re) (S : ℕ → Finset ℕ)
    (hS : ∀ u, S u ⊆ Finset.Icc 1 (u ^ 5)) :
    Tendsto (fun u : ℕ ↦ ∑' M : ℕ, (gammaPhysicalWeight (((u : ℝ) ^ 6)⁻¹) M : ℂ) *
      pairedEtaCompletedMoebiusSelectedAggregate rho (S u) M) atTop (𝓝 0) := by
  apply (gammaMoebiusSelected_sixth_tendsto_zero rho hrho S hS).congr'
  filter_upwards [eventually_ge_atTop 1] with u hu
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  exact (hasSum_gammaPhysicalWeight_moebiusSelected rho (pow_pos huR 6)
    (fun _ hd ↦ (Finset.mem_Icc.mp (hS u hd)).1)).tsum_eq.symm

end

end RiemannGaussian.EtaGammaSmoothing
