import CheckAlpogeCubicCross
import RiemannGaussian.ZetaVaughanIdentity

/-! # Vaughan's identity in the averaged cubic window -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real MeasureTheory ZetaVaughanReduction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt ArithmeticFunction.zeta

private theorem head_mul_eq (f g : ArithmeticFunction ℝ) (U p : ℕ) :
    (head U f * g) p =
      ∑ d ∈ Ioc 0 U, f d * (if d ∣ p then g (p/d) else 0) := by
  by_cases hp : p = 0
  · subst p
    simp
  rw [ArithmeticFunction.mul_apply, ← Nat.map_div_right_divisors, sum_map]
  change (∑ d ∈ p.divisors, (if d ≤ U then f d else 0)*g (p/d)) = _
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, ← sum_filter]
  congr 1
  ext d
  simp only [mem_filter, Nat.mem_divisors, mem_Ioc]
  constructor
  · rintro ⟨⟨hd, _⟩, hU⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hp), hU⟩, hd⟩
  · rintro ⟨⟨_, hU⟩, hd⟩
    exact ⟨⟨hd, hp⟩, hU⟩

private theorem head_log_eq (U p : ℕ) :
    (head U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) p =
      ∑ d ∈ Ioc 0 U, (μ d:ℝ) * strideLog d p := by
  rw [head_mul_eq]
  simp only [strideLog, ArithmeticFunction.log_apply, ArithmeticFunction.intCoe_apply]

private theorem head_cross_eq (U V p : ℕ) :
    (head U (μ : ArithmeticFunction ℝ) * head V Λ * ζ) p =
      ∑ d ∈ Ioc 0 U, ∑ v ∈ Ioc 0 V, (μ d:ℝ)*Λ v*strideUnit (d*v) p := by
  rw [mul_assoc, head_mul_eq]
  apply sum_congr rfl
  intro d hd
  have hd0 := (mem_Ioc.mp hd).1.ne'
  simp only [ArithmeticFunction.intCoe_apply, ← mul_sum, mul_assoc]
  congr 1
  by_cases hdp : d ∣ p
  · rw [ite_eq_left hdp, head_mul_eq]
    apply sum_congr rfl
    intro v _
    congr 1
    have hdiv : d*v ∣ p ↔ v ∣ p/d := by
      conv_lhs => rw [← Nat.mul_div_cancel' hdp]
      exact Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hd0)
    by_cases hv : v ∣ p/d
    · rw [ite_eq_left hv, strideUnit, ite_eq_left (hdiv.mpr hv), Nat.div_div_eq_div_mul]
      simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply]
    · rw [ite_eq_right hv, strideUnit, ite_eq_right (not_congr hdiv |>.mpr hv)]
  · rw [ite_eq_right hdp]
    symm
    apply sum_eq_zero
    intro v _
    simp [strideUnit, show ¬ d*v ∣ p from fun h => hdp ((dvd_mul_right d v).trans h)]

/-- The finite weighted response of a coefficient, including the cubic cutoff. -/
def weightedCoefficient (M D : ℕ) : (ℕ → ℝ) →ₗ[ℝ] ℝ where
  toFun c := weight M D * coefficientPrefix c D + ∑ p ∈ Ioc D M, c p * weight M p
  map_add' a b := by
    simp only [Pi.add_apply, coefficientPrefix, sum_add_distrib, add_mul, mul_add]
    ring
  map_smul' r a := by
    simp only [coefficientPrefix, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_assoc r, ← mul_sum]
    ring

private theorem weightedCoefficient_sumIntegral (M D : ℕ) (c : ℕ → ℝ)
    (hD : 0 < D) (hDM : D ≤ M) :
    weightedCoefficient M D c = tailQuadratureSumIntegral M D (coefficientPrefix c) :=
  (coefficient_tailQuadratureSumIntegral c hD hDM).symm

private theorem weightedMangoldtDiscrepancy_eq (M D : ℕ) :
    weightedMangoldtDiscrepancy M D = weightedCoefficient M D (strideUnit 1) -
      weightedCoefficient M D (fun p => Λ p) := by
  change _ = (weight M D * coefficientPrefix (strideUnit 1) D + _) -
    (weight M D * coefficientPrefix (fun p => Λ p) D + _)
  rw [strideUnit_prefix (by decide : 0 < 1), Nat.cast_one, div_one, Nat.floor_natCast]
  simp only [coefficientPrefix, Nat.floor_natCast, weightedMangoldtDiscrepancy]
  rw [show Chebyshev.psi D = ∑ j ∈ Icc 0 D, Λ j from Chebyshev.psi_eq_sum_Icc _ |>.trans
    (by rw [Nat.floor_natCast])]
  rw [show (∑ p ∈ Ioc D M, (1-Λ p)*weight M p) =
    (∑ p ∈ Ioc D M, strideUnit 1 p * weight M p) -
      ∑ p ∈ Ioc D M, Λ p * weight M p by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro p hp
      have hp0 := ((Nat.zero_le D).trans_lt (mem_Ioc.mp hp).1).ne'
      simp [sub_mul, strideUnit, hp0]]
  ring

private def smallLogError (M n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 n, (μ d:ℝ) *
    (tailQuadratureSumIntegral M (n^3) (coefficientPrefix (strideLog d)) -
      tailQuadratureSumIntegral M (n^3) (strideLogMain d))

private def crossError (M n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 n, ∑ v ∈ Ioc 0 n, (μ d:ℝ)*Λ v*strideUnitError M (n^3) (d*v)

/-- The signed residual after replacing the small progression sums by their
continuous main terms and removing the nonpositive small-prime-power head. -/
private def vaughanResidualAt (M n : ℕ) : ℝ :=
  tailQuadratureSumIntegral M (n^3) id -
    (∑ d ∈ Ioc 0 n, (μ d:ℝ)*tailQuadratureSumIntegral M (n^3) (strideLogMain d)) +
    (∑ d ∈ Ioc 0 n, ∑ v ∈ Ioc 0 n, (μ d:ℝ)*Λ v*
      tailQuadratureSumIntegral M (n^3) (fun x => x/((d*v:ℕ):ℝ))) -
    weightedCoefficient M (n^3) (bilinear n n)

private theorem weightedMangoldtDiscrepancy_split {M n : ℕ} (hn : 0 < n)
    (hM : n^3 ≤ M) :
    weightedMangoldtDiscrepancy M (n^3) =
      vaughanResidualAt M n - weightedCoefficient M (n^3) (head n Λ) -
        smallLogError M n + crossError M n + strideUnitError M (n^3) 1 := by
  let Q := weightedCoefficient M (n^3)
  have hQ (c : ℕ → ℝ) : Q c = tailQuadratureSumIntegral M (n^3) (coefficientPrefix c) :=
    weightedCoefficient_sumIntegral M (n^3) c (pow_pos hn 3) hM
  have hsplit : (fun p => Λ p) = ⇑(head n Λ) +
      ⇑(head n (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) -
      ⇑(head n (μ : ArithmeticFunction ℝ) * head n Λ * ζ) + ⇑(bilinear n n) := by
    funext p
    exact congrArg (fun a : ArithmeticFunction ℝ => a p) (vaughan n n)
  have hlog : Q ⇑(head n (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) =
      ∑ d ∈ Ioc 0 n, (μ d:ℝ)*tailQuadratureSumIntegral M (n^3)
        (coefficientPrefix (strideLog d)) := by
    have h : ⇑(head n (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) =
        ∑ d ∈ Ioc 0 n, (μ d:ℝ) • strideLog d := by
      funext p
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using head_log_eq n p
    rw [h, map_sum]
    simp only [map_smul, smul_eq_mul]
    simp only [hQ]
  have hcross : Q ⇑(head n (μ : ArithmeticFunction ℝ) * head n Λ * ζ) =
      ∑ d ∈ Ioc 0 n, ∑ v ∈ Ioc 0 n, (μ d:ℝ)*Λ v*
        tailQuadratureSumIntegral M (n^3) (coefficientPrefix (strideUnit (d*v))) := by
    have h : ⇑(head n (μ : ArithmeticFunction ℝ) * head n Λ * ζ) =
        ∑ d ∈ Ioc 0 n, ∑ v ∈ Ioc 0 n, ((μ d:ℝ)*Λ v) • strideUnit (d*v) := by
      funext p
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using head_cross_eq n n p
    rw [h]
    simp only [map_sum, map_smul, smul_eq_mul]
    simp only [hQ]
  have hunit : Q (strideUnit 1) = tailQuadratureSumIntegral M (n^3) id +
      strideUnitError M (n^3) 1 := by
    rw [hQ, strideUnitError,
      show (fun x : ℝ => x/((1:ℕ):ℝ)) = id by funext x; simp]
    ring
  rw [weightedMangoldtDiscrepancy_eq]
  change Q (strideUnit 1) - Q (fun p => Λ p) = _
  rw [hunit, hsplit, map_add, map_sub, map_add, hlog, hcross]
  unfold vaughanResidualAt smallLogError crossError strideUnitError
  simp only [mul_sub, sum_sub_distrib]
  dsimp only [Q]
  ring

private theorem weightedCoefficient_nonneg {c : ℕ → ℝ} {M D : ℕ} (hD : 0 < D)
    (hc : ∀ p, 0 ≤ c p) : 0 ≤ weightedCoefficient M D c :=
  add_nonneg (mul_nonneg (weight_mem (N := M) hD).1 (sum_nonneg fun p _ => hc p))
    (sum_nonneg fun p hp => mul_nonneg (hc p)
      (weight_mem (N := M) (hD.trans (mem_Ioc.mp hp).1)).1)

/-- The repeated average evaluated at the base of the cubic window for n. -/
def cubicMean (n : ℕ) : (ℕ → ℝ) →ₗ[ℝ] ℝ :=
  let k := Nat.log 2 n+1
  (LinearMap.proj (n^4-k*n^3)).comp (repeatedMean (2*n^3+1) k)

private theorem cubicMean_mono {n : ℕ} (hn : 8 ≤ n) {f g : ℕ → ℝ}
    (h : ∀ M ≥ n^3, f M ≤ g M) : cubicMean n f ≤ cubicMean n g := by
  let k := Nat.log 2 n+1
  have hk : 2*k ≤ n := (cubic_tail_parameters hn).1
  have hA : n^3 ≤ n^4-k*n^3 := by
    rw [show n^4=n*n^3 by ring, ← Nat.sub_mul]
    exact Nat.le_mul_of_pos_left _ (by omega)
  change repeatedMean (2*n^3+1) k f (n^4-k*n^3) ≤
    repeatedMean (2*n^3+1) k g (n^4-k*n^3)
  apply repeat_mono
  intro M hM _
  exact h M (hA.trans hM)

private theorem cubicMean_crossError (n : ℕ) :
    cubicMean n (fun M => crossError M n) = averagedCubicCrossError n := by
  have h : (fun M : ℕ => crossError M n) = ∑ d ∈ Ioc 0 n, ∑ v ∈ Ioc 0 n,
      ((μ d:ℝ)*Λ v) • (fun M : ℕ => strideUnitError M (n^3) (d*v)) := by
    funext M
    simp only [crossError, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h]
  simp only [map_sum, map_smul, smul_eq_mul]
  rfl

/-- The signed Vaughan residual with the original repeated average. -/
def cubicVaughanResidual (n : ℕ) : ℝ :=
  cubicMean n (fun M => vaughanResidualAt M n)

private theorem log_kernel_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => x*log x/x^2) volume a b :=
  ((continuousOn_id.mul (continuousOn_id.log fun _ hx => (ha.trans_le hx.1).ne')).div
    (continuousOn_id.pow 2) fun _ hx =>
      pow_ne_zero _ (ha.trans_le hx.1).ne').intervalIntegrable_of_Icc hab

private theorem tailQuadrature_linearMoments {M D : ℕ} (hD : 0 < D) (hDM : D ≤ M)
    (a b : ℝ) :
    tailQuadratureSumIntegral M D (fun x => a*(x*log x)+b*x) =
      a*tailQuadratureSumIntegral M D (fun x => x*log x) + b*tailQuadratureSumIntegral M D id := by
  have hDR : 0 < (D:ℝ) := by exact_mod_cast hD
  have hDMR : (D:ℝ) ≤ M := by exact_mod_cast hDM
  have hnz (x : ℝ) (hx : x ∈ Set.Icc (D:ℝ) M) : x ≠ 0 := (hDR.trans_le hx.1).ne'
  have hi : IntervalIntegrable (fun x : ℝ => x/x^2) volume D M :=
    (continuousOn_id.div (continuousOn_id.pow 2)
      fun x hx => pow_ne_zero _ (hnz x hx)).intervalIntegrable_of_Icc hDMR
  have hl := log_kernel_integrable hDR hDMR
  have hInt : (∫ x in (D:ℝ)..(M:ℝ), (a*(x*log x)+b*x)/x^2) =
      a*(∫ x in (D:ℝ)..(M:ℝ), x*log x/x^2) + b*(∫ x in (D:ℝ)..(M:ℝ), x/x^2) := by
    have h : (fun x : ℝ => (a*(x*log x)+b*x)/x^2) =
        (fun x : ℝ => a*(x*log x/x^2)+b*(x/x^2)) := by
      funext x
      rw [add_div, mul_div_assoc a, mul_div_assoc b]
    rw [h, intervalIntegral.integral_add (hl.const_mul a) (hi.const_mul b)]
    simp only [intervalIntegral.integral_const_mul]
  unfold tailQuadratureSumIntegral
  simp only [id_eq, hInt, sum_add_distrib, ← mul_sum]
  ring

/-- The reciprocal sum of the small Möbius factors. -/
def moebiusReciprocal (n : ℕ) : ℝ := ∑ d ∈ Ioc 0 n, (μ d:ℝ)/d

/-- The logarithmic reciprocal sum of the small Möbius factors. -/
def moebiusLogReciprocal (n : ℕ) : ℝ := ∑ d ∈ Ioc 0 n, (μ d:ℝ)*log d/d

/-- The reciprocal sum of the small von Mangoldt factors. -/
def mangoldtReciprocal (n : ℕ) : ℝ := ∑ v ∈ Ioc 0 n, Λ v/v

private theorem vaughanResidualAt_eq_moments {M n : ℕ} (hn : 0 < n) (hM : n^3 ≤ M) :
    vaughanResidualAt M n = -weightedCoefficient M (n^3) (bilinear n n) -
      moebiusReciprocal n * tailQuadratureSumIntegral M (n^3) (fun x => x*log x) +
      (1+moebiusLogReciprocal n + moebiusReciprocal n * (1+mangoldtReciprocal n)) *
        tailQuadratureSumIntegral M (n^3) id := by
  let Q := tailQuadratureSumIntegral M (n^3)
  have hD := pow_pos hn 3
  have hlog : ∑ d ∈ Ioc 0 n, (μ d:ℝ)*Q (strideLogMain d) =
      moebiusReciprocal n * Q (fun x => x*log x) -
        (moebiusLogReciprocal n + moebiusReciprocal n) * Q id := by
    unfold moebiusReciprocal moebiusLogReciprocal
    rw [← sum_add_distrib, sum_mul, sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro d hd
    have hd0 : (d:ℝ) ≠ 0 := (Nat.cast_pos.mpr (mem_Ioc.mp hd).1).ne'
    have he : strideLogMain d = fun x : ℝ => (d:ℝ)⁻¹*(x*log x) + (-(1+log d)/d)*x := by
      funext x
      by_cases hx : x = 0
      · simp [hx, strideLogMain]
      · simp only [strideLogMain, log_div hx hd0]
        ring
    rw [he, show Q (fun x => (d:ℝ)⁻¹*(x*log x) + (-(1+log d)/d)*x) = _ from
      tailQuadrature_linearMoments hD hM _ _]
    ring
  have hcross : ∑ d ∈ Ioc 0 n, ∑ v ∈ Ioc 0 n, (μ d:ℝ)*Λ v*
      Q (fun x => x/((d*v:ℕ):ℝ)) = moebiusReciprocal n * mangoldtReciprocal n * Q id := by
    unfold moebiusReciprocal mangoldtReciprocal
    rw [sum_mul, sum_mul]
    apply sum_congr rfl
    intro d _
    rw [mul_sum, sum_mul]
    apply sum_congr rfl
    intro v _
    have he : (fun x : ℝ => x/((d*v:ℕ):ℝ)) =
        (fun x : ℝ => 0*(x*log x) + (((d*v:ℕ):ℝ)⁻¹)*x) := by
      funext x
      simp only [zero_mul, zero_add, div_eq_mul_inv, mul_comm]
    rw [he, show Q (fun x => 0*(x*log x) + (((d*v:ℕ):ℝ)⁻¹)*x) = _ from
      tailQuadrature_linearMoments hD hM _ _]
    simp only [zero_mul, zero_add, Nat.cast_mul, mul_inv]
    ring
  change Q id -
    (∑ d ∈ Ioc 0 n, (μ d:ℝ)*Q (strideLogMain d)) +
    (∑ d ∈ Ioc 0 n, ∑ v ∈ Ioc 0 n, (μ d:ℝ)*Λ v*Q (fun x => x/((d*v:ℕ):ℝ))) -
    weightedCoefficient M (n^3) (bilinear n n) = _
  rw [hlog, hcross]
  dsimp only [Q]
  ring

/-- Only two smooth moments remain alongside the exact finite weighted sum. -/
theorem cubicVaughanResidual_eq_moments {n : ℕ} (hn : 8 ≤ n) :
    cubicVaughanResidual n = cubicMean n (fun M =>
      -weightedCoefficient M (n^3) (bilinear n n) -
      moebiusReciprocal n * tailQuadratureSumIntegral M (n^3) (fun x => x*log x) +
      (1+moebiusLogReciprocal n + moebiusReciprocal n * (1+mangoldtReciprocal n)) *
        tailQuadratureSumIntegral M (n^3) id) := by
  apply le_antisymm <;> apply cubicMean_mono hn <;> intro M hM
  · exact (vaughanResidualAt_eq_moments (by omega) hM).le
  · exact (vaughanResidualAt_eq_moments (by omega) hM).ge

/-- The linear moment is a harmonic sum minus its reciprocal integral. -/
theorem tailQuadratureSumIntegral_id_formula {M D : ℕ} (hD : 0 < D) (hDM : D ≤ M) :
    tailQuadratureSumIntegral M D id = (M:ℝ)*(harmonic (M/D)-log ((M:ℝ)/D)) := by
  have h := id_tailQuadrature_formula hD hDM
  unfold tailQuadrature at h
  simp only [id_eq] at h
  linarith only [h]

/-- The logarithmic moment is a finite quotient sum with an explicit endpoint correction. -/
theorem tailQuadratureSumIntegral_log_formula {M D : ℕ} (hD : 0 < D) (hDM : D ≤ M) :
    tailQuadratureSumIntegral M D (fun x => x*log x) =
      (∑ j ∈ Icc 1 (M/D), ((M:ℝ)/j)*log ((M:ℝ)/j)) -
        (M:ℝ)*(log (M:ℝ)^2-log (D:ℝ)^2)/2 := by
  have ha : 0 < (D:ℝ) := by exact_mod_cast hD
  have hab : (D:ℝ) ≤ M := by exact_mod_cast hDM
  have hd (x : ℝ) (hx : x ∈ Set.uIcc (D:ℝ) M) :
      HasDerivAt (fun t : ℝ => log t^2/2) (x*log x/x^2) x := by
    rw [Set.uIcc_of_le hab] at hx
    have hx0 := (ha.trans_le hx.1).ne'
    convert ((hasDerivAt_log hx0).pow 2).div_const 2 using 1
    field_simp
    ring
  rw [tailQuadratureSumIntegral,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (log_kernel_integrable ha hab)]
  ring

def averagedCubicUnitError (n : ℕ) : ℝ :=
  cubicMean n (fun M => strideUnitError M (n^3) 1)

theorem averagedCubicUnitError_bound {n : ℕ} (hn8 : 8 ≤ n) :
    |averagedCubicUnitError n| ≤ (n:ℝ)^2 := by
  have hnR : 8 ≤ (n:ℝ) := by exact_mod_cast hn8
  have hn0 : 0 < (n:ℝ) := by positivity
  have hk : ((Nat.log 2 n+1:ℕ):ℝ) ≤ n := by
    have h := (cubic_tail_parameters hn8).1
    exact_mod_cast (show Nat.log 2 n+1 ≤ n by omega)
  have hB : 27+3*((Nat.log 2 n+1:ℕ):ℝ)+log n ≤ (n:ℝ)^2 := by
    nlinarith only [hk, log_le_sub_one_of_pos hn0, hnR,
      mul_nonneg (sub_nonneg.mpr hnR) hn0.le]
  have he : |averagedCubicUnitError n| ≤ _ :=
    averaged_strideUnitError hn8 (by decide : 0 < 1)
      (Nat.one_le_pow _ _ (by omega : 0 < n))
  exact he.trans hB

private theorem unit_window_error {m b : ℕ} (hm : 8 ≤ m) :
    ∑ n ∈ Icc m b, |averagedCubicUnitError n|/(n:ℝ)^3 ≤ 1+log b := by
  refine (sum_le_sum (s := Icc m b) (g := fun n : ℕ => (n:ℝ)⁻¹) ?_).trans
    (primeWindow_harmonic_le (a := m) (b := b) (by omega))
  intro n hn
  have hn8 := hm.trans (mem_Icc.mp hn).1
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  apply (div_le_iff₀ (pow_pos hn0 3)).mpr
  rw [show (n:ℝ)⁻¹*(n:ℝ)^3=(n:ℝ)^2 by field_simp]
  exact averagedCubicUnitError_bound hn8

/-- Keep the small Mangoldt head and all three signed quadrature errors. -/
theorem cubicMangoldtTail_signed {n : ℕ} (hn : 8 ≤ n) :
    cubicMangoldtTail n = cubicVaughanResidual n -
      cubicMean n (fun M => weightedCoefficient M (n^3) (head n Λ)) -
      averagedSmallDivisorLogError n + averagedCubicCrossError n + averagedCubicUnitError n := by
  let H := fun M => weightedCoefficient M (n^3) (head n Λ)
  let F := fun M => weightedMangoldtDiscrepancy M (n^3)
  let V := (fun M => vaughanResidualAt M n) - H - (fun M => smallLogError M n) +
    (fun M => crossError M n) + (fun M => strideUnitError M (n^3) 1)
  have he (M : ℕ) (hM : n^3 ≤ M) : F M = V M := weightedMangoldtDiscrepancy_split (by omega) hM
  have h : cubicMean n F = cubicMean n V := le_antisymm
    (cubicMean_mono hn (fun M hM => (he M hM).le)) (cubicMean_mono hn (fun M hM => (he M hM).ge))
  dsimp only [V] at h
  rw [map_add,map_add,map_sub,map_sub,cubicMean_crossError] at h
  exact h

private theorem cubicMangoldtTail_le_vaughanResidual {n : ℕ} (hn : 8 ≤ n) :
    cubicMangoldtTail n ≤ cubicVaughanResidual n + |averagedSmallDivisorLogError n| +
      |averagedCubicCrossError n| + |averagedCubicUnitError n| := by
  have h0 : cubicMean n (fun _ => 0) = 0 := map_zero (cubicMean n)
  have hhead := cubicMean_mono (f := fun _ => 0) hn (fun M _ =>
    weightedCoefficient_nonneg (M := M) (pow_pos (by omega : 0 < n) 3)
      (c := ⇑(head n Λ)) (fun p => by by_cases hp : p ≤ n <;> simp [head,hp,ArithmeticFunction.vonMangoldt_nonneg]))
  rw [h0] at hhead
  linarith only [cubicMangoldtTail_signed hn,hhead,neg_le_abs (averagedSmallDivisorLogError n),
    le_abs_self (averagedCubicCrossError n),le_abs_self (averagedCubicUnitError n)]

/-- The positive window mass of the remaining signed Vaughan sum. -/
def cubicVaughanMassOn (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (cubicVaughanResidual n) 0 / (n:ℝ)^3

theorem cubicMangoldtMassOn_le_vaughan {m b : ℕ} (hm : 8 ≤ m) :
    cubicMangoldtMassOn m b ≤ cubicVaughanMassOn m b +
      (17+(log 4+4)*(31+3/log 2))*(1+log b)^2 := by
  calc
    _ ≤ ∑ n ∈ Icc m b, (max (cubicVaughanResidual n) 0 / (n:ℝ)^3 +
        |averagedSmallDivisorLogError n|/(n:ℝ)^3 + |averagedCubicCrossError n|/(n:ℝ)^3 +
        |averagedCubicUnitError n|/(n:ℝ)^3) := by
      apply sum_le_sum
      intro n hn
      simp only [← add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply max_le
      · exact (cubicMangoldtTail_le_vaughanResidual (hm.trans (mem_Icc.mp hn).1)).trans
          (by linarith only [le_max_left (cubicVaughanResidual n) 0])
      · linarith only [le_max_right (cubicVaughanResidual n) 0,
          abs_nonneg (averagedSmallDivisorLogError n), abs_nonneg (averagedCubicCrossError n),
          abs_nonneg (averagedCubicUnitError n)]
    _ ≤ _ := by
      simp only [sum_add_distrib, cubicVaughanMassOn]
      nlinarith only [smallDivisor_log_window_error (b := b) hm, cubicCross_window_error (b := b) hm,
        unit_window_error (b := b) hm, log_natCast_nonneg b, sq_nonneg (log (b:ℝ))]

/-- Cofinal subpower positive mass for the signed Vaughan residual suffices
for the windowed RH proof. -/
theorem rh_of_cubicVaughanMassOn_powerWindows
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, cubicVaughanMassOn m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply rh_of_cubicMangoldtMassOn_powerWindows
  intro α hα
  let C := 17+(log 4+4)*(31+3/log 2)
  let p := α/4
  let K := 1+C*(1+2/p)^2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity [log_pos (by norm_num : (1:ℝ)<4), log_pos (by norm_num : (1:ℝ)<2)]
  have hp : 0 < p := by dsimp [p]; positivity
  obtain ⟨δ,hδ,hδ1,hw⟩ := h p hp
  obtain ⟨R,hR⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hp).eventually_ge_atTop K)
  refine ⟨δ,hδ,hδ1,fun A => ?_⟩
  obtain ⟨m,hm,hmass⟩ := hw (max 8 (max A ⌈R⌉₊))
  let b := powerWindowEnd δ m
  have hm8 : 8 ≤ m := (le_max_left _ _).trans hm
  have hm1 : 1 ≤ m := by omega
  have hmR : 1 ≤ (m:ℝ) := by exact_mod_cast hm1
  have hm0 := zero_lt_one.trans_le hmR
  obtain ⟨hmb,hbm⟩ := powerWindowEnd_bounds hm1 hδ.le hδ1
  have hb0 : 0 < (b:ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hlog := log_le_log hb0 (show (b:ℝ) ≤ (m:ℝ)^2 by exact_mod_cast hbm)
  rw [log_pow, Nat.cast_ofNat] at hlog
  have hsmall := log_le_rpow_div hm0.le hp
  have hone := one_le_rpow hmR hp.le
  have hsquare : (m:ℝ)^p ≤ ((m:ℝ)^p)^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hone) ((zero_le_one.trans hone))]
  have hK := hR m (Nat.ceil_le.mp (by omega : ⌈R⌉₊ ≤ m))
  have hlogcost : 1+log b ≤ (1+2/p)*(m:ℝ)^p := by
    rw [div_eq_mul_inv] at hsmall ⊢
    nlinarith only [hlog,hsmall,hone]
  have hcost := pow_le_pow_left₀ (by positivity [log_natCast_nonneg b]) hlogcost 2
  refine ⟨m,by omega,?_⟩
  change cubicMangoldtMassOn m b ≤ (m:ℝ)^α
  calc
    _ ≤ (m:ℝ)^p+C*((1+2/p)*(m:ℝ)^p)^2 :=
      (cubicMangoldtMassOn_le_vaughan hm8).trans (add_le_add hmass
        (mul_le_mul_of_nonneg_left hcost hC))
    _ ≤ K*((m:ℝ)^p)^2 := by dsimp [K]; nlinarith only [hsquare]
    _ ≤ ((((m:ℝ)^p)^2)^2) := by
      rw [pow_two (((m:ℝ)^p)^2)]
      exact mul_le_mul_of_nonneg_right (hK.trans hsquare) (sq_nonneg _)
    _ = _ := by
      rw [show ((m:ℝ)^p)^2 = (m:ℝ)^(p+p) by rw [pow_two, ← rpow_add hm0],
        pow_two, ← rpow_add hm0]
      congr 1
      dsimp [p]
      ring

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.cubicVaughanResidual_eq_moments,
      ``RiemannGaussian.AlpogeMined.tailQuadratureSumIntegral_log_formula,
      ``RiemannGaussian.AlpogeMined.cubicMangoldtMassOn_le_vaughan,
      ``RiemannGaussian.AlpogeMined.rh_of_cubicVaughanMassOn_powerWindows] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
