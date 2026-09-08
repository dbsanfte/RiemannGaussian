import RiemannGaussian.EtaGammaMellin

/-!
# Cubic bounds for the gamma-damped eta and Mobius series

The literal signed damped eta series is absolutely convergent and equals
the smoothed Mellin transform. Its zero-specific cubic estimate controls
every selected finite Mobius divisor family, retaining completion and
all complex powers. The sixth/fifth-power schedule gives low-family
decay even on the critical line; it does not establish a zero bound.
-/

open Complex Filter MeasureTheory Set
open scoped Classical Topology Interval ArithmeticFunction.Moebius

namespace RiemannGaussian.EtaGammaSmoothing

noncomputable section

private theorem hasSum_square_geometric {q : ℝ} (hq : |q| < 1) :
    HasSum (fun n : ℕ ↦ (n : ℝ) ^ 2 * q ^ n) (q * (1 + q) / (1 - q) ^ 3) := by
  have h0 := hasSum_geometric_of_abs_lt_one hq
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (show ‖q‖ < 1 from hq)
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one 2 (show ‖q‖ < 1 from hq)
  have h := ((h2.mul_left 2).sub (h1.mul_left 3)).sub (h0.mul_left 2)
  convert! h using 1
  · funext n
    rw [Nat.cast_choose_two]
    push_cast
    ring
  · have hne : 1 - q ≠ 0 := by
      have hlt := (abs_lt.mp hq).2
      linarith
    field_simp
    ring

private theorem hasSum_gamma_geometric {q : ℝ} (hq : |q| < 1) (x : ℝ) :
    HasSum (fun n : ℕ ↦ -q ^ (n + 1) *
      (1 + (n + 1 : ℝ) * x + (n + 1 : ℝ) ^ 2 * x ^ 2 / 2))
      (1 - (1 - q)⁻¹ - x * (q / (1 - q) ^ 2) -
        x ^ 2 / 2 * (q * (1 + q) / (1 - q) ^ 3)) := by
  have h0 := hasSum_geometric_of_abs_lt_one hq
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (show ‖q‖ < 1 from hq)
  have h2 := hasSum_square_geometric hq
  have hall : HasSum (fun n : ℕ ↦ -q ^ n * (1 + (n : ℝ) * x + (n : ℝ) ^ 2 * x ^ 2 / 2))
      (-(1 - q)⁻¹ - x * (q / (1 - q) ^ 2) - x ^ 2 / 2 * (q * (1 + q) / (1 - q) ^ 3)) := by
    convert! ((h0.mul_left (-1)).add (h1.mul_left (-x))).add (h2.mul_left (-(x ^ 2 / 2))) using 1
    · funext n
      ring
    · ring
  have hdrop := (hasSum_nat_add_iff' 1).mpr hall
  convert! hdrop using 1
  · funext n
    push_cast
    rfl
  · simp only [Finset.sum_range_one, pow_zero, Nat.cast_zero, zero_mul, zero_pow (by decide : 2 ≠ 0),
      zero_div, add_zero, mul_one]
    ring

private theorem fermi_eq_exp_neg_div (t : ℝ) :
    fermi t = Real.exp (-t) / (1 + Real.exp (-t)) := by
  rw [fermi, Real.exp_neg]
  field_simp
  ring

/-- The full real transformed kernel has an absolutely convergent signed exponential series. -/
theorem hasSum_gammaTransform_geometric {u : ℝ} (hu : 0 < u) (x : ℝ) :
    HasSum (fun n : ℕ ↦ -(-Real.exp (-u)) ^ (n + 1) *
      (1 + (n + 1 : ℝ) * x + (n + 1 : ℝ) ^ 2 * x ^ 2 / 2))
      (gammaTransform (u - x) x) := by
  have hq : |-Real.exp (-u)| < 1 := by
    rw [abs_neg, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  convert! hasSum_gamma_geometric hq x using 1
  simp only [gammaTransform, sub_add_cancel, fermiOne, fermiTwo, fermi_eq_exp_neg_div]
  have hne : 1 + Real.exp (-u) ≠ 0 := by positivity
  field_simp [hne]
  ring

/-- The exponential Dirichlet coefficient retains the literal alternating sign and positive survival weight. -/
def gammaEtaCoefficient (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * gammaSurvival ((n + 1 : ℝ) * x)

/-- The transformed kernel is exactly the exponential series of the survival-weighted eta coefficients. -/
theorem hasSum_gammaEtaCoefficient_exp {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ gammaEtaCoefficient x n * Real.exp (-(n + 1 : ℝ) * t))
      (gammaTransform t x) := by
  have hu : 0 < t + x := add_pos ht hx
  have h := hasSum_gammaTransform_geometric hu x
  convert! h using 1
  · funext n
    have hsign : -(-Real.exp (-(t + x))) ^ (n + 1) =
        (-1 : ℝ) ^ n * Real.exp (-(t + x)) ^ (n + 1) := by
      rw [neg_pow, pow_succ (-1 : ℝ)]
      ring
    simp only [gammaEtaCoefficient, gammaSurvival, hsign,
      ← Real.exp_nat_mul, Nat.cast_add, Nat.cast_one]
    rw [show ((n : ℝ) + 1) * -(t + x) = -(((n : ℝ) + 1) * x) + -(((n : ℝ) + 1) * t) by ring,
      Real.exp_add]
    ring_nf
  · congr 1
    ring

/-- The positive survival coefficient is nonnegative at every nonnegative cutoff. -/
theorem gammaSurvival_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ gammaSurvival x := by
  unfold gammaSurvival
  positivity

/-- The absolute survival coefficients have exponential summability before any Mellin weighting. -/
theorem summable_gammaSurvival_nat_mul {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ ↦ gammaSurvival ((n : ℝ) * x)) := by
  have hq : ‖Real.exp (-x)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have h0 := summable_geometric_of_norm_lt_one hq
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hq
  apply ((h0.add (h1.mul_left x)).add (h2.mul_left (x ^ 2 / 2))).congr
  intro n
  simp only [gammaSurvival, ← Real.exp_nat_mul, pow_one]
  rw [show (n : ℝ) * -x = -((n : ℝ) * x) by ring]
  ring

/-- The complete absolute Mellin coefficient condition is discharged for the actual survival weights. -/
theorem summable_norm_gammaEtaCoefficient_div_rpow {s : ℂ} (hs : 0 < s.re)
    {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ ↦ ‖(gammaEtaCoefficient x n : ℂ)‖ / (n + 1 : ℝ) ^ s.re) := by
  have hQ : Summable (fun n : ℕ ↦ gammaSurvival ((n + 1 : ℝ) * x)) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (summable_gammaSurvival_nat_mul hx).comp_injective
        (show Function.Injective (fun n : ℕ ↦ n + 1) from by intro a b hab; exact Nat.add_right_cancel hab)
  apply hQ.of_nonneg_of_le (fun n ↦ by positivity)
  intro n
  have hQn := gammaSurvival_nonneg (show 0 ≤ (n + 1 : ℝ) * x by positivity)
  have hp : 1 ≤ (n + 1 : ℝ) ^ s.re := Real.one_le_rpow
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) hs.le
  simp only [gammaEtaCoefficient, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hQn]
  exact (div_le_self hQn hp)

/-- The gamma-damped eta series retains the original positive-integer complex powers. -/
def gammaDampedEta (s : ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, (gammaEtaCoefficient x n : ℂ) * ((n + 1 : ℝ) : ℂ) ^ (-s)

/-- The complete damped eta Dirichlet series sums to the actual smoothed Mellin transform. -/
theorem hasSum_gammaDampedEta {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ ↦ (gammaEtaCoefficient x n : ℂ) * ((n + 1 : ℝ) : ℂ) ^ (-s))
      (smoothedEtaMellin s x) := by
  have h := hasSum_mellin (a := fun n : ℕ ↦ (gammaEtaCoefficient x n : ℂ))
    (p := fun n : ℕ ↦ (n + 1 : ℝ)) (F := fun t : ℝ ↦ (gammaTransform t x : ℂ))
    (fun n ↦ Or.inr (by positivity)) hs
    (fun t ht ↦ by
      simpa only [Complex.ofReal_mul] using Complex.hasSum_ofReal.mpr (hasSum_gammaEtaCoefficient_exp hx ht))
    (summable_norm_gammaEtaCoefficient_div_rpow hs hx)
  have hd := h.div_const (Complex.Gamma s)
  convert! hd using 1
  · funext n
    simp only [Complex.cpow_neg, div_eq_mul_inv]
    calc
      _ = (Complex.Gamma s * (Complex.Gamma s)⁻¹) *
          ((gammaEtaCoefficient x n : ℂ) * (((n + 1 : ℝ) : ℂ) ^ s)⁻¹) := by
        rw [mul_inv_cancel₀ (Complex.Gamma_ne_zero_of_re_pos hs), one_mul]
      _ = _ := by ring

/-- The literal damped eta series is the same complex object as the integrable Mellin transform. -/
theorem gammaDampedEta_eq_mellin {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    gammaDampedEta s x = smoothedEtaMellin s x := (hasSum_gammaDampedEta hs hx).tsum_eq

/-- The cubic estimate applies to the literal damped eta Dirichlet series at an actual zero. -/
theorem norm_gammaDampedEta_at_zero_le (rho : RiemannGaussian.NontrivialZetaZero)
    {x : ℝ} (hx : 0 < x) :
    ‖gammaDampedEta rho.1 x‖ ≤ Real.Gamma rho.1.re / (6 * ‖Complex.Gamma rho.1‖) * x ^ 3 := by
  rw [gammaDampedEta_eq_mellin (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho) hx]
  exact norm_smoothedEtaMellin_at_zero_le rho hx.le


/-- The completed cubic allowance keeps the original completion factor. -/
def gammaMoebiusConstant (rho : NontrivialZetaZero) : ℝ :=
  ‖pairedEtaXiCompletionFactor rho.1‖ *
    (Real.Gamma rho.1.re / (6 * ‖Complex.Gamma rho.1‖))

/-- The completed allowance is strictly positive at every actual nontrivial zero. -/
theorem gammaMoebiusConstant_pos (rho : NontrivialZetaZero) : 0 < gammaMoebiusConstant rho := by
  exact mul_pos (norm_pos_iff.mpr (pairedEtaXiCompletionFactor_ne_zero
    (NontrivialZetaZero.zero_lt_re rho) (NontrivialZetaZero.re_lt_one rho)))
    (mellinRemainderConstant_pos (NontrivialZetaZero.zero_lt_re rho))

/-- The smoothed divisor term keeps the literal Möbius coefficient and both complex phases. -/
def gammaMoebiusTerm (rho : NontrivialZetaZero) (A : ℝ) (d : ℕ) : ℂ :=
  (μ d : ℂ) * (d : ℂ) ^ (-rho.1) *
    (pairedEtaXiCompletionFactor rho.1 * gammaDampedEta rho.1 ((d : ℝ) / A))

/-- The damped eta cancellation gives a cubic physical-scale gain for each original divisor coefficient. -/
theorem norm_gammaMoebiusTerm_le (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    {d : ℕ} (hd : 1 ≤ d) :
    ‖gammaMoebiusTerm rho A d‖ ≤
      gammaMoebiusConstant rho / A ^ 3 * (d : ℝ) ^ (3 - rho.1.re) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hm : ‖(μ d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  have hX := norm_nonneg (pairedEtaXiCompletionFactor rho.1)
  have hpow := Real.rpow_nonneg hdR.le (-rho.1.re)
  rw [gammaMoebiusTerm, norm_mul, norm_mul, norm_mul,
    Complex.norm_natCast_cpow_of_pos hd, Complex.neg_re]
  calc
    _ ≤ 1 * (d : ℝ) ^ (-rho.1.re) *
        (‖pairedEtaXiCompletionFactor rho.1‖ *
          (Real.Gamma rho.1.re / (6 * ‖Complex.Gamma rho.1‖) * ((d : ℝ) / A) ^ 3)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hm hpow)
        (mul_le_mul_of_nonneg_left (norm_gammaDampedEta_at_zero_le rho (div_pos hdR hA)) hX)
        (mul_nonneg hX (norm_nonneg _)) (by positivity)
    _ = _ := by
      rw [Real.rpow_sub hdR, Real.rpow_ofNat, Real.rpow_neg hdR.le]
      dsimp only [gammaMoebiusConstant]
      rw [div_pow]
      ring

/-- The finite selected smoothed family retains all complex divisor terms before taking a norm. -/
def gammaMoebiusSelected (rho : NontrivialZetaZero) (S : Finset ℕ) (A : ℝ) : ℂ :=
  ∑ d ∈ S, gammaMoebiusTerm rho A d

/-- The whole selected family has allowance `C A^(-3) D^(4-Re(rho))`, with no omitted divisor endpoint. -/
theorem norm_gammaMoebiusSelected_le (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    {S : Finset ℕ} {D : ℕ} (hS : S ⊆ Finset.Icc 1 D) :
    ‖gammaMoebiusSelected rho S A‖ ≤
      gammaMoebiusConstant rho / A ^ 3 * (D : ℝ) ^ (4 - rho.1.re) := by
  by_cases hD : D = 0
  · subst D
    have hSe : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun d hd ↦ by
      have hh := Finset.mem_Icc.mp (hS hd)
      omega)
    simp only [gammaMoebiusSelected, hSe, Finset.sum_empty, norm_zero]
    exact mul_nonneg (div_nonneg (gammaMoebiusConstant_pos rho).le (by positivity))
      (Real.rpow_nonneg (by positivity) _)
  have hDR : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero hD
  have hC : 0 ≤ gammaMoebiusConstant rho / A ^ 3 := by
    exact div_nonneg (gammaMoebiusConstant_pos rho).le (by positivity)
  have he : 0 ≤ 3 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hcount : (S.card : ℝ) ≤ D := by
    exact_mod_cast (Finset.card_le_card hS).trans_eq (by simp)
  apply (norm_sum_le S (gammaMoebiusTerm rho A)).trans
  calc
    _ ≤ ∑ _d ∈ S, gammaMoebiusConstant rho / A ^ 3 * (D : ℝ) ^ (3 - rho.1.re) := by
      apply Finset.sum_le_sum
      intro d hdS
      obtain ⟨hd, hdD⟩ := Finset.mem_Icc.mp (hS hdS)
      exact (norm_gammaMoebiusTerm_le rho hA hd).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg d)
          (by exact_mod_cast hdD) he) hC)
    _ ≤ (D : ℝ) * (gammaMoebiusConstant rho / A ^ 3 * (D : ℝ) ^ (3 - rho.1.re)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcount (mul_nonneg hC (Real.rpow_nonneg hDR.le _))
    _ = _ := by
      rw [show 4 - rho.1.re = 1 + (3 - rho.1.re) by ring,
        Real.rpow_add hDR, Real.rpow_one]
      ring

/-- On the sixth-power physical scale the entire selected fifth-power divisor range has a negative-power allowance for `Re(rho)>2/5`. -/
theorem norm_gammaMoebiusSelected_sixth_le (rho : NontrivialZetaZero) {u : ℕ} (hu : 1 ≤ u)
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 (u ^ 5)) :
    ‖gammaMoebiusSelected rho S ((u : ℝ) ^ 6)‖ ≤
      gammaMoebiusConstant rho * (u : ℝ) ^ (2 - 5 * rho.1.re) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  apply (norm_gammaMoebiusSelected_le rho (pow_pos huR 6) hS).trans_eq
  simp only [Nat.cast_pow]
  rw [← Real.rpow_natCast_mul huR.le, ← pow_mul, ← Real.rpow_natCast (u : ℝ) (6 * 3),
    div_mul_eq_mul_div, mul_div_assoc, ← Real.rpow_sub huR]
  congr 2
  norm_num
  ring

/-- The complete selected low-divisor family decays under positive gamma smoothing, including throughout the critical line. -/
theorem gammaMoebiusSelected_sixth_tendsto_zero (rho : NontrivialZetaZero)
    (hrho : (2 : ℝ) / 5 < rho.1.re) (S : ℕ → Finset ℕ)
    (hS : ∀ u, S u ⊆ Finset.Icc 1 (u ^ 5)) :
    Tendsto (fun u : ℕ ↦ gammaMoebiusSelected rho (S u) ((u : ℝ) ^ 6)) atTop (𝓝 0) := by
  have hp : Tendsto (fun u : ℕ ↦ (u : ℝ) ^ (2 - 5 * rho.1.re)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by linarith : 0 < 5 * rho.1.re - 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    ext u
    simp only [Function.comp_apply]
    congr 1
    ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _))
    ((eventually_ge_atTop 1).mono fun u hu ↦ norm_gammaMoebiusSelected_sixth_le rho hu (hS u))
  simpa only [mul_zero] using hp.const_mul (gammaMoebiusConstant rho)

end

end RiemannGaussian.EtaGammaSmoothing
