import RiemannGaussian.EtaMoebiusPrimeProduct

/-!
# Decay of whole odd-prime product families on the original cubic windows

The complete prime-removal annulus is estimated at its literal divided
physical cutoff. On original scales `u = p*v`, these divided windows are
exact complete blocks. Their full sampling loss is still only cubic in
`v`; the original physical power makes the whole prime-product mean
square vanish for a hypothetical zero to the right of one half.
-/

open Complex Filter
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The literal prime-product mean square on the original cubic window and squared divisor cutoff, along original scales divisible by the fixed prime. -/
def pairedEtaMoebiusPrimeProductCubicEnergy (rho : NontrivialZetaZero) (p v : ℕ) : ℝ :=
  (∑ t ∈ Finset.range ((p * v) ^ 3),
    ‖pairedEtaCompletedMoebiusPrimeProductAggregate rho p ((p * v) ^ 2) ((p * v) ^ 3 + t)‖ ^ 2) /
      ((p * v) ^ 3 : ℕ)

/-- A cutoff-independent constant for the whole selected prime-product family; its dependence on the fixed prime is explicit. -/
def pairedEtaMoebiusPrimeProductDecayConstant (rho : NontrivialZetaZero) (p : ℕ) : ℝ :=
  (10 * ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 * finiteCircleSamplingConstant +
    2 * (pairedEtaCompletedMoebiusPhysicalErrorConstant rho +
      2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho) ^ 2) *
    (p : ℝ) ^ 4 * (1 + Real.log p) ^ 2

private theorem prime_window_budget_le {p v c e : ℝ}
    (hp : 1 ≤ p) (hv : 1 ≤ v) (hc : 0 ≤ c) (he : 0 ≤ e) :
    c * ((4 * (p ^ 2 * v ^ 2) ^ 2 + p ^ 2 * v ^ 3) / (p ^ 2 * v ^ 3)) *
        (1 + Real.log (p ^ 2 * v ^ 2)) ^ 2 * (p ^ 2 * v ^ 2) +
      e * (p ^ 2 * v ^ 2) ^ 4 / (p ^ 2 * v ^ 3) ^ 2 ≤
        (20 * c + e) * p ^ 4 * (1 + Real.log p) ^ 2 * v ^ 3 * (1 + Real.log v) ^ 2 := by
  have hpp : 0 < p := by linarith
  have hvp : 0 < v := by linarith
  have hpl := Real.log_nonneg hp
  have hvl := Real.log_nonneg hv
  have hv23 : v ^ 2 ≤ v ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hv (sq_nonneg v)]
  have hp24 : p ^ 2 ≤ p ^ 4 := by nlinarith [sq_nonneg (p ^ 2 - 1)]
  have ha : p ^ 2 * v ^ 2 + 4 * p ^ 4 * v ^ 3 ≤ 5 * p ^ 4 * v ^ 3 := by
    have h := mul_le_mul hp24 hv23 (sq_nonneg v) (pow_nonneg hpp.le 4)
    linarith
  have hb : (1 + 2 * Real.log p + 2 * Real.log v) ^ 2 ≤
      4 * (1 + Real.log p) ^ 2 * (1 + Real.log v) ^ 2 := by
    have h : 1 + 2 * Real.log p + 2 * Real.log v ≤
        2 * (1 + Real.log p) * (1 + Real.log v) := by
      nlinarith [mul_nonneg hpl hvl]
    have hs := (sq_le_sq₀ (by positivity) (by positivity)).mpr h
    nlinarith
  have hlog : 1 ≤ (1 + Real.log p) ^ 2 * (1 + Real.log v) ^ 2 := by
    have hp1 : 1 ≤ (1 + Real.log p) ^ 2 := by nlinarith
    have hv1 : 1 ≤ (1 + Real.log v) ^ 2 := by nlinarith
    nlinarith [mul_le_mul hp1 hv1 (by norm_num) (by positivity)]
  calc
    _ = c * (p ^ 2 * v ^ 2 + 4 * p ^ 4 * v ^ 3) *
        (1 + 2 * Real.log p + 2 * Real.log v) ^ 2 + e * p ^ 4 * v ^ 2 := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      field_simp
      ring
    _ ≤ c * (5 * p ^ 4 * v ^ 3) *
        (4 * (1 + Real.log p) ^ 2 * (1 + Real.log v) ^ 2) +
        e * p ^ 4 * (v ^ 3 * ((1 + Real.log p) ^ 2 * (1 + Real.log v) ^ 2)) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left ha hc) hb (sq_nonneg _) (by positivity)
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hv23.trans (by nlinarith [mul_le_mul_of_nonneg_left hlog (pow_nonneg hvp.le 3)])
    _ = _ := by ring

/-- Every complete odd-prime product family has an explicit mean-square allowance on the original squared/cubic schedule. No correlation-sign assumption is used. -/
theorem pairedEtaMoebiusPrimeProductCubicEnergy_le
    (rho : NontrivialZetaZero) {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {v : ℕ} (hv : 1 ≤ v) :
    pairedEtaMoebiusPrimeProductCubicEnergy rho p v ≤
      pairedEtaMoebiusPrimeProductDecayConstant rho p * (1 + Real.log v) ^ 2 *
        (v : ℝ) ^ (3 - 6 * rho.1.re) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hC := finiteCircleSamplingConstant_pos.le
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv
  have hv23 : v ^ 2 ≤ v ^ 3 := by nlinarith [Nat.mul_le_mul_left (v ^ 2) hv]
  have hA : (p * v) ^ 3 = p * (p ^ 2 * v ^ 3) := by ring
  have hD : (p * v) ^ 2 = p ^ 2 * v ^ 2 := by ring
  have hAp : 0 < p ^ 2 * v ^ 3 := Nat.mul_pos (pow_pos hp.pos 2) (pow_pos hv 3)
  have hDp : 0 < p ^ 2 * v ^ 2 := Nat.mul_pos (pow_pos hp.pos 2) (pow_pos hv 2)
  have hb := pairedEtaCompletedMoebiusPrimeProductAggregate_meanSquare_le_window rho hp hodd
    (A := p ^ 2 * v ^ 3) (L := p ^ 2 * v ^ 3) (D := p ^ 2 * v ^ 2)
    hAp hAp hDp (Nat.mul_le_mul_left _ hv23)
  have hmain := prime_window_budget_le hpR hvR
    (mul_nonneg (by positivity : 0 ≤ ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 2)
      finiteCircleSamplingConstant_pos.le)
    (by positivity : 0 ≤ 2 * (pairedEtaCompletedMoebiusPhysicalErrorConstant rho +
      2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho) ^ 2)
  have hpow : (p : ℝ) ^ (-2 * rho.1.re) *
      ((p : ℝ) ^ 2 * (v : ℝ) ^ 3) ^ (-2 * rho.1.re) ≤
        ((v : ℝ) ^ 3) ^ (-2 * rho.1.re) := by
    have he : -2 * rho.1.re ≤ 0 := by linarith [NontrivialZetaZero.zero_lt_re rho]
    have hp1 : (p : ℝ) ^ (-2 * rho.1.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hpR he
    have hbase : (v : ℝ) ^ 3 ≤ (p : ℝ) ^ 2 * (v : ℝ) ^ 3 := by
      have hp2 : 1 ≤ (p : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hp2 (by positivity : 0 ≤ (v : ℝ) ^ 3)]
    have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (v : ℝ) ^ 3) hbase he
    simpa only [one_mul] using mul_le_mul hp1 h (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
  have hscale : (v : ℝ) ^ 3 * ((v : ℝ) ^ 3) ^ (-2 * rho.1.re) =
      (v : ℝ) ^ (3 - 6 * rho.1.re) := by
    have h := (Real.rpow_mul hv0.le 3 (-2 * rho.1.re)).symm
    norm_num only [Real.rpow_ofNat] at h
    rw [h, show 3 - 6 * rho.1.re = 3 + 3 * (-2 * rho.1.re) by ring,
      Real.rpow_add hv0, Real.rpow_ofNat]
  unfold pairedEtaMoebiusPrimeProductCubicEnergy
  rw [hA, hD]
  simp only [Nat.cast_mul, Nat.cast_pow] at hb ⊢
  apply hb.trans
  have hn := mul_le_mul hpow hmain (by positivity)
    (by positivity : 0 ≤ ((v : ℝ) ^ 3) ^ (-2 * rho.1.re))
  apply hn.trans_eq
  rw [pairedEtaMoebiusPrimeProductDecayConstant, ← hscale]
  ring

private theorem tendsto_log_square_mul_rpow_neg {a : ℝ} (ha : a < 0) :
    Tendsto (fun v : ℕ ↦ (1 + Real.log v) ^ 2 * (v : ℝ) ^ a) atTop (𝓝 0) := by
  have he : 0 < -a / 2 := by linarith
  have hp : Tendsto (fun v : ℕ ↦ (v : ℝ) ^ (a / 2)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop he).comp (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    ext v
    simp only [Function.comp_apply]
    congr 1
    ring
  have hl : Tendsto (fun v : ℕ ↦ Real.log v / (v : ℝ) ^ (-a / 2)) atTop (𝓝 0) := by
    convert (isLittleO_log_rpow_atTop he).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    ext v
    rfl
  have hz := (hp.add hl).pow 2
  simp only [add_zero, zero_pow (by norm_num : 2 ≠ 0)] at hz
  apply hz.congr'
  filter_upwards [eventually_ge_atTop 1] with v hv
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv
  have hi : (v : ℝ) ^ (a / 2) = ((v : ℝ) ^ (-a / 2))⁻¹ := by
    rw [show a / 2 = -(-a / 2) by ring, Real.rpow_neg hv0.le]
  have hs : ((v : ℝ) ^ (a / 2)) ^ 2 = (v : ℝ) ^ a := by
    rw [← Real.rpow_mul_natCast hv0.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  calc
    ((v : ℝ) ^ (a / 2) + Real.log v / (v : ℝ) ^ (-a / 2)) ^ 2 =
        (1 + Real.log v) ^ 2 * ((v : ℝ) ^ (a / 2)) ^ 2 := by rw [hi]; ring
    _ = _ := by rw [hs]

/-- The whole product family divisible by any fixed odd prime has vanishing mean square for a hypothetical right-half zero, on arbitrarily large original cubic windows. -/
theorem pairedEtaMoebiusPrimeProductCubicEnergy_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    Tendsto (pairedEtaMoebiusPrimeProductCubicEnergy rho p) atTop (𝓝 0) := by
  have hz := (tendsto_log_square_mul_rpow_neg
    (show 3 - 6 * rho.1.re < 0 by linarith)).const_mul (pairedEtaMoebiusPrimeProductDecayConstant rho p)
  simp only [mul_zero] at hz
  apply squeeze_zero' (Eventually.of_forall (fun v ↦ by
    unfold pairedEtaMoebiusPrimeProductCubicEnergy
    positivity)) ((eventually_ge_atTop 1).mono fun v hv ↦
      pairedEtaMoebiusPrimeProductCubicEnergy_le rho hp hodd hv)
  convert hz using 1
  ext v
  ring

end

end RiemannGaussian
