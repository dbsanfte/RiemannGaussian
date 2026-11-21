import RiemannGaussian.DyadicPrimeDeficit
import RiemannGaussian.SuzukiLocalCancellationPrimitiveBound
import RiemannGaussian.RosserSchoenfeldZeroTail

/-! # Estimates for the signed dyadic prime sum from increments of the explicit formula -/

namespace RiemannGaussian.DyadicPrime
noncomputable section
open Complex Set
open scoped Classical

private abbrev mass (ρ : NontrivialZetaZero) : ℝ := analyticZetaZeroMultiplicity ρ / ‖ρ.1‖^2

/-- The constant subtracted at logarithmic time zero cancels in the increment. -/
def zeroIncrement (a v : ℝ) (ρ : NontrivialZetaZero) : ℂ :=
  RosserSchoenfeldZeroPrimitive.term ρ (Real.log v) -
    RosserSchoenfeldZeroPrimitive.term ρ (Real.log a)

private theorem exp_norm_le {z : ℂ} {x n B : ℝ} (hx : 1 ≤ x) (hxn : x ≤ n)
    (hB : 0 ≤ B) (hz : z.re ≤ B) :
    ‖Complex.exp (z * (Real.log x : ℂ))‖ ≤ n ^ B := by
  rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  apply le_trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz (Real.log_nonneg hx)))
  rw [mul_comm B, ← Real.rpow_def_of_pos (zero_lt_one.trans_le hx)]
  exact Real.rpow_le_rpow (zero_le_one.trans hx) hxn hB

private theorem norm_zeroIncrement_le {a v n B : ℝ} (ha : 1 ≤ a) (hav : a ≤ v) (hvn : v ≤ n)
    (hB : 0 ≤ B) (ρ : NontrivialZetaZero) (hz : ρ.1.re ≤ B) :
    ‖zeroIncrement a v ρ‖ ≤ (2*n^B)*mass ρ := by
  have he : zeroIncrement a v ρ = ((analyticZetaZeroMultiplicity ρ : ℂ) / ρ.1^2) *
      (Complex.exp (ρ.1 * (Real.log v : ℂ)) - Complex.exp (ρ.1 * (Real.log a : ℂ))) := by
    unfold zeroIncrement RosserSchoenfeldZeroPrimitive.term RosserSchoenfeldZeroPrimitive.atom
    ring
  have h := (norm_sub_le (Complex.exp (ρ.1 * (Real.log v : ℂ))) (Complex.exp (ρ.1 * (Real.log a : ℂ)))).trans
    (add_le_add (exp_norm_le (ha.trans hav) hvn hB hz) (exp_norm_le ha (hav.trans hvn) hB hz))
  rw [he, norm_mul, norm_div, norm_pow, Complex.norm_natCast, mul_comm (2 * n ^ B)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

private theorem trivial_monotone {a v : ℝ} (ha : 1 ≤ a) (hav : a ≤ v) :
    (RosserSchoenfeldTrivialPrimitive.value (Real.log a)).re ≤
      (RosserSchoenfeldTrivialPrimitive.value (Real.log v)).re := by
  have hs {x : ℝ} (hx : 1 ≤ x) :=
    (RosserSchoenfeldTrivialPrimitive.summable_norm_term (Real.log_nonneg hx)).of_norm
  rw [RosserSchoenfeldTrivialPrimitive.value, RosserSchoenfeldTrivialPrimitive.value,
    Complex.re_tsum (hs ha), Complex.re_tsum (hs (ha.trans hav))]
  apply (Complex.reCLM.summable (hs ha)).tsum_le_tsum _ (Complex.reCLM.summable (hs (ha.trans hav)))
  intro k
  change (1-Real.exp (-2*((k:ℝ)+1)*Real.log a))/(4*((k:ℝ)+1)^2) ≤
    (1-Real.exp (-2*((k:ℝ)+1)*Real.log v))/(4*((k:ℝ)+1)^2)
  apply div_le_div_of_nonneg_right (sub_le_sub_left (Real.exp_le_exp.mpr _) 1) (by positivity)
  apply mul_le_mul_of_nonpos_left (Real.log_le_log (zero_lt_one.trans_le ha) hav)
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

private theorem deficit_formula {x : ℝ} (hx : 1 ≤ x) :
    primePrimitiveDeficit x = 1 + Real.log (2*Real.pi)*Real.log x +
      (RosserSchoenfeldZeroPrimitive.value (Real.log x)).re -
      (RosserSchoenfeldTrivialPrimitive.value (Real.log x)).re := by
  have he := congrArg Complex.re (RosserSchoenfeldExplicitFormula.prime_eq_spectral (Real.log_nonneg hx))
  rw [RosserSchoenfeldExplicitFormula.spectral, RosserSchoenfeldExplicitFormula.mainTerm_eq,
    Real.exp_log (zero_lt_one.trans_le hx)] at he
  simp only [Complex.add_re,Complex.sub_re,Complex.ofReal_re] at he
  unfold primePrimitiveDeficit
  linarith

private theorem sum_increment {a v : ℝ} (ha : 1 ≤ a) (hav : a ≤ v) :
    (∑' ρ, zeroIncrement a v ρ) = RosserSchoenfeldZeroPrimitive.value (Real.log v)
      - RosserSchoenfeldZeroPrimitive.value (Real.log a) :=
  (RosserSchoenfeldZeroPrimitive.summable_term (Real.log_nonneg (ha.trans hav))).tsum_sub
    (RosserSchoenfeldZeroPrimitive.summable_term (Real.log_nonneg ha))

/-- The exact integer prime shortfall is bounded by a single signed zero increment;
the complete trivial-zero contribution has favorable sign. -/
theorem exists_signed_increment {n : ℕ} (hn : 2 ≤ n) :
    ∃ v ∈ Icc ((n : ℝ)/2) (n : ℝ), dyadicPrimeError n ≤
      2*Real.log (2*Real.pi)*Real.log 2 + 2*(∑' ρ, zeroIncrement ((n : ℝ)/2) v ρ).re := by
  obtain ⟨v,hv,he⟩ := exists_primitive_increment hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 1 ≤ (n : ℝ)/2 := by linarith
  have hlog : Real.log v - Real.log ((n : ℝ)/2) ≤ Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num)]
    linarith [Real.log_le_log (zero_lt_one.trans_le (ha.trans hv.1)) hv.2]
  have hL := mul_le_mul_of_nonneg_left hlog (Real.log_nonneg (show 1 ≤ 2*Real.pi by linarith [Real.pi_gt_three]))
  refine ⟨v,hv,?_⟩
  rw [he, deficit_formula (ha.trans hv.1), deficit_formula ha, sum_increment ha hv.1, Complex.sub_re]
  rw [mul_sub] at hL
  linarith [trivial_monotone ha hv.1]

private theorem signed_increment_le_of_zero_bound {a v x B : ℝ}
    (ha : 1 ≤ a) (hav : a ≤ v) (hvx : v ≤ x) (hB : 0 ≤ B) (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) :
    (∑' ρ, zeroIncrement a v ρ).re ≤ (463/5000 : ℝ)*x^B := by
  have hx := (ha.trans hav).trans hvx
  have hs := RosserSchoenfeldZeroMass.norm_square_mass_summable.mul_left (2*x^B)
  have hb := fun ρ => norm_zeroIncrement_le ha hav hvx hB ρ (hz ρ)
  have hnorm := hs.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  have hsum := (Complex.re_le_norm _).trans ((norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum hb hs))
  rw [tsum_mul_left] at hsum
  have hmass := mul_le_mul_of_nonneg_left RosserSchoenfeldZeroMass.norm_square_mass_lt.le
    (show 0 ≤ 2*x^B by positivity)
  linarith

/-- A real-part bound controls the centered increment at any two specified sample locations. -/
theorem centered_increment_le_of_zero_bound {a v x B : ℝ} (ha : 1 ≤ a) (hav : a ≤ v) (hvx : v ≤ x)
    (hB : 0 ≤ B) (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) :
    primePrimitiveDeficit v - primePrimitiveDeficit a - Real.log (2*Real.pi)*(Real.log v - Real.log a) ≤
      (463/5000 : ℝ)*x^B := by
  have h := signed_increment_le_of_zero_bound ha hav hvx hB hz
  rw [sum_increment ha hav,Complex.sub_re] at h
  rw [deficit_formula (ha.trans hav),deficit_formula ha,mul_sub]
  linarith [trivial_monotone ha hav]

/-- The absolute zero mass in an increment costs 0.1852 times the power of the sample. -/
theorem dyadicPrimeError_le_of_zero_bound {B : ℝ} (hB : 0 ≤ B)
    (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) {n : ℕ} (hn : 2 ≤ n) :
    dyadicPrimeError n ≤ 2*Real.log (2*Real.pi)*Real.log 2 + (463/2500 : ℝ)*(n:ℝ)^B := by
  obtain ⟨v,hv,he⟩ := exists_signed_increment hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h := signed_increment_le_of_zero_bound (show 1 ≤ (n:ℝ)/2 by linarith) hv.1 hv.2 hB hz
  linarith

theorem dyadicPrimeError_le_seven_eighths {n : ℕ} (hn : 2 ≤ n) :
    dyadicPrimeError n ≤ 2*Real.log (2*Real.pi)*Real.log 2 + (463/2500 : ℝ)*(n:ℝ)^(7/8 : ℝ) :=
  dyadicPrimeError_le_of_zero_bound (by norm_num) suzukiLocalZero_re_le_seven_eighths hn


/-- The finite set whose signed contribution can exceed square-root scale. -/
def rightZeros (T : ℝ) : Finset NontrivialZetaZero :=
  (spectralZetaZeroWindow T).filter (fun ρ => 1/2 < ρ.1.re)

/-- Removing the finite right-half-plane sum leaves only critical-scale mass and an explicit height tail. -/
theorem signed_increment_truncation {a v x T : ℝ} (ha : 1 ≤ a) (hav : a ≤ v) (hvx : v ≤ x) (hT : 2 ≤ T) :
    (∑' ρ, zeroIncrement a v ρ).re ≤ (∑ ρ ∈ rightZeros T, zeroIncrement a v ρ).re +
      (463/5000 : ℝ)*Real.sqrt x + 2*x^(7/8 : ℝ)*((8+2*Real.log T)/T) := by
  let S := rightZeros T
  let f := zeroIncrement a v
  let U := 2*x^(7/8 : ℝ)
  have hx : 1 ≤ x := (ha.trans hav).trans hvx
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hc : Summable mass := RosserSchoenfeldZeroMass.norm_square_mass_summable
  have ht := RosserSchoenfeldZeroTail.summable_term T
  have hf : Summable (fun ρ => ‖f ρ‖) := (hc.mul_left U).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun ρ => norm_zeroIncrement_le ha hav hvx (by norm_num) ρ (suzukiLocalZero_re_le_seven_eighths ρ))
  have hpoint (ρ : ↥(S : Set NontrivialZetaZero)ᶜ) :
      ‖f ρ.1‖ ≤ (2 * Real.sqrt x) * mass ρ.1 + U * RosserSchoenfeldZeroTail.term T ρ.1 := by
    by_cases h : ρ.1.1.re ≤ 1/2
    · have hb := norm_zeroIncrement_le ha hav hvx (by norm_num) ρ.1 h
      rw [← Real.sqrt_eq_rpow] at hb
      exact hb.trans (le_add_of_nonneg_right (mul_nonneg hU (RosserSchoenfeldZeroTail.term_nonneg _ _)))
    · have hfar : T ≤ |ρ.1.1.im| := by
        by_contra! hsmall
        apply ρ.2
        exact Finset.mem_filter.mpr ⟨(mem_spectralZetaZeroWindow (by linarith : 0 ≤ T) _).mpr
          (by simpa only [zetaSpectralCoordinate_re] using hsmall.le), lt_of_not_ge h⟩
      rw [RosserSchoenfeldZeroTail.term, ite_eq_left hfar]
      exact (norm_zeroIncrement_le ha hav hvx (by norm_num) ρ.1 (suzukiLocalZero_re_le_seven_eighths _)).trans
        (le_add_of_nonneg_left (by dsimp [mass]; positivity))
  have hsc : Summable (fun ρ : ↥(S : Set NontrivialZetaZero)ᶜ => mass ρ.1) := hc.subtype _
  have hst : Summable (fun ρ : ↥(S : Set NontrivialZetaZero)ᶜ => RosserSchoenfeldZeroTail.term T ρ.1) := ht.subtype _
  have hsn := hf.subtype (· ∈ (S : Set NontrivialZetaZero)ᶜ)
  have he := hsn.tsum_le_tsum hpoint ((hsc.mul_left (2*Real.sqrt x)).add (hst.mul_left U))
  rw [(hsc.mul_left _).tsum_add (hst.mul_left _), tsum_mul_left, tsum_mul_left] at he
  have hm := (Summable.tsum_subtype_le mass (· ∈ (S : Set NontrivialZetaZero)ᶜ)
    (fun _ => by dsimp [mass]; positivity) hc).trans RosserSchoenfeldZeroMass.norm_square_mass_lt.le
  have hr := (Summable.tsum_subtype_le (RosserSchoenfeldZeroTail.term T) (· ∈ (S : Set NontrivialZetaZero)ᶜ)
    (RosserSchoenfeldZeroTail.term_nonneg T) ht).trans (RosserSchoenfeldZeroTail.value_le hT)
  have he' := he.trans (add_le_add (mul_le_mul_of_nonneg_left hm (by positivity)) (mul_le_mul_of_nonneg_left hr hU))
  have hsub := (Complex.re_le_norm _).trans ((norm_tsum_le_tsum_norm hsn).trans he')
  change (∑' ρ, f ρ).re ≤ (∑ ρ ∈ S, f ρ).re + _ + _
  rw [← hf.of_norm.sum_add_tsum_compl (s := S), Complex.add_re]
  dsimp [U] at hsub
  linarith

/-- Growing the height with the arithmetic sample pays the complete high-zero tail. -/
def cutoff (x : ℝ) : ℝ := 64 * x^(3/8 : ℝ) * (2 + Real.log x)

private theorem cutoff_budget {x : ℝ} (hx : 1 ≤ x) :
    2 ≤ cutoff x ∧ 2*x^(7/8 : ℝ)*((8+2*Real.log (cutoff x))/cutoff x) ≤ Real.sqrt x / 2 := by
  have hp := Real.one_le_rpow hx (by norm_num : (0 : ℝ) ≤ 3/8)
  have hl := Real.log_nonneg hx
  have hT : 2 ≤ cutoff x := by unfold cutoff; nlinarith [mul_nonneg (sub_nonneg.mpr hp) hl]
  refine ⟨hT,?_⟩
  have hx0 := zero_lt_one.trans_le hx
  have hxpow := Real.rpow_pos_of_pos hx0 (3/8 : ℝ)
  have hfactor : 0 < 2+Real.log x := by linarith
  have hlog64 : Real.log (64 : ℝ) ≤ 6 := by
    rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hlog : 8+2*Real.log (cutoff x) ≤ 16*(2+Real.log x) := by
    rw [cutoff, Real.log_mul (mul_pos (by norm_num) hxpow).ne' hfactor.ne',
      Real.log_mul (by norm_num) hxpow.ne', Real.log_rpow hx0]
    linarith [Real.log_le_sub_one_of_pos hfactor]
  rw [← mul_div_assoc, div_le_iff₀ (by linarith : 0 < cutoff x)]
  have he : x^(7/8 : ℝ) = Real.sqrt x * x^(3/8 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
    norm_num
  have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2*x^(7/8 : ℝ) by positivity)
  rw [he] at h ⊢
  apply h.trans_eq
  unfold cutoff
  ring

/-- At the sample-dependent cutoff, the infinite remainder is smaller than one square root. -/
theorem signed_increment_le_finite_add_sqrt {a v x : ℝ} (ha : 1 ≤ a) (hav : a ≤ v) (hvx : v ≤ x) :
    (∑' ρ, zeroIncrement a v ρ).re ≤
      (∑ ρ ∈ rightZeros (cutoff x), zeroIncrement a v ρ).re + Real.sqrt x := by
  obtain ⟨hT,hb⟩ := cutoff_budget ((ha.trans hav).trans hvx)
  have h := signed_increment_truncation ha hav hvx hT
  linarith [Real.sqrt_nonneg x]

/-- The centered prime primitive is controlled by only the low right-half-plane modes. -/
theorem centered_increment_le_finite_add_sqrt {a v x : ℝ} (ha : 1 ≤ a) (hav : a ≤ v) (hvx : v ≤ x) :
    primePrimitiveDeficit v - primePrimitiveDeficit a - Real.log (2*Real.pi)*(Real.log v - Real.log a) ≤
      (∑ ρ ∈ rightZeros (cutoff x), zeroIncrement a v ρ).re + Real.sqrt x := by
  have h := signed_increment_le_finite_add_sqrt ha hav hvx
  rw [sum_increment ha hav, Complex.sub_re] at h
  rw [deficit_formula (ha.trans hav), deficit_formula ha, mul_sub]
  linarith [trivial_monotone ha hav]

/-- On every integer sample all remaining error above the square-root scale is in a finite signed sum. -/
theorem dyadicPrimeError_le_finite_add_sqrt {n : ℕ} (hn : 2 ≤ n) :
    ∃ v ∈ Icc ((n:ℝ)/2) (n:ℝ), dyadicPrimeError n ≤
      2*Real.log (2*Real.pi)*Real.log 2 +
      2*(∑ ρ ∈ rightZeros (cutoff n), zeroIncrement ((n:ℝ)/2) v ρ).re + 2*Real.sqrt n := by
  obtain ⟨v,hv,he⟩ := exists_signed_increment hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ht := signed_increment_le_finite_add_sqrt (show 1 ≤ (n:ℝ)/2 by linarith) hv.1 hv.2
  refine ⟨v,hv,?_⟩
  linarith

end
end RiemannGaussian.DyadicPrime
