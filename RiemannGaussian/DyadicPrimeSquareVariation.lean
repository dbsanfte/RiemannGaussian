import RiemannGaussian.DyadicPrimeSquareSamples

/-! # Local variation of the exact square-sampled prime error -/

namespace RiemannGaussian.DyadicPrime
noncomputable section
open Complex
open scoped Classical

private abbrev zeroMass (ρ : NontrivialZetaZero) : ℝ :=
  analyticZetaZeroMultiplicity ρ / ‖ρ.1‖^2

/-- The reciprocal-square zero mass weighted by the ordinate clipped at height `T`. -/
def clippedWeight (T : ℝ) (ρ : NontrivialZetaZero) : ℝ :=
  (1 + min |ρ.1.im| T) * zeroMass ρ

private theorem summable_clipped {T : ℝ} (hT : 0 ≤ T) : Summable (clippedWeight T) := by
  apply (RosserSchoenfeldZeroMass.norm_square_mass_summable.mul_left (1+T)).of_nonneg_of_le
  · intro ρ
    exact mul_nonneg (by linarith [le_min (abs_nonneg ρ.1.im) hT]) (by positivity)
  · intro ρ
    exact mul_le_mul_of_nonneg_right (add_le_add_right (min_le_right _ _) _) (by positivity)

private theorem clipped_step {T : ℝ} (hT : 2 ≤ T) :
    (∑' ρ, clippedWeight (2*T) ρ) ≤ (∑' ρ, clippedWeight T ρ) + (8+2*Real.log T) := by
  have hpoint (ρ : NontrivialZetaZero) :
      clippedWeight (2*T) ρ ≤ clippedWeight T ρ + T * RosserSchoenfeldZeroTail.term T ρ := by
    unfold clippedWeight RosserSchoenfeldZeroTail.term
    by_cases h : T ≤ |ρ.1.im|
    · rw [ite_eq_left h, min_eq_right h]
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (by linarith [min_le_right |ρ.1.im| (2*T)]) (by positivity)
    · rw [ite_eq_right h,min_eq_left (le_of_not_ge h),min_eq_left (by linarith : |ρ.1.im| ≤ 2*T)]
      simp
  have ha := summable_clipped (show 0 ≤ T by linarith)
  have hb := (RosserSchoenfeldZeroTail.summable_term T).mul_left T
  have hs := (summable_clipped (show 0 ≤ 2*T by linarith)).tsum_le_tsum hpoint (ha.add hb)
  rw [ha.tsum_add hb,tsum_mul_left] at hs
  have ht := (le_div_iff₀ (show 0 < T by linarith)).mp (RosserSchoenfeldZeroTail.value_le hT)
  change (∑' ρ, RosserSchoenfeldZeroTail.term T ρ)*T ≤ _ at ht
  linarith

/-- The full clipped reciprocal-square moment grows at most quadratically in the dyadic index. -/
theorem clippedWeight_dyadic_le (J : ℕ) :
    (∑' ρ, clippedWeight (2^(J+1)) ρ) ≤ 8*((J:ℝ)+1)^2 := by
  induction J with
  | zero =>
    norm_num
    have h := (summable_clipped (by norm_num : (0:ℝ) ≤ 2)).tsum_le_tsum (g := fun ρ => 3*zeroMass ρ)
      (fun ρ => mul_le_mul_of_nonneg_right (by linarith [min_le_right |ρ.1.im| (2:ℝ)]) (by positivity))
      (RosserSchoenfeldZeroMass.norm_square_mass_summable.mul_left 3)
    rw [tsum_mul_left] at h
    change (∑' ρ, clippedWeight 2 ρ) ≤ 3 * ∑' ρ, zeroMass ρ at h
    have hm : (∑' ρ, zeroMass ρ) < 463/10000 := RosserSchoenfeldZeroMass.norm_square_mass_lt
    exact h.trans (by linarith)
  | succ J ih =>
    have ht : (2:ℝ) ≤ 2^(J+1) := by rw [pow_succ]; linarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := J)]
    have hs := clipped_step ht
    rw [Real.log_pow, Nat.cast_add_one] at hs
    rw [pow_succ (2:ℝ) (J+1),mul_comm _ 2,Nat.cast_succ]
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    nlinarith only [ih,hs,mul_le_mul_of_nonneg_left hl (show 0 ≤ (J:ℝ)+1 by positivity),
      Nat.cast_nonneg (α := ℝ) J]

private theorem norm_one_sub_exp_le {z : ℂ} (hz : z.re ≤ 0) :
    ‖1 - Complex.exp z‖ ≤ 2*‖z‖ := by
  rw [norm_sub_rev]
  by_cases h : ‖z‖ ≤ 1
  · exact Complex.norm_exp_sub_one_le h
  · have he : ‖Complex.exp z‖ ≤ 1 := by rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr hz
    have hs := norm_sub_le (Complex.exp z) 1
    rw [norm_one] at hs
    linarith

private theorem local_zero_bound {B a v T : ℝ} (hB : 0 ≤ B) (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) (ha : 1 ≤ a) (hav : a ≤ v) (hT : 2 ≤ T)
    (ρ : NontrivialZetaZero) :
    ‖zeroIncrement a v ρ‖ ≤ (2*v^B) *
      ((Real.log v - Real.log a)*clippedWeight T ρ + RosserSchoenfeldZeroTail.term T ρ) := by
  let u := Real.log v
  let t := Real.log a
  have hgap : 0 ≤ u-t := sub_nonneg.mpr (Real.log_le_log (by linarith) hav)
  have hex (x : ℝ) (hx : 0 ≤ x) (hxu : x ≤ u) :
      ‖Complex.exp (ρ.1 * (x:ℂ))‖ ≤ v^B := by
    rw [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
      Real.rpow_def_of_pos (by linarith : 0 < v)]
    exact Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_right (hz ρ) hx).trans
      (by dsimp [u] at hxu; nlinarith only [mul_le_mul_of_nonneg_left hxu hB]))
  have hnorm : ‖zeroIncrement a v ρ‖ = zeroMass ρ *
      ‖Complex.exp (ρ.1*(u:ℂ))-Complex.exp (ρ.1*(t:ℂ))‖ := by
    have he : zeroIncrement a v ρ = ((analyticZetaZeroMultiplicity ρ : ℂ) / ρ.1^2) *
        (Complex.exp (ρ.1*(u:ℂ))-Complex.exp (ρ.1*(t:ℂ))) := by
      unfold zeroIncrement RosserSchoenfeldZeroPrimitive.term RosserSchoenfeldZeroPrimitive.atom
      dsimp [u,t]
      ring
    rw [he,norm_mul,norm_div,norm_pow,Complex.norm_natCast]
  have hp : 0 ≤ (Real.log v - Real.log a)*clippedWeight T ρ :=
    mul_nonneg hgap (mul_nonneg (by linarith [le_min (abs_nonneg ρ.1.im) (by linarith : 0 ≤ T)])
      (by positivity))
  have hmass : 0 ≤ zeroMass ρ := by positivity
  have hvp : 0 ≤ v^B := Real.rpow_nonneg (by linarith) _
  rw [hnorm]
  by_cases hhigh : T ≤ |ρ.1.im|
  · have he := (norm_sub_le (Complex.exp (ρ.1*(u:ℂ))) (Complex.exp (ρ.1*(t:ℂ)))).trans
      (add_le_add (hex u (Real.log_nonneg (ha.trans hav)) le_rfl) (hex t (Real.log_nonneg ha) (by linarith)))
    rw [RosserSchoenfeldZeroTail.term,ite_eq_left hhigh]
    change _ ≤ (2*v^B)*(_ + zeroMass ρ)
    nlinarith only [mul_le_mul_of_nonneg_left he hmass,mul_nonneg hvp hp]
  · let z := ρ.1*((t-u:ℝ):ℂ)
    have hz : z.re ≤ 0 := by
      simp only [z,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (NontrivialZetaZero.zero_lt_re ρ).le (by linarith)
    have hf : Complex.exp (ρ.1*(u:ℂ))-Complex.exp (ρ.1*(t:ℂ)) =
        Complex.exp (ρ.1*(u:ℂ))*(1-Complex.exp z) := by
      rw [mul_sub,mul_one,← Complex.exp_add]
      dsimp [z]
      push_cast
      ring_nf
    have hzn : ‖z‖ ≤ (1+|ρ.1.im|)*(u-t) := by
      rw [show ‖z‖ = ‖ρ.1‖*(u-t) by
        rw [show z = ρ.1*((t-u:ℝ):ℂ) from rfl,norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonpos (show t-u ≤ 0 by linarith),neg_sub]]
      apply mul_le_mul_of_nonneg_right _ hgap
      have hh := Complex.norm_le_abs_re_add_abs_im ρ.1
      rw [abs_of_pos (NontrivialZetaZero.zero_lt_re ρ)] at hh
      linarith [NontrivialZetaZero.re_lt_one ρ]
    have he := mul_le_mul (hex u (Real.log_nonneg (ha.trans hav)) le_rfl)
      ((norm_one_sub_exp_le hz).trans (by linarith : 2*‖z‖ ≤ 2*((1+|ρ.1.im|)*(u-t))))
      (norm_nonneg _) hvp
    rw [hf,norm_mul,RosserSchoenfeldZeroTail.term,ite_eq_right hhigh,add_zero,
      clippedWeight,min_eq_left (le_of_not_ge hhigh)]
    change _ ≤ (2*v^B)*((u-t)*((1+|ρ.1.im|)*zeroMass ρ))
    exact (mul_le_mul_of_nonneg_left he hmass).trans_eq (by ring)

/-- Variation of the complete signed zero sum on a logarithmic interval, with a free dyadic cutoff. -/
theorem norm_zeroIncrement_dyadic_le_of_re_le {B a v : ℝ} (hB : 0 ≤ B)
    (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) (ha : 1 ≤ a) (hav : a ≤ v) (J : ℕ) :
    ‖∑' ρ, zeroIncrement a v ρ‖ ≤ (2*v^B) *
      ((Real.log v - Real.log a)*(8*((J:ℝ)+1)^2) +
        (8+2*Real.log (2^(J+1):ℝ))/2^(J+1)) := by
  let T : ℝ := 2^(J+1)
  have ht : 2 ≤ T := by dsimp [T]; rw [pow_succ]; linarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := J)]
  have hfac : 0 ≤ 2*v^B := mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)
  have hgap := sub_nonneg.mpr (Real.log_le_log (by linarith : 0 < a) hav)
  have hc := (summable_clipped (show 0 ≤ T by linarith)).mul_left (Real.log v - Real.log a)
  have hh := RosserSchoenfeldZeroTail.summable_term T
  have hm := (hc.add hh).mul_left (2*v^B)
  have hp := local_zero_bound hB hz ha hav ht
  have hs := hm.of_nonneg_of_le (fun _ => norm_nonneg _) hp
  have hb := (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hp hm)
  rw [tsum_mul_left,hc.tsum_add hh,tsum_mul_left] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (clippedWeight_dyadic_le J) hgap)
      (RosserSchoenfeldZeroTail.value_le ht)) hfac)

/-- The dyadic zero-increment estimate specialized to the verified seven-eighths half-plane. -/
theorem norm_zeroIncrement_dyadic_le {a v : ℝ} (ha : 1 ≤ a) (hav : a ≤ v) (J : ℕ) :
    ‖∑' ρ, zeroIncrement a v ρ‖ ≤ (2*v^(7/8:ℝ)) *
      ((Real.log v - Real.log a)*(8*((J:ℝ)+1)^2) +
        (8+2*Real.log (2^(J+1):ℝ))/2^(J+1)) :=
  norm_zeroIncrement_dyadic_le_of_re_le (by norm_num) suzukiLocalZero_re_le_seven_eighths ha hav J

private theorem primeError_eq_spectral {x : ℝ} (hx : 1 ≤ x) :
    QuasiRHPrimeWindowBounds.primeError x =
      (RosserSchoenfeldZeroPrimitive.value (Real.log x)).re -
      (RosserSchoenfeldTrivialPrimitive.value (Real.log x)).re := by
  have he := congrArg Complex.re (RosserSchoenfeldExplicitFormula.prime_eq_spectral (Real.log_nonneg hx))
  rw [RosserSchoenfeldExplicitFormula.spectral, RosserSchoenfeldExplicitFormula.mainTerm_eq,
    Real.exp_log (zero_lt_one.trans_le hx)] at he
  simp only [Complex.add_re,Complex.sub_re,Complex.ofReal_re] at he
  unfold QuasiRHPrimeWindowBounds.primeError
  linarith

/-- Two-sided variation of the actual centered prime sum between any two given cutoffs. -/
theorem primeError_dyadic_variation_of_re_le {B a v : ℝ} (hB : 0 ≤ B)
    (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) (ha : 1 ≤ a) (hav : a ≤ v) (J : ℕ) :
    |QuasiRHPrimeWindowBounds.primeError v - QuasiRHPrimeWindowBounds.primeError a| ≤
      Real.pi^2/12 + (2*v^B) * ((Real.log v - Real.log a)*(8*((J:ℝ)+1)^2) +
        (8+2*Real.log (2^(J+1):ℝ))/2^(J+1)) := by
  have hsum : (∑' ρ, zeroIncrement a v ρ) = RosserSchoenfeldZeroPrimitive.value (Real.log v)
      - RosserSchoenfeldZeroPrimitive.value (Real.log a) :=
    (RosserSchoenfeldZeroPrimitive.summable_term (Real.log_nonneg (ha.trans hav))).tsum_sub
      (RosserSchoenfeldZeroPrimitive.summable_term (Real.log_nonneg ha))
  have hv := norm_zeroIncrement_dyadic_le_of_re_le hB hz ha hav J
  have ht {x : ℝ} (hx : 1 ≤ x) := (Complex.abs_re_le_norm _).trans
    (RosserSchoenfeldTrivialPrimitive.norm_value_le (Real.log_nonneg hx))
  have hz := (Complex.abs_re_le_norm _).trans hv
  rw [hsum,Complex.sub_re] at hz
  rw [primeError_eq_spectral (ha.trans hav),primeError_eq_spectral ha]
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hz).1,(abs_le.mp (ht (ha.trans hav))).2,(abs_le.mp (ht ha)).1],
    by linarith [(abs_le.mp hz).2,(abs_le.mp (ht (ha.trans hav))).1,(abs_le.mp (ht ha)).2]⟩

/-- The unconditional dyadic variation of the actual centered prime sum. -/
theorem primeError_dyadic_variation {a v : ℝ} (ha : 1 ≤ a) (hav : a ≤ v) (J : ℕ) :
    |QuasiRHPrimeWindowBounds.primeError v - QuasiRHPrimeWindowBounds.primeError a| ≤
      Real.pi^2/12 + (2*v^(7/8:ℝ)) * ((Real.log v - Real.log a)*(8*((J:ℝ)+1)^2) +
        (8+2*Real.log (2^(J+1):ℝ))/2^(J+1)) :=
  primeError_dyadic_variation_of_re_le (by norm_num) suzukiLocalZero_re_le_seven_eighths ha hav J

/-- The variation bound holds for real square roots and every intervening real cutoff. -/
theorem real_square_variation {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2*x) :
    |QuasiRHPrimeWindowBounds.primeError (y^2)-QuasiRHPrimeWindowBounds.primeError (x^2)| ≤
      Real.pi^2/12 + 208*(y-x+1)*x^(3/4:ℝ)*(1+Real.log x/Real.log 2)^2 := by
  have hx0 := zero_lt_one.trans_le hx
  obtain ⟨J,hlo,hhi⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ) < 2)
  let T : ℝ := 2^(J+1)
  let L : ℝ := 1+Real.log x/Real.log 2
  have hL : 1 ≤ L := by dsimp [L]; linarith [div_nonneg (Real.log_nonneg hx) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))]
  have hJ : (J:ℝ)+1 ≤ L := by
    have hl := Real.log_le_log (by positivity : 0 < (2:ℝ)^J) hlo
    rw [Real.log_pow] at hl
    dsimp [L]
    linarith [(le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr hl]
  have ht : Real.log T ≤ L := by
    dsimp [T]
    rw [Real.log_pow,Nat.cast_succ]
    nlinarith only [hJ,mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2))
      (show 0 ≤ (J:ℝ)+1 by positivity)]
  have hd : 0 ≤ y-x := sub_nonneg.mpr hxy
  have hgap : Real.log (y^2) - Real.log (x^2) ≤ 2*(y-x)/x := by
    rw [Real.log_pow,Real.log_pow]
    have h := Real.log_le_sub_one_of_pos (div_pos (hx0.trans_le hxy) hx0)
    rw [Real.log_div (hx0.trans_le hxy).ne' hx0.ne'] at h
    simpa only [Nat.cast_ofNat] using (show (2:ℝ)*Real.log y-2*Real.log x ≤ 2*(y-x)/x by
      rw [mul_div_assoc,sub_div,div_self hx0.ne']; linarith)
  have hbase : (y^2)^(7/8:ℝ) ≤ 4*x^(7/4:ℝ) := by
    rw [← Real.rpow_natCast_mul (hx0.trans_le hxy).le]
    norm_num
    calc
      y^(7/4:ℝ) ≤ (2*x)^(7/4:ℝ) := Real.rpow_le_rpow (hx0.trans_le hxy).le hy (by norm_num)
      _ = (2:ℝ)^(7/4:ℝ)*x^(7/4:ℝ) := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        calc
          (2:ℝ)^(7/4:ℝ) ≤ 2^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 4 := by norm_num) (by positivity)
  have htail : (8+2*Real.log T)/T ≤ (10*L^2)/x := by
    calc
      _ ≤ (10*L^2)/T := by
        apply div_le_div_of_nonneg_right _ (by dsimp [T]; positivity)
        nlinarith [sq_nonneg (L-1)]
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hx0 hhi.le
  have hlow := mul_le_mul hgap (show 8*((J:ℝ)+1)^2 ≤ 8*L^2 by
    nlinarith [sq_le_sq' (by linarith : -L ≤ (J:ℝ)+1) hJ]) (by positivity)
    (div_nonneg (by linarith) hx0.le)
  have hc : Real.log (y^2) - Real.log (x^2) ≥ 0 :=
    sub_nonneg.mpr (Real.log_le_log (by positivity) (by nlinarith))
  have ht0 : 0 ≤ Real.log T := Real.log_nonneg (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hs := primeError_dyadic_variation (a := x^2) (v := y^2) (by nlinarith) (by nlinarith) J
  change |QuasiRHPrimeWindowBounds.primeError (y^2)-QuasiRHPrimeWindowBounds.primeError (x^2)| ≤ Real.pi^2/12 + (2*(y^2)^(7/8:ℝ)) *
    ((Real.log (y^2)-Real.log (x^2))*(8*((J:ℝ)+1)^2)+(8+2*Real.log T)/T) at hs
  have hcost := add_le_add hlow htail
  have htpos : 0 < T := by dsimp [T]; positivity
  have hpos : 0 ≤ 2*(y-x)/x*(8*L^2)+(10*L^2)/x := by positivity
  have hmul := mul_le_mul (by linarith : 2*(y^2)^(7/8:ℝ) ≤ 8*x^(7/4:ℝ))
    hcost (by positivity) (by positivity : 0 ≤ 8*x^(7/4:ℝ))
  have hp : x^(7/4:ℝ) = x^(3/4:ℝ)*x := by
    rw [show (7/4:ℝ) = 3/4+1 by norm_num,Real.rpow_add hx0,Real.rpow_one]
  have hred : 8*x^(7/4:ℝ)*(2*(y-x)/x*(8*L^2)+10*L^2/x) =
      (128*(y-x)+80)*x^(3/4:ℝ)*L^2 := by rw [hp]; field_simp; ring
  rw [hred] at hmul
  change _ ≤ Real.pi^2/12 + 208*(y-x+1)*x^(3/4:ℝ)*L^2
  exact hs.trans (add_le_add_right (hmul.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (sq_nonneg _))) _)

/-- Square spacing changes the physical power from `7/4` to `3/4` in the root index. -/
theorem squareError_variation {m k : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) (hk : k ≤ 2*m) :
    |squareError k - squareError m| ≤ Real.pi^2/12 +
      208*((k:ℝ)-m+1)*(m:ℝ)^(3/4:ℝ)*(1+Real.log m/Real.log 2)^2 :=
  real_square_variation (by exact_mod_cast hm) (by exact_mod_cast hmk) (by exact_mod_cast hk)

/-- Uniform two-sided variation for the signed difference between the full and half-index squares. -/
theorem squareError_increment_variation {m j : ℕ} (hm : 2 ≤ m) (hj : j ≤ m/2) :
    |(squareError (m+j)-squareError ((m+j)/2)) - (squareError m-squareError (m/2))| ≤
      Real.pi^2/6 + 416*((j:ℝ)+1)*(m:ℝ)^(3/4:ℝ)*(1+Real.log m/Real.log 2)^2 := by
  have htop := squareError_variation (m := m) (k := m+j) (by omega) (by omega) (by omega)
  have hbot := squareError_variation (m := m/2) (k := (m+j)/2) (by omega) (by omega) (by omega)
  have hmpos : (0:ℝ) < (m/2:ℕ) := by exact_mod_cast (show 0 < m/2 by omega)
  have hmone : (1:ℝ) ≤ (m/2:ℕ) := by exact_mod_cast (show 1 ≤ m/2 by omega)
  have hsmall : ((m/2:ℕ):ℝ) ≤ m := by exact_mod_cast Nat.div_le_self m 2
  have hgap : (((m+j)/2:ℕ):ℝ) ≤ ((m/2:ℕ):ℝ)+j := by exact_mod_cast (show (m+j)/2 ≤ m/2+j by omega)
  have hp := Real.rpow_le_rpow hmpos.le hsmall (by norm_num : (0:ℝ) ≤ 3/4)
  have hl := div_le_div_of_nonneg_right (Real.log_le_log hmpos hsmall) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  have hl0 := div_nonneg (Real.log_nonneg hmone) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  have hsq := sq_le_sq' (by linarith : -(1+Real.log m/Real.log 2) ≤ 1+Real.log (m/2:ℕ)/Real.log 2)
    (by linarith : 1+Real.log (m/2:ℕ)/Real.log 2 ≤ 1+Real.log m/Real.log 2)
  have hbound : 208*((((m+j)/2:ℕ):ℝ)-(m/2:ℕ)+1)*((m/2:ℕ):ℝ)^(3/4:ℝ)*(1+Real.log (m/2:ℕ)/Real.log 2)^2 ≤
      208*((j:ℝ)+1)*(m:ℝ)^(3/4:ℝ)*(1+Real.log m/Real.log 2)^2 := by
    apply mul_le_mul _ hsq (sq_nonneg _) (by positivity)
    exact mul_le_mul (by linarith) hp (by positivity) (by positivity)
  rw [Nat.cast_add,add_sub_cancel_left] at htop
  exact abs_le.mpr ⟨by linarith [(abs_le.mp htop).1,(abs_le.mp hbot).2],
    by linarith [(abs_le.mp htop).2,(abs_le.mp hbot).1]⟩

open Filter

/-- Throughout every interval of root indices of length `m^δ`, for `0 ≤ δ < 1/4`,
the actual dyadic increment varies by `o(m)`, uniformly over the starting index. -/
theorem eventually_small_increment_variation {δ ε : ℝ} (hδ : 0 ≤ δ) (hq : δ < 1/4) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ j : ℕ, (j:ℝ) ≤ (m:ℝ)^δ →
      |(squareError (m+j)-squareError ((m+j)/2)) - (squareError m-squareError (m/2))| ≤ ε*m := by
  let s := (1/4-δ)/4
  let A := 1+(1/s)/Real.log 2
  let b := δ+3/4+2*s
  let C := Real.pi^2/6+832*A^2
  have hs : 0 < s := by dsimp [s]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hlog2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hbig {p : ℝ} (hp : 0 < p) (c : ℝ) :
      ∀ᶠ m : ℕ in atTop, c ≤ (m:ℝ)^p :=
    ((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c
  filter_upwards [eventually_ge_atTop 2, hbig (by linarith : 0 < 1-δ) 2,
    hbig (by linarith : 0 < 2*s) (C/ε)] with m hm hhalf hbudget
  intro j hj
  let x : ℝ := m
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ m by omega)
  have hx0 := zero_lt_one.trans_le hx
  have hprod : x^δ * x^(1-δ) = x := by rw [← Real.rpow_add hx0]; simp
  have hxp := Real.rpow_nonneg hx0.le δ
  have hhalf' : (2:ℝ)*(j:ℝ) ≤ x := calc
    _ ≤ x^δ*2 := by linarith
    _ ≤ x^δ*x^(1-δ) := mul_le_mul_of_nonneg_left hhalf hxp
    _ = x := hprod
  have hjhalf : j ≤ m/2 := by
    have hn : 2*j ≤ m := by change (2:ℝ)*(j:ℝ) ≤ m at hhalf'; exact_mod_cast hhalf'
    omega
  have hbnd := squareError_increment_variation hm hjhalf
  have h1s := Real.one_le_rpow hx hs.le
  have h1δ := Real.one_le_rpow hx hδ
  have h1b := Real.one_le_rpow hx hb
  have hj' : (j:ℝ)+1 ≤ 2*x^δ := by change (j:ℝ) ≤ x^δ at hj; linarith
  have hl : 1+Real.log x/Real.log 2 ≤ A*x^s := by
    have h := div_le_div_of_nonneg_right (Real.log_le_rpow_div hx0.le hs) hlog2.le
    dsimp [A]
    calc
      _ ≤ x^s + (x^s/s)/Real.log 2 := add_le_add h1s h
      _ = _ := by ring
  have hl0 : 0 ≤ 1+Real.log x/Real.log 2 := by linarith [div_nonneg (Real.log_nonneg hx) hlog2.le]
  have hls := sq_le_sq' (by linarith : -(A*x^s) ≤ 1+Real.log x/Real.log 2) hl
  have hcost : 416*((j:ℝ)+1)*x^(3/4:ℝ)*(1+Real.log x/Real.log 2)^2 ≤
      832*A^2*x^b := by
    calc
      _ ≤ 416*(2*x^δ)*x^(3/4:ℝ)*(A*x^s)^2 := by
        apply mul_le_mul _ hls (sq_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj' (by norm_num)) (by positivity)
      _ = 832*A^2*(x^δ*x^(3/4:ℝ)*(x^s*x^s)) := by ring
      _ = _ := by simp only [← Real.rpow_add hx0]; dsimp [b]; ring_nf
  have htotal : Real.pi^2/6 + 832*A^2*x^b ≤ C*x^b := by
    dsimp [C]
    nlinarith only [mul_le_mul_of_nonneg_left h1b (by positivity : 0 ≤ Real.pi^2/6)]
  have he : x^b*x^(2*s) = x := by
    rw [← Real.rpow_add hx0,show b+2*s = 1 by dsimp [b,s]; ring,Real.rpow_one]
  have hpay : C*x^b ≤ ε*x := calc
    _ ≤ (x^(2*s)*ε)*x^b := mul_le_mul_of_nonneg_right ((div_le_iff₀ hε).mp hbudget) (by positivity)
    _ = ε*(x^b*x^(2*s)) := by ring
    _ = ε*x := by rw [he]
  exact hbnd.trans ((add_le_add_right hcost _).trans (htotal.trans hpay))

/-- Every sufficiently late power window contains a starting index for a whole polynomial-width
block satisfying the prescribed one-sided linear allowance. -/
theorem eventually_power_block_squareError_increment {δ ε : ℝ} (hδ : 0 ≤ δ) (hq : δ < 1/4)
    (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∃ m ∈ Set.Icc M (M^32), ∀ j : ℕ, (j:ℝ) ≤ (m:ℝ)^δ →
      squareError (m+j) - squareError ((m+j)/2) ≤ ε*(m+j : ℕ) := by
  obtain ⟨b,hb⟩ := eventually_atTop.mp (eventually_small_increment_variation hδ hq (half_pos hε))
  filter_upwards [eventually_small_increment_in_power_window (half_pos hε),
    eventually_ge_atTop b] with M ⟨m,hm,he⟩ hM
  refine ⟨m,hm,fun j hj => ?_⟩
  have h := (abs_le.mp (hb m (hM.trans hm.1) j hj)).2
  rw [Nat.cast_add]
  nlinarith only [he,h,mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) j)]

/-- One good arithmetic observation in every sufficiently late interval of length `m^δ`
suffices. The location of the observation may depend on the interval. -/
theorem rh_iff_eventually_good_power_intervals {δ : ℝ} (hδ : 0 ≤ δ) (hq : δ < 1/4) :
    RiemannHypothesis ↔ ∀ᶠ m : ℕ in atTop, ∃ j : ℕ, (j:ℝ) ≤ (m:ℝ)^δ ∧
      squareError (m+j) - squareError ((m+j)/2) ≤ ((m+j:ℕ):ℝ)/10 := by
  constructor
  · intro h
    filter_upwards [eventually_ge_atTop 2] with m hm
    exact ⟨0,by simpa using Real.rpow_nonneg (Nat.cast_nonneg m) δ,
      by simpa using rh_iff_squareError_increment_le_tenth.mp h m hm⟩
  · intro h
    have he : ∀ᶠ m : ℕ in atTop, squareError m-squareError (m/2) ≤ 2*(m:ℝ) := by
      filter_upwards [h,eventually_small_increment_variation hδ hq (by norm_num : (0:ℝ) < 1),
        eventually_ge_atTop 2] with m ⟨j,hj,hgood⟩ hv hm
      have hx : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      have hjm := hj.trans ((Real.rpow_le_rpow_of_exponent_le hx (by linarith : δ ≤ 1)).trans_eq
        (Real.rpow_one _))
      have hb := (abs_le.mp (hv j hj)).1
      rw [Nat.cast_add] at hgood
      linarith
    obtain ⟨b,hb⟩ := eventually_atTop.mp he
    let K := ∑ m ∈ Finset.range b, |squareError m-squareError (m/2)|
    have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    apply rh_of_squareError_increment (C := 2+K) (by linarith)
    intro m hm
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    by_cases hmb : b ≤ m
    · exact (hb m hmb).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    · have hsmall : |squareError m-squareError (m/2)| ≤ K :=
        Finset.single_le_sum (f := fun n => |squareError n-squareError (n/2)|)
          (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))
      nlinarith only [hsmall,le_abs_self (squareError m-squareError (m/2)),hm1,
        mul_le_mul_of_nonneg_left hm1 hK]

end
end RiemannGaussian.DyadicPrime
