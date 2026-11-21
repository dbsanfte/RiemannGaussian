import RiemannGaussian.AlpogeZetaPowerWindows
import RiemannGaussian.RosserSchoenfeldDesmoothing

/-! # Pointwise Chebyshev estimates from increments of the zero sum -/

namespace RiemannGaussian.PrimeMassFromZeroBound
noncomputable section
open Real Filter

private def envelope (B x : ℝ) : ℝ := x^B*(1+log x/log 2)^2

private theorem sqrt_le_envelope {x B : ℝ} (hx : 1 ≤ x) (hB : 1/2 ≤ B) :
    sqrt x ≤ envelope B x := by
  have hp := Real.rpow_le_rpow_of_exponent_le hx hB
  rw [← Real.sqrt_eq_rpow] at hp
  apply hp.trans
  apply le_mul_of_one_le_right (Real.rpow_nonneg (zero_le_one.trans hx) _)
  exact one_le_pow₀ (by linarith [div_nonneg (Real.log_nonneg hx) (Real.log_pos (by norm_num : (1:ℝ)<2)).le])

private theorem envelope_mono {x y B : ℝ} (hx : 1 ≤ x) (hy : x ≤ y) (hB : 0 ≤ B) :
    envelope B x ≤ envelope B y := by
  have hl := Real.log_le_log (zero_lt_one.trans_le hx) hy
  have hd : 0 < log 2 := log_pos (by norm_num)
  have hx0 := zero_le_one.trans hx
  have hL : 0 ≤ 1+log x/log 2 := by positivity [Real.log_nonneg hx]
  exact mul_le_mul (Real.rpow_le_rpow hx0 hy hB)
    (pow_le_pow_left₀ hL (add_le_add_right (div_le_div_of_nonneg_right hl hd.le) _) _)
    (sq_nonneg _) (Real.rpow_nonneg (hx0.trans hy) _)

private abbrev K : ℝ := 288 + Real.pi^2/6
private abbrev c : ℝ := log (2*Real.pi)

private theorem secant {B a b : ℝ} (hB : 1/2 ≤ B) (hB1 : B ≤ 1)
    (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B)
    (ha : 1 ≤ a) (hs : sqrt a ≤ b-a) (hb : b ≤ 2*a) :
    Chebyshev.psi a + c ≤ b + K*envelope B a ∧ a-K*envelope B a ≤ Chebyshev.psi b+c := by
  have ha0 := zero_lt_one.trans_le ha
  have hab : a < b := by linarith [Real.sqrt_pos.mpr ha0]
  have hb0 := ha0.trans hab
  let d := log b-log a
  let M := envelope B a
  have hd : 0 < d := sub_pos.mpr (Real.log_lt_log ha0 hab)
  have hM : sqrt a ≤ M := sqrt_le_envelope ha hB
  have hM0 := (sqrt_nonneg a).trans hM
  have h1 : 1 ≤ b-a := (Real.one_le_sqrt.mpr ha).trans hs
  have hm : a ≤ (b-a)*M := by
    calc a = sqrt a * sqrt a := (Real.mul_self_sqrt ha0.le).symm
         _ ≤ _ := mul_le_mul hs hM (sqrt_nonneg a) (by linarith)
  have hlo : d*a ≤ b-a := by
    have hh := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    rw [Real.log_div hb0.ne' ha0.ne'] at hh
    exact (le_div_iff₀ ha0).mp (show d ≤ (b-a)/a by rwa [sub_div,div_self ha0.ne'])
  have hhi : b-a ≤ d*b := by
    have hh := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    rw [Real.log_div ha0.ne' hb0.ne'] at hh
    have htmp : a/b ≥ 1-d := by dsimp [d]; linarith
    linarith only [(le_div_iff₀ hb0).mp htmp]
  have hratio : (b-a)/a ≤ 2*d := (div_le_iff₀ ha0).mpr (by
    linarith only [hhi,mul_le_mul_of_nonneg_left hb hd.le])
  have hnorm : 1 ≤ 2*d*M := by
    have hh : 1 ≤ (b-a)/a*M := by
      rw [div_mul_eq_mul_div,one_le_div ha0]; exact hm
    exact hh.trans (mul_le_mul_of_nonneg_right hratio hM0)
  have hratio' : (b-a+1)/a ≤ 4*d := by
    apply (div_le_iff₀ ha0).mpr
    linarith only [(div_le_iff₀ ha0).mp hratio,h1]
  have hv := AlpogeZetaSamples.primeError_increment_le_of_zero_bound ha hab.le hb (by linarith) hB1 hz
  have hcost : |QuasiRHPrimeWindowBounds.primeError b - QuasiRHPrimeWindowBounds.primeError a| ≤
      d*(K*M) := by
    apply hv.trans
    have hh := mul_le_mul_of_nonneg_right hratio' hM0
    have hpi := mul_le_mul_of_nonneg_left hnorm (sq_nonneg Real.pi)
    change Real.pi^2/12 + 72*((b-a+1)/a)*a^B*(1+log a/log 2)^2 ≤ d*(K*M)
    rw [mul_assoc (72*((b-a+1)/a)), show a^B*(1+log a/log 2)^2 = M by rfl]
    dsimp only [K]
    linarith only [hh,hpi]
  have hu := RosserSchoenfeldDesmoothing.prime_increment_lower (Real.log_le_log ha0 hab.le)
  have hl := RosserSchoenfeldDesmoothing.prime_increment_upper (Real.log_le_log ha0 hab.le)
  rw [Real.exp_log ha0] at hu
  rw [Real.exp_log hb0] at hl
  obtain ⟨hmn,hmx⟩ := abs_le.mp hcost
  unfold QuasiRHPrimeWindowBounds.primeError at hmn hmx
  constructor
  · apply (mul_le_mul_iff_right₀ hd).mp
    dsimp [d,M] at *
    linarith only [hu,hmn,hhi]
  · apply (mul_le_mul_iff_right₀ hd).mp
    dsimp [d,M] at *
    linarith only [hl,hmx,hlo]

/-- In physical coordinates, the unsmoothed Chebyshev mass has error of order
`x^B (1+log x)^2`, assuming an all-height bound on the real parts of the zeros. -/
theorem psi_error {B : ℝ} (hB : 1/2 ≤ B) (hB1 : B ≤ 1)
    (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) {x : ℝ} (hx : 4 ≤ x) :
    |Chebyshev.psi x-x| ≤ (289+Real.pi^2/6+log (2*Real.pi))*(x^B*(1+log x/log 2)^2) := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 := zero_lt_one.trans_le hx1
  have hs := Real.sq_sqrt hx0.le
  have hs2 : 2 ≤ sqrt x := (Real.le_sqrt (by norm_num) hx0.le).mpr (by nlinarith)
  have hsx : 2*sqrt x ≤ x := by nlinarith [mul_nonneg (sub_nonneg.mpr hs2) (sqrt_nonneg x)]
  have ha : 1 ≤ x-sqrt x := by linarith
  have hc : 0 ≤ c := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hM := sqrt_le_envelope hx1 hB
  have hM1 : 1 ≤ envelope B x := by linarith
  have hK : 0 ≤ K := by positivity
  have hu := (secant hB hB1 hz hx1 (b := x+sqrt x) (by linarith) (by linarith)).1
  have hsmall := Real.sqrt_le_sqrt (show x-sqrt x ≤ x by linarith)
  have hl := (secant hB hB1 hz ha (b := x) (by linarith) (by linarith)).2
  have hm := envelope_mono ha (show x-sqrt x ≤ x by linarith) (by linarith : 0 ≤ B)
  change |Chebyshev.psi x-x| ≤ (289+Real.pi^2/6+c)*envelope B x
  rw [show 289+Real.pi^2/6 = 1+K by dsimp only [K]; ring]
  apply abs_le.mpr
  constructor <;> linarith only [hl,hu,hM,mul_le_mul_of_nonneg_left hm hK,
    mul_le_mul_of_nonneg_left hM1 hc,hc, mul_nonneg hc (zero_le_one.trans hM1)]

/-- Pointwise mass of ordinary primes with the same zero exponent and logarithmic loss. -/
theorem theta_error {B : ℝ} (hB : 1/2 ≤ B) (hB1 : B ≤ 1)
    (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 4 ≤ x →
      |Chebyshev.theta x-x| ≤ C*(x^B*(1+log x/log 2)^2) := by
  obtain ⟨P,hP⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let A := 289+Real.pi^2/6+log (2*Real.pi)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity [Real.log_nonneg (show 1 ≤ 2*Real.pi by linarith [Real.pi_gt_three])]
  refine ⟨|P|+A, by positivity,fun x hx => ?_⟩
  have hp := hP x
  have hmass : |Chebyshev.theta x-Chebyshev.psi x| ≤ |P| * envelope B x := by
    rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))]
    exact hp.trans (mul_le_mul (le_abs_self _) (sqrt_le_envelope (by linarith) hB) (sqrt_nonneg x) (abs_nonneg _))
  have h := abs_sub_le (Chebyshev.theta x) (Chebyshev.psi x) x
  exact h.trans ((add_le_add hmass (psi_error hB hB1 hz hx)).trans_eq (by dsimp [A,envelope]; ring))

/-- In the reciprocal prime band ending at x to the four-sevenths power, the discrepancy
in ordinary prime mass is bounded by the square root times the displayed logarithmic factor. -/
theorem theta_four_sevenths :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → 4 ≤ x^(4/7:ℝ) →
      |Chebyshev.theta (x^(4/7:ℝ))-x^(4/7:ℝ)| ≤ C*sqrt x*(1+log x/log 2)^2 := by
  obtain ⟨C,hC,h⟩ := theta_error (B := 7/8) (by norm_num) (by norm_num) suzukiLocalZero_re_le_seven_eighths
  refine ⟨C,hC,fun x hx hs => ?_⟩
  have hh := h _ hs
  rw [← Real.rpow_mul (zero_le_one.trans hx),show (4/7:ℝ)*(7/8)=1/2 by norm_num,← Real.sqrt_eq_rpow,
    Real.log_rpow (zero_lt_one.trans_le hx)] at hh
  apply hh.trans
  rw [← mul_assoc]
  gcongr
  · positivity [Real.log_nonneg hx]
  · linarith [Real.log_nonneg hx]

end
end RiemannGaussian.PrimeMassFromZeroBound
