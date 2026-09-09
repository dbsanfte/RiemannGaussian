/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusTailMoments
import RiemannGaussian.ZetaPrimePowerMoments

/-!
# Independent control of the single-prime part of the Möbius tail

On a prime power, the full signed divisor convolution reduces to one
Möbius term. Its higher logarithmic moments have a summable majorant
strictly beyond real part one half, uniformly in the divisor cutoff.
This removes the single-prime interactions from the selected-zero source
while preserving the exact remaining arithmetic sum.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The exact signed tail coefficient on every positive power of a
prime. Only divisor `p` can survive; the unit divisor and all nonsquarefree
divisors contribute zero. -/
theorem zetaMoebiusLogTailCoefficient_prime_pow (D : ℕ) (hD : 1 ≤ D)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    zetaMoebiusLogTailCoefficient D (p ^ (k + 1)) =
      if D < p then -(k : ℂ) * (Real.log p : ℂ) else 0 := by
  rw [zetaMoebiusLogTailCoefficient_eq, Finset.sum_eq_single (p, p ^ k)]
  · simp only [ArithmeticFunction.moebius_apply_prime hp, Int.cast_neg, Int.cast_one,
      Nat.cast_pow, Real.log_pow, Complex.ofReal_mul, Complex.ofReal_natCast]
    split_ifs <;> ring
  · intro a ha hne
    by_cases hd : D < a.1
    · rw [if_pos hd]
      have hprod := (Nat.mem_divisorsAntidiagonal.mp ha).1
      have hdvd : a.1 ∣ p ^ (k + 1) := ⟨a.2, hprod.symm⟩
      obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      rcases j with _ | j
      · simp only [pow_zero] at hj
        omega
      · by_cases hj1 : j + 1 = 1
        · have ha1 : a.1 = p := by simpa [hj1] using hj
          have ha2 : a.2 = p ^ k := by
            apply Nat.eq_of_mul_eq_mul_left hp.pos
            simpa only [ha1, pow_succ', Nat.add_comm 1 k] using hprod
          exact (hne (Prod.ext ha1 ha2)).elim
        · rw [hj, ArithmeticFunction.moebius_apply_prime_pow hp (Nat.succ_ne_zero j), if_neg hj1]
          simp
    · rw [if_neg hd]
  · intro h
    exact (h (Nat.mem_divisorsAntidiagonal.mpr
      ⟨(pow_succ' p k).symm, pow_ne_zero _ hp.ne_zero⟩)).elim

/-- The exact contribution of prime powers to the large-divisor tail,
retaining the negative Möbius sign and every complex phase downstream. -/
def zetaMoebiusTailPrimePowerCoefficient (D n : ℕ) : ℂ :=
  if IsPrimePow n then zetaMoebiusLogTailCoefficient D n else 0

/-- A fixed nonnegative arithmetic majorant with only one extra log
factor over the existing proper-prime-power coefficient. -/
def zetaMoebiusTailPrimePowerMajorant (n : ℕ) : ℝ :=
  (Real.log n / Real.log 2) * zetaProperPrimePowerCoefficient n

/-- The prime-power majorant is nonnegative at every natural index. -/
theorem zetaMoebiusTailPrimePowerMajorant_nonneg (n : ℕ) :
    0 ≤ zetaMoebiusTailPrimePowerMajorant n := by
  exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
    (zetaProperPrimePowerCoefficient_nonneg n)

/-- The exact single-prime tail coefficient is bounded by a fixed
majorant independent of the divisor cutoff. -/
theorem norm_zetaMoebiusTailPrimePowerCoefficient_le (D : ℕ) (hD : 1 ≤ D) (n : ℕ) :
    ‖zetaMoebiusTailPrimePowerCoefficient D n‖ ≤ zetaMoebiusTailPrimePowerMajorant n := by
  by_cases hn : IsPrimePow n
  · rw [zetaMoebiusTailPrimePowerCoefficient, if_pos hn]
    by_cases hnp : n.Prime
    · rw [zetaMoebiusLogTailCoefficient_prime D hD hnp, norm_zero]
      exact zetaMoebiusTailPrimePowerMajorant_nonneg n
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [zetaMoebiusLogTailCoefficient_prime_pow D hD hp]
    by_cases hd : D < p
    · rw [if_pos hd, norm_mul, norm_neg, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg p)]
      have hlp : Real.log 2 ≤ Real.log p :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
      have hlog : Real.log (p ^ (k + 1) : ℕ) = (k + 1 : ℝ) * Real.log p := by
        rw [Nat.cast_pow, Real.log_pow]
        push_cast
        rfl
      have hv : zetaProperPrimePowerCoefficient (p ^ (k + 1)) = Real.log p := by
        rw [zetaProperPrimePowerCoefficient, if_neg hnp,
          ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
          ArithmeticFunction.vonMangoldt_apply_prime hp]
      rw [zetaMoebiusTailPrimePowerMajorant, hv, hlog]
      have he : (k + 1 : ℝ) * Real.log p / Real.log 2 * Real.log p =
          ((k + 1 : ℝ) * Real.log p) * (Real.log p / Real.log 2) := by ring
      rw [he]
      have h1 : 1 ≤ Real.log p / Real.log 2 :=
        (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr (by simpa using hlp)
      calc
        _ ≤ ((k + 1 : ℝ) * Real.log p) * 1 := by nlinarith [Real.log_natCast_nonneg p]
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    · rw [if_neg hd, norm_zero]
      exact zetaMoebiusTailPrimePowerMajorant_nonneg _
  · rw [zetaMoebiusTailPrimePowerCoefficient, if_neg hn, norm_zero]
    exact zetaMoebiusTailPrimePowerMajorant_nonneg n

/-- The existing proper-prime-power series converges absolutely past
one half; multiplication by a logarithm preserves that abscissa bound. -/
theorem LSeriesSummable_zetaMoebiusTailPrimePowerMajorant {s : ℂ} (hs : 1 / 2 < s.re) :
    LSeriesSummable (fun n ↦ (zetaMoebiusTailPrimePowerMajorant n : ℂ)) s := by
  have ha : LSeries.abscissaOfAbsConv (fun n ↦ (zetaProperPrimePowerCoefficient n : ℂ)) ≤ (1 / 2 : ℝ) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    exact LSeriesSummable_zetaProperPrimePower (by simpa using hy)
  have h : LSeriesSummable (LSeries.logMul (fun n ↦ (zetaProperPrimePowerCoefficient n : ℂ))) s :=
    LSeriesSummable_logMul_of_lt_re (lt_of_le_of_lt ha (by exact_mod_cast hs))
  have he : (fun n ↦ (zetaMoebiusTailPrimePowerMajorant n : ℂ)) =
      (fun n ↦ ((Real.log 2 : ℂ)⁻¹) *
        LSeries.logMul (fun m ↦ (zetaProperPrimePowerCoefficient m : ℂ)) n) := by
    funext n
    simp only [zetaMoebiusTailPrimePowerMajorant, Complex.ofReal_mul, Complex.ofReal_div,
      LSeries.logMul, ← Complex.natCast_log]
    ring
  rw [he]
  simpa only [Pi.smul_def, smul_eq_mul] using h.smul ((Real.log 2 : ℂ)⁻¹)

/-- The fixed majorant's exponential weights are genuinely summable
strictly past real part one half. -/
theorem summable_zetaMoebiusTailPrimePowerMajorant {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun n ↦ zetaMoebiusTailPrimePowerMajorant n * zetaPrimeExpWeight σ n) := by
  apply summable_zetaPrimeExpWeight_mul _ (by simp [zetaMoebiusTailPrimePowerMajorant])
  exact LSeriesSummable_zetaMoebiusTailPrimePowerMajorant (by simpa using hσ)

/-- A finite positive arithmetic mass for the complete single-prime
tail, independent of the divisor cutoff and the ordinate. -/
def zetaMoebiusTailPrimePowerMass (σ : ℝ) : ℝ :=
  ∑' n, zetaMoebiusTailPrimePowerMajorant n * zetaPrimeExpWeight σ n

private theorem kernel_majorant (D : ℕ) (hD : 1 ≤ D) (k : ℕ) (s : ℂ) {q : ℝ} (hq : 0 < q) (n : ℕ) :
    ‖zetaMoebiusTailPrimePowerCoefficient D n * zetaPrimeLogKernel k s n‖ ≤
      q⁻¹ ^ k * (zetaMoebiusTailPrimePowerMajorant n * zetaPrimeExpWeight (s.re - q) n) := by
  rw [norm_mul]
  calc
    _ ≤ zetaMoebiusTailPrimePowerMajorant n * (q⁻¹ ^ k * zetaPrimeExpWeight (s.re - q) n) :=
      mul_le_mul (norm_zetaMoebiusTailPrimePowerCoefficient_le D hD n)
        (norm_zetaPrimeLogKernel_le k s n hq) (norm_nonneg _) (zetaMoebiusTailPrimePowerMajorant_nonneg n)
    _ = _ := by ring

/-- Every logarithmic moment of the signed prime-power tail converges
in the stronger half-plane, uniformly dominated over all positive cutoffs. -/
theorem summable_zetaMoebiusTailPrimePowerMoment (D : ℕ) (hD : 1 ≤ D) (k : ℕ)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun n ↦ zetaMoebiusTailPrimePowerCoefficient D n * zetaPrimeLogKernel k s n) := by
  let q := (s.re - 1 / 2) / 2
  have hq : 0 < q := by dsimp [q]; linarith
  have hσ : 1 / 2 < s.re - q := by dsimp [q]; linarith
  apply ((summable_zetaMoebiusTailPrimePowerMajorant hσ).mul_left (q⁻¹ ^ k)).of_norm_bounded
  exact kernel_majorant D hD k s hq

/-- The actual complex factorial moment of the single-prime tail. -/
def zetaMoebiusTailPrimePowerMoment (D k : ℕ) (s : ℂ) : ℂ :=
  ∑' n, zetaMoebiusTailPrimePowerCoefficient D n * zetaPrimeLogKernel k s n

/-- A quantitative bound for the entire single-prime moment, with a
fixed mass that does not depend on the moving divisor cutoff. -/
theorem norm_zetaMoebiusTailPrimePowerMoment_le (D : ℕ) (hD : 1 ≤ D) (k : ℕ) (s : ℂ)
    {q : ℝ} (hq : 0 < q) (hσ : 1 / 2 < s.re - q) :
    ‖zetaMoebiusTailPrimePowerMoment D k s‖ ≤ q⁻¹ ^ k * zetaMoebiusTailPrimePowerMass (s.re - q) := by
  have hs : 1 / 2 < s.re := by linarith
  have hsum := summable_zetaMoebiusTailPrimePowerMoment D hD k hs
  calc
    _ ≤ ∑' n, ‖zetaMoebiusTailPrimePowerCoefficient D n * zetaPrimeLogKernel k s n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n, q⁻¹ ^ k * (zetaMoebiusTailPrimePowerMajorant n * zetaPrimeExpWeight (s.re - q) n) :=
      Summable.tsum_le_tsum (kernel_majorant D hD k s hq) hsum.norm
        ((summable_zetaMoebiusTailPrimePowerMajorant hσ).mul_left _)
    _ = _ := tsum_mul_left

/-- The complete polynomial filter of the actual single-prime tail. -/
def zetaMoebiusTailPrimePowerFilter (p : Polynomial ℂ) (D N : ℕ) (s : ℂ) : ℂ :=
  zetaMomentSequenceFilter p (fun n ↦ zetaMoebiusTailPrimePowerMoment D n s) N

/-- The whole prime-power filter has an independent arithmetic bound
uniform in the divisor cutoff and ordinate, for every polynomial. -/
theorem norm_zetaMoebiusTailPrimePowerFilter_le (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D)
    (y : ℝ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ‖zetaMoebiusTailPrimePowerFilter p D N (3 / 2 + I * y)‖ ≤
      q⁻¹ ^ N * (zetaMoebiusTailPrimePowerMass (3 / 2 - q) *
        ∑ k ∈ p.support, ‖p.coeff k‖ * q⁻¹ ^ k) := by
  rw [zetaMoebiusTailPrimePowerFilter, zetaMomentSequenceFilter, Polynomial.sum]
  have hs : (3 / 2 + I * (y : ℂ)).re = 3 / 2 := by simp
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ *
        (q⁻¹ ^ (N + k) * zetaMoebiusTailPrimePowerMass (3 / 2 - q)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [hs] using norm_zetaMoebiusTailPrimePowerMoment_le D hD (N + k)
        (3 / 2 + I * y) hq (by rw [hs]; linarith)
    _ = _ := by
      simp only [Finset.mul_sum, pow_add]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- The single-prime contribution has the explicit geometric rate
`sqrt(u)` at each positive source scale `u<1`, for any varying positive
divisor cutoff and every fixed polynomial filter. -/
theorem exists_zetaMoebiusTailPrimePowerFilter_geometric_bound (p : Polynomial ℂ) (y : ℝ)
    (D : ℕ → ℕ) (hD : ∀ N, 1 ≤ D N) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖(u : ℂ) ^ (N + 1) * zetaMoebiusTailPrimePowerFilter p (D N) N (3 / 2 + I * y)‖ ≤
        C * (Real.sqrt u) ^ N := by
  have hq : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hq1 : Real.sqrt u < 1 := by nlinarith [Real.sq_sqrt hu.le, Real.sqrt_nonneg u]
  have hratio : u * (Real.sqrt u)⁻¹ = Real.sqrt u := by
    rw [← div_eq_mul_inv]
    exact (div_eq_iff hq.ne').mpr (by simpa only [pow_two] using (Real.sq_sqrt hu.le).symm)
  let A := zetaMoebiusTailPrimePowerMass (3 / 2 - Real.sqrt u) *
    ∑ k ∈ p.support, ‖p.coeff k‖ * (Real.sqrt u)⁻¹ ^ k
  have hmass : 0 ≤ zetaMoebiusTailPrimePowerMass (3 / 2 - Real.sqrt u) :=
    tsum_nonneg (fun n ↦ mul_nonneg (zetaMoebiusTailPrimePowerMajorant_nonneg n) (Real.exp_pos _).le)
  have hA : 0 ≤ A := mul_nonneg hmass (Finset.sum_nonneg (fun _ _ ↦ by positivity))
  refine ⟨u * A, mul_nonneg hu.le hA, fun N ↦ ?_⟩
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  apply (mul_le_mul_of_nonneg_left (norm_zetaMoebiusTailPrimePowerFilter_le p (D N) N (hD N) y hq hq1)
    (pow_nonneg hu.le _)).trans_eq
  change u ^ (N + 1) * ((Real.sqrt u)⁻¹ ^ N * A) = u * A * (Real.sqrt u) ^ N
  calc
    _ = u * A * (u * (Real.sqrt u)⁻¹) ^ N := by rw [pow_succ, mul_pow]; ring
    _ = _ := by rw [hratio]

/-- Even an arbitrary varying divisor cutoff leaves the single-prime
tail negligible at every source scale strictly below one. The estimate
comes from arithmetic alone and needs no pole-cancelling filter condition. -/
theorem tendsto_zetaMoebiusTailPrimePowerFilter_mul_pow (p : Polynomial ℂ) (y : ℝ)
    (D : ℕ → ℕ) (hD : ∀ᶠ N in atTop, 1 ≤ D N) {a : ℂ} (ha : ‖a‖ < 1) :
    Tendsto (fun N : ℕ ↦ a ^ (N + 1) * zetaMoebiusTailPrimePowerFilter p (D N) N (3 / 2 + I * y))
      atTop (𝓝 0) := by
  obtain ⟨q, haq, hq1⟩ := exists_between ha
  have hq : 0 < q := lt_of_le_of_lt (norm_nonneg a) haq
  let C := ‖a‖ * (zetaMoebiusTailPrimePowerMass (3 / 2 - q) *
    ∑ k ∈ p.support, ‖p.coeff k‖ * q⁻¹ ^ k)
  have hlim : Tendsto (fun N : ℕ ↦ (‖a‖ / q) ^ N * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ ‖a‖ / q)
        ((div_lt_one hq).mpr haq)).mul_const C
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [hD] with N hN
  rw [norm_mul, norm_pow]
  apply (mul_le_mul_of_nonneg_left (norm_zetaMoebiusTailPrimePowerFilter_le p (D N) N hN y hq hq1)
    (pow_nonneg (norm_nonneg _) _)).trans_eq
  dsimp only [C]
  rw [div_pow, inv_pow, pow_succ]
  ring

end

end RiemannGaussian
