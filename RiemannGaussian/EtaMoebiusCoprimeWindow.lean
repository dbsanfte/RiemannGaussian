import RiemannGaussian.EtaMoebiusCoprimeProduct

/-!
# Uniform physical-window cost of simultaneous coprime exclusion

Every divided window is kept in the finite sieve, including its sampling
and endpoint losses. The completed low sieve has mean square at most a
zero-dependent constant times `P^4 * (1+log u)^2 * u^(3-6*sigma)` on the
original cubic window when the odd modulus `P` divides `u`. The modulus
is not fixed in this inequality. Cross terms between its divisor terms
are controlled together by finite Cauchy--Schwarz.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The physical sampling and endpoint constant, independent of the sieve modulus and every cutoff. -/
def pairedEtaMoebiusCoprimeSamplingConstant (rho : NontrivialZetaZero) : ℝ :=
  10 * ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 * finiteCircleSamplingConstant +
    2 * (pairedEtaCompletedMoebiusPhysicalErrorConstant rho +
      2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho) ^ 2

/-- The modulus-independent sampling constant is nonnegative. -/
theorem pairedEtaMoebiusCoprimeSamplingConstant_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaMoebiusCoprimeSamplingConstant rho := by
  unfold pairedEtaMoebiusCoprimeSamplingConstant
  have hc := finiteCircleSamplingConstant_pos.le
  positivity

private theorem selected_divided_meanSquare_eq
    (rho : NontrivialZetaZero) {e : ℕ} (he : 0 < e) (S : Finset ℕ) (A L : ℕ) :
    (∑ t ∈ Finset.range (e * L),
      ‖(e : ℂ) ^ (-rho.1) *
        pairedEtaCompletedMoebiusSelectedAggregate rho S ((e * A + t) / e)‖ ^ 2) / (e * L : ℕ) =
      (e : ℝ) ^ (-2 * rho.1.re) *
        ((∑ t ∈ Finset.range L, ‖pairedEtaCompletedMoebiusSelectedAggregate rho S (A + t)‖ ^ 2) / L) := by
  have hdiv (t : ℕ) : (e * A + t) / e = A + t / e := by
    rw [Nat.add_comm, Nat.add_mul_div_left t A he, Nat.add_comm]
  have hnorm (t : ℕ) :
      ‖(e : ℂ) ^ (-rho.1) *
        pairedEtaCompletedMoebiusSelectedAggregate rho S ((e * A + t) / e)‖ ^ 2 =
        (e : ℝ) ^ (-2 * rho.1.re) *
          ‖pairedEtaCompletedMoebiusSelectedAggregate rho S (A + t / e)‖ ^ 2 := by
    rw [hdiv, norm_mul, Complex.norm_natCast_cpow_of_pos he, Complex.neg_re, mul_pow,
      ← Real.rpow_mul_natCast (Nat.cast_nonneg e)]
    norm_num only [Nat.cast_ofNat]
    congr 2
    ring
  simp_rw [hnorm]
  rw [← Finset.mul_sum, sum_range_div_blocks
    (fun t ↦ ‖pairedEtaCompletedMoebiusSelectedAggregate rho S (A + t)‖ ^ 2) he L, nsmul_eq_mul]
  push_cast
  by_cases hL : L = 0
  · simp [hL]
  · have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL
    field_simp

private theorem divided_cubic_budget_le {e u c b : ℝ}
    (he : 1 ≤ e) (hu : 1 ≤ u) (hc : 0 ≤ c) (hb : 0 ≤ b) :
    c * ((4 * (u ^ 2) ^ 2 + u ^ 3 / e) / (u ^ 3 / e)) *
        (1 + Real.log (u ^ 2)) ^ 2 * u ^ 2 +
      b * (u ^ 2) ^ 4 / (u ^ 3 / e) ^ 2 ≤
        (20 * c + b) * e ^ 2 * u ^ 3 * (1 + Real.log u) ^ 2 := by
  have he0 : 0 < e := by linarith
  have hu0 : 0 < u := by linarith
  have hlu := Real.log_nonneg hu
  have he2 : e ≤ e ^ 2 := by nlinarith
  have hu23 : u ^ 2 ≤ u ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hu (sq_nonneg u)]
  have hmain : 4 * e * u ^ 3 + u ^ 2 ≤ 5 * e ^ 2 * u ^ 3 := by
    have h1 := mul_le_mul_of_nonneg_right he2 (pow_nonneg hu0.le 3)
    have h2 : u ^ 3 ≤ e ^ 2 * u ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_right (show 1 ≤ e ^ 2 by nlinarith) (pow_nonneg hu0.le 3)]
    linarith
  have hlog : (1 + 2 * Real.log u) ^ 2 ≤ 4 * (1 + Real.log u) ^ 2 := by nlinarith
  have hlog1 : 1 ≤ (1 + Real.log u) ^ 2 := by nlinarith
  calc
    _ = c * (4 * e * u ^ 3 + u ^ 2) * (1 + 2 * Real.log u) ^ 2 + b * e ^ 2 * u ^ 2 := by
      rw [Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      field_simp
    _ ≤ c * (5 * e ^ 2 * u ^ 3) * (4 * (1 + Real.log u) ^ 2) +
        b * e ^ 2 * (u ^ 3 * (1 + Real.log u) ^ 2) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hmain hc) hlog (sq_nonneg _) (by positivity)
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hu23.trans (by nlinarith [mul_le_mul_of_nonneg_left hlog1 (pow_nonneg hu0.le 3)])
    _ = _ := by ring

/-- A selected divisor family at a divided physical cutoff has a uniform quadratic cost in that divisor, with the original complex dilation retained. -/
theorem pairedEtaCompletedMoebiusSelectedAggregate_divided_cubic_meanSquare_le
    (rho : NontrivialZetaZero) {e u : ℕ} (he : 1 ≤ e) (hu : 1 ≤ u) (heu : e ∣ u)
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 (u ^ 2)) :
    (∑ t ∈ Finset.range (u ^ 3),
      ‖(e : ℂ) ^ (-rho.1) * pairedEtaCompletedMoebiusSelectedAggregate rho S ((u ^ 3 + t) / e)‖ ^ 2) /
        (u ^ 3 : ℕ) ≤
      pairedEtaMoebiusCoprimeSamplingConstant rho * (e : ℝ) ^ 2 *
        (1 + Real.log u) ^ 2 * (u : ℝ) ^ (3 - 6 * rho.1.re) := by
  let A := u ^ 3 / e
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have heu' : e ≤ u := Nat.le_of_dvd hu heu
  have hdvd : e ∣ u ^ 3 := dvd_trans heu ⟨u ^ 2, by ring⟩
  have hA : u ^ 3 = e * A := (Nat.mul_div_cancel' hdvd).symm
  have hDA : u ^ 2 ≤ A := by
    apply (Nat.le_div_iff_mul_le he).mpr
    nlinarith [Nat.mul_le_mul_left (u ^ 2) heu']
  have hD : 1 ≤ u ^ 2 := by nlinarith
  have hAp : 1 ≤ A := hD.trans hDA
  have hAc : (A : ℝ) = (u : ℝ) ^ 3 / e := by
    apply (eq_div_iff he0.ne').mpr
    have hh : (u : ℝ) ^ 3 = (e : ℝ) * A := by exact_mod_cast hA
    linarith
  have heq := selected_divided_meanSquare_eq rho he S A A
  rw [← hA] at heq
  rw [heq]
  have hb := pairedEtaCompletedMoebiusSelectedAggregate_meanSquare_le_window rho hS hAp hAp hD hDA
  have hc := finiteCircleSamplingConstant_pos.le
  have hmain := divided_cubic_budget_le heR huR
    (mul_nonneg (by positivity : 0 ≤ ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 2) hc)
    (by positivity : 0 ≤ 2 * (pairedEtaCompletedMoebiusPhysicalErrorConstant rho +
      2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho) ^ 2)
  have hpower : (e : ℝ) ^ (-2 * rho.1.re) * (A : ℝ) ^ (-2 * rho.1.re) =
      (u : ℝ) ^ (-6 * rho.1.re) := by
    rw [← Real.mul_rpow he0.le (by positivity : (0 : ℝ) ≤ A)]
    have hh : (e : ℝ) * A = (u : ℝ) ^ 3 := by exact_mod_cast hA.symm
    rw [hh, ← Real.rpow_natCast_mul hu0.le]
    congr 1
    ring
  calc
    _ ≤ (e : ℝ) ^ (-2 * rho.1.re) * ((A : ℝ) ^ (-2 * rho.1.re) *
        (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 2 * finiteCircleSamplingConstant *
          ((4 * ((u ^ 2 : ℕ) : ℝ) ^ 2 + A) / A) * (1 + Real.log (u ^ 2 : ℕ)) ^ 2 * (u ^ 2 : ℕ) +
          2 * (pairedEtaCompletedMoebiusPhysicalErrorConstant rho +
            2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho) ^ 2 *
            ((u ^ 2 : ℕ) : ℝ) ^ 4 / (A : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (u : ℝ) ^ (-6 * rho.1.re) *
        (pairedEtaMoebiusCoprimeSamplingConstant rho * (e : ℝ) ^ 2 * (u : ℝ) ^ 3 * (1 + Real.log u) ^ 2) := by
      rw [← mul_assoc, hpower, hAc]
      simp only [Nat.cast_pow]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply hmain.trans_eq
      rw [pairedEtaMoebiusCoprimeSamplingConstant]
      ring
    _ = _ := by
      rw [show 3 - 6 * rho.1.re = -6 * rho.1.re + 3 by ring,
        Real.rpow_add hu0, Real.rpow_ofNat]
      ring

/-- The full low sieve mean square on the original cubic physical window. -/
def pairedEtaMoebiusCoprimeLowCubicEnergy (rho : NontrivialZetaZero) (P u : ℕ) : ℝ :=
  (∑ t ∈ Finset.range (u ^ 3),
    ‖pairedEtaCompletedMoebiusCoprimeLowAggregate rho P (u ^ 2) (u ^ 3 + t)‖ ^ 2) / (u ^ 3 : ℕ)

private theorem norm_sum_sq_le_card (S : Finset ℕ) (f : ℕ → ℂ) :
    ‖∑ e ∈ S, f e‖ ^ 2 ≤ (S.card : ℝ) * ∑ e ∈ S, ‖f e‖ ^ 2 := by
  have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S f) 2
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ : ℕ ↦ (1 : ℝ)) (fun e ↦ ‖f e‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  exact hn.trans hc

/-- The simultaneous sieve estimate retains the actual divisor count and squared-divisor cost of all its intersections. -/
theorem pairedEtaMoebiusCoprimeLowCubicEnergy_le_divisors
    (rho : NontrivialZetaZero) {P u : ℕ} (hP : 0 < P) (hodd : Odd P)
    (hu : 1 ≤ u) (hPu : P ∣ u) :
    pairedEtaMoebiusCoprimeLowCubicEnergy rho P u ≤
      pairedEtaMoebiusCoprimeSamplingConstant rho * (P.divisors.card : ℝ) *
        (∑ e ∈ P.divisors, (e : ℝ) ^ 2) *
          (1 + Real.log u) ^ 2 * (u : ℝ) ^ (3 - 6 * rho.1.re) := by
  let S := pairedEtaMoebiusCoprimeDivisors P (u ^ 2)
  let f : ℕ → ℕ → ℂ := fun e t ↦
    (e : ℂ) ^ (-rho.1) * pairedEtaCompletedMoebiusSelectedAggregate rho S ((u ^ 3 + t) / e)
  have hterm (e : ℕ) (he : e ∈ P.divisors) :
      (∑ t ∈ Finset.range (u ^ 3), ‖f e t‖ ^ 2) / (u ^ 3 : ℕ) ≤
        pairedEtaMoebiusCoprimeSamplingConstant rho * (e : ℝ) ^ 2 *
          (1 + Real.log u) ^ 2 * (u : ℝ) ^ (3 - 6 * rho.1.re) :=
    pairedEtaCompletedMoebiusSelectedAggregate_divided_cubic_meanSquare_le rho
      (Nat.pos_of_mem_divisors he) hu ((Nat.dvd_of_mem_divisors he).trans hPu)
      (pairedEtaMoebiusCoprimeDivisors_subset P (u ^ 2))
  have hpoint (t : ℕ) :
      ‖pairedEtaCompletedMoebiusCoprimeLowAggregate rho P (u ^ 2) (u ^ 3 + t)‖ ^ 2 ≤
        (P.divisors.card : ℝ) * ∑ e ∈ P.divisors, ‖f e t‖ ^ 2 := by
    rw [pairedEtaCompletedMoebiusCoprimeLowAggregate_eq_sieve rho hP hodd]
    have hn := norm_sum_sq_le_card P.divisors (fun e ↦ (μ e : ℂ) * f e t)
    simp only [mul_assoc]
    apply hn.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro e _
    have hm : ‖(μ e : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := e)
    rw [norm_mul, mul_pow]
    have hs := pow_le_pow_left₀ (norm_nonneg _) hm 2
    simpa only [one_pow, one_mul] using mul_le_mul_of_nonneg_right hs (sq_nonneg ‖f e t‖)
  unfold pairedEtaMoebiusCoprimeLowCubicEnergy
  calc
    _ ≤ (∑ t ∈ Finset.range (u ^ 3),
        (P.divisors.card : ℝ) * ∑ e ∈ P.divisors, ‖f e t‖ ^ 2) / (u ^ 3 : ℕ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun t _ ↦ hpoint t)) (Nat.cast_nonneg _)
    _ = (P.divisors.card : ℝ) *
        ∑ e ∈ P.divisors, (∑ t ∈ Finset.range (u ^ 3), ‖f e t‖ ^ 2) / (u ^ 3 : ℕ) := by
      rw [← Finset.mul_sum, Finset.sum_comm, mul_div_assoc, Finset.sum_div]
    _ ≤ (P.divisors.card : ℝ) * ∑ e ∈ P.divisors,
        pairedEtaMoebiusCoprimeSamplingConstant rho * (e : ℝ) ^ 2 *
          (1 + Real.log u) ^ 2 * (u : ℝ) ^ (3 - 6 * rho.1.re) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]; ring

/-- A uniform polynomial modulus budget permits the set of excluded primes to grow with the original physical cutoff. -/
theorem pairedEtaMoebiusCoprimeLowCubicEnergy_le
    (rho : NontrivialZetaZero) {P u : ℕ} (hP : 0 < P) (hodd : Odd P)
    (hu : 1 ≤ u) (hPu : P ∣ u) :
    pairedEtaMoebiusCoprimeLowCubicEnergy rho P u ≤
      pairedEtaMoebiusCoprimeSamplingConstant rho * (P : ℝ) ^ 4 *
        (1 + Real.log u) ^ 2 * (u : ℝ) ^ (3 - 6 * rho.1.re) := by
  have hc : (P.divisors.card : ℝ) ≤ P := by exact_mod_cast Nat.card_divisors_le_self P
  have hs : (∑ e ∈ P.divisors, (e : ℝ) ^ 2) ≤ (P.divisors.card : ℝ) * (P : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _e ∈ P.divisors, (P : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro e he
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_of_dvd hP (Nat.dvd_of_mem_divisors he)) 2
      _ = _ := by simp
  have hbudget : (P.divisors.card : ℝ) * (∑ e ∈ P.divisors, (e : ℝ) ^ 2) ≤ (P : ℝ) ^ 4 := by
    calc
      _ ≤ (P.divisors.card : ℝ) * ((P.divisors.card : ℝ) * (P : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
      _ ≤ (P : ℝ) * ((P : ℝ) * (P : ℝ) ^ 2) :=
        mul_le_mul hc (mul_le_mul_of_nonneg_right hc (sq_nonneg _)) (by positivity) (Nat.cast_nonneg _)
      _ = _ := by ring
  apply (pairedEtaMoebiusCoprimeLowCubicEnergy_le_divisors rho hP hodd hu hPu).trans
  have hC := pairedEtaMoebiusCoprimeSamplingConstant_nonneg rho
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbudget hC) (sq_nonneg (1 + Real.log u)))
    (Real.rpow_nonneg (Nat.cast_nonneg u) (3 - 6 * rho.1.re))
  convert hh using 1
  ring

end

end RiemannGaussian
