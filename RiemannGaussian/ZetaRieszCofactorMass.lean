/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeFractionalBudget
import RiemannGaussian.ZetaRieszMacroPrimeWindows

/-! # Uniform counting mechanism for fixed cofactor counts

The minimum-prime logarithm distributes across every cofactor prime.
Fractional prime moments then give the same linear mass bound at each
fixed count, including all small primes. These bounds pay coefficient
variation after the signed last-prime period has been summed.
-/
namespace RiemannGaussian.ZetaRieszCofactorMass
noncomputable section
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes

/-- All ordinary primes below the logarithmic upper endpoint. -/
def primes (v : ℝ) : Finset ℕ := logPrimes 0 v

/-- Actual products of exactly `k` prime choices; repeated factors are
allowed in this upper counting cover. -/
def products (k : ℕ) (v : ℝ) : Finset ℕ :=
  (Fintype.piFinset (fun _ : Fin k => primes v)).image (fun p => ∏ i, p i)

/-- Every squarefree label with the specified count and prime upper bound
lies in the counting cover; the tuple notation adds no arithmetic restriction. -/
theorem mem_products_of_squarefree {a k : ℕ} (ha : Squarefree a)
    (hc : a.primeFactors.card = k) {v : ℝ}
    (hv : ∀ p ∈ a.primeFactors, Real.log p ≤ v) : a ∈ products k v := by
  let p := a.primeFactors.orderEmbOfFin hc
  have hp (i : Fin k) : p i ∈ a.primeFactors := a.primeFactors.orderEmbOfFin_mem hc i
  have he := a.primeFactors.image_orderEmbOfFin_univ hc
  apply Finset.mem_image.mpr
  refine ⟨p,Fintype.mem_piFinset.mpr (fun i => ?_),?_⟩
  · have hq := Nat.prime_of_mem_primeFactors (hp i)
    exact (ZetaRieszMacroPrimeWindows.mem_logPrimes_iff (p i) 0 v).mpr ⟨hq,Real.log_pos (by exact_mod_cast hq.one_lt),by simpa using hv _ (hp i)⟩
  · rw [← Nat.prod_primeFactors_of_squarefree ha,← he,Finset.prod_image]
    exact p.injective.injOn

/-- Constant for the least-prime weighted cofactor mass. -/
def logMassConstant (k : ℕ) : ℝ :=
  (ZetaRieszPrimeFractionalBudget.momentConstant (1/(k : ℝ)))^k

/-- Constant for the unsigned mass used only to pay cutoff variation. -/
def variationConstant (k : ℕ) : ℝ :=
  (2*ZetaRieszPrimeFractionalBudget.momentConstant (1/(2*(k : ℝ))))^k

/-- Both constants are positive at every positive fixed count. -/
theorem constants_pos {k : ℕ} (hk : 0 < k) :
    0 < logMassConstant k ∧ 0 < variationConstant k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := ZetaRieszPrimeFractionalBudget.momentConstant_pos
    (show (0 : ℝ) < 1/(k : ℝ) by positivity)
  have h2 := ZetaRieszPrimeFractionalBudget.momentConstant_pos
    (show (0 : ℝ) < 1/(2*(k : ℝ)) by positivity)
  unfold logMassConstant variationConstant
  constructor <;> positivity

private theorem prime_moment {v e : ℝ} (hv : 0 < v) (he : 0 < e) :
    (∑ p ∈ primes v, (Real.log p)^e*(p : ℝ)⁻¹) ≤
      ZetaRieszPrimeFractionalBudget.momentConstant e*v^e := by
  have hh := ZetaRieszPrimeFractionalBudget.prime_fractional_log_mass_le (primes v) hv he
    (by intro p hp; have hb := logPrimes_bounds hp; exact ⟨hb.1,by simpa using hb.2.2⟩)
  have heq (p : ℕ) (hp : p ∈ primes v) : Real.exp (-Real.log p) = (p : ℝ)⁻¹ := by
    rw [Real.exp_neg,Real.exp_log (by exact_mod_cast (logPrimes_bounds hp).1.pos)]
  exact (Finset.sum_congr rfl (fun p hp => by rw [heq p hp])).le.trans hh

/-- The same fractional minimum inequality holds at every positive count. -/
theorem minimum_le_product {k : ℕ} (hk : 0 < k) {t : ℝ} (ht : 0 < t)
    (x : Fin k → ℝ) (hx : ∀ i, t ≤ x i) :
    t ≤ ∏ i, (x i)^(1/(k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    t = (t^(1/(k : ℝ)))^k := by
      rw [← Real.rpow_mul_natCast ht.le]
      simp [hkR.ne']
    _ = ∏ _ : Fin k, t^(1/(k : ℝ)) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => by positivity)
      (fun i _ => Real.rpow_le_rpow ht.le (hx i) (by positivity))

/-- Every subset of the literal product cover has linear least-prime
weighted reciprocal mass. No positive lower prime cutoff is used. -/
theorem log_mass {k : ℕ} (hk : 0 < k) {v : ℝ} (hv : 0 < v)
    (D : Finset ℕ) (hD : D ⊆ products k v) :
    (∑ a ∈ D, Real.log a.minFac*(a : ℝ)⁻¹) ≤ logMassConstant k*v := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let F := fun p : ℕ => (Real.log p)^(1/(k : ℝ))*(p : ℝ)⁻¹
  have hpoint (p : Fin k → ℕ) (hp : p ∈ Fintype.piFinset (fun _ : Fin k => primes v)) :
      Real.log (∏ i, p i : ℕ).minFac*(∏ i, p i : ℝ)⁻¹ ≤ ∏ i, F (p i) := by
    have hprime (i : Fin k) := (logPrimes_bounds (Fintype.mem_piFinset.mp hp i)).1
    have hn0 : (∏ i, p i : ℕ) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (hprime i).ne_zero)
    have hn1 : (∏ i, p i : ℕ) ≠ 1 := by
      have hi := hprime ⟨0,hk⟩
      have hd : p ⟨0,hk⟩ ∣ ∏ i, p i := Finset.dvd_prod_of_mem p (Finset.mem_univ _)
      intro he
      rw [he] at hd
      exact hi.ne_one (Nat.eq_one_of_dvd_one hd)
    have ht : 0 < Real.log (∏ i, p i : ℕ).minFac :=
      Real.log_pos (by exact_mod_cast (Nat.minFac_prime hn1).one_lt)
    have hb := minimum_le_product hk ht (fun i => Real.log (p i)) (by
      intro i
      exact Real.log_le_log (by exact_mod_cast Nat.minFac_pos _) (by
        exact_mod_cast Nat.minFac_le_of_dvd (hprime i).two_le (Finset.dvd_prod_of_mem p (Finset.mem_univ i))))
    have hh := mul_le_mul_of_nonneg_right hb (show 0 ≤ (∏ i, p i : ℝ)⁻¹ by positivity)
    simpa only [F,Finset.prod_mul_distrib,Finset.prod_inv_distrib] using hh
  calc
    _ ≤ ∑ a ∈ products k v, Real.log a.minFac*(a : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hD (by intro a _ _; positivity)
    _ ≤ ∑ p ∈ Fintype.piFinset (fun _ : Fin k => primes v),
        Real.log (∏ i, p i : ℕ).minFac*((∏ i, p i : ℕ) : ℝ)⁻¹ :=
      Finset.sum_image_le_of_nonneg (fun a _ => by positivity)
    _ ≤ ∑ p ∈ Fintype.piFinset (fun _ : Fin k => primes v), ∏ i, F (p i) := by
      apply Finset.sum_le_sum
      intro p hp
      simpa only [Nat.cast_prod] using hpoint p hp
    _ = (∑ p ∈ primes v, F p)^k := (Finset.sum_pow' _ _ _).symm
    _ ≤ (ZetaRieszPrimeFractionalBudget.momentConstant (1/(k : ℝ))*v^(1/(k : ℝ)))^k :=
      pow_le_pow_left₀ (by positivity) (prime_moment hv (by positivity)) k
    _ = logMassConstant k*v := by
      rw [mul_pow,← Real.rpow_mul_natCast hv.le]
      simp [logMassConstant,hkR.ne']

/-- At fixed count, even the unweighted cofactor reciprocal mass is at
most a square-root power. This is not a signed prime-density approximation. -/
theorem reciprocal_mass {k : ℕ} (hk : 0 < k) {v : ℝ} (hv : 0 < v)
    (D : Finset ℕ) (hD : D ⊆ products k v) :
    (∑ a ∈ D, (a : ℝ)⁻¹) ≤ variationConstant k*v^(1/2 : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  let e : ℝ := 1/(2*(k : ℝ))
  have he : 0 < e := by dsimp [e]; positivity
  have heu : e ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hprime : (∑ p ∈ primes v, (p : ℝ)⁻¹) ≤
      (2*ZetaRieszPrimeFractionalBudget.momentConstant e)*v^e := by
    have hpoint (p : ℕ) (hp : p ∈ primes v) :
        (p : ℝ)⁻¹ ≤ 2*((Real.log p)^e*(p : ℝ)⁻¹) := by
      have hp0 := (logPrimes_bounds hp).1
      have hlo : (1/2 : ℝ) ≤ Real.log p := by
        have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
          (show (2 : ℝ) ≤ p by exact_mod_cast hp0.two_le)
        linarith [Real.log_two_gt_d9]
      have hb := (Real.self_le_rpow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num) heu).trans (Real.rpow_le_rpow (by norm_num) hlo he.le)
      nlinarith [mul_le_mul_of_nonneg_right hb (show 0 ≤ (p : ℝ)⁻¹ by positivity)]
    calc
      _ ≤ ∑ p ∈ primes v, 2*((Real.log p)^e*(p : ℝ)⁻¹) := Finset.sum_le_sum hpoint
      _ ≤ _ := by rw [← Finset.mul_sum]; nlinarith only [prime_moment hv he]
  calc
    _ ≤ ∑ a ∈ products k v, (a : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hD (by intro a _ _; positivity)
    _ ≤ ∑ p ∈ Fintype.piFinset (fun _ : Fin k => primes v), ((∏ i, p i : ℕ) : ℝ)⁻¹ :=
      Finset.sum_image_le_of_nonneg (fun a _ => by positivity)
    _ = (∑ p ∈ primes v, (p : ℝ)⁻¹)^k := by
      simp only [Nat.cast_prod,Finset.prod_inv_distrib,Finset.sum_pow']
    _ ≤ ((2*ZetaRieszPrimeFractionalBudget.momentConstant e)*v^e)^k :=
      pow_le_pow_left₀ (by positivity) hprime k
    _ = variationConstant k*v^(1/2 : ℝ) := by
      rw [mul_pow,← Real.rpow_mul_natCast hv.le]
      have heq : e*(k : ℝ) = 1/2 := by dsimp [e]; field_simp
      rw [heq]
      rfl

end
end RiemannGaussian.ZetaRieszCofactorMass
