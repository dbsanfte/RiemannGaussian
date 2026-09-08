import RiemannGaussian.EtaMoebiusCoprimeWindow

/-!
# A growing odd-prime sieve with vanishing physical error

The modulus is the product of odd integers through `2*v+1`. The original
physical scale is an explicit zero-dependent positive integer power of
that modulus. The uniform polynomial sieve budget then tends to zero at
every hypothetical right-half zero, although the number of simultaneously
excluded primes grows without bound. No bound on the surviving energy is
inferred merely from the sparsity of its products.
-/

open Complex Filter
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- An explicit odd modulus containing every odd prime through `2*v+1`. -/
def pairedEtaOddSieveModulus (v : ℕ) : ℕ :=
  ∏ j ∈ Finset.range (v + 1), (2 * j + 1)

/-- Every growing sieve modulus is positive. -/
theorem pairedEtaOddSieveModulus_pos (v : ℕ) : 0 < pairedEtaOddSieveModulus v := by
  unfold pairedEtaOddSieveModulus
  exact Finset.prod_pos (fun j _ ↦ by omega)

/-- The growing modulus never removes the exceptional even prime. -/
theorem pairedEtaOddSieveModulus_odd (v : ℕ) : Odd (pairedEtaOddSieveModulus v) := by
  induction v with
  | zero => simp [pairedEtaOddSieveModulus]
  | succ v ih =>
    rw [pairedEtaOddSieveModulus, Finset.prod_range_succ]
    exact ih.mul ⟨v + 1, by ring⟩

/-- Every odd integer through the current sieve threshold divides the literal modulus. -/
theorem dvd_pairedEtaOddSieveModulus {v k : ℕ} (hk : Odd k) (hkv : k ≤ 2 * v + 1) :
    k ∣ pairedEtaOddSieveModulus v := by
  obtain ⟨j, hj⟩ := hk
  have hjv : j < v + 1 := by omega
  have hd := Finset.dvd_prod_of_mem (f := fun j : ℕ ↦ 2 * j + 1) (Finset.mem_range.mpr hjv)
  change k ∣ ∏ j ∈ Finset.range (v + 1), (2 * j + 1)
  have hk' : k = 2 * j + 1 := by omega
  rw [hk']
  exact hd

/-- The odd sieve moduli grow at least as fast as their last odd factor. -/
theorem le_pairedEtaOddSieveModulus (v : ℕ) : 2 * v + 1 ≤ pairedEtaOddSieveModulus v :=
  Nat.le_of_dvd (pairedEtaOddSieveModulus_pos v)
    (dvd_pairedEtaOddSieveModulus ⟨v, by ring⟩ le_rfl)

/-- The actual moduli tend to infinity, rather than leaving a fixed prime selection in the limit. -/
theorem pairedEtaOddSieveModulus_tendsto_atTop :
    Tendsto pairedEtaOddSieveModulus atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with v hv
  exact hv.trans (by have hh := le_pairedEtaOddSieveModulus v; omega)

/-- Every multiple of an odd prime through the growing threshold is excluded by the actual coprimality test. -/
theorem not_coprime_pairedEtaOddSieveModulus_of_prime_dvd
    {v p n : ℕ} (hp : p.Prime) (hodd : Odd p) (hpv : p ≤ 2 * v + 1) (hpn : p ∣ n) :
    ¬n.Coprime (pairedEtaOddSieveModulus v) := by
  intro hc
  have hd := Nat.dvd_gcd hpn (dvd_pairedEtaOddSieveModulus hodd hpv)
  rw [hc.gcd_eq_one] at hd
  exact hp.ne_one (Nat.dvd_one.mp hd)

/-- Every fixed odd prime is eventually excluded on every one of its product multiples. -/
theorem eventually_not_coprime_pairedEtaOddSieveModulus_of_prime_dvd
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    ∀ᶠ v : ℕ in atTop, ∀ n : ℕ, p ∣ n → ¬n.Coprime (pairedEtaOddSieveModulus v) := by
  filter_upwards [eventually_ge_atTop p] with v hv
  intro n hn
  exact not_coprime_pairedEtaOddSieveModulus_of_prime_dvd hp hodd (by omega) hn

/-- A concrete exponent pays the entire polynomial modulus loss at a hypothetical right-half zero. -/
def pairedEtaCoprimeScalePower (rho : NontrivialZetaZero) : ℕ :=
  ⌈8 / (6 * rho.1.re - 3)⌉₊ + 1

/-- The physical scale exponent is always a positive integer. -/
theorem pairedEtaCoprimeScalePower_pos (rho : NontrivialZetaZero) :
    0 < pairedEtaCoprimeScalePower rho := Nat.succ_pos _

/-- The chosen scale makes the full sieve power strictly negative, with all modulus costs included. -/
theorem pairedEtaCoprimeScalePower_rate_neg
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    4 + (pairedEtaCoprimeScalePower rho : ℝ) * (3 - 6 * rho.1.re) < 0 := by
  have ha : 0 < 6 * rho.1.re - 3 := by linarith
  have hc := Nat.le_ceil (8 / (6 * rho.1.re - 3))
  have hm := (div_le_iff₀ ha).mp hc
  simp only [pairedEtaCoprimeScalePower, Nat.cast_add, Nat.cast_one]
  nlinarith

/-- The unchanged squared/cubic schedule is evaluated at this explicit increasing original scale. -/
def pairedEtaCoprimeScale (rho : NontrivialZetaZero) (v : ℕ) : ℕ :=
  pairedEtaOddSieveModulus v ^ pairedEtaCoprimeScalePower rho

/-- Every selected original physical scale is positive. -/
theorem pairedEtaCoprimeScale_pos (rho : NontrivialZetaZero) (v : ℕ) :
    0 < pairedEtaCoprimeScale rho v :=
  pow_pos (pairedEtaOddSieveModulus_pos v) _

/-- The whole growing modulus divides each selected physical scale, so all divided windows are complete. -/
theorem pairedEtaOddSieveModulus_dvd_scale (rho : NontrivialZetaZero) (v : ℕ) :
    pairedEtaOddSieveModulus v ∣ pairedEtaCoprimeScale rho v := by
  unfold pairedEtaCoprimeScale pairedEtaCoprimeScalePower
  exact ⟨pairedEtaOddSieveModulus v ^ ⌈8 / (6 * rho.1.re - 3)⌉₊, by rw [pow_succ]; ring⟩

/-- The original physical scales are cofinal even after imposing the growing sieve. -/
theorem pairedEtaCoprimeScale_tendsto_atTop (rho : NontrivialZetaZero) :
    Tendsto (pairedEtaCoprimeScale rho) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [(pairedEtaOddSieveModulus_tendsto_atTop).eventually (eventually_ge_atTop b)] with v hv
  exact hv.trans (Nat.le_of_dvd (pairedEtaCoprimeScale_pos rho v) (pairedEtaOddSieveModulus_dvd_scale rho v))

private theorem logarithmic_power_budget {P : ℝ} (hP : 1 ≤ P) {m : ℕ} (hm : 1 ≤ m) (a : ℝ) :
    P ^ 4 * (1 + Real.log (P ^ m)) ^ 2 * (P ^ m) ^ a ≤
      (m : ℝ) ^ 2 * ((1 + Real.log P) ^ 2 * P ^ (4 + (m : ℝ) * a)) := by
  have hP0 : 0 < P := by linarith
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hl := Real.log_nonneg hP
  have he : (1 + (m : ℝ) * Real.log P) ^ 2 ≤ (m : ℝ) ^ 2 * (1 + Real.log P) ^ 2 := by
    have hh : 1 + (m : ℝ) * Real.log P ≤ (m : ℝ) * (1 + Real.log P) := by nlinarith
    have hs := (sq_le_sq₀ (by positivity) (by positivity)).mpr hh
    nlinarith
  have hp : P ^ 4 * (P ^ m) ^ a = P ^ (4 + (m : ℝ) * a) := by
    rw [Real.rpow_add hP0, Real.rpow_ofNat, Real.rpow_natCast_mul hP0.le]
  rw [Real.log_pow]
  calc
    _ ≤ P ^ 4 * ((m : ℝ) ^ 2 * (1 + Real.log P) ^ 2) * (P ^ m) ^ a := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity)
    _ = _ := by rw [← hp]; ring

/-- A fully explicit allowance for the simultaneous growing sieve; the exponent includes the entire intersection cost. -/
theorem pairedEtaMoebiusCoprimeLowCubicEnergy_growing_le
    (rho : NontrivialZetaZero) (v : ℕ) :
    pairedEtaMoebiusCoprimeLowCubicEnergy rho (pairedEtaOddSieveModulus v) (pairedEtaCoprimeScale rho v) ≤
      (pairedEtaMoebiusCoprimeSamplingConstant rho * (pairedEtaCoprimeScalePower rho : ℝ) ^ 2) *
        ((1 + Real.log (pairedEtaOddSieveModulus v)) ^ 2 *
          (pairedEtaOddSieveModulus v : ℝ) ^
            (4 + (pairedEtaCoprimeScalePower rho : ℝ) * (3 - 6 * rho.1.re))) := by
  have hb := pairedEtaMoebiusCoprimeLowCubicEnergy_le rho (pairedEtaOddSieveModulus_pos v)
    (pairedEtaOddSieveModulus_odd v) (pairedEtaCoprimeScale_pos rho v)
    (pairedEtaOddSieveModulus_dvd_scale rho v)
  have hpR : (1 : ℝ) ≤ pairedEtaOddSieveModulus v := by exact_mod_cast pairedEtaOddSieveModulus_pos v
  have hh := mul_le_mul_of_nonneg_left
    (logarithmic_power_budget hpR (pairedEtaCoprimeScalePower_pos rho) (3 - 6 * rho.1.re))
    (pairedEtaMoebiusCoprimeSamplingConstant_nonneg rho)
  apply hb.trans
  simp only [pairedEtaCoprimeScale, Nat.cast_pow]
  convert hh using 1 <;> ring

/-- The full low sieve has vanishing mean square even though every odd prime is eventually excluded simultaneously with all smaller odd primes. -/
theorem pairedEtaMoebiusCoprimeLowCubicEnergy_growing_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun v ↦ pairedEtaMoebiusCoprimeLowCubicEnergy rho
      (pairedEtaOddSieveModulus v) (pairedEtaCoprimeScale rho v)) atTop (𝓝 0) := by
  have ht := ((tendsto_log_square_mul_rpow_neg (pairedEtaCoprimeScalePower_rate_neg rho hrho)).comp
    pairedEtaOddSieveModulus_tendsto_atTop).const_mul
      (pairedEtaMoebiusCoprimeSamplingConstant rho * (pairedEtaCoprimeScalePower rho : ℝ) ^ 2)
  simp only [mul_zero] at ht
  apply squeeze_zero (fun v ↦ by unfold pairedEtaMoebiusCoprimeLowCubicEnergy; positivity)
    (pairedEtaMoebiusCoprimeLowCubicEnergy_growing_le rho)
  convert ht using 1
  ext v
  rfl

end

end RiemannGaussian
