import CheckAlpogeCubicSurplusDensity

/-! # Removing rough products of two or three primes from the cubic response

The first Mertens estimate bounds the harmonic mass of the available small
factors. Chebyshev's bound is applied only to the largest prime in each row.
-/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real Filter
open scoped Classical Topology ArithmeticFunction.vonMangoldt ArithmeticFunction.Omega

private def primesBetween (n y : ℕ) := (Ioc n y).filter Nat.Prime

private def reciprocalMass (n y : ℕ) : ℝ := ∑ p ∈ primesBetween n y, (p:ℝ)⁻¹

private theorem mem_primesBetween {n y p : ℕ} (hp : p ∈ primesBetween n y) :
    n < p ∧ p ≤ y ∧ p.Prime :=
  ⟨(mem_Ioc.mp (mem_filter.mp hp).1).1,(mem_Ioc.mp (mem_filter.mp hp).1).2,(mem_filter.mp hp).2⟩

/-- Mertens' upper and lower bounds at the two endpoints suffice for the
whole harmonic interval, with a constant independent of its length. -/
private theorem reciprocalMass_le {n y : ℕ} (hn : 1 ≤ n) (hy : n ≤ y) :
    log n * reciprocalMass n y ≤ log y - log n + (log 4+5) := by
  let A := Formalism.LogFactorialMertensBounds.A
  have hsplit : A n + (∑ p ∈ Ioc n y, Λ p/p) = A y :=
    sum_Ioc_consecutive _ (Nat.zero_le n) hy
  have hu := Formalism.LogFactorialMertensBounds.mertens_upper y (hn.trans hy)
  have hl := Formalism.LogFactorialMertensBounds.mertens_lower n hn
  change A y ≤ _ at hu
  change _ ≤ A n at hl
  have hr : log n * reciprocalMass n y ≤ ∑ p ∈ Ioc n y, Λ p/p := by
    unfold reciprocalMass primesBetween
    rw [sum_filter,mul_sum]
    apply sum_le_sum
    intro p hp
    by_cases h : p.Prime
    · rw [ite_eq_left h,ArithmeticFunction.vonMangoldt_apply_prime h,div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (log_le_log (by exact_mod_cast hn)
        (by exact_mod_cast (mem_Ioc.mp hp).1.le)) (by positivity)
    · rw [ite_eq_right h,mul_zero]
      positivity [ArithmeticFunction.vonMangoldt_nonneg (n := p)]
  linarith only [hr,hsplit,hu,hl]

/-- q=1 denotes a semiprime. Otherwise p ≤ q ≤ r are the three prime factors. -/
def sieveRoughProducts (n y : ℕ) : Finset ℕ := (Ioc n (cubicSampleEnd n)).filter fun t =>
  ∃ p q r : ℕ, p.Prime ∧ r.Prime ∧ n<p ∧ p≤y ∧ p≤r ∧
    (q=1 ∨ (q.Prime ∧ p≤q ∧ q≤r)) ∧ t=p*q*r

private theorem rough_product_abs {n y t : ℕ} (hn : 8 ≤ n) (ht : t ∈ sieveRoughProducts n y) :
    |cubicThreeFactorCoefficient n t| ≤ log t := by
  obtain ⟨hi,p,q,r,hp,hr,hnp,_,hpr,hq,rfl⟩ := mem_filter.mp ht
  have hcop {u : ℕ} (hu : u.Prime) (hs : n<u) : u.Coprime n.factorial :=
    hu.coprime_iff_not_dvd.mpr fun h => (not_le.mpr hs) (hu.dvd_factorial.mp h)
  have hqc : q.Coprime n.factorial := by
    rcases hq with rfl | ⟨hqp,hpq,_⟩
    · simp
    · exact hcop hqp (hnp.trans_le hpq)
  rw [cubicThreeFactorCoefficient_rough_eq (by omega) (mem_Ioc.mp hi).1
    (((hcop hp hnp).mul_left hqc).mul_left (hcop hr (hnp.trans_le hpr)))]
  split_ifs
  · rw [abs_of_nonpos (sub_nonpos.mpr ArithmeticFunction.vonMangoldt_le_log)]
    linarith only [ArithmeticFunction.vonMangoldt_nonneg (n := p*q*r)]
  · simpa only [abs_zero] using log_natCast_nonneg _

/-- Uniform over arbitrary endpoints for the smaller prime. Sorting the
factors lets the last prime pay for all three logarithms, including repeats. -/
private theorem sieveRoughProducts_log {n y : ℕ} (hn : 8 ≤ n) :
    ∑ t ∈ sieveRoughProducts n y, log t ≤
      (6*log 4*(n:ℝ)^4)*reciprocalMass n y*(1+reciprocalMass n (2*n^2)) := by
  let P := primesBetween n y
  let Q := insert 1 (primesBetween n (2*n^2))
  let I := P ×ˢ Q
  let R (i : ℕ × ℕ) := (Icc 0 (2*n^4/(i.1*i.2))).filter Nat.Prime
  let Z := I.sigma R
  let prod := fun z : (_ : ℕ × ℕ) × ℕ => z.1.1*z.1.2*z.2
  have hw (t : ℕ) (ht : t ∈ sieveRoughProducts n y) :
      ∃ z ∈ Z, prod z=t ∧ log t ≤ 3*log z.2 := by
    obtain ⟨hi,p,q,r,hp,hr,hnp,hpy,hpr,hq,rfl⟩ := mem_filter.mp ht
    have hE := ((mem_Ioc.mp hi).2).trans (cubicSampleEnd_le hn)
    have hq' : q ∈ Q ∧ 0<q ∧ q≤r := by
      rcases hq with rfl | ⟨hqp,hpq,hqr⟩
      · exact ⟨mem_insert_self ..,Nat.zero_lt_one,hr.one_lt.le⟩
      have hqbound : q ≤ 2*n^2 := by
        apply Nat.le_of_mul_le_mul_right _ (by positivity : 0<n^2)
        calc
          q*n^2 ≤ q*(p*r) := Nat.mul_le_mul_left _ (by rw [pow_two]; exact Nat.mul_le_mul hnp.le (hnp.le.trans hpr))
          _ = p*q*r := by ring
          _ ≤ (2*n^2)*n^2 := hE.trans_eq (by ring)
      exact ⟨mem_insert_of_mem (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hnp.trans_le hpq,hqbound⟩,hqp⟩),hqp.pos,hqr⟩
    refine ⟨⟨(p,q),r⟩,mem_sigma.mpr ⟨mem_product.mpr
      ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨hnp,hpy⟩,hp⟩,hq'.1⟩,mem_filter.mpr
      ⟨mem_Icc.mpr ⟨Nat.zero_le _,(Nat.le_div_iff_mul_le (Nat.mul_pos hp.pos hq'.2.1)).mpr
        ((Nat.mul_comm r (p*q)).le.trans hE)⟩,hr⟩⟩,rfl,?_⟩
    have hp0 : (p:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hq0 : (q:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq'.2.1.ne'
    simp only [Nat.cast_mul,log_mul (mul_ne_zero hp0 hq0) (Nat.cast_ne_zero.mpr hr.ne_zero),log_mul hp0 hq0]
    linarith only [log_le_log (Nat.cast_pos.mpr hp.pos) (show (p:ℝ)≤r by exact_mod_cast hpr),
      log_le_log (Nat.cast_pos.mpr hq'.2.1) (show (q:ℝ)≤r by exact_mod_cast hq'.2.2)]
  choose! e he hprod hlog using hw
  have hinj : Set.InjOn e ↑(sieveRoughProducts n y) := fun s hs t ht h =>
    (hprod s hs).symm.trans ((congrArg prod h).trans (hprod t ht))
  calc
    _ ≤ ∑ z ∈ Z, 3*log z.2 := sum_le_sum_of_injOn e hinj
      (by intro z hz; obtain ⟨t,ht,rfl⟩ := mem_image.mp hz; exact he t ht) hlog
      (fun z _ _ => by positivity [log_natCast_nonneg z.2])
    _ = ∑ i ∈ I, 3*Chebyshev.theta ((2*n^4/(i.1*i.2):ℕ):ℝ) := by
      rw [show Z=I.sigma R from rfl,sum_sigma]
      apply sum_congr rfl
      intro i _
      rw [Chebyshev.theta_eq_sum_Icc,Nat.floor_natCast,mul_sum]
    _ ≤ ∑ i ∈ I, (6*log 4*(n:ℝ)^4)*(i.1:ℝ)⁻¹*(i.2:ℝ)⁻¹ := by
      apply sum_le_sum
      intro i hi
      obtain ⟨hP,hQ⟩ := mem_product.mp hi
      have hp := (mem_primesBetween hP).2.2.pos
      have hq : 0 < i.2 := by
        rcases mem_insert.mp hQ with h | h
        · omega
        · exact (mem_primesBetween h).2.2.pos
      have hdiv : ((2*n^4/(i.1*i.2):ℕ):ℝ) ≤ 2*(n:ℝ)^4/((i.1:ℝ)*i.2) :=
        (le_div_iff₀ (mul_pos (Nat.cast_pos.mpr hp) (Nat.cast_pos.mpr hq))).mpr
          (by exact_mod_cast Nat.div_mul_le_self (2*n^4) (i.1*i.2))
      have hb := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (2*n^4/(i.1*i.2)))
      have hh := mul_le_mul_of_nonneg_left hdiv (show 0≤log 4 by positivity)
      simp only [div_eq_mul_inv,mul_inv_rev] at hh
      linarith only [hb,hh]
    _ = _ := by
      have hone : 1 ∉ primesBetween n (2*n^2) := by
        intro h
        exact Nat.not_prime_one (mem_primesBetween h).2.2
      rw [show I=P ×ˢ Q from rfl,sum_product]
      simp only [← mul_sum,← sum_mul]
      rw [show Q=insert 1 (primesBetween n (2*n^2)) from rfl,sum_insert hone,Nat.cast_one,inv_one]
      rfl

/-- The sum of the divisor counts on an initial interval costs one harmonic sum. -/
private theorem divisor_prefix_le (b : ℕ) :
    (∑ t ∈ Ioc 0 b, (t.divisors.card:ℝ)) ≤ (b:ℝ)*(1+log b) := by
  have hsum := ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div b
  simp only [ArithmeticFunction.sigma_zero_apply] at hsum
  calc
    _ = ∑ d ∈ Ioc 0 b, ((b/d:ℕ):ℝ) := by exact_mod_cast hsum
    _ ≤ ∑ d ∈ Ioc 0 b, (b:ℝ)*(d:ℝ)⁻¹ := by
      apply sum_le_sum
      intro d hd
      rw [← div_eq_mul_inv]
      exact (le_div_iff₀ (Nat.cast_pos.mpr (mem_Ioc.mp hd).1)).mpr (by exact_mod_cast Nat.div_mul_le_self b d)
    _ ≤ _ := by
      rw [← mul_sum,show Ioc 0 b=Icc 1 b by ext; simp; omega]
      exact mul_le_mul_of_nonneg_left (primeWindow_harmonic_le (a := 1) le_rfl) (Nat.cast_nonneg _)

/-- Absolute mass of every three-factor coefficient up to an arbitrary cutoff,
including integers with small prime divisors. -/
theorem cubicThreeFactor_prefix_abs (n b : ℕ) :
    ∑ t ∈ Ioc 0 b, |cubicThreeFactorCoefficient n t| ≤ 3*(b:ℝ)*(1+log b)^2 := by
  have hb := log_natCast_nonneg b
  calc
    _ ≤ ∑ t ∈ Ioc 0 b, (1+2*(t.divisors.card:ℝ))*log b := by
      apply sum_le_sum
      intro t ht
      obtain ⟨ht0,htb⟩ := mem_Ioc.mp ht
      have hlog := log_le_log (Nat.cast_pos.mpr ht0) (show (t:ℝ) ≤ b by exact_mod_cast htb)
      unfold cubicThreeFactorCoefficient
      split_ifs
      · rw [abs_zero]; positivity
      · exact (abs_cubicRoughCoefficient_le_divisors ht0 n).trans
          (mul_le_mul_of_nonneg_left hlog (by positivity))
    _ = ((b:ℝ)+2*∑ t ∈ Ioc 0 b, (t.divisors.card:ℝ))*log b := by
      rw [← sum_mul,sum_add_distrib,← mul_sum]
      simp
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (divisor_prefix_le b) hb
      nlinarith only [h,mul_nonneg (Nat.cast_nonneg (α := ℝ) b) hb,
        mul_nonneg (Nat.cast_nonneg (α := ℝ) b) (sq_nonneg (log b)),Nat.cast_nonneg (α := ℝ) b]

/-- The whole prefix is charged absolutely. Its endpoint is n⁴ divided
by the cube of the binary logarithm rounded up to the next integer. -/
def roughRangeStart (n : ℕ) : ℕ := n^4/(Nat.log 2 n+1)^3

/-- This endpoint for the least prime is a fixed power of the sample index. -/
def roughRangePrimeEnd (n : ℕ) : ℕ := ⌊(n:ℝ)^(1+(1/16777216:ℝ))⌋₊

theorem cubicLog_le_depth {n : ℕ} (hn : 0<n) : log n ≤ ((Nat.log 2 n+1:ℕ):ℝ) := by
  let k := Nat.log 2 n+1
  have h := log_le_log (Nat.cast_pos.mpr hn) (show (n:ℝ)≤(2:ℝ)^k by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le)
  rw [log_pow] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2))
    (Nat.cast_nonneg k)).trans_eq (by ring))

private theorem prefix_cost {n : ℕ} (hn : 8 ≤ n) :
    ((Nat.log 2 n+1:ℕ):ℝ)*(∑ t ∈ Ioc 0 (roughRangeStart n), |cubicThreeFactorCoefficient n t|) ≤
      75*(n:ℝ)^4 := by
  let k := Nat.log 2 n+1
  let b := roughRangeStart n
  have hk : (1:ℝ) ≤ k := by exact_mod_cast (show 1≤k by dsimp [k]; omega)
  have hsmall : (b:ℝ)*(k:ℝ)^3 ≤ (n:ℝ)^4 := by exact_mod_cast Nat.div_mul_le_self (n^4) (k^3)
  have hnlog := cubicLog_le_depth (by omega : 0<n)
  have hb : log (b:ℝ) ≤ 4*(k:ℝ) := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h]; simp
    have hbnd : b ≤ n^4 := Nat.div_le_self _ _
    have hl := log_le_log (Nat.cast_pos.mpr h) (show (b:ℝ)≤(n:ℝ)^4 by exact_mod_cast hbnd)
    rw [log_pow,Nat.cast_ofNat] at hl
    change log n ≤ (k:ℝ) at hnlog
    linarith only [hl,hnlog]
  have hs := pow_le_pow_left₀ (by positivity [log_natCast_nonneg b] : (0:ℝ)≤1+log b)
    (show 1+log (b:ℝ) ≤ 5*k by linarith only [hk,hb]) 2
  have hcost := (cubicThreeFactor_prefix_abs n b).trans (mul_le_mul_of_nonneg_left hs (by positivity))
  have h := mul_le_mul_of_nonneg_left hcost (Nat.cast_nonneg (α := ℝ) k)
  change (k:ℝ)*_ ≤ _
  linarith only [h,hsmall]

private theorem harmonic_range_cost {n : ℕ} (hn : 8 ≤ n) (hbig : 4294967296 ≤ log (n:ℝ)) :
    reciprocalMass n (roughRangePrimeEnd n) ≤ 9/(8*16777216:ℝ) ∧
      reciprocalMass n (2*n^2) ≤ 3/2 := by
  let y := roughRangePrimeEnd n
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1≤n by omega)
  have hpow : (n:ℝ) ≤ (n:ℝ)^(1+(1/16777216:ℝ)) := by
    simpa only [rpow_one] using
      rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1:ℝ) ≤ 1+1/16777216)
  have hny : n ≤ y := Nat.le_floor hpow
  have hl := log_le_log (Nat.cast_pos.mpr (show 0<y by omega))
    (Nat.floor_le (rpow_nonneg (Nat.cast_nonneg _) _) : (y:ℝ) ≤ _)
  rw [log_rpow (by positivity)] at hl
  have h4 : log 4 ≤ 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,log_pow,Nat.cast_ofNat]
    linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have h2 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hh := reciprocalMass_le (by omega : 1≤n) hny
  have h2n : n ≤ 2*n^2 := by nlinarith
  have hh' := reciprocalMass_le (by omega : 1≤n) h2n
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,log_mul (by norm_num) (by positivity),log_pow,Nat.cast_ofNat] at hh'
  have hp : 0<log (n:ℝ) := by linarith
  constructor
  · apply le_of_mul_le_mul_left (a := log (n:ℝ)) _ hp
    change _ * reciprocalMass n y ≤ _
    linarith only [hh,hl,h4,hbig]
  · apply le_of_mul_le_mul_left (a := log (n:ℝ)) _ hp
    linarith only [hh',h4,h2,hbig]

/-- All coefficients in the prefix and all selected rough products. A term
lying in both sets is included only once. -/
def roughRangeDebits (n : ℕ) := Ioc 0 (roughRangeStart n) ∪ sieveRoughProducts n (roughRangePrimeEnd n)

def roughRangeDebitCoefficient (n t : ℕ) : ℝ :=
  if t ∈ roughRangeDebits n then cubicThreeFactorCoefficient n t else 0

/-- The new response needs only the coefficients outside the prefix, the
covered rough products, and the positive triples used to pay for them. -/
def roughRangeCoefficient (n t : ℕ) : ℝ :=
  if t ∈ crossingPrimeTriples n ∨ t ∈ roughRangeDebits n then 0 else cubicThreeFactorCoefficient n t

private theorem debit_cost {n : ℕ} (hn : 64 ≤ n) (hbig : 4294967296 ≤ log (n:ℝ)) :
    |cubicWeightedResponse n (roughRangeDebitCoefficient n)| ≤ ((3/327680:ℝ)-1/200000)*(n:ℝ)^4 := by
  let b := roughRangeStart n
  let y := roughRangePrimeEnd n
  let P := Ioc 0 b
  let R := sieveRoughProducts n y
  let k := Nat.log 2 n+1
  let f := fun t => |cubicThreeFactorCoefficient n t|
  have h8 : 8 ≤ n := by omega
  have hsum : (∑ t ∈ Icc 0 (cubicSampleEnd n), |roughRangeDebitCoefficient n t|) ≤
      (∑ t ∈ P, f t) + ∑ t ∈ R, log t := by
    calc
      _ = ∑ t ∈ (Icc 0 (cubicSampleEnd n)).filter (· ∈ roughRangeDebits n), f t := by
        rw [sum_filter]
        apply sum_congr rfl
        intro t _
        by_cases h : t ∈ roughRangeDebits n <;> simp [roughRangeDebitCoefficient,h,f]
      _ ≤ ∑ t ∈ P ∪ R, f t := sum_le_sum_of_subset_of_nonneg
        (fun _ h => (mem_filter.mp h).2) (fun _ _ _ => abs_nonneg _)
      _ ≤ (∑ t ∈ P, f t) + ∑ t ∈ R, f t := by
        have h := sum_union_inter (s₁ := P) (s₂ := R) (f := f)
        linarith only [h,show 0 ≤ ∑ t ∈ P ∩ R, f t from sum_nonneg fun t _ => abs_nonneg _]
      _ ≤ _ := add_le_add_right (sum_le_sum fun t ht => rough_product_abs h8 ht) _
  have hk : 4294967296 ≤ (k:ℝ) := hbig.trans (cubicLog_le_depth (by omega))
  have hpc := prefix_cost h8
  change (k:ℝ)*(∑ t ∈ P, f t) ≤ _ at hpc
  have hprefix : (4294967296:ℝ)*(∑ t ∈ P, f t) ≤ 75*(n:ℝ)^4 :=
    (mul_le_mul_of_nonneg_right hk (sum_nonneg fun t _ => abs_nonneg _)).trans hpc
  obtain ⟨hP,hQ⟩ := harmonic_range_cost h8 hbig
  have hpos : 0 ≤ reciprocalMass n (2*n^2) := sum_nonneg fun p _ => by positivity
  have hprod := mul_le_mul hP (add_le_add_right hQ 1) (by linarith only [hpos]) (by norm_num)
  have h4 : log 4 ≤ 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,log_pow,Nat.cast_ofNat]
    linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hcoef := mul_le_mul h4 hprod (mul_nonneg (sum_nonneg fun p _ => by positivity)
    (by linarith only [hpos])) (by norm_num)
  have hR := sieveRoughProducts_log (y := y) h8
  change _ ≤ _*reciprocalMass n y*(1+reciprocalMass n (2*n^2)) at hR
  change log 4*(reciprocalMass n y*(1+reciprocalMass n (2*n^2))) ≤ _ at hcoef
  have hq := mul_le_mul_of_nonneg_right hcoef (pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 4)
  have hw := (cubicWeightedResponse_abs h8 _).trans (mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ)≤2))
  linarith only [hprefix,hR,hq,hw,pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 4]

private theorem crossing_untouched {n t : ℕ} (hn : 64 ≤ n) (ht : t ∈ crossingPrimeTriples n) :
    t ∉ roughRangeDebits n ∧ cubicCompensatedCoefficient n t = cubicThreeFactorCoefficient n t := by
  obtain ⟨_,hl,_,a,b,r,ha,hb,hr,h2,hab,hbn,hnr,_,rfl⟩ := mem_filter.mp ht
  have hpow : 0<n^4 := by positivity
  have hk : 2 ≤ Nat.log 2 n + 1 := by
    have := (Nat.le_log_iff_pow_le (by decide : 1<2) (by omega : n≠0)).mpr (by omega : 2^1 ≤ n)
    omega
  have he : roughRangeStart n*2 ≤ n^4 := (Nat.mul_le_mul_left _ (hk.trans
    (Nat.le_self_pow (by decide : 3 ≠ 0) _))).trans (Nat.div_mul_le_self _ _)
  have hscale : 64*n^3 ≤ n^4 := (Nat.mul_le_mul_right (n^3) hn).trans_eq (by ring)
  have hodd {u : ℕ} (hp : u.Prime) (hu : 2<u) : ¬2 ∣ u := fun h =>
    hu.ne ((hp.dvd_iff_eq (by decide : 2≠1)).mp h).symm
  constructor
  · intro h
    rcases mem_union.mp h with h | h
    · have hh := (mem_Ioc.mp h).2
      omega
    obtain ⟨_,p,q,z,hp,hz,hnp,_,hpz,hq,he'⟩ := mem_filter.mp h
    have hd : a ∣ p*q*z := he' ▸ dvd_mul_of_dvd_left (dvd_mul_right a b) r
    rcases ha.dvd_mul.mp hd with hd | hd
    · rcases ha.dvd_mul.mp hd with hd | hd
      · have := (hp.dvd_iff_eq ha.ne_one).mp hd
        omega
      · rcases hq with rfl | ⟨hqp,hpq,_⟩
        · exact ha.not_dvd_one hd
        · have := (hqp.dvd_iff_eq ha.ne_one).mp hd
          omega
    · have := (hz.dvd_iff_eq ha.ne_one).mp hd
      omega
  · apply cubicCompensatedCoefficient_of_odd_upper (by omega) (by omega)
    rw [Nat.prime_two.dvd_mul,Nat.prime_two.dvd_mul]
    exact not_or.mpr ⟨not_or.mpr ⟨hodd ha h2,hodd hb (by omega)⟩,hodd hr (by omega)⟩

/-- Exact reconstruction from the original three-factor response. This bypasses
the earlier semiprime transfers and retains every sign before clipping. -/
theorem roughRangeResponse_eq {n : ℕ} (hn : 64 ≤ n) :
    cubicWeightedResponse n (roughRangeCoefficient n) + crossingTripleMass n +
      cubicWeightedResponse n (roughRangeDebitCoefficient n) =
        cubicWeightedResponse n (cubicThreeFactorCoefficient n) := by
  have he : roughRangeCoefficient n = cubicThreeFactorCoefficient n -
      crossingTripleCoefficient n - roughRangeDebitCoefficient n := by
    funext t
    by_cases ht : t ∈ crossingPrimeTriples n
    · obtain ⟨hD,hc⟩ := crossing_untouched hn ht
      simp [roughRangeCoefficient,crossingTripleCoefficient,roughRangeDebitCoefficient,ht,hD,hc]
    · by_cases hD : t ∈ roughRangeDebits n <;>
        simp [roughRangeCoefficient,crossingTripleCoefficient,roughRangeDebitCoefficient,ht,hD]
  rw [he,← cubicWeightedResponse_sub,← cubicWeightedResponse_sub,crossingTripleResponse_eq hn]
  ring

theorem roughRangeResponse_quartic_margin_sharp :
    ∃ N : ℕ, ∀ n ≥ N, cubicWeightedResponse n (roughRangeCoefficient n) +
      (1/200000:ℝ)*(n:ℝ)^4 ≤ cubicWeightedResponse n (cubicThreeFactorCoefficient n) := by
  obtain ⟨A,hA⟩ := crossingTripleMass_quartic
  have hlim : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨B,hB⟩ := eventually_atTop.mp (hlim.eventually_ge_atTop (4294967296:ℝ))
  refine ⟨max 64 (max A B),fun n hn => ?_⟩
  have h64 : 64 ≤ n := by omega
  have hdebit := (abs_le.mp (debit_cost h64 (hB n (by omega)))).1
  linarith only [roughRangeResponse_eq h64,hA n (by omega),hdebit]

theorem roughRangeResponse_quartic_margin :
    ∃ N : ℕ, ∀ n ≥ N, cubicWeightedResponse n (roughRangeCoefficient n) +
      (3/655360:ℝ)*(n:ℝ)^4 ≤ cubicWeightedResponse n (cubicThreeFactorCoefficient n) := by
  obtain ⟨N,hN⟩ := roughRangeResponse_quartic_margin_sharp
  refine ⟨N,fun n hn => ?_⟩
  linarith only [hN n hn,pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 4]

theorem roughRangeCoefficient_prefix {n t : ℕ} (ht : t ∈ Ioc 0 (roughRangeStart n)) :
    roughRangeCoefficient n t = 0 :=
  ite_eq_left (Or.inr (mem_union_left _ ht))

theorem roughRangeCoefficient_semiprime {n p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hnp : n<p) (hpr : p≤r) (hy : (p:ℝ) ≤ (n:ℝ)^(1+(1/16777216:ℝ)))
    (hE : p*r ≤ cubicSampleEnd n) : roughRangeCoefficient n (p*r)=0 := by
  have h : p*r ∈ sieveRoughProducts n (roughRangePrimeEnd n) := mem_filter.mpr
    ⟨mem_Ioc.mpr ⟨hnp.trans_le (Nat.le_mul_of_pos_right _ hr.pos),hE⟩,
      p,1,r,hp,hr,hnp,Nat.le_floor hy,hpr,Or.inl rfl,by simp⟩
  exact ite_eq_left (Or.inr (mem_union_right _ h))

theorem roughRangeCoefficient_threePrimes {n p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hnp : n<p) (hpq : p≤q) (hqr : q≤r) (hy : (p:ℝ) ≤ (n:ℝ)^(1+(1/16777216:ℝ)))
    (hE : p*q*r ≤ cubicSampleEnd n) : roughRangeCoefficient n (p*q*r)=0 := by
  have h : p*q*r ∈ sieveRoughProducts n (roughRangePrimeEnd n) := mem_filter.mpr
    ⟨mem_Ioc.mpr ⟨(hnp.trans_le (Nat.le_mul_of_pos_right _ hq.pos)).trans_le
      (Nat.le_mul_of_pos_right _ hr.pos),hE⟩,
      p,q,r,hp,hr,hnp,Nat.le_floor hy,hpq.trans hqr,Or.inr ⟨hq,hpq,hqr⟩,rfl⟩
  exact ite_eq_left (Or.inr (mem_union_right _ h))

theorem cubicDepth_power_eventually (p : ℕ) {C ε : ℝ} (hC : 0≤C) (hε : 0<ε) :
    ∃ N : ℕ, ∀ n ≥ N, C*((Nat.log 2 n+1:ℕ):ℝ)^p ≤ (n:ℝ)^ε := by
  have h := ((isLittleO_log_rpow_rpow_atTop (p:ℝ) hε).const_mul_left (C*3^p)).bound
    (by norm_num : (0:ℝ)<1)
  have ht := h.and (tendsto_log_atTop.eventually_ge_atTop 1)
  obtain ⟨T,hT⟩ := eventually_atTop.mp ht
  refine ⟨max 2 ⌈T⌉₊,fun n hn => ?_⟩
  obtain ⟨hb,hlog⟩ := hT n (Nat.le_ceil T |>.trans (by exact_mod_cast (show ⌈T⌉₊≤n by omega)))
  change 1 ≤ log (n:ℝ) at hlog
  change ‖(C*3^p)*log (n:ℝ)^(p:ℝ)‖ ≤ 1*‖(n:ℝ)^ε‖ at hb
  rw [rpow_natCast,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity [log_natCast_nonneg n]),
    abs_of_nonneg (rpow_nonneg (Nat.cast_nonneg _) _),one_mul] at hb
  have hn0 : 0<n := by omega
  have hpow := log_le_log (by positivity : (0:ℝ)<2^(Nat.log 2 n))
    (show (2:ℝ)^(Nat.log 2 n) ≤ n by exact_mod_cast Nat.pow_log_le_self 2 hn0.ne')
  rw [log_pow] at hpow
  have hk := mul_le_mul_of_nonneg_left
    (show (1/2:ℝ) ≤ log 2 by linarith only [Real.log_two_gt_d9]) (Nat.cast_nonneg (Nat.log 2 n))
  have hd : ((Nat.log 2 n+1:ℕ):ℝ) ≤ 3*log n := by push_cast; linarith only [hlog,hpow,hk]
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hd p) hC
  rw [mul_pow] at hp
  linarith only [hp,hb]

/-- Every fixed subquartic power eventually falls inside the removed prefix. -/
theorem roughRangeStart_covers_power {ε : ℝ} (hε : 0<ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℕ, (t:ℝ) ≤ (n:ℝ)^(4-ε) → t ≤ roughRangeStart n := by
  obtain ⟨N,h⟩ := cubicDepth_power_eventually 3 (C := 1) zero_le_one hε
  refine ⟨max 1 N,fun n hn t ht => ?_⟩
  have hn0 : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hk := h n (by omega)
  rw [one_mul] at hk
  have hb := mul_le_mul ht hk (pow_nonneg (Nat.cast_nonneg _) _) (rpow_pos_of_pos hn0 _).le
  rw [← rpow_add hn0,sub_add_cancel,show (4:ℝ)=((4:ℕ):ℝ) by norm_num,rpow_natCast] at hb
  exact (Nat.le_div_iff_mul_le (by positivity)).mpr (by exact_mod_cast hb)

/-- For a retained index only multiples in the short smoothing interval can change its quotient. -/
def roughRangeCrossings (n : ℕ) : Finset ℕ :=
  (Ioc (max (3*n^3) (roughRangeStart n)) (cubicSampleEnd n)).filter fun t =>
    cubicSampleStart n/t < cubicSampleEnd n/t

theorem roughRangeCrossings_quotient {n t : ℕ} (hn : 8 ≤ n) (ht : t ∈ roughRangeCrossings n) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ 2*(Nat.log 2 n+1)^3 ∧
      cubicSampleStart n < j*t ∧ j*t ≤ cubicSampleEnd n := by
  obtain ⟨hi,hq⟩ := mem_filter.mp ht
  have ht0 := (Nat.zero_le _).trans_lt (mem_Ioc.mp hi).1
  have hmin := (le_max_right _ _).trans_lt (mem_Ioc.mp hi).1
  have hnt := (Nat.div_lt_iff_lt_mul (by positivity : 0<(Nat.log 2 n+1)^3)).mp hmin
  let j := cubicSampleEnd n/t
  have htop : j*t ≤ cubicSampleEnd n := Nat.div_mul_le_self _ _
  have hstart := (Nat.div_lt_iff_lt_mul ht0).mp hq
  have hmul := Nat.mul_le_mul_left 2 hnt.le
  have hj : j ≤ 2*(Nat.log 2 n+1)^3 := by
    apply Nat.le_of_mul_le_mul_right _ ht0
    exact (htop.trans (cubicSampleEnd_le hn)).trans (hmul.trans_eq (by ring))
  exact ⟨j,(Nat.zero_le _).trans_lt hq,hj,hstart,htop⟩

theorem cubicQuotientInterval_count {a b j : ℕ} (hab : a ≤ b) (hj : 0 < j) :
    ((b/j-a/j:ℕ):ℝ) ≤ 1 + ((b-a:ℕ):ℝ)*(j:ℝ)⁻¹ := by
  have hleft : (a:ℝ) ≤ (((a/j:ℕ):ℝ)+1)*j := by
    exact_mod_cast (show a ≤ (a/j+1)*j by simpa [mul_comm] using (Nat.lt_mul_div_succ a hj).le)
  have hright : ((b/j:ℕ):ℝ)*j ≤ b := by exact_mod_cast Nat.div_mul_le_self b j
  have hjR : 0 < (j:ℝ) := by exact_mod_cast hj
  rw [Nat.cast_sub (Nat.div_le_div_right hab),Nat.cast_sub hab]
  apply le_of_mul_le_mul_right (a := (j:ℝ)) _ hjR
  rw [add_mul,one_mul,mul_assoc,inv_mul_cancel₀ hjR.ne',mul_one,sub_mul]
  linarith only [hleft,hright]

/-- The full moving correction is supported on at most a smoothing width times
a harmonic sum over the possible quotients, plus one endpoint per quotient. -/
theorem roughRangeCrossings_card {n : ℕ} (hn : 8 ≤ n) :
    let k := Nat.log 2 n+1
    let J : ℕ := 2*k^3
    ((roughRangeCrossings n).card:ℝ) ≤ (J:ℝ) +
      (2*k*n^3:ℕ)*(1+log J) := by
  let k := Nat.log 2 n+1
  let J : ℕ := 2*k^3
  let a := cubicSampleStart n
  let b := cubicSampleEnd n
  let row := fun j : ℕ => Ioc (a/j) (b/j)
  have hab : a ≤ b := (Nat.sub_le _ _).trans (Nat.le_add_right _ _)
  have hcov : roughRangeCrossings n ⊆ (Icc 1 J).biUnion row := by
    intro t ht
    obtain ⟨j,hj,hJ,hlo,hhi⟩ := roughRangeCrossings_quotient hn ht
    exact mem_biUnion.mpr ⟨j,mem_Icc.mpr ⟨hj,hJ⟩,mem_Ioc.mpr
      ⟨(Nat.div_lt_iff_lt_mul (by omega : 0 < j)).mpr (by simpa [mul_comm] using hlo),
       (Nat.le_div_iff_mul_le (by omega : 0 < j)).mpr (by simpa [mul_comm] using hhi)⟩⟩
  have hcard := (card_le_card hcov).trans card_biUnion_le
  have hrow (j : ℕ) (hj : j ∈ Icc 1 J) :
      ((row j).card:ℝ) ≤ 1 + (2*k*n^3:ℕ)*(j:ℝ)⁻¹ := by
    have hj0 : 0 < j := (mem_Icc.mp hj).1
    have hw : b-a ≤ 2*k*n^3 := by
      change (n^4+k*n^3)-(n^4-k*n^3) ≤ 2*k*n^3
      rw [mul_assoc]
      omega
    change ((Ioc (a/j) (b/j)).card:ℝ) ≤ _
    rw [Nat.card_Ioc]
    exact (cubicQuotientInterval_count hab hj0).trans (by gcongr)
  have hc : ((roughRangeCrossings n).card:ℝ) ≤ ∑ j ∈ Icc 1 J, ((row j).card:ℝ) := by
    exact_mod_cast hcard
  refine hc.trans ((sum_le_sum hrow).trans ?_)
  rw [sum_add_distrib,← mul_sum]
  have hones : (∑ _j ∈ Icc 1 J, (1:ℝ)) = J := by simp [Nat.card_Icc]
  rw [hones]
  exact add_le_add_right (mul_le_mul_of_nonneg_left (primeWindow_harmonic_le (a := 1) le_rfl)
    (Nat.cast_nonneg (2*k*n^3))) _

theorem roughRangeCrossings_unique :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ roughRangeCrossings n, ∃! j : ℕ,
      cubicSampleStart n < j*t ∧ j*t ≤ cubicSampleEnd n := by
  obtain ⟨N,hN⟩ := cubicDepth_power_eventually 4 (C := 2) (by norm_num) (by norm_num : (0:ℝ)<1)
  refine ⟨max 8 N,fun n hn t ht => ?_⟩
  obtain ⟨j,_,_,hj⟩ := roughRangeCrossings_quotient (by omega : 8≤n) ht
  refine ⟨j,hj,fun i hi => ?_⟩
  have hk := hN n (by omega)
  rw [rpow_one] at hk
  let k := Nat.log 2 n+1
  have hk' : 2*k^4 ≤ n := by exact_mod_cast hk
  have hwidth : 2*k*n^3 ≤ roughRangeStart n := (Nat.le_div_iff_mul_le (by positivity : 0<k^3)).mpr (by
    calc
      _ = (2*k^4)*n^3 := by ring
      _ ≤ n*n^3 := Nat.mul_le_mul_right _ hk'
      _ = _ := by ring)
  have hbelow := hwidth.trans_lt ((le_max_right _ _).trans_lt (mem_Ioc.mp (mem_filter.mp ht).1).1)
  have htwice : 2*(k*n^3) < t := (show 2*(k*n^3) = 2*k*n^3 by ring).trans_lt hbelow
  change n^4-k*n^3 < i*t ∧ i*t ≤ n^4+k*n^3 at hi
  change n^4-k*n^3 < j*t ∧ j*t ≤ n^4+k*n^3 at hj
  have hlt {a b : ℕ} (h : a<b) : a*t+t ≤ b*t := (Nat.succ_mul a t).ge.trans (Nat.mul_le_mul_right t h)
  rcases lt_trichotomy i j with he | he | he
  · have := hlt he; omega
  · exact he
  · have := hlt he; omega


/-- The contribution of an upper coefficient at one sample, including its support cutoff. -/
def activeCubicWeight (M t : ℕ) : ℝ := if t ≤ M then weight M t else 0

private theorem cubicMean_congr_on {n : ℕ} (hn : 8 ≤ n) {f g : ℕ → ℝ}
    (h : ∀ M, cubicSampleStart n ≤ M → M ≤ cubicSampleEnd n → f M = g M) :
    cubicMean n f = cubicMean n g :=
  le_antisymm (cubicMean_le_on hn (fun M a b => (h M a b).le))
    (cubicMean_le_on hn (fun M a b => (h M a b).ge))

private theorem weight_quotient {t : ℕ} (ht : 0 < t) (M : ℕ) :
    weight M t = 1 + ((M/t:ℕ):ℝ) - (M:ℝ)/t := by
  have h : ((M%t:ℕ):ℝ) + t*((M/t:ℕ):ℝ) = M := by exact_mod_cast Nat.mod_add_div M t
  unfold weight
  field_simp [show (t:ℝ) ≠ 0 by exact_mod_cast ht.ne']
  linarith only [h]

private def quotientAffine (q t : ℕ) : ℕ → ℝ :=
  (fun _ => 1 + (q:ℝ)) - (t:ℝ)⁻¹ • (fun M : ℕ => (M:ℝ))

private theorem quotientAffine_apply (q t M : ℕ) :
    quotientAffine q t M = 1 + (q:ℝ) - (M:ℝ)/t := by
  simp [quotientAffine,div_eq_mul_inv,mul_comm]

private theorem cubicMean_quotientAffine {n : ℕ} (hn : 8 ≤ n) (q t : ℕ) :
    cubicMean n (quotientAffine q t) = quotientAffine q t (n^4) := by
  unfold quotientAffine
  rw [map_sub,map_smul,cubicMean_const,cubicMean_first_moment hn]
  simp [smul_eq_mul]

/-- Away from a quotient crossing the upper weight averages exactly to its central value. -/
theorem cubicMean_activeWeight_eq {n t : ℕ} (hn : 8 ≤ n) (ht : 0 < t)
    (hq : cubicSampleStart n/t = cubicSampleEnd n/t) :
    cubicMean n (fun M => activeCubicWeight M t) = activeCubicWeight (n^4) t := by
  have hs : cubicSampleStart n ≤ n^4 := Nat.sub_le _ _
  have he : n^4 ≤ cubicSampleEnd n := Nat.le_add_right _ _
  have hqM (M : ℕ) (a : cubicSampleStart n ≤ M) (b : M ≤ cubicSampleEnd n) :
      M/t = cubicSampleStart n/t :=
    le_antisymm ((Nat.div_le_div_right b).trans_eq hq.symm) (Nat.div_le_div_right a)
  by_cases hz : cubicSampleStart n/t = 0
  · have h (M : ℕ) (a : cubicSampleStart n ≤ M) (b : M ≤ cubicSampleEnd n) :
        activeCubicWeight M t = 0 := by
      have hlt := (Nat.div_lt_iff_lt_mul ht).mp (show M/t < 1 by rw [hqM M a b,hz]; decide)
      simp [activeCubicWeight,show ¬ t ≤ M by omega]
    exact (cubicMean_congr_on (g := fun _ => 0) hn h).trans
      ((cubicMean_const n 0).trans (h _ hs he).symm)
  · have h (M : ℕ) (a : cubicSampleStart n ≤ M) (b : M ≤ cubicSampleEnd n) :
        activeCubicWeight M t = quotientAffine (cubicSampleStart n/t) t M := by
      have hle : t ≤ M := le_of_not_gt (fun hh => hz ((hqM M a b).symm.trans (Nat.div_eq_of_lt hh)))
      rw [activeCubicWeight,ite_eq_left hle,weight_quotient ht,hqM M a b,quotientAffine_apply]
    rw [cubicMean_congr_on hn h,h _ hs he]
    exact cubicMean_quotientAffine hn _ _

private theorem activeCubicWeight_nonneg (M : ℕ) {t : ℕ} (ht : 0 < t) : 0 ≤ activeCubicWeight M t := by
  by_cases h : t ≤ M
  · simpa [activeCubicWeight,h] using (weight_mem (N := M) ht).1
  · simp [activeCubicWeight,h]

/-- If the central quotient agrees with the left endpoint, smoothing increases
the weight. If it agrees with the right endpoint, smoothing decreases it. -/
theorem cubicMean_activeWeight_sides {n t : ℕ} (hn : 8 ≤ n) (ht : 0 < t) :
    (n^4/t = cubicSampleStart n/t →
      activeCubicWeight (n^4) t ≤ cubicMean n (fun M => activeCubicWeight M t)) ∧
    (n^4/t = cubicSampleEnd n/t →
      cubicMean n (fun M => activeCubicWeight M t) ≤ activeCubicWeight (n^4) t) := by
  let q := n^4/t
  have hcenter (h : t ≤ n^4) : activeCubicWeight (n^4) t = quotientAffine q t (n^4) := by
    rw [activeCubicWeight,ite_eq_left h,weight_quotient ht,quotientAffine_apply]
  constructor
  · intro hs
    by_cases h : t ≤ n^4
    · have hq : 1 ≤ q := (Nat.le_div_iff_mul_le ht).mpr (by simpa)
      rw [hcenter h,← cubicMean_quotientAffine hn]
      apply cubicMean_le_on hn
      intro M a _
      have hM : q ≤ M/t := (show q = cubicSampleStart n/t from hs).le.trans (Nat.div_le_div_right a)
      have hm : t ≤ M := by simpa using (Nat.le_div_iff_mul_le ht).mp (hq.trans hM)
      rw [activeCubicWeight,ite_eq_left hm,weight_quotient ht,quotientAffine_apply]
      linarith only [show (q:ℝ) ≤ ((M/t:ℕ):ℝ) by exact_mod_cast hM]
    · rw [activeCubicWeight,ite_eq_right h,← cubicMean_const n 0]
      exact cubicMean_le_on hn (fun M _ _ => activeCubicWeight_nonneg M ht)
  · intro he
    by_cases h : t ≤ n^4
    · rw [hcenter h,← cubicMean_quotientAffine hn]
      apply cubicMean_le_on hn
      intro M _ b
      have hM : M/t ≤ q := (Nat.div_le_div_right b).trans_eq he.symm
      rw [quotientAffine_apply]
      by_cases hm : t ≤ M
      · rw [activeCubicWeight,ite_eq_left hm,weight_quotient ht]
        linarith only [show ((M/t:ℕ):ℝ) ≤ (q:ℝ) by exact_mod_cast hM]
      · rw [activeCubicWeight,ite_eq_right hm]
        have hratio : (M:ℝ)/t ≤ 1 := (div_le_one (by exact_mod_cast ht)).mpr
          (by exact_mod_cast (le_of_not_ge hm))
        linarith only [hratio,Nat.cast_nonneg (α := ℝ) q]
    · have hz : cubicSampleEnd n/t = 0 := he.symm.trans (Nat.div_eq_of_lt (lt_of_not_ge h))
      have hs : cubicSampleStart n ≤ n^4 := Nat.sub_le _ _
      have heq : cubicSampleStart n/t = cubicSampleEnd n/t :=
        (Nat.div_eq_of_lt (hs.trans_lt (lt_of_not_ge h))).trans hz.symm
      exact (cubicMean_activeWeight_eq hn ht heq).le

/-- At every sufficiently late retained crossing, the sign of the weight
correction is determined by the side of the centre containing its multiple. -/
theorem roughRangeCrossings_weight_sign :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ roughRangeCrossings n, ∀ j : ℕ,
      cubicSampleStart n < j*t → j*t ≤ cubicSampleEnd n →
        (n^4 < j*t → activeCubicWeight (n^4) t ≤ cubicMean n (fun M => activeCubicWeight M t)) ∧
        (j*t ≤ n^4 → cubicMean n (fun M => activeCubicWeight M t) ≤ activeCubicWeight (n^4) t) := by
  obtain ⟨N,hN⟩ := roughRangeCrossings_unique
  refine ⟨max 8 N,fun n hn t ht j ha hb => ?_⟩
  obtain ⟨u,_,hu⟩ := hN n (by omega) t ht
  have ht0 := (Nat.zero_le _).trans_lt (mem_Ioc.mp (mem_filter.mp ht).1).1
  have hq := (mem_filter.mp ht).2
  have hj := hu j ⟨ha,hb⟩
  have hs1 := hu (cubicSampleStart n/t+1) ⟨(Nat.div_lt_iff_lt_mul ht0).mp (by omega),
    (Nat.le_div_iff_mul_le ht0).mp hq⟩
  have he1 := hu (cubicSampleEnd n/t) ⟨(Nat.div_lt_iff_lt_mul ht0).mp hq,Nat.div_mul_le_self _ _⟩
  have hlow := Nat.div_le_div_right (c := t) (show cubicSampleStart n ≤ n^4 from Nat.sub_le _ _)
  have hhigh := Nat.div_le_div_right (c := t) (show n^4 ≤ cubicSampleEnd n from Nat.le_add_right _ _)
  have hsign := cubicMean_activeWeight_sides (by omega : 8 ≤ n) ht0
  constructor
  · intro hc
    have := (Nat.div_lt_iff_lt_mul ht0).mpr hc
    apply hsign.1
    omega
  · intro hc
    have := (Nat.le_div_iff_mul_le ht0).mpr hc
    apply hsign.2
    omega

private theorem cubicWeightedResponse_expand {n : ℕ} (hn : 8 ≤ n) (c : ℕ → ℝ) :
    cubicWeightedResponse n c = (∑ t ∈ Icc 0 (3*n^3), c t)/2 +
      ∑ t ∈ Ioc (3*n^3) (cubicSampleEnd n), c t*cubicMean n (fun M => activeCubicWeight M t) := by
  let U := Ioc (3*n^3) (cubicSampleEnd n)
  have hrow (M : ℕ) (_ : cubicSampleStart n ≤ M) (b : M ≤ cubicSampleEnd n) :
      (∑ t ∈ Ioc (3*n^3) M, c t*weight M t) = ∑ t ∈ U, c t*activeCubicWeight M t := by
    simp only [activeCubicWeight,mul_ite,mul_zero,← sum_filter]
    have h : U.filter (fun t => t ≤ M) = Ioc (3*n^3) M := by
      ext t
      simp only [U,mem_filter,mem_Ioc]
      omega
    rw [h]
  have hs : (fun M => ∑ t ∈ U, c t*activeCubicWeight M t) =
      ∑ t ∈ U, c t • fun M => activeCubicWeight M t := by
    ext M
    simp [Finset.sum_apply,smul_eq_mul]
  unfold cubicWeightedResponse
  rw [cubicMean_congr_on hn hrow,hs,map_sum]
  simp [U,smul_eq_mul]

/-- Evaluate all retained coefficients at the single sample n^4. -/
def roughRangeCentralResponse (n : ℕ) : ℝ :=
  (∑ t ∈ Icc 0 (3*n^3), roughRangeCoefficient n t)/2 +
    ∑ t ∈ Ioc (3*n^3) (n^4), roughRangeCoefficient n t*weight (n^4) t

/-- Signed change of the retained response on the quotient crossings. -/
def roughRangeCorrection (n : ℕ) : ℝ :=
  ∑ t ∈ roughRangeCrossings n, roughRangeCoefficient n t*
    (cubicMean n (fun M => activeCubicWeight M t) - activeCubicWeight (n^4) t)

theorem roughRangeCentral_add_correction {n : ℕ} (hn : 8 ≤ n) :
    roughRangeCentralResponse n + roughRangeCorrection n =
      cubicWeightedResponse n (roughRangeCoefficient n) := by
  let U := Ioc (3*n^3) (cubicSampleEnd n)
  have he : n^4 ≤ cubicSampleEnd n := Nat.le_add_right _ _
  have hsplit : U.filter (fun t => t ≤ n^4) = Ioc (3*n^3) (n^4) := by
    ext t
    simp only [U,mem_filter,mem_Ioc]
    omega
  have hcentral : (∑ t ∈ Ioc (3*n^3) (n^4), roughRangeCoefficient n t*weight (n^4) t) =
      ∑ t ∈ U, roughRangeCoefficient n t*activeCubicWeight (n^4) t := by
    simp only [activeCubicWeight,mul_ite,mul_zero,← sum_filter,hsplit]
  have hcross : roughRangeCrossings n = U.filter (fun t =>
      roughRangeStart n < t ∧ cubicSampleStart n/t < cubicSampleEnd n/t) := by
    ext t
    simp only [roughRangeCrossings,U,mem_filter,mem_Ioc,max_lt_iff]
    tauto
  rw [roughRangeCentralResponse,hcentral,roughRangeCorrection,hcross,sum_filter,add_assoc,
    ← sum_add_distrib,cubicWeightedResponse_expand hn]
  congr 1
  apply sum_congr rfl
  intro t hmem
  have ht : 0 < t := (Nat.zero_le _).trans_lt (mem_Ioc.mp hmem).1
  by_cases hp : roughRangeStart n < t
  · by_cases hq : cubicSampleStart n/t < cubicSampleEnd n/t
    · rw [ite_eq_left ⟨hp,hq⟩]
      ring
    · have heq := le_antisymm (Nat.div_le_div_right ((Nat.sub_le _ _).trans he :
          cubicSampleStart n ≤ cubicSampleEnd n)) (le_of_not_gt hq)
      simp [hq,cubicMean_activeWeight_eq hn ht heq]
  · simp [roughRangeCoefficient_prefix (mem_Ioc.mpr ⟨ht,le_of_not_gt hp⟩)]

/-- The same exceptional mass expressed through central weights and the signed crossing correction. -/
def roughRangeMassOn (C : ℝ) (m b : ℕ) : ℝ := ∑ n ∈ Icc m b, max
  (cubicSmoothMoments n - roughRangeCentralResponse n - roughRangeCorrection n -
    crossingTripleMass n - cubicWeightedResponse n (roughRangeDebitCoefficient n) -
    C*(n:ℝ)^2*(1+log n)^2) 0 / (n:ℝ)^3

theorem roughRangeMassOn_eq {m b : ℕ} (hm : 64 ≤ m) (C : ℝ) :
    roughRangeMassOn C m b = cubicExceptionalMassOn C m b := by
  apply sum_congr rfl
  intro n hn
  have h64 := hm.trans (mem_Icc.mp hn).1
  have h8 : 8 ≤ n := by omega
  rw [sub_sub _ (roughRangeCentralResponse n),roughRangeCentral_add_correction h8,
    sub_sub _ (cubicWeightedResponse n (roughRangeCoefficient n)),
    sub_sub _ (_ + crossingTripleMass n),roughRangeResponse_eq h64,
    sub_sub _ (cubicWeightedResponse n (cubicCompensatedCoefficient n)),cubicCompensatedResponse_eq h8]

theorem rh_of_roughRangeMassOn_powerWindows {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, roughRangeMassOn C m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply rh_of_cubicExceptionalMassOn_powerWindows hC
  intro α hα
  obtain ⟨δ,hδ,hδ1,hw⟩ := h α hα
  refine ⟨δ,hδ,hδ1,fun A => ?_⟩
  obtain ⟨m,hm,he⟩ := hw (max 64 A)
  exact ⟨m,by omega,(roughRangeMassOn_eq (by omega : 64 ≤ m) C).ge.trans he⟩

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.cubicThreeFactor_prefix_abs,
      ``RiemannGaussian.AlpogeMined.roughRangeResponse_eq,
      ``RiemannGaussian.AlpogeMined.roughRangeResponse_quartic_margin,
      ``RiemannGaussian.AlpogeMined.roughRangeCoefficient_prefix,
      ``RiemannGaussian.AlpogeMined.roughRangeCoefficient_semiprime,
      ``RiemannGaussian.AlpogeMined.roughRangeCoefficient_threePrimes,
      ``RiemannGaussian.AlpogeMined.roughRangeStart_covers_power,
      ``RiemannGaussian.AlpogeMined.roughRangeCrossings_quotient,
      ``RiemannGaussian.AlpogeMined.roughRangeCrossings_card,
      ``RiemannGaussian.AlpogeMined.roughRangeCrossings_unique,
      ``RiemannGaussian.AlpogeMined.cubicMean_activeWeight_eq,
      ``RiemannGaussian.AlpogeMined.roughRangeCrossings_weight_sign,
      ``RiemannGaussian.AlpogeMined.roughRangeCentral_add_correction,
      ``RiemannGaussian.AlpogeMined.roughRangeMassOn_eq,
      ``RiemannGaussian.AlpogeMined.rh_of_roughRangeMassOn_powerWindows] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
