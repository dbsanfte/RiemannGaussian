import CheckAlpogeCubicProducts

/-! # Rough factors and the proper prime-power correction in the cubic window -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real MeasureTheory ZetaVaughanReduction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt ArithmeticFunction.zeta

/-- The sum of the Möbius weights on divisors through the cutoff. -/
def truncatedMoebiusSum (n : ℕ) : ArithmeticFunction ℝ := head n μ * ζ

theorem truncatedMoebiusSum_apply (n t : ℕ) :
    truncatedMoebiusSum n t = ∑ d ∈ t.divisors.filter (· ≤ n), (μ d:ℝ) := by
  rw [truncatedMoebiusSum, ArithmeticFunction.coe_mul_zeta_apply, sum_filter]
  rfl

private theorem small_divisors_mul_rough {s r n : ℕ} (hs : 0 < s) (hr : 0 < r)
    (hrough : r.Coprime n.factorial) :
    (s*r).divisors.filter (· ≤ n) = s.divisors.filter (· ≤ n) := by
  ext d
  simp only [mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd,_⟩,hdn⟩
    have hd0 := Nat.pos_of_dvd_of_pos hd (Nat.mul_pos hs hr)
    have hc := Nat.Coprime.of_dvd_left (Nat.dvd_factorial hd0 hdn) hrough.symm
    exact ⟨⟨hc.dvd_of_dvd_mul_right hd,hs.ne'⟩,hdn⟩
  · rintro ⟨⟨hd,_⟩,hdn⟩
    exact ⟨⟨hd.trans (dvd_mul_right s r),(Nat.mul_pos hs hr).ne'⟩,hdn⟩

theorem truncatedMoebiusSum_mul_rough {s r n : ℕ} (hs : 0 < s) (hr : 0 < r)
    (hrough : r.Coprime n.factorial) : truncatedMoebiusSum n (s*r) = truncatedMoebiusSum n s := by
  rw [truncatedMoebiusSum_apply,truncatedMoebiusSum_apply,small_divisors_mul_rough hs hr hrough]

/-- The logarithmic contribution from primes strictly above n, with multiplicity. -/
def roughPrimeLog (n p : ℕ) : ℝ :=
  ∑ v ∈ p.divisors, if v.Coprime n.factorial then Λ v else 0

/-- Residual divisors exceeding n that share a prime with n factorial.
Only proper prime powers have nonzero von Mangoldt weight here. -/
def largePrimePowerCorrection (n p : ℕ) : ℝ :=
  ∑ v ∈ p.divisors, if n<v ∧ ¬v.Coprime n.factorial then Λ v * truncatedMoebiusSum n (p/v) else 0

/-- Above the cutoff, the exceptional divisors of nonzero weight are exactly
the powers with exponent at least two and base prime at most the cutoff. -/
theorem exceptional_power_iff {n v : ℕ} (hnv : n < v) :
    (¬v.Coprime n.factorial ∧ Λ v ≠ 0) ↔
      ∃ q k : ℕ, q.Prime ∧ q ≤ n ∧ 2 ≤ k ∧ q^k = v := by
  constructor
  · rintro ⟨hc, hw⟩
    obtain ⟨q,k,hq,hk,rfl⟩ := (isPrimePow_nat_iff v).mp
      (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hw)
    have hqn : q ≤ n := by
      by_contra! h
      exact hc (Nat.Coprime.pow_left k (hq.coprime_iff_not_dvd.mpr
        (fun hd => (not_le_of_gt h) (hq.dvd_factorial.mp hd))))
    refine ⟨q,k,hq,hqn,?_,rfl⟩
    by_contra! h
    rw [show k=1 by omega, pow_one] at hnv
    omega
  · rintro ⟨q,k,hq,hqn,hk,rfl⟩
    refine ⟨fun hc => ?_, ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr
      ((isPrimePow_nat_iff _).mpr ⟨q,k,hq,by omega,rfl⟩)⟩
    have h := hc.of_dvd_left (dvd_pow_self q (by omega : k ≠ 0))
    exact hq.coprime_iff_not_dvd.mp h (hq.dvd_factorial.mpr hqn)

private theorem small_rough_mangoldt_zero {n v : ℕ} (hv : v ≤ n) (hv0 : 0 < v)
    (hcop : v.Coprime n.factorial) : Λ v = 0 := by
  have he := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (Nat.dvd_factorial hv0 hv)
  simp [he]

/-- Separating large prime powers by their underlying prime evaluates the
rough contribution using one truncated divisor sum for the tested integer. -/
theorem bilinear_eq_roughLog (n p : ℕ) : bilinear n n p =
    (Λ p-head n Λ p) - truncatedMoebiusSum n p * roughPrimeLog n p -
      largePrimePowerCorrection n p := by
  let L := Λ-head n Λ
  have h : bilinear n n = L - L * truncatedMoebiusSum n := by
    unfold bilinear cofactor truncatedMoebiusSum
    change ((μ : ArithmeticFunction ℝ)-head n μ)*(L*ζ) = _
    rw [sub_mul, show (μ : ArithmeticFunction ℝ)*(L*ζ) = (μ*ζ:ArithmeticFunction ℝ)*L by ring,
      ArithmeticFunction.coe_moebius_mul_coe_zeta, one_mul]
    ring
  rw [h]
  change L p - (L*truncatedMoebiusSum n) p = _
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun v t => L v * truncatedMoebiusSum n t), roughPrimeLog, largePrimePowerCorrection]
  rw [sub_sub, mul_sum, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro v hv
  obtain ⟨hvp,hp0⟩ := Nat.mem_divisors.mp hv
  have hv0 := Nat.pos_of_dvd_of_pos hvp (Nat.pos_of_ne_zero hp0)
  change (Λ v-head n Λ v) * _ = _
  by_cases hcop : v.Coprime n.factorial
  · have hq := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hp0) hvp) hv0
    have he := truncatedMoebiusSum_mul_rough hq hv0 hcop
    rw [Nat.div_mul_cancel hvp] at he
    by_cases hsmall : v ≤ n
    · simp [head,hsmall,hcop,small_rough_mangoldt_zero hsmall hv0 hcop]
    · simp [head,hsmall,hcop,he,mul_comm]
  · by_cases hsmall : v ≤ n
    · simp [head,hsmall,hcop,not_lt.mpr hsmall]
    · simp [head,hsmall,hcop,lt_of_not_ge hsmall]

private theorem cofactor_mul_rough {n s r : ℕ} (hs : 0 < s) (hr : 0 < r)
    (hc : r.Coprime n.factorial) : cofactor n (s*r) = cofactor n s + log r := by
  have he (t : ℕ) : cofactor n t = log t - ∑ d ∈ t.divisors.filter (· ≤ n), Λ d := by
    rw [cofactor_eq, ← ArithmeticFunction.vonMangoldt_sum, sum_filter, ← sum_sub_distrib]
    apply sum_congr rfl
    intro d _
    by_cases h : d ≤ n <;> simp [h, not_lt.mpr, lt_of_not_ge]
  rw [he,he,small_divisors_mul_rough hs hr hc, Nat.cast_mul,
    log_mul (Nat.cast_ne_zero.mpr hs.ne') (Nat.cast_ne_zero.mpr hr.ne')]
  ring

/-- Multiplication by a rough cofactor contributes a single logarithm at a
fixed slope, for every positive base including bases larger than the cutoff. -/
theorem bilinear_mul_rough {n s r : ℕ} (hs : 0 < s) (hr : 0 < r)
    (hc : r.Coprime n.factorial) :
    bilinear n n (s*r) = bilinear n n s + (Λ (s*r)-head n Λ (s*r)) -
      (Λ s-head n Λ s) - truncatedMoebiusSum n s * log r := by
  have he (t : ℕ) : bilinear n n t = (Λ t-head n Λ t) -
      ∑ d ∈ t.divisors.filter (· ≤ n), (μ d:ℝ)*cofactor n (t/d) := by
    let L := Λ-head n Λ
    have hh : bilinear n n = L - head n μ * cofactor n := by
      rw [bilinear,sub_mul, show (μ:ArithmeticFunction ℝ)*cofactor n = L by
        unfold cofactor
        change _*(L*ζ)=_
        rw [show (μ:ArithmeticFunction ℝ)*(L*ζ)=(μ*ζ:ArithmeticFunction ℝ)*L by ring,
          ArithmeticFunction.coe_moebius_mul_coe_zeta,one_mul]]
    rw [hh]
    change _ - (head n (μ:ArithmeticFunction ℝ)*cofactor n) t = _
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (fun d q => head n (μ:ArithmeticFunction ℝ) d * cofactor n q), sum_filter]
    congr 1
    apply sum_congr rfl
    intro d _
    by_cases hd : d ≤ n <;> simp [head,hd]
  rw [he, he, small_divisors_mul_rough hs hr hc, truncatedMoebiusSum_apply, sum_mul]
  have hx : (∑ d ∈ s.divisors.filter (· ≤ n), (μ d:ℝ)*cofactor n (s*r/d)) =
      (∑ d ∈ s.divisors.filter (· ≤ n), (μ d:ℝ)*cofactor n (s/d)) +
        ∑ d ∈ s.divisors.filter (· ≤ n), (μ d:ℝ)*log r := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro d hd
    have hdv := Nat.dvd_of_mem_divisors (mem_filter.mp hd).1
    have hd0 := Nat.pos_of_dvd_of_pos hdv hs
    rw [Nat.mul_comm s r, Nat.mul_div_assoc r hdv, Nat.mul_comm r,
      cofactor_mul_rough (Nat.div_pos (Nat.le_of_dvd hs hdv) hd0) hr hc, mul_add]
  rw [hx]
  ring

/-- For base integers between the cutoff and its first possible pair product,
the whole rough progression is determined by its truncated Möbius sum. -/
theorem bilinear_mul_rough_below_pair {n s r : ℕ} (hs : n < s)
    (hpair : s < (n+1)^2) (hr : 0 < r) (hc : r.Coprime n.factorial) :
    bilinear n n (s*r) = Λ (s*r) - Λ s - truncatedMoebiusSum n s * log r := by
  have hsr := hs.trans_le (Nat.le_mul_of_pos_right s hr)
  rw [bilinear_mul_rough ((Nat.zero_le _).trans_lt hs) hr hc]
  have he : bilinear n n = vaughanPair n * ζ := by
    simp only [bilinear, cofactor, vaughanPair, mul_assoc]
  have hz : bilinear n n s = 0 := by
    rw [he,ArithmeticFunction.coe_mul_zeta_apply]
    exact sum_eq_zero fun e he => vaughanPair_eq_zero
      ((Nat.le_of_dvd ((Nat.zero_le _).trans_lt hs) (Nat.dvd_of_mem_divisors he)).trans_lt hpair)
  simp [hz,head,not_le.mpr hs,not_le.mpr hsr]

/-- In the first dyadic band every proper divisor is below the cutoff.
The slope on a rough progression is therefore just the full Möbius weight. -/
theorem bilinear_mul_rough_first_band {n s r : ℕ} (hs : n < s)
    (hs2 : s ≤ 2*n) (hr : 0 < r) (hc : r.Coprime n.factorial) :
    bilinear n n (s*r) = Λ (s*r) - Λ s + (μ s:ℝ)*log r := by
  have hs1 : 1 < s := by omega
  have hset : s.divisors.filter (· ≤ n) = s.divisors.erase s := by
    ext d
    simp only [mem_filter,mem_erase]
    constructor
    · exact fun h => ⟨by omega,h.1⟩
    · rintro ⟨hne,hd⟩
      have hproper := Nat.mem_properDivisors.mpr ⟨Nat.dvd_of_mem_divisors hd,
        lt_of_le_of_ne (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)) hne⟩
      obtain ⟨k,hk,he⟩ := (Nat.mem_properDivisors_iff_exists (by omega : s ≠ 0)).mp hproper
      have h2 := Nat.mul_le_mul_left d (show 2 ≤ k from hk)
      exact ⟨hd,by nlinarith only [he,h2,hs2]⟩
  have hsum := congrArg (fun f : ArithmeticFunction ℝ => f s)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  rw [ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.one_apply_ne (by omega)] at hsum
  have hz : ∑ d ∈ s.divisors, (μ d:ℝ) = 0 := hsum
  have htotal := sum_erase_add s.divisors (fun d => (μ d:ℝ)) (Nat.mem_divisors.mpr
    (show s ∣ s ∧ s ≠ 0 from ⟨dvd_rfl,by omega⟩))
  rw [hz] at htotal
  rw [bilinear_mul_rough_below_pair hs (by nlinarith only [hs2]) hr hc,
    truncatedMoebiusSum_apply,hset,eq_neg_of_add_eq_zero_left htotal]
  ring

private theorem divisor_rows (a g : ℕ → ℝ) (hg : g 0 = 0) (X : ℕ) :
    ∑ t ∈ Icc 0 X, ∑ d ∈ t.divisors, a d*g (t/d) =
      ∑ d ∈ Ioc 0 X, a d * ∑ k ∈ Icc 0 (X/d), g k := by
  have h (t : ℕ) (ht : t ∈ Icc 0 X) :
      ∑ d ∈ t.divisors, a d*g (t/d) =
        ∑ d ∈ Ioc 0 X, if d ∣ t then a d*g (t/d) else 0 := by
    by_cases ht0 : t=0
    · simp [ht0,hg]
    rw [← sum_filter]
    congr 1
    ext d
    simp only [Nat.mem_divisors,mem_filter,mem_Ioc]
    exact ⟨fun hh => ⟨⟨Nat.pos_of_dvd_of_pos hh.1 (Nat.pos_of_ne_zero ht0),
      (Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) hh.1).trans (mem_Icc.mp ht).2⟩,hh.1⟩,
      fun hh => ⟨hh.2,ht0⟩⟩
  rw [sum_congr rfl h,sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [← sum_filter, ← sum_stride g X (mem_Ioc.mp hd).1, mul_sum]

private theorem truncatedMoebiusSum_prefix_abs (n X : ℕ) :
    ∑ t ∈ Icc 0 X, |truncatedMoebiusSum n t| ≤ (X:ℝ)*(1+log n) := by
  let a (d : ℕ) : ℝ := if d≤n then 1 else 0
  let g (k : ℕ) : ℝ := if k=0 then 0 else 1
  calc
    _ ≤ ∑ t ∈ Icc 0 X, ∑ d ∈ t.divisors, a d*g (t/d) := by
      apply sum_le_sum
      intro t _
      rw [truncatedMoebiusSum_apply,sum_filter]
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro d hd
      obtain ⟨hdv,ht⟩ := Nat.mem_divisors.mp hd
      have hq := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ht) hdv)
        (Nat.pos_of_dvd_of_pos hdv (Nat.pos_of_ne_zero ht))
      by_cases hn : d≤n
      · simpa [a,g,hn,hq.ne'] using (show |(μ d:ℝ)| ≤ 1 by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one)
      · simp [a,g,hn]
    _ = ∑ d ∈ (Ioc 0 X).filter (· ≤ n), ((X/d:ℕ):ℝ) := by
      rw [divisor_rows a g (by simp [g]),sum_filter]
      apply sum_congr rfl
      intro d _
      simp only [a,ite_mul,one_mul,zero_mul]
      congr 1
      rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le (X/d))]
      simp only [g,ite_true,zero_add]
      rw [sum_congr rfl (g := fun _ => (1:ℝ)) (fun k hk => ite_eq_right (mem_Ioc.mp hk).1.ne')]
      simp
    _ ≤ ∑ d ∈ Icc 1 n, (X:ℝ)*(d:ℝ)⁻¹ := by
      apply (sum_le_sum (g := fun d : ℕ => (X:ℝ)*(d:ℝ)⁻¹) ?_).trans
      · exact sum_le_sum_of_subset_of_nonneg (fun d hd =>
          mem_Icc.mpr ⟨(mem_Ioc.mp (mem_filter.mp hd).1).1,(mem_filter.mp hd).2⟩)
          (fun _ _ _ => by positivity)
      · intro d _
        simpa only [← div_eq_mul_inv] using (Nat.cast_div_le (m := X) (n := d) (α := ℝ))
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (primeWindow_harmonic_le (by decide : 1 ≤ 1))
        (Nat.cast_nonneg _)

/-- The total logarithmic weight of prime powers through X with base at most
n is at most n log X, counting every exponent. -/
theorem small_base_prime_power_mass (n X : ℕ) (hX : 0 < X) :
    ∑ v ∈ (Ioc 0 X).filter (fun v => ¬v.Coprime n.factorial), Λ v ≤ (n:ℝ)*log X := by
  let A := ∏ q ∈ Ioc 0 n, q^(Nat.log q X)
  have hA : 0 < A := prod_pos fun q hq => pow_pos (mem_Ioc.mp hq).1 _
  let S := ((Ioc 0 X).filter (fun v => ¬v.Coprime n.factorial)).filter IsPrimePow
  have he : (∑ v ∈ S, Λ v) = ∑ v ∈ (Ioc 0 X).filter (fun v => ¬v.Coprime n.factorial), Λ v := by
    unfold S
    rw [sum_filter]
    apply sum_congr rfl
    intro v _
    by_cases hv : IsPrimePow v <;> simp [hv, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr]
  rw [← he]
  have hsub : S ⊆ A.divisors := by
    intro v hv
    obtain ⟨hm,hpow⟩ := mem_filter.mp hv
    obtain ⟨hvX,hcop⟩ := mem_filter.mp hm
    obtain ⟨q,k,hq,_,rfl⟩ := (isPrimePow_nat_iff v).mp hpow
    have hqn : q ≤ n := by
      by_contra! h
      exact hcop (Nat.Coprime.pow_left k (hq.coprime_iff_not_dvd.mpr
        (fun hh => (not_le_of_gt h) (hq.dvd_factorial.mp hh))))
    have hk := Nat.le_log_of_pow_le hq.one_lt (mem_Ioc.mp hvX).2
    exact Nat.mem_divisors.mpr ⟨(pow_dvd_pow q hk).trans
      (dvd_prod_of_mem _ (mem_Ioc.mpr ⟨hq.pos,hqn⟩)),hA.ne'⟩
  apply (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)).trans
  rw [ArithmeticFunction.vonMangoldt_sum]
  dsimp only [A]
  push_cast
  rw [Real.log_prod (fun q hq => pow_ne_zero _ (Nat.cast_ne_zero.mpr (mem_Ioc.mp hq).1.ne'))]
  calc
    _ ≤ ∑ _q ∈ Ioc 0 n, log (X:ℝ) := by
      apply sum_le_sum
      intro q hq
      apply log_le_log (pow_pos (Nat.cast_pos.mpr (mem_Ioc.mp hq).1) _)
      exact_mod_cast Nat.pow_log_le_self q hX.ne'
    _ = _ := by simp

/-- Part of the proper prime-power correction beyond a chosen divisor threshold. -/
def deepPowerCorrection (n Y p : ℕ) : ℝ :=
  ∑ v ∈ p.divisors, if Y<v ∧ ¬v.Coprime n.factorial then Λ v*truncatedMoebiusSum n (p/v) else 0

/-- The absolute prefix of the discarded large powers has a factor n/Y
in addition to the linear observation scale. -/
theorem deepPowerCorrection_prefix_abs {X Y : ℕ} (n : ℕ) (hX : 0 < X) (hY : 0 < Y) :
    ∑ p ∈ Icc 0 X, |deepPowerCorrection n Y p| ≤
      (X:ℝ)*(1+log n)/Y * ((n:ℝ)*log X) := by
  let a (v : ℕ) : ℝ := if Y<v ∧ ¬v.Coprime n.factorial then Λ v else 0
  let g (t : ℕ) : ℝ := |truncatedMoebiusSum n t|
  have hg : g 0=0 := by simp [g]
  calc
    _ ≤ ∑ p ∈ Icc 0 X, ∑ v ∈ p.divisors, a v*g (p/v) := by
      apply sum_le_sum
      intro p _
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro v _
      by_cases hh : Y<v ∧ ¬v.Coprime n.factorial <;>
        simp [a,g,hh, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    _ = ∑ v ∈ Ioc 0 X, a v * ∑ t ∈ Icc 0 (X/v), g t := divisor_rows a g hg X
    _ ≤ ∑ v ∈ (Ioc 0 X).filter (fun v => ¬v.Coprime n.factorial),
        ((X:ℝ)*(1+log n)/Y)*Λ v := by
      rw [sum_filter]
      apply sum_le_sum
      intro v _
      by_cases hcop : v.Coprime n.factorial
      · simp [a,hcop]
      by_cases hv : Y<v
      · simp only [a,hv,hcop,not_false_eq_true,and_self,ite_true]
        rw [mul_comm _ (Λ v)]
        apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
        have hdiv : ((X/v:ℕ):ℝ) ≤ (X:ℝ)/Y := Nat.cast_div_le.trans
          (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (Nat.cast_pos.mpr hY) (by exact_mod_cast hv.le))
        exact (truncatedMoebiusSum_prefix_abs n (X/v)).trans
          ((mul_le_mul_of_nonneg_right hdiv (by positivity [log_natCast_nonneg n])).trans_eq (by ring))
      · simp [a,hv,hcop]
        positivity [log_natCast_nonneg n, (ArithmeticFunction.vonMangoldt_nonneg (n := v))]
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (small_base_prime_power_mass n X hX) (by positivity [log_natCast_nonneg n])

/-- Only the exceptional small-base powers between n and its cube are retained. -/
def cubicRoughCoefficient (n p : ℕ) : ℝ :=
  (Λ p-head n Λ p) - truncatedMoebiusSum n p * roughPrimeLog n p -
    ∑ v ∈ p.divisors, if n<v ∧ v≤n^3 ∧ ¬v.Coprime n.factorial
      then Λ v*truncatedMoebiusSum n (p/v) else 0

private theorem cubicRoughCoefficient_sub (n p : ℕ) :
    cubicRoughCoefficient n p - bilinear n n p = deepPowerCorrection n (n^3) p := by
  rw [bilinear_eq_roughLog, cubicRoughCoefficient]
  unfold largePrimePowerCorrection deepPowerCorrection
  rw [show ∀ a b c : ℝ, (a-b)-(a-c)=c-b by intros; ring, ← sum_sub_distrib]
  apply sum_congr rfl
  intro v _
  have hnn : n ≤ n^3 := Nat.le_self_pow (by decide) _
  by_cases hc : v.Coprime n.factorial
  · simp [hc]
  by_cases hv : n^3 < v
  · simp [hc,hv,hnn.trans_lt hv,not_le.mpr hv]
  · simp [hc,hv,Nat.le_of_not_gt hv]

/-- When the base fits under the power cutoff, every exceptional divisor
comes from the base itself, even if the rough cofactor is arbitrarily large. -/
theorem cubicRoughCoefficient_eq_on_rough_progression {n s r : ℕ}
    (hs : 0 < s) (hs3 : s ≤ n^3) (hc : r.Coprime n.factorial) :
    cubicRoughCoefficient n (s*r) = bilinear n n (s*r) := by
  apply sub_eq_zero.mp
  rw [cubicRoughCoefficient_sub,deepPowerCorrection]
  apply sum_eq_zero
  intro v hv
  by_cases h : n^3 < v ∧ ¬v.Coprime n.factorial
  · rw [ite_eq_left h]
    suffices hz : Λ v = 0 by rw [hz,zero_mul]
    by_contra hw
    have hnv := (Nat.le_self_pow (by decide : 3 ≠ 0) n).trans_lt h.1
    obtain ⟨q,k,hq,hqn,_,rfl⟩ := (exceptional_power_iff hnv).mp ⟨h.2,hw⟩
    have hqr := Nat.Coprime.of_dvd_left (hq.dvd_factorial.mpr hqn) hc.symm
    have hd := (hqr.pow_left k).dvd_of_dvd_mul_right (Nat.dvd_of_mem_divisors hv)
    exact (not_le.mpr h.1) ((Nat.le_of_dvd hs hd).trans hs3)
  · rw [ite_eq_right h]

/-- Largest integer sampled by the repeated mean around the fourth power. -/
def cubicSampleEnd (n : ℕ) := n^4+(Nat.log 2 n+1)*n^3

theorem cubicSampleEnd_le {n : ℕ} (hn : 8 ≤ n) : cubicSampleEnd n ≤ 2*n^4 := by
  have hk := (cubic_tail_parameters hn).1
  have h := Nat.mul_le_mul_right (n^3) (show Nat.log 2 n+1 ≤ n by omega)
  unfold cubicSampleEnd
  grind only [show n^4 = n*n^3 by ring]

private theorem cubicMean_abs_of_bound {n : ℕ} (hn : 8 ≤ n) (f : ℕ → ℝ) {B : ℝ}
    (hf : ∀ M ≤ cubicSampleEnd n, |f M| ≤ B) : |cubicMean n f| ≤ B := by
  let k := Nat.log 2 n+1
  let D := n^3
  let W := 2*D+1
  let A := n^4-k*D
  have hk : 2*k ≤ n := (cubic_tail_parameters hn).1
  have hhalf : 2*(k*D) ≤ n^4 := by
    simpa only [D,← Nat.mul_assoc,show n^4=n*n^3 by ring] using Nat.mul_le_mul_right D hk
  have hw : 0 < W := by dsimp [W]; omega
  have hmax : A+k*(W-1) ≤ cubicSampleEnd n := by
    change n^4-k*D+k*(2*D) ≤ n^4+k*D
    rw [show k*(2*D)=2*(k*D) by ring]
    omega
  have hu := repeat_mono W k A (f := f) (g := fun _ => B)
    (fun M _ hM => (abs_le.mp (hf M (hM.trans hmax))).2)
  have hl := repeat_mono W k A (f := fun _ => -B) (g := f)
    (fun M _ hM => (abs_le.mp (hf M (hM.trans hmax))).1)
  change |repeatedMean W k f A| ≤ B
  exact abs_le.mpr ⟨by simpa only [repeat_const hw k A] using hl,
    by simpa only [repeat_const hw k A] using hu⟩

theorem cubicWeightedResponse_sub (n : ℕ) (c g : ℕ → ℝ) :
    cubicWeightedResponse n c - cubicWeightedResponse n g = cubicWeightedResponse n (c-g) := by
  have hx : (fun M => ∑ p ∈ Ioc (3*n^3) M, (c-g) p*weight M p) =
      (fun M : ℕ => ∑ p ∈ Ioc (3*n^3) M, c p*weight M p) -
        (fun M : ℕ => ∑ p ∈ Ioc (3*n^3) M, g p*weight M p) := by
    funext M
    simp only [Pi.sub_apply,sub_mul,sum_sub_distrib]
  unfold cubicWeightedResponse
  rw [hx, map_sub]
  simp only [Pi.sub_apply,sum_sub_distrib]
  ring

/-- An absolute coefficient prefix controls the combined half-weight and moving tail. -/
theorem cubicWeightedResponse_abs {n : ℕ} (hn : 8 ≤ n) (c : ℕ → ℝ) :
    |cubicWeightedResponse n c| ≤ 2*∑ p ∈ Icc 0 (cubicSampleEnd n), |c p| := by
  let P := ∑ p ∈ Icc 0 (cubicSampleEnd n), |c p|
  have hP : 0 ≤ P := sum_nonneg fun _ _ => abs_nonneg _
  have hR : 3*n^3 ≤ cubicSampleEnd n := by
    exact (Nat.mul_le_mul_right (n^3) (by omega : 3 ≤ n)).trans
      (by unfold cubicSampleEnd; rw [show n^4=n*n^3 by ring]; omega)
  have hl : |∑ p ∈ Icc 0 (3*n^3), c p| ≤ P :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum_of_subset_of_nonneg
      (Icc_subset_Icc_right hR) (fun _ _ _ => abs_nonneg _))
  have hu : |cubicMean n (fun M => ∑ p ∈ Ioc (3*n^3) M, c p*weight M p)| ≤ P := by
    apply cubicMean_abs_of_bound hn
    intro M hM
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ p ∈ Ioc (3*n^3) M, |c p| := by
        apply sum_le_sum
        intro p hp
        have hw := weight_mem (N := M) ((Nat.zero_le _).trans_lt (mem_Ioc.mp hp).1)
        rw [abs_mul,abs_of_nonneg hw.1]
        exact mul_le_of_le_one_right (abs_nonneg _) hw.2
      _ ≤ P := sum_le_sum_of_subset_of_nonneg
        (fun p hp => mem_Icc.mpr ⟨Nat.zero_le _,(mem_Ioc.mp hp).2.trans hM⟩)
        (fun _ _ _ => abs_nonneg _)
  apply (abs_add_le _ _).trans
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  change _ ≤ 2*P
  linarith only [hu,hl,hP]

/-- Removing all exceptional powers beyond n cubed costs square-root scale
times a squared logarithm at a single fourth-power sample. -/
theorem cubicRoughCoefficient_response_error {n : ℕ} (hn : 8 ≤ n) :
    |cubicWeightedResponse n (cubicRoughCoefficient n)-cubicProductResponse n| ≤
      16*(n:ℝ)^2*(1+log n)^2 := by
  unfold cubicProductResponse
  rw [cubicWeightedResponse_sub,show (cubicRoughCoefficient n-⇑(bilinear n n)) =
    deepPowerCorrection n (n^3) by funext p; exact cubicRoughCoefficient_sub n p]
  apply (cubicWeightedResponse_abs hn _).trans
  apply (mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg
    (Icc_subset_Icc_right (cubicSampleEnd_le hn)) (fun _ _ _ => abs_nonneg _)) (by norm_num)).trans
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hX : 0 < 2*n^4 := by positivity
  have h := deepPowerCorrection_prefix_abs n hX (show 0<n^3 by positivity)
  push_cast at h
  have he : (2*(n:ℝ)^4*(1+log n)/(n:ℝ)^3)*((n:ℝ)*log (2*(n:ℝ)^4)) =
      2*(n:ℝ)^2*(1+log n)*log (2*(n:ℝ)^4) := by field_simp
  rw [he] at h
  have hl : log (2*(n:ℝ)^4) ≤ 4*(1+log n) := by
    rw [log_mul (by norm_num) (pow_ne_zero _ hn0.ne'),log_pow,Nat.cast_ofNat]
    linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hh := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ 2*(n:ℝ)^2*(1+log n) by positivity [log_natCast_nonneg n])
  nlinarith only [h,hh]

/-- Remaining positive mass with the small-base prime powers cut off at n cubed. -/
def cubicRoughMassOn (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (cubicSmoothMoments n -
    cubicWeightedResponse n (cubicRoughCoefficient n)) 0 / (n:ℝ)^3

theorem cubicRoughMassOn_error {m b : ℕ} (hm : 8 ≤ m) :
    |cubicProductMassOn m b-cubicRoughMassOn m b| ≤ 16*(1+log b)^3 := by
  unfold cubicProductMassOn cubicRoughMassOn
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Icc m b, (16*(1+log b)^2)*(n:ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      have hn8 := hm.trans (mem_Icc.mp hn).1
      have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
      have h := abs_max_sub_max_le_abs (cubicProductResidual n)
        (cubicSmoothMoments n-cubicWeightedResponse n (cubicRoughCoefficient n)) 0
      rw [cubicProductResidual,show ∀ a b c : ℝ, (a-b)-(a-c)=c-b by intros; ring] at h
      rw [← sub_div,abs_div,abs_of_pos (pow_pos hn0 3)]
      apply (div_le_iff₀ (pow_pos hn0 3)).mpr
      rw [show 16*(1+log b)^2*(n:ℝ)⁻¹*(n:ℝ)^3=16*(n:ℝ)^2*(1+log b)^2 by field_simp]
      apply (h.trans (cubicRoughCoefficient_response_error hn8)).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_pow_left₀ (by positivity [log_natCast_nonneg n])
      exact add_le_add_right (log_le_log hn0 (by exact_mod_cast (mem_Icc.mp hn).2)) _
    _ ≤ _ := by
      rw [← mul_sum]
      exact (mul_le_mul_of_nonneg_left (primeWindow_harmonic_le (a := m) (b := b) (by omega))
        (by positivity : 0 ≤ 16*(1+log b)^2)).trans_eq (by ring)

/-- The cofinal signed comparison needs only the intermediate exceptional powers. -/
theorem rh_of_cubicRoughMassOn_powerWindows
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, cubicRoughMassOn m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply rh_of_cubicProductMassOn_powerWindows
  apply subpowerWindows_of_log_cube_error (K := 16) (by norm_num) _ h
  intro m b hm
  linarith only [(abs_le.mp (cubicRoughMassOn_error (b := b) hm)).2]

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.bilinear_mul_rough,
      ``RiemannGaussian.AlpogeMined.bilinear_mul_rough_first_band,
      ``RiemannGaussian.AlpogeMined.cubicRoughCoefficient_eq_on_rough_progression,
      ``RiemannGaussian.AlpogeMined.bilinear_eq_roughLog,
      ``RiemannGaussian.AlpogeMined.cubicRoughMassOn_error,
      ``RiemannGaussian.AlpogeMined.rh_of_cubicRoughMassOn_powerWindows] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
