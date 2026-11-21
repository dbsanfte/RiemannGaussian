import CheckAlpogeCubicSemiprimes
import PrimeNumberTheoremAnd.Wiener

/-! # Prime sums that compensate rough semiprime losses

The analytic input is the weak prime number theorem from the vendored
compatibility port of Kontorovich and collaborators' PrimeNumberTheoremAnd.
The positive response of odd crossing triples covers every upper semiprime
whose smaller factor is in a fixed power range above the cutoff.
-/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Filter Real
open scoped Classical Topology ArithmeticFunction.Omega

private def primeInterval (a b : ℕ) := (Ioc a b).filter Nat.Prime

private def primesInWindow (x A : ℝ) := primeInterval ⌊x⌋₊ ⌊A*x⌋₊

private theorem mem_primesInWindow_bounds {x A : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) {p : ℕ}
    (hp : p ∈ primesInWindow x A) : x < p ∧ (p:ℝ) ≤ A*x ∧ p.Prime := by
  obtain ⟨hi,hp⟩ := mem_filter.mp hp
  exact ⟨(Nat.floor_lt hx).mp (mem_Ioc.mp hi).1,
    (Nat.le_floor_iff (mul_nonneg hA hx)).mp (mem_Ioc.mp hi).2,hp⟩

/-- The numerator in the weak PNT ends just before its integer argument. -/
theorem cubicPsi_div_tendsto_one :
    Tendsto (fun x : ℝ => Chebyshev.psi x/x) atTop (𝓝 1) := by
  have hfloor : Tendsto (fun x : ℝ => ((⌊x⌋₊:ℝ)+1)/x) atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one (eventually_ne_atTop (0:ℝ))).mp
      (Asymptotics.isEquivalent_nat_floor.add_isLittleO (Asymptotics.isLittleO_const_id_atTop 1))
  have hsum := WeakPNT.comp ((tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_atTop (α := ℝ)))
  have h := hsum.mul hfloor
  rw [one_mul] at h
  apply h.congr'
  filter_upwards with x
  simp only [Function.comp_apply,cumsum,Nat.range_succ_eq_Icc_zero,Chebyshev.psi_eq_sum_Icc,
    Nat.cast_add,Nat.cast_one]
  field_simp

private theorem theta_div_tendsto_one :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  have hpsi := cubicPsi_div_tendsto_one
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hdiff : Tendsto (fun x : ℝ => (Chebyshev.psi x-Chebyshev.theta x)/x) atTop (𝓝 0) := by
    have hb : Tendsto (fun x : ℝ => C/sqrt x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_sqrt_atTop
    apply squeeze_zero' _ _ hb
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      exact div_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x)) hx.le
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      calc
        _ ≤ (C*sqrt x)/x := div_le_div_of_nonneg_right (hC x) hx.le
        _ = C/sqrt x := by rw [mul_div_assoc,sqrt_div_self,div_eq_mul_inv]
  simpa only [sub_zero, ← sub_div, sub_sub_cancel] using hpsi.sub hdiff

/-- The same PNT threshold works for every row started beyond it. -/
private theorem prime_log_lower {A c : ℝ} (hA : 1 ≤ A) (hc : c < A-1) :
    ∃ N : ℕ, ∀ x : ℝ, N ≤ x → c*x ≤ ∑ p ∈ primesInWindow x A, log p := by
  have hlim := ((theta_div_tendsto_one.comp
    (tendsto_id.const_mul_atTop (zero_lt_one.trans_le hA))).mul_const A).sub theta_div_tendsto_one
  simp only [one_mul] at hlim
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hlim.eventually (lt_mem_nhds hc))
  refine ⟨⌈max 1 T⌉₊,fun x hx => ?_⟩
  have h := (Nat.le_ceil (max 1 T)).trans hx
  have hx0 := zero_lt_one.trans_le ((le_max_left _ _).trans h)
  have hf : ⌊x⌋₊ ≤ ⌊A*x⌋₊ := Nat.floor_mono (le_mul_of_one_le_left hx0.le hA)
  have hi : Icc 0 ⌊x⌋₊ ⊆ Icc 0 ⌊A*x⌋₊ := Icc_subset_Icc_right hf
  have hd : (Icc 0 ⌊A*x⌋₊ \ Icc 0 ⌊x⌋₊ : Finset ℕ) = Ioc ⌊x⌋₊ ⌊A*x⌋₊ := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_sdiff,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  have he := sum_sdiff (f := fun p : ℕ => if p.Prime then log p else 0) hi
  rw [hd] at he
  have hlim' := (hT x ((le_max_right _ _).trans h)).le
  change c ≤ Chebyshev.theta (A*x)/(A*x)*A-Chebyshev.theta x/x at hlim'
  have hA0 := zero_lt_one.trans_le hA
  rw [show Chebyshev.theta (A*x)/(A*x)*A-Chebyshev.theta x/x =
    (Chebyshev.theta (A*x)-Chebyshev.theta x)/x by field_simp] at hlim'
  have hmass := (le_div_iff₀ hx0).mp hlim'
  simp only [Chebyshev.theta_eq_sum_Icc,sum_filter] at hmass
  simp only [primesInWindow,primeInterval,sum_filter]
  linarith only [he,hmass]

private theorem consecutive_prime_intervals (f : ℕ → ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ p ∈ primeInterval a b, f p)+(∑ p ∈ primeInterval b c, f p) =
      ∑ p ∈ primeInterval a c, f p := by
  unfold primeInterval
  simp only [sum_filter]
  exact sum_Ioc_consecutive _ hab hbc

private theorem dyadic_log_mass :
    ∃ N : ℕ, ∀ x ≥ N, (x:ℝ)/2 ≤ ∑ p ∈ primeInterval x (2*x), log p := by
  obtain ⟨N,h⟩ := prime_log_lower (A := 2) (c := 1/2) (by norm_num) (by norm_num)
  refine ⟨N,fun x hx => ?_⟩
  have he : primesInWindow (x:ℝ) 2 = primeInterval x (2*x) := by
    unfold primesInWindow primeInterval
    rw [Nat.floor_natCast,show (2:ℝ)*x=((2*x:ℕ):ℝ) by push_cast; rfl,Nat.floor_natCast]
  simpa only [he,one_div,div_eq_inv_mul,mul_one] using h x (by exact_mod_cast hx)

/-- Each complete dyadic block contributes a fixed log-weighted harmonic mass. -/
private theorem dyadic_weighted_reciprocals {n : ℕ} (hn : 0<n)
    (h : ∀ x ≥ n, (x:ℝ)/2 ≤ ∑ p ∈ primeInterval x (2*x), log p) (j : ℕ) :
    (j:ℝ)/4 ≤ ∑ p ∈ primeInterval n (n*2^j), log p / p := by
  induction j with
  | zero => simp [primeInterval]
  | succ j ih =>
    let x := n*2^j
    have hx : n ≤ x := Nat.le_mul_of_pos_right _ (by positivity)
    have hx0 : 0 < (x:ℝ) := by exact_mod_cast hn.trans_le hx
    have hblock : (1/4:ℝ) ≤ ∑ p ∈ primeInterval x (2*x), log p / p := by
      have hsum := h x hx
      calc
        (1/4:ℝ) = ((x:ℝ)/2)/(2*x) := by field_simp; norm_num
        _ ≤ _ := div_le_div_of_nonneg_right hsum (by positivity)
        _ = ∑ p ∈ primeInterval x (2*x), log p/(2*x) := sum_div _ _ _
        _ ≤ _ := by
          apply sum_le_sum
          intro p hp
          have hb := mem_Ioc.mp (mem_filter.mp hp).1
          have hp0 : 0 < (p:ℝ) := by exact_mod_cast (Nat.zero_le x).trans_lt hb.1
          exact div_le_div_of_nonneg_left (log_natCast_nonneg _) hp0 (by exact_mod_cast hb.2)
    rw [show n*2^(j+1)=2*x by dsimp [x]; ring,← consecutive_prime_intervals _ hx (by omega : x ≤ 2*x)]
    push_cast
    linarith only [ih,hblock]

/-- Uniform positive reciprocal mass between n and a cutoff small enough
that the second prime is always the larger member of the pair. -/
private theorem first_prime_interval :
    ∃ N : ℕ, ∀ n ≥ N, ∃ b ≥ n, b^4 ≤ n^5 ∧ 16*b^2 ≤ n^3 ∧
      (1/64:ℝ) ≤ ∑ p ∈ primeInterval n b, (p:ℝ)⁻¹ := by
  obtain ⟨N,h⟩ := dyadic_log_mass
  refine ⟨max 256 N,fun n hn => ?_⟩
  have hn0 : 0<n := by omega
  let k := Nat.log 2 n
  let j := k/4
  have hk : 8 ≤ k := (Nat.le_log_iff_pow_le (by decide) hn0.ne').mpr (by omega)
  have hj : 4+2*j ≤ k := by dsimp [j]; omega
  have hbnd : 16*(2^j)^2 ≤ n := by
    have hpow := (Nat.pow_le_pow_right (by decide : 0<2) hj).trans (Nat.pow_log_le_self 2 hn0.ne')
    simpa only [pow_add,show (2:ℕ)^4=16 by decide,mul_comm 2 j,pow_mul] using hpow
  let b := n*2^j
  have hb : 16*b^2 ≤ n^3 := by
    dsimp [b]
    calc
      _ = n^2*(16*(2^j)^2) := by ring
      _ ≤ n^2*n := Nat.mul_le_mul_left _ hbnd
      _ = _ := by ring
  have hj4 : (2^j)^4 ≤ n := by
    rw [← pow_mul]
    exact (Nat.pow_le_pow_right (by decide : 0<2) (show j*4≤k by dsimp [j]; omega)).trans
      (Nat.pow_log_le_self 2 hn0.ne')
  have hb4 : b^4 ≤ n^5 := by
    dsimp [b]
    rw [mul_pow,pow_succ n 4]
    exact Nat.mul_le_mul_left _ hj4
  refine ⟨b,Nat.le_mul_of_pos_right _ (by positivity),hb4,hb,?_⟩
  have hpow := Nat.lt_pow_succ_log_self (by decide : 1<2) n
  have hlog : log (n:ℝ) ≤ k+1 := by
    have hl := log_le_log (by exact_mod_cast hn0 : (0:ℝ)<n)
      (show (n:ℝ) ≤ (2:ℝ)^(k+1) by exact_mod_cast hpow.le)
    rw [log_pow,Nat.cast_add,Nat.cast_one] at hl
    exact hl.trans ((mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2))
      (by positivity : (0:ℝ) ≤ k+1)).trans_eq (by ring))
  have hjlog : log n ≤ 8*j := hlog.trans (by exact_mod_cast (show k+1 ≤ 8*j by dsimp [j]; omega))
  have hjn : 2^j ≤ n := (Nat.pow_le_pow_right (by decide : 0<2) (show j≤k by omega)).trans
    (Nat.pow_log_le_self 2 hn0.ne')
  have hb2 : b ≤ n^2 := by simpa only [b,pow_two] using Nat.mul_le_mul_left n hjn
  have hmass := dyadic_weighted_reciprocals hn0 (fun x hx => h x (by omega)) j
  have hupper : ∑ p ∈ primeInterval n b, log p/p ≤
      (2*log n)*∑ p ∈ primeInterval n b, (p:ℝ)⁻¹ := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hp' := mem_Ioc.mp (mem_filter.mp hp).1
    have hl := log_le_log (by exact_mod_cast hn0.trans hp'.1 : (0:ℝ)<p)
      (show (p:ℝ) ≤ (n:ℝ)^2 by exact_mod_cast hp'.2.trans hb2)
    rw [log_pow,Nat.cast_ofNat] at hl
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hl (by positivity : (0:ℝ) ≤ (p:ℝ)⁻¹)
  have hlpos : 0 < log (n:ℝ) := log_pos (by exact_mod_cast (show 1<n by omega))
  apply le_of_mul_le_mul_left (a := 2*log (n:ℝ)) _ (by positivity)
  linarith only [hjlog,hmass,hupper]

private def densityBand (n : ℕ) := (movingSemiprimes n).filter (fun r =>
  4*n^4 ≤ 5*(2*crossingPrime n*r) ∧ 8*(2*crossingPrime n*r) ≤ 7*n^4)

/-- Sum the prime logarithms in the rows (4X/(5p),7X/(8p)], where
X = n⁴/(2q) and q is the crossing prime. All second primes exceed b,
so different rows have disjoint semiprime products. -/
private theorem density_rows {n b : ℕ} (hn : 64 ≤ n) (hb : 16*b^2 ≤ n^3)
    (hPNT : ∀ x : ℝ, n ≤ x → (1/16)*x ≤ ∑ q ∈ primesInWindow x (35/32), log q) :
    ((n:ℝ)^3/40)*(∑ p ∈ primeInterval n b, (p:ℝ)⁻¹) ≤
      ∑ r ∈ densityBand n, log r := by
  let K := 2*crossingPrime n
  let X := 4*(n:ℝ)^4/(5*(K:ℝ))
  let x (p : ℕ) := X/p
  let P := primeInterval n b
  let Q (p : ℕ) := primesInWindow (x p) (35/32)
  obtain ⟨_,hq,hqn,_⟩ := crossingPrime_spec (by omega : 8≤n)
  have hK0 : 0<K := by dsimp [K]; omega
  have hK : (K:ℝ) ≤ 2*n := by exact_mod_cast (show K ≤ 2*n by dsimp [K]; omega)
  have hKpos : 0 < (K:ℝ) := by exact_mod_cast hK0
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hX : (2/5:ℝ)*(n:ℝ)^3 ≤ X := by
    apply (le_div_iff₀ (by positivity : 0<5*(K:ℝ))).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hK (by positivity : 0≤(n:ℝ)^3)]
  have hPb {p : ℕ} (hp : p ∈ P) : n<p ∧ p≤b ∧ p.Prime := by
    obtain ⟨hi,hpr⟩ := mem_filter.mp hp
    exact ⟨(mem_Ioc.mp hi).1,(mem_Ioc.mp hi).2,hpr⟩
  have hbefore {p : ℕ} (hp : p ∈ P) : (b:ℝ) < x p := by
    obtain ⟨_,hpB,hpr⟩ := hPb hp
    apply (lt_div_iff₀ (by exact_mod_cast hpr.pos : 0 < (p:ℝ))).mpr
    have hB : 16*(b:ℝ)^2 ≤ (n:ℝ)^3 := by exact_mod_cast hb
    have hbp : (b:ℝ)*p ≤ (b:ℝ)*b := mul_le_mul_of_nonneg_left
      (by exact_mod_cast hpB) (Nat.cast_nonneg _)
    nlinarith only [hbp,hB,hX,pow_pos hn0 3]
  have hQb {p q : ℕ} (hp : p ∈ P) (h : q ∈ Q p) : b<q ∧ q.Prime := by
    have he := mem_primesInWindow_bounds ((Nat.cast_nonneg _).trans (hbefore hp).le)
      (by norm_num : (0:ℝ)≤35/32) h
    exact ⟨by exact_mod_cast (hbefore hp).trans he.1,he.2.2⟩
  have hprod {p q : ℕ} (hp : p ∈ P) (hq' : q ∈ Q p) : p*q ∈ densityBand n := by
    obtain ⟨hnp,hpb,hpp⟩ := hPb hp
    obtain ⟨hbq,hqp⟩ := hQb hp hq'
    have he := mem_primesInWindow_bounds ((Nat.cast_nonneg _).trans (hbefore hp).le)
      (by norm_num : (0:ℝ)≤35/32) hq'
    have hp0 : 0 < (p:ℝ) := by exact_mod_cast hpp.pos
    have hid : ((K:ℝ)*p)*x p = (4/5:ℝ)*(n:ℝ)^4 := by
      dsimp [x,X]
      field_simp
    have hlo := mul_le_mul_of_nonneg_left he.1.le (mul_nonneg hKpos.le hp0.le)
    have hhi := mul_le_mul_of_nonneg_left he.2.1 (mul_nonneg hKpos.le hp0.le)
    have hl : 4*n^4 ≤ 5*(K*(p*q)) := by
      exact_mod_cast (show 4*(n:ℝ)^4 ≤ 5*((K:ℝ)*(p*q)) by nlinarith only [hid,hlo])
    have hu : 8*(K*(p*q)) ≤ 7*n^4 := by
      exact_mod_cast (show 8*((K:ℝ)*(p*q)) ≤ 7*(n:ℝ)^4 by nlinarith only [hid,hhi])
    have hcop {u : ℕ} (hu : u.Prime) (hnu : n<u) : u.Coprime n.factorial :=
      hu.coprime_iff_not_dvd.mpr fun hd => (not_le.mpr hnu) (hu.dvd_factorial.mp hd)
    refine mem_filter.mpr ⟨movingSemiprimes_of_top_band hn (hnp.trans_le
      (Nat.le_mul_of_pos_right _ hqp.pos)) ((hcop hpp hnp).mul_left (hcop hqp (by omega)))
      ?_ (by change 3*n^4≤4*(K*(p*q)); omega) hu,hl,hu⟩
    rw [ArithmeticFunction.cardFactors_mul hpp.ne_zero hqp.ne_zero,
      ArithmeticFunction.cardFactors_apply_prime hpp,ArithmeticFunction.cardFactors_apply_prime hqp]
  let product := fun z : (p : ℕ) × ℕ => z.1*z.2
  have hinj : Set.InjOn product ↑(P.sigma Q) := by
    rintro ⟨p,q⟩ hz ⟨p',q'⟩ hw he
    obtain ⟨hp,hq⟩ := mem_sigma.mp hz
    obtain ⟨hp',hq'⟩ := mem_sigma.mp hw
    change p*q=p'*q' at he
    obtain ⟨_,hpb,hpp⟩ := hPb hp
    obtain ⟨_,_,hpp'⟩ := hPb hp'
    obtain ⟨hbq',hqp'⟩ := hQb hp' hq'
    have hd : p ∣ p'*q' := he ▸ dvd_mul_right p q
    have hpeq : p=p' := by
      rcases hpp.dvd_mul.mp hd with h | h
      · exact ((hpp'.dvd_iff_eq hpp.ne_one).mp h).symm
      · have := (hqp'.dvd_iff_eq hpp.ne_one).mp h
        omega
    subst p'
    obtain rfl := Nat.eq_of_mul_eq_mul_left hpp.pos he
    rfl
  calc
    _ = ∑ p ∈ P, ((n:ℝ)^3/40)*(p:ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ ∑ p ∈ P, ∑ q ∈ Q p, log q := by
      apply sum_le_sum
      intro p hp
      have hnx : (n:ℝ) ≤ x p := (show (n:ℝ) ≤ b by exact_mod_cast
        ((hPb hp).1.le.trans (hPb hp).2.1)).trans (hbefore hp).le
      apply le_trans _ (hPNT (x p) hnx)
      have hh := mul_le_mul_of_nonneg_right hX (by positivity : 0 ≤ (p:ℝ)⁻¹)
      dsimp only [x]
      simp only [div_eq_mul_inv] at hh ⊢
      linarith only [hh]
    _ = ∑ z ∈ P.sigma Q, log z.2 := by rw [sum_sigma]
    _ ≤ _ := sum_le_sum_of_injOn product hinj (by
      rintro _ hz
      obtain ⟨⟨p,q⟩,hpq,rfl⟩ := mem_image.mp hz
      exact hprod (mem_sigma.mp hpq).1 (mem_sigma.mp hpq).2)
      (by
        rintro ⟨p,q⟩ hz
        obtain ⟨hp,hq⟩ := mem_sigma.mp hz
        apply log_le_log (Nat.cast_pos.mpr (hQb hp hq).2.pos)
        exact_mod_cast Nat.le_mul_of_pos_left q (hPb hp).2.2.pos)
      (fun r _ _ => log_natCast_nonneg r)

/-- The reserve is at least a fixed positive multiple of the complete window
normalization at every sufficiently late sample. -/
theorem movingSemiprimeSurplus_cubic :
    ∃ N : ℕ, ∀ n ≥ N, (n:ℝ)^3/32768 ≤ movingSemiprimeSurplus n := by
  obtain ⟨A,hA⟩ := first_prime_interval
  obtain ⟨B,hB⟩ := prime_log_lower (A := 35/32) (c := 1/16) (by norm_num) (by norm_num)
  refine ⟨max 64 (max A B),fun n hn => ?_⟩
  obtain ⟨b,_,_,hb,hm⟩ := hA n (by omega)
  have hrows := density_rows (by omega : 64≤n) hb (fun x hx => hB x
    ((show (B:ℝ) ≤ n by exact_mod_cast (show B ≤ n by omega)).trans hx))
  have hs := movingSemiprimeSurplus_lower (by omega : 64≤n)
  change (3/32:ℝ)*(∑ r ∈ densityBand n, log r) ≤ _ at hs
  have hrec := mul_le_mul_of_nonneg_left hm (by positivity : 0≤(n:ℝ)^3/40)
  linarith only [hrec,hrows,hs,pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 3]

/-- Upper bound for the deficit mass obtained by using the uniform lower
bound in place of the exact semiprime surplus at each sample. -/
def cubicReserveMassOn (m b : ℕ) : ℝ := ∑ n ∈ Icc m b, max
  (cubicSmoothMoments n - cubicWeightedResponse n (cubicCompensatedCoefficient n) -
    (n:ℝ)^3/32768) 0 / (n:ℝ)^3

theorem cubicCompensatedMassOn_le_reserve :
    ∃ N : ℕ, ∀ m ≥ N, ∀ b, cubicCompensatedMassOn m b ≤ cubicReserveMassOn m b := by
  obtain ⟨N,hN⟩ := movingSemiprimeSurplus_cubic
  refine ⟨N,fun m hm b => ?_⟩
  apply sum_le_sum
  intro n hn
  exact div_le_div_of_nonneg_right
    (max_le_max_right _ (sub_le_sub_left (hN n (hm.trans (mem_Icc.mp hn).1)) _))
    (by positivity)

theorem rh_of_cubicReserveMassOn_powerWindows
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, cubicReserveMassOn m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply rh_of_cubicCompensatedMassOn_powerWindows
  obtain ⟨N,hN⟩ := cubicCompensatedMassOn_le_reserve
  intro α hα
  obtain ⟨δ,hδ,hδ1,hw⟩ := h α hα
  refine ⟨δ,hδ,hδ1,fun A => ?_⟩
  obtain ⟨m,hm,he⟩ := hw (max N A)
  exact ⟨m,by omega,(hN m (by omega) _).trans he⟩

/-- Odd products of three primes in the interior weight band. The first
two primes individually fit below the sieve cutoff and together cross it. -/
def crossingPrimeTriples (n : ℕ) : Finset ℕ := (Icc 1 (n^4)).filter fun t =>
  4*n^4 ≤ 5*t ∧ 8*t ≤ 7*n^4 ∧ ∃ a b r : ℕ, a.Prime ∧ b.Prime ∧ r.Prime ∧
    2<a ∧ a<b ∧ b≤n ∧ n<r ∧ n<a*b ∧ t=a*b*r

/-- The part of the compensated coefficient on the crossing triples. -/
def crossingTripleCoefficient (n t : ℕ) : ℝ :=
  if t ∈ crossingPrimeTriples n then cubicCompensatedCoefficient n t else 0

/-- An ordinary prime sum with no repeated averages or sieve coefficients. -/
def crossingTripleMass (n : ℕ) : ℝ := ∑ t ∈ crossingPrimeTriples n,
  log t.maxPrimeFac*(2-(n:ℝ)^4/t)

private theorem crossing_triple_value {n a b r : ℕ} (hn : 64≤n)
    (ha : a.Prime) (hb : b.Prime) (hr : r.Prime) (h2 : 2<a) (hab : a<b)
    (hbn : b≤n) (hnr : n<r) (hcross : n<a*b)
    (hl : 4*n^4 ≤ 5*(a*b*r)) (hu : 8*(a*b*r) ≤ 7*n^4) :
    cubicCompensatedCoefficient n (a*b*r) = log r := by
  have hscale : 64*n^3 ≤ n^4 := (Nat.mul_le_mul_right (n^3) hn).trans_eq (by ring)
  have hp : 0<n^3 := by positivity
  have hodd {p : ℕ} (hp : p.Prime) (hg : 2<p) : ¬2 ∣ p := fun h =>
    (ne_of_gt hg) ((hp.dvd_iff_eq (by decide : 2≠1)).mp h)
  have ho : ¬2 ∣ a*b*r := by
    rw [Nat.prime_two.dvd_mul,Nat.prime_two.dvd_mul]
    exact not_or.mpr ⟨not_or.mpr ⟨hodd ha h2,hodd hb (by omega)⟩,hodd hr (by omega)⟩
  rw [cubicCompensatedCoefficient_of_odd_upper (by omega : 8≤n) (by omega) ho]
  exact cubicThreeFactorCoefficient_crossing_pair (by omega) hr.pos
    (hr.coprime_iff_not_dvd.mpr fun h => (not_le.mpr hnr) (hr.dvd_factorial.mp h))
    ha hb hab.ne (hab.le.trans hbn) hbn hcross (no_four_of_le_fourth (by omega))

private theorem crossing_triple_nonneg {n t : ℕ} (hn : 64≤n) (ht : t ∈ crossingPrimeTriples n) :
    0 ≤ cubicCompensatedCoefficient n t := by
  obtain ⟨_,hl,hu,a,b,r,ha,hb,hr,h2,hab,hbn,hnr,hcross,rfl⟩ := mem_filter.mp ht
  rw [crossing_triple_value hn ha hb hr h2 hab hbn hnr hcross hl hu]
  exact log_natCast_nonneg _

/-- Each triple has a unique largest prime, and its entire averaged weight
is the single central value at n⁴. -/
theorem crossingTripleResponse_eq {n : ℕ} (hn : 64≤n) :
    cubicWeightedResponse n (crossingTripleCoefficient n) = crossingTripleMass n := by
  unfold crossingTripleCoefficient crossingTripleMass
  rw [cubicWeightedResponse_interior_eq hn _ _ (fun t ht =>
    ⟨(mem_filter.mp ht).2.1,(mem_filter.mp ht).2.2.1⟩)]
  apply sum_congr rfl
  intro t ht
  obtain ⟨_,hl,hu,a,b,r,ha,hb,hr,h2,hab,hbn,hnr,hc,rfl⟩ := mem_filter.mp ht
  rw [crossing_triple_value hn ha hb hr h2 hab hbn hnr hc hl hu,
    Nat.maxPrimeFac_mul (Nat.mul_ne_zero ha.ne_zero hb.ne_zero) hr.ne_zero,
    Nat.maxPrimeFac_mul ha.ne_zero hb.ne_zero,ha.maxPrimeFac_eq_self,hb.maxPrimeFac_eq_self,
    hr.maxPrimeFac_eq_self,max_eq_right hab.le,max_eq_right (hbn.trans hnr.le)]

private theorem primeInterval_mem {u v p : ℕ} (hp : p ∈ primeInterval u v) :
    u<p ∧ p≤v ∧ p.Prime := by
  obtain ⟨hi,hpr⟩ := mem_filter.mp hp
  exact ⟨(mem_Ioc.mp hi).1,(mem_Ioc.mp hi).2,hpr⟩

/-- Disjoint intervals of small primes, each of fixed harmonic mass, fit
between the square root and the cutoff. -/
private theorem two_prime_intervals :
    ∃ N : ℕ, ∀ n ≥ N, ∃ v w : ℕ, 2 ≤ n.sqrt ∧ n.sqrt ≤ v ∧ v ≤ w ∧ w ≤ n ∧
      (1/64:ℝ) ≤ ∑ a ∈ primeInterval n.sqrt v, (a:ℝ)⁻¹ ∧
      (1/64:ℝ) ≤ ∑ b ∈ primeInterval v w, (b:ℝ)⁻¹ := by
  obtain ⟨N,hN⟩ := first_prime_interval
  refine ⟨(max N 2)^2,fun n hn => ?_⟩
  let u := n.sqrt
  have hu : max N 2 ≤ u := Nat.le_sqrt'.mpr hn
  obtain ⟨v,huv,hv4,_,hA⟩ := hN u (by omega)
  obtain ⟨w,hvw,_,hw2,hB⟩ := hN v (by omega)
  have hw : w^2 ≤ v^3 := by omega
  have hu0 : 0<u := by omega
  have h8 : w^8 ≤ n^8 := calc
    _ = (w^2)^4 := by ring
    _ ≤ (v^3)^4 := Nat.pow_le_pow_left hw _
    _ = (v^4)^3 := by ring
    _ ≤ (u^5)^3 := Nat.pow_le_pow_left hv4 _
    _ = u^15 := by ring
    _ ≤ u^16 := Nat.pow_le_pow_right hu0 (by decide)
    _ = (u^2)^8 := by ring
    _ ≤ _ := Nat.pow_le_pow_left (Nat.sqrt_le' n) _
  exact ⟨v,w,by omega,huv,hvw,le_of_pow_le_pow_left₀ (by decide : 8 ≠ 0) (Nat.zero_le _) h8,hA,hB⟩

private theorem prime_dvd_three {p a b r : ℕ} (hp : p.Prime) (ha : a.Prime)
    (hb : b.Prime) (hr : r.Prime) (hd : p ∣ a*b*r) : p=a ∨ p=b ∨ p=r := by
  rw [hp.dvd_mul,hp.dvd_mul] at hd
  rcases hd with (h | h) | h
  · exact Or.inl ((ha.dvd_iff_eq hp.ne_one).mp h).symm
  · exact Or.inr (Or.inl ((hb.dvd_iff_eq hp.ne_one).mp h).symm)
  · exact Or.inr (Or.inr ((hr.dvd_iff_eq hp.ne_one).mp h).symm)

/-- For each pair of small primes the large prime ranges over a fixed-ratio
interval on which its full logarithm contributes to the compensated response. -/
private theorem crossing_triple_rows {n v w : ℕ} (hn : 64≤n) (hu : 2≤n.sqrt)
    (hvw : v≤w) (hwn : w≤n)
    (hPNT : ∀ x : ℝ, n≤x → (1/16)*x ≤ ∑ r ∈ primesInWindow x (35/32), log r) :
    ((n:ℝ)^4/20) * ((∑ a ∈ primeInterval n.sqrt v, (a:ℝ)⁻¹) *
      ∑ b ∈ primeInterval v w, (b:ℝ)⁻¹) ≤
      ∑ t ∈ crossingPrimeTriples n, cubicCompensatedCoefficient n t := by
  let A := primeInterval n.sqrt v
  let B := primeInterval v w
  let I := A ×ˢ B
  let x (i : ℕ × ℕ) := (4*(n:ℝ)^4/5)/((i.1:ℝ)*i.2)
  let R (i : ℕ × ℕ) := primesInWindow (x i) (35/32)
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hstart {i : ℕ × ℕ} (hi : i ∈ I) : (n:ℝ) < x i := by
    obtain ⟨hA,hB⟩ := mem_product.mp hi
    obtain ⟨_,hav,ha⟩ := primeInterval_mem hA
    obtain ⟨_,hbw,hb⟩ := primeInterval_mem hB
    have ha0 : 0 < (i.1:ℝ) := Nat.cast_pos.mpr ha.pos
    have hb0 : 0 < (i.2:ℝ) := Nat.cast_pos.mpr hb.pos
    apply (lt_div_iff₀ (mul_pos ha0 hb0)).mpr
    have hab : (i.1:ℝ)*i.2 ≤ (n:ℝ)*n :=
      by exact_mod_cast Nat.mul_le_mul ((hav.trans hvw).trans hwn) (hbw.trans hwn)
    have hscale : (5:ℝ)<4*n := by exact_mod_cast (show 5<4*n by omega)
    nlinarith only [mul_le_mul_of_nonneg_left hab hn0.le,mul_lt_mul_of_pos_right hscale (pow_pos hn0 3)]
  have hrow {i : ℕ × ℕ} (hi : i ∈ I) {r : ℕ} (hr : r ∈ R i) :
      r.Prime ∧ n<r ∧ i.1*i.2*r ∈ crossingPrimeTriples n ∧
      cubicCompensatedCoefficient n (i.1*i.2*r) = log r := by
    obtain ⟨hA,hB⟩ := mem_product.mp hi
    obtain ⟨hua,hav,ha⟩ := primeInterval_mem hA
    obtain ⟨hvb,hbw,hb⟩ := primeInterval_mem hB
    obtain ⟨hl,hh,hrp⟩ := mem_primesInWindow_bounds (hn0.trans (hstart hi)).le
      (by norm_num : (0:ℝ)≤35/32) hr
    have hnr : n<r := by exact_mod_cast (hstart hi).trans hl
    have hc : n < i.1*i.2 := (Nat.lt_succ_sqrt' n).trans_le (by
      rw [pow_two]; exact Nat.mul_le_mul hua (by omega))
    have ha0 : 0<(i.1:ℝ) := Nat.cast_pos.mpr ha.pos
    have hb0 : 0<(i.2:ℝ) := Nat.cast_pos.mpr hb.pos
    have hx : ((i.1:ℝ)*i.2)*x i = 4*(n:ℝ)^4/5 := by dsimp [x]; field_simp
    have hlo := mul_le_mul_of_nonneg_left hl.le (mul_pos ha0 hb0).le
    have hhi := mul_le_mul_of_nonneg_left hh (mul_pos ha0 hb0).le
    have hl' : 4*n^4 ≤ 5*(i.1*i.2*r) := by
      exact_mod_cast (show 4*(n:ℝ)^4 ≤ 5*((i.1:ℝ)*i.2*r) by nlinarith only [hx,hlo])
    have hu' : 8*(i.1*i.2*r) ≤ 7*n^4 := by
      exact_mod_cast (show 8*((i.1:ℝ)*i.2*r) ≤ 7*(n:ℝ)^4 by nlinarith only [hx,hhi])
    have htpos := Nat.mul_pos (Nat.mul_pos ha.pos hb.pos) hrp.pos
    have h2 := hu.trans_lt hua
    have hab := hav.trans_lt hvb
    have hbn := hbw.trans hwn
    refine ⟨hrp,hnr,mem_filter.mpr ⟨mem_Icc.mpr ⟨htpos,by omega⟩,hl',hu',i.1,i.2,r,ha,hb,
      hrp,h2,hab,hbn,hnr,hc,rfl⟩,crossing_triple_value hn ha hb hrp h2 hab hbn hnr hc hl' hu'⟩
  let product := fun z : (_ : ℕ × ℕ) × ℕ => z.1.1*z.1.2*z.2
  have hinj : Set.InjOn product ↑(I.sigma R) := by
    rintro ⟨⟨a,b⟩,r⟩ hz ⟨⟨a',b'⟩,r'⟩ hz' he
    obtain ⟨hi,hr⟩ := mem_sigma.mp hz
    obtain ⟨hi',hr'⟩ := mem_sigma.mp hz'
    obtain ⟨hA,hB⟩ := mem_product.mp hi
    obtain ⟨hA',hB'⟩ := mem_product.mp hi'
    obtain ⟨_,hav,ha⟩ := primeInterval_mem hA
    obtain ⟨hvb,hbw,hb⟩ := primeInterval_mem hB
    obtain ⟨_,hav',ha'⟩ := primeInterval_mem hA'
    obtain ⟨hvb',_,hb'⟩ := primeInterval_mem hB'
    obtain ⟨hrp',hnr',_⟩ := hrow hi' hr'
    change a*b*r=a'*b'*r' at he
    have hda : a ∣ a'*b'*r' := he ▸ dvd_mul_of_dvd_left (dvd_mul_right a b) r
    have hdb : b ∣ a'*b'*r' := he ▸ dvd_mul_of_dvd_left (dvd_mul_left b a) r
    have ea := prime_dvd_three ha ha' hb' hrp' hda
    have eb := prime_dvd_three hb ha' hb' hrp' hdb
    dsimp only at ea eb hav hav' hvb hvb' hbw hnr'
    have : a=a' := by omega
    subst a'
    have : b=b' := by omega
    subst b'
    obtain rfl := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos ha.pos hb.pos) he
    rfl
  calc
    _ = ∑ i ∈ I, (1/16:ℝ)*x i := by
      rw [show I=A ×ˢ B from rfl,sum_product]
      change (n:ℝ)^4/20*((∑ a ∈ A, (a:ℝ)⁻¹)*∑ b ∈ B, (b:ℝ)⁻¹) = _
      rw [← mul_assoc,mul_sum (s := A),sum_mul]
      apply sum_congr rfl
      intro a _
      rw [mul_sum]
      apply sum_congr rfl
      intro b _
      dsimp [x]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ ∑ i ∈ I, ∑ r ∈ R i, log r := sum_le_sum fun i hi => hPNT (x i) (hstart hi).le
    _ = ∑ z ∈ I.sigma R, log z.2 := by rw [sum_sigma]
    _ ≤ _ := sum_le_sum_of_injOn product hinj (by
      intro t ht
      obtain ⟨z,hz,rfl⟩ := mem_image.mp ht
      obtain ⟨hi,hr⟩ := mem_sigma.mp hz
      exact (hrow hi hr).2.2.1)
      (by
        intro z hz
        obtain ⟨hi,hr⟩ := mem_sigma.mp hz
        exact (hrow hi hr).2.2.2.ge)
      (fun t ht _ => crossing_triple_nonneg hn ht)

/-- A disjoint positive part of the compensated response has quartic mass
at every sufficiently large sample. No RH estimate is used for the primes. -/
theorem crossingTripleMass_quartic :
    ∃ N : ℕ, ∀ n ≥ N, (3/327680:ℝ)*(n:ℝ)^4 ≤ crossingTripleMass n := by
  obtain ⟨A,hA⟩ := two_prime_intervals
  obtain ⟨B,hB⟩ := prime_log_lower (A := 35/32) (c := 1/16) (by norm_num) (by norm_num)
  refine ⟨max 64 (max A B),fun n hn => ?_⟩
  obtain ⟨v,w,hu,_,hvw,hwn,hm,hm'⟩ := hA n (by omega)
  have hrows := crossing_triple_rows (by omega : 64≤n) hu hvw hwn (fun x hx => hB x
    ((show (B:ℝ)≤n by exact_mod_cast (show B≤n by omega)).trans hx))
  have hprod := mul_le_mul hm hm' (by norm_num) ((by norm_num : (0:ℝ)≤1/64).trans hm)
  have hmass := mul_le_mul_of_nonneg_left hprod (by positivity : 0≤(n:ℝ)^4/20)
  rw [← crossingTripleResponse_eq (by omega : 64≤n)]
  unfold crossingTripleCoefficient
  rw [cubicWeightedResponse_interior_eq (by omega : 64≤n) _ _ (fun t ht =>
    ⟨(mem_filter.mp ht).2.1,(mem_filter.mp ht).2.2.1⟩)]
  calc
    _ ≤ (3/4:ℝ)*∑ t ∈ crossingPrimeTriples n, cubicCompensatedCoefficient n t := by
      linarith only [hmass,hrows]
    _ ≤ _ := by
      rw [mul_sum]
      apply sum_le_sum
      intro t ht
      obtain ⟨hi,hl,_⟩ := mem_filter.mp ht
      have ht0 : 0<(t:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hi).1
      have htlow : 4*(n:ℝ)^4 ≤ 5*t := by exact_mod_cast hl
      have hdiv : (n:ℝ)^4/t ≤ 5/4 := (div_le_iff₀ ht0).mpr (by linarith)
      rw [mul_comm (3/4:ℝ)]
      exact mul_le_mul_of_nonneg_left (by linarith only [hdiv]) (crossing_triple_nonneg (by omega) ht)

/-- The number of complete dyadic intervals paid by the triple mass. -/
def nearCutoffBlocks (n : ℕ) := Nat.log 2 n / 268435456 + 1

private theorem le_dyadic_power_cutoff {d n p : ℕ} (hd : 0<d) (hp : p^d ≤ n^(d+1)) :
    p ≤ n*2^(Nat.log 2 n/d+1) := by
  apply le_of_pow_le_pow_left₀ hd.ne' (Nat.zero_le _)
  have hk : Nat.log 2 n + 1 ≤ (Nat.log 2 n/d+1)*d := by
    rw [Nat.add_mul,one_mul,Nat.mul_comm (Nat.log 2 n/d)]
    have he := Nat.mod_add_div (Nat.log 2 n) d
    have hr := Nat.mod_lt (Nat.log 2 n) hd
    omega
  have hscale := (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le.trans
    (Nat.pow_le_pow_right (by decide : 0<2) hk)
  rw [mul_pow,← pow_mul]
  exact hp.trans ((pow_succ n d).le.trans (Nat.mul_le_mul_left _ hscale))

/-- The covered range includes every smaller prime p ≤ n^(1+1/268435456).
The integer formulation avoids rounding the right endpoint. -/
theorem le_nearCutoff_of_pow_le {n p : ℕ} (hp : p^268435456 ≤ n^(268435456+1)) :
    p ≤ n*2^(nearCutoffBlocks n) :=
  le_dyadic_power_cutoff (d := 268435456) (n := n) (p := p) (by decide) hp

/-- All upper semiprimes whose smaller prime falls in the covered range,
through the full smoothing support. -/
def nearCutoffSemiprimes (n : ℕ) : Finset ℕ :=
  (Ioc (3*n^3) (cubicSampleEnd n)).filter fun t =>
    ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ n<p ∧ p≤n*2^(nearCutoffBlocks n) ∧ p≤r ∧ t=p*r

def nearCutoffCoefficient (n t : ℕ) : ℝ :=
  if t ∈ nearCutoffSemiprimes n then cubicCompensatedCoefficient n t else 0

/-- A square with base in this range lies below the upper sum, so every
selected semiprime has two distinct factors and loses its entire logarithm. -/
theorem nearCutoffCoefficient_eq {n t : ℕ} (hn : 8 ≤ n) (ht : t ∈ nearCutoffSemiprimes n) :
    nearCutoffCoefficient n t = -log t := by
  obtain ⟨hi,p,r,hp,hr,hnp,hcut,hpr,rfl⟩ := mem_filter.mp ht
  have ht3 := (mem_Ioc.mp hi).1
  have hk : 3 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide) (by omega : n≠0)).mpr hn
  have hsmall : 2^(nearCutoffBlocks n*2) ≤ n := (Nat.pow_le_pow_right (by decide : 0<2)
    (show nearCutoffBlocks n*2 ≤ Nat.log 2 n by dsimp [nearCutoffBlocks]; omega)).trans
    (Nat.pow_log_le_self 2 (by omega : n≠0))
  have hpsq : p^2 ≤ n^3 := calc
    _ ≤ (n*2^(nearCutoffBlocks n))^2 := Nat.pow_le_pow_left hcut _
    _ = n^2*2^(nearCutoffBlocks n*2) := by rw [mul_pow,pow_mul]
    _ ≤ n^2*n := Nat.mul_le_mul_left _ hsmall
    _ = _ := by ring
  have hne : p≠r := by
    rintro rfl
    rw [pow_two] at hpsq
    omega
  have hΛ : ArithmeticFunction.vonMangoldt (p*r)=0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (by
    rw [isPrimePow_iff_card_primeFactors_eq_one,Nat.primeFactors_mul hp.ne_zero hr.ne_zero,
      hp.primeFactors,hr.primeFactors]
    simp [hne])
  have hcop {a : ℕ} (ha : a.Prime) (h : n<a) : a.Coprime n.factorial :=
    ha.coprime_iff_not_dvd.mpr fun hd => (not_le.mpr h) (ha.dvd_factorial.mp hd)
  have hodd : ¬2 ∣ p*r := by
    rw [Nat.prime_two.dvd_mul]
    intro h
    rcases h with h | h
    · have := (hp.dvd_iff_eq (by decide : 2≠1)).mp h
      omega
    · have := (hr.dvd_iff_eq (by decide : 2≠1)).mp h
      omega
  have hΩ : Ω (p*r) = 2 := by
    rw [ArithmeticFunction.cardFactors_mul hp.ne_zero hr.ne_zero,
      ArithmeticFunction.cardFactors_apply_prime hp,ArithmeticFunction.cardFactors_apply_prime hr]
  rw [nearCutoffCoefficient,ite_eq_left ht,cubicCompensatedCoefficient_of_odd_upper hn ht3 hodd,
    cubicThreeFactorCoefficient_rough_eq (by omega) (hnp.trans_le (Nat.le_mul_of_pos_right _ hr.pos))
      ((hcop hp hnp).mul_left (hcop hr (hnp.trans_le hpr))),ite_eq_left (Or.inl hΩ),hΛ,zero_sub]

private theorem primeInterval_card_log {n : ℕ} (hn : 0<n) :
    ((primeInterval n (2*n)).card:ℝ)*log n ≤ log 4*(2*n) := by
  have hp0 : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  calc
    _ = ∑ _p ∈ primeInterval n (2*n), log n := by simp
    _ ≤ ∑ p ∈ primeInterval n (2*n), log p := sum_le_sum fun p hp =>
      log_le_log hp0 (by exact_mod_cast (primeInterval_mem hp).1.le)
    _ ≤ Chebyshev.theta ((2*n:ℕ):ℝ) := by
      rw [Chebyshev.theta_eq_sum_Icc,Nat.floor_natCast]
      apply sum_le_sum_of_subset_of_nonneg _ (fun p _ _ => log_natCast_nonneg p)
      intro p hp
      obtain ⟨_,hu,hpr⟩ := primeInterval_mem hp
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,hu⟩,hpr⟩
    _ ≤ _ := by simpa using Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (2*n))

private theorem dyadic_reciprocal_upper {n : ℕ} (hn : 0<n) (j : ℕ) :
    log n*(∑ p ∈ primeInterval n (n*2^j), (p:ℝ)⁻¹) ≤ 2*log 4*j := by
  induction j with
  | zero => simp [primeInterval]
  | succ j ih =>
    let x := n*2^j
    have hnx : n≤x := Nat.le_mul_of_pos_right _ (by positivity)
    have hx0 : 0<(x:ℝ) := Nat.cast_pos.mpr (hn.trans_le hnx)
    have hlog := log_le_log (Nat.cast_pos.mpr hn) (show (n:ℝ)≤x by exact_mod_cast hnx)
    have hblock : log n*(∑ p ∈ primeInterval x (2*x), (p:ℝ)⁻¹) ≤ 2*log 4 := by
      rw [mul_sum]
      calc
        _ ≤ ∑ _p ∈ primeInterval x (2*x), log x/x := by
          apply sum_le_sum
          intro p hp
          rw [← div_eq_mul_inv]
          exact (div_le_div_of_nonneg_right hlog (Nat.cast_nonneg p)).trans
            (div_le_div_of_nonneg_left (log_natCast_nonneg x) hx0
              (by exact_mod_cast (primeInterval_mem hp).1.le))
        _ = ((primeInterval x (2*x)).card:ℝ)*log x/x := by simp; ring
        _ ≤ _ := (div_le_iff₀ hx0).mpr (by linarith only [primeInterval_card_log (hn.trans_le hnx)])
    rw [show n*2^(j+1)=2*x by dsimp [x]; ring,← consecutive_prime_intervals _ hnx (by omega : x≤2*x),
      mul_add]
    push_cast
    linarith only [ih,hblock]

private theorem nearCutoff_log_sum {n : ℕ} (hn : 8 ≤ n) :
    ∑ t ∈ nearCutoffSemiprimes n, log t ≤
      (4*log 4*(n:ℝ)^4)*∑ p ∈ primeInterval n (n*2^(nearCutoffBlocks n)), (p:ℝ)⁻¹ := by
  let P := primeInterval n (n*2^(nearCutoffBlocks n))
  let Q (p : ℕ) := (Icc 0 (2*n^4/p)).filter Nat.Prime
  let e := fun t : ℕ => (⟨t/t.maxPrimeFac,t.maxPrimeFac⟩ : (_ : ℕ) × ℕ)
  have hpair {t : ℕ} (ht : t ∈ nearCutoffSemiprimes n) :
      e t ∈ P.sigma Q ∧ (e t).1*(e t).2=t ∧ log t ≤ 2*log (e t).2 := by
    obtain ⟨hi,p,r,hp,hr,hnp,hp2,hpr,rfl⟩ := mem_filter.mp ht
    have hmax : (p*r).maxPrimeFac=r := by
      rw [Nat.maxPrimeFac_mul hp.ne_zero hr.ne_zero,hp.maxPrimeFac_eq_self,hr.maxPrimeFac_eq_self,
        max_eq_right hpr]
    have he : e (p*r) = ⟨p,r⟩ := by dsimp [e]; rw [hmax,Nat.mul_div_cancel _ hr.pos]
    rw [he]
    have hsize := ((mem_Ioc.mp hi).2).trans (cubicSampleEnd_le hn)
    refine ⟨mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨hnp,hp2⟩,hp⟩,
      mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,(Nat.le_div_iff_mul_le hp.pos).mpr
        ((Nat.mul_comm r p).le.trans hsize)⟩,hr⟩⟩,rfl,?_⟩
    rw [Nat.cast_mul,log_mul (Nat.cast_ne_zero.mpr hp.ne_zero) (Nat.cast_ne_zero.mpr hr.ne_zero)]
    nlinarith only [log_le_log (Nat.cast_pos.mpr hp.pos) (show (p:ℝ) ≤ r by exact_mod_cast hpr)]
  have hinj : Set.InjOn e ↑(nearCutoffSemiprimes n) := by
    intro s hs t ht he
    obtain ⟨_,hs',_⟩ := hpair hs
    obtain ⟨_,ht',_⟩ := hpair ht
    rw [he,ht'] at hs'
    exact hs'.symm
  calc
    _ ≤ ∑ z ∈ P.sigma Q, 2*log z.2 := sum_le_sum_of_injOn e hinj
      (by intro z hz; obtain ⟨t,ht,rfl⟩ := mem_image.mp hz; exact (hpair ht).1)
      (fun t ht => (hpair ht).2.2) (fun z _ _ => by positivity [log_natCast_nonneg z.2])
    _ = ∑ p ∈ P, 2*Chebyshev.theta ((2*n^4/p:ℕ):ℝ) := by
      rw [sum_sigma]
      apply sum_congr rfl
      intro p _
      rw [Chebyshev.theta_eq_sum_Icc,Nat.floor_natCast,mul_sum]
    _ ≤ ∑ p ∈ P, (4*log 4*(n:ℝ)^4)*(p:ℝ)⁻¹ := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hnp,_,hpr⟩ := primeInterval_mem hp
      have hdiv : ((2*n^4/p:ℕ):ℝ) ≤ 2*(n:ℝ)^4/p := (le_div_iff₀ (Nat.cast_pos.mpr hpr.pos)).mpr
        (by exact_mod_cast Nat.div_mul_le_self (2*n^4) p)
      have hb := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (2*n^4/p))
      have hlog := mul_le_mul_of_nonneg_left hdiv (show 0≤log 4 by positivity)
      rw [div_eq_mul_inv] at hlog
      linarith only [hb,hlog]
    _ = _ := (mul_sum ..).symm

/-- Each dyadic block of possible smaller primes costs only a logarithmic
fraction of the full quartic scale, with absolute values on all moving weights. -/
theorem nearCutoffResponse_log_bound {n : ℕ} (hn : 8 ≤ n) :
    log n * |cubicWeightedResponse n (nearCutoffCoefficient n)| ≤
      16*(log 4)^2*(nearCutoffBlocks n:ℝ)*(n:ℝ)^4 := by
  have hsum : ∑ t ∈ Icc 0 (cubicSampleEnd n), |nearCutoffCoefficient n t| ≤
      ∑ t ∈ nearCutoffSemiprimes n, log t := by
    calc
      _ ≤ ∑ t ∈ Icc 0 (cubicSampleEnd n), if t ∈ nearCutoffSemiprimes n then log t else 0 := by
        apply sum_le_sum
        intro t _
        by_cases ht : t ∈ nearCutoffSemiprimes n
        · rw [ite_eq_left ht,nearCutoffCoefficient_eq hn ht,abs_neg,abs_of_nonneg (log_natCast_nonneg t)]
        · simp [nearCutoffCoefficient,ht]
      _ ≤ _ := by
        rw [← sum_filter]
        apply sum_le_sum_of_subset_of_nonneg (fun _ h => (mem_filter.mp h).2)
          (fun t _ _ => log_natCast_nonneg t)
  have hw := (cubicWeightedResponse_abs hn _).trans (mul_le_mul_of_nonneg_left
    (hsum.trans (nearCutoff_log_sum hn)) (by norm_num : (0:ℝ)≤2))
  have hmain := mul_le_mul_of_nonneg_left hw (log_natCast_nonneg n)
  have hcount := mul_le_mul_of_nonneg_right (dyadic_reciprocal_upper (by omega : 0<n) (nearCutoffBlocks n))
    (by positivity : 0≤8*log 4*(n:ℝ)^4)
  linarith only [hmain,hcount]

theorem crossingTriples_disjoint_nearCutoff (n : ℕ) :
    Disjoint (crossingPrimeTriples n) (nearCutoffSemiprimes n) := by
  apply disjoint_left.mpr
  intro t ht hs
  obtain ⟨_,_,_,a,b,u,ha,_,_,_,hab,hbn,_,_,he⟩ := mem_filter.mp ht
  obtain ⟨_,p,r,hp,hr,hnp,_,hpr,he'⟩ := mem_filter.mp hs
  have hd : a ∣ p*r := by
    rw [← he',he]
    exact dvd_mul_of_dvd_left (dvd_mul_right a b) u
  rcases ha.dvd_mul.mp hd with h | h
  · have := (hp.dvd_iff_eq ha.ne_one).mp h
    omega
  · have := (hr.dvd_iff_eq ha.ne_one).mp h
    omega

/-- Erase both the positive crossing triples and the near-cutoff losses. -/
def cubicUnpairedCoefficient (n t : ℕ) : ℝ :=
  if t ∈ crossingPrimeTriples n ∨ t ∈ nearCutoffSemiprimes n then 0 else cubicCompensatedCoefficient n t

theorem cubicUnpairedCoefficient_eq_zero_of_semiprime {n p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hnp : n<p) (hpr : p≤r)
    (hpow : p^268435456 ≤ n^(268435456+1))
    (ht : p*r ∈ Ioc (3*n^3) (cubicSampleEnd n)) : cubicUnpairedCoefficient n (p*r) = 0 := by
  have h : p*r ∈ nearCutoffSemiprimes n := mem_filter.mpr ⟨ht,p,r,hp,hr,hnp,
    le_nearCutoff_of_pow_le (n := n) (p := p) hpow,hpr,rfl⟩
  exact ite_eq_left (Or.inr h)

theorem cubicUnpairedResponse_eq {n : ℕ} (hn : 64 ≤ n) :
    cubicWeightedResponse n (cubicUnpairedCoefficient n) + crossingTripleMass n +
      cubicWeightedResponse n (nearCutoffCoefficient n) =
      cubicWeightedResponse n (cubicCompensatedCoefficient n) := by
  have he : cubicUnpairedCoefficient n =
      cubicCompensatedCoefficient n - crossingTripleCoefficient n - nearCutoffCoefficient n := by
    funext t
    have hdis : t ∈ crossingPrimeTriples n → t ∉ nearCutoffSemiprimes n :=
      fun h => disjoint_left.mp (crossingTriples_disjoint_nearCutoff n) h
    by_cases hp : t ∈ crossingPrimeTriples n
    · simp [cubicUnpairedCoefficient,crossingTripleCoefficient,nearCutoffCoefficient,hp,hdis hp]
    · by_cases hs : t ∈ nearCutoffSemiprimes n <;>
        simp [cubicUnpairedCoefficient,crossingTripleCoefficient,nearCutoffCoefficient,hp,hs]
  rw [he,← cubicWeightedResponse_sub,← cubicWeightedResponse_sub,crossingTripleResponse_eq hn]
  ring

/-- The positive triple mass pays the full signed response of every upper
rough semiprime in the specified power range, with a quartic margin left. -/
theorem cubicUnpairedResponse_quartic_margin_sharp :
    ∃ N : ℕ, ∀ n ≥ N, cubicWeightedResponse n (cubicUnpairedCoefficient n) +
      (1/200000:ℝ)*(n:ℝ)^4 ≤ cubicWeightedResponse n (cubicCompensatedCoefficient n) := by
  obtain ⟨A,hA⟩ := crossingTripleMass_quartic
  have hlim : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨B,hB⟩ := eventually_atTop.mp (hlim.eventually_ge_atTop (268435456:ℝ))
  refine ⟨max 64 (max A B),fun n hn => ?_⟩
  have hn64 : 64 ≤ n := by omega
  have hlog := hB n (by omega)
  change 268435456 ≤ log (n:ℝ) at hlog
  have hpos : 0 < log (n:ℝ) := log_pos (by exact_mod_cast (show 1<n by omega))
  have hpow := log_le_log (by positivity : (0:ℝ) < 2^(Nat.log 2 n))
    (show (2:ℝ)^(Nat.log 2 n) ≤ n by exact_mod_cast Nat.pow_log_le_self 2 (by omega : n≠0))
  rw [log_pow] at hpow
  have hk := mul_le_mul_of_nonneg_left
    (show (1/2:ℝ) ≤ log 2 by linarith only [Real.log_two_gt_d9]) (Nat.cast_nonneg (Nat.log 2 n))
  have hj : (nearCutoffBlocks n:ℝ)*268435456 ≤ (Nat.log 2 n:ℕ)+ (268435456:ℝ) := by
    exact_mod_cast (show nearCutoffBlocks n*268435456 ≤ Nat.log 2 n+268435456 by
      dsimp [nearCutoffBlocks]; omega)
  have hsq : (log 4)^2 ≤ (3:ℝ)^2 := pow_le_pow_left₀ (by positivity)
    (by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]) 2
  have hstep := mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg (α := ℝ) (nearCutoffBlocks n))
  have hbudget : 16*(log 4)^2*(nearCutoffBlocks n:ℝ) ≤ ((3/327680:ℝ)-1/200000)*log n := by
    linarith only [hstep,hj,hk,hpow,hlog]
  have hnorm : |cubicWeightedResponse n (nearCutoffCoefficient n)| ≤ ((3/327680:ℝ)-1/200000)*(n:ℝ)^4 := by
    apply le_of_mul_le_mul_left (a := log (n:ℝ)) _ hpos
    have hscale := mul_le_mul_of_nonneg_right hbudget (pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 4)
    linarith only [nearCutoffResponse_log_bound (by omega : 8 ≤ n),hscale]
  linarith only [cubicUnpairedResponse_eq hn64,hA n (by omega), (abs_le.mp hnorm).1]

theorem cubicUnpairedResponse_quartic_margin :
    ∃ N : ℕ, ∀ n ≥ N, cubicWeightedResponse n (cubicUnpairedCoefficient n) +
      (3/655360:ℝ)*(n:ℝ)^4 ≤ cubicWeightedResponse n (cubicCompensatedCoefficient n) := by
  obtain ⟨N,hN⟩ := cubicUnpairedResponse_quartic_margin_sharp
  refine ⟨N,fun n hn => ?_⟩
  linarith only [hN n hn,pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 4]

/-- The exceptional mass with both priced families removed from the coefficient.
The net response of the two families is retained exactly before taking the positive part. -/
def cubicUnpairedMassOn (C : ℝ) (m b : ℕ) : ℝ := ∑ n ∈ Icc m b, max
  (cubicSmoothMoments n - cubicWeightedResponse n (cubicUnpairedCoefficient n) -
    crossingTripleMass n - cubicWeightedResponse n (nearCutoffCoefficient n) -
    movingSemiprimeSurplus n - C*(n:ℝ)^2*(1+log n)^2) 0 / (n:ℝ)^3

theorem cubicUnpairedMassOn_eq {m b : ℕ} (hm : 64 ≤ m) (C : ℝ) :
    cubicUnpairedMassOn C m b = cubicExceptionalMassOn C m b := by
  apply sum_congr rfl
  intro n hn
  rw [← cubicUnpairedResponse_eq (hm.trans (mem_Icc.mp hn).1)]
  ring_nf

theorem rh_of_cubicUnpairedMassOn_powerWindows {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, cubicUnpairedMassOn C m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply rh_of_cubicExceptionalMassOn_powerWindows hC
  intro α hα
  obtain ⟨δ,hδ,hδ1,hw⟩ := h α hα
  refine ⟨δ,hδ,hδ1,fun A => ?_⟩
  obtain ⟨m,hm,he⟩ := hw (max 64 A)
  exact ⟨m,by omega,(cubicUnpairedMassOn_eq (by omega : 64 ≤ m) C).ge.trans he⟩

/-- Conditional implication for the flat margin. CheckAlpogeCubicMainTerm
proves its premise false at exponent one half. The exact signed criterion above
retains the full contribution. -/
theorem rh_of_cubicUnpairedMargin_powerWindows {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ A : ℕ, ∃ m ≥ A,
      (∑ n ∈ Icc m (powerWindowEnd δ m), max
        (cubicSmoothMoments n - cubicWeightedResponse n (cubicUnpairedCoefficient n) -
          (3/655360:ℝ)*(n:ℝ)^4 - movingSemiprimeSurplus n - C*(n:ℝ)^2*(1+log n)^2) 0 / (n:ℝ)^3)
        ≤ (m:ℝ)^α) : RiemannHypothesis := by
  apply rh_of_cubicExceptionalMassOn_powerWindows hC
  obtain ⟨N,hN⟩ := cubicUnpairedResponse_quartic_margin
  intro α hα
  obtain ⟨δ,hδ,hδ1,hw⟩ := h α hα
  refine ⟨δ,hδ,hδ1,fun A => ?_⟩
  obtain ⟨m,hm,he⟩ := hw (max N A)
  refine ⟨m,by omega, le_trans ?_ he⟩
  apply sum_le_sum
  intro n hn
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply max_le_max_right
  linarith only [hN n (((le_max_left _ _).trans hm).trans (mem_Icc.mp hn).1)]

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.movingSemiprimeSurplus_cubic,
      ``RiemannGaussian.AlpogeMined.cubicCompensatedMassOn_le_reserve,
      ``RiemannGaussian.AlpogeMined.rh_of_cubicReserveMassOn_powerWindows,
      ``RiemannGaussian.AlpogeMined.crossingTripleResponse_eq,
      ``RiemannGaussian.AlpogeMined.crossingTripleMass_quartic,
      ``RiemannGaussian.AlpogeMined.nearCutoffResponse_log_bound,
      ``RiemannGaussian.AlpogeMined.cubicUnpairedCoefficient_eq_zero_of_semiprime,
      ``RiemannGaussian.AlpogeMined.cubicUnpairedResponse_eq,
      ``RiemannGaussian.AlpogeMined.cubicUnpairedResponse_quartic_margin,
      ``RiemannGaussian.AlpogeMined.cubicUnpairedMassOn_eq,
      ``RiemannGaussian.AlpogeMined.rh_of_cubicUnpairedMassOn_powerWindows,
      ``RiemannGaussian.AlpogeMined.rh_of_cubicUnpairedMargin_powerWindows] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
