/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszGlobalHeadCentralPayment
import RiemannGaussian.ZetaRieszAllowanceGrowth

/-!
# Test the residual semiprime atom price after the full head credit

Balanced semiprimes near total log 2N do not meet the head's owner mask.
Their positive atom price has rate 2u>1. This audit concerns ONLY the
post-cancellation norm allowance, not the actual signed prime sum.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszGlobalHeadPriceAudit
open ZetaRieszGlobalHeadCentralPayment ZetaRieszGlobalCentralPayment
open ZetaRieszGlobalBulkPayment ZetaRieszBalancedRadialPayment
open ZetaRieszAllowancePrimeBoxes ZetaRieszPrimeCountFrequency

/-- Two adjacent disjoint logarithmic prime intervals, with no phase
selection. They test an unsigned price, not signed carrier cancellation. -/
def balancedPairs (N : ℕ) : Finset (ℕ×ℕ) :=
  (logPrimes N 1).product (logPrimes ((N : ℝ)+1) 1)

/-- Distinct ordinary-prime products untouched by the high-owner head. -/
def balancedProducts (N : ℕ) : Finset ℕ :=
  (balancedPairs N).image (fun e => e.1*e.2)

private theorem balanced_pair_data {N p q : ℕ} (he : (p,q)∈balancedPairs N) :
    p.Prime ∧ q.Prime ∧ p<q ∧
      (N : ℝ)<log p ∧ log p≤(N : ℝ)+1 ∧
      (N : ℝ)+1<log q ∧ log q≤(N : ℝ)+2 := by
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp he
  have hpB := logPrimes_bounds hp
  have hqB := logPrimes_bounds hq
  exact ⟨hpB.1,hqB.1,logPrimes_order le_rfl hp hq,
    hpB.2.1,hpB.2.2,hqB.2.1,by linarith only [hqB.2.2]⟩

private theorem balanced_pair_largest {N p q : ℕ} (he : (p,q)∈balancedPairs N) :
    ZetaRieszPrimeEndpoint.largestPrime (p*q)=q := by
  obtain ⟨hp,hq,hpq,_⟩ := balanced_pair_data he
  rw [mul_comm]
  apply ZetaRieszPrimeIntervals.largestPrime_mul q p hq hp.ne_zero
  intro r hr
  rw [hp.primeFactors,Finset.mem_singleton] at hr
  subst r
  exact hpq

/-- Products have one incidence because the two prime intervals are ordered. -/
theorem balanced_pair_injective (N : ℕ) :
    Set.InjOn (fun e : ℕ×ℕ => e.1*e.2) (balancedPairs N) := by
  rintro ⟨p,q⟩ he ⟨p',q'⟩ hf h
  change p*q=p'*q' at h
  have hq : q=q' := by
    rw [← balanced_pair_largest he,← balanced_pair_largest hf,h]
  subst q'
  have hp : p=p' := Nat.eq_of_mul_eq_mul_right (balanced_pair_data he).2.1.pos h
  simp only [hp]

theorem balancedProducts_card (N : ℕ) :
    (balancedProducts N).card=(logPrimes N 1).card*(logPrimes ((N : ℝ)+1) 1).card := by
  rw [balancedProducts,Finset.card_image_of_injOn (balanced_pair_injective N)]
  simp only [balancedPairs,Finset.product_eq_sprod,Finset.card_product]

private theorem balanced_product_data {N n : ℕ} (hn : n∈balancedProducts N) :
    Squarefree n ∧ n.primeFactors.card=2 ∧
      2*(N : ℝ)+1<log n ∧ log n≤2*(N : ℝ)+3 ∧
      log (ZetaRieszPrimeEndpoint.largestPrime n)≤(N : ℝ)+2 := by
  obtain ⟨⟨p,q⟩,he,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp,hq,hpq,hpl,hpu,hql,hqu⟩ := balanced_pair_data he
  have hcop := hp.coprime_iff_not_dvd.mpr
    (fun h => hpq.ne ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))
  have hs := Nat.squarefree_mul_iff.mpr ⟨hcop,hp.squarefree,hq.squarefree⟩
  have ht : log (p*q : ℕ)=log p+log q := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  refine ⟨hs,?_,?_,?_,?_⟩
  · simp only [Nat.primeFactors_mul hp.ne_zero hq.ne_zero,
      hp.primeFactors,hq.primeFactors,Finset.union_singleton]
    rw [Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton] using hpq.ne.symm),
      Finset.card_singleton]
  · rw [ht]; linarith only [hpl,hql]
  · rw [ht]; linarith only [hpu,hqu]
  · rw [balanced_pair_largest he]
    exact hqu

/-- Every label is in the exact central semiprime boundary but outside
the literal original head. This uses its owner mask, not a limiting share. -/
theorem balancedProducts_subset_unmatched {u : ℝ} {N : ℕ} (hN : 65536≤N) :
    balancedProducts N⊆semiprimeLabels N\centralHeadLabels u N := by
  intro n hn
  obtain ⟨hs,hc,hlo,hhi,howner⟩ := balanced_product_data hn
  have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
  have hn0 : (0 : ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hs.ne_zero
  have hf : n∈fullLabels N := by
    apply Finset.mem_Ioc.mpr
    constructor
    · apply (Nat.floor_lt (exp_pos _).le).mpr
      rw [sub_zero]
      apply (exp_lt_exp.mpr (show (39/20 : ℝ)*N<log n by
        nlinarith only [hlo,hNr])).trans_eq (exp_log hn0)
    · apply Nat.le_floor
      rw [sub_zero,← exp_log hn0]
      apply exp_le_exp.mpr
      nlinarith only [hhi,hNr]
  have hsN : n∈semiprimeLabels N := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hf,?_,?_⟩,hs,hc⟩
    all_goals nlinarith only [hlo,hhi,hNr]
  refine Finset.mem_sdiff.mpr ⟨hsN,?_⟩
  intro hh
  obtain ⟨e,he,heq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hh).1
  have hd : e.1∈ZetaRieszSmallTagNativeFloor.owners u N :=
    (Finset.mem_sigma.mp he).1
  have ho := (ZetaRieszSmallTagNativeFloor.owners_data hd).2.2.1
  have hemax := largestPrime_label (by omega : 64≤N) he
  rw [heq] at hemax
  rw [hemax] at howner
  nlinarith only [ho,howner,hNr]

/-- At the actual moving length, these balanced semiprimes have a
coefficient of norm at least one. No phase or zero hypothesis is used. -/
theorem balanced_coefficient_lower {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N n : ℕ}
    (hN : 65536≤N) (hn : n∈balancedProducts N) :
    1≤‖completedCoefficient (SquarefreeVaughanLogSource.length u N) n‖ := by
  obtain ⟨⟨p,q⟩,he,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp,hq,hpq,hpl,hpu,hql,hqu⟩ := balanced_pair_data he
  have hs := (balanced_product_data (Finset.mem_image.mpr ⟨(p,q),he,rfl⟩)).1
  let L := SquarefreeVaughanLogSource.length u N
  have hL : 0<L := SquarefreeVaughanLogSource.length_pos u N
  have hLl := ZetaRieszPostHingeEnergy.length_ge_rational hN (by linarith : 0<u) hU
  have hLu := ZetaRieszSmallTagNativeFloor.length_upper hu (by omega : 2≤N)
  have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
  have ht : log (p*q : ℕ)=log p+log q := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  have hpp : log p≤L := by dsimp only [L]; nlinarith only [hLl,hpu,hNr]
  have hqp : log q≤L := by dsimp only [L]; nlinarith only [hLl,hqu,hNr]
  have hT : L≤log (p*q : ℕ) := by dsimp only [L]; rw [ht]; nlinarith only [hLu,hpl,hql,hNr]
  have hr : VaughanLogAverage.riesz L (p*q)=log (p*q : ℕ)-L := by
    rw [ZetaRieszSemiprimePrefixDecay.riesz_semiprime_eq_tent _ hp hq hpq.ne]
    unfold ZetaSquarefreeRieszWindows.primePairTent
    rw [max_eq_right hL.le,max_eq_right (sub_nonneg.mpr hpp),
      max_eq_right (sub_nonneg.mpr hqp),max_eq_left (by linarith only [hT,ht])]
    rw [ht]
    ring
  have hg : 1≤log (p*q : ℕ)-L := by
    dsimp only [L]
    rw [ht]
    nlinarith only [hLu,hpl,hql,hNr]
  simp only [completedCoefficient,if_pos hs,Complex.norm_real,Real.norm_eq_abs]
  change 1≤|-log (p*q : ℕ)*VaughanLogAverage.riesz L (p*q)/L|
  rw [hr,abs_div,abs_mul,abs_neg,abs_of_nonneg (log_natCast_nonneg _),
    abs_of_nonneg (by linarith only [hg] : 0≤log (p*q : ℕ)-L),abs_of_pos hL]
  apply (le_div_iff₀ hL).mpr
  nlinarith only [hT,hg,hL]

/-- A fixed-width PNT lower bound with an explicit scalar. This is a
LOWER bound for a diagnostic positive price, not a transport estimate or
an RH-strength prime-cancellation hypothesis. Its start is unevaluated. -/
theorem eventually_explicit_prime_box_count :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℝ, (N : ℝ)≤a → a≤(N : ℝ)+1 →
      exp N/(6*((N : ℝ)+1))≤((logPrimes a 1).card : ℝ) := by
  have hd : (1/2 : ℝ)<exp 1-1 := by
    have h := Real.add_one_lt_exp (show (1 : ℝ)≠0 by norm_num)
    linarith only [h]
  have hm := (PrimeWindow.theta_interval_div_tendsto (exp_pos (1 : ℝ))).eventually_const_lt hd
  obtain ⟨X,hX⟩ := eventually_atTop.mp hm
  have hx : Tendsto (fun N : ℕ => exp (N : ℝ)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hx.eventually (eventually_ge_atTop X)] with N hN a ha hau
  have he : exp N≤exp a := exp_le_exp.mpr ha
  have hl := (lt_div_iff₀ (exp_pos a)).mp (hX (exp a) (hN.trans he))
  rw [← PrimeWindow.sum_log_primesInWindow (exp_pos a).le
    (one_le_exp_iff.mpr (by norm_num : (0 : ℝ)≤1))] at hl
  have hs : (∑ p∈logPrimes a 1,log p)≤((logPrimes a 1).card : ℝ)*(3*((N : ℝ)+1)) := by
    calc
      _ ≤ ∑ _p∈logPrimes a 1,3*((N : ℝ)+1) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpL := (logPrimes_bounds hp).2.2
        nlinarith only [hpL,hau,Nat.cast_nonneg (α:=ℝ) N]
      _ = _ := by simp
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<6*((N : ℝ)+1))).mpr
  have he' := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ)≤1/2)
  dsimp only [logPrimes] at hs ⊢
  nlinarith only [he',hl,hs]

/-- The two disjoint prime boxes supply exponentially many DISTINCT
unmatched labels, with the exact factorial scale still to be applied. -/
theorem eventually_balanced_product_count :
    ∀ᶠ N : ℕ in atTop,
      exp (2*(N : ℝ))/(36*((N : ℝ)+1)^2)≤((balancedProducts N).card : ℝ) := by
  filter_upwards [eventually_explicit_prime_box_count] with N hN
  have hp := hN N le_rfl (by linarith : (N : ℝ)≤(N : ℝ)+1)
  have hq := hN ((N : ℝ)+1) (by linarith : (N : ℝ)≤(N : ℝ)+1) le_rfl
  have h0 : 0≤exp N/(6*((N : ℝ)+1)) := by positivity
  have hm := mul_le_mul hp hq h0 (Nat.cast_nonneg _)
  rw [← pow_two,div_pow,← exp_nat_mul] at hm
  rw [balancedProducts_card,Nat.cast_mul]
  norm_num only [Nat.cast_ofNat,mul_pow] at hm
  exact hm

/-- Every unmatched atom has its full factorial/source weight. Norms
here test an unsigned allowance ONLY; the actual phase is not bounded
by a fixed positive charge in the floor. -/
theorem balanced_atom_lower {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N n : ℕ}
    (hN : 65536≤N) (hn : n∈balancedProducts N) (y : ℝ) :
    u^(N+1)*(exp (-(3/2 : ℝ)*(2*N+3))*(2*N)^N/(N.factorial : ℝ))≤
      ‖(u : ℂ)^(N+1)*completedCoefficient (SquarefreeVaughanLogSource.length u N) n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := by
  obtain ⟨_,_,hlo,hhi,_⟩ := balanced_product_data hn
  have hu0 : 0≤u := by linarith only [hu]
  have hc := balanced_coefficient_lower hu hU hN hn
  have hk : exp (-(3/2 : ℝ)*(2*N+3))*(2*N)^N/(N.factorial : ℝ)≤
      ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := by
    rw [norm_zetaPrimeLogKernel]
    have hsre : ((3/2 : ℂ)+Complex.I*y).re=3/2 := by simp
    simp only [zetaPrimeExpWeight,hsre]
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤2*N)
      (by linarith only [hlo] : 2*(N : ℝ)≤log n) N
    have hex := exp_le_exp.mpr (show -(3/2 : ℝ)*(2*N+3)≤-(3/2 : ℝ)*log n by
      nlinarith only [hhi])
    have hb := mul_le_mul hex hpow (by positivity) (exp_pos _).le
    have hd := div_le_div_of_nonneg_right hb (Nat.cast_nonneg (α:=ℝ) N.factorial)
    exact hd.trans_eq (by ring)
  rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu0]
  have hck : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖≤
      ‖completedCoefficient (SquarefreeVaughanLogSource.length u N) n‖*
        ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ :=
    le_mul_of_one_le_left (norm_nonneg _) hc
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hk.trans hck) (pow_nonneg hu0 _)

/-- Every untouched balanced label remains in the post-cancellation
central price. Other head labels can spend only their OWN coefficient. -/
theorem balanced_mass_le_central_price {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) :
    (∑ n∈balancedProducts N,
      ‖(u : ℂ)^(N+1)*completedCoefficient (SquarefreeVaughanLogSource.length u N) n*
        zetaPrimeLogKernel N (3/2+Complex.I*0) n‖)≤
      semiprimePrice u N-centralHeadMass u N := by
  let S := semiprimeLabels N
  let H := centralHeadLabels u N
  let a := fun n => ‖(u : ℂ)^(N+1)*
    completedCoefficient (SquarefreeVaughanLogSource.length u N) n*
      zetaPrimeLogKernel N (3/2+Complex.I*0) n‖
  let b := fun n => ‖(u : ℂ)^(N+1)*headCoefficient u N n*
    zetaPrimeLogKernel N (3/2+Complex.I*0) n‖
  have hHS : H⊆S := centralHeadLabels_subset_semiprime (by omega : 64≤N)
  have hba : ∑ n∈H,b n≤∑ n∈H,a n := by
    apply Finset.sum_le_sum
    intro n hn
    have hh := headCoefficient_bounds hu hU hN (Finset.mem_filter.mp hn).1
    have him : (headCoefficient u N n).im=0 := by
      simp only [headCoefficient,Complex.ofReal_im]
    have hr : ‖headCoefficient u N n‖≤(headCoefficient u N n).re := by
      have h := Complex.norm_le_abs_re_add_abs_im (headCoefficient u N n)
      simpa only [him,abs_zero,add_zero,abs_of_nonneg hh.1] using h
    have hc : ‖headCoefficient u N n‖≤
        ‖completedCoefficient (SquarefreeVaughanLogSource.length u N) n‖ := by
      apply (hr.trans hh.2).trans
      simpa only [Complex.neg_re,norm_neg] using Complex.re_le_norm
        (-completedCoefficient (SquarefreeVaughanLogSource.length u N) n)
    dsimp only [a,b]
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (norm_nonneg _)) (norm_nonneg _)
  have ht : ∑ n∈balancedProducts N,a n≤∑ n∈S\H,a n :=
    Finset.sum_le_sum_of_subset_of_nonneg (balancedProducts_subset_unmatched hN)
      (fun _ _ _ => norm_nonneg _)
  have he := Finset.sum_sdiff hHS (f:=a)
  change (∑ n∈balancedProducts N,a n)≤(∑ n∈S,a n)-(∑ n∈H,b n)
  linarith only [ht,hba,he]

/-- The EXACT positive right side of the already proved full
semiprime/head bound. This is a diagnostic allowance, never a new carrier. -/
def fullJoinedAtomPrice (u : ℝ) (N : ℕ) : ℝ :=
  semiprimePrice u N-ZetaRieszRoughPrimePairCancellation.nativeHead u 0 N+
    2*(ZetaRieszLargeOrderCore.rate^N*radialConstant)

/-- The explicit constant in the unmatched balanced-pair lower envelope. -/
def growthConstant (u : ℝ) : ℝ := u*exp (-(9/2 : ℝ))/216

/-- The funded radial credit cannot remove any untouched balanced
semiprime. The entire old head and its actual zero-height mass remain. -/
theorem central_price_le_full_price {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) :
    semiprimePrice u N-centralHeadMass u N≤fullJoinedAtomPrice u N := by
  have hm := (abs_le.mp (fullHead_sub_centralMass_bound hu hU hN)).2
  have he : 0≤ZetaRieszLargeOrderCore.rate^N*radialConstant :=
    mul_nonneg (pow_nonneg ZetaRieszLargeOrderCore.rate_bounds.1.le _) radialConstant_nonneg
  unfold fullJoinedAtomPrice
  linarith only [hm,he]

/-- Exact factorial normalization of the two fixed-width prime boxes.
The native coefficient is not replaced by a continuum approximation. -/
theorem balanced_box_scalar_lower {u : ℝ} (hu : 0≤u) {N : ℕ} (hN : 1≤N) :
    growthConstant u*(2*u)^N/((N : ℝ)+1)^3≤
      (exp (2*(N : ℝ))/(36*((N : ℝ)+1)^2))*
        (u^(N+1)*(exp (-(3/2 : ℝ)*(2*N+3))*(2*N)^N/N.factorial)) := by
  have hs := PrimeWindow.local_monomial_lower hN (by norm_num : (0 : ℝ)≤2)
  norm_num [PrimeWindow.localGrowth] at hs
  rw [show -(2*(N : ℝ))/2=-(N : ℝ) by ring] at hs
  have hs' : (2 : ℝ)^N/(6*((N : ℝ)+1))≤
      exp (-(N : ℝ))*(2*N)^N/N.factorial := by
    apply le_trans _ hs
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have he : exp (2*(N : ℝ))*exp (-(3/2 : ℝ)*(2*N+3))=
      exp (-(9/2 : ℝ))*exp (-(N : ℝ)) := by
    rw [←exp_add,←exp_add]
    congr 1
    ring
  let k := u^(N+1)*exp (-(9/2 : ℝ))/(36*((N : ℝ)+1)^2)
  have hk : 0≤k := by dsimp only [k]; positivity
  calc
    _ = k*((2 : ℝ)^N/(6*((N : ℝ)+1))) := by
      dsimp only [growthConstant,k]
      rw [mul_pow,pow_succ]
      field_simp
      ring
    _ ≤ k*(exp (-(N : ℝ))*(2*N)^N/N.factorial) :=
      mul_le_mul_of_nonneg_left hs' hk
    _ = _ := by
      dsimp only [k]
      calc
        _ = u^(N+1)/(36*((N : ℝ)+1)^2)*
          (exp (-(9/2 : ℝ))*exp (-(N : ℝ)))*((2*N)^N/N.factorial) := by ring
        _ = _ := by rw [←he]; ring

/-- Even after the ENTIRE global head credit and funded radial errors,
the remaining positive allowance has an explicit exponential lower
envelope. This statement says nothing about the signed prime sum. -/
theorem eventually_full_price_growth {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop,
      growthConstant u*(2*u)^N/((N : ℝ)+1)^3≤fullJoinedAtomPrice u N := by
  filter_upwards [eventually_balanced_product_count,eventually_ge_atTop (65536 : ℕ)]
    with N hc hN
  let M := u^(N+1)*(exp (-(3/2 : ℝ)*(2*N+3))*(2*N)^N/N.factorial)
  have hu0 : 0≤u := by linarith only [hu]
  have hm : 0≤M := by dsimp only [M]; positivity
  calc
    _ ≤ (exp (2*(N : ℝ))/(36*((N : ℝ)+1)^2))*M :=
      balanced_box_scalar_lower hu0 (by omega : 1≤N)
    _ ≤ ((balancedProducts N).card : ℝ)*M := mul_le_mul_of_nonneg_right hc hm
    _ = ∑ _n∈balancedProducts N,M := by simp
    _ ≤ ∑ n∈balancedProducts N,
        ‖(u : ℂ)^(N+1)*completedCoefficient (SquarefreeVaughanLogSource.length u N) n*
          zetaPrimeLogKernel N (3/2+Complex.I*0) n‖ := by
      apply Finset.sum_le_sum
      intro n hn
      exact balanced_atom_lower (by linarith : 1/2≤u) hU hN hn 0
    _ ≤ semiprimePrice u N-centralHeadMass u N :=
      balanced_mass_le_central_price (by linarith : 1/2≤u) hU hN
    _ ≤ fullJoinedAtomPrice u N := central_price_le_full_price (by linarith : 1/2≤u) hU hN

/-- Any fixed radius strictly above one half makes this positive
post-cancellation price diverge. Cancellation across DIFFERENT labels
must remain signed; the actual joined sum is not claimed to diverge. -/
theorem fullJoinedAtomPrice_tendsto_atTop {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fullJoinedAtomPrice u) atTop atTop := by
  have hk : 0<growthConstant u := by unfold growthConstant; positivity
  have ht := ZetaRieszAllowanceGrowth.geometric_over_successor_four_tendsto
    (show 1<2*u by linarith only [hu])
  have hkht : Tendsto (fun N : ℕ => growthConstant u*((2*u)^N/((N : ℝ)+1)^4))
      atTop atTop := ht.const_mul_atTop hk
  refine tendsto_atTop_mono' atTop ?_ hkht
  filter_upwards [eventually_full_price_growth hu hU] with N hN
  apply le_trans _ hN
  rw [←mul_div_assoc]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hn : 1≤(N : ℝ)+1 := by linarith only [Nat.cast_nonneg (α:=ℝ) N]
  simpa only [pow_succ] using le_mul_of_one_le_right (pow_nonneg (by positivity) 3) hn

/-- The obstruction holds on the EXACT native dyadic moment sequence,
not just an unrelated continuous or factorial model. -/
theorem native_full_price_tendsto_atTop {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun j => fullJoinedAtomPrice u (dyadicMomentOrder j)) atTop atTop :=
  (fullJoinedAtomPrice_tendsto_atTop hu hU).comp tendsto_dyadicMomentOrder

/-- No cofinal subsequence of this positive allowance can meet ANY fixed
ceiling, including 399/5000. This is not a no-go for a signed floor. -/
theorem not_frequently_native_full_price_le {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (M : ℝ) :
    ¬ ∃ᶠ j in atTop,fullJoinedAtomPrice u (dyadicMomentOrder j)≤M := by
  intro h
  obtain ⟨j,hle,hgt⟩ := (h.and_eventually
    ((native_full_price_tendsto_atTop hu hU).eventually_gt_atTop M)).exists
  exact hgt.not_ge hle

end RiemannGaussian.ZetaRieszGlobalHeadPriceAudit
