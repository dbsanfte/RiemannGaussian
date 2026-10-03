/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLowCountSignedBoundary
import RiemannGaussian.ZetaRieszGlobalHeadPriceAudit
import RiemannGaussian.SuzukiLogarithmicConvolution
import RiemannGaussian.ZetaPrimePairDiagonal

/-!
# Test Selberg completion against the literal joined low-count boundary

Selberg's coefficient matches the ordinary-prime coefficient, but not
the balanced prime-pair coefficient. The mismatch remains on complete
interior phase periods, with the actual moving length and every original
head/correction mask. Its absolute factorial price diverges at source
scale. This rules out ONLY completion followed by an absolute remainder
payment; it does not bound or disprove cancellation in the signed main.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszLowCountSelbergAudit
open ZetaRieszLowCountSignedBoundary ZetaRieszGlobalHeadPriceAudit
open ZetaRieszGlobalBulkPayment ZetaRieszGlobalCentralPayment
open ZetaRieszGlobalHeadCentralPayment ZetaRieszGlobalPeriodEdgePayment
open ZetaRieszAllowancePrimeBoxes ZetaRieszPrimeEndpoint

/-- The normalized classical second logarithmic convolution, without
discarding its ordered prime-pair contribution. -/
def selbergCoefficient (n : ℕ) : ℂ :=
  ((-(ArithmeticFunction.vonMangoldt n*log n+zetaPrimePairArithmetic n)/log n : ℝ) : ℂ)

theorem selbergCoefficient_eq_moebius (n : ℕ) :
    selbergCoefficient n=
      ((-(∑ d∈n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius d.1 : ℝ)*(log d.2)^2)/log n : ℝ) : ℂ) := by
  rw [selbergCoefficient,sum_moebius_log_square_eq_vonMangoldt_log_add_pair]

theorem selbergCoefficient_prime {p : ℕ} (hp : p.Prime) :
    selbergCoefficient p=(-(log p : ℂ)) := by
  have hl : log (p : ℝ)≠0 := (log_pos (by exact_mod_cast hp.two_le)).ne'
  rw [selbergCoefficient,zetaPrimePairArithmetic_prime hp,
    ArithmeticFunction.vonMangoldt_apply_prime hp,add_zero]
  push_cast
  field_simp

private theorem pair_divisors {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (p*q).divisors={1,p,q,p*q} := by
  rw [Nat.divisors_mul,hp.divisors,hq.divisors]
  ext d
  simp only [Finset.mul_def,Finset.mem_image,Finset.mem_product,Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨a,b⟩,⟨(rfl | rfl),(rfl | rfl)⟩,rfl⟩ <;> simp
  · rintro (hd | hd | hd | hd)
    · exact ⟨(1,1),⟨Or.inl rfl,Or.inl rfl⟩,by simp [hd]⟩
    · exact ⟨(p,1),⟨Or.inr rfl,Or.inl rfl⟩,by simp [hd]⟩
    · exact ⟨(1,q),⟨Or.inl rfl,Or.inr rfl⟩,by simp [hd]⟩
    · exact ⟨(p,q),⟨Or.inr rfl,Or.inr rfl⟩,hd.symm⟩

theorem selbergCoefficient_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p<q) :
    selbergCoefficient (p*q)=((-2*log p*log q/log (p*q : ℕ) : ℝ) : ℂ) := by
  have hcop := hp.coprime_iff_not_dvd.mpr
    (fun h => hpq.ne ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))
  have hs := Nat.squarefree_mul_iff.mpr ⟨hcop,hp.squarefree,hq.squarefree⟩
  have hc : (p*q).primeFactors.card=2 := by
    simp only [Nat.primeFactors_mul hp.ne_zero hq.ne_zero,
      hp.primeFactors,hq.primeFactors,Finset.union_singleton]
    rw [Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton] using hpq.ne.symm),
      Finset.card_singleton]
  have hv := ZetaRieszSignedConvolution.vonMangoldt_zero_of_squarefree_count hs (by omega)
  have ht : p*q≠1 := by nlinarith only [hp.two_le,hq.two_le]
  have hpm : p≠p*q := by nlinarith only [hp.pos,hq.two_le]
  have hqm : q≠p*q := by nlinarith only [hq.pos,hp.two_le]
  have hpair : zetaPrimePairArithmetic (p*q)=2*log p*log q := by
    rw [zetaPrimePairArithmetic,ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b =>
        ArithmeticFunction.vonMangoldt a*ArithmeticFunction.vonMangoldt b),
      pair_divisors hp hq]
    rw [Finset.sum_insert (by simp [hp.ne_one.symm,hq.ne_one.symm,ht.symm]),
      Finset.sum_insert (by simp [hpq.ne,hpm]),
      Finset.sum_insert (by simp [hqm]),Finset.sum_singleton]
    simp only [ArithmeticFunction.vonMangoldt_apply_one,zero_mul,zero_add,hv,
      Nat.mul_div_right _ hp.pos,Nat.mul_div_left _ hq.pos,
      ArithmeticFunction.vonMangoldt_apply_prime hp,
      ArithmeticFunction.vonMangoldt_apply_prime hq]
    ring
  rw [selbergCoefficient,hv,hpair]
  push_cast
  ring

/-- Exact difference from Selberg, with all four literal masks still
inside `joinedCoefficient`. This is a diagnostic, not a new carrier. -/
def selbergDefect (u : ℝ) (N n : ℕ) : ℂ :=
  joinedCoefficient u N n-selbergCoefficient n

/-- Selberg agrees EXACTLY on the ordinary-prime part of the current
boundary. Thus the remaining defect is genuinely a prime-pair issue. -/
theorem selbergDefect_prime_eq_zero {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N p : ℕ}
    (hN : 65536≤N) (hpN : p∈primeLabels N) : selbergDefect u N p=0 := by
  have hp := (Finset.mem_filter.mp hpN).2
  have hc : p∉correctionLabels u N := fun h => (correction_not_prime hu hU hN h) hp
  have hh : p∉headLabels u N := fun h => hc (headLabels_subset_correction u N h)
  have hcentral := (Finset.mem_filter.mp hpN).1
  have hl := (Finset.mem_filter.mp hcentral).2.1
  have hLu := ZetaRieszSmallTagNativeFloor.length_upper hu (by omega : 2≤N)
  have hN0 : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hLp : SquarefreeVaughanLogSource.length u N≤log p := by
    nlinarith only [hLu,hl,hN0]
  have hL := SquarefreeVaughanLogSource.length_pos u N
  have hr : VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) p=
      SquarefreeVaughanLogSource.length u N := by
    simp [VaughanLogAverage.riesz,hp.divisors,hp.ne_one.symm,
      ArithmeticFunction.moebius_apply_prime hp,
      max_eq_right hL.le,max_eq_left (by linarith only [hLp] :
        SquarefreeVaughanLogSource.length u N-log p≤0)]
  rw [selbergDefect,joinedCoefficient,
    if_pos (Finset.mem_union.mpr (Or.inl hpN)),if_neg hh,if_neg hc,
    add_zero,sub_zero,selbergCoefficient_prime hp]
  simp only [completedCoefficient,if_pos hp.squarefree,hr]
  have hLc : (SquarefreeVaughanLogSource.length u N : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr hL.ne'
  push_cast
  field_simp [hLc]
  ring

private theorem balanced_pair_data {N p q : ℕ} (he : (p,q)∈balancedPairs N) :
    p.Prime ∧ q.Prime ∧ p<q ∧
      (N : ℝ)<log p ∧ log p≤(N : ℝ)+1 ∧
      (N : ℝ)+1<log q ∧ log q≤(N : ℝ)+2 := by
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp he
  have hpB := logPrimes_bounds hp
  have hqB := logPrimes_bounds hq
  exact ⟨hpB.1,hqB.1,logPrimes_order le_rfl hp hq,
    hpB.2.1,hpB.2.2,hqB.2.1,by linarith only [hqB.2.2]⟩

private theorem balanced_largest {N p q : ℕ} (he : (p,q)∈balancedPairs N) :
    largestPrime (p*q)=q := by
  obtain ⟨hp,hq,hpq,_⟩ := balanced_pair_data he
  rw [mul_comm]
  apply ZetaRieszPrimeIntervals.largestPrime_mul q p hq hp.ne_zero
  intro r hr
  rw [hp.primeFactors,Finset.mem_singleton] at hr
  subst r
  exact hpq

/-- Balanced pairs fail the NEW unallocated correction's owner mask,
not just the older allocated head. No physical prime is deleted. -/
theorem balanced_not_correction {u : ℝ} {N n : ℕ} (hN : 65536≤N)
    (hn : n∈balancedProducts N) : n∉correctionLabels u N := by
  obtain ⟨⟨p,q⟩,he,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨_hp,_hq,_hpq,_hpl,_hpu,_hql,hqu⟩ := balanced_pair_data he
  have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
  intro hc
  obtain ⟨e,he',heq⟩ := Finset.mem_image.mp hc
  have ho := ZetaRieszUnallocatedOwnerPayment.highOwner_data (Finset.mem_sigma.mp he').1
  have hf : e.1=q ∨ e.1=p := by
    have hd : e.1∣p*q := by rw [←heq]; exact dvd_mul_right _ _
    rcases ho.1.dvd_mul.mp hd with hp | hq
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq ho.1 (balanced_pair_data he).1).mp hp)
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq ho.1 (balanced_pair_data he).2.1).mp hq)
  rcases hf with hf | hf
  · rw [hf] at ho
    nlinarith only [ho.2.2.1,hqu,hNr]
  · rw [hf] at ho
    nlinarith only [ho.2.2.1,(balanced_pair_data he).2.2.2.2.1,hNr]

theorem balanced_joined_eq_completed {u : ℝ} {N n : ℕ} (hN : 65536≤N)
    (hn : n∈balancedProducts N) :
    joinedCoefficient u N n=completedCoefficient (SquarefreeVaughanLogSource.length u N) n := by
  have hs := (Finset.mem_sdiff.mp (balancedProducts_subset_unmatched (u:=u) hN hn)).1
  have hc := balanced_not_correction (u:=u) hN hn
  have hh : n∉headLabels u N := fun h => hc (headLabels_subset_correction u N h)
  simp only [joinedCoefficient,if_pos (Finset.mem_union.mpr (Or.inr hs)),
    if_neg hh,if_neg hc,add_zero,sub_zero]

/-- On balanced pairs the residual is a BULK coefficient, not an
endpoint term: it is at least N/20 at the actual moving length. -/
theorem balanced_defect_lower {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N n : ℕ}
    (hN : 65536≤N) (hn : n∈balancedProducts N) :
    (N : ℝ)/20≤(selbergDefect u N n).re := by
  obtain ⟨⟨p,q⟩,he,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp,hq,hpq,hpl,hpu,hql,hqu⟩ := balanced_pair_data he
  have hn : p*q∈balancedProducts N := Finset.mem_image.mpr ⟨(p,q),he,rfl⟩
  have hs := (Finset.mem_filter.mp (Finset.mem_sdiff.mp
    (balancedProducts_subset_unmatched (u:=u) hN hn)).1).2.1
  let L := SquarefreeVaughanLogSource.length u N
  let T := log (p*q : ℕ)
  have hL : 0<L := SquarefreeVaughanLogSource.length_pos u N
  have hLl := ZetaRieszPostHingeEnergy.length_ge_rational hN (by linarith : 0<u) hU
  have hLu := ZetaRieszSmallTagNativeFloor.length_upper hu (by omega : 2≤N)
  have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
  have ht : T=log p+log q := by
    dsimp only [T]
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  have hpp : log p≤L := by dsimp only [L]; nlinarith only [hLl,hpu,hNr]
  have hqp : log q≤L := by dsimp only [L]; nlinarith only [hLl,hqu,hNr]
  have hT : L≤T := by dsimp only [L]; rw [ht]; nlinarith only [hLu,hpl,hql,hNr]
  have hr : VaughanLogAverage.riesz L (p*q)=T-L := by
    rw [ZetaRieszSemiprimePrefixDecay.riesz_semiprime_eq_tent _ hp hq hpq.ne]
    unfold ZetaSquarefreeRieszWindows.primePairTent
    rw [max_eq_right hL.le,max_eq_right (sub_nonneg.mpr hpp),
      max_eq_right (sub_nonneg.mpr hqp),max_eq_left (by linarith only [hT,ht])]
    rw [ht]
    ring
  have hTl : 2*(N : ℝ)≤T := by linarith only [ht,hpl,hql]
  have hTu : T≤2*(N : ℝ)+3 := by linarith only [ht,hpu,hqu]
  have hTp : 0<T := by linarith only [hTl,hNr]
  have hprod : (N : ℝ)^2≤log p*log q := by
    have hh := mul_le_mul (le_of_lt hpl) (by linarith only [hql] : (N : ℝ)≤log q)
      (Nat.cast_nonneg (α:=ℝ) N) (log_natCast_nonneg p)
    simpa only [pow_two] using hh
  have hpterm : (49/50 : ℝ)*N≤2*log p*log q/T := by
    apply (le_div_iff₀ hTp).mpr
    nlinarith only [hprod,hTu,hNr]
  have hLterm : T^2/L≤(293/100 : ℝ)*N := by
    apply (div_le_iff₀ hL).mpr
    have hsq : T^2≤(2*(N : ℝ)+3)^2 :=
      pow_le_pow_left₀ hTp.le hTu 2
    change (277/200 : ℝ)*N≤L at hLl
    nlinarith only [hsq,hLl,hNr]
  rw [selbergDefect,balanced_joined_eq_completed hN hn,selbergCoefficient_pair hp hq hpq]
  simp only [completedCoefficient,if_pos hs,Complex.sub_re,Complex.ofReal_re]
  rw [hr]
  change (N : ℝ)/20≤ -T*(T-L)/L-(-2*log p*log q/T)
  have he : -T*(T-L)/L-(-2*log p*log q/T)=T-T^2/L+2*log p*log q/T := by
    field_simp
    ring
  rw [he]
  linarith only [hTl,hpterm,hLterm]

/-- These are COMPLETE interior periods of the current joined support.
The mismatch cannot be moved into an already paid endpoint strip. -/
theorem balancedProducts_subset_periods {u : ℝ} {N : ℕ} (hN : 65536≤N)
    {y : ℝ} (hy : 54≤|y|) :
    balancedProducts N⊆completePeriodLabels (joinedLabels u N) N y := by
  intro n hn
  have hs := (Finset.mem_sdiff.mp (balancedProducts_subset_unmatched (u:=u) hN hn)).1
  have hj : n∈joinedLabels u N :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hs)))
  obtain ⟨⟨p,q⟩,he,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp,hq,_hpq,hpl,hpu,hql,hqu⟩ := balanced_pair_data he
  have ht : log (p*q : ℕ)=log p+log q := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
  apply interiorLabels_subset_completePeriods _ _ hy
  apply Finset.mem_filter.mpr
  refine ⟨hj,?_,?_⟩ <;> rw [ht]
  · nlinarith only [hpl,hql,hNr]
  · nlinarith only [hpu,hqu,hNr]

private theorem balanced_defect_atom_lower {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N n : ℕ}
    (hN : 65536≤N) (hn : n∈balancedProducts N) (y : ℝ) :
    u^(N+1)*(exp (-(3/2 : ℝ)*(2*N+3))*(2*N)^N/(N.factorial : ℝ))≤
      ‖(u : ℂ)^(N+1)*selbergDefect u N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := by
  have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
  have hc : 1≤‖selbergDefect u N n‖ :=
    (show 1≤(N : ℝ)/20 by linarith only [hNr]).trans
      ((balanced_defect_lower hu hU hN hn).trans (Complex.re_le_norm _))
  obtain ⟨⟨p,q⟩,he,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp,hq,_hpq,hpl,hpu,hql,hqu⟩ := balanced_pair_data he
  have ht : log (p*q : ℕ)=log p+log q := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  have hlo : 2*(N : ℝ)≤log (p*q : ℕ) := by linarith only [ht,hpl,hql]
  have hhi : log (p*q : ℕ)≤2*(N : ℝ)+3 := by linarith only [ht,hpu,hqu]
  have hu0 : 0≤u := by linarith only [hu]
  have hk : exp (-(3/2 : ℝ)*(2*N+3))*(2*N)^N/(N.factorial : ℝ)≤
      ‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*q)‖ := by
    rw [norm_zetaPrimeLogKernel]
    have hsre : ((3/2 : ℂ)+Complex.I*y).re=3/2 := by simp
    simp only [zetaPrimeExpWeight,hsre]
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤2*N) hlo N
    have hex := exp_le_exp.mpr (show -(3/2 : ℝ)*(2*N+3)≤-(3/2 : ℝ)*log (p*q : ℕ) by
      nlinarith only [hhi])
    have hb := mul_le_mul hex hpow (by positivity) (exp_pos _).le
    exact (div_le_div_of_nonneg_right hb (Nat.cast_nonneg (α:=ℝ) N.factorial)).trans_eq (by ring)
  rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu0]
  have hck : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*q)‖≤
      ‖selbergDefect u N (p*q)‖*‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*q)‖ :=
    le_mul_of_one_le_left (norm_nonneg _) hc
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hk.trans hck) (pow_nonneg hu0 _)

/-- Only a diagnostic for the proposed ABSOLUTE Selberg completion
remainder. No such allowance is inserted into the signed floor ledger. -/
def selbergDefectPrice (u y : ℝ) (N : ℕ) : ℝ :=
  ∑ n∈completePeriodLabels (joinedLabels u N) N y,
    ‖(u : ℂ)^(N+1)*selbergDefect u N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖

/-- Even after joining prime/head/correction coefficients, the Selberg
remainder price has rate 2u>1 on the retained complete periods. -/
theorem eventually_selberg_defect_price_growth {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ N : ℕ in atTop,
      growthConstant u*(2*u)^N/((N : ℝ)+1)^3 ≤ selbergDefectPrice u y N := by
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
        ‖(u : ℂ)^(N+1)*selbergDefect u N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := by
      apply Finset.sum_le_sum
      intro n hn
      exact balanced_defect_atom_lower (by linarith : 1/2≤u) hU hN hn y
    _ ≤ selbergDefectPrice u y N :=
      Finset.sum_le_sum_of_subset_of_nonneg (balancedProducts_subset_periods hN hy)
        (fun _ _ _ => norm_nonneg _)

theorem selbergDefectPrice_tendsto_atTop {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (selbergDefectPrice u y) atTop atTop := by
  have hk : 0<growthConstant u := by unfold growthConstant; positivity
  have ht := ZetaRieszAllowanceGrowth.geometric_over_successor_four_tendsto
    (show 1<2*u by linarith only [hu])
  have hkht : Tendsto (fun N : ℕ => growthConstant u*((2*u)^N/((N : ℝ)+1)^4))
      atTop atTop := ht.const_mul_atTop hk
  refine tendsto_atTop_mono' atTop ?_ hkht
  filter_upwards [eventually_selberg_defect_price_growth hu hU hy] with N hN
  apply le_trans _ hN
  rw [←mul_div_assoc]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hn : 1≤(N : ℝ)+1 := by linarith only [Nat.cast_nonneg (α:=ℝ) N]
  simpa only [pow_succ] using le_mul_of_one_le_right (pow_nonneg (by positivity) 3) hn

/-- The obstruction applies to the EXACT native sequence and permits
no cofinal absolute-defect bound at any fixed target. Signed bounds are
not excluded by this theorem. -/
theorem not_frequently_native_selberg_defect_price_le {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) (M : ℝ) :
    ¬ ∃ᶠ j in atTop,selbergDefectPrice u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)≤M := by
  intro h
  have ht := (selbergDefectPrice_tendsto_atTop hu hU hy).comp
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder
  obtain ⟨j,hle,hgt⟩ := (h.and_eventually (ht.eventually_gt_atTop M)).exists
  exact hgt.not_ge hle

end RiemannGaussian.ZetaRieszLowCountSelbergAudit
