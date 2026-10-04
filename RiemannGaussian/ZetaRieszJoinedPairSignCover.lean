/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPairPrimePowerPayment

/-!
# Signed credits for the whole joined prime-pair profile

Both factorial prefixes and the full Selberg subtraction are joined before
their sign is tested. Two broad share regions have opposite coefficient
signs. On their favorable Fourier halves the SAME literal signed prefix
earns an explicit nonnegative credit, without a positive allowance for
the remaining main. This does not prove its independent 399/5000 bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszJoinedPairSignCover
open ZetaRieszPairPrefixPayment ZetaRieszJointAllocation
open ZetaRieszLowCountSelbergAudit ZetaRieszPrimeEndpoint
open ZetaRieszGlobalCentralPayment ZetaRieszGlobalHeadCentralPayment
open ZetaRieszGlobalPeriodEdgePayment ZetaRieszLowCountSignedBoundary
open ZetaRieszSignedSelbergPayment
open ZetaRieszOwnerMaximal

private theorem tiny_lower_tail {N : ℕ} (hN : 65536≤N) :
    exp (-(N : ℝ)/250)≤1/200 := by
  have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
  have he := add_one_le_exp ((N : ℝ)/250)
  rw [show -(N : ℝ)/250=-((N : ℝ)/250) by ring,exp_neg]
  rw [←one_div]
  apply (div_le_iff₀ (exp_pos _)).mpr
  nlinarith only [he,hNr]

private theorem tiny_upper_tail {N : ℕ} (hN : 65536≤N) :
    2*exp (-(N : ℝ)/1250)≤1/1000 := by
  have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
  have he : (18 : ℝ)≤exp ((N : ℝ)/3750) := by
    have hh := add_one_le_exp ((N : ℝ)/3750)
    linarith only [hh,hNr]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤18) he 3
  have hid : (exp ((N : ℝ)/3750))^3=exp ((N : ℝ)/1250) := by
    rw [←exp_nat_mul]
    congr 1
    ring
  rw [hid] at hp
  rw [show -(N : ℝ)/1250=-((N : ℝ)/1250) by ring,exp_neg]
  rw [←div_eq_mul_inv]
  apply (div_le_iff₀ (exp_pos _)).mpr
  nlinarith only [hp]

private theorem ratio_bounds {N : ℕ} (hN : 65536≤N) {L T : ℝ}
    (hlo : (277/200 : ℝ)*N≤L) (hhi : L≤(139/100 : ℝ)*N)
    (hTlo : (39/20 : ℝ)*N≤T) (hThi : T≤(203/100 : ℝ)*N) :
    0<L ∧ 0<T ∧ (195/139 : ℝ)≤T/L ∧ T/L≤406/277 := by
  have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
  have hL : 0<L := by linarith only [hlo,hNr]
  have hT : 0<T := by linarith only [hTlo,hNr]
  refine ⟨hL,hT,?_,?_⟩
  · apply (le_div_iff₀ hL).mpr
    nlinarith only [hhi,hTlo]
  · apply (div_le_iff₀ hL).mpr
    nlinarith only [hlo,hThi]

/-- On the balanced box, the FULL joined coefficient is positive with
a uniform rational margin. The exact binomial prefix is retained. -/
theorem balanced_coefficient_lower {N : ℕ} (hN : 65536≤N) {L x z : ℝ}
    (hlo : (277/200 : ℝ)*N≤L) (hhi : L≤(139/100 : ℝ)*N)
    (hTlo : (39/20 : ℝ)*N≤x+z) (hThi : x+z≤(203/100 : ℝ)*N)
    (hx : 12/25≤x/(x+z)) (hz : 12/25≤z/(x+z)) :
    (x+z)/50≤prefixLogCoefficient N L x z+2*x*z/(x+z) := by
  obtain ⟨hL,hT,_hmin,hmax⟩ := ratio_bounds hN hlo hhi hTlo hThi
  have hsum : x/(x+z)+z/(x+z)=1 := by field_simp
  have hx1 : x/(x+z)≤1 := by linarith only [hsum,hz]
  have hz1 : z/(x+z)≤1 := by linarith only [hsum,hx]
  have hx0 : 0≤x := by
    simpa using (le_div_iff₀ hT).mp (show 0≤x/(x+z) by linarith only [hx])
  have hz0 : 0≤z := by
    simpa using (le_div_iff₀ hT).mp (show 0≤z/(x+z) by linarith only [hz])
  have hfx := (low_owner_tail N hx hx1).trans (tiny_lower_tail hN)
  have hfz := (low_owner_tail N hz hz1).trans (tiny_lower_tail hN)
  have hfx0 := (lowerMass_bounds (N+1) (13*N/32) (by linarith only [hx]) hx1).1
  have hfz0 := (lowerMass_bounds (N+1) (13*N/32) (by linarith only [hz]) hz1).1
  have hpx := (mul_le_mul_of_nonneg_right (show L-z≤L by linarith only [hz0]) hfx0).trans
    (mul_le_mul_of_nonneg_left hfx hL.le)
  have hpz := (mul_le_mul_of_nonneg_right (show L-x≤L by linarith only [hx0]) hfz0).trans
    (mul_le_mul_of_nonneg_left hfz hL.le)
  have hp : ((L-x)*lowerMass (N+1) (13*N/32) (z/(x+z))+
      (L-z)*lowerMass (N+1) (13*N/32) (x/(x+z)))/L≤1/100 := by
    apply (div_le_iff₀ hL).mpr
    linarith only [hpx,hpz]
  have hxhi : x/(x+z)≤13/25 := by linarith only [hsum,hz]
  have hprod := mul_nonneg (show 0≤x/(x+z)-12/25 by linarith only [hx])
    (show 0≤13/25-x/(x+z) by linarith only [hxhi])
  have hshare : (312/625 : ℝ)≤2*(x/(x+z))*(z/(x+z)) := by
    rw [show z/(x+z)=1-x/(x+z) by linarith only [hsum]]
    nlinarith only [hprod]
  have hid : (prefixLogCoefficient N L x z+2*x*z/(x+z))/(x+z)=
      1-(x+z)/L-
        ((L-x)*lowerMass (N+1) (13*N/32) (z/(x+z))+
         (L-z)*lowerMass (N+1) (13*N/32) (x/(x+z)))/L+
        2*(x/(x+z))*(z/(x+z)) := by
    unfold prefixLogCoefficient
    field_simp [hT.ne',hL.ne']
  have hg : (1/50 : ℝ)≤(prefixLogCoefficient N L x z+2*x*z/(x+z))/(x+z) := by
    rw [hid]
    linarith only [hp,hshare,hmax]
  have hh := (le_div_iff₀ hT).mp hg
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh

/-- The same FULL profile has the opposite sign on a higher-owner box.
No count, prefix endpoint or Selberg phase is split off. -/
theorem owner_coefficient_upper {N : ℕ} (hN : 65536≤N) {L x z : ℝ}
    (hlo : (277/200 : ℝ)*N≤L) (hhi : L≤(139/100 : ℝ)*N)
    (hTlo : (39/20 : ℝ)*N≤x+z) (hThi : x+z≤(203/100 : ℝ)*N)
    (hxlo : 5/8≤x/(x+z)) (hxhi : x/(x+z)≤11/16) :
    prefixLogCoefficient N L x z+2*x*z/(x+z)≤-(x+z)/200 := by
  obtain ⟨hL,hT,hmin,hmax⟩ := ratio_bounds hN hlo hhi hTlo hThi
  have hsum : x/(x+z)+z/(x+z)=1 := by field_simp
  have hzlo : (5/16 : ℝ)≤z/(x+z) := by linarith only [hsum,hxhi]
  have hzhi : z/(x+z)≤3/8 := by linarith only [hsum,hxlo]
  have hx0 : 0≤x := by
    simpa using (le_div_iff₀ hT).mp (show 0≤x/(x+z) by linarith only [hxlo])
  have hz0 : 0≤z/(x+z) := by linarith only [hzlo]
  have hzL : z≤L := by
    have hzT := (div_le_iff₀ hT).mp hzhi
    linarith only [hzT,hThi,hlo]
  have hc0 := (lowerMass_bounds (N+1) (13*N/32) hz0 (by linarith only [hzhi])).2
  have hc : 1-lowerMass (N+1) (13*N/32) (z/(x+z))≤1/1000 :=
    (high_owner_tail N hz0 (by linarith only [hzhi])).trans (tiny_upper_tail hN)
  have hf0 := (lowerMass_bounds (N+1) (13*N/32)
    (by linarith only [hxlo]) (by linarith only [hxhi])).1
  have hpos := mul_nonneg (show 0≤L-z by linarith only [hzL]) hf0
  have hp := (mul_le_mul_of_nonneg_right (show L-x≤L by linarith only [hx0])
    (show 0≤1-lowerMass (N+1) (13*N/32) (z/(x+z)) by linarith only [hc0])).trans
      (mul_le_mul_of_nonneg_left hc hL.le)
  have herr : ((L-x)*(1-lowerMass (N+1) (13*N/32) (z/(x+z)))-
      (L-z)*lowerMass (N+1) (13*N/32) (x/(x+z)))/L≤1/1000 := by
    apply (div_le_iff₀ hL).mpr
    linarith only [hp,hpos]
  have hdiff : 2*(x/(x+z))-(x+z)/L≤11/8-195/139 := by linarith only [hxhi,hmin]
  have hm := mul_le_mul_of_nonneg_left hdiff hz0
  have hn := mul_le_mul_of_nonpos_right hzlo (by norm_num : (11/8-195/139 : ℝ)≤0)
  have hid : (prefixLogCoefficient N L x z+2*x*z/(x+z))/(x+z)=
      (z/(x+z))*(2*(x/(x+z))-(x+z)/L)+
      ((L-x)*(1-lowerMass (N+1) (13*N/32) (z/(x+z)))-
       (L-z)*lowerMass (N+1) (13*N/32) (x/(x+z)))/L := by
    unfold prefixLogCoefficient
    field_simp [hT.ne',hL.ne']
    ring
  have hg : (prefixLogCoefficient N L x z+2*x*z/(x+z))/(x+z)≤-(1/200 : ℝ) := by
    rw [hid]
    linarith only [herr,hm,hn]
  have hh := (div_le_iff₀ hT).mp hg
  simpa only [div_eq_mul_inv,mul_comm,neg_mul,mul_neg,one_mul] using hh

private theorem largest_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p<q) :
    largestPrime (p*q)=q := by
  rw [mul_comm]
  apply ZetaRieszPrimeIntervals.largestPrime_mul q p hq hp.ne_zero
  intro r hr
  rw [hp.primeFactors,Finset.mem_singleton] at hr
  subst r
  exact hpq

private theorem literal_pair_coefficient {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p<q) (u : ℝ) (N : ℕ) (hn : p*q∈semiprimeLabels N) :
    prefixCoefficient u N (p*q)-selbergCoefficient (p*q)=
      ((prefixLogCoefficient N (SquarefreeVaughanLogSource.length u N) (log q) (log p)+
        2*log p*log q/log (p*q : ℕ) : ℝ) : ℂ) := by
  have hl := largest_pair hp hq hpq
  have hc : ZetaRieszOwnedCells.ownerCofactor (p*q)=p := by
    rw [ZetaRieszOwnedCells.ownerCofactor,hl,Nat.mul_div_left _ hq.pos]
  rw [prefixCoefficient,hl,hc,
    if_pos (Finset.mem_union.mpr (Or.inr hn)),sub_zero,selbergCoefficient_pair hp hq hpq]
  push_cast
  ring

private theorem atom_real (a y : ℝ) (N n : ℕ) :
    ((a : ℂ)*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re=
      a*‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖*cos (y*log n) := by
  have hr := ZetaRieszCosineCarrier.re_filterKernel_one N y (n : ℝ)
  rw [ZetaRieszJointAllocation.filter_one_eq] at hr
  rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    hr,norm_zetaPrimeLogKernel]
  have hs : (3/2+Complex.I*(y : ℂ)).re=(3/2 : ℝ) := by norm_num
  rw [hs,zetaPrimeExpWeight]
  ring

private theorem favorable_scalar {a T c : ℝ} (hT : 0≤T) (hc0 : -1≤c) (hc1 : c≤1)
    (h : (T/50≤a ∧ c≤0) ∨ (a≤-T/200 ∧ 0≤c)) :
    a*c≤-(T/200)*c^2 := by
  rcases h with ⟨ha,hc⟩ | ⟨ha,hc⟩
  · have hm := mul_le_mul_of_nonpos_right (show T/200≤a by linarith only [ha,hT]) hc
    have hprod := mul_nonneg (show 0≤-c by linarith only [hc])
      (show 0≤1+c by linarith only [hc0])
    have ht := mul_le_mul_of_nonneg_left (show c≤-c^2 by nlinarith only [hprod])
      (show 0≤T/200 by positivity)
    linarith only [hm,ht]
  · have hm := mul_le_mul_of_nonneg_right ha hc
    have hprod := mul_nonneg hc (show 0≤1-c by linarith only [hc1])
    have ht := mul_le_mul_of_nonpos_left (show c^2≤c by nlinarith only [hprod])
      (neg_nonpos.mpr (show 0≤T/200 by positivity))
    linarith only [hm,ht]

/-- Favorable labels are a subfamily of the SAME original retained
support. Their two sign geometries are tested AFTER the full coefficient
is joined. Physical, endpoint and complete-period masks stay literal. -/
def favorableLabels (u y : ℝ) (N : ℕ) : Finset ℕ :=
  ((completePeriodLabels (joinedLabels u N) N y).filter (fun n => ¬n.Prime)).filter
    (fun n => n∈semiprimeLabels N ∧ ∃ p q : ℕ,p.Prime ∧ q.Prime ∧ p<q ∧ p*q=n ∧
      (39/20 : ℝ)*N≤log n ∧ log n≤(203/100 : ℝ)*N ∧
      ((12/25≤log p/log n ∧ 12/25≤log q/log n ∧ cos (y*log n)≤0) ∨
       (5/8≤log q/log n ∧ log q/log n≤11/16 ∧ 0≤cos (y*log n))))

/-- Every favorable literal atom earns a rational signed credit. This
uses its actual phase; neither the main nor a Fourier integral is normed. -/
theorem favorable_atom_credit {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N)
    {y : ℝ} {n : ℕ} (hn : n∈favorableLabels u y N) :
    ((prefixCoefficient u N n-selbergCoefficient n)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re≤
      -(log n/200)*‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖*(cos (y*log n))^2 := by
  obtain ⟨_,hsemi,p,q,hp,hq,hpq,he,hTlo,hThi,hgeom⟩ := Finset.mem_filter.mp hn
  subst n
  have hlog : log q+log p=log (p*q : ℕ) := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
    ring
  have hlo := ZetaRieszPostHingeEnergy.length_ge_rational hN
    (by linarith only [hu] : 0<u) hU
  have hhi := ZetaRieszSmallTagNativeFloor.length_upper hu (by omega : 2≤N)
  let a : ℝ := prefixLogCoefficient N (SquarefreeVaughanLogSource.length u N) (log q) (log p)+
    2*log p*log q/log (p*q : ℕ)
  have hs : (log (p*q : ℕ)/50≤a ∧ cos (y*log (p*q : ℕ))≤0) ∨
      (a≤-log (p*q : ℕ)/200 ∧ 0≤cos (y*log (p*q : ℕ))) := by
    rcases hgeom with ⟨hps,hqs,hcos⟩ | ⟨hqs,hqhi,hcos⟩
    · refine Or.inl ⟨?_,hcos⟩
      have hb := balanced_coefficient_lower (x := log q) (z := log p) hN hlo hhi
        (by simpa only [hlog] using hTlo) (by simpa only [hlog] using hThi)
        (by simpa only [hlog] using hqs) (by simpa only [hlog] using hps)
      dsimp only [a]
      simpa only [hlog,mul_comm,mul_left_comm,mul_assoc] using hb
    · refine Or.inr ⟨?_,hcos⟩
      have hb := owner_coefficient_upper (x := log q) (z := log p) hN hlo hhi
        (by simpa only [hlog] using hTlo) (by simpa only [hlog] using hThi)
        (by simpa only [hlog] using hqs) (by simpa only [hlog] using hqhi)
      dsimp only [a]
      simpa only [hlog,mul_comm,mul_left_comm,mul_assoc] using hb
  have hc := favorable_scalar (a := a) (T := log (p*q : ℕ)) (c := cos (y*log (p*q : ℕ)))
    (log_natCast_nonneg (p*q))
    (neg_one_le_cos _) (cos_le_one _) hs
  rw [literal_pair_coefficient hp hq hpq u N hsemi,atom_real]
  change a*‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*q)‖*cos (y*log (p*q : ℕ))≤_
  calc
    _ = (a*cos (y*log (p*q : ℕ)))*‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*q)‖ := by ring
    _ ≤ (-(log (p*q : ℕ)/200)*(cos (y*log (p*q : ℕ)))^2)*
        ‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*q)‖ :=
      mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = _ := by ring

/-- A nonnegative CREDIT, not a termwise positive allowance. It is
measured on actual prime labels and their original full phases. -/
def signCredit (u y : ℝ) (N : ℕ) : ℝ :=
  u^(N+1)/200*∑ n∈favorableLabels u y N,
    log n*‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖*(cos (y*log n))^2

theorem signCredit_nonneg {u : ℝ} (hu : 0≤u) (y : ℝ) (N : ℕ) :
    0 ≤ signCredit u y N := by
  unfold signCredit
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun n _ =>
    mul_nonneg (mul_nonneg (log_natCast_nonneg n) (norm_nonneg _)) (sq_nonneg _)))

/-- An independent upper inequality for the EXISTING retained signed
main. Both sign regions and ALL their radial periods are credited at
once. The complementary sum stays signed and is still unpaid. -/
theorem prefix_upper_with_signed_credit {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) (y : ℝ) :
    (prefixPairDefect u y N).re≤
      ((u : ℂ)^(N+1)*∑ n∈
        ((completePeriodLabels (joinedLabels u N) N y).filter (fun n => ¬n.Prime))\
          favorableLabels u y N,
        (prefixCoefficient u N n-selbergCoefficient n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-signCredit u y N := by
  let S := (completePeriodLabels (joinedLabels u N) N y).filter (fun n => ¬n.Prime)
  let f (n : ℕ) := (prefixCoefficient u N n-selbergCoefficient n)*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hsub : favorableLabels u y N⊆S := Finset.filter_subset _ _
  have he := Finset.sum_sdiff (f := f) hsub
  have hpart : (∑ n∈favorableLabels u y N,f n).re≤
      -(1/200 : ℝ)*∑ n∈favorableLabels u y N,
        log n*‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖*(cos (y*log n))^2 := by
    rw [Complex.re_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    exact (favorable_atom_credit hu hU hN hn).trans_eq (by ring)
  have hr : (u : ℂ)^(N+1)=((u^(N+1) : ℝ) : ℂ) := by simp
  change ((u : ℂ)^(N+1)*∑ n∈S,f n).re≤_
  rw [←he,mul_add,Complex.add_re,hr]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hb := mul_le_mul_of_nonneg_left hpart (pow_nonneg (by linarith only [hu]) (N+1))
  unfold signCredit
  dsimp only [f,S] at *
  linarith only [hb]

/-- Keep the ENTIRE signed favorable contribution in the joint ledger.
The smaller rational `signCredit` is a proved benchmark, not a license
to discard the remaining favorable mass before phase matching. -/
def exactSignCredit (u y : ℝ) (N : ℕ) : ℝ :=
  -((u : ℂ)^(N+1)*∑ n∈favorableLabels u y N,
    (prefixCoefficient u N n-selbergCoefficient n)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re

/-- Preserve the exact credit when grouping the original floor. No
favorable excess, unmatched period or mask boundary is thrown away. -/
theorem prefix_eq_rest_sub_exact_credit (u y : ℝ) (N : ℕ) :
    (prefixPairDefect u y N).re=
      ((u : ℂ)^(N+1)*∑ n∈
        ((completePeriodLabels (joinedLabels u N) N y).filter (fun n => ¬n.Prime))\
          favorableLabels u y N,
        (prefixCoefficient u N n-selbergCoefficient n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-exactSignCredit u y N := by
  have hsub : favorableLabels u y N⊆
      (completePeriodLabels (joinedLabels u N) N y).filter (fun n => ¬n.Prime) :=
    Finset.filter_subset _ _
  have he := Finset.sum_sdiff (f := fun n => (prefixCoefficient u N n-selbergCoefficient n)*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n) hsub
  unfold prefixPairDefect exactSignCredit
  rw [←he,mul_add,Complex.add_re]
  ring

/-- A quantitative, independent lower bound for the EXACT signed
credit. All source-carrying favorable mass stays available. -/
theorem signCredit_le_exact {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) (y : ℝ) :
    signCredit u y N≤exactSignCredit u y N := by
  have hb := prefix_upper_with_signed_credit hu hU hN y
  rw [prefix_eq_rest_sub_exact_credit] at hb
  linarith only [hb]

theorem exactSignCredit_nonneg {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) (y : ℝ) :
    0 ≤ exactSignCredit u y N :=
  (signCredit_nonneg (by linarith only [hu]) y N).trans (signCredit_le_exact hu hU hN y)

/-- Both broad sign populations improve the ORIGINAL native floor by
their exact credit. The remaining signed difference has not been bounded
by 399/5000; no completion or earlier payment is spent a second time. -/
theorem eventually_native_exact_credit_floor {u C : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) (hC : 1≤C)
    (ha : ∀ k,‖(u : ℂ)^(k+1)*zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖≤C) :
    ∀ᶠ j in atTop,
      -((u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*∑ n∈
        ((completePeriodLabels (joinedLabels u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) y).filter (fun n => ¬n.Prime))\
            favorableLabels u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j),
        (prefixCoefficient u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) n-selbergCoefficient n)*
          zetaPrimeLogKernel (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (3/2+Complex.I*y) n).re+
        exactSignCredit u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (nativeSelbergBudget u y C j+prefixBudget (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))≤
      ((u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
        (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  filter_upwards [eventually_native_prefix_floor hu hU hy hC ha] with j hj
  rw [prefix_eq_rest_sub_exact_credit] at hj
  linarith only [hj]

end RiemannGaussian.ZetaRieszJoinedPairSignCover
