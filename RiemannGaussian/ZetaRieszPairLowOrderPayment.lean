/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPairPrefixConvolution

/-!
# Geometric payment of the surviving low logged orders

The exact endpoint cancellation leaves logged orders, not an order-zero
error. On the literal pairs whose largest prime log is at most the moving
length, both shares are at least `7/24`. Their logged orders through
`floor(17N/64)+1` have a uniform exponential payment. Every actual period,
radial flag and phase is retained. The higher orders and the unbounded
largest-prime population remain signed and unpaid.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszPairLowOrderPayment
open ZetaRieszJointAllocation ZetaRieszOwnerMaximal ZetaRieszPairPrefixPayment
open ZetaRieszPairPrefixConvolution ZetaRieszHeadOrders
open ZetaRieszLowCountSignedBoundary ZetaRieszGlobalPeriodEdgePayment
open ZetaRieszSignedSelbergPayment ZetaRieszPrimeEndpoint

/-- The exact lower logged-order cutoff; no continuum share mask is used. -/
def lowOrders (N : ℕ) : Finset ℕ := Finset.Icc 1 (17*N/64+1)

/-- These are genuine existing logged orders, rather than a completed
factorial population introduced for the estimate. -/
theorem lowOrders_subset {N : ℕ} (hN : 8≤N) :
    lowOrders N⊆(Finset.range (13*N/32+1)).filter (fun k => 0<k) := by
  intro k hk
  have hk' := Finset.mem_Icc.mp hk
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ?_,by omega⟩
  omega

private theorem log_tilt_upper : log (11/10 : ℝ) ≤ 12/125 := by
  apply (log_le_iff_le_exp (by norm_num : (0 : ℝ)<11/10)).mpr
  have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤12/125) 4
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- A literal binomial lower prefix uniformly separated from both
physical prime shares. Its rate is stronger than the source growth. -/
theorem low_prefix_bound (N : ℕ) {x : ℝ} (hx : 7/24 ≤ x) (hx1 : x ≤ 1) :
    lowerMass (N+1) (17*N/64) x ≤ exp (-(N : ℝ)/1000) := by
  have hx0 : 0≤x := by linarith
  have h := prefix_tilt (N+1) (17*N/64) (by omega) hx0 hx1
    (by norm_num : (1 : ℝ)<11/10)
  have hbase : (11/10 : ℝ)⁻¹*x+(1-x) ≤ 257/264 := by norm_num; linarith
  have hnonneg : 0 ≤ (11/10 : ℝ)⁻¹*x+(1-x) := by norm_num; linarith
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hbase (N+1))
    (exp_pos (((17*N/64 : ℕ) : ℝ)*log (11/10))).le
  apply (h.trans hp).trans
  rw [←exp_log (by norm_num : (0 : ℝ)<257/264),←exp_nat_mul,←exp_add]
  apply exp_le_exp.mpr
  have hcut : ((17*N/64 : ℕ) : ℝ) ≤ (17/64 : ℝ)*N := by
    have h := Nat.mul_div_le (17*N) 64
    have hr : 64*((17*N/64 : ℕ) : ℝ)≤17*N := by exact_mod_cast h
    linarith
  have hb : log (257/264 : ℝ) ≤ -(7/264) := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<257/264)
    linarith
  have h1 := mul_le_mul_of_nonneg_right log_tilt_upper
    (Nat.cast_nonneg (α:=ℝ) (17*N/64))
  have h2 := mul_le_mul_of_nonneg_right hcut (by norm_num : (0 : ℝ)≤12/125)
  have h3 := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α:=ℝ) (N+1))
  push_cast at h3 ⊢
  nlinarith only [h1,h2,h3,Nat.cast_nonneg (α:=ℝ) N]

/-- The exact logged prefix after joining both swapped prime incidences. -/
def lowLoggedCoefficient (N : ℕ) (L x z : ℝ) : ℝ :=
  -(x+z)/L*(x*lowerMass (N+1) (17*N/64) (x/(x+z))+
    z*lowerMass (N+1) (17*N/64) (z/(x+z)))

private theorem logged_prefix_reindex (N H p q : ℕ) (s : ℂ) :
    (∑ k∈Finset.Icc 1 (H+1), (k : ℂ)*zetaPrimeLogKernel k s p*
      zetaPrimeLogKernel (N+2-k) s q) =
    (log p : ℂ)*(∑ l∈Finset.range (H+1), zetaPrimeLogKernel l s p*
      zetaPrimeLogKernel (N+1-l) s q) := by
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun k _ => k-1) ?_ ?_ ?_ ?_
  · intro k hk
    have := Finset.mem_Icc.mp hk
    exact Finset.mem_range.mpr (by omega)
  · intro a ha b hb he
    have := Finset.mem_Icc.mp ha
    have := Finset.mem_Icc.mp hb
    omega
  · intro l hl
    have := Finset.mem_range.mp hl
    exact ⟨l+1,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
  · intro k hk
    have hk0 := (Finset.mem_Icc.mp hk).1
    have he : k-1+1=k := by omega
    have hs : N+2-k=N+1-(k-1) := by omega
    have hlog := log_mul_kernel (k-1) p s
    rw [he] at hlog
    rw [hs,←hlog]
    ring

/-- This is precisely the low portion of the surviving logged convolution,
not a new coefficient guessed from share geometry. Both incidences and
the literal product phase remain in the identity. -/
theorem low_logged_atom_eq (N p q : ℕ) (L : ℝ) (s : ℂ)
    (hp : 0<p) (hq : 0<q) (hpq : 1<p*q) :
    (lowLoggedCoefficient N L (log p) (log q) : ℂ)*
      zetaPrimeLogKernel N s (p*q) =
    -(N+1 : ℂ)/(L : ℂ)*∑ k∈lowOrders N,(k : ℂ)*
      (zetaPrimeLogKernel k s p*zetaPrimeLogKernel (N+2-k) s q+
        zetaPrimeLogKernel k s q*zetaPrimeLogKernel (N+2-k) s p) := by
  have hK : 17*N/64≤N+1 := by omega
  have hpref := prefix_mass_kernel (N+1) (17*N/64) q p hK hq hp
    (by simpa only [mul_comm] using hpq) s
  have hqref := prefix_mass_kernel (N+1) (17*N/64) p q hK hp hq hpq s
  have hlog : log (p*q : ℕ)=log p+log q := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast hq.ne')]
  rw [lowOrders]
  simp only [mul_add,←mul_assoc,Finset.sum_add_distrib]
  rw [logged_prefix_reindex,logged_prefix_reindex]
  rw [mul_comm q p,hlog] at hpref
  rw [hlog] at hqref
  have hpr : (∑ l∈Finset.range (17*N/64+1), zetaPrimeLogKernel l s p*
      zetaPrimeLogKernel (N+1-l) s q) =
      (lowerMass (N+1) (17*N/64) (log p/(log p+log q)) : ℂ)*
        zetaPrimeLogKernel (N+1) s (p*q) := by
    rw [hpref]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hqr : (∑ l∈Finset.range (17*N/64+1), zetaPrimeLogKernel l s q*
      zetaPrimeLogKernel (N+1-l) s p) =
      (lowerMass (N+1) (17*N/64) (log q/(log p+log q)) : ℂ)*
        zetaPrimeLogKernel (N+1) s (p*q) := by
    rw [hqref]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [hpr,hqr]
  have hk := log_mul_kernel N (p*q) s
  rw [hlog] at hk
  simp only [Complex.ofReal_add,Nat.cast_add,Nat.cast_one] at hk
  simp only [lowLoggedCoefficient,Complex.ofReal_mul,Complex.ofReal_add,
    Complex.ofReal_div,Complex.ofReal_neg]
  linear_combination (-((log p : ℂ)*
    (lowerMass (N+1) (17*N/64) (log p/(log p+log q)) : ℂ)+
    (log q : ℂ)*(lowerMass (N+1) (17*N/64) (log q/(log p+log q)) : ℂ))/(L : ℂ))*hk

/-- Both physical prime shares stay uniformly away from the deleted
factorial range; the moving length is not replaced by its limit. -/
theorem physical_shares {N : ℕ} {L x z : ℝ}
    (hx : 0≤x) (hz : 0≤z) (hT : 0<x+z)
    (hl : (1971/1000 : ℝ)*N≤x+z) (hL : L≤(139/100 : ℝ)*N)
    (hxp : x≤L) (hzp : z≤L) :
    7/24≤x/(x+z) ∧ x/(x+z)≤1 ∧
      7/24≤z/(x+z) ∧ z/(x+z)≤1 := by
  have hsep : L≤(17/24 : ℝ)*(x+z) := by
    nlinarith only [hl,hL,Nat.cast_nonneg (α:=ℝ) N]
  refine ⟨(le_div_iff₀ hT).mpr ?_,(div_le_one hT).mpr ?_,
    (le_div_iff₀ hT).mpr ?_,(div_le_one hT).mpr ?_⟩
  · linarith only [hsep,hzp]
  · linarith only [hz]
  · linarith only [hsep,hxp]
  · linarith only [hx]

/-- The whole symmetric low logged coefficient is small on every
physical pair, before any phase estimate or prime-density input. -/
theorem low_coefficient_bound {N : ℕ} {L x z : ℝ}
    (hx : 0≤x) (hz : 0≤z) (hT : 0<x+z) (hLp : 0<L)
    (hl : (1971/1000 : ℝ)*N≤x+z) (hh : x+z≤(2029/1000 : ℝ)*N)
    (hLlo : (277/200 : ℝ)*N≤L) (hLhi : L≤(139/100 : ℝ)*N)
    (hxp : x≤L) (hzp : z≤L) :
    |lowLoggedCoefficient N L x z| ≤ 2*(x+z)*exp (-(N : ℝ)/1000) := by
  obtain ⟨hxs,hxs1,hzs,hzs1⟩ := physical_shares hx hz hT hl hLhi hxp hzp
  have hfx := low_prefix_bound N hxs hxs1
  have hfz := low_prefix_bound N hzs hzs1
  have hfx0 := (lowerMass_bounds (N+1) (17*N/64) (by linarith : 0≤x/(x+z)) hxs1).1
  have hfz0 := (lowerMass_bounds (N+1) (17*N/64) (by linarith : 0≤z/(x+z)) hzs1).1
  have hsum : 0≤x*lowerMass (N+1) (17*N/64) (x/(x+z))+
      z*lowerMass (N+1) (17*N/64) (z/(x+z)) := by positivity
  have hs := add_le_add (mul_le_mul_of_nonneg_left hfx hx)
    (mul_le_mul_of_nonneg_left hfz hz)
  have hr : (x+z)/L ≤ 2 := (div_le_iff₀ hLp).mpr (by
    nlinarith only [hh,hLlo,Nat.cast_nonneg (α:=ℝ) N])
  rw [lowLoggedCoefficient,abs_mul,abs_div,abs_neg,abs_of_nonneg hT.le,
    abs_of_pos hLp,abs_of_nonneg hsum]
  calc
    _ ≤ (x+z)/L*((x+z)*exp (-(N : ℝ)/1000)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith only [hs]
    _ ≤ 2*((x+z)*exp (-(N : ℝ)/1000)) :=
      mul_le_mul_of_nonneg_right hr (by positivity)
    _ = _ := by ring

/-- The actual support for this payment. Pairs above the moving physical
largest-prime cutoff are explicitly not included. -/
def physicalLabels (u y : ℝ) (N : ℕ) : Finset ℕ :=
  ((completePeriodLabels (joinedLabels u N) N y).filter (fun n => ¬n.Prime)).filter
    (fun n => log (largestPrime n)≤SquarefreeVaughanLogSource.length u N)

/-- The low logged piece inside the existing signed carrier, with every
literal radial/period flag and both prime phases unchanged. -/
def lowLoggedPacket (u y : ℝ) (N : ℕ) : ℂ :=
  (u : ℂ)^(N+1)*∑ n∈physicalLabels u y N,
    (lowLoggedCoefficient N (SquarefreeVaughanLogSource.length u N)
      (log (largestPrime n)) (log (ZetaRieszOwnedCells.ownerCofactor n)) : ℂ)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- Explicit whole-population source-scale cost for the removed orders. -/
def lowOrderBudget (N : ℕ) : ℝ := 8*exp 2*((N : ℝ)+1)*exp (-(N : ℝ)/1250)

/-- The source growth is strictly smaller than the binomial tail saving. -/
theorem low_order_source_rate {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ) :
    (2*u)^(N+1)*exp (-(N : ℝ)/1000)≤2*exp (-(N : ℝ)/1250) := by
  have hbase : 2*u≤exp (1/10000 : ℝ) := by
    have h := add_one_le_exp (1/10000 : ℝ)
    unfold ZetaRieszWideOwnerAudit.radiusCeiling at hU
    linarith
  have hpow := pow_le_pow_left₀ (by linarith : 0≤2*u) hbase (N+1)
  rw [←exp_nat_mul] at hpow
  have hmul := mul_le_mul_of_nonneg_right hpow (exp_pos (-(N : ℝ)/1000)).le
  rw [←exp_add] at hmul
  have hrate : ((N+1 : ℕ) : ℝ)*(1/10000)-(N : ℝ)/1000≤
      (1/10000 : ℝ)-(N : ℝ)/1250 := by
    push_cast
    nlinarith only [Nat.cast_nonneg (α:=ℝ) N]
  have hconst : exp (1/10000 : ℝ)≤2 := by
    calc
      _ ≤ exp (log 2) := exp_le_exp.mpr (by linarith [log_two_gt_d9])
      _ = _ := exp_log (by norm_num)
  calc
    _ ≤ exp ((1/10000 : ℝ)-(N : ℝ)/1250) := hmul.trans
      (exp_le_exp.mpr (by simpa only [sub_eq_add_neg,neg_div] using hrate))
    _ = exp (1/10000 : ℝ)*exp (-(N : ℝ)/1250) := by
      rw [sub_eq_add_neg,exp_add,neg_div]
    _ ≤ _ := mul_le_mul_of_nonneg_right hconst (exp_pos _).le

/-- This payment tends to zero geometrically; it is not a norm bound
for the remaining signed central/logged carrier. -/
theorem lowOrderBudget_tendsto : Tendsto lowOrderBudget atTop (𝓝 0) := by
  have h := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1
    (exp_pos (-(1/1250 : ℝ))) (exp_lt_one_iff.mpr (by norm_num : -(1/1250 : ℝ)<0))).const_mul
      (8*exp 2)
  simp only [pow_one,mul_zero] at h
  apply h.congr'
  filter_upwards [] with N
  have he : (exp (-(1/1250 : ℝ)))^N=exp (-(N : ℝ)/1250) := by
    rw [←exp_nat_mul]
    congr 1
    ring
  simp only [he,lowOrderBudget,mul_assoc]

/-- Whole-population summation of an independently exponentially small
coefficient. The surviving signed main is never normed in this theorem. -/
theorem source_scaled_low_coefficient_bound {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ) (y : ℝ)
    (S : Finset ℕ) (hS : ∀ n∈S,0<n) (a : ℕ→ℂ)
    (ha : ∀ n∈S,‖a n‖≤2*log n*exp (-(N : ℝ)/1000)) :
    ‖(u : ℂ)^(N+1)*∑ n∈S,a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖≤
      lowOrderBudget N := by
  let E := exp (-(N : ℝ)/1000)
  have hsum : ‖∑ n∈S,a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖≤
      2*E*((N+1 : ℕ) : ℝ)*(exp 2*2^(N+2)) := by
    calc
      _ ≤ ∑ n∈S,‖a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := norm_sum_le _ _
      _ ≤ ∑ n∈S,2*E*(log n*‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul]
        simpa only [E,mul_assoc,mul_left_comm,mul_comm] using
          mul_le_mul_of_nonneg_right (ha n hn)
            (norm_nonneg (zetaPrimeLogKernel N (3/2+Complex.I*y) n))
      _ = 2*E*((N+1 : ℕ) : ℝ)*∑ n∈S,
          ZetaRieszCentralRadialCost.radial (N+1) (log n)/(n : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [log_kernel_radial N n (hS n hn) y]
        ring
      _ ≤ 2*E*((N+1 : ℕ) : ℝ)*∑ n∈Finset.Icc 1 (S.sup id),
          ZetaRieszCentralRadialCost.radial (N+1) (log n)/(n : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          exact Finset.mem_Icc.mpr ⟨hS n hn,Finset.le_sup (f:=id) hn⟩
        · intro n _ _
          unfold ZetaRieszCentralRadialCost.radial
          positivity
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (ZetaRieszSignedDensityMain.radial_integer_mass (N+1) (S.sup id)) (by positivity)
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (by linarith : 0≤u)]
  calc
    _ ≤ u^(N+1)*(2*E*((N+1 : ℕ) : ℝ)*(exp 2*2^(N+2))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4*exp 2*((N : ℝ)+1)*((2*u)^(N+1)*exp (-(N : ℝ)/1000)) := by
      dsimp [E]
      rw [mul_pow,show N+2=(N+1)+1 by omega,pow_succ]
      push_cast
      ring
    _ ≤ 4*exp 2*((N : ℝ)+1)*(2*exp (-(N : ℝ)/1250)) :=
      mul_le_mul_of_nonneg_left (low_order_source_rate hu hU N) (by positivity)
    _ = _ := by unfold lowOrderBudget; ring

private theorem physical_label_coefficient_bound {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N n : ℕ} (hN : 65536≤N)
    {y : ℝ} (hy : 54≤|y|) (hn : n∈physicalLabels u y N) :
    0<n ∧ ‖(lowLoggedCoefficient N (SquarefreeVaughanLogSource.length u N)
      (log (largestPrime n)) (log (ZetaRieszOwnedCells.ownerCofactor n)) : ℂ)‖≤
        2*log n*exp (-(N : ℝ)/1000) := by
  obtain ⟨hn,hphysical⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn,hnot⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn,hl,hh⟩ := Finset.mem_filter.mp hn
  rcases ordinaryLabel_pair (joinedLabels_ordinary hu hU hN hn) with hp | ⟨p,q,hp,hq,hpq,he⟩
  · exact (hnot hp).elim
  have hgeom := period_log_bracket hy n
  have hlarge : ∃ p q : ℕ,p.Prime ∧ q.Prime ∧ q<p ∧ p*q=n := by
    rcases lt_or_gt_of_ne hpq with hlt | hgt
    · exact ⟨q,p,hq,hp,hlt,by simpa only [mul_comm] using he⟩
    · exact ⟨p,q,hp,hq,hgt,he⟩
  obtain ⟨p,q,hp,hq,hqp,rfl⟩ := hlarge
  have hm : ∀ r∈q.primeFactors,r<p := by
    intro r hr
    rw [hq.primeFactors,Finset.mem_singleton] at hr
    subst r
    exact hqp
  have hpmax := ZetaRieszPrimeIntervals.largestPrime_mul p q hp hq.ne_zero hm
  have hco := ZetaRieszPrimeIntervals.ownerCofactor_mul p q hp hq.ne_zero hm
  have hlog : log (p*q : ℕ)=log p+log q := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  have hpos : 0<p*q := Nat.mul_pos hp.pos hq.pos
  have hT : 0<log p+log q := by
    have h := log_pos (by exact_mod_cast hp.two_le : (1 : ℝ)<p)
    linarith [log_natCast_nonneg q]
  have hLp := SquarefreeVaughanLogSource.length_pos u N
  have hx := hphysical
  rw [hpmax] at hx
  have hz : log q≤SquarefreeVaughanLogSource.length u N :=
    (log_le_log (by exact_mod_cast hq.pos) (by exact_mod_cast hqp.le)).trans hx
  rw [hpmax,hco,Complex.norm_real,Real.norm_eq_abs,hlog]
  refine ⟨hpos,low_coefficient_bound (log_natCast_nonneg _) (log_natCast_nonneg _)
    hT hLp ?_ ?_ (ZetaRieszPostHingeEnergy.length_ge_rational hN (by linarith) hU)
      (ZetaRieszSmallTagNativeFloor.length_upper hu (by omega : 2≤N)) hx hz⟩
  · simpa only [hlog] using hl.trans hgeom.1
  · simpa only [hlog] using hgeom.2.le.trans hh

/-- An independent geometric payment on the actual signed prime-pair
population. No exposure, multiplicity, completion or phase hypothesis is
used except the original nonzero-height complete-period geometry. -/
theorem norm_lowLoggedPacket_le {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N)
    {y : ℝ} (hy : 54≤|y|) :
    ‖lowLoggedPacket u y N‖≤lowOrderBudget N := by
  exact source_scaled_low_coefficient_bound hu hU N y (physicalLabels u y N)
    (fun _ hn => (physical_label_coefficient_bound hu hU hN hy hn).1)
    (fun n => (lowLoggedCoefficient N (SquarefreeVaughanLogSource.length u N)
      (log (largestPrime n)) (log (ZetaRieszOwnedCells.ownerCofactor n)) : ℂ))
    (fun _ hn => (physical_label_coefficient_bound hu hU hN hy hn).2)

/-- The removed logged orders vanish on the literal support, uniformly
in fixed height; the signed remaining central orders are left intact. -/
theorem tendsto_lowLoggedPacket {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (lowLoggedPacket u y) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ lowOrderBudget_tendsto
  filter_upwards [eventually_ge_atTop (65536 : ℕ)] with N hN
  exact norm_lowLoggedPacket_le hu hU hN hy

/-- Direct upper transfer on the existing prefix carrier, paying only
the identified low factorial orders, rather than the signed main. -/
theorem prefix_re_le_sub_low {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N)
    {y : ℝ} (hy : 54≤|y|) :
    (prefixPairDefect u y N).re≤
      (prefixPairDefect u y N-lowLoggedPacket u y N).re+lowOrderBudget N := by
  have h := (Complex.re_le_norm (lowLoggedPacket u y N)).trans
    (norm_lowLoggedPacket_le hu hU hN hy)
  simp only [Complex.sub_re]
  linarith only [h]

open ZetaRieszPrimeCountFrequency

/-- Spend the new geometric payment directly in the original whole-core
floor. The remaining signed prefix and all prior budgets remain explicit. -/
theorem eventually_native_sub_low_floor {u C : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (hC : 1≤C)
    (ha : ∀ k,‖(u : ℂ)^(k+1)*zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖≤C) :
    ∀ᶠ j in atTop,
      -(prefixPairDefect u y (dyadicMomentOrder j)-
        lowLoggedPacket u y (dyadicMomentOrder j)).re-
        (nativeSelbergBudget u y C j+prefixBudget (dyadicMomentOrder j)+
          lowOrderBudget (dyadicMomentOrder j))≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
        (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  filter_upwards [eventually_native_prefix_floor hu hU hy hC ha,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (65536 : ℕ))]
      with j hfloor hN
  have hlow := prefix_re_le_sub_low hu.le hU hN hy
  linarith only [hfloor,hlow]

/-- Under the original simple exposed-zero hypotheses all three payments
have proved vanishing budgets. Only the signed remaining carrier is unpaid. -/
theorem exists_native_sub_low_payment_simple (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hm : analyticZetaZeroMultiplicity rho=1)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|rho.1.im|) :
    ∃ C : ℝ,1≤C ∧
      Tendsto (fun j => nativeSelbergBudget (3/2-rho.1.re) rho.1.im C j+
        prefixBudget (dyadicMomentOrder j)+lowOrderBudget (dyadicMomentOrder j)) atTop (𝓝 0) ∧
      ∀ᶠ j in atTop,
        -(prefixPairDefect (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)-
          lowLoggedPacket (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)).re-
          (nativeSelbergBudget (3/2-rho.1.re) rho.1.im C j+
            prefixBudget (dyadicMomentOrder j)+lowOrderBudget (dyadicMomentOrder j))≤
        (((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse
          (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)
            (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  obtain ⟨C,hC,hcost,hfloor⟩ := exists_native_prefix_payment_simple
    rho hrho hexposed hm hU hy
  have hu : 1/2≤3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  refine ⟨C,hC,?_,?_⟩
  · simpa only [add_zero,Function.comp_def] using
      hcost.add (lowOrderBudget_tendsto.comp tendsto_dyadicMomentOrder)
  · filter_upwards [hfloor,tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (65536 : ℕ))] with j hj hN
    have hlow := prefix_re_le_sub_low hu hU hN hy
    linarith only [hj,hlow]

end RiemannGaussian.ZetaRieszPairLowOrderPayment
