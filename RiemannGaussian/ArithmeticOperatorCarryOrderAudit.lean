/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorKummerGcdAudit
import Mathlib.Data.Fintype.BigOperators

/-!
# Arbitrary correlated phases INSIDE every prime-power carry order

Keep every actual Kummer order before joining, with a code depending on
the entire tuple of different binomial-row orders. No factorization of
that code, independence of its phases, or replacement of prime powers
by their base is assumed. Above the physical square-root threshold all
active orders are exactly one. The extra channel has an explicit
square-root/polylogarithmic bound and therefore no nonzero power source.

The same source-gate failure holds for growing row count whenever the
tuple complexity (2J)^D is at most exp(J/4). The full signed first-order
packet remains UNPAID. Distinct prime columns, larger complexity and
unbounded order-code amplitudes are outside this scoped rejection.
-/

namespace RiemannGaussian.ArithmeticOperatorCarryOrderAudit
noncomputable section
open ArithmeticOperatorKummerPolynomialAudit Filter
open scoped BigOperators Classical Topology

/-- EVERY positive carry order in every literal binomial row. -/
def jointOrders {D : ℕ} (J p : ℕ) (a b : Fin D → ℕ) : Finset (Fin D → ℕ) :=
  Fintype.piFinset (fun i => carryOrders p (a i) (b i) J)

/-- The unique all-first-order tuple, including the empty-row convention. -/
def firstTuple (D : ℕ) : Fin D → ℕ := fun _ => 1

/-- All correlated order tuples BEFORE taking any norm or real part. -/
def jointCoefficient {D : ℕ} (J p : ℕ) (a b : Fin D → ℕ)
    (code : (Fin D → ℕ) → ℂ) : ℂ :=
  ∑ v∈jointOrders J p a b,code v

/-- The literal first-order mask; no higher carry is silently omitted. -/
def firstCoefficient {D : ℕ} (J p : ℕ) (a b : Fin D → ℕ)
    (code : (Fin D → ℕ) → ℂ) : ℂ :=
  if firstTuple D∈jointOrders J p a b then code (firstTuple D) else 0

/-- EXACT complementary order population, retaining every subset sign,
physical binomial endpoint, phase and correlated order mask. -/
def higherCoefficient {D : ℕ} (J p : ℕ) (a b : Fin D → ℕ)
    (code : (Fin D → ℕ) → ℂ) : ℂ :=
  ∑ v∈(jointOrders J p a b).erase (firstTuple D),code v

/-- First gate: finite integer identity for ANY joint code. -/
theorem jointCoefficient_eq_first_add_higher {D : ℕ} (J p : ℕ) (a b : Fin D → ℕ)
    (code : (Fin D → ℕ) → ℂ) :
    jointCoefficient J p a b code=firstCoefficient J p a b code+higherCoefficient J p a b code := by
  unfold jointCoefficient firstCoefficient higherCoefficient
  by_cases hv : firstTuple D∈jointOrders J p a b
  · rw [ite_eq_left hv,←Finset.sum_erase_add _ _ hv,add_comm]
  · simp only [ite_eq_right hv,Finset.erase_eq_of_notMem hv,zero_add]

/-- The first mask is an exact quotient/remainder test on every row. -/
theorem firstTuple_mem_iff {D J : ℕ} (hJ : 0<J) (p : ℕ) (a b : Fin D → ℕ) :
    firstTuple D∈jointOrders J p a b ↔ ∀ i,p≤b i%p+a i%p := by
  have he : 1<2*J+1 := by omega
  simp [jointOrders,Fintype.mem_piFinset,firstTuple,carryOrders,he]

/-- Count of ALL joint carry tuples, not a truncation of orders. -/
theorem card_jointOrders_le {D J p : ℕ} (hp : p.Prime) (a b : Fin D → ℕ)
    (hab : ∀ i,a i+b i≤2^(2*J)) :
    (jointOrders J p a b).card≤(2*J)^D := by
  rw [jointOrders,Fintype.card_piFinset]
  calc
    _ ≤ ∏ _i : Fin D,2*J := Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
      (fun i _ => by rw [←valuation_eq_card hp (hab i)]; exact valuation_le_orders hp (hab i))
    _ = _ := by simp

/-- At unit code the joined object is the product of the ACTUAL
binomial valuations, not a smooth or freely prescribed divisor row. -/
theorem jointCoefficient_one {D J p : ℕ} (hp : p.Prime) (a b : Fin D → ℕ)
    (hab : ∀ i,a i+b i≤2^(2*J)) :
    jointCoefficient J p a b (fun _ => 1)=((∏ i : Fin D,valuation p (a i) (b i) : ℕ) : ℂ) := by
  simp only [jointCoefficient,Finset.sum_const,nsmul_eq_mul,mul_one]
  congr 1
  rw [jointOrders,Fintype.card_piFinset]
  exact Finset.prod_congr rfl (fun i _ => (valuation_eq_card hp (hab i)).symm)

/-- All large-prime joint order vectors are the SAME first-order vector,
even with different rows and completely nonseparable codes. -/
theorem jointOrders_large_prime {D J p : ℕ} (hp : p.Prime) (a b : Fin D → ℕ)
    (hab : ∀ i,a i+b i≤2^(2*J)) (hlarge : 2^J<p) :
    jointOrders J p a b ⊆ {firstTuple D} := by
  intro v hv
  apply Finset.mem_singleton.mpr
  funext i
  exact Finset.mem_singleton.mp (carryOrders_large_prime hp (hab i) hlarge
    (Fintype.mem_piFinset.mp hv i))

/-- The extra-order channel is EXACTLY zero beyond the square root. -/
theorem higherCoefficient_large_prime_zero {D J p : ℕ} (hp : p.Prime) (a b : Fin D → ℕ)
    (hab : ∀ i,a i+b i≤2^(2*J)) (hlarge : 2^J<p)
    (code : (Fin D → ℕ) → ℂ) : higherCoefficient J p a b code=0 := by
  have he : (jointOrders J p a b).erase (firstTuple D)=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hne,hv⟩ := Finset.mem_erase.mp hv
    exact hne (Finset.mem_singleton.mp (jointOrders_large_prime hp a b hab hlarge hv))
  simp [higherCoefficient,he]

/-- A code can put the FULL height phase on each separate prime POWER.
No base-phase approximation or complete-leg phase limit is used. -/
def orderPhase {D : ℕ} (y : Fin D → ℝ) (p : ℕ) (v : Fin D → ℕ) : ℂ :=
  ∏ i : Fin D,SuzukiCarryCorrelation.primePhase (y i) (p^(v i))

theorem norm_orderPhase {D : ℕ} (y : Fin D → ℝ) (p : ℕ) (v : Fin D → ℕ) :
    ‖orderPhase y p v‖=1 := by
  simp [orderPhase,norm_prod,SuzukiCarryCorrelation.norm_primePhase]

/-- The quantitative budget is uniform in EVERY correlated order mask
and modular/height phase whose joined coefficient is unit-bounded. -/
theorem norm_higherCoefficient_le {D J p : ℕ} (hp : p.Prime) (a b : Fin D → ℕ)
    (hab : ∀ i,a i+b i≤2^(2*J)) (code : (Fin D → ℕ) → ℂ)
    (hcode : ∀ v∈jointOrders J p a b,‖code v‖≤1) :
    ‖higherCoefficient J p a b code‖≤((2*J : ℕ) : ℝ)^D := by
  unfold higherCoefficient
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _v∈(jointOrders J p a b).erase (firstTuple D),(1 : ℝ) :=
      Finset.sum_le_sum (fun v hv => hcode v (Finset.mem_erase.mp hv).2)
    _ = ((jointOrders J p a b).erase (firstTuple D)).card := by simp
    _ ≤ ((2*J : ℕ) : ℝ)^D := by
      exact_mod_cast (Finset.card_le_card (Finset.erase_subset _ _)).trans
        (card_jointOrders_le hp a b hab)

/-- Full marked-prime packet with ALL its actual order tuples. -/
def jointPacket {D : ℕ} (P : Finset ℕ) (J : ℕ) (a b : Fin D → ℕ)
    (code : ℕ → (Fin D → ℕ) → ℂ) : ℂ :=
  ∑ p∈P,(Real.log p : ℂ)*jointCoefficient J p a b (code p)

/-- The retained signed first-carry population is explicitly UNPAID. -/
def firstPacket {D : ℕ} (P : Finset ℕ) (J : ℕ) (a b : Fin D → ℕ)
    (code : ℕ → (Fin D → ℕ) → ℂ) : ℂ :=
  ∑ p∈P,(Real.log p : ℂ)*firstCoefficient J p a b (code p)

/-- Only the extra tuple-order channel. -/
def higherPacket {D : ℕ} (P : Finset ℕ) (J : ℕ) (a b : Fin D → ℕ)
    (code : ℕ → (Fin D → ℕ) → ℂ) : ℂ :=
  ∑ p∈P,(Real.log p : ℂ)*higherCoefficient J p a b (code p)

theorem jointPacket_eq_first_add_higher {D : ℕ} (P : Finset ℕ) (J : ℕ)
    (a b : Fin D → ℕ) (code : ℕ → (Fin D → ℕ) → ℂ) :
    jointPacket P J a b code=firstPacket P J a b code+higherPacket P J a b code := by
  unfold jointPacket firstPacket higherPacket
  rw [←Finset.sum_add_distrib]
  simp_rw [jointCoefficient_eq_first_add_higher,mul_add]

/-- Centering away the all-first-order tuple removes the ENTIRE retained
source channel, not merely density. No order tuple is discarded by norm. -/
theorem jointPacket_eq_higher_of_first_zero {D : ℕ} (P : Finset ℕ) (J : ℕ)
    (a b : Fin D → ℕ) (code : ℕ → (Fin D → ℕ) → ℂ)
    (hfirst : ∀ p∈P,code p (firstTuple D)=0) :
    jointPacket P J a b code=higherPacket P J a b code := by
  rw [jointPacket_eq_first_add_higher]
  have hf : firstPacket P J a b code=0 := by
    unfold firstPacket
    apply Finset.sum_eq_zero
    intro p hp
    simp [firstCoefficient,hfirst p hp]
  rw [hf,zero_add]

/-- No higher order outside the literal small-prime population occurs. -/
theorem higherPacket_eq_small {D J : ℕ} (P : Finset ℕ) (hP : ∀ p∈P,p.Prime)
    (a b : Fin D → ℕ) (hab : ∀ i,a i+b i≤2^(2*J))
    (code : ℕ → (Fin D → ℕ) → ℂ) :
    higherPacket P J a b code=higherPacket (P.filter (fun p => p≤2^J)) J a b code := by
  unfold higherPacket
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hnot
  have hlarge : 2^J<p := by
    by_contra hh
    exact hnot (Finset.mem_filter.mpr ⟨hp,by omega⟩)
  rw [higherCoefficient_large_prime_zero (hP p hp) a b hab hlarge,mul_zero]

/-- Source-sensitive finite estimate. No actual-prime PNT or generic
absolute whole-carrier allowance enters this higher-order payment. -/
theorem norm_higherPacket_le {D J : ℕ} (P : Finset ℕ) (hP : ∀ p∈P,p.Prime)
    (a b : Fin D → ℕ) (hab : ∀ i,a i+b i≤2^(2*J))
    (code : ℕ → (Fin D → ℕ) → ℂ)
    (hcode : ∀ p∈P,∀ v∈jointOrders J p a b,‖code p v‖≤1) :
    ‖higherPacket P J a b code‖≤
      (2 : ℝ)^J*((2*J : ℕ) : ℝ)^(D+1)*Real.log 2 := by
  rw [higherPacket_eq_small P hP a b hab]
  let Q := P.filter (fun p => p≤2^J)
  have hcard : (Q.card : ℝ)≤(2 : ℝ)^J := by
    have hs : Q ⊆ Finset.Icc 1 (2^J) := by
      intro p hp
      obtain ⟨hp,hpb⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨(hP p hp).pos,hpb⟩
    exact_mod_cast (by simpa using Finset.card_le_card hs : Q.card≤2^J)
  have hterm (p : ℕ) (hp : p∈Q) :
      ‖(Real.log p : ℂ)*higherCoefficient J p a b (code p)‖≤
        ((2*J : ℕ) : ℝ)^(D+1)*Real.log 2 := by
    have hpP := (Finset.mem_filter.mp hp).1
    have hpS := (Finset.mem_filter.mp hp).2
    have hlog : ‖(Real.log p : ℂ)‖≤((2*J : ℕ) : ℝ)*Real.log 2 := by
      rw [Complex.norm_real,Real.norm_of_nonneg (Real.log_natCast_nonneg p)]
      have hpX : p≤2^(2*J) := hpS.trans (by
        apply Nat.pow_le_pow_right (by omega : 0<(2 : ℕ)); omega)
      have hh := Real.log_le_log (by exact_mod_cast (hP p hpP).pos : (0 : ℝ)<p)
        (by exact_mod_cast hpX : (p : ℝ)≤(2 : ℝ)^(2*J))
      simpa only [Real.log_pow] using hh
    rw [norm_mul]
    apply (mul_le_mul hlog (norm_higherCoefficient_le (hP p hpP) a b hab
      (code p) (hcode p hpP)) (norm_nonneg _) (by positivity)).trans_eq
    rw [pow_succ]
    ring
  unfold higherPacket
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _p∈Q,((2*J : ℕ) : ℝ)^(D+1)*Real.log 2 := Finset.sum_le_sum hterm
    _ = (Q.card : ℝ)*(((2*J : ℕ) : ℝ)^(D+1)*Real.log 2) := by simp
    _ ≤ _ := by
      calc
        _ ≤ (2 : ℝ)^J*(((2*J : ℕ) : ℝ)^(D+1)*Real.log 2) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by ring

/-- Higher-order phase information loses the campaign source at every
FIXED number of rows, with no order or physical-mask approximation. -/
theorem tendsto_scaled_higherPacket {D : ℕ} (P : ℕ → Finset ℕ)
    (a b : ℕ → Fin D → ℕ) (code : ℕ → ℕ → (Fin D → ℕ) → ℂ)
    (hP : ∀ J p,p∈P J → p.Prime) (hab : ∀ J i,a J i+b J i≤2^(2*J))
    (hcode : ∀ J p,p∈P J → ∀ v∈jointOrders J p (a J) (b J),‖code J p v‖≤1)
    {beta : ℝ} (hbeta : 1/2<beta) :
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      higherPacket (P J) J (a J) (b J) (code J)) atTop (𝓝 0) := by
  let r := Real.exp ((1-2*beta)*Real.log 2)
  have hr0 : 0≤r := (Real.exp_pos _).le
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (by linarith) (Real.log_pos (by norm_num)))
  have he : Real.exp (-2*beta*Real.log 2)*2=r := by
    calc
      _ = Real.exp (-2*beta*Real.log 2)*Real.exp (Real.log 2) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ)<2)]
      _ = _ := by dsimp [r];rw [←Real.exp_add];congr 1;ring
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one (D+1) hr0 hr1).const_mul
    ((2 : ℝ)^(D+1)*Real.log 2)
  simp only [mul_zero] at ht
  apply squeeze_zero_norm (a := fun J : ℕ =>
    ((2 : ℝ)^(D+1)*Real.log 2)*((J : ℝ)^(D+1)*r^J)) _ ht
  intro J
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  apply (mul_le_mul_of_nonneg_left
    (norm_higherPacket_le (P J) (hP J) (a J) (b J) (hab J) (code J) (hcode J))
    (by positivity)).trans_eq
  rw [←he,mul_pow]
  push_cast
  rw [mul_pow]
  ring

/-- No nonzero zero-source response can occur in the new bounded
order-correlated channel. Stop this candidate at its source gate. -/
theorem no_nonzero_higher_source {D : ℕ} (P : ℕ → Finset ℕ)
    (a b : ℕ → Fin D → ℕ) (code : ℕ → ℕ → (Fin D → ℕ) → ℂ)
    (hP : ∀ J p,p∈P J → p.Prime) (hab : ∀ J i,a J i+b J i≤2^(2*J))
    (hcode : ∀ J p,p∈P J → ∀ v∈jointOrders J p (a J) (b J),‖code J p v‖≤1)
    {beta : ℝ} (hbeta : 1/2<beta) {v : ℂ} (hv : v≠0) :
    ¬Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      higherPacket (P J) J (a J) (b J) (code J)) atTop (𝓝 v) := by
  intro hh
  exact hv (tendsto_nhds_unique hh (tendsto_scaled_higherPacket P a b code hP hab hcode hbeta))

/-- Source is conserved wholly in the retained first-carry packet.
The extra phase/order information cannot change that source at fixed D. -/
theorem tendsto_scaled_joint_iff_first {D : ℕ} (P : ℕ → Finset ℕ)
    (a b : ℕ → Fin D → ℕ) (code : ℕ → ℕ → (Fin D → ℕ) → ℂ)
    (hP : ∀ J p,p∈P J → p.Prime) (hab : ∀ J i,a J i+b J i≤2^(2*J))
    (hcode : ∀ J p,p∈P J → ∀ v∈jointOrders J p (a J) (b J),‖code J p v‖≤1)
    {beta : ℝ} (hbeta : 1/2<beta) (v : ℂ) :
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      jointPacket (P J) J (a J) (b J) (code J)) atTop (𝓝 v) ↔
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      firstPacket (P J) J (a J) (b J) (code J)) atTop (𝓝 v) := by
  have hc := tendsto_scaled_higherPacket P a b code hP hab hcode hbeta
  constructor
  · intro hh
    have ht := hh.sub hc
    simp only [sub_zero] at ht
    apply ht.congr
    intro J
    rw [jointPacket_eq_first_add_higher]
    ring
  · intro hh
    have ht := hh.add hc
    simp only [add_zero] at ht
    apply ht.congr
    intro J
    rw [jointPacket_eq_first_add_higher]
    ring

/-- Explicit complexity criterion allowing a growing number of rows.
No floor replacement of D or of the actual carry orders is used. -/
theorem tuple_complexity_le_exp {D J : ℕ} (hJ : 0<J)
    (hD : (D : ℝ)*Real.log ((2*J : ℕ) : ℝ)≤(J : ℝ)/4) :
    ((2*J : ℕ) : ℝ)^D≤Real.exp ((J : ℝ)/4) := by
  have hp : (0 : ℝ)<(2*J : ℕ) := by exact_mod_cast (show 0<2*J by omega)
  calc
    _ = Real.exp ((D : ℝ)*Real.log ((2*J : ℕ) : ℝ)) := by
      rw [Real.exp_nat_mul,Real.exp_log hp]
    _ ≤ _ := Real.exp_le_exp.mpr hD

/-- Finite quantitative payment at GROWING tuple complexity. -/
theorem norm_scaled_higherPacket_le_of_complexity {D J : ℕ} (P : Finset ℕ)
    (hP : ∀ p∈P,p.Prime) (a b : Fin D → ℕ) (hab : ∀ i,a i+b i≤2^(2*J))
    (code : ℕ → (Fin D → ℕ) → ℂ)
    (hcode : ∀ p∈P,∀ v∈jointOrders J p a b,‖code p v‖≤1)
    (hD : ((2*J : ℕ) : ℝ)^D≤Real.exp ((J : ℝ)/4)) (beta : ℝ) :
    ‖(Real.exp (-2*beta*Real.log 2)^J : ℂ)*higherPacket P J a b code‖≤
      (2*Real.log 2)*(J : ℝ)*(Real.exp ((1-2*beta)*Real.log 2+1/4))^J := by
  have he : Real.exp (-2*beta*Real.log 2)*2*Real.exp (1/4)=
      Real.exp ((1-2*beta)*Real.log 2+1/4) := by
    calc
      _ = Real.exp (-2*beta*Real.log 2)*Real.exp (Real.log 2)*Real.exp (1/4) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ)<2)]
      _ = _ := by
        rw [←Real.exp_add,←Real.exp_add]
        congr 1
        ring
  have hpow : Real.exp ((J : ℝ)/4)=(Real.exp (1/4))^J := by
    rw [show (J : ℝ)/4=(J : ℝ)*(1/4) by ring,Real.exp_nat_mul]
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ (Real.exp (-2*beta*Real.log 2))^J*
        ((2 : ℝ)^J*((2*J : ℕ) : ℝ)^(D+1)*Real.log 2) :=
      mul_le_mul_of_nonneg_left (norm_higherPacket_le P hP a b hab code hcode) (by positivity)
    _ ≤ (Real.exp (-2*beta*Real.log 2))^J*
        ((2 : ℝ)^J*(Real.exp ((J : ℝ)/4)*((2*J : ℕ) : ℝ))*Real.log 2) := by
      rw [pow_succ]
      gcongr
    _ = _ := by
      rw [hpow,←he,mul_pow,mul_pow]
      push_cast
      ring

/-- The campaign has a concrete geometric margin even at growing row
count, provided its exact tuple budget is exp(J/4) or less. -/
theorem campaign_rate_le_three_quarters {beta : ℝ} (hb : 19999/20000≤beta) :
    Real.exp ((1-2*beta)*Real.log 2+1/4)≤3/4 := by
  have hl : 2/3≤Real.log (2 : ℝ) := by linarith [Real.log_two_gt_d9]
  have he : (1-2*beta)*Real.log 2+1/4≤-(1/3 : ℝ) := by
    have hm := mul_le_mul_of_nonpos_left hl (show 1-2*beta≤0 by linarith)
    nlinarith
  have hexp : 4/3≤Real.exp (1/3 : ℝ) := by linarith [Real.add_one_le_exp (1/3 : ℝ)]
  calc
    _ ≤ Real.exp (-(1/3 : ℝ)) := Real.exp_le_exp.mpr he
    _ ≤ 3/4 := by
      rw [Real.exp_neg,←one_div]
      have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<4/3) hexp
      norm_num at hh
      simpa only [one_div] using hh

/-- Campaign payment with an explicit fixed rational geometric factor. -/
theorem norm_scaled_higherPacket_campaign {D J : ℕ} (P : Finset ℕ)
    (hP : ∀ p∈P,p.Prime) (a b : Fin D → ℕ) (hab : ∀ i,a i+b i≤2^(2*J))
    (code : ℕ → (Fin D → ℕ) → ℂ)
    (hcode : ∀ p∈P,∀ v∈jointOrders J p a b,‖code p v‖≤1)
    (hD : ((2*J : ℕ) : ℝ)^D≤Real.exp ((J : ℝ)/4)) {beta : ℝ}
    (hb : 19999/20000≤beta) :
    ‖(Real.exp (-2*beta*Real.log 2)^J : ℂ)*higherPacket P J a b code‖≤
      (2*Real.log 2)*(J : ℝ)*(3/4 : ℝ)^J := by
  apply (norm_scaled_higherPacket_le_of_complexity P hP a b hab code hcode hD beta).trans
  apply mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Real.exp_pos _).le (campaign_rate_le_three_quarters hb) J)
    (by positivity)

/-- The WHOLE centered order contrast has a geometric arithmetic bound,
but consequently cannot be an off-line source detector in this class. -/
theorem norm_scaled_centeredPacket_campaign {D J : ℕ} (P : Finset ℕ)
    (hP : ∀ p∈P,p.Prime) (a b : Fin D → ℕ) (hab : ∀ i,a i+b i≤2^(2*J))
    (code : ℕ → (Fin D → ℕ) → ℂ)
    (hcode : ∀ p∈P,∀ v∈jointOrders J p a b,‖code p v‖≤1)
    (hfirst : ∀ p∈P,code p (firstTuple D)=0)
    (hD : ((2*J : ℕ) : ℝ)^D≤Real.exp ((J : ℝ)/4)) {beta : ℝ}
    (hb : 19999/20000≤beta) :
    ‖(Real.exp (-2*beta*Real.log 2)^J : ℂ)*jointPacket P J a b code‖≤
      (2*Real.log 2)*(J : ℝ)*(3/4 : ℝ)^J := by
  rw [jointPacket_eq_higher_of_first_zero P J a b code hfirst]
  exact norm_scaled_higherPacket_campaign P hP a b hab code hcode hD hb

/-- Actual source-normalized geometric payment over a growing family. -/
theorem tendsto_scaled_higherPacket_growing (D : ℕ → ℕ) (P : ℕ → Finset ℕ)
    (a b : ∀ J,Fin (D J) → ℕ) (code : ∀ J,ℕ → (Fin (D J) → ℕ) → ℂ)
    (hP : ∀ J p,p∈P J → p.Prime) (hab : ∀ J i,a J i+b J i≤2^(2*J))
    (hcode : ∀ J p,p∈P J → ∀ v∈jointOrders J p (a J) (b J),‖code J p v‖≤1)
    (hD : ∀ᶠ J : ℕ in atTop,((2*J : ℕ) : ℝ)^(D J)≤Real.exp ((J : ℝ)/4))
    {beta : ℝ} (hbeta : 3/4<beta) :
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      higherPacket (P J) J (a J) (b J) (code J)) atTop (𝓝 0) := by
  let r := Real.exp ((1-2*beta)*Real.log 2+1/4)
  have hr0 : 0≤r := (Real.exp_pos _).le
  have hr1 : r<1 := by
    apply Real.exp_lt_one_iff.mpr
    have hl : 1/2<Real.log (2 : ℝ) := by linarith [Real.log_two_gt_d9]
    have hm := mul_lt_mul_of_neg_left hl (show 1-2*beta<0 by linarith)
    linarith
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one 1 hr0 hr1).const_mul (2*Real.log 2)
  simp only [pow_one,mul_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [hD] with J hDJ
  simpa only [r,mul_assoc] using norm_scaled_higherPacket_le_of_complexity
    (P J) (hP J) (a J) (b J) (hab J) (code J) (hcode J) hDJ beta

/-- Increasing rows within the stated tuple budget still cannot restore
a nonzero extra source. The first-order packet remains explicitly unpaid. -/
theorem no_nonzero_higher_source_growing (D : ℕ → ℕ) (P : ℕ → Finset ℕ)
    (a b : ∀ J,Fin (D J) → ℕ) (code : ∀ J,ℕ → (Fin (D J) → ℕ) → ℂ)
    (hP : ∀ J p,p∈P J → p.Prime) (hab : ∀ J i,a J i+b J i≤2^(2*J))
    (hcode : ∀ J p,p∈P J → ∀ v∈jointOrders J p (a J) (b J),‖code J p v‖≤1)
    (hD : ∀ᶠ J : ℕ in atTop,((2*J : ℕ) : ℝ)^(D J)≤Real.exp ((J : ℝ)/4))
    {beta : ℝ} (hbeta : 3/4<beta) {v : ℂ} (hv : v≠0) :
    ¬Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      higherPacket (P J) J (a J) (b J) (code J)) atTop (𝓝 v) := by
  intro hh
  exact hv (tendsto_nhds_unique hh
    (tendsto_scaled_higherPacket_growing D P a b code hP hab hcode hD hbeta))

/-- A source-detector centered on first-order cancellation has lost the
matched power source, even with the stated growing correlated tuple budget. -/
theorem no_nonzero_centered_order_source (D : ℕ → ℕ) (P : ℕ → Finset ℕ)
    (a b : ∀ J,Fin (D J) → ℕ) (code : ∀ J,ℕ → (Fin (D J) → ℕ) → ℂ)
    (hP : ∀ J p,p∈P J → p.Prime) (hab : ∀ J i,a J i+b J i≤2^(2*J))
    (hcode : ∀ J p,p∈P J → ∀ v∈jointOrders J p (a J) (b J),‖code J p v‖≤1)
    (hfirst : ∀ J p,p∈P J → code J p (firstTuple (D J))=0)
    (hD : ∀ᶠ J : ℕ in atTop,((2*J : ℕ) : ℝ)^(D J)≤Real.exp ((J : ℝ)/4))
    {beta : ℝ} (hbeta : 3/4<beta) {v : ℂ} (hv : v≠0) :
    ¬Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      jointPacket (P J) J (a J) (b J) (code J)) atTop (𝓝 v) := by
  simp only [jointPacket_eq_higher_of_first_zero (P _) _ (a _) (b _) (code _) (hfirst _)]
  exact no_nonzero_higher_source_growing D P a b code hP hab hcode hD hbeta hv

/-- Even growing complexity in the paid range conserves the entire
source in the old first-order packet, for arbitrary original joint codes. -/
theorem tendsto_scaled_joint_growing_iff_first (D : ℕ → ℕ) (P : ℕ → Finset ℕ)
    (a b : ∀ J,Fin (D J) → ℕ) (code : ∀ J,ℕ → (Fin (D J) → ℕ) → ℂ)
    (hP : ∀ J p,p∈P J → p.Prime) (hab : ∀ J i,a J i+b J i≤2^(2*J))
    (hcode : ∀ J p,p∈P J → ∀ v∈jointOrders J p (a J) (b J),‖code J p v‖≤1)
    (hD : ∀ᶠ J : ℕ in atTop,((2*J : ℕ) : ℝ)^(D J)≤Real.exp ((J : ℝ)/4))
    {beta : ℝ} (hbeta : 3/4<beta) (v : ℂ) :
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      jointPacket (P J) J (a J) (b J) (code J)) atTop (𝓝 v) ↔
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      firstPacket (P J) J (a J) (b J) (code J)) atTop (𝓝 v) := by
  have hc := tendsto_scaled_higherPacket_growing D P a b code hP hab hcode hD hbeta
  constructor
  · intro hh
    have ht := hh.sub hc
    simp only [sub_zero] at ht
    apply ht.congr
    intro J
    rw [jointPacket_eq_first_add_higher]
    ring
  · intro hh
    have ht := hh.add hc
    simp only [add_zero] at ht
    apply ht.congr
    intro J
    rw [jointPacket_eq_first_add_higher]
    ring

end
end RiemannGaussian.ArithmeticOperatorCarryOrderAudit
