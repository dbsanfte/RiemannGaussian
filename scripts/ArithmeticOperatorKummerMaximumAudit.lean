/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorKummerCutoff
import RiemannGaussian.ZetaPrimeMomentChebyshev
import RiemannGaussian.ZetaRieszPrimeCompletionPhase
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# All-split maximal Kummer-order gate

The maximum is taken at each literal integer denominator over every split
of one binomial row. This leaf does not assert a simultaneous maximizer for
different primes, or a binomial-row LCM identity. A common maximizer for all
nested powers of EACH prime is proved. All endpoints and all prime powers
are retained before the arbitrary-weight collapse audit.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical Topology
namespace RiemannGaussian.ArithmeticOperatorKummerMaximumAudit
open Complex Filter ArithmeticOperatorKummerCutoff SuzukiCarryCorrelation

/-- Maximum single-order carry over every split of a literal binomial row. -/
def rowMaxCarry (N d : ℕ) : ℕ :=
  (Finset.range (N+1)).sup (fun k => binomialCarry k (N-k) d)

/-- The carry records exactly a remainder borrow; no prime restriction is used. -/
theorem row_carry_eq_borrow {N k d : ℕ} (hk : k≤N) (hd : 0<d) :
    binomialCarry k (N-k) d=if N%d<k%d then 1 else 0 := by
  have hs : k+(N-k)=N := Nat.add_sub_of_le hk
  have hsum := Nat.add_mod k (N-k) d
  have hmodk := Nat.mod_lt k hd
  have hmodb := Nat.mod_lt (N-k) hd
  rw [hs] at hsum
  have hlow : k%d+(N-k)%d<d → N%d=k%d+(N-k)%d := by
    intro h
    rw [hsum,Nat.mod_eq_of_lt h]
  have hhigh : d≤k%d+(N-k)%d → N%d=k%d+(N-k)%d-d := by
    intro h
    rw [hsum,Nat.mod_eq_sub_mod h,Nat.mod_eq_of_lt (by omega)]
  unfold binomialCarry
  rw [Nat.add_div hd]
  split_ifs <;> first | (have := hhigh (by omega); omega) | (have := hlow (by omega); omega)

theorem row_carry_le_one {N k d : ℕ} (hk : k≤N) (hd : 0<d) :
    binomialCarry k (N-k) d≤1 := by
  rw [row_carry_eq_borrow hk hd]
  split_ifs <;> omega

/-- Every split vanishes at a divisor of the row successor. -/
theorem row_carry_zero_of_dvd {N k d : ℕ} (hk : k≤N) (hdiv : d∣N+1) :
    binomialCarry k (N-k) d=0 := by
  have hs : k+(N-k)=N := Nat.add_sub_of_le hk
  unfold binomialCarry
  rw [Nat.add_div_of_dvd_add_add_one (by simpa only [hs] using hdiv)]
  omega

theorem row_carry_zero_above {N k d : ℕ} (hk : k≤N) (hlarge : N<d) :
    binomialCarry k (N-k) d=0 := by
  have hs : k+(N-k)=N := Nat.add_sub_of_le hk
  simp [binomialCarry,hs,Nat.div_eq_of_lt hlarge,
    Nat.div_eq_of_lt (show k<d by omega),
    Nat.div_eq_of_lt (show N-k<d by omega)]

/-- One deterministic split attains the maximum whenever a borrow is possible. -/
theorem row_carry_witness {N d : ℕ} (hd : 0<d) (hdN : d≤N+1)
    (hdiv : ¬d∣N+1) :
    d-1≤N ∧ binomialCarry (d-1) (N-(d-1)) d=1 := by
  have hmod := Nat.mod_lt N hd
  have hm : N%d<d-1 := by
    have he := Nat.add_mod N 1 d
    by_cases hd1 : d=1
    · simp_all
    have hzero : (N+1)%d≠0 := by
      intro hm
      exact hdiv (Nat.dvd_of_mod_eq_zero hm)
    have hlast : N%d≠d-1 := by
      intro hl
      rw [hl,Nat.mod_eq_of_lt (by omega : 1<d)] at he
      have heq : d-1+1=d := by omega
      rw [heq,Nat.mod_self] at he
      exact hzero he
    omega
  refine ⟨by omega,?_⟩
  rw [row_carry_eq_borrow (by omega) hd,Nat.mod_eq_of_lt (by omega : d-1<d),
    ite_eq_left hm]

/-- Complete nonlinear maximum gate, valid for every positive integer denominator. -/
theorem rowMaxCarry_eq {N d : ℕ} (hd : 0<d) :
    rowMaxCarry N d=if d≤N+1 ∧ ¬d∣N+1 then 1 else 0 := by
  by_cases h : d≤N+1 ∧ ¬d∣N+1
  · rw [ite_eq_left h]
    apply Nat.le_antisymm
    · apply Finset.sup_le_iff.mpr
      intro k hk
      exact row_carry_le_one (by simp only [Finset.mem_range] at hk; omega) hd
    · obtain ⟨hk,he⟩ := row_carry_witness hd h.1 h.2
      have hw := Finset.le_sup (s := Finset.range (N+1))
        (f := fun k => binomialCarry k (N-k) d)
        (show d-1∈Finset.range (N+1) by simp only [Finset.mem_range]; omega)
      rw [he] at hw
      exact hw
  · rw [ite_eq_right h]
    apply Nat.eq_zero_of_le_zero
    apply Finset.sup_le_iff.mpr
    intro k hk
    have hkN : k≤N := by simp only [Finset.mem_range] at hk; omega
    by_cases hdiv : d∣N+1
    · rw [row_carry_zero_of_dvd hkN hdiv]
    · rw [row_carry_zero_above hkN (by omega)]

/-- Zero denominator is excluded from every actual prime-power packet. -/
theorem rowMaxCarry_zero (N : ℕ) : rowMaxCarry N 0=0 := by
  simp [rowMaxCarry,binomialCarry]

/-- Nested prime-power orders have a common split; this is stronger than separate maxima. -/
def primeWitness (p N : ℕ) : ℕ := p^(Nat.log p (N+1))-1

theorem primeWitness_le (p N : ℕ) : primeWitness p N≤N := by
  have he := Nat.pow_log_le_self p (by omega : N+1≠0)
  unfold primeWitness
  omega

/-- One literal split attains every orderwise maximum at a fixed prime, including higher orders. -/
theorem primeWitness_all_orders {p N : ℕ} (hp : p.Prime) (i : ℕ) :
    binomialCarry (primeWitness p N) (N-primeWitness p N) (p^i)=rowMaxCarry N (p^i) := by
  have hd : 0<p^i := Nat.pow_pos hp.pos
  have hw := primeWitness_le p N
  by_cases hi : i≤Nat.log p (N+1)
  · have hdv : p^i∣primeWitness p N+1 := by
      have hpow : 0<p^(Nat.log p (N+1)) := Nat.pow_pos hp.pos
      rw [primeWitness,show p^Nat.log p (N+1)-1+1=p^Nat.log p (N+1) by omega]
      exact Nat.pow_dvd_pow p hi
    have hm := (Nat.mod_eq_sub_iff (by norm_num : (0 : ℕ)<1) hd).mpr hdv
    have hbound : p^i≤N+1 :=
      (Nat.pow_le_pow_right hp.pos hi).trans (Nat.pow_log_le_self p (by omega))
    rw [row_carry_eq_borrow hw hd,hm,rowMaxCarry_eq hd]
    by_cases hdiv : p^i∣N+1
    · have hn := (Nat.mod_eq_sub_iff (by norm_num : (0 : ℕ)<1) hd).mpr hdiv
      simp [hn,hdiv]
    · have hn : N%p^i<p^i-1 := by
        have hlt := Nat.mod_lt N hd
        have hne : N%p^i≠p^i-1 := by
          intro h
          exact hdiv ((Nat.mod_eq_sub_iff (by norm_num : (0 : ℕ)<1) hd).mp h)
        omega
      simp [hn,hbound,hdiv]
  · have hlarge : N+1<p^i := by
      exact (Nat.log_lt_iff_lt_pow hp.one_lt (by omega : N+1≠0)).mp (by omega)
    rw [row_carry_zero_above hw (by omega),rowMaxCarry_eq hd,ite_eq_right (by omega)]

/-- Kummer's valuation count is the exact set of nonzero carry orders in this row. -/
theorem row_valuation_eq_carry_card {p N k B : ℕ} (hp : p.Prime) (hk : k≤N)
    (hB : Nat.log p N<B) :
    padicValNat p (N.choose (N-k))=
      ((Finset.Ico 1 B).filter (fun i => binomialCarry k (N-k) (p^i)=1)).card := by
  let : Fact p.Prime := ⟨hp⟩
  have hs : k+(N-k)=N := Nat.add_sub_of_le hk
  have hv := valuation_eq_carry_count (p := p) (a := k) (b := N-k) (B := B)
    (by simpa only [hs] using hB)
  rw [hs] at hv
  rw [hv]
  congr 1
  ext i
  have hc : binomialCarry k (N-k) (p^i)=
      if p^i≤(N-k)%p^i+k%p^i then 1 else 0 := by
    unfold binomialCarry
    rw [Nat.add_div (Nat.pow_pos hp.pos)]
    split_ifs <;> omega
  simp only [Finset.mem_filter,hc]
  split_ifs <;> simp_all

/-- All prime-power orders can be joined BEFORE the row maximum, without a compatibility loss. -/
theorem row_valuation_le_witness {p N k : ℕ} (hp : p.Prime) (hk : k≤N) :
    padicValNat p (N.choose (N-k))≤
      padicValNat p (N.choose (N-primeWitness p N)) := by
  rw [row_valuation_eq_carry_card hp hk (by omega : Nat.log p N<Nat.log p N+1),
    row_valuation_eq_carry_card hp (primeWitness_le p N)
      (by omega : Nat.log p N<Nat.log p N+1)]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi,hc⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨hi,?_⟩
  rw [primeWitness_all_orders hp]
  have hl := Finset.le_sup (s := Finset.range (N+1))
    (f := fun k => binomialCarry k (N-k) (p^i))
    (show k∈Finset.range (N+1) by simp only [Finset.mem_range]; omega)
  have hu := (Finset.sup_le_iff.mpr (fun k hk =>
    row_carry_le_one (by simp only [Finset.mem_range] at hk; omega) (Nat.pow_pos hp.pos)) :
    rowMaxCarry N (p^i)≤1)
  rw [hc] at hl
  exact Nat.le_antisymm hu hl

/-- The actual binomial valuation maximum has a literal simultaneous order witness. -/
theorem row_valuation_max_eq {p N : ℕ} (hp : p.Prime) :
    (Finset.range (N+1)).sup (fun k => padicValNat p (N.choose (N-k)))=
      padicValNat p (N.choose (N-primeWitness p N)) := by
  apply Nat.le_antisymm
  · apply Finset.sup_le_iff.mpr
    intro k hk
    exact row_valuation_le_witness hp (by simp only [Finset.mem_range] at hk; omega)
  · exact Finset.le_sup (f := fun k => padicValNat p (N.choose (N-k)))
      (show primeWitness p N∈Finset.range (N+1) by
      simp only [Finset.mem_range]
      have hw := primeWitness_le p N
      omega)

/-- Joined maximum packet; the nonlinear row operation precedes the denominator join. -/
def maxPacket (X : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ d∈Finset.Icc 1 X,(rowMaxCarry (X-1) d : ℂ)*w d

/-- The exact arbitrary-weight obstruction: only one prefix and one divisor endpoint remain. -/
theorem maxPacket_eq {X : ℕ} (hX : 0<X) (w : ℕ → ℂ) :
    maxPacket X w=(∑ d∈Finset.Icc 1 X,w d)-divisorObservation w X := by
  have he : (Finset.Icc 1 X).filter (fun d => d∣X)=X.divisors := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨_,hd⟩
      exact ⟨hd,hX.ne'⟩
    · rintro ⟨hd,_⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hX,Nat.le_of_dvd hX hd⟩,hd⟩
  have hm : maxPacket X w=∑ d∈Finset.Icc 1 X,
      (w d-if d∣X then w d else 0) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [rowMaxCarry_eq (Finset.mem_Icc.mp hd).1,
      show X-1+1=X by omega]
    have hle := (Finset.mem_Icc.mp hd).2
    split_ifs <;> simp_all
  rw [hm,Finset.sum_sub_distrib,←Finset.sum_filter,he]
  rfl

/-- An active denominator remains freely selectable: a joined maximum is not a weight constraint. -/
theorem maxPacket_delta {X d : ℕ} (hd : d∈Finset.Icc 1 X) (hdiv : ¬d∣X) (v : ℂ) :
    maxPacket X (fun n => if n=d then v else 0)=v := by
  unfold maxPacket
  rw [Finset.sum_eq_single d]
  · rw [rowMaxCarry_eq (Finset.mem_Icc.mp hd).1,show X-1+1=X by
      have hp := (Finset.mem_Icc.mp hd).1
      have hn := (Finset.mem_Icc.mp hd).2
      omega]
    simp [hdiv,(Finset.mem_Icc.mp hd).2]
  · intro n _ hnd
    simp [hnd]
  · intro h
    exact (h hd).elim

/-- Identity-only all-weight bounds fail at every nontrivial row, with the whole packet joined. -/
theorem no_free_weight_bound {X : ℕ} (hX : 2<X) (B : ℝ) :
    ¬∀ w : ℕ → ℂ,‖maxPacket X w‖≤B := by
  intro h
  have hnot : ¬X-1∣X := by
    intro hd
    have he := Nat.dvd_sub hd (dvd_refl (X-1))
    rw [show X-(X-1)=1 by omega] at he
    have hl := Nat.le_of_dvd (by norm_num : (0 : ℕ)<1) he
    omega
  have hm := maxPacket_delta (d := X-1)
    (by simp only [Finset.mem_Icc]; omega) hnot ((|B|+1 : ℝ) : ℂ)
  have hb := h (fun n => if n=X-1 then ((|B|+1 : ℝ) : ℂ) else 0)
  rw [hm,Complex.norm_real,Real.norm_of_nonneg (by positivity)] at hb
  linarith [le_abs_self B]

/-- Literal phased von Mangoldt weights, including all proper prime powers. -/
def actualWeight (y : ℝ) (d : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d

/-- The full fixed-height phase is never replaced by its norm in the identity. -/
theorem maxPacket_actual {X : ℕ} (hX : 0<X) (y : ℝ) :
    maxPacket X (actualWeight y)=
      (∑ d∈Finset.Icc 1 X,actualWeight y d)-divisorObservation (actualWeight y) X :=
  maxPacket_eq hX _

/-- Only the explicit divisor endpoint is independently paid. -/
theorem actual_endpoint_norm (X : ℕ) (y : ℝ) :
    ‖divisorObservation (actualWeight y) X‖≤Real.log X := by
  calc
    _ ≤ ∑ d∈X.divisors,‖actualWeight y d‖ := norm_sum_le _ _
    _ = ∑ d∈X.divisors,ArithmeticFunction.vonMangoldt d := by
      apply Finset.sum_congr rfl
      intro d _
      rw [actualWeight,norm_mul,norm_primePhase,Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,mul_one]
    _ = Real.log X := ArithmeticFunction.vonMangoldt_sum

/-- Nonlinear maximal carries leave the same twisted prefix, up to a logarithmic endpoint. -/
theorem actual_prefix_difference_norm {X : ℕ} (hX : 0<X) (y : ℝ) :
    ‖maxPacket X (actualWeight y)-(∑ d∈Finset.Icc 1 X,actualWeight y d)‖≤Real.log X := by
  rw [maxPacket_actual hX]
  simpa only [sub_sub_cancel_left,norm_neg] using actual_endpoint_norm X y

/-- In the untwisted row, ordinary integer factorization identifies the endpoint exactly. -/
theorem maxPacket_vonMangoldt {X : ℕ} (hX : 0<X) :
    maxPacket X (fun d => (ArithmeticFunction.vonMangoldt d : ℂ))=
      (Chebyshev.psi (X : ℝ)-Real.log X : ℝ) := by
  rw [maxPacket_eq hX,divisorObservation_vonMangoldt]
  have hi : Finset.Icc 1 X=Finset.Ioc 0 X := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_Ioc]
    omega
  rw [hi]
  simp only [Chebyshev.psi,Nat.floor_natCast,Complex.ofReal_sub,Complex.ofReal_sum]

open MeasureTheory Set
open ZetaPrimeMomentCoherence ZetaPrimeMomentChebyshev

/-- Exact logarithmic-coordinate divisor endpoint, not a smoothed replacement. -/
def endpointLog (t : ℝ) : ℝ :=
  Real.exp (-t)*Real.log (⌊Real.exp t⌋₊ : ℝ)

theorem endpointLog_bound {t : ℝ} (ht : 0≤t) :
    0≤endpointLog t ∧ endpointLog t≤t*Real.exp (-t) := by
  have hf : 1≤⌊Real.exp t⌋₊ := (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr ht)
  have hp : 0<(⌊Real.exp t⌋₊ : ℝ) := by exact_mod_cast (show 0<⌊Real.exp t⌋₊ by omega)
  have hl : Real.log (⌊Real.exp t⌋₊ : ℝ)≤t := by
    simpa only [Real.log_exp] using
      Real.log_le_log hp (Nat.floor_le (Real.exp_pos t).le)
  refine ⟨mul_nonneg (Real.exp_pos _).le (Real.log_natCast_nonneg _),?_⟩
  unfold endpointLog
  nlinarith only [mul_le_mul_of_nonneg_left hl (Real.exp_pos (-t)).le]

theorem measurable_endpointLog : Measurable endpointLog := by
  unfold endpointLog
  fun_prop

/-- The actual endpoint transform is analytic past the full source radius. -/
theorem integrable_endpointLog {x : ℝ} (hx : -1<x) :
    IntegrableOn (fun t : ℝ => endpointLog t*Real.exp (-x*t)) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => t*Real.exp (-(x+1)*t)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1)
        (by norm_num) (by norm_num) (by linarith : 0<x+1))
  apply hi.mono' ((measurable_endpointLog.mul (by fun_prop)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hb := endpointLog_bound ht.le
  calc
    ‖endpointLog t*Real.exp (-x*t)‖=
        endpointLog t*Real.exp (-x*t) :=
      Real.norm_of_nonneg (mul_nonneg hb.1 (Real.exp_pos _).le)
    _ ≤ (t*Real.exp (-t))*Real.exp (-x*t) :=
      mul_le_mul_of_nonneg_right hb.2 (Real.exp_pos _).le
    _ = t*Real.exp (-(x+1)*t) := by rw [mul_assoc,←Real.exp_add]; congr 2; ring

/-- The genuine endpoint, with the full fixed-height Laplace phase. -/
def endpointLaplace (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0,(endpointLog t : ℂ)*Complex.exp (-z*t)

/-- Normalized factorial moment of the actual floor-log endpoint. -/
def endpointMoment (k : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0,
    ((endpointLog t : ℂ)*(t : ℂ)^k*Complex.exp (-z*t))/(k.factorial : ℂ)

theorem endpoint_analytic_and_moments {z : ℂ} (hz : -1<z.re) :
    AnalyticAt ℂ endpointLaplace z ∧ ∀ k : ℕ,
      IntegrableOn (fun t : ℝ => (endpointLog t : ℂ)*(t : ℂ)^k*
        Complex.exp (-z*t)) (Ioi 0) ∧
      signedTaylorMoment k endpointLaplace z=endpointMoment k z :=
  signed_real_laplace_moments (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := endpointLog) measurable_endpointLog.aemeasurable
    (fun _ hx => integrable_endpointLog hx) hz

/-- Fixed-radius Cauchy estimate for this single actual endpoint, not a carrier envelope. -/
theorem endpointMoment_geometric (y : ℝ) :
    ∃ B : ℝ,0≤B ∧ ∀ k : ℕ,
      ‖endpointMoment k (center y-1)‖≤B/(5/4 : ℝ)^k := by
  have han : AnalyticOnNhd ℂ endpointLaplace (Metric.closedBall (center y-1) (5/4)) := by
    intro z hz
    have he := Complex.abs_re_le_norm (z-(center y-1))
    have hd : ‖z-(center y-1)‖≤5/4 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    have hc : (center y-1).re=1/2 := by norm_num [ZetaPrimeMomentCoherence.center]
    exact (endpoint_analytic_and_moments (by
      rw [Complex.sub_re,hc] at he
      have h := (abs_le.mp (he.trans hd)).1
      linarith)).1
  obtain ⟨B,hB⟩ := ((isCompact_closedBall (center y-1) (5/4)).image_of_continuousOn
    han.continuousOn).isBounded.exists_norm_le
  have hself : center y-1∈Metric.closedBall (center y-1) (5/4) :=
    Metric.mem_closedBall_self (by norm_num)
  refine ⟨B,(norm_nonneg _).trans (hB _ ⟨_,hself,rfl⟩),fun k => ?_⟩
  rw [←(endpoint_analytic_and_moments (by norm_num [ZetaPrimeMomentCoherence.center] :
    -1<(center y-1).re)).2 k |>.2]
  apply norm_signedTaylorMoment_le (by norm_num : (0 : ℝ)<5/4)
    (DifferentiableOn.diffContOnCl (by
      rw [closure_ball _ (by norm_num : (5/4 : ℝ)≠0)]
      exact han.differentiableOn))
  intro z hz
  exact hB _ ⟨z,Metric.sphere_subset_closedBall hz,rfl⟩

/-- The only discarded endpoint has a genuine geometric source-scale payment. -/
theorem endpointMoment_source_norm {u : ℝ} (hu : 0≤u) (y : ℝ) :
    ∃ B : ℝ,0≤B ∧ ∀ k : ℕ,
      ‖(u : ℂ)^k*endpointMoment k (center y-1)‖≤B*(u/(5/4))^k := by
  obtain ⟨B,hB,h⟩ := endpointMoment_geometric y
  refine ⟨B,hB,fun k => ?_⟩
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu]
  calc
    _ ≤ u^k*(B/(5/4)^k) := mul_le_mul_of_nonneg_left (h k) (pow_nonneg hu _)
    _ = _ := by simp only [div_pow]; field_simp

theorem endpointMoment_source_tendsto {u : ℝ} (hu : 0≤u) (hu1 : u<1) (y : ℝ) :
    Tendsto (fun k : ℕ => (u : ℂ)^k*endpointMoment k (center y-1)) atTop (𝓝 0) := by
  obtain ⟨B,hB,h⟩ := endpointMoment_source_norm hu y
  have hr : 0≤u/(5/4 : ℝ) := by positivity
  have hr1 : u/(5/4 : ℝ)<1 := (div_lt_one (by norm_num)).mpr (by linarith)
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).const_mul B
  exact squeeze_zero_norm (by intro k; exact h k) (by simpa only [mul_zero] using ht)

/-- The independently paid endpoint in the consecutive Chebyshev-error source moments. -/
def endpointSource (u y : ℝ) (k : ℕ) : ℂ :=
  (u : ℂ)^(k+2)*(center y*endpointMoment (k+1) (center y-1)-
    endpointMoment k (center y-1))

theorem endpointSource_tendsto {u : ℝ} (hu : 0≤u) (hu1 : u<1) (y : ℝ) :
    Tendsto (endpointSource u y) atTop (𝓝 0) := by
  have ht := endpointMoment_source_tendsto hu hu1 y
  have hs := ht.comp (tendsto_add_atTop_nat 1)
  have hm := (hs.const_mul ((u : ℂ)*center y)).sub (ht.const_mul ((u : ℂ)^2))
  simpa only [mul_zero,sub_zero] using hm.congr (fun k => by
    dsimp only [Function.comp_def,endpointSource]
    rw [pow_succ,pow_succ]
    ring)

/-- The maximal row is evaluated at the literal floor of the radial variable. -/
def maxLogError (t : ℝ) : ℝ :=
  Real.exp (-t)*(maxPacket ⌊Real.exp t⌋₊
    (fun d => (ArithmeticFunction.vonMangoldt d : ℂ))).re-1

theorem maxLogError_eq {t : ℝ} (ht : 0≤t) :
    maxLogError t=logError t-endpointLog t := by
  have hf : 0<⌊Real.exp t⌋₊ := Nat.floor_pos.mpr (Real.one_le_exp_iff.mpr ht)
  unfold maxLogError
  rw [maxPacket_vonMangoldt hf]
  simp only [Complex.ofReal_re,Chebyshev.psi,Nat.floor_natCast]
  unfold logError endpointLog
  simp only [Chebyshev.psi]
  ring

/-- All factorial orders and the full complex phase are retained. -/
def maxErrorMoment (k : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0,
    ((maxLogError t : ℂ)*(t : ℂ)^k*Complex.exp (-z*t))/(k.factorial : ℂ)

theorem maxErrorMoment_eq {z : ℂ} (hz : 0<z.re) (k : ℕ) :
    maxErrorMoment k z=errorMoment k z-endpointMoment k z := by
  have hreal := (analytic_errorLaplace_and_moments hz).2 k |>.1
  have hend := (endpoint_analytic_and_moments (by linarith)).2 k |>.1
  rw [maxErrorMoment,errorMoment,endpointMoment,
    ←integral_sub (hreal.div_const _) (hend.div_const _)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [maxLogError_eq ht.le,Complex.ofReal_sub]
  ring

/-- This is the same actual source detector, after one independently paid endpoint. -/
def maxErrorSource (u y : ℝ) (k : ℕ) : ℂ :=
  (u : ℂ)^(k+2)*(center y*maxErrorMoment (k+1) (center y-1)-
    maxErrorMoment k (center y-1))

theorem maxErrorSource_eq (u y : ℝ) (k : ℕ) :
    maxErrorSource u y k=errorSource u y k-endpointSource u y k := by
  rw [maxErrorSource,maxErrorMoment_eq (by norm_num [ZetaPrimeMomentCoherence.center]),
    maxErrorMoment_eq (by norm_num [ZetaPrimeMomentCoherence.center]),errorSource,endpointSource]
  ring

/-- No new non-coherence follows: the complete native maximum has exactly the old moment limit. -/
theorem maxErrorSource_tendsto_iff {u y : ℝ} (hu : 0≤u) (hu1 : u<1)
    (hy : 1≤|y|) (l : ℂ) :
    Tendsto (maxErrorSource u y) atTop (𝓝 l) ↔ Tendsto (moments u y) atTop (𝓝 l) := by
  have hp := endpointSource_tendsto hu hu1 y
  rw [←errorSource_tendsto_iff hu hu1 hy l]
  constructor
  · intro h
    simpa only [add_zero] using (h.add hp).congr (fun k => by rw [maxErrorSource_eq]; ring)
  · intro h
    simpa only [sub_zero] using (h.sub hp).congr (fun k => (maxErrorSource_eq u y k).symm)

/-- Every genuinely exposed actual source and its analytic multiplicity survive the maximum. -/
theorem max_actual_exposed_source (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re) (hy : 1≤|rho.1.im|)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖) :
    Tendsto (maxErrorSource (3/2-rho.1.re) rho.1.im) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  apply (maxErrorSource_tendsto_iff
    (by linarith [NontrivialZetaZero.re_lt_one rho]) (by linarith) hy _).mpr
  exact ZetaRieszPrimeCompletionPhase.tendsto_ordinary_prime_source rho hrho hexposed

/-- Conversely the maximum criterion still identifies the old actual zero, without exposure. -/
theorem max_source_identifies_actual_zero {u y : ℝ} (hu : 0<u) (hu1 : u<1)
    (hy : 1≤|y|) {m : ℕ} (hm : 0<m)
    (h : Tendsto (maxErrorSource u y) atTop (𝓝 (-(m : ℂ)))) :
    ∃ rho : NontrivialZetaZero,rho.1=candidate u y ∧ analyticZetaZeroMultiplicity rho=m :=
  exists_zero_multiplicity_of_tendsto hu hu1 hm
    ((maxErrorSource_tendsto_iff hu.le hu1 hy _).mp h)

end RiemannGaussian.ArithmeticOperatorKummerMaximumAudit

#lint+ in RiemannGaussian.ArithmeticOperatorKummerMaximumAudit

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    -- Module provenance also includes compiler helpers outside the user namespace.
    if env.isImportedConst n then continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty maximal-Kummer audit."
  logInfo m!"Maximal-Kummer audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-kummer-maximum"
  IO.FS.writeFile ".lake/arithmetic-operator-kummer-maximum/axioms.json"
    (Json.mkObj [("scope",toJson "all-split Kummer maxima and actual endpoint/source collapse"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
