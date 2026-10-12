/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorTwistedBulkAudit
import RiemannGaussian.ArithmeticOperatorCommutatorAudit
import RiemannGaussian.ArithmeticOperatorGammaTwistAudit
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# Actual Mobius coprimality is source-sensitive, but is not a PSD constraint

The complete finite primitive-pair lattice, with its exact diagonal
included, joins to mu(d)*d^(-iy)*floor(X/d)*(floor(X/d)+1).
Its genuine Euler response is 2*zeta(s-1)/zeta(s+iy). The actual
matched zero gives a nonzero singularity of its full analytic order;
the density pole can be removed without removing that source.

The literal coprimality matrix, however, has negative quadratic forms
on two distinct actual-prime rows beyond every head. The full phase is
retained. This rejects unrestricted Mobius-GCD PSD, not a specially
restricted signed packet or a new actual Mobius cancellation estimate.
-/

namespace RiemannGaussian.ArithmeticOperatorMoebiusCoprimeAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorGcdAudit ArithmeticOperatorGramAudit
open ArithmeticOperatorGammaTwistAudit ArithmeticOperatorCommutatorAudit
open ArithmeticOperatorDilationAudit SuzukiCarryCorrelation
open scoped BigOperators Topology ComplexConjugate Classical

/-- Unaltered integer Mobius, including its exact zero proper powers. -/
def mu (d : ℕ) : ℂ := (ArithmeticFunction.moebius d : ℂ)

/-- Full phase on the actual Mobius denominator. -/
def column (y : ℝ) (d : ℕ) : ℂ := mu d*primePhase y d

/-- Twice every physical cofactor index. No endpoint is deleted. -/
def twoIndex (a : ℕ) : ℂ := 2*(a : ℂ)

/-- Exact shell coefficient of the primitive lattice plus its diagonal. -/
def shell (y : ℝ) : ℕ → ℂ := LSeries.convolution (column y) twoIndex

/-- Both original integer rows and the literal diagonal remain. -/
def nativePacket (y : ℝ) (X : ℕ) : ℂ :=
  gcdQuadratic X (fun _ => 1) (column y)+
    ∑ n ∈ Finset.Icc 1 X,gcdKernel (column y) n n

/-- Arbitrary-column counterpart, solely for the collapse audit. -/
def freePacket (X : ℕ) (w : ℕ → ℂ) : ℂ :=
  gcdQuadratic X (fun _ => 1) w+∑ n ∈ Finset.Icc 1 X,gcdKernel w n n

private theorem feature_prefix (X d : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,divisorFeature n d)=((X/d : ℕ) : ℂ) := by
  have he : (Finset.Icc 1 X).filter (fun n => d∣n)=
      (Finset.range (X+1)).filter (fun n => n≠0 ∧ d∣n) := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_range]
    omega
  unfold divisorFeature
  rw [← Finset.sum_filter,he]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,Nat.card_multiples']

/-- Actual square floor from joining BOTH rows; no mean completion. -/
theorem quadratic_eq_floor (X : ℕ) (w : ℕ → ℂ) :
    gcdQuadratic X (fun _ => 1) w =
      ∑ d ∈ Finset.Icc 1 X,w d*((X/d : ℕ) : ℂ)^2 := by
  rw [gcdQuadratic_eq_joined,joinedGram_eq]
  apply Finset.sum_congr rfl
  intro d _
  simp only [gramKernel,one_mul,feature_prefix,Complex.norm_natCast]
  push_cast
  rfl

/-- The diagonal has its own exact floor, not an anonymous error. -/
theorem diagonal_eq_floor (X : ℕ) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 X,gcdKernel w n n) =
      ∑ d ∈ Finset.Icc 1 X,w d*((X/d : ℕ) : ℂ) := by
  have he (n : ℕ) (hn : n∈Finset.Icc 1 X) :
      gcdKernel w n n=∑ d ∈ Finset.Icc 1 X,w d*divisorFeature n d := by
    rw [gcdKernel_eq_incidence (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2]
    apply Finset.sum_congr rfl
    intro d _
    simp only [divisorFeature]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl he,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.mul_sum,feature_prefix]

/-- Exact signed scalar join for arbitrary weights. Actual Mobius is
only one specialization; no free control satisfies its arithmetic data. -/
theorem freePacket_eq_scalar (X : ℕ) (w : ℕ → ℂ) :
    freePacket X w=∑ d ∈ Finset.Icc 1 X,w d*
      (((X/d : ℕ) : ℂ)*(((X/d : ℕ) : ℂ)+1)) := by
  rw [freePacket,quadratic_eq_floor,diagonal_eq_floor,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem twoIndex_prefix (X : ℕ) :
    (∑ a ∈ Finset.Icc 1 X,twoIndex a)=(X : ℂ)*((X : ℂ)+1) := by
  induction X with
  | zero => simp
  | succ X ih =>
    rw [Finset.sum_Icc_succ_top (by omega),ih]
    simp only [twoIndex,Nat.cast_add,Nat.cast_one]
    ring

/-- Native pair packet is exactly the full divisor-convolution prefix. -/
theorem nativePacket_eq_shell_prefix (y : ℝ) (X : ℕ) :
    nativePacket y X=∑ n ∈ Finset.Icc 1 X,shell y n := by
  change freePacket X (column y)=_
  rw [freePacket_eq_scalar]
  have he : (∑ n ∈ Finset.Icc 1 X,shell y n)=cutoffConvolution (column y) twoIndex X := by
    simp only [shell,LSeries.convolution_def,cutoffConvolution,divisorConvolution]
  rw [he,cutoffConvolution_eq_quotient]
  simp only [prefixSum,twoIndex_prefix]

/-- Ordinary coprimality is the ACTUAL Mobius divisor sum. -/
theorem untwisted_entry (m n : ℕ) :
    gcdKernel (column 0) m n=if m.Coprime n then 1 else 0 := by
  have he : column 0=mu := by funext d; simp [column,primePhase]
  rw [he,gcdKernel]
  have h := congrArg (fun f : ArithmeticFunction ℂ => f (Nat.gcd m n))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa only [mu,ArithmeticFunction.intCoe_apply,ArithmeticFunction.one_apply,
    Nat.coprime_iff_gcd_eq_one] using h

private theorem term_index (s : ℂ) (n : ℕ) :
    LSeries.term (fun n : ℕ => (n : ℂ)) s n=LSeries.term 1 (s-1) n := by
  by_cases hn : n=0
  · simp [hn]
  rw [LSeries.term_of_ne_zero hn,LSeries.term_of_ne_zero hn,Pi.one_apply,
    Complex.cpow_sub s 1 (Nat.cast_ne_zero.mpr hn),Complex.cpow_one]
  field_simp

private theorem index_summable {s : ℂ} (hs : 2<s.re) :
    LSeriesSummable (fun n : ℕ => (n : ℂ)) s := by
  have h := LSeriesSummable_one_iff.mpr (show 1<(s-1).re by simp only [sub_re,one_re]; linarith)
  have he : LSeries.term (fun n : ℕ => (n : ℂ)) s=LSeries.term 1 (s-1) :=
    funext (term_index s)
  change Summable (LSeries.term (fun n : ℕ => (n : ℂ)) s)
  rw [he]
  exact h

private theorem index_series {s : ℂ} (hs : 2<s.re) :
    LSeries (fun n : ℕ => (n : ℂ)) s=riemannZeta (s-1) := by
  calc
    _ = LSeries 1 (s-1) := tsum_congr (term_index s)
    _ = _ := LSeries_one_eq_riemannZeta (by simp only [sub_re,one_re]; linarith)

/-- Continuation in the original selected-zero coordinate. -/
def response (y : ℝ) (z : ℂ) : ℂ :=
  2*riemannZeta (z-I*y-1)/riemannZeta z

/-- Genuine Euler identity, with all ordinary integer/cofactor and
Mobius fibers retained. No continued series is asserted below Re(s)>2. -/
theorem euler_response (y : ℝ) {s : ℂ} (hs : 2<s.re) :
    LSeries (shell y) s=response y (s+I*y) := by
  have ht : 1<(s+I*y).re := by simp only [add_re,mul_re,I_re,I_im,ofReal_re,ofReal_im]; linarith
  have hf : LSeriesSummable (column y) s := (LSeriesSummable_primePhase_iff mu y s).mpr
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr ht)
  have he : twoIndex=(2 : ℂ) • (fun n : ℕ => (n : ℂ)) := by funext n; rfl
  have hg : LSeriesSummable twoIndex s := by rw [he]; exact (index_summable hs).smul 2
  rw [shell,LSeries_convolution' hf hg]
  change LSeries (fun d => mu d*primePhase y d) s*LSeries twoIndex s=_
  rw [LSeries_primePhase,he,LSeries_smul,index_series hs]
  have hμ : riemannZeta (s+I*y)*LSeries mu (s+I*y)=1 := by
    rw [← LSeries_one_eq_riemannZeta ht]
    exact LSeries_one_mul_Lseries_moebius ht
  have hμ' : LSeries mu (s+I*y)=1/riemannZeta (s+I*y) := by
    apply (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re ht)).mpr
    simpa only [mul_comm] using hμ
  rw [hμ',response]
  simp only [add_sub_cancel_right]
  ring

/-- The numerator does not annihilate any actual matched zero: its
real argument is in (-1,0), outside all genuine and trivial zeros. -/
theorem matched_numerator_ne_zero (rho : NontrivialZetaZero) :
    riemannZeta (rho.1-I*rho.1.im-1)≠0 := by
  have he : rho.1-I*rho.1.im-1=((rho.1.re-1 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [he]
  intro hzero
  have hr0 := NontrivialZetaZero.zero_lt_re rho
  have hr1 := NontrivialZetaZero.re_lt_one rho
  let tau : NontrivialZetaZero := ⟨((rho.1.re-1 : ℝ) : ℂ),hzero,by
    rintro ⟨n,hn⟩
    have h := congrArg Complex.re hn
    norm_num [Complex.mul_re] at h
    nlinarith [Nat.cast_nonneg (α := ℝ) n],by
    intro h
    have h' := congrArg Complex.re h
    simp only [ofReal_re,one_re] at h'
    linarith⟩
  have h := NontrivialZetaZero.zero_lt_re tau
  change 0<rho.1.re-1 at h
  linarith

/-- The complete actual packet has a nonzero source at EVERY analytic
multiplicity. This is a local continuation statement, not a cutoff limit. -/
theorem actual_zero_source (rho : NontrivialZetaZero) :
    ∃ v : ℂ,v≠0 ∧ Tendsto
      (fun z : ℂ => (z-rho.1)^(analyticZetaZeroMultiplicity rho)*response rho.1.im z)
      (𝓝[≠] rho.1) (𝓝 v) := by
  obtain ⟨g,hg,hg0,he⟩ := (analyticAt_riemannZeta_nontrivialZero rho).analyticOrderAt_ne_top.mp
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)
  have hz0 := matched_numerator_ne_zero rho
  have hn : rho.1-I*rho.1.im-1≠1 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [sub_re,mul_re,I_re,I_im,ofReal_re,ofReal_im,mul_zero,sub_zero,
      zero_mul,one_re] at hh
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hnA : AnalyticAt ℂ (fun z : ℂ => riemannZeta (z-I*rho.1.im-1)) rho.1 :=
    AnalyticAt.comp (g := riemannZeta) (f := fun z : ℂ => z-I*rho.1.im-1)
      (analyticOn_riemannZeta _ hn) ((analyticAt_id.sub analyticAt_const).sub analyticAt_const)
  have ha : AnalyticAt ℂ (fun z : ℂ => 2*riemannZeta (z-I*rho.1.im-1)/g z) rho.1 :=
    (analyticAt_const.mul hnA).div hg hg0
  refine ⟨2*riemannZeta (rho.1-I*rho.1.im-1)/g rho.1,
    div_ne_zero (mul_ne_zero (by norm_num) hz0) hg0,?_⟩
  have heq : (fun z : ℂ => (z-rho.1)^(analyticZetaZeroMultiplicity rho)*response rho.1.im z)
      =ᶠ[𝓝[≠] rho.1] fun z => 2*riemannZeta (z-I*rho.1.im-1)/g z := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,
      hg.continuousAt.eventually_ne hg0 |>.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hgz (hzn : z≠rho.1)
    rw [response,hz]
    simp only [smul_eq_mul]
    change (z-rho.1)^(analyticZetaZeroMultiplicity rho)*
      (2*riemannZeta (z-I*rho.1.im-1)/
        ((z-rho.1)^(analyticZetaZeroMultiplicity rho)*g z))=_
    field_simp [pow_ne_zero _ (sub_ne_zero.mpr hzn),hgz]
  exact (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm

/-- Density pole of the two-dimensional primitive lattice. -/
def centeredResponse (y : ℝ) (z : ℂ) : ℂ :=
  (z-(2+I*y))*response y z

/-- The density pole is removed as an analytic germ with the whole
height retained. This does not assert convergence in the zero strip. -/
theorem centered_density_analytic (y : ℝ) :
    ∃ E : ℂ → ℂ,AnalyticAt ℂ E (2+I*y) ∧
      centeredResponse y=ᶠ[𝓝[≠] (2+I*y)] E := by
  have hc : (2+I*y : ℂ)≠1 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num at h'
  have hz : riemannZeta (2+I*y)≠0 := riemannZeta_ne_zero_of_one_le_re (by simp)
  have hA : AnalyticAt ℂ (fun z : ℂ => riemannZeta₁ (z-I*y-1)) (2+I*y) :=
    AnalyticAt.comp (g := riemannZeta₁) (f := fun z : ℂ => z-I*y-1)
      (differentiable_riemannZeta₁.analyticAt _) ((analyticAt_id.sub analyticAt_const).sub analyticAt_const)
  refine ⟨fun z => 2*riemannZeta₁ (z-I*y-1)/riemannZeta z,
    (analyticAt_const.mul hA).div (analyticOn_riemannZeta _ hc) hz,?_⟩
  have hne := (analyticOn_riemannZeta _ hc).continuousAt.eventually_ne hz
  filter_upwards [self_mem_nhdsWithin,hne.filter_mono nhdsWithin_le_nhds]
    with z (hzc : z≠2+I*y) hzz
  have hshift : z-I*y-1≠1 := by intro h; apply hzc; linear_combination h
  have he : z-I*y-1-1=z-(2+I*y) := by ring
  rw [centeredResponse,response,riemannZeta_eq_inv_sub_mul hshift,he]
  field_simp [sub_ne_zero.mpr hzc,hzz]

/-- Pole centering still retains the full genuine zero order and a
nonzero source. No exposure or simplicity is used. -/
theorem centered_actual_zero_source (rho : NontrivialZetaZero) :
    ∃ v : ℂ,v≠0 ∧ Tendsto
      (fun z : ℂ => (z-rho.1)^(analyticZetaZeroMultiplicity rho)*centeredResponse rho.1.im z)
      (𝓝[≠] rho.1) (𝓝 v) := by
  obtain ⟨v,hv,ht⟩ := actual_zero_source rho
  have hc : rho.1-(2+I*rho.1.im)≠0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [Complex.sub_re] at hh
    linarith [NontrivialZetaZero.re_lt_one rho]
  refine ⟨(rho.1-(2+I*rho.1.im))*v,mul_ne_zero hc hv,?_⟩
  have hx : Tendsto (fun z : ℂ => z-(2+I*rho.1.im)) (𝓝[≠] rho.1)
      (𝓝 (rho.1-(2+I*rho.1.im))) :=
    (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  convert hx.mul ht using 1
  funext z
  unfold centeredResponse
  ring

/-- A free scalar allowance requires the literal full floor kernel to
vanish. Those free weights do not obey actual Mobius coprimality data. -/
theorem bound_forall_free_columns_iff (X : ℕ) (B : ℝ) :
    (∀ w,‖freePacket X w‖≤B) ↔
      0≤B ∧ ∀ d ∈ Finset.Icc 1 X,
        (((X/d : ℕ) : ℂ)*(((X/d : ℕ) : ℂ)+1))=0 := by
  simp_rw [freePacket_eq_scalar]
  exact scalar_bound_forall_weights_iff _ _ _

/-- Matrix with exactly the same diagonal credit as the native packet. -/
def augmentedKernel (y : ℝ) (m n : ℕ) : ℂ :=
  gcdKernel (column y) m n+if m=n then gcdKernel (column y) n n else 0

/-- The matrix tested below is precisely the native packet's matrix,
including its actual diagonal credit. -/
theorem nativePacket_eq_augmented (y : ℝ) (X : ℕ) :
    nativePacket y X=
      ∑ m ∈ Finset.Icc 1 X,∑ n ∈ Finset.Icc 1 X,augmentedKernel y m n := by
  unfold nativePacket gcdQuadratic
  simp only [map_one,one_mul,mul_one]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  simp [augmentedKernel,Finset.sum_add_distrib,hm]

/-- Complete literal coprimality observations uniquely force actual
Mobius on every positive integer. Free or smooth columns do not
automatically satisfy these data. -/
theorem coprime_observations_force_mu (w : ℕ → ℂ)
    (hw : ∀ m n,gcdKernel w m n=if m.Coprime n then 1 else 0) :
    ∀ n>0,w n=mu n := by
  let g : ℕ → ℂ := fun n => if n=1 then 1 else 0
  have hwobs : ∀ n>0,∑ i ∈ n.divisors,w i=g n := by
    intro n _
    simpa [g,gcdKernel,Nat.gcd_self,Nat.coprime_self] using hw n n
  have hmobs : ∀ n>0,∑ i ∈ n.divisors,mu i=g n := by
    intro n _
    simpa [g,gcdKernel,Nat.gcd_self,Nat.coprime_self,column,primePhase]
      using untwisted_entry n n
  have hwi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := w) (g := g)).mp hwobs
  have hmi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := mu) (g := g)).mp hmobs
  intro n hn
  exact (hwi n hn).symm.trans (hmi n hn)

/-- The antisymmetric two-row quadratic keeps the full complex phase. -/
def twoPrimeQuadratic (y : ℝ) (p q : ℕ) : ℂ :=
  augmentedKernel y p p-augmentedKernel y p q-
    augmentedKernel y q p+augmentedKernel y q q

/-- A literal finite row vector, not just a determinant diagnostic. -/
theorem twoPrimeQuadratic_eq_joined (y : ℝ) {p q : ℕ} (hpq : p≠q) :
    twoPrimeQuadratic y p q=
      ∑ m ∈ ({p,q} : Finset ℕ),∑ n ∈ ({p,q} : Finset ℕ),
        (if m=p then (1 : ℂ) else -1)*conj (if n=p then (1 : ℂ) else -1)*
          augmentedKernel y m n := by
  simp [Finset.sum_pair hpq,twoPrimeQuadratic,Ne.symm hpq]
  ring

private theorem prime_entry (y : ℝ) {p : ℕ} (hp : p.Prime) :
    gcdKernel (column y) p p=1-primePhase y p := by
  rw [gcdKernel,Nat.gcd_self,hp.divisors]
  rw [Finset.sum_pair hp.ne_one.symm]
  simp [column,mu,ArithmeticFunction.moebius_apply_prime hp,primePhase]
  ring

private theorem distinct_prime_entry (y : ℝ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) :
    gcdKernel (column y) p q=1 := by
  have hg := ((Nat.coprime_primes hp hq).mpr hpq).gcd_eq_one
  simp [gcdKernel,hg,column,mu,primePhase]

/-- The exact diagonal credit does not repair the Mobius signs. -/
theorem twoPrimeQuadratic_eq (y : ℝ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) :
    twoPrimeQuadratic y p q=2-2*primePhase y p-2*primePhase y q := by
  unfold twoPrimeQuadratic augmentedKernel
  rw [prime_entry y hp,prime_entry y hq,distinct_prime_entry y hp hq hpq,
    distinct_prime_entry y hq hp hpq.symm]
  simp only [ite_eq_right hpq,ite_eq_right hpq.symm,ite_true]
  ring

private theorem phase_re (y : ℝ) (n : ℕ) :
    (primePhase y n).re=Real.cos (y*Real.log n) := by
  simp only [primePhase,Complex.exp_re,Complex.neg_re,Complex.neg_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,one_mul,
    zero_add,sub_zero,neg_zero,Real.exp_zero]
  rw [neg_mul,Real.cos_neg]

/-- Positive phase center at the ACTUAL fixed height. -/
def positiveScale (y : ℝ) (J : ℕ) : ℝ :=
  Real.exp ((J : ℝ)*(2*Real.pi)/|y|)

/-- Half a radian gives a strict negative quadratic margin. -/
def positiveWidth (y : ℝ) : ℝ := Real.exp (1/(2*|y|))

theorem positiveScale_tendsto {y : ℝ} (hy : y≠0) :
    Tendsto (positiveScale y) atTop atTop := by
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const
    (div_pos (by positivity : 0<2*Real.pi) (abs_pos.mpr hy))
  convert Real.tendsto_exp_atTop.comp ht using 1
  funext J
  unfold positiveScale
  congr 1
  ring

/-- Existing PNT is used ONLY to locate counterexample rows, not to
provide a source-scale prime-sum estimate. -/
theorem eventually_prime_in_positiveBand {y : ℝ} (hy : y≠0) :
    ∀ᶠ J : ℕ in atTop,∃ p ∈ PrimeWindow.primesInWindow
      (positiveScale y J) (positiveWidth y),True := by
  have hw : 1<positiveWidth y := by
    unfold positiveWidth
    exact Real.one_lt_exp_iff.mpr (div_pos zero_lt_one (mul_pos (by norm_num) (abs_pos.mpr hy)))
  have ht := (PrimeWindow.theta_interval_div_tendsto (zero_lt_one.trans hw)).comp
    (positiveScale_tendsto hy)
  have hp := ht.eventually (eventually_gt_nhds (by linarith : (0 : ℝ)<positiveWidth y-1))
  filter_upwards [hp] with J hJ
  have hd := (lt_div_iff₀ (show 0<positiveScale y J from Real.exp_pos _)).mp hJ
  rw [zero_mul] at hd
  have hs := PrimeWindow.sum_log_primesInWindow (show 0≤positiveScale y J from (Real.exp_pos _).le) hw.le
  have hn : (PrimeWindow.primesInWindow (positiveScale y J) (positiveWidth y)).Nonempty := by
    by_contra hh
    rw [Finset.not_nonempty_iff_eq_empty.mp hh,Finset.sum_empty] at hs
    linarith
  obtain ⟨p,hp⟩ := hn
  exact ⟨p,hp,trivial⟩

private theorem positiveBand_log_bounds {y : ℝ} {J p : ℕ}
    (hp : p∈PrimeWindow.primesInWindow (positiveScale y J) (positiveWidth y)) :
    p.Prime ∧ (J : ℝ)*(2*Real.pi)/|y|<Real.log p ∧
      Real.log p≤1/(2*|y|)+(J : ℝ)*(2*Real.pi)/|y| := by
  obtain ⟨hlo,hup,hprime⟩ := PrimeWindow.mem_primesInWindow_bounds
    (show 0≤positiveScale y J from (Real.exp_pos _).le)
    (show 0≤positiveWidth y from (Real.exp_pos _).le) hp
  have hl := Real.log_lt_log (show 0<positiveScale y J from Real.exp_pos _) hlo
  have hu := Real.log_le_log (by exact_mod_cast hprime.pos) hup
  simp only [positiveScale,Real.log_exp] at hl
  rw [Real.log_mul (show positiveWidth y≠0 from (Real.exp_pos _).ne')
    (show positiveScale y J≠0 from (Real.exp_pos _).ne'),positiveScale,
    positiveWidth,Real.log_exp,Real.log_exp] at hu
  exact ⟨hprime,hl,hu⟩

theorem positiveBand_cos_ge {y : ℝ} (hy : y≠0) {J p : ℕ}
    (hp : p∈PrimeWindow.primesInWindow (positiveScale y J) (positiveWidth y)) :
    7/8≤Real.cos (y*Real.log p) := by
  obtain ⟨_,hl,hu⟩ := positiveBand_log_bounds hp
  have ha : 0 < |y| := abs_pos.mpr hy
  have hv0 := (div_lt_iff₀ ha).mp hl
  have hv1 := mul_le_mul_of_nonneg_left hu ha.le
  have he : |y| *(1/(2*|y|)+(J : ℝ)*(2*Real.pi)/|y|)=
      1/2+(J : ℝ)*(2*Real.pi) := by field_simp
  rw [he] at hv1
  let v : ℝ := |y| *Real.log p-(J : ℝ)*(2*Real.pi)
  have h0 : 0≤v := by dsimp [v]; linarith
  have h1 : v≤1/2 := by dsimp [v]; linarith
  have hc : 7/8≤Real.cos v := by
    have hv : v^2≤1/4 := by nlinarith
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := v)]
  have harg : |y| *Real.log p=v+(J : ℝ)*(2*Real.pi) := by dsimp [v]; ring
  have hcos : Real.cos (y*Real.log p)=Real.cos (|y| *Real.log p) := by
    rcases le_total 0 y with hy0 | hy0
    · rw [abs_of_nonneg hy0]
    · rw [abs_of_nonpos hy0,neg_mul,Real.cos_neg]
  rwa [hcos,harg,Real.cos_add_nat_mul_two_pi]

/-- Positive phase primes exist cofinally at every fixed nonzero height. -/
theorem exists_positive_prime_above {y : ℝ} (hy : y≠0) (H : ℕ) :
    ∃ p : ℕ,H<p ∧ p.Prime ∧ 7/8≤Real.cos (y*Real.log p) := by
  have hbig := (positiveScale_tendsto hy).eventually (eventually_gt_atTop (H : ℝ))
  obtain ⟨J,hJ,hH⟩ := ((eventually_prime_in_positiveBand hy).and hbig).exists
  obtain ⟨p,hp,_⟩ := hJ
  obtain ⟨hlo,_,hprime⟩ := PrimeWindow.mem_primesInWindow_bounds
    (show 0≤positiveScale y J from (Real.exp_pos _).le)
    (show 0≤positiveWidth y from (Real.exp_pos _).le) hp
  exact ⟨p,by exact_mod_cast hH.trans hlo,hprime,positiveBand_cos_ge hy hp⟩

/-- No finite head deletion makes the ACTUAL phased coprime packet PSD.
Even its exact diagonal credit is included in the negative quadratic. -/
theorem exists_negative_bulk_form {y : ℝ} (hy : y≠0) (H : ℕ) :
    ∃ p q : ℕ,H<p ∧ p<q ∧ p.Prime ∧ q.Prime ∧
      (twoPrimeQuadratic y p q).re≤-(3/2 : ℝ) := by
  obtain ⟨p,hpH,hp,hpc⟩ := exists_positive_prime_above hy H
  obtain ⟨q,hqp,hq,hqc⟩ := exists_positive_prime_above hy p
  refine ⟨p,q,hpH,hqp,hp,hq,?_⟩
  rw [twoPrimeQuadratic_eq y hp hq hqp.ne]
  norm_num [Complex.mul_re,phase_re]
  nlinarith

/-- In particular the obstruction occurs at every genuine zero ordinate,
without exposure or a simplicity assumption. -/
theorem exists_negative_form_at_zero_height (rho : NontrivialZetaZero) (H : ℕ) :
    ∃ p q : ℕ,H<p ∧ p<q ∧ p.Prime ∧ q.Prime ∧
      (twoPrimeQuadratic rho.1.im p q).re≤-(3/2 : ℝ) :=
  exists_negative_bulk_form (NontrivialZetaZero.im_ne_zero_of_eta_mass rho) H

end
end RiemannGaussian.ArithmeticOperatorMoebiusCoprimeAudit
