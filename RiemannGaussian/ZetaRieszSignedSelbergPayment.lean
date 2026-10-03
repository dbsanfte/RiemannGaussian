/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.HarmonicProductContinuity
import RiemannGaussian.ZetaRieszPrimeCompletionPhase
import RiemannGaussian.ZetaRieszLowCountSelbergAudit

/-!
# Pay the retained ordinary-prime/Selberg-pair combination jointly

The exact finite factorial convolution keeps all endpoint orders and the
prime-square diagonal. A uniform independently proved radial-edge estimate
transports the complete combination to the SAME literal complete periods.
Under a simple exposed zero its normalized prime and pair sources cancel.

Only this joined Selberg component is paid. The original head, owner, sieve,
allocation and physical masks stay inside the signed distinct-pair defect;
its independent cofinal upper bound, the floor and zero exclusion are open.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszSignedSelbergPayment

/-- Center the entire factorial convolution at the simple-zero value one. -/
def convolutionError (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ k ∈ Finset.range (N+1), (a k*a (N-k)-1))/((N+1 : ℕ) : ℂ)

theorem norm_convolutionError_le (a : ℕ → ℂ) {C : ℝ}
    (hC : 1≤C) (ha : ∀ k, ‖a k‖≤C) (N : ℕ) :
    ‖convolutionError a N‖≤
      2*C*((((N+1 : ℕ) : ℝ))⁻¹*∑ k ∈ Finset.range (N+1), ‖a k+1‖) := by
  have hterms k : ‖a k*a (N-k)-1‖≤C*(‖a k+1‖+‖a (N-k)+1‖) := by
    simpa using HarmonicProductContinuity.norm_product_sub_square
      (a := (-1 : ℂ)) (ha (N-k)) (by simpa using hC)
  have href : (∑ k ∈ Finset.range (N+1), ‖a (N-k)+1‖)=
      ∑ k ∈ Finset.range (N+1), ‖a k+1‖ := by
    simpa using Finset.sum_range_reflect (fun k => ‖a k+1‖) (N+1)
  unfold convolutionError
  rw [norm_div,Complex.norm_natCast]
  calc
    _ ≤ (∑ k ∈ Finset.range (N+1), C*(‖a k+1‖+‖a (N-k)+1‖))/((N+1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right ((norm_sum_le _ _).trans
        (Finset.sum_le_sum (fun k _ => hterms k))) (Nat.cast_nonneg _)
    _ = _ := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,href]
      ring

/-- Signed prime/convolution trace with its leading sources kept joined. -/
def traceError (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  -a (N+1)-(∑ k ∈ Finset.range (N+1), a k*a (N-k))/((N+1 : ℕ) : ℂ)

theorem traceError_eq (a : ℕ → ℂ) (N : ℕ) :
    traceError a N=-(a (N+1)+1)-convolutionError a N := by
  have hn : ((N+1 : ℕ) : ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero N
  simp only [traceError,convolutionError,Finset.sum_sub_distrib,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
  field_simp [hn]
  ring

/-- Centered Cesaro cost of the signed trace, retaining all low orders. -/
def traceBudget (a : ℕ → ℂ) (C : ℝ) (N : ℕ) : ℝ :=
  ‖a (N+1)+1‖+2*C*((((N+1 : ℕ) : ℝ))⁻¹*
    ∑ k ∈ Finset.range (N+1), ‖a k+1‖)

theorem norm_traceError_le (a : ℕ → ℂ) {C : ℝ}
    (hC : 1≤C) (ha : ∀ k, ‖a k‖≤C) (N : ℕ) :
    ‖traceError a N‖≤traceBudget a C N := by
  rw [traceError_eq]
  exact (norm_sub_le _ _).trans (by
    simpa only [norm_neg,traceBudget] using
      add_le_add_right (norm_convolutionError_le a hC ha N) ‖a (N+1)+1‖)

theorem traceBudget_tendsto (a : ℕ → ℂ)
    (ha : Tendsto a atTop (𝓝 (-1))) (C : ℝ) :
    Tendsto (traceBudget a C) atTop (𝓝 0) := by
  have he : Tendsto (fun n => ‖a n+1‖) atTop (𝓝 0) := by
    simpa using (ha.add_const 1).norm
  have ht := he.cesaro.comp (tendsto_add_atTop_nat 1)
  have hh := (he.comp (tendsto_add_atTop_nat 1)).add (ht.const_mul (2*C))
  convert hh using 1
  · funext N
    simp [traceBudget]
  · simp



open ZetaRieszLowCountSelbergAudit ZetaRieszHeadOrders
open ZetaRieszPrimePairConvolution ZetaPrimeCofactorCompletion
open ZetaRieszRemainingPrefix

/-- Exact symmetry of the distinct ordinary-prime Selberg coefficient. -/
theorem selbergCoefficient_pair_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) :
    selbergCoefficient (p*q)=((-2*Real.log p*Real.log q/Real.log (p*q : ℕ) : ℝ) : ℂ) := by
  rcases lt_or_gt_of_ne hpq with h | h
  · exact selbergCoefficient_pair hp hq h
  · rw [mul_comm p q,selbergCoefficient_pair hq hp h]
    push_cast
    ring

/-- Dividing the total product logarithm removes exactly one factorial
order; no share projection or prime phase is separated. -/
theorem selberg_pair_kernel {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (N : ℕ) (s : ℂ) :
    selbergCoefficient (p*q)*zetaPrimeLogKernel (N+1) s (p*q)=
      -2/((N+1 : ℕ) : ℂ)*(Real.log p : ℂ)*(Real.log q : ℂ)*
        zetaPrimeLogKernel N s (p*q) := by
  have hn : ((N+1 : ℕ) : ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero N
  have hlog : (Real.log (p*q : ℕ) : ℂ)≠0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (Real.log_pos (by exact_mod_cast (show 1<p*q by nlinarith [hp.two_le,hq.two_le]))).ne'
  have hk : zetaPrimeLogKernel (N+1) s (p*q)=
      (Real.log (p*q : ℕ) : ℂ)*zetaPrimeLogKernel N s (p*q)/((N+1 : ℕ) : ℂ) := by
    apply (eq_div_iff hn).mpr
    simpa only [mul_comm] using (log_mul_kernel N (p*q) s).symm
  rw [selbergCoefficient_pair_ne hp hq hpq,hk]
  simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat]
  field_simp [hlog,hn]

/-- The two logged ordinary-prime arrays have one exact factorial
convolution, including all endpoint orders and repeated-prime terms. -/
theorem logged_ordered_convolution (A : Finset ℕ) (hA : ∀ p∈A,0<p)
    (N : ℕ) (s : ℂ) :
    (∑ p∈A,∑ q∈A,(Real.log p : ℂ)*(Real.log q : ℂ)*
      zetaPrimeLogKernel N s (p*q))=
        ∑ k∈Finset.range (N+1),cofactorMoment A k s*cofactorMoment A (N-k) s := by
  simp only [cofactorMoment,Finset.sum_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [mul_comm p q,logKernel_product N s (hA q hq) (hA p hp)]
  simp only [Finset.mul_sum,zetaPrimeLogKernel]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- The finite ordinary-prime square diagonal is retained exactly. -/
def loggedDiagonal (A : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ p∈A,(Real.log p : ℂ)^2*zetaPrimeLogKernel N s (p^2)

/-- The complete finite Selberg combination joins its prime and unordered
pair terms BEFORE any norm. Its diagonal is not counted twice. -/
def finiteSelberg (A : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  (∑ p∈A,selbergCoefficient p*zetaPrimeLogKernel (N+1) s p)+
    ∑ n∈pairedLabels A,selbergCoefficient n*zetaPrimeLogKernel (N+1) s n

theorem finiteSelberg_eq (A : Finset ℕ) (hA : ∀ p∈A,p.Prime)
    (N : ℕ) (s : ℂ) :
    finiteSelberg A N s= -cofactorMoment A (N+1) s-
      ((∑ k∈Finset.range (N+1),cofactorMoment A k s*cofactorMoment A (N-k) s)-
        loggedDiagonal A N s)/((N+1 : ℕ) : ℂ) := by
  let w : ℕ×ℕ→ℂ := fun pq => (Real.log pq.1 : ℂ)*(Real.log pq.2 : ℂ)*
    zetaPrimeLogKernel N s (pq.1*pq.2)
  have hd : (∑ pq∈(A×ˢA).filter (fun pq => pq.1=pq.2),w pq)=loggedDiagonal A N s := by
    simp only [Finset.sum_filter,Finset.sum_product,loggedDiagonal]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.sum_eq_single p]
    · simp [w,pow_two]
    · intro q _ hqp
      simp [hqp.symm]
    · exact fun h => (h hp).elim
  have hf := Finset.sum_filter_add_sum_filter_not (A×ˢA)
    (fun pq => pq.1≠pq.2) w
  simp only [not_not] at hf
  rw [hd,Finset.sum_product] at hf
  have hc := logged_ordered_convolution A (fun p hp => (hA p hp).pos) N s
  change (∑ p∈A,∑ q∈A,w (p,q))=_ at hc
  rw [hc] at hf
  change (∑ pq∈distinctPairs A,w pq)+loggedDiagonal A N s=
    ∑ k∈Finset.range (N+1),cofactorMoment A k s*cofactorMoment A (N-k) s at hf
  have hp := sum_distinct_eq_twice_labels A hA
    (fun n => selbergCoefficient n*zetaPrimeLogKernel (N+1) s n)
  have he : (∑ pq∈distinctPairs A,
      selbergCoefficient (pq.1*pq.2)*zetaPrimeLogKernel (N+1) s (pq.1*pq.2))=
        (-2/((N+1 : ℕ) : ℂ))*(∑ pq∈distinctPairs A,w pq) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro pq hpq
    obtain ⟨hpq,hne⟩ := Finset.mem_filter.mp hpq
    obtain ⟨hpA,hqA⟩ := Finset.mem_product.mp hpq
    rw [selberg_pair_kernel (hA _ hpA) (hA _ hqA) hne]
    dsimp only [w]
    ring
  rw [he] at hp
  have hprime : (∑ p∈A,selbergCoefficient p*zetaPrimeLogKernel (N+1) s p)=
      -cofactorMoment A (N+1) s := by
    rw [cofactorMoment,←Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun p hp => by rw [selbergCoefficient_prime (hA p hp)]; ring)
  unfold finiteSelberg
  rw [hprime]
  linear_combination -(1/2 : ℂ)*hp-(1/((N+1 : ℕ) : ℂ))*hf


/-- One logged ordinary-prime square channel; it is analytic strictly
beyond the source radius and is paid independently. -/
def squareTerm (N : ℕ) (y : ℝ) (p : ℕ) : ℂ :=
  if p.Prime then (Real.log p : ℂ)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p^2) else 0

/-- Convergent Euler majorant for the repeated ordinary-prime channel. -/
def squareMass : ℝ := ∑' n,ZetaPrimeNonlinearTail.squareLogWeight (3/4) n

/-- Complete logged prime-square moment with its actual height phase. -/
def squareMoment (N : ℕ) (y : ℝ) : ℂ := ∑' p,squareTerm N y p

theorem norm_squareTerm_le (N : ℕ) (y : ℝ) (p : ℕ) :
    ‖squareTerm N y p‖≤(4/3 : ℝ)^N*ZetaPrimeNonlinearTail.squareLogWeight (3/4) p := by
  by_cases hp : p.Prime
  · rw [squareTerm,if_pos hp,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (Real.log_natCast_nonneg p)]
    have hk := norm_zetaPrimeLogKernel_le N (3/2+Complex.I*(y : ℂ)) (p^2)
      (by norm_num : (0 : ℝ)<3/4)
    have hl : Real.log (p^2 : ℕ)=2*Real.log p := by
      rw [Nat.cast_pow,Real.log_pow]
      norm_num
    simp only [show (3/2+Complex.I*(y : ℂ)).re=3/2 by simp] at hk
    norm_num at hk
    simp only [zetaPrimeExpWeight,hl] at hk
    apply (mul_le_mul_of_nonneg_left hk (Real.log_natCast_nonneg p)).trans_eq
    dsimp only [ZetaPrimeNonlinearTail.squareLogWeight,zetaPrimeExpWeight]
    rw [show -(3/4 : ℝ)*(2*Real.log p)=-(2*(3/4 : ℝ))*Real.log p by ring]
    ring
  · rw [squareTerm,if_neg hp,norm_zero]
    exact mul_nonneg (by positivity)
      (mul_nonneg (Real.exp_pos _).le (Real.log_natCast_nonneg p))

theorem summable_squareTerm (N : ℕ) (y : ℝ) : Summable (squareTerm N y) :=
  ((ZetaPrimeNonlinearTail.summable_squareLogWeight (by norm_num : (1/2 : ℝ)<3/4)).mul_left
    ((4/3 : ℝ)^N)).of_norm_bounded (norm_squareTerm_le N y)

theorem norm_squareMoment_le (N : ℕ) (y : ℝ) :
    ‖squareMoment N y‖≤(4/3 : ℝ)^N*squareMass := by
  have hs := summable_squareTerm N y
  apply (norm_tsum_le_tsum_norm hs.norm).trans
  calc
    _ ≤ ∑' p,(4/3 : ℝ)^N*ZetaPrimeNonlinearTail.squareLogWeight (3/4) p :=
      Summable.tsum_le_tsum (norm_squareTerm_le N y) hs.norm
        ((ZetaPrimeNonlinearTail.summable_squareLogWeight (by norm_num : (1/2 : ℝ)<3/4)).mul_left _)
    _ = _ := tsum_mul_left

/-- The exact repeated-prime diagonal after removal of one factorial
order. This identity includes order zero. -/
theorem loggedDiagonal_div_eq (A : Finset ℕ) (N : ℕ) (s : ℂ) :
    loggedDiagonal A N s/((N+1 : ℕ) : ℂ)=
      (1/2 : ℂ)*(∑ p∈A,(Real.log p : ℂ)*zetaPrimeLogKernel (N+1) s (p^2)) := by
  have hn : ((N+1 : ℕ) : ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero N
  simp only [loggedDiagonal,Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  have h := log_mul_kernel N (p^2) s
  rw [Nat.cast_pow,Real.log_pow] at h
  simp only [Complex.ofReal_mul,Nat.cast_add,Nat.cast_one] at h
  norm_num at h
  rw [←Complex.natCast_log] at h
  apply (div_eq_iff hn).mpr
  simp only [Nat.cast_add,Nat.cast_one]
  linear_combination (Real.log p : ℂ)/2*h

/-- Complete arithmetic Selberg trace, retaining every ordinary-prime
factorial order and the ordinary-prime square diagonal. -/
def completeSelberg (N : ℕ) (y : ℝ) : ℂ :=
  -zetaOrdinaryPrimeLogMoment (N+1) (3/2+Complex.I*y)-
    (∑ k∈Finset.range (N+1),
      zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)*
      zetaOrdinaryPrimeLogMoment (N-k) (3/2+Complex.I*y))/((N+1 : ℕ) : ℂ)+
    squareMoment (N+1) y/2

/-- All ordinary primes, exhausted by a deterministic finite prefix. -/
def primePrefix (P : ℕ) : Finset ℕ := (Finset.range P).filter Nat.Prime

theorem cofactorMoment_prefix_tendsto (N : ℕ) {s : ℂ} (hs : 1<s.re) :
    Tendsto (fun P => cofactorMoment (primePrefix P) N s) atTop
      (𝓝 (zetaOrdinaryPrimeLogMoment N s)) := by
  have ht := (summable_zetaOrdinaryPrimeLogMoment N hs).hasSum.tendsto_sum_nat
  apply ht.congr'
  filter_upwards [] with P
  simp only [cofactorMoment,primePrefix,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hp : p.Prime
  · simp only [if_pos hp,ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp only [if_neg hp]

theorem finiteSelberg_prefix_tendsto (N : ℕ) (y : ℝ) :
    Tendsto (fun P => finiteSelberg (primePrefix P) N (3/2+Complex.I*y)) atTop
      (𝓝 (completeSelberg N y)) := by
  have hp := cofactorMoment_prefix_tendsto (N+1) (by norm_num : 1<(3/2+Complex.I*(y : ℂ)).re)
  have hc := tendsto_finsetSum (Finset.range (N+1)) (fun k _ =>
    (cofactorMoment_prefix_tendsto k (by norm_num : 1<(3/2+Complex.I*(y : ℂ)).re)).mul
      (cofactorMoment_prefix_tendsto (N-k) (by norm_num : 1<(3/2+Complex.I*(y : ℂ)).re)))
  have hd := (summable_squareTerm (N+1) y).hasSum.tendsto_sum_nat
  have ht := (hp.neg.sub (hc.div_const ((N+1 : ℕ) : ℂ))).add (hd.div_const 2)
  change Tendsto _ _ (𝓝 (completeSelberg N y)) at ht
  apply ht.congr'
  filter_upwards [] with P
  rw [finiteSelberg_eq (primePrefix P)
    (fun p hp => (Finset.mem_filter.mp hp).2),sub_div,loggedDiagonal_div_eq]
  simp only [primePrefix,Finset.sum_filter,squareTerm]
  ring

/-- The source-scaled complete trace is an exact joined cancellation
plus a geometrically small diagonal, not a sum of separate allowances. -/
theorem scaled_completeSelberg_eq (u y : ℝ) (N : ℕ) :
    (u : ℂ)^(N+2)*completeSelberg N y=
      traceError (fun k => (u : ℂ)^(k+1)*
        zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)) N+
      (u : ℂ)^(N+2)*squareMoment (N+1) y/2 := by
  have he : (u : ℂ)^(N+2)*
      (∑ k∈Finset.range (N+1),zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)*
        zetaOrdinaryPrimeLogMoment (N-k) (3/2+Complex.I*y))=
      ∑ k∈Finset.range (N+1),
        ((u : ℂ)^(k+1)*zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y))*
        ((u : ℂ)^(N-k+1)*zetaOrdinaryPrimeLogMoment (N-k) (3/2+Complex.I*y)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn := Finset.mem_range.mp hk
    rw [show N+2=(k+1)+(N-k+1) by omega,pow_add]
    ring
  unfold completeSelberg traceError
  simp only [mul_add,mul_sub,←mul_div_assoc]
  rw [he]
  ring

theorem scaled_squareMoment_bound {u : ℝ} (hu : 0≤u) (y : ℝ) (N : ℕ) :
    ‖(u : ℂ)^(N+2)*squareMoment (N+1) y/2‖≤
      (4*u/3)^(N+1)*(u*squareMass/2) := by
  rw [norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_squareMoment_le (N+1) y) (pow_nonneg hu _))
    (by norm_num : (0 : ℝ)≤2)).trans_eq
  rw [show N+2=N+1+1 by omega,pow_succ,
    show 4*u/3=u*(4/3) by ring,mul_pow]
  ring

/-- Conditional cancellation of the whole complete ordinary-prime
Selberg trace under a SIMPLE exposed zero. This is not a floor for the
remaining literal masked pair defect. -/
theorem tendsto_completeSelberg_simple (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hm : analyticZetaZeroMultiplicity rho=1)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => ((3/2-rho.1.re : ℝ) : ℂ)^(N+2)*
      completeSelberg N rho.1.im) atTop (𝓝 0) := by
  let u : ℝ := 3/2-rho.1.re
  let a : ℕ→ℂ := fun k => (u : ℂ)^(k+1)*
    zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*(rho.1.im : ℂ))
  have hu : 0<u := by dsimp only [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have ha : Tendsto a atTop (𝓝 (-1)) := by
    simpa only [hm,Nat.cast_one,a,u] using
      ZetaRieszPrimeCompletionPhase.tendsto_ordinary_prime_source rho hrho hexposed
  obtain ⟨B,hB,hb⟩ := ZetaExposedPrimeMoments.exists_normalized_ordinary_prime_moment_bound
    rho hrho hexposed
  let C : ℝ := 1+B
  have hC : 1≤C := by dsimp only [C]; linarith only [hB]
  have hbound k : ‖a k‖≤C := (hb k).trans (by dsimp only [C]; linarith)
  have he : Tendsto (fun N => traceError a N) atTop (𝓝 0) :=
    squeeze_zero_norm (norm_traceError_le a hC hbound) (traceBudget_tendsto a ha C)
  have hr : 4*u/3<1 := by
    dsimp only [u] at hU ⊢
    unfold ZetaRieszWideOwnerAudit.radiusCeiling at hU
    linarith only [hU]
  have hd : Tendsto (fun N => (u : ℂ)^(N+2)*squareMoment (N+1) rho.1.im/2)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (scaled_squareMoment_bound hu.le rho.1.im)
    simpa only [zero_mul,Function.comp_def] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr).comp
        (tendsto_add_atTop_nat 1)).mul_const (u*squareMass/2)
  have ht := he.add hd
  rw [zero_add] at ht
  apply ht.congr'
  filter_upwards [] with N
  simp only [scaled_completeSelberg_eq,a,u]


open ZetaRieszGlobalCentralPayment ZetaRieszGlobalBulkPayment
open ZetaRieszLowCountSignedBoundary ZetaRieszGlobalPeriodEdgePayment
open ZetaRieszUnallocatedOwnerPayment
open ZetaRieszPrimeCountFrequency

/-- Exactly the genuine ordinary-prime and squarefree distinct-pair
population. There is no physical rough-prime deletion in this completion. -/
def OrdinaryLabel (n : ℕ) : Prop := n.Prime ∨ (Squarefree n ∧ n.primeFactors.card=2)

theorem ordinaryLabel_pair {n : ℕ} (hn : OrdinaryLabel n) :
    n.Prime ∨ ∃ p q : ℕ,p.Prime ∧ q.Prime ∧ p≠q ∧ p*q=n := by
  rcases hn with hp | ⟨hs,hc⟩
  · exact Or.inl hp
  · obtain ⟨p,q,hpq,hset⟩ := Finset.card_eq_two.mp hc
    have hp : p∈n.primeFactors := by rw [hset]; simp
    have hq : q∈n.primeFactors := by rw [hset]; simp
    have he := Nat.prod_primeFactors_of_squarefree hs
    rw [hset,Finset.prod_pair hpq] at he
    exact Or.inr ⟨p,q,Nat.prime_of_mem_primeFactors hp,
      Nat.prime_of_mem_primeFactors hq,hpq,he⟩

theorem pair_ordinaryLabel {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) :
    OrdinaryLabel (p*q) := by
  have hcop := hp.coprime_iff_not_dvd.mpr
    (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))
  refine Or.inr ⟨Nat.squarefree_mul_iff.mpr ⟨hcop,hp.squarefree,hq.squarefree⟩,?_⟩
  simp only [Nat.primeFactors_mul hp.ne_zero hq.ne_zero,hp.primeFactors,hq.primeFactors,
    Finset.union_singleton]
  rw [Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton] using hpq.symm),
    Finset.card_singleton]

/-- Only the newly completed Selberg coefficient is norm-majorized here,
and ONLY for its exterior/partial-period payment. -/
theorem norm_selbergCoefficient_le {n : ℕ} (hn : OrdinaryLabel n) :
    ‖selbergCoefficient n‖≤Real.log n := by
  rcases ordinaryLabel_pair hn with hp | ⟨p,q,hp,hq,hpq,rfl⟩
  · rw [selbergCoefficient_prime hp,norm_neg,Complex.norm_real,
      Real.norm_of_nonneg (Real.log_natCast_nonneg n)]
  · have hlp := Real.log_natCast_nonneg p
    have hlq := Real.log_natCast_nonneg q
    have ht : Real.log (p*q : ℕ)=Real.log p+Real.log q := by
      rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
    have hpos : 0<Real.log (p*q : ℕ) :=
      Real.log_pos (by exact_mod_cast (show 1<p*q by nlinarith only [hp.two_le,hq.two_le]))
    have hnon : -2*Real.log p*Real.log q/Real.log (p*q : ℕ)≤0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith only [mul_nonneg hlp hlq]) hpos.le
    rw [selbergCoefficient_pair_ne hp hq hpq,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonpos hnon]
    apply (le_of_eq (by ring : -(-2*Real.log p*Real.log q/Real.log (p*q : ℕ))=
      2*Real.log p*Real.log q/Real.log (p*q : ℕ))).trans
    apply (div_le_iff₀ hpos).mpr
    rw [ht]
    nlinarith [sq_nonneg (Real.log p),sq_nonneg (Real.log q)]

/-- Ordinary primes and distinct-prime products, each integer counted once. -/
def finiteLabels (A : Finset ℕ) : Finset ℕ := A∪pairedLabels A

theorem finiteLabels_ordinary (A : Finset ℕ) (hA : ∀ p∈A,p.Prime)
    {n : ℕ} (hn : n∈finiteLabels A) : OrdinaryLabel n := by
  rcases Finset.mem_union.mp hn with hp | hpair
  · exact Or.inl (hA n hp)
  · obtain ⟨⟨p,q⟩,hpq,rfl⟩ := Finset.mem_image.mp hpair
    obtain ⟨hpq,hne⟩ := Finset.mem_filter.mp hpq
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
    exact pair_ordinaryLabel (hA p hp) (hA q hq) hne

theorem finiteSelberg_eq_label_sum (A : Finset ℕ) (hA : ∀ p∈A,p.Prime)
    (N : ℕ) (s : ℂ) :
    finiteSelberg A N s=∑ n∈finiteLabels A,selbergCoefficient n*zetaPrimeLogKernel (N+1) s n := by
  have hd : Disjoint A (pairedLabels A) := by
    apply Finset.disjoint_left.mpr
    intro n hn hpair
    obtain ⟨⟨p,q⟩,hpq,rfl⟩ := Finset.mem_image.mp hpair
    obtain ⟨hpq,_hne⟩ := Finset.mem_filter.mp hpq
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
    exact Nat.not_prime_mul (hA p hp).ne_one (hA q hq).ne_one (hA _ hn)
  exact (Finset.sum_union hd).symm

/-- The exact original joined support contains ONLY ordinary primes
and squarefree distinct pairs, including every old head/correction mask. -/
theorem joinedLabels_ordinary {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N n : ℕ} (hN : 65536≤N)
    (hn : n∈joinedLabels u N) : OrdinaryLabel n := by
  rcases Finset.mem_union.mp hn with hcentral | hcorrection
  · rcases Finset.mem_union.mp hcentral with hp | hpair
    · exact Or.inl (Finset.mem_filter.mp hp).2
    · exact Or.inr (Finset.mem_filter.mp hpair).2
  · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hcorrection
    obtain ⟨hp,hq'⟩ := Finset.mem_sigma.mp he
    obtain ⟨hq,hqp⟩ := Finset.mem_filter.mp hq'
    have hL := ZetaRieszPostHingeEnergy.length_ge_rational hN (by linarith : 0<u) hU
    have hLlo : (51/50 : ℝ)*N≤SquarefreeVaughanLogSource.length u N := by
      nlinarith only [hL,Nat.cast_nonneg (α:=ℝ) N]
    have hqp_lt := (cofactor_window_data hu (by omega : 64≤N) hp hLlo hq).2.1
    exact pair_ordinaryLabel (highOwner_data hp).1 hqp hqp_lt.ne'

/-- Every genuine interior ordinary-prime/pair label is already in the
original central joined support. No owner or allocation mask is erased. -/
theorem interior_ordinary_mem_joined {u : ℝ} {N n : ℕ}
    (hn : OrdinaryLabel n)
    (hl : (1971/1000 : ℝ)*N+1<Real.log n)
    (hh : Real.log n≤(2029/1000 : ℝ)*N-1) : n∈joinedLabels u N := by
  have hn0 : 0<n := by
    rcases ordinaryLabel_pair hn with hp | ⟨p,q,hp,hq,_hne,hpq⟩
    · exact hp.pos
    · rw [←hpq]; exact Nat.mul_pos hp.pos hq.pos
  have hf : n∈centralFullLabels N := by
    apply Finset.mem_filter.mpr
    refine ⟨(ZetaRieszOwnerLatticePhase.coreFloor_membership N 0 hn0).mpr ⟨?_,?_⟩,?_,?_⟩
    · simp only [zero_add]
      nlinarith only [hl,Nat.cast_nonneg (α:=ℝ) N]
    · simp only [zero_add]
      nlinarith only [hh,Nat.cast_nonneg (α:=ℝ) N]
    · linarith only [hl]
    · linarith only [hh]
  apply Finset.mem_union.mpr
  apply Or.inl
  rcases hn with hp | hpair
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hf,hp⟩))
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hf,hpair⟩))

/-- The actual literal Selberg part on the SAME complete-period support
as `lowCountPeriods`; this is a subexpression, not a replacement carrier. -/
def literalSelberg (u y : ℝ) (N : ℕ) : ℂ :=
  (u : ℂ)^(N+1)*∑ n∈completePeriodLabels (joinedLabels u N) N y,
    selbergCoefficient n*zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- Each fixed literal label is eventually inside the finite exhaustive
ordinary-prime/pair prefix. Only the proof cutoff tends to infinity. -/
theorem ordinaryLabel_eventually_prefix {n : ℕ} (hn : OrdinaryLabel n) :
    ∀ᶠ P : ℕ in atTop,n∈finiteLabels (primePrefix P) := by
  rcases ordinaryLabel_pair hn with hp | ⟨p,q,hp,hq,hpq,rfl⟩
  · filter_upwards [eventually_gt_atTop n] with P hP
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hP,hp⟩))
  · filter_upwards [eventually_gt_atTop p,eventually_gt_atTop q] with P hpP hqP
    apply Finset.mem_union.mpr
    apply Or.inr
    exact Finset.mem_image.mpr ⟨(p,q),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpP,hp⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqP,hq⟩⟩,hpq⟩,rfl⟩

/-- Reuse the proved all-count radial/period edge estimate. Its SINGLE
geometric budget now transports the joined Selberg expression to the
literal support. No bound for the central pair defect is assumed. -/
theorem exists_literalSelberg_completion_bound :
    ∃ C : ℝ,0≤C ∧ ∀ (u y : ℝ),1/2≤u→u≤ZetaRieszWideOwnerAudit.radiusCeiling→
      54≤|y|→∀ N : ℕ,65536≤N+1→
      ‖(u : ℂ)^(N+2)*completeSelberg N y-literalSelberg u y (N+1)‖≤
        ZetaRieszLargeOrderCore.rate^(N+1)*C := by
  obtain ⟨C,hC,hb⟩ := exists_displaced_edge_bound
  refine ⟨C,hC,?_⟩
  intro u y hu hU hy N hN
  let S := completePeriodLabels (joinedLabels u (N+1)) (N+1) y
  have hS : ∀ n∈S,OrdinaryLabel n := fun n hn =>
    joinedLabels_ordinary hu hU hN (Finset.mem_filter.mp hn).1
  have hprefix : ∀ᶠ P : ℕ in atTop,S⊆finiteLabels (primePrefix P) :=
    (eventually_all_finset S).mpr (fun n hn => ordinaryLabel_eventually_prefix (hS n hn))
  have hbound : ∀ᶠ P : ℕ in atTop,
      ‖(u : ℂ)^(N+2)*finiteSelberg (primePrefix P) N (3/2+Complex.I*y)-
        literalSelberg u y (N+1)‖≤ZetaRieszLargeOrderCore.rate^(N+1)*C := by
    filter_upwards [hprefix] with P hP
    let E := finiteLabels (primePrefix P)\S
    have hA : ∀ p∈primePrefix P,p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
    have he : interiorLabels E (N+1)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨hn,hl,hh⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn,hnS⟩ := Finset.mem_sdiff.mp hn
      have hi := interior_ordinary_mem_joined (u:=u) (finiteLabels_ordinary _ hA hn) hl hh
      have hnI : n∈interiorLabels (joinedLabels u (N+1)) (N+1) :=
        Finset.mem_filter.mpr ⟨hi,hl,hh⟩
      exact hnS (interiorLabels_subset_completePeriods _ _ hy hnI)
    have ht := hb (N+1) E selbergCoefficient (by omega : 64≤N+1)
      (fun n hn => (norm_selbergCoefficient_le
        (finiteLabels_ordinary _ hA (Finset.mem_sdiff.mp hn).1)).trans
          (ZetaRieszCentralWindow.log_le_divisor_majorant n)) y u (by linarith : 0≤u) hU
    rw [he,Finset.sum_empty,sub_zero] at ht
    have hsum := Finset.sum_sdiff hP
      (f:=fun n => selbergCoefficient n*zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n)
    have heq : (∑ n∈E,selbergCoefficient n*zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n)=
      finiteSelberg (primePrefix P) N (3/2+Complex.I*y)-
        ∑ n∈S,selbergCoefficient n*zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n := by
      rw [finiteSelberg_eq_label_sum _ hA]
      exact eq_sub_of_add_eq hsum
    rw [heq,mul_sub] at ht
    simpa only [literalSelberg,S,show N+1+1=N+2 by omega] using ht
  have hlim := (((finiteSelberg_prefix_tendsto N y).const_mul ((u : ℂ)^(N+2))).sub_const
    (literalSelberg u y (N+1))).norm
  exact le_of_tendsto hlim hbound


/-- A fixed constant from the independently proved radial edge bound.
It is never used to price the retained signed interior defect. -/
def selbergEdgeConstant : ℝ := Classical.choose exists_literalSelberg_completion_bound

theorem selbergEdgeConstant_nonneg : 0 ≤ selbergEdgeConstant :=
  (Classical.choose_spec exists_literalSelberg_completion_bound).1

/-- Explicit cost of the joined Selberg cancellation: centered Cesaro
error, prime-square geometric tail and one literal support edge payment. -/
def selbergBudget (u y C : ℝ) (N : ℕ) : ℝ :=
  traceBudget (fun k => (u : ℂ)^(k+1)*zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)) C N+
    (4*u/3)^(N+1)*(u*squareMass/2)+
      ZetaRieszLargeOrderCore.rate^(N+1)*selbergEdgeConstant

theorem norm_literalSelberg_le {u C : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (hC : 1≤C)
    (ha : ∀ k,‖(u : ℂ)^(k+1)*zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖≤C)
    {N : ℕ} (hN : 65536≤N+1) :
    ‖literalSelberg u y (N+1)‖ ≤ selbergBudget u y C N := by
  have he := (Classical.choose_spec exists_literalSelberg_completion_bound).2
    u y hu hU hy N hN
  have ht := norm_traceError_le _ hC ha N
  have hd := scaled_squareMoment_bound (by linarith : 0≤u) y N
  have hs : ‖(u : ℂ)^(N+2)*completeSelberg N y‖≤
      traceBudget (fun k => (u : ℂ)^(k+1)*zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)) C N+
        (4*u/3)^(N+1)*(u*squareMass/2) := by
    rw [scaled_completeSelberg_eq]
    exact (norm_add_le _ _).trans (add_le_add ht hd)
  have hn := norm_sub_le ((u : ℂ)^(N+2)*completeSelberg N y)
    ((u : ℂ)^(N+2)*completeSelberg N y-literalSelberg u y (N+1))
  rw [sub_sub_cancel] at hn
  exact hn.trans (add_le_add hs he)

/-- The completion payment vanishes independently, before any use of
selected-zero phase cancellation. -/
theorem tendsto_literalSelberg_completion_error {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (fun N => (u : ℂ)^(N+2)*completeSelberg N y-literalSelberg u y (N+1))
      atTop (𝓝 0) := by
  have hb : Tendsto (fun N : ℕ => ZetaRieszLargeOrderCore.rate^(N+1)*selbergEdgeConstant)
      atTop (𝓝 0) := by
    simpa only [zero_mul,Function.comp_def] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one ZetaRieszLargeOrderCore.rate_bounds.1.le
        ZetaRieszLargeOrderCore.rate_bounds.2).comp (tendsto_add_atTop_nat 1)).mul_const
        selbergEdgeConstant
  apply squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_ge_atTop (65536 : ℕ)] with N hN
  exact (Classical.choose_spec exists_literalSelberg_completion_bound).2
    u y hu hU hy N (by omega)

/-- Actual signed cancellation on the ORIGINAL retained complete-period
support. Exposure and simplicity remain explicit. The masked Selberg
pair defect is neither completed nor norm-paid. -/
theorem tendsto_literalSelberg_simple (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hm : analyticZetaZeroMultiplicity rho=1)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|rho.1.im|) :
    Tendsto (literalSelberg (3/2-rho.1.re) rho.1.im) atTop (𝓝 0) := by
  have hu : 1/2≤3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hc := tendsto_completeSelberg_simple rho hrho hexposed hm hU
  have he := tendsto_literalSelberg_completion_error hu hU hy
  have ht := hc.sub he
  rw [sub_zero] at ht
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply ht.congr'
  filter_upwards [] with N
  ring

/-- Exact remainder on the SAME original complete-period support. Its
ordinary-prime summands vanish, so only genuine distinct pairs survive. -/
def literalPairDefect (u y : ℝ) (N : ℕ) : ℂ :=
  (u : ℂ)^(N+1)*∑ n∈completePeriodLabels (joinedLabels u N) N y,
    selbergDefect u N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n

theorem literalPairDefect_eq_nonprime {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) (y : ℝ) :
    literalPairDefect u y N=(u : ℂ)^(N+1)*
      ∑ n∈(completePeriodLabels (joinedLabels u N) N y).filter (fun n => ¬n.Prime),
        selbergDefect u N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
  unfold literalPairDefect
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · have hn' := (Finset.mem_filter.mp hn).1
    have hprime : n∈primeLabels N := by
      rcases Finset.mem_union.mp hn' with hc | he
      · rcases Finset.mem_union.mp hc with hpN | hpair
        · exact hpN
        · have hcount := (Finset.mem_filter.mp hpair).2.2
          simp only [hp.primeFactors,Finset.card_singleton] at hcount
          omega
      · exact (correction_not_prime hu hU hN he hp).elim
    rw [selbergDefect_prime_eq_zero hu hU hN hprime]
    simp only [hp,not_true_eq_false,if_false,zero_mul]
  · simp only [hp,not_false_eq_true,if_true]

/-- The current floor scalar is split EXACTLY into the paid joined
Selberg term and its still-signed literal pair defect. No allocation,
owner, physical or radial condition is moved outside either coefficient. -/
theorem lowCountPeriods_eq (u y : ℝ) (j : ℕ) :
    lowCountPeriods u y j=
      (literalSelberg u y (dyadicMomentOrder j)).re+
        (literalPairDefect u y (dyadicMomentOrder j)).re := by
  unfold lowCountPeriods literalSelberg literalPairDefect selbergDefect
  simp only [Finset.sum_sub_distrib,sub_mul,mul_sub,Complex.sub_re]
  ring

/-- The Selberg expression has now been paid JOINTLY. The one-sided
inequality still exposes the EXACT original signed pair defect. -/
theorem eventually_native_pairDefect_floor {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      -(literalPairDefect u y (dyadicMomentOrder j)).re-
        nativeSignedPeriodBudget u y j-‖literalSelberg u y (dyadicMomentOrder j)‖≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
        (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  filter_upwards [eventually_native_signed_period_floor hu hU hy] with j hj
  rw [lowCountPeriods_eq] at hj
  have hs := Complex.abs_re_le_norm (literalSelberg u y (dyadicMomentOrder j))
  linarith only [hj,(abs_le.mp hs).2]

/-- Conditional source equivalence to the actual signed pair defect,
AFTER the joined ordinary-prime/Selberg-pair payment. This is not an
independent arithmetic upper bound on that defect. -/
theorem tendsto_native_plus_pairDefect_simple (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hm : analyticZetaZeroMultiplicity rho=1)
    (hu : 1/2<3/2-rho.1.re)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|rho.1.im|) :
    Tendsto (fun j =>
      (((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse
        (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)
          (ZetaRieszNearCriticalCountPayment.countCeiling j)).re+
        (literalPairDefect (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)).re)
      atTop (𝓝 0) := by
  have hn := tendsto_native_plus_lowCountPeriods hu hU hy
  have hs := (Complex.continuous_re.tendsto (0 : ℂ)).comp
    ((tendsto_literalSelberg_simple rho hrho hexposed hm hU hy).comp tendsto_dyadicMomentOrder)
  have ht := hn.sub hs
  simp only [Complex.zero_re,sub_zero] at ht
  apply ht.congr'
  filter_upwards [] with j
  simp only [Function.comp_def,lowCountPeriods_eq]
  ring


/-- The explicit cost vanishes under the simple exposed phase; no signed
pair-defect estimate enters this proof. -/
theorem selbergBudget_tendsto_simple (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hm : analyticZetaZeroMultiplicity rho=1)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling) (C : ℝ) :
    Tendsto (selbergBudget (3/2-rho.1.re) rho.1.im C) atTop (𝓝 0) := by
  let u : ℝ := 3/2-rho.1.re
  let a : ℕ→ℂ := fun k => (u : ℂ)^(k+1)*
    zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*(rho.1.im : ℂ))
  have hu : 0<u := by dsimp only [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have ha : Tendsto a atTop (𝓝 (-1)) := by
    simpa only [a,u,hm,Nat.cast_one] using
      ZetaRieszPrimeCompletionPhase.tendsto_ordinary_prime_source rho hrho hexposed
  have htrace := traceBudget_tendsto a ha C
  have hr : 4*u/3<1 := by
    dsimp only [u] at hU ⊢
    unfold ZetaRieszWideOwnerAudit.radiusCeiling at hU
    linarith only [hU]
  have hd := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr).comp
    (tendsto_add_atTop_nat 1)).mul_const (u*squareMass/2)
  have he := ((tendsto_pow_atTop_nhds_zero_of_lt_one ZetaRieszLargeOrderCore.rate_bounds.1.le
    ZetaRieszLargeOrderCore.rate_bounds.2).comp (tendsto_add_atTop_nat 1)).mul_const selbergEdgeConstant
  have ht := (htrace.add hd).add he
  convert ht using 1
  · funext N
    rfl
  · simp

/-- ONE native budget combining previous independent payments with the
newly paid joined Selberg expression. The convolution remains centered. -/
def nativeSelbergBudget (u y C : ℝ) (j : ℕ) : ℝ :=
  nativeSignedPeriodBudget u y j+selbergBudget u y C (dyadicMomentOrder j-1)

theorem nativeSelbergBudget_tendsto_simple (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hm : analyticZetaZeroMultiplicity rho=1)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling) (C : ℝ) :
    Tendsto (nativeSelbergBudget (3/2-rho.1.re) rho.1.im C) atTop (𝓝 0) := by
  have hn := nativeSignedPeriodBudget_tendsto (3/2-rho.1.re) rho.1.im
  have hs := (selbergBudget_tendsto_simple rho hrho hexposed hm hU C).comp
    ((tendsto_sub_atTop_nat 1).comp tendsto_dyadicMomentOrder)
  have ht := hn.add hs
  convert ht using 1
  · funext j
    rfl
  · simp

/-- The new explicit centered-convolution cost is actually spent in the
original whole-core floor ledger. The signed pair-defect upper bound is
still the open arithmetic estimate. -/
theorem eventually_native_budgeted_pairDefect_floor {u C : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (hC : 1≤C)
    (ha : ∀ k,‖(u : ℂ)^(k+1)*zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖≤C) :
    ∀ᶠ j in atTop,
      -(literalPairDefect u y (dyadicMomentOrder j)).re-nativeSelbergBudget u y C j≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
        (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  filter_upwards [eventually_native_pairDefect_floor hu hU hy,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (65536 : ℕ))] with j hj hN
  have hpred : dyadicMomentOrder j-1+1=dyadicMomentOrder j := by omega
  have hs := norm_literalSelberg_le hu.le hU hy hC ha (N:=dyadicMomentOrder j-1)
    (by omega : 65536≤dyadicMomentOrder j-1+1)
  rw [hpred] at hs
  unfold nativeSelbergBudget
  linarith only [hj,hs]

/-- The retained signed floor is now reduced to the actual pair defect
with a proved vanishing explicit budget, not a new bilinear hypothesis. -/
theorem exists_native_pairDefect_payment_simple (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hm : analyticZetaZeroMultiplicity rho=1)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|rho.1.im|) :
    ∃ C : ℝ,1≤C ∧
      Tendsto (nativeSelbergBudget (3/2-rho.1.re) rho.1.im C) atTop (𝓝 0) ∧
      ∀ᶠ j in atTop,
        -(literalPairDefect (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)).re-
          nativeSelbergBudget (3/2-rho.1.re) rho.1.im C j≤
        (((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse
          (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)
            (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  obtain ⟨B,hB,hb⟩ := ZetaExposedPrimeMoments.exists_normalized_ordinary_prime_moment_bound
    rho hrho hexposed
  have hC : 1≤1+B := by linarith only [hB]
  refine ⟨1+B,hC,nativeSelbergBudget_tendsto_simple rho hrho hexposed hm hU (1+B),?_⟩
  have hu : 1/2<3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  exact eventually_native_budgeted_pairDefect_floor hu hU hy hC
    (fun k => (hb k).trans (by linarith))

end RiemannGaussian.ZetaRieszSignedSelbergPayment
