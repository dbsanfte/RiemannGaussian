/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPairWholeCompletion

/-!
# Join the Selberg trace and pay the whole square correction

Collect the ordinary-prime Selberg convolution before estimating the pair
expression. The square correction is one joined object, with an independent
source-scale geometric bound. All central and logged pair products remain
signed. No independent `399/5000` bound is supplied by this payment.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszPairJointQuadratic
open ZetaRieszPairPrefixPayment ZetaRieszPairPrefixConvolution
open ZetaRieszPairWholeCompletion ZetaRieszSignedSelbergPayment
open ZetaRieszPrimePairConvolution ZetaRieszLowCountSelbergAudit
open ZetaRieszHeadOrders ZetaRieszOwnerMaximal
open ZetaRieszPrimeCountFrequency

/-- One full finite logged square moment, with its original prime phase. -/
def finiteSquare (A : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ p∈A,(log p : ℂ)*zetaPrimeLogKernel N s (p^2)

/-- The Selberg pair term is the negative FULL logged convolution plus
one half square moment. Its ordinary-prime term cancels exactly. -/
theorem selberg_pairs_eq_trace (A : Finset ℕ) (hA : ∀ p∈A,p.Prime)
    {N : ℕ} (hN : 0<N) (s : ℂ) :
    (∑ n∈ZetaRieszRemainingPrefix.pairedLabels A,
      selbergCoefficient n*zetaPrimeLogKernel N s n)=
      -(∑ k∈Finset.range N,cofactorMoment A k s*cofactorMoment A (N-1-k) s)/(N : ℂ)+
        (1/2 : ℂ)*finiteSquare A N s := by
  have he : N-1+1=N := by omega
  have hc := finiteSelberg_eq A hA (N-1) s
  rw [sub_div,loggedDiagonal_div_eq,he] at hc
  have hp : (∑ p∈A,selbergCoefficient p*zetaPrimeLogKernel N s p)=
      -cofactorMoment A N s := by
    rw [cofactorMoment,←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [selbergCoefficient_prime (hA p hp)]
    ring
  unfold finiteSelberg at hc
  rw [he,hp] at hc
  change _=_ at hc
  unfold finiteSquare
  linear_combination hc

/-- Unjoin each logged slot without changing its phase or assigned prime.
Every Selberg trace product has TOTAL ordinary-prime order `N+1`. -/
theorem selbergTrace_eq_weighted_orders (A : Finset ℕ) (N : ℕ) (s : ℂ) :
    (∑ k∈Finset.range N,cofactorMoment A k s*cofactorMoment A (N-1-k) s)=
      ∑ k∈Finset.range N,((k+1 : ℕ) : ℂ)*((N-k : ℕ) : ℂ)*
        finiteMoment A (k+1) s*finiteMoment A (N-k) s := by
  apply Finset.sum_congr rfl
  intro k hk
  have he : N-1-k+1=N-k := by have := Finset.mem_range.mp hk; omega
  rw [cofactorMoment_eq_succ,cofactorMoment_eq_succ,he]
  push_cast
  ring

/-- Its scalar weight is strictly positive on EVERY retained order.
Thus this trace reinforces the unlogged band; it is not an endpoint debit. -/
theorem selbergTrace_order_weight_pos {N k : ℕ} (hk : k∈Finset.range N) :
    0<((k+1 : ℕ) : ℝ)*((N-k : ℕ) : ℝ)/(N : ℝ) := by
  have hkN := Finset.mem_range.mp hk
  have hNk : 0<N-k := by omega
  have hN : 0<N := by omega
  exact div_pos (mul_pos (by exact_mod_cast Nat.succ_pos k)
    (by exact_mod_cast hNk)) (by exact_mod_cast hN)

/-- The TWO prefix central sums, logged prefix and full Selberg trace,
kept as one coupled quadratic. This only evaluates the existing carrier. -/
def factorialQuadratic (A : Finset ℕ) (N : ℕ) (L : ℝ) (s : ℂ) : ℂ :=
  (N+1 : ℂ)/2*(∑ k∈centralOrders (N+1) (13*N/32),
    finiteMoment A k s*finiteMoment A (N+1-k) s)-
  (N+1 : ℂ)*(N+2)/(2*(L : ℂ))*(∑ k∈centralOrders (N+2) (13*N/32),
    finiteMoment A k s*finiteMoment A (N+2-k) s)-
  (N+1 : ℂ)/(L : ℂ)*(∑ k∈(Finset.range (13*N/32+1)).filter (fun k => 0<k),
    (k : ℂ)*finiteMoment A k s*finiteMoment A (N+2-k) s)+
  (∑ k∈Finset.range N,cofactorMoment A k s*cofactorMoment A (N-1-k) s)/(N : ℂ)

/-- Exact half-share prefix, with its original integer order cutoff. -/
def squarePrefix (N : ℕ) : ℝ := lowerMass (N+1) (13*N/32) (1/2)

theorem squarePrefix_bounds (N : ℕ) : 0 ≤ squarePrefix N ∧ squarePrefix N ≤ 1 :=
  lowerMass_bounds _ _ (by norm_num) (by norm_num)

/-- The prefix and Selberg square channels have already been joined here.
The whole diagonal is counted once, with the literal signs. -/
def joinedSquare (A : Finset ℕ) (N : ℕ) (L : ℝ) (s : ℂ) : ℂ :=
  ((2*squarePrefix N-3/2 : ℝ) : ℂ)*finiteSquare A N s+
    ((N+1 : ℕ) : ℂ)/(L : ℂ)*((1-squarePrefix N : ℝ) : ℂ)*finiteSquare A (N+1) s

private theorem prefix_diagonal_atom (N p : ℕ) (hp : p.Prime) (L : ℝ) (hL : L≠0) (s : ℂ) :
    (prefixLogCoefficient N L (log p) (log p) : ℂ)*zetaPrimeLogKernel N s (p^2)=
      2*((1-2*squarePrefix N : ℝ) : ℂ)*(log p : ℂ)*zetaPrimeLogKernel N s (p^2)+
      2*((N+1 : ℕ) : ℂ)/(L : ℂ)*((squarePrefix N-1 : ℝ) : ℂ)*
        (log p : ℂ)*zetaPrimeLogKernel (N+1) s (p^2) := by
  have hx : log p≠0 := (log_pos (show (1 : ℝ)<p by exact_mod_cast hp.one_lt)).ne'
  have hshare : log p/(log p+log p)=(1/2 : ℝ) := by field_simp [hx]; ring
  have hcoef : prefixLogCoefficient N L (log p) (log p)=
      2*(1-2*squarePrefix N)*log p+4/L*(squarePrefix N-1)*(log p)^2 := by
    unfold prefixLogCoefficient squarePrefix
    rw [hshare]
    field_simp [hL]
    ring
  have hk := log_mul_kernel N (p^2) s
  have hlog : log (p^2 : ℕ)=2*log p := by rw [Nat.cast_pow,log_pow]; norm_num
  rw [hlog] at hk
  rw [hcoef]
  push_cast
  have hh := congrArg (fun v : ℂ => (2 : ℂ)/(L : ℂ)*((squarePrefix N : ℂ)-1)*(log p : ℂ)*v) hk
  push_cast at hh
  linear_combination hh

/-- The current exhaustive pair expression is exactly one signed
quadratic plus its joined square correction; no count is separately paid. -/
theorem finitePrefix_eq_quadratic_add_square (u y : ℝ) {N : ℕ} (hN : 0<N) (P : ℕ) :
    finitePrefixPairDefect u y N P=(u : ℂ)^(N+1)*
      (factorialQuadratic (primePrefix P) N (SquarefreeVaughanLogSource.length u N)
          (3/2+Complex.I*y)+
        joinedSquare (primePrefix P) N (SquarefreeVaughanLogSource.length u N)
          (3/2+Complex.I*y)) := by
  rw [finitePrefixPairDefect_eq_joined,
    selberg_pairs_eq_trace (primePrefix P) (fun p hp => (Finset.mem_filter.mp hp).2) hN]
  have hd : (∑ p∈primePrefix P,
      (prefixLogCoefficient N (SquarefreeVaughanLogSource.length u N) (log p) (log p) : ℂ)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p^2))=
      2*((1-2*squarePrefix N : ℝ) : ℂ)*finiteSquare (primePrefix P) N (3/2+Complex.I*y)+
      2*((N+1 : ℕ) : ℂ)/(SquarefreeVaughanLogSource.length u N : ℂ)*
        ((squarePrefix N-1 : ℝ) : ℂ)*finiteSquare (primePrefix P) (N+1) (3/2+Complex.I*y) := by
    simp only [finiteSquare,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    simpa only [mul_assoc] using prefix_diagonal_atom N p (Finset.mem_filter.mp hp).2 _
      (SquarefreeVaughanLogSource.length_pos u N).ne' _
  rw [hd]
  unfold factorialQuadratic joinedSquare
  push_cast
  ring

/-- Absolute convergence pays only the square channel, uniformly over
all finite ordinary-prime universes. The signed pair main is untouched. -/
theorem norm_finiteSquare_le (A : Finset ℕ) (hA : ∀ p∈A,p.Prime) (N : ℕ) (y : ℝ) :
    ‖finiteSquare A N (3/2+Complex.I*y)‖≤(4/3 : ℝ)^N*squareMass := by
  unfold finiteSquare
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p∈A,(4/3 : ℝ)^N*ZetaPrimeNonlinearTail.squareLogWeight (3/4) p := by
      apply Finset.sum_le_sum
      intro p hp
      simpa only [squareTerm,if_pos (hA p hp)] using norm_squareTerm_le N y p
    _ = (4/3 : ℝ)^N*∑ p∈A,ZetaPrimeNonlinearTail.squareLogWeight (3/4) p := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((ZetaPrimeNonlinearTail.summable_squareLogWeight (by norm_num : (1/2 : ℝ)<3/4)).sum_le_tsum A
        (fun p _ => by
          unfold ZetaPrimeNonlinearTail.squareLogWeight
          exact mul_nonneg (Real.exp_pos _).le (Real.log_natCast_nonneg p))) (by positivity)

/-- The independent cost of the FULL joined square correction. -/
def squareBudget (u : ℝ) (N : ℕ) : ℝ := (17/6)*(u*squareMass)*(4*u/3)^N

theorem squareBudget_nonneg {u : ℝ} (hu : 0≤u) (N : ℕ) : 0 ≤ squareBudget u N := by
  have hm : 0 ≤ squareMass := tsum_nonneg (fun p => by
    unfold ZetaPrimeNonlinearTail.squareLogWeight
    exact mul_nonneg (Real.exp_pos _).le (Real.log_natCast_nonneg p))
  unfold squareBudget
  positivity

/-- A single rational geometric rate covers EVERY radius in the target
interval; the finite mass constant is independent of height and order. -/
theorem squareBudget_le_uniform {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ) :
    squareBudget u N≤((17/6)*(ZetaRieszWideOwnerAudit.radiusCeiling*squareMass))*
      (10001/15000 : ℝ)^N := by
  have hm : 0 ≤ squareMass := tsum_nonneg (fun p => by
    unfold ZetaPrimeNonlinearTail.squareLogWeight
    exact mul_nonneg (Real.exp_pos _).le (Real.log_natCast_nonneg p))
  have hc : (17/6 : ℝ)*(u*squareMass)≤
      (17/6)*(ZetaRieszWideOwnerAudit.radiusCeiling*squareMass) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hU hm) (by norm_num)
  have hq : 4*u/3≤(10001/15000 : ℝ) := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU
    linarith only [hU]
  unfold squareBudget
  exact mul_le_mul hc (pow_le_pow_left₀ (by positivity : 0≤4*u/3) hq N)
    (pow_nonneg (by positivity) N)
    (mul_nonneg (by norm_num) (mul_nonneg (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]) hm))

/-- A joined correction payment: the combined square error is geometric
AFTER source normalization and needs no exposed-zero or phase hypothesis. -/
theorem norm_normalized_joinedSquare_le {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N)
    (A : Finset ℕ) (hA : ∀ p∈A,p.Prime) (y : ℝ) :
    ‖(u : ℂ)^(N+1)*joinedSquare A N (SquarefreeVaughanLogSource.length u N)
      (3/2+Complex.I*y)‖ ≤ squareBudget u N := by
  have hu0 : 0≤u := by linarith only [hu]
  have hL := SquarefreeVaughanLogSource.length_pos u N
  have hratio : ‖((N+1 : ℕ) : ℂ)/(SquarefreeVaughanLogSource.length u N : ℂ)‖≤1 := by
    rw [norm_div,Complex.norm_natCast,Complex.norm_real,Real.norm_of_nonneg hL.le]
    apply (div_le_one hL).mpr
    have hlo := ZetaRieszPostHingeEnergy.length_ge_rational hN (by linarith : 0<u) hU
    have hn : (65536 : ℝ)≤N := by exact_mod_cast hN
    push_cast
    nlinarith only [hlo,hn]
  obtain ⟨hf0,hf1⟩ := squarePrefix_bounds N
  have ha : ‖((2*squarePrefix N-3/2 : ℝ) : ℂ)‖≤3/2 := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith only [hf0],by linarith only [hf1]⟩
  have hb : ‖((1-squarePrefix N : ℝ) : ℂ)‖≤1 := by
    rw [Complex.norm_real,Real.norm_of_nonneg (by linarith only [hf1])]
    linarith only [hf0]
  have hsq : ‖joinedSquare A N (SquarefreeVaughanLogSource.length u N) (3/2+Complex.I*y)‖≤
      (3/2 : ℝ)*((4/3 : ℝ)^N*squareMass)+(4/3 : ℝ)^(N+1)*squareMass := by
    unfold joinedSquare
    apply (norm_add_le _ _).trans
    simp only [norm_mul]
    apply add_le_add
    · exact mul_le_mul ha (norm_finiteSquare_le A hA N y) (norm_nonneg _) (by norm_num)
    · exact (mul_le_of_le_one_left (norm_nonneg _)
        ((mul_le_of_le_one_left (norm_nonneg _) hratio).trans hb)).trans
        (norm_finiteSquare_le A hA (N+1) y)
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu0]
  apply (mul_le_mul_of_nonneg_left hsq (pow_nonneg hu0 (N+1))).trans_eq
  unfold squareBudget
  rw [pow_succ,pow_succ,show 4*u/3=u*(4/3) by ring,mul_pow]
  ring

/-- The joined square budget tends to zero throughout the current radius
interval, independently of height or a hypothetical source. -/
theorem squareBudget_tendsto {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (squareBudget u) atTop (𝓝 0) := by
  have hr : 4*u/3<1 := by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU; linarith
  change Tendsto (fun N : ℕ => (17/6)*(u*squareMass)*(4*u/3)^N) atTop (𝓝 0)
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0≤4*u/3) hr).const_mul
      ((17/6)*(u*squareMass))

/-- The actual exhaustive pair sum is bounded on both sides by the SAME
joined factorial quadratic and one independent vanishing square budget. -/
theorem norm_finitePrefix_sub_quadratic_le {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) (y : ℝ) (P : ℕ) :
    ‖finitePrefixPairDefect u y N P-(u : ℂ)^(N+1)*
      factorialQuadratic (primePrefix P) N (SquarefreeVaughanLogSource.length u N)
        (3/2+Complex.I*y)‖ ≤ squareBudget u N := by
  rw [finitePrefix_eq_quadratic_add_square u y (by omega : 0<N) P,mul_add,add_sub_cancel_left]
  exact norm_normalized_joinedSquare_le hu hU hN _ (fun p hp => (Finset.mem_filter.mp hp).2) y

/-- The independent completion and joined square costs together leave
exactly the coupled factorial quadratic in the original signed target. -/
theorem eventually_norm_prefix_sub_quadratic_le {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    {N : ℕ} (hN : 65536≤N) :
    ∀ᶠ P : ℕ in atTop,
      ‖prefixPairDefect u y N-(u : ℂ)^(N+1)*
        factorialQuadratic (primePrefix P) N (SquarefreeVaughanLogSource.length u N)
          (3/2+Complex.I*y)‖≤wholeCompletionBudget N+squareBudget u N := by
  filter_upwards [eventually_norm_whole_completion_le hu hU hy hN] with P hP
  have hs := norm_finitePrefix_sub_quadratic_le hu hU hN y P
  exact (norm_sub_le_norm_sub_add_norm_sub _ (finitePrefixPairDefect u y N P) _).trans
    (add_le_add (by simpa only [norm_sub_rev] using hP) hs)

/-- The new square payment is spent ONCE in the literal whole-core floor.
The coupled quadratic remains the single unpaid signed term. -/
theorem eventually_native_quadratic_floor {u C : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (hC : 1≤C)
    (ha : ∀ k,‖(u : ℂ)^(k+1)*zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖≤C) :
    ∀ᶠ j in atTop,∀ᶠ P : ℕ in atTop,
      -((u : ℂ)^(dyadicMomentOrder j+1)*
        factorialQuadratic (primePrefix P) (dyadicMomentOrder j)
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (3/2+Complex.I*y)).re-
        (nativeSelbergBudget u y C j+prefixBudget (dyadicMomentOrder j)+
          wholeCompletionBudget (dyadicMomentOrder j)+squareBudget u (dyadicMomentOrder j))≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
        (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  filter_upwards [eventually_native_whole_pair_floor hu hU hy hC ha,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop 65536)] with j hf hN
  filter_upwards [hf] with P hP
  have hs := norm_finitePrefix_sub_quadratic_le hu.le hU hN y P
  have he := Complex.re_le_norm (finitePrefixPairDefect u y (dyadicMomentOrder j) P-
    (u : ℂ)^(dyadicMomentOrder j+1)*factorialQuadratic (primePrefix P) (dyadicMomentOrder j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (3/2+Complex.I*y))
  rw [Complex.sub_re] at he
  linarith only [hP,he,hs]

/-- All FOUR costs vanish under the original simple exposed-zero
hypotheses. The independent `399/5000` upper bound is not a conclusion. -/
theorem exists_native_quadratic_payment_simple (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      ‖(3/2:ℂ)+Complex.I*rho.1.im-tau.1‖>3/2-rho.1.re)
    (hm : analyticZetaZeroMultiplicity rho=1)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|rho.1.im|) :
    ∃ C : ℝ,1≤C ∧
      Tendsto (fun j => nativeSelbergBudget (3/2-rho.1.re) rho.1.im C j+
        prefixBudget (dyadicMomentOrder j)+wholeCompletionBudget (dyadicMomentOrder j)+
          squareBudget (3/2-rho.1.re) (dyadicMomentOrder j)) atTop (𝓝 0) ∧
      ∀ᶠ j in atTop,∀ᶠ P : ℕ in atTop,
        -((((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1))*
          factorialQuadratic (primePrefix P) (dyadicMomentOrder j)
            (SquarefreeVaughanLogSource.length (3/2-rho.1.re) (dyadicMomentOrder j))
              (3/2+Complex.I*rho.1.im)).re-
          (nativeSelbergBudget (3/2-rho.1.re) rho.1.im C j+
            prefixBudget (dyadicMomentOrder j)+wholeCompletionBudget (dyadicMomentOrder j)+
              squareBudget (3/2-rho.1.re) (dyadicMomentOrder j))≤
        (((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse
          (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)
            (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  obtain ⟨C,hC,hcost,hfloor⟩ := exists_native_whole_pair_payment_simple rho hrho hexposed hm hU hy
  have hu : 1/2≤3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  refine ⟨C,hC,?_,?_⟩
  · simpa only [add_zero,Function.comp_def] using hcost.add
      ((squareBudget_tendsto (by linarith only [hu] : 0≤3/2-rho.1.re) hU).comp
        tendsto_dyadicMomentOrder)
  · filter_upwards [hfloor,tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop 65536)]
      with j hf hN
    filter_upwards [hf] with P hP
    have hs := norm_finitePrefix_sub_quadratic_le hu hU hN rho.1.im P
    have he := Complex.re_le_norm (finitePrefixPairDefect (3/2-rho.1.re) rho.1.im
      (dyadicMomentOrder j) P-(((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1))*
        factorialQuadratic (primePrefix P) (dyadicMomentOrder j)
          (SquarefreeVaughanLogSource.length (3/2-rho.1.re) (dyadicMomentOrder j))
            (3/2+Complex.I*rho.1.im))
    rw [Complex.sub_re] at he
    linarith only [hP,he,hs]

end RiemannGaussian.ZetaRieszPairJointQuadratic
