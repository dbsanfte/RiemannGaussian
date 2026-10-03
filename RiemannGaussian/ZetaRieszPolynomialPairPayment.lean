/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSignedSelbergPayment
import RiemannGaussian.ZetaRieszSemiprimeCompletion

/-!
# Pay polynomial-small cofactors in the literal signed pair defect

Complete only the larger prime, after retaining the full factorial
translation and product phase. The smaller prime is still literal. All
original windows and head/correction masks are retained in the finite
defect; their exterior discrepancy is independently geometrically paid.
This conditional payment does not prove the remaining arithmetic floor.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszPolynomialPairPayment
open ZetaRieszSignedSelbergPayment ZetaRieszLowCountSelbergAudit
open ZetaRieszLowCountSignedBoundary ZetaRieszGlobalPeriodEdgePayment
open ZetaRieszGlobalCentralPayment ZetaRieszGlobalBulkPayment
open ZetaRieszGlobalHeadCentralPayment
open ZetaRieszCompletedCofactor ZetaPrimeCofactorCompletion
open ZetaRieszSemiprimeCompletion ZetaExposedZero
open ZetaRieszUnallocatedOwnerPayment ZetaRieszPrimeEndpoint

/-- The smaller prime cutoff is polynomial; it is not a fixed log-share mask. -/
def smallPrimes (N : ℕ) : Finset ℕ := (Finset.Icc 1 (N^16)).filter Nat.Prime

theorem smallPrimes_data {N q : ℕ} (hq : q∈smallPrimes N) :
    q.Prime ∧ q≤N^16 := by
  obtain ⟨hq,hqp⟩ := Finset.mem_filter.mp hq
  exact ⟨hqp,(Finset.mem_Icc.mp hq).2⟩

/-- Explicit arithmetic mass after completing the larger prime with its phase. -/
def cofactorMass (beta : ℝ) (N : ℕ) : ℝ :=
  ∑ q∈smallPrimes N,log q*(1+log q)*exp (-beta*log q)

/-- Fixed real-power slack absorbs both logarithms. In the restricted
zero strip the exponent below is negative, with a large rational margin. -/
theorem exists_cofactorMass_power_bound {beta : ℝ} (hb : beta<1) :
    ∃ D : ℝ,0≤D ∧ ∀ N : ℕ,
      cofactorMass beta N≤D*(N : ℝ)^(16*(1-beta+1/128)) := by
  let alpha : ℝ := 1-beta+1/128
  have ha : 0<alpha := by dsimp [alpha]; linarith
  let D : ℝ := ((1/128 : ℝ)⁻¹+2*(1/128 : ℝ)⁻¹^2)*(1+1/alpha)
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  intro N
  have h := cofactor_log_mass_prefix_le (beta:=beta) (eps:=1/128)
    (by norm_num) ha (smallPrimes N) (N^16)
    (fun q hq => ⟨(smallPrimes_data hq).1.pos,(smallPrimes_data hq).2⟩)
  change cofactorMass beta N≤D*((N^16 : ℕ) : ℝ)^alpha at h
  rw [Nat.cast_pow,←Real.rpow_natCast_mul (Nat.cast_nonneg N)] at h
  simpa [alpha] using h

theorem cofactor_power_margin {beta : ℝ} (hb : 19999/20000≤beta) :
    16*(1-beta+1/128)<1/5 := by linarith

/-- The complete signed larger-prime row is paid before summing small
cofactors. No absolute source envelope is used on its prime phase. -/
theorem tendsto_cofactorMass_div_length {beta u : ℝ}
    (hb : 19999/20000≤beta) (hb1 : beta<1) (hu : 0<u) (hu1 : u<1) :
    Tendsto (fun N => cofactorMass beta N/SquarefreeVaughanLogSource.length u N)
      atTop (𝓝 0) := by
  obtain ⟨D,hD,hbound⟩ := exists_cofactorMass_power_bound hb1
  obtain ⟨c,hc,hL⟩ := eventually_linear_length_lower hu hu1
  let a : ℝ := 16*(1-beta+1/128)
  have ha : a<1 := by dsimp [a]; linarith [cofactor_power_margin hb]
  have ht := ((tendsto_rpow_neg_atTop (show 0<1-a by linarith)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul (D/c)
  apply squeeze_zero' (Eventually.of_forall fun N => by
    unfold cofactorMass
    exact div_nonneg (Finset.sum_nonneg fun q _ => by positivity)
      (SquarefreeVaughanLogSource.length_pos u N).le) ?_ (by simpa only [mul_zero] using ht)
  filter_upwards [hL,eventually_ge_atTop 1] with N hLN hN
  have hNp : (0 : ℝ)<N := by exact_mod_cast hN
  calc
    _ ≤ (D*(N : ℝ)^a)/SquarefreeVaughanLogSource.length u N :=
      div_le_div_of_nonneg_right (hbound N) (SquarefreeVaughanLogSource.length_pos u N).le
    _ ≤ (D*(N : ℝ)^a)/(c*N) := div_le_div_of_nonneg_left (by positivity)
      (mul_pos hc hNp) hLN
    _ = D/c*(N : ℝ)^(-(1-a)) := by
      rw [show -(1-a)=a-1 by ring,Real.rpow_sub_one hNp.ne']
      ring

theorem tendsto_cofactorMass_div_order {beta : ℝ}
    (hb : 19999/20000≤beta) (hb1 : beta<1) :
    Tendsto (fun N => cofactorMass beta N/(N : ℝ)) atTop (𝓝 0) := by
  obtain ⟨D,hD,hbound⟩ := exists_cofactorMass_power_bound hb1
  let a : ℝ := 16*(1-beta+1/128)
  have ha : a<1 := by dsimp [a]; linarith [cofactor_power_margin hb]
  have ht := ((tendsto_rpow_neg_atTop (show 0<1-a by linarith)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul D
  apply squeeze_zero' (Eventually.of_forall fun N => by
    unfold cofactorMass
    exact div_nonneg (Finset.sum_nonneg fun q _ => by positivity) (Nat.cast_nonneg N))
    ?_ (by simpa only [mul_zero] using ht)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNp : (0 : ℝ)<N := by exact_mod_cast hN
  calc
    _ ≤ (D*(N : ℝ)^a)/N := div_le_div_of_nonneg_right (hbound N) hNp.le
    _ = D*(N : ℝ)^(-(1-a)) := by
      rw [show -(1-a)=a-1 by ring,Real.rpow_sub_one hNp.ne']
      ring

/-- Complete Selberg pair row, with one literal small cofactor. -/
def loggedPairLift (q n : ℕ) : ℂ :=
  if q∣n ∧ (n/q).Prime then ((2*log q*log (n/q : ℕ)/log n : ℝ) : ℂ) else 0

/-- Completed incidence coefficient, with all duplicate exterior factorizations kept. -/
def smallCoefficient (u : ℝ) (N n : ℕ) : ℂ :=
  integerCoefficient (SquarefreeVaughanLogSource.length u N) (smallPrimes N) n+
    ∑ q∈smallPrimes N,loggedPairLift q n

/-- The completed polynomial coefficient is exactly the original
two-hinge row minus Selberg on the actual interior. Duplicate small-factor
incidences are kept here; they occur only on paid radial exteriors. -/
def completedSmall (u y : ℝ) (N : ℕ) : ℂ :=
  completedCofactorHead (smallPrimes N) 1 N (3/2+Complex.I*y)
    (SquarefreeVaughanLogSource.length u N)+
  (2/(N : ℂ))*∑ q∈smallPrimes N,(log q : ℂ)*
    ∑' p : ℕ,if p.Prime then (ArithmeticFunction.vonMangoldt p : ℂ)*
      zetaPrimeLogKernel (N-1) (3/2+Complex.I*y) (q*p) else 0

theorem loggedPairLift_kernel {q p : ℕ} (hq : 0<q) (hp : p.Prime)
    {N : ℕ} (hN : 0<N) (s : ℂ) :
    loggedPairLift q (q*p)*zetaPrimeLogKernel N s (q*p)=
      (2/(N : ℂ))*(log q : ℂ)*(ArithmeticFunction.vonMangoldt p : ℂ)*
        zetaPrimeLogKernel (N-1) s (q*p) := by
  have ht : log (q*p : ℕ)≠0 := (log_pos (by exact_mod_cast
    (show 1<q*p by nlinarith only [hq,hp.two_le]))).ne'
  have hNr : (N : ℂ)≠0 := by exact_mod_cast hN.ne'
  have hk : zetaPrimeLogKernel N s (q*p)=
      (log (q*p : ℕ) : ℂ)*zetaPrimeLogKernel (N-1) s (q*p)/(N : ℂ) := by
    apply (eq_div_iff hNr).mpr
    simpa only [show N-1+1=N by omega,mul_comm] using
      (ZetaRieszHeadOrders.log_mul_kernel (N-1) (q*p) s).symm
  simp only [loggedPairLift,dvd_mul_right,Nat.mul_div_right _ hq,hp,and_self,
    if_true,ArithmeticFunction.vonMangoldt_apply_prime hp]
  rw [hk]
  simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat]
  have htC : (log (q*p : ℕ) : ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht
  calc
    _ = (2/(N : ℂ))*(log q : ℂ)*(log p : ℂ)*
        zetaPrimeLogKernel (N-1) s (q*p)*
          ((log (q*p : ℕ) : ℂ)*(log (q*p : ℕ) : ℂ)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ htC,mul_one]

theorem hasSum_loggedPairLift {q : ℕ} (hq : 0<q) {N : ℕ} (hN : 0<N)
    {s : ℂ} (hs : 1<s.re) :
    HasSum (fun n => loggedPairLift q n*zetaPrimeLogKernel N s n)
      ((2/(N : ℂ))*(log q : ℂ)*
        ∑' p : ℕ,if p.Prime then (ArithmeticFunction.vonMangoldt p : ℂ)*
          zetaPrimeLogKernel (N-1) s (q*p) else 0) := by
  have hinj : Function.Injective (fun p : ℕ => q*p) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_left hq h
  have hz (n : ℕ) (hn : n∉Set.range (fun p : ℕ => q*p)) :
      loggedPairLift q n*zetaPrimeLogKernel N s n=0 := by
    have hd : ¬q∣n := fun h => hn ⟨n/q,Nat.mul_div_cancel' h⟩
    simp [loggedPairLift,hd]
  apply (hinj.hasSum_iff hz).mp
  apply ((hasSum_prime_log_product hs (N-1) hq).summable.hasSum.mul_left
    ((2/(N : ℂ))*(log q : ℂ))).congr_fun
  intro p
  by_cases hp : p.Prime
  · simpa only [Function.comp_apply,if_pos hp,mul_assoc] using loggedPairLift_kernel hq hp hN s
  · simp [Function.comp_apply,loggedPairLift,Nat.mul_div_right _ hq,hp]

theorem hasSum_smallCoefficient (u y : ℝ) {N : ℕ} (hN : 0<N) :
    HasSum (fun n => smallCoefficient u N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)
      (completedSmall u y N) := by
  have h1 := hasSum_integerCoefficient (smallPrimes N)
    (fun q hq => (smallPrimes_data hq).1.pos) (SquarefreeVaughanLogSource.length u N)
      (1 : Polynomial ℂ) N (by norm_num : 1<(3/2+Complex.I*(y : ℂ)).re)
  simp only [SquarefreeEulerQuadratic.primeFilterKernel_one] at h1
  have h2 := hasSum_sum (s:=smallPrimes N) (fun q hq =>
    hasSum_loggedPairLift (smallPrimes_data hq).1.pos hN
      (by norm_num : 1<(3/2+Complex.I*(y : ℂ)).re))
  simp only [mul_assoc,←Finset.mul_sum] at h2
  simpa only [completedSmall] using (h1.add h2).congr_fun (fun n => by
    simp only [smallCoefficient,add_mul,Finset.sum_mul,zetaPrimeLogKernel])

/-- Both exact completed rows have a vanishing cofactor budget. This
is conditional on exposure, but does not require simplicity. -/
theorem tendsto_completedSmall (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => ((3/2-rho.1.re : ℝ) : ℂ)^(N+1)*
      completedSmall (3/2-rho.1.re) rho.1.im N) atTop (𝓝 0) := by
  let u : ℝ := 3/2-rho.1.re
  let s : ℂ := 3/2+Complex.I*(rho.1.im : ℂ)
  have hu : 0<u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u<1 := by dsimp [u]; linarith
  have hb : 19999/20000≤rho.1.re := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU
    linarith
  obtain ⟨C,hC,hhead⟩ := exists_completedCofactorHead_bound rho hrho hexposed
  have hheadlim : Tendsto (fun N => (u : ℂ)^(N+1)*
      completedCofactorHead (smallPrimes N) 1 N s (SquarefreeVaughanLogSource.length u N))
      atTop (𝓝 0) := by
    have ht := (tendsto_cofactorMass_div_length hb
      (NontrivialZetaZero.re_lt_one rho) hu hu1).const_mul C
    apply squeeze_zero_norm (fun N => ?_) (by simpa only [mul_zero] using ht)
    have h := hhead (smallPrimes N) (fun q hq => (smallPrimes_data hq).1.pos)
      1 N (SquarefreeVaughanLogSource.length u N) (SquarefreeVaughanLogSource.length_pos u N)
    have hsupp : (1 : Polynomial ℂ).support={0} := by
      rw [←Polynomial.C_1,Polynomial.support_C one_ne_zero]
    simpa only [hsupp,Finset.sum_singleton,Polynomial.coeff_one_zero,norm_one,pow_zero,
      mul_one,cofactorMass,u,s,div_mul_eq_mul_div,mul_div_assoc] using h
  obtain ⟨D,hD,hlogged⟩ := exists_prime_log_product_bound rho hrho hexposed
  have hloggedlim : Tendsto (fun N : ℕ => (u : ℂ)^(N+1)*((2/(N : ℂ))*
      ∑ q∈smallPrimes N,(log q : ℂ)*
        ∑' p : ℕ,if p.Prime then (ArithmeticFunction.vonMangoldt p : ℂ)*
          zetaPrimeLogKernel (N-1) s (q*p) else 0)) atTop (𝓝 0) := by
    have ht := (tendsto_cofactorMass_div_order hb
      (NontrivialZetaZero.re_lt_one rho)).const_mul (2*u*D)
    apply squeeze_zero_norm' ?_ (by simpa only [mul_zero] using ht)
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNp : (0 : ℝ)<N := by exact_mod_cast hN
    have he : (u : ℂ)^(N+1)*((2/(N : ℂ))*
        ∑ q∈smallPrimes N,(log q : ℂ)*
          ∑' p : ℕ,if p.Prime then (ArithmeticFunction.vonMangoldt p : ℂ)*
            zetaPrimeLogKernel (N-1) s (q*p) else 0)=
        ((2*u/N : ℝ) : ℂ)*∑ q∈smallPrimes N,(log q : ℂ)*
          ((u : ℂ)^N*∑' p : ℕ,if p.Prime then (ArithmeticFunction.vonMangoldt p : ℂ)*
            zetaPrimeLogKernel (N-1) s (q*p) else 0) := by
      simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat,
        Complex.ofReal_natCast,Finset.mul_sum,pow_succ]
      exact Finset.sum_congr rfl (fun q _ => by ring)
    rw [he,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (2*u/N)*∑ q∈smallPrimes N,log q*(D*exp (-rho.1.re*log q)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro q hq
        rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (log_natCast_nonneg q)]
        simpa only [show N-1+1=N by omega] using
          mul_le_mul_of_nonneg_left (hlogged q (smallPrimes_data hq).1.pos (N-1))
            (log_natCast_nonneg q)
      _ ≤ (2*u/N)*(D*cofactorMass rho.1.re N) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [cofactorMass,Finset.mul_sum]
        apply Finset.sum_le_sum
        intro q _
        have hq := log_natCast_nonneg q
        have hE := (exp_pos (-rho.1.re*log q)).le
        nlinarith [mul_nonneg (mul_nonneg hD (sq_nonneg (log q))) hE]
      _ = _ := by ring
  simpa only [completedSmall,mul_add,add_zero] using hheadlim.add hloggedlim

/-- A product of two primes has at most two selected prime-cofactor
incidences, including the repeated-prime exterior. -/
private theorem cofactor_incidence_card_le (A : Finset ℕ)
    (hA : ∀ q∈A,q.Prime) (n : ℕ) :
    (A.filter (fun q => q∣n ∧ (n/q).Prime)).card≤2 := by
  let S := A.filter (fun q => q∣n ∧ (n/q).Prime)
  by_cases hS : S.Nonempty
  · obtain ⟨q,hq⟩ := hS
    obtain ⟨hqA,hqd,hp⟩ := Finset.mem_filter.mp hq
    have he : q*(n/q)=n := Nat.mul_div_cancel' hqd
    have hs : S⊆{q,n/q} := by
      intro b hb
      obtain ⟨hbA,hbd,_⟩ := Finset.mem_filter.mp hb
      have hbP := hA b hbA
      rcases hbP.dvd_mul.mp (he ▸ hbd) with hd | hd
      · simp [(Nat.prime_dvd_prime_iff_eq hbP (hA q hqA)).mp hd]
      · simp [(Nat.prime_dvd_prime_iff_eq hbP hp).mp hd]
    exact (Finset.card_le_card hs).trans (by
      simpa only [Finset.card_singleton] using Finset.card_insert_le q {n/q})
  · change S.card≤2
    rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.card_empty]
    norm_num

theorem norm_loggedPairLift_le {q : ℕ} (hq : q.Prime) (n : ℕ) :
    ‖loggedPairLift q n‖≤log n := by
  by_cases hd : q∣n ∧ (n/q).Prime
  · let p := n/q
    have hp : p.Prime := hd.2
    have he : q*p=n := Nat.mul_div_cancel' hd.1
    have ht : log n=log q+log p := by
      rw [←he,Nat.cast_mul,log_mul (by exact_mod_cast hq.ne_zero)
        (by exact_mod_cast hp.ne_zero)]
    have hpos : 0<log n := log_pos (by exact_mod_cast
      (show 1<n by rw [←he]; nlinarith only [hq.two_le,hp.two_le]))
    have h0 : 0≤2*log q*log p/log n := by positivity
    rw [loggedPairLift,if_pos hd,Complex.norm_real,Real.norm_of_nonneg h0]
    apply (div_le_iff₀ hpos).mpr
    rw [ht]
    nlinarith [sq_nonneg (log q),sq_nonneg (log p)]
  · simp only [loggedPairLift,if_neg hd,norm_zero]
    exact log_natCast_nonneg n

theorem norm_loggedCoefficient_le (A : Finset ℕ)
    (hA : ∀ q∈A,q.Prime) (n : ℕ) :
    ‖∑ q∈A,loggedPairLift q n‖≤2*log n := by
  let S := A.filter (fun q => q∣n ∧ (n/q).Prime)
  have he : (∑ q∈A,loggedPairLift q n)=∑ q∈S,loggedPairLift q n := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun q _ => by
      by_cases h : q∣n ∧ (n/q).Prime <;> simp [loggedPairLift,h])
  rw [he]
  calc
    _ ≤ ∑ q∈S,log n := (norm_sum_le _ _).trans (Finset.sum_le_sum fun q hq =>
      norm_loggedPairLift_le (hA q (Finset.mem_filter.mp hq).1) n)
    _ = (S.card : ℝ)*log n := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast cofactor_incidence_card_le A hA n) (log_natCast_nonneg n)

/-- This global majorant funds exterior completion only. It is never
spent on the retained central pair defect. -/
theorem norm_smallCoefficient_le {u : ℝ} {N : ℕ}
    (hcut : 2*log (N^16 : ℕ)≤SquarefreeVaughanLogSource.length u N) (n : ℕ) :
    ‖smallCoefficient u N n‖≤3*zetaMoebiusLogMajorant n := by
  have hi := norm_integerCoefficient_le_majorant (smallPrimes N) (N^16) n
    (fun q hq => smallPrimes_data hq) (SquarefreeVaughanLogSource.length_pos u N) hcut
  have hl := norm_loggedCoefficient_le (smallPrimes N)
    (fun q hq => (smallPrimes_data hq).1) n
  have hc := ZetaRieszCentralWindow.log_le_divisor_majorant n
  exact (norm_add_le _ _).trans (by linarith only [hi,hl,hc])

/-- The entire polynomial prefix has negligible log-share. This is a
proved eventual fact, not a replacement of any finite-order mask. -/
theorem eventually_small_log : ∀ᶠ N : ℕ in atTop,log (N^16 : ℕ)≤(N : ℝ)/10 := by
  have ht : Tendsto (fun N : ℕ => 16*log N/(N : ℝ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))
    simpa only [Function.comp_def,pow_one,one_mul,add_zero,mul_div_assoc,mul_zero]
      using h.const_mul 16
  filter_upwards [ht.eventually_lt_const (by norm_num : (0 : ℝ)<1/10),
    eventually_ge_atTop 1] with N hN hNp
  have hn : (0 : ℝ)<N := by exact_mod_cast hNp
  rw [Nat.cast_pow,log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [(div_lt_iff₀ hn).mp hN]

/-- A distinct pair whose uniquely smaller prime belongs to the polynomial prefix. -/
def SmallPair (N n : ℕ) : Prop :=
  ∃ q∈smallPrimes N,∃ p : ℕ,p.Prime ∧ q<p ∧ n=q*p

/-- Literal subpopulation of exactly the current retained support.
Every old owner, head, allocation, physical and phase mask remains. -/
def literalSmallLabels (u y : ℝ) (N : ℕ) : Finset ℕ :=
  (completePeriodLabels (joinedLabels u N) N y).filter (SmallPair N)

/-- Actual signed small-cofactor subexpression on the original retained periods. -/
def literalSmall (u y : ℝ) (N : ℕ) : ℂ :=
  (u : ℂ)^(N+1)*∑ n∈literalSmallLabels u y N,
    selbergDefect u N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- Zero extension of that literal subexpression, used only for exterior transport. -/
def maskedSmallCoefficient (u y : ℝ) (N n : ℕ) : ℂ :=
  if n∈literalSmallLabels u y N then selbergDefect u N n else 0

theorem norm_maskedSmallCoefficient_le {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    {N : ℕ} (hN : 65536≤N) (n : ℕ) :
    ‖maskedSmallCoefficient u y N n‖≤2*zetaMoebiusLogMajorant n := by
  unfold maskedSmallCoefficient
  split_ifs with hn
  · have hs := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    have hb := joinedCoefficient_majorant hu hU hN n
    have ht := norm_selbergCoefficient_le (joinedLabels_ordinary hu hU hN hs)
    have hl := ZetaRieszCentralWindow.log_le_divisor_majorant n
    exact (norm_sub_le _ _).trans (by linarith only [hb,ht,hl])
  · simpa only [norm_zero] using mul_nonneg (by norm_num : (0 : ℝ)≤2)
      (zetaMoebiusLogMajorant_nonneg n)

private theorem smallCoefficient_pair {u : ℝ} {N p q : ℕ}
    (hq : q∈smallPrimes N) (hp : p.Prime) (hpn : p∉smallPrimes N) :
    smallCoefficient u N (q*p)=
      ((-log (q*p : ℕ)*log q/SquarefreeVaughanLogSource.length u N+
        2*log q*log p/log (q*p : ℕ) : ℝ) : ℂ) := by
  have hqP := (smallPrimes_data hq).1
  have hother (a : ℕ) (ha : a∈smallPrimes N) (hne : a≠q) : ¬a∣q*p := by
    intro hd
    have haP := (smallPrimes_data ha).1
    rcases haP.dvd_mul.mp hd with hd | hd
    · exact hne ((Nat.prime_dvd_prime_iff_eq haP hqP).mp hd)
    · exact hpn ((Nat.prime_dvd_prime_iff_eq haP hp).mp hd ▸ ha)
  rw [smallCoefficient,integerCoefficient,
    Finset.sum_eq_single q (by
      intro a ha hne
      simp [pairLift,hother a ha hne]) (by exact fun h => (h hq).elim),
    Finset.sum_eq_single q (by
      intro a ha hne
      simp [loggedPairLift,hother a ha hne]) (by exact fun h => (h hq).elim)]
  simp only [pairLift,loggedPairLift,dvd_mul_right,Nat.mul_div_right _ hqP.pos,hp,
    and_self,if_true,←Complex.ofReal_add]

/-- Canonical masks disappear only by their exact support conditions:
the large prime exceeds the physical length on this interior population. -/
private theorem interior_small_pair_eq {u y : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|)
    {N p q : ℕ} (hN : 65536≤N)
    (hcut : log (N^16 : ℕ)≤(N : ℝ)/10) (hq : q∈smallPrimes N) (hp : p.Prime)
    (hl : (1971/1000 : ℝ)*N+1<log (q*p : ℕ))
    (hh : log (q*p : ℕ)≤(2029/1000 : ℝ)*N-1) :
    q*p∈literalSmallLabels u y N ∧
      smallCoefficient u N (q*p)=selbergDefect u N (q*p) := by
  have hqP := (smallPrimes_data hq).1
  have hqlog : log q≤log (N^16 : ℕ) := log_le_log
    (by exact_mod_cast hqP.pos) (by exact_mod_cast (smallPrimes_data hq).2)
  have ht : log (q*p : ℕ)=log q+log p := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hqP.ne_zero) (by exact_mod_cast hp.ne_zero)]
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hpq : q<p := by
    apply (Nat.cast_lt (α:=ℝ)).mp
    apply (log_lt_log_iff (by exact_mod_cast hqP.pos) (by exact_mod_cast hp.pos)).mp
    nlinarith only [hl,ht,hqlog,hcut,hNp]
  have hpn : p∉smallPrimes N := by
    intro h
    have hpl : log p≤log (N^16 : ℕ) := log_le_log
      (by exact_mod_cast hp.pos) (by exact_mod_cast (smallPrimes_data h).2)
    nlinarith only [hl,ht,hqlog,hpl,hcut,hNp]
  have hLhi := ZetaRieszSmallTagNativeFloor.length_upper hu (by omega : 2≤N)
  have hLlo := ZetaRieszPostHingeEnergy.length_ge_rational hN (by linarith : 0<u) hU
  have hpL : SquarefreeVaughanLogSource.length u N<log p := by
    nlinarith only [hLhi,hl,ht,hqlog,hcut,hNp]
  have hqL : log q≤SquarefreeVaughanLogSource.length u N := by
    nlinarith only [hLlo,hqlog,hcut,hNp]
  have hOrd := pair_ordinaryLabel hqP hp hpq.ne
  have hjoin := interior_ordinary_mem_joined (u:=u) hOrd hl hh
  have hsmall : q*p∈literalSmallLabels u y N := Finset.mem_filter.mpr
    ⟨interiorLabels_subset_completePeriods _ _ hy (Finset.mem_filter.mpr ⟨hjoin,hl,hh⟩),
      q,hq,p,hp,hpq,rfl⟩
  have hlarge : ZetaRieszPrimeEndpoint.largestPrime (q*p)=p := by
    rw [mul_comm]
    apply ZetaRieszPrimeIntervals.largestPrime_mul p q hp hqP.ne_zero
    intro a ha
    rw [hqP.primeFactors,Finset.mem_singleton] at ha
    subst a
    exact hpq
  have hnotcorr : q*p∉correctionLabels u N := by
    intro h
    obtain ⟨e,he,hprod⟩ := Finset.mem_image.mp h
    have heq : e.1=p := by
      rw [←correction_largest hu hU hN he,hprod,hlarge]
    have howner := (Finset.mem_sigma.mp he).1
    have hle := (highOwner_data howner).2.2.2
    rw [heq] at hle
    exact (not_le.mpr hpL) hle
  have hnothead : q*p∉headLabels u N := fun h => hnotcorr (headLabels_subset_correction u N h)
  have hc : q*p∈primeLabels N∪semiprimeLabels N :=
    (Finset.mem_union.mp hjoin).resolve_right hnotcorr
  have hs : Squarefree (q*p) := by
    rcases hOrd with h | h
    · exact (Nat.not_prime_mul hqP.ne_one hp.ne_one h).elim
    · exact h.1
  have hR : VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) (q*p)=log q := by
    rw [ZetaRieszSemiprimePrefixDecay.riesz_semiprime_eq_tent _ hqP hp hpq.ne]
    unfold ZetaSquarefreeRieszWindows.primePairTent
    rw [max_eq_right (SquarefreeVaughanLogSource.length_pos u N).le,
      max_eq_right (sub_nonneg.mpr hqL),max_eq_left (sub_nonpos.mpr hpL.le),
      max_eq_left (by linarith only [hpL,log_natCast_nonneg q])]
    ring
  refine ⟨hsmall,?_⟩
  rw [smallCoefficient_pair hq hp hpn,selbergDefect,joinedCoefficient,if_pos hc,
    if_neg hnothead,if_neg hnotcorr,add_zero,sub_zero,
    selbergCoefficient_pair_ne hqP hp hpq.ne]
  simp only [completedCoefficient,if_pos hs,hR,←Complex.ofReal_sub]
  congr 1
  ring

/-- Every interior completed incidence is the unique literal small
cofactor. Every other interior label has zero coefficient on both sides. -/
theorem interior_coefficient_eq {u y : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|)
    {N n : ℕ} (hN : 65536≤N) (hcut : log (N^16 : ℕ)≤(N : ℝ)/10)
    (hl : (1971/1000 : ℝ)*N+1<log n)
    (hh : log n≤(2029/1000 : ℝ)*N-1) :
    smallCoefficient u N n=maskedSmallCoefficient u y N n := by
  by_cases hex : ∃ q∈smallPrimes N,q∣n ∧ (n/q).Prime
  · obtain ⟨q,hq,hqd,hp⟩ := hex
    have he : q*(n/q)=n := Nat.mul_div_cancel' hqd
    have h := interior_small_pair_eq hu hU hy hN hcut hq hp (he.symm ▸ hl) (he.symm ▸ hh)
    rw [he] at h
    simpa only [maskedSmallCoefficient,if_pos h.1] using h.2
  · have hzero : smallCoefficient u N n=0 := by
      have hnot (q : ℕ) (hq : q∈smallPrimes N) : ¬(q∣n ∧ (n/q).Prime) :=
        fun h => hex ⟨q,hq,h⟩
      simp only [smallCoefficient,integerCoefficient]
      rw [Finset.sum_eq_zero (fun q hq => by simp [pairLift,hnot q hq]),
        Finset.sum_eq_zero (fun q hq => by simp [loggedPairLift,hnot q hq]),add_zero]
    have hn : n∉literalSmallLabels u y N := by
      intro h
      obtain ⟨_hS,q,hq,p,hp,_hqp,he⟩ := Finset.mem_filter.mp h
      apply hex
      refine ⟨q,hq,he ▸ dvd_mul_right q p,?_⟩
      simpa only [he,Nat.mul_div_right _ (smallPrimes_data hq).1.pos] using hp
    simp [hzero,maskedSmallCoefficient,hn]

/-- An independent uniform geometric price for the actual support
discrepancy. Only its exterior is norm-estimated; the prime row has already
been summed with its correlated factorial weights and product phase. -/
theorem exists_literalSmall_completion_bound :
    ∃ C : ℝ,0≤C ∧ ∀ (u y : ℝ),1/2≤u→u≤ZetaRieszWideOwnerAudit.radiusCeiling→
      54≤|y|→∀ N : ℕ,65536≤N→log (N^16 : ℕ)≤(N : ℝ)/10→
      ‖(u : ℂ)^(N+1)*completedSmall u y N-literalSmall u y N‖≤
        ZetaRieszLargeOrderCore.rate^N*C := by
  obtain ⟨C,hC,hb⟩ := exists_displaced_edge_bound
  refine ⟨5*C,by positivity,?_⟩
  intro u y hu hU hy N hN hlog
  have hLlo := ZetaRieszPostHingeEnergy.length_ge_rational hN (by linarith : 0<u) hU
  have hcut : 2*log (N^16 : ℕ)≤SquarefreeVaughanLogSource.length u N := by
    nlinarith only [hlog,hLlo,Nat.cast_nonneg (α:=ℝ) N]
  let g : ℕ→ℂ := fun n => smallCoefficient u N n-maskedSmallCoefficient u y N n
  let a : ℕ→ℂ := fun n => g n/5
  have ha (n : ℕ) : ‖a n‖≤zetaMoebiusLogMajorant n := by
    have hg : ‖g n‖≤5*zetaMoebiusLogMajorant n := (norm_sub_le _ _).trans (by
      linarith only [norm_smallCoefficient_le hcut n,norm_maskedSmallCoefficient_le hu hU y hN n])
    dsimp only [a]
    rw [norm_div,show ‖(5 : ℂ)‖=(5 : ℝ) by norm_num]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ)<5)).mpr (by linarith only [hg])
  have hbound (P : ℕ) :
      ‖(u : ℂ)^(N+1)*∑ n∈Finset.range P,g n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖≤
        ZetaRieszLargeOrderCore.rate^N*(5*C) := by
    have he : (∑ n∈interiorLabels (Finset.range P) N,a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)=0 := by
      apply Finset.sum_eq_zero
      intro n hn
      obtain ⟨_hn,hl,hh⟩ := Finset.mem_filter.mp hn
      simp only [a,g,interior_coefficient_eq hu hU hy hN hlog hl hh,sub_self,
        zero_div,zero_mul]
    have h := hb N (Finset.range P) a (by omega : 64≤N) (fun n _ => ha n)
      y u (by linarith : 0≤u) hU
    rw [he,sub_zero] at h
    have hs : (u : ℂ)^(N+1)*∑ n∈Finset.range P,g n*zetaPrimeLogKernel N (3/2+Complex.I*y) n=
        5*((u : ℂ)^(N+1)*∑ n∈Finset.range P,a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
      simp only [a,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => by ring)
    rw [hs,norm_mul,show ‖(5 : ℂ)‖=(5 : ℝ) by norm_num]
    exact (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ)≤5)).trans_eq (by ring)
  have hm : HasSum (fun n => maskedSmallCoefficient u y N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)
      (∑ n∈literalSmallLabels u y N,selbergDefect u N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
    have h : HasSum (fun n => maskedSmallCoefficient u y N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)
        (∑ n∈literalSmallLabels u y N,maskedSmallCoefficient u y N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n) :=
      hasSum_sum_of_ne_finset_zero (s:=literalSmallLabels u y N)
      (f:=fun n => maskedSmallCoefficient u y N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)
      (by intro n hn; simp [maskedSmallCoefficient,hn])
    have hs : (∑ n∈literalSmallLabels u y N,maskedSmallCoefficient u y N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)=
        ∑ n∈literalSmallLabels u y N,selbergDefect u N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n :=
      Finset.sum_congr rfl (fun n hn => by simp only [maskedSmallCoefficient,if_pos hn])
    rw [hs] at h
    exact h
  have ht := (((hasSum_smallCoefficient u y (by omega : 0<N)).sub hm).tendsto_sum_nat.const_mul
    ((u : ℂ)^(N+1))).norm
  have h := le_of_tendsto ht (Eventually.of_forall (fun P => by
    simpa only [g,sub_mul] using hbound P))
  simpa only [g,sub_mul,literalSmall,mul_sub] using h

/-- Actual source-normalized signed payment on the original retained
support. Exposure is explicit; every analytic multiplicity is permitted. -/
theorem tendsto_literalSmall (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|rho.1.im|) :
    Tendsto (literalSmall (3/2-rho.1.re) rho.1.im) atTop (𝓝 0) := by
  let u : ℝ := 3/2-rho.1.re
  have hu : 1/2≤u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  obtain ⟨C,_hC,hbound⟩ := exists_literalSmall_completion_bound
  have he : Tendsto (fun N => (u : ℂ)^(N+1)*completedSmall u rho.1.im N-
      literalSmall u rho.1.im N) atTop (𝓝 0) := by
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
      ZetaRieszLargeOrderCore.rate_bounds.1.le ZetaRieszLargeOrderCore.rate_bounds.2).mul_const C
    apply squeeze_zero_norm' ?_ (by simpa only [zero_mul] using ht)
    filter_upwards [eventually_ge_atTop (65536 : ℕ),eventually_small_log] with N hN hlog
    exact hbound u rho.1.im hu hU hy N hN hlog
  have ht := (tendsto_completedSmall rho hrho hexposed hU).sub he
  rw [sub_zero] at ht
  simpa only [u,sub_sub_cancel] using ht

/-- The remainder retains every large-cofactor pair with its sign.
The polynomial-small payment is spent once, not as a floor credit. -/
def largePairRest (u y : ℝ) (N : ℕ) : ℂ :=
  (u : ℂ)^(N+1)*∑ n∈completePeriodLabels (joinedLabels u N) N y\literalSmallLabels u y N,
    selbergDefect u N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n

theorem literalPairDefect_eq (u y : ℝ) (N : ℕ) :
    literalPairDefect u y N=largePairRest u y N+literalSmall u y N := by
  unfold literalPairDefect largePairRest literalSmall
  rw [←mul_add]
  congr 1
  exact (Finset.sum_sdiff (show literalSmallLabels u y N⊆
    completePeriodLabels (joinedLabels u N) N y from Finset.filter_subset _ _)).symm

/-- Conditional source equivalence to the STILL unpaid large-cofactor
aggregate. No bound of `399/5000` for that aggregate is inferred. -/
theorem tendsto_native_plus_largePairRest_simple (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hm : analyticZetaZeroMultiplicity rho=1)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|rho.1.im|) :
    Tendsto (fun j =>
      (((3/2-rho.1.re : ℝ) : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ZetaRieszParityPacket.coreResponse (3/2-rho.1.re) rho.1.im
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszNearCriticalCountPayment.countCeiling j)).re+
      (largePairRest (3/2-rho.1.re) rho.1.im (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)).re)
      atTop (𝓝 0) := by
  have hu : 1/2<3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have h1 := tendsto_native_plus_pairDefect_simple rho hrho hexposed hm hu hU hy
  have h2 := Complex.continuous_re.tendsto (0 : ℂ) |>.comp
    ((tendsto_literalSmall rho hrho hexposed hU hy).comp
      ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder)
  have ht := h1.sub h2
  simp only [Complex.zero_re,sub_zero] at ht
  apply ht.congr'
  filter_upwards [] with j
  simp only [Function.comp_def,literalPairDefect_eq,Complex.add_re]
  ring

/-- The surviving balanced boxes are not affected by the polynomial
cofactor payment. In particular, this result cannot be advertised as a
saving on their required signed `399/5000` upper bound. -/
theorem balancedProducts_disjoint_literalSmall (u y : ℝ) {N : ℕ}
    (hN : 0<N) (hcut : log (N^16 : ℕ)≤(N : ℝ)/10) :
    Disjoint (ZetaRieszGlobalHeadPriceAudit.balancedProducts N) (literalSmallLabels u y N) := by
  apply Finset.disjoint_left.mpr
  intro n hn hsmall
  obtain ⟨⟨a,b⟩,he,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp he
  have haD := ZetaRieszAllowancePrimeBoxes.logPrimes_bounds ha
  have hbD := ZetaRieszAllowancePrimeBoxes.logPrimes_bounds hb
  obtain ⟨_hs,q,hq,p,_hp,_hqp,hprod⟩ := Finset.mem_filter.mp hsmall
  have hqP := (smallPrimes_data hq).1
  have hqd : q∣a*b := hprod ▸ dvd_mul_right q p
  have hqlog : log q≤log (N^16 : ℕ) := log_le_log
    (by exact_mod_cast hqP.pos) (by exact_mod_cast (smallPrimes_data hq).2)
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  rcases hqP.dvd_mul.mp hqd with hd | hd
  · have hqa := (Nat.prime_dvd_prime_iff_eq hqP haD.1).mp hd
    rw [hqa] at hqlog
    nlinarith only [haD.2.1,hqlog,hcut,hNr]
  · have hqb := (Nat.prime_dvd_prime_iff_eq hqP hbD.1).mp hd
    rw [hqb] at hqlog
    nlinarith only [hbD.2.1,hqlog,hcut,hNr]

/-- Spend the real estimate in the original floor ledger. The surviving
balanced-pair term is still signed and still requires its independent
cofinal upper bound; this theorem does not assume that bound. -/
theorem eventually_native_largePairRest_floor {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      -(largePairRest u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)).re-
        ZetaRieszLowCountSignedBoundary.nativeSignedPeriodBudget u y j-
        ‖literalSelberg u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)‖-
        ‖literalSmall u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)‖≤
      ((u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ZetaRieszParityPacket.coreResponse u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  filter_upwards [eventually_native_pairDefect_floor hu hU hy] with j hj
  rw [literalPairDefect_eq,Complex.add_re] at hj
  have hs := Complex.re_le_norm (literalSmall u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
  linarith only [hj,hs]

end RiemannGaussian.ZetaRieszPolynomialPairPayment
end
