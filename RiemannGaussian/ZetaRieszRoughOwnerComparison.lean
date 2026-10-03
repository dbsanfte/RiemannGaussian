/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSmoothOwnerDiscrepancy
import RiemannGaussian.ZetaRieszLongCutoffError
import RiemannGaussian.ZetaRieszCubicSieveCost
import RiemannGaussian.ZetaRieszNearCriticalCountPayment

/-!
# A signed comparison on complete rough owner rows

The original owner allocation and product phase are kept in the smooth
weight. Squarefreeness and ALL forbidden-prime incidences stay in the
counting measure, including at prime cofactors. Counts are not separated.
Only the centered counting error is paid. The signed density main and
ordinary-prime subtraction remain coupled and unpaid.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszRoughOwnerComparison
open ZetaRieszCofactorPhaseEnergy ZetaRieszCofactorDiscrepancy
open ZetaRieszSmoothOwnerDiscrepancy
open ZetaRieszUnsignedDivisorError (sieve)
open ZetaRieszLongCutoffError (roughDensityPrefix)

/-- Exact deletion of unit/prime cofactors in the rough measure. In
particular, the smooth extension does NOT erase its prime subtraction. -/
theorem rough_composite_error_identity {X D : ℕ} (hX : 0 < X) (hD : 0 < D)
    (S : Finset ℕ) (w : ℕ → ℝ) :
    correlation (compositePrefix X) (fun n => w n*sieve S n) D-
      (roughDensityPrefix S D*(∑ n ∈ Finset.Icc 1 X, w n)-w 1*sieve S 1-
        ∑ p ∈ (Finset.Icc 1 X).filter (fun p => p.Prime ∧ D<p), w p*sieve S p) =
      (∑ n ∈ Finset.Icc 1 X, w n*sieve S n*sharp D n)-
        roughDensityPrefix S D*(∑ n ∈ Finset.Icc 1 X, w n) := by
  have h := composite_model hX hD (fun n => w n*sieve S n)
  have hi n : w n*sieve S n*(if Squarefree n then sharp D n else 0) =
      w n*sieve S n*sharp D n := by
    by_cases hs : Squarefree n
    · simp [hs]
    · simp [sieve,hs]
  simp only [hi,compositeModel] at h
  linarith only [h]

/-- No variation of squarefree/rough holes is charged. The variation
belongs only to the test weight, before multiplication by the sieve. -/
theorem rough_composite_error_exponential (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) {X D : ℕ} (hX : 0 < X) (hD : 0 < D)
    (N : ℕ) (w : ℕ → ℝ) (b : ℝ) (hend : w (X+1)=0)
    (hcut : ∀ k ∈ Finset.Icc 1 X, w k ≠ w (k+1) → D^4 ≤ k^3)
    (hlower : ∀ k ∈ Finset.Icc 1 X, w k ≠ w (k+1) → exp (b*N) ≤ k) :
    |correlation (compositePrefix X) (fun n => w n*sieve S n) D-
      (roughDensityPrefix S D*(∑ n ∈ Finset.Icc 1 X, w n)-w 1*sieve S 1-
        ∑ p ∈ (Finset.Icc 1 X).filter (fun p => p.Prime ∧ D<p), w p*sieve S p)| ≤
      ZetaRieszLongCutoffError.countingConstant*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*exp (-(b*N)/64)*
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|w k-w (k+1)|) := by
  rw [rough_composite_error_identity hX hD]
  exact ZetaRieszLongCutoffError.rough_weighted_error_exponential
    S hS X D N w b hend hD hcut hlower

private theorem shell_prime_deletion {M X D : ℕ} (hM : 0 < M) (hDM : D ≤ M)
    (S : Finset ℕ) (a : ℕ → ℝ) (y c : ℝ) :
    shellWeight M X a y c 1*sieve S 1+
      (∑ p ∈ (Finset.Icc 1 X).filter (fun p => p.Prime ∧ D<p),
        shellWeight M X a y c p*sieve S p) =
      ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
        shellWeight M X a y c p*sieve S p := by
  have h1 : shellWeight M X a y c 1=0 := by
    simp [shellWeight,show ¬M<1 by omega]
  rw [h1,zero_mul,zero_add]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.Prime <;> by_cases hDp : D<p
  · simp [hp,hDp]
  · simp [hp,hDp,shellWeight,show ¬M<p by omega]
  · simp [hp]
  · simp [hp]

/-- The WHOLE rough owner correlation is compared with ONE signed main:
the density scalar times the full phase sum MINUS the literal prime head.
The owner selector keeps every factorial order. -/
theorem rough_owner_shell_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {N M X D : ℕ} (hN : 32 ≤ N) (hM : 0 < M) (hMX : M<X) (hXM : X≤2*M)
    (hD : 0 < D) (hDM : D≤M) (hcut : D^4≤M^3)
    (hlarge : exp ((N : ℝ)/2)≤M) {c : ℝ} (hc : 0<c) (y : ℝ) :
    let w := shellWeight M X (ownerAmplitude N c) y c;
    |correlation (compositePrefix X) (fun n => w n*sieve S n) D-
      (roughDensityPrefix S D*(∑ n ∈ Finset.Icc 1 X, w n)-
        ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, w p*sieve S p)| ≤
      ZetaRieszLongCutoffError.countingConstant*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*
          exp (-(N : ℝ)/128)*(6+|y|)*radialCap N := by
  let w := shellWeight M X (ownerAmplitude N c) y c
  have hactive k (_hk : k ∈ Finset.Icc 1 X) (hz : w k≠w (k+1)) : M≤k := by
    by_contra hn
    have hk : k<M := lt_of_not_ge hn
    simp [w,shellWeight,show ¬M<k by omega,show ¬M<k+1 by omega] at hz
  have he := rough_composite_error_exponential S hS (by omega : 0<X) hD N w (1/2)
    (by simp [w,shellWeight])
    (fun k hk hz => hcut.trans (Nat.pow_le_pow_left (hactive k hk hz) 3))
    (fun k hk hz => by
      have hMk : (M : ℝ)≤k := by exact_mod_cast hactive k hk hz
      convert hlarge.trans hMk using 1
      congr 1
      ring)
  have hv := shellWeight_variation hM hMX hXM (ownerAmplitude N c) y c
    (radialCap N) (radialCap_nonneg N)
    (fun n _ => by
      rw [abs_of_nonneg (ownerAmplitude_bounds N hc n).1]
      exact (ownerAmplitude_bounds N hc n).2)
  have ha := ownerAmplitude_variation hN hM hMX hXM hc
  have hv' : (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|w k-w (k+1)|) ≤
      (6+|y|)*radialCap N := hv.trans (by linarith only [ha])
  dsimp only
  have hd := shell_prime_deletion (X := X) hM hDM S (ownerAmplitude N c) y c
  rw [show -((1/2 : ℝ)*N)/64=-(N : ℝ)/128 by ring] at he
  have hh : roughDensityPrefix S D*(∑ n ∈ Finset.Icc 1 X, w n)-w 1*sieve S 1-
      (∑ p ∈ (Finset.Icc 1 X).filter (fun p => p.Prime ∧ D<p), w p*sieve S p) =
      roughDensityPrefix S D*(∑ n ∈ Finset.Icc 1 X, w n)-
        ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, w p*sieve S p := by
    dsimp [w] at hd ⊢
    linarith only [hd]
  rw [hh] at he
  have hh' : ZetaRieszLongCutoffError.countingConstant*
      ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*exp (-(N : ℝ)/128)*
        ((6+|y|)*radialCap N) =
      ZetaRieszLongCutoffError.countingConstant*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*exp (-(N : ℝ)/128)*
          (6+|y|)*radialCap N := by ring
  exact he.trans ((mul_le_mul_of_nonneg_left hv'
    (by positivity [ZetaRieszLongCutoffError.countingConstant_pos,
      ZetaRieszPrimeWeightedSieve.sieveCost_nonneg (3/4) S])).trans_eq hh')

/-- An explicit exponential source saving, uniform throughout the actual
restricted radius interval. This pays ONLY the comparison error. -/
theorem rough_source_rate {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ) :
    (2*u)^N*exp (-(N : ℝ)/128)≤exp (-(7/1000 : ℝ)*N) := by
  have hlog : log (2*ZetaRieszWideOwnerAudit.radiusCeiling)≤1/10000 := by
    have h := log_le_sub_one_of_pos
      (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
        (0 : ℝ)<2*ZetaRieszWideOwnerAudit.radiusCeiling)
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at h ⊢
    exact h
  calc
    _ ≤ (2*ZetaRieszWideOwnerAudit.radiusCeiling)^N*exp (-(N : ℝ)/128) := by gcongr
    _ = exp ((log (2*ZetaRieszWideOwnerAudit.radiusCeiling)-1/128)*(N : ℝ)) := by
      have hp : (2*ZetaRieszWideOwnerAudit.radiusCeiling)^N =
          exp ((N : ℝ)*log (2*ZetaRieszWideOwnerAudit.radiusCeiling)) := by
        rw [exp_nat_mul,exp_log (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
          (0 : ℝ)<2*ZetaRieszWideOwnerAudit.radiusCeiling)]
      rw [hp,← exp_add]
      congr 1
      ring
    _ ≤ _ := exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith only [hlog])
      (Nat.cast_nonneg N))

/-- Source-normalized signed owner comparison with the actual intersection
cost, not three per excluded prime or a termwise carrier norm. -/
theorem normalized_rough_owner_shell_error (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) {N M X D : ℕ} (hN : 32≤N) (hM : 0<M)
    (hMX : M<X) (hXM : X≤2*M) (hD : 0<D) (hDM : D≤M) (hcut : D^4≤M^3)
    (hlarge : exp ((N : ℝ)/2)≤M) {c u : ℝ} (hc : 0<c) (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    let w := shellWeight M X (ownerAmplitude N c) y c;
    |u^(N+1)*(correlation (compositePrefix X) (fun n => w n*sieve S n) D-
      (roughDensityPrefix S D*(∑ n ∈ Finset.Icc 1 X, w n)-
        ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, w p*sieve S p))| ≤
      2*u*ZetaRieszLongCutoffError.countingConstant*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(6+|y|)*((N : ℝ)+1)*
          exp (-(7/1000 : ℝ)*N) := by
  dsimp only
  rw [abs_mul,abs_of_nonneg (pow_nonneg hu _)]
  apply (mul_le_mul_of_nonneg_left
    (rough_owner_shell_error S hS hN hM hMX hXM hD hDM hcut hlarge hc y)
    (pow_nonneg hu _)).trans
  have h := mul_le_mul_of_nonneg_left (rough_source_rate hu hU N)
    (show 0≤2*u*ZetaRieszLongCutoffError.countingConstant*
      ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(6+|y|)*((N : ℝ)+1) by
        positivity [ZetaRieszLongCutoffError.countingConstant_pos,
          ZetaRieszPrimeWeightedSieve.sieveCost_nonneg (3/4) S])
  convert h using 1
  simp only [radialCap,mul_pow,pow_succ]
  ring

private theorem sum_steps (R : ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 R, (f d-f (d+1)))=f 1-f (R+1) := by
  have hi : Finset.Icc 1 R=Finset.Ico 1 (R+1) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_Ico]
    omega
  rw [hi,Finset.sum_Ico_eq_sum_range]
  simpa only [Nat.add_sub_cancel,Nat.add_zero,Nat.zero_add,Nat.add_comm,
    Nat.add_left_comm,Nat.add_assoc] using Finset.sum_range_sub' (fun i => f (i+1)) R

/-- All divisor cutoffs are joined BEFORE comparison. This bounds the
actual signed response, with its density and prime head in the SAME main
term, rather than a positive allowance per prime-count class. -/
theorem normalized_rough_owner_profile_error (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) {N M X R : ℕ} (hN : 32≤N) (hM : 0<M)
    (hMX : M<X) (hXM : X≤2*M) (hRM : R≤M) (hcut : R^4≤M^3)
    (hlarge : exp ((N : ℝ)/2)≤M) {c u : ℝ} (hc : 0<c) (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (f : ℕ → ℝ) (hf : f (R+1)=0) :
    let w := shellWeight M X (ownerAmplitude N c) y c;
    |u^(N+1)*((∑ n ∈ compositePrefix X, w n*sieve S n*
        (∑ d ∈ Finset.Icc 1 R, f d*(if d∣n then (μ d : ℝ) else 0)))-
      ((∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*roughDensityPrefix S D)*
        (∑ n ∈ Finset.Icc 1 X, w n)-
          f 1*(∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, w p*sieve S p)))| ≤
      (2*u*ZetaRieszLongCutoffError.countingConstant*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(6+|y|)*((N : ℝ)+1)*
          exp (-(7/1000 : ℝ)*N))*∑ D ∈ Finset.Icc 1 R, |f D-f (D+1)| := by
  let w := shellWeight M X (ownerAmplitude N c) y c
  have hl : (∑ n ∈ compositePrefix X, w n*sieve S n*
      (∑ d ∈ Finset.Icc 1 R, f d*(if d∣n then (μ d : ℝ) else 0))) =
      ∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*
        correlation (compositePrefix X) (fun n => w n*sieve S n) D := by
    simp_rw [ZetaRieszSignedCutoffEnergy.abel_profile R f _ hf,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro D _
    simp only [correlation,sharp,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hm : ((∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*roughDensityPrefix S D)*
      (∑ n ∈ Finset.Icc 1 X, w n)-
        f 1*(∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, w p*sieve S p)) =
      ∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*
        (roughDensityPrefix S D*(∑ n ∈ Finset.Icc 1 X, w n)-
          ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, w p*sieve S p) := by
    symm
    calc
      _ = (∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*roughDensityPrefix S D)*
          (∑ n ∈ Finset.Icc 1 X, w n)-
          (∑ D ∈ Finset.Icc 1 R, (f D-f (D+1)))*
            (∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, w p*sieve S p) := by
        simp only [mul_sub,← mul_assoc]
        rw [Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.sum_mul]
      _ = _ := by rw [sum_steps,hf,sub_zero]
  dsimp only
  change |u^(N+1)*(_-_ )|≤_
  rw [hl,hm,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ D ∈ Finset.Icc 1 R, |f D-f (D+1)| *
        (2*u*ZetaRieszLongCutoffError.countingConstant*
          ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(6+|y|)*((N : ℝ)+1)*
            exp (-(7/1000 : ℝ)*N)) := by
      apply Finset.sum_le_sum
      intro D hD
      have hd := Finset.mem_Icc.mp hD
      have he := normalized_rough_owner_shell_error S hS hN hM hMX hXM hd.1
        (hd.2.trans hRM) ((Nat.pow_le_pow_left hd.2 4).trans hcut) hlarge hc hu hU y
      have hh := mul_le_mul_of_nonneg_left he (abs_nonneg (f D-f (D+1)))
      convert hh using 1
      rw [← abs_mul]
      congr 1
      ring
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Retain the physical cubic threshold using the ALREADY proved weighted
intersection cost. This is monotonicity in the exponent, not a new sieve. -/
theorem sieveCost_le_cubic (S : Finset ℕ) (N : ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p≤N^3) :
    ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S≤
      ZetaRieszCubicSieveCost.cubicCost N := by
  apply le_trans _ (ZetaRieszCubicSieveCost.intersectionCost_cubic_bound S N hS)
  unfold ZetaRieszPrimeWeightedSieve.sieveCost ZetaRieszCubicSieveCost.intersectionCost
  apply Finset.prod_le_prod
  · intro p _
    linarith [primeSquareCorrectedWeight_nonneg (3/4) p]
  · intro p _
    have he : zetaPrimeExpWeight (3/4) p≤zetaPrimeExpWeight (23/32) p := by
      unfold zetaPrimeExpWeight
      apply exp_le_exp.mpr
      nlinarith [log_natCast_nonneg p]
    have hsq := mul_self_le_mul_self
      (show 0≤zetaPrimeExpWeight (3/4) p by unfold zetaPrimeExpWeight; positivity) he
    unfold primeSquareCorrectedWeight
    linarith only [he,hsq]

/-- The count comparison still pays ALL excluded primes through N³:
their subexponential cost fits inside a fixed geometric source margin. -/
theorem eventually_cubic_counting_rate :
    ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ p≤N^3) →
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*exp (-(7/1000 : ℝ)*N)≤
          exp (-(3/500 : ℝ)*N) := by
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<5/32)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hm := ht.const_mul (64/9 : ℝ)
  simp only [mul_zero] at hm
  filter_upwards [hm.eventually_lt_const (by norm_num : (0 : ℝ)<1/1000),
    eventually_ge_atTop (1 : ℕ)] with N h hN
  simp only [Function.comp_apply] at h
  intro S hS
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have hp : (N : ℝ)^(27/32 : ℝ)=(N : ℝ)^(-(5/32 : ℝ))*(N : ℝ) := by
    calc
      _ = (N : ℝ)^(-(5/32 : ℝ)+1) := by norm_num
      _ = (N : ℝ)^(-(5/32 : ℝ))*(N : ℝ)^1 := rpow_add hn _ _
      _ = _ := by rw [rpow_one]
  have hs : (64/9 : ℝ)*(N : ℝ)^(27/32 : ℝ)≤(N : ℝ)/1000 := by
    rw [hp]
    have hh := mul_le_mul_of_nonneg_right h.le hn.le
    nlinarith only [hh]
  calc
    _ ≤ ZetaRieszCubicSieveCost.cubicCost N*exp (-(7/1000 : ℝ)*N) :=
      mul_le_mul_of_nonneg_right (sieveCost_le_cubic S N hS) (exp_pos _).le
    _ = exp ((64/9 : ℝ)*(N : ℝ)^(27/32 : ℝ)-(7/1000 : ℝ)*N) := by
      rw [ZetaRieszCubicSieveCost.cubicCost,← exp_add]; congr 1; ring
    _ ≤ _ := exp_le_exp.mpr (by linarith only [hs])

private theorem positive_hinge_steps {R : ℕ} {b : ℝ} (hb : 0≤b)
    (hend : b≤log (R+1 : ℕ)) :
    (∑ D ∈ Finset.Icc 1 R,
      |max 0 (b-log D)-max 0 (b-log (D+1 : ℕ))|)=b := by
  have hi D (hD : D ∈ Finset.Icc 1 R) :
      0 ≤ max 0 (b-log D)-max 0 (b-log (D+1 : ℕ)) := by
    have hl := log_le_log
      (show (0 : ℝ)<D by exact_mod_cast (Finset.mem_Icc.mp hD).1)
      (show (D : ℝ)≤(D+1 : ℕ) by exact_mod_cast Nat.le_succ D)
    exact sub_nonneg.mpr (max_le_max_left 0 (by linarith))
  rw [Finset.sum_congr rfl (fun D hD => abs_of_nonneg (hi D hD)),sum_steps,
    max_eq_left (sub_nonpos.mpr hend)]
  simp only [Nat.cast_one,log_one,sub_zero,max_eq_right hb]

/-- The exact Riesz profile is summed over EVERY composite cofactor
count. Its error is geometric; its main is still SIGNED. -/
theorem normalized_rough_owner_riesz_error (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) {N M X R : ℕ} (hN : 32≤N) (hM : 0<M)
    (hMX : M<X) (hXM : X≤2*M) (hRM : R≤M) (hcut : R^4≤M^3)
    (hlarge : exp ((N : ℝ)/2)≤M) {c u b : ℝ} (hc : 0<c) (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hb : 0≤b)
    (hend : b≤log (R+1 : ℕ)) (y : ℝ) :
    let w := shellWeight M X (ownerAmplitude N c) y c;
    let densityMain := (∑ D ∈ Finset.Icc 1 R,
      (max 0 (b-log D)-max 0 (b-log (D+1 : ℕ)))*roughDensityPrefix S D)*
        (∑ n ∈ Finset.Icc 1 X, w n);
    let primeHead := b*(∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, w p*sieve S p);
    |u^(N+1)*((∑ n ∈ compositePrefix X, w n*sieve S n*VaughanLogAverage.riesz b n)-
      (densityMain-primeHead))| ≤
      2*u*ZetaRieszLongCutoffError.countingConstant*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(6+|y|)*((N : ℝ)+1)*b*
          exp (-(7/1000 : ℝ)*N) := by
  let w := shellWeight M X (ownerAmplitude N c) y c
  let f := fun d : ℕ => max 0 (b-log d)
  have hf : f (R+1)=0 := max_eq_left (sub_nonpos.mpr hend)
  have hl : (∑ n ∈ compositePrefix X, w n*sieve S n*VaughanLogAverage.riesz b n) =
      ∑ n ∈ compositePrefix X, w n*sieve S n*
        (∑ d ∈ Finset.Icc 1 R, f d*(if d∣n then (μ d : ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n≠0 := by
      have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
      omega
    rw [ZetaSquarefreeRieszCompletion.riesz_eq_finite_divisor_cutoff b hend hn0]
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d∣n <;> simp [f,hd,mul_comm]
  have h := normalized_rough_owner_profile_error S hS hN hM hMX hXM hRM hcut
    hlarge hc hu hU y f hf
  dsimp only
  change |u^(N+1)*(_-_ )|≤_
  rw [hl]
  have hf1 : f 1=b := by simp [f,max_eq_right hb]
  rw [hf1] at h
  have hv := positive_hinge_steps hb hend
  change (∑ D ∈ Finset.Icc 1 R, |f D-f (D+1)|)=b at hv
  rw [hv] at h
  exact h.trans_eq (by ring)

/-- The rough shell is a LITERAL sum of the existing owner atoms. The
prime owner is unchanged, its original factorial selector is unchanged,
and the ordinary-prime COFACTOR is excluded exactly on both sides. -/
theorem literal_rough_owner_shell_eq (S A : Finset ℕ) (N M X : ℕ) (hM : 0<M)
    {p : ℕ} (hp : p.Prime) (hXp : X<p) (hpA : p∈A)
    {L : ℝ} (hpL : log p≤L) (y : ℝ) :
    (∑ a ∈ (Finset.Ioc M X).filter (fun a =>
      Squarefree a ∧ ¬a.Prime ∧ ¬∃ q ∈ S, q∣a),
      (ZetaRieszJointAllocation.residualCoefficient
        (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L N (p*a)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re) =
      (∑ a ∈ compositePrefix X,
        shellWeight M X (ownerAmplitude N (log p)) y (log p) a*sieve S a*
          VaughanLogAverage.riesz (L-log p) a)/(L*p) := by
  let B := (Finset.Ioc M X).filter (fun a =>
    Squarefree a ∧ ¬a.Prime ∧ ¬∃ q ∈ S, q∣a)
  have hs : B⊆compositePrefix X := by
    intro a ha
    obtain ⟨haI,has,hap,_⟩ := Finset.mem_filter.mp ha
    have hi := Finset.mem_Ioc.mp haI
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega,hi.2⟩,has,hap⟩
  have he : (∑ a ∈ compositePrefix X,
      shellWeight M X (ownerAmplitude N (log p)) y (log p) a*sieve S a*
        VaughanLogAverage.riesz (L-log p) a) =
      ∑ a ∈ B, shellWeight M X (ownerAmplitude N (log p)) y (log p) a*sieve S a*
        VaughanLogAverage.riesz (L-log p) a := by
    symm
    apply Finset.sum_subset hs
    intro a ha hn
    obtain ⟨haI,has,hap⟩ := Finset.mem_filter.mp ha
    have haX := (Finset.mem_Ioc.mp haI).2
    by_cases hlo : M<a
    · have hrough : ¬(¬∃ q ∈ S, q∣a) := by
        intro hr
        exact hn (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hlo,haX⟩,has,hap,hr⟩)
      simp [sieve,hrough]
    · simp [shellWeight,hlo]
  rw [he,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨haI,has,hap,hr⟩ := Finset.mem_filter.mp ha
  have hi := Finset.mem_Ioc.mp haI
  rw [owner_atom_eq A N has (by omega : 1<a) hap hp (hi.2.trans_lt hXp) hpA hpL y]
  simp [shellWeight,hi.1,hi.2,sieve,has,hr]

/-- A direct bound for the ORIGINAL rough owner atoms, not just a sharp
prefix or an artificial prime-density carrier. The signed ordinary-prime
head is retained in the comparison main, not paid by a norm. -/
theorem literal_rough_owner_riesz_error (S A : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime) {N M X R : ℕ} (hN : 32≤N) (hM : 0<M)
    (hMX : M<X) (hXM : X≤2*M) (hRM : R≤M) (hcut : R^4≤M^3)
    (hlarge : exp ((N : ℝ)/2)≤M) {p : ℕ} (hp : p.Prime) (hXp : X<p)
    (hpA : p∈A) {L u : ℝ} (hL : 0<L) (hpL : log p≤L) (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hend : L-log p≤log (R+1 : ℕ)) (y : ℝ) :
    let w := shellWeight M X (ownerAmplitude N (log p)) y (log p);
    let main := (∑ D ∈ Finset.Icc 1 R,
      (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*roughDensityPrefix S D)*
        (∑ a ∈ Finset.Icc 1 X, w a)-
      (L-log p)*(∑ q ∈ (Finset.Icc 1 X).filter Nat.Prime, w q*sieve S q);
    |u^(N+1)*((∑ a ∈ (Finset.Ioc M X).filter (fun a =>
        Squarefree a ∧ ¬a.Prime ∧ ¬∃ q ∈ S, q∣a),
        (ZetaRieszJointAllocation.residualCoefficient
          (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L N (p*a)*
            zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re)-main/(L*p))| ≤
      (2*u*ZetaRieszLongCutoffError.countingConstant*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(6+|y|)*((N : ℝ)+1)*
          (L-log p)*exp (-(7/1000 : ℝ)*N))/(L*p) := by
  have hc : 0<log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hden : 0<L*(p : ℝ) := mul_pos hL (by exact_mod_cast hp.pos)
  have h := normalized_rough_owner_riesz_error S hS hN hM hMX hXM hRM hcut
    hlarge hc hu hU (sub_nonneg.mpr hpL) hend y
  dsimp only
  rw [literal_rough_owner_shell_eq S A N M X hM hp hXp hpA hpL y,← sub_div,
    ← mul_div_assoc,abs_div,abs_of_pos hden]
  exact div_le_div_of_nonneg_right h hden.le

/-- The normalization costs the owner harmonic weight, not its cardinality.
The signed main on the left is unchanged. -/
theorem literal_rough_owner_error_cap (S A : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime) {N M X R : ℕ} (hN : 32≤N) (hM : 0<M)
    (hMX : M<X) (hXM : X≤2*M) (hRM : R≤M) (hcut : R^4≤M^3)
    (hlarge : exp ((N : ℝ)/2)≤M) {p : ℕ} (hp : p.Prime) (hXp : X<p)
    (hpA : p∈A) {L u : ℝ} (hL : 0<L) (hpL : log p≤L) (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hend : L-log p≤log (R+1 : ℕ)) (y : ℝ) :
    let w := shellWeight M X (ownerAmplitude N (log p)) y (log p);
    let main := (∑ D ∈ Finset.Icc 1 R,
      (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*roughDensityPrefix S D)*
        (∑ a ∈ Finset.Icc 1 X, w a)-
      (L-log p)*(∑ q ∈ (Finset.Icc 1 X).filter Nat.Prime, w q*sieve S q);
    |u^(N+1)*((∑ a ∈ (Finset.Ioc M X).filter (fun a =>
        Squarefree a ∧ ¬a.Prime ∧ ¬∃ q ∈ S, q∣a),
        (ZetaRieszJointAllocation.residualCoefficient
          (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L N (p*a)*
            zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re)-main/(L*p))| ≤
      (2*u*ZetaRieszLongCutoffError.countingConstant*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(6+|y|)*((N : ℝ)+1)*
          exp (-(7/1000 : ℝ)*N))*(p : ℝ)⁻¹ := by
  have h := literal_rough_owner_riesz_error S A hS hN hM hMX hXM hRM hcut hlarge
    hp hXp hpA hL hpL hu hU hend y
  have hp0 : (0 : ℝ)<p := by exact_mod_cast hp.pos
  have hr : (L-log p)/L≤1 := (div_le_one hL).mpr (by linarith [log_natCast_nonneg p])
  have hn : 0≤(2*u*ZetaRieszLongCutoffError.countingConstant*
      ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(6+|y|)*((N : ℝ)+1)*
        exp (-(7/1000 : ℝ)*N))*(p : ℝ)⁻¹ := by
    positivity [ZetaRieszLongCutoffError.countingConstant_pos,
      ZetaRieszPrimeWeightedSieve.sieveCost_nonneg (3/4) S]
  apply h.trans
  have he := mul_le_mul_of_nonneg_left hr hn
  convert he using 1 <;> ring

/-- Aggregate ALL selected owners and ALL cofactor counts first. Norms
are taken only of comparison errors. No count-dependent capacity or
positive prime-cofactor allowance enters the main. -/
theorem joint_rough_owner_error (S A P : Finset ℕ) (hS : ∀ q ∈ S, q.Prime)
    (M X R : ℕ → ℕ) {N : ℕ} (hN : 32≤N) {L u : ℝ} (hL : 0<L)
    (hu : 0≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (hP : ∀ p ∈ P, p.Prime ∧ p∈A ∧ log p≤L)
    (hshell : ∀ p ∈ P, 0<M p ∧ M p<X p ∧ X p≤2*M p ∧ X p<p)
    (hcut : ∀ p ∈ P, R p≤M p ∧ (R p)^4≤(M p)^3 ∧
      exp ((N : ℝ)/2)≤M p ∧ L-log p≤log (R p+1 : ℕ)) :
    let w := fun p => shellWeight (M p) (X p) (ownerAmplitude N (log p)) y (log p);
    |u^(N+1)*((∑ p ∈ P,
      ∑ a ∈ (Finset.Ioc (M p) (X p)).filter (fun a =>
        Squarefree a ∧ ¬a.Prime ∧ ¬∃ q ∈ S, q∣a),
        (ZetaRieszJointAllocation.residualCoefficient
          (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L N (p*a)*
            zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re)-
      ∑ p ∈ P, ((∑ D ∈ Finset.Icc 1 (R p),
        (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*roughDensityPrefix S D)*
          (∑ a ∈ Finset.Icc 1 (X p), w p a)-
        (L-log p)*(∑ q ∈ (Finset.Icc 1 (X p)).filter Nat.Prime, w p q*sieve S q))/(L*p))| ≤
      (2*u*ZetaRieszLongCutoffError.countingConstant*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(6+|y|)*((N : ℝ)+1)*
          exp (-(7/1000 : ℝ)*N))*∑ p ∈ P, (p : ℝ)⁻¹ := by
  dsimp only
  rw [← Finset.sum_sub_distrib,Finset.mul_sum,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hpP,hpA,hpL⟩ := hP p hp
  obtain ⟨hM,hMX,hXM,hXp⟩ := hshell p hp
  obtain ⟨hRM,hcutp,hlarge,hend⟩ := hcut p hp
  exact literal_rough_owner_error_cap S A hS hN hM hMX hXM hRM hcutp hlarge
    hpP hXp hpA hL hpL hu hU hend y

/-- The joined comparison error is genuinely source-small after excluding
EVERY prime through the physical N³ threshold, even with an exponential
owner endpoint. The main still needs an independent signed bound. -/
theorem eventually_joint_rough_owner_error :
    ∀ᶠ N : ℕ in atTop, ∀ (S A P : Finset ℕ) (M X R : ℕ → ℕ) (Q : ℕ)
      (L u y : ℝ), 0<L → 0≤u → u≤ZetaRieszWideOwnerAudit.radiusCeiling →
      (∀ q ∈ S, q.Prime ∧ q≤N^3) →
      (∀ p ∈ P, p.Prime ∧ p∈A ∧ log p≤L ∧ p≤Q) →
      log Q≤(203/100 : ℝ)*N →
      (∀ p ∈ P, 0<M p ∧ M p<X p ∧ X p≤2*M p ∧ X p<p) →
      (∀ p ∈ P, R p≤M p ∧ (R p)^4≤(M p)^3 ∧
        exp ((N : ℝ)/2)≤M p ∧ L-log p≤log (R p+1 : ℕ)) →
      let w := fun p => shellWeight (M p) (X p) (ownerAmplitude N (log p)) y (log p);
      |u^(N+1)*((∑ p ∈ P,
        ∑ a ∈ (Finset.Ioc (M p) (X p)).filter (fun a =>
          Squarefree a ∧ ¬a.Prime ∧ ¬∃ q ∈ S, q∣a),
          (ZetaRieszJointAllocation.residualCoefficient
            (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L N (p*a)*
              zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re)-
        ∑ p ∈ P, ((∑ D ∈ Finset.Icc 1 (R p),
          (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*roughDensityPrefix S D)*
            (∑ a ∈ Finset.Icc 1 (X p), w p a)-
          (L-log p)*(∑ q ∈ (Finset.Icc 1 (X p)).filter Nat.Prime, w p q*sieve S q))/(L*p))| ≤
        (2*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*((N : ℝ)+1)*
          (1+(203/100 : ℝ)*N))*exp (-(3/500 : ℝ)*N) := by
  filter_upwards [eventually_cubic_counting_rate,eventually_ge_atTop (32 : ℕ)]
    with N hrate hN S A P M X R Q L u y hL hu hU hS hP hQ hshell hcut
  have hc := hrate S hS
  have hh : (∑ p ∈ P, (p : ℝ)⁻¹)≤1+(203/100 : ℝ)*N :=
    (marked_harmonic_bound P (fun p hp =>
      ⟨(hP p hp).1,(hP p hp).2.2.2⟩)).trans
        (by simpa only [add_comm] using add_le_add_left hQ 1)
  have he := joint_rough_owner_error S A P (fun p hp => (hS p hp).1)
    M X R hN hL hu hU y (fun p hp => ⟨(hP p hp).1,(hP p hp).2.1,(hP p hp).2.2.1⟩)
    hshell hcut
  apply he.trans
  have hnon : 0≤2*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*((N : ℝ)+1) :=
    by positivity [ZetaRieszLongCutoffError.countingConstant_pos]
  calc
    _ = (2*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*((N : ℝ)+1))*
        (ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*exp (-(7/1000 : ℝ)*N))*
          (∑ p ∈ P, (p : ℝ)⁻¹) := by ring
    _ ≤ (2*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*((N : ℝ)+1))*
        exp (-(3/500 : ℝ)*N)*(1+(203/100 : ℝ)*N) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hc hnon) hh
        (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
    _ = _ := by ring

private theorem owned_product_squarefree {p a : ℕ} (hp : p.Prime)
    (ha : Squarefree a) (hap : a<p) : Squarefree (p*a) := by
  apply Nat.squarefree_mul_iff.mpr
  refine ⟨hp.coprime_iff_not_dvd.mpr ?_,hp.squarefree,ha⟩
  intro hd
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero ha.ne_zero) hd).not_gt hap

/-- Original unique-owner incidences cannot spend the count payment twice.
All physical/phase/allocation masks may remain in the finite row set. -/
theorem owned_rows_injective (E : Finset (ℕ×ℕ))
    (hE : ∀ pa ∈ E, pa.1.Prime ∧ Squarefree pa.2 ∧ pa.2<pa.1) :
    Set.InjOn (fun pa : ℕ×ℕ => pa.1*pa.2) (E : Set (ℕ×ℕ)) := by
  intro pa hpa pb hpb he
  change pa.1*pa.2=pb.1*pb.2 at he
  obtain ⟨hp,ha,hap⟩ := hE pa hpa
  obtain ⟨hq,hb,hbq⟩ := hE pb hpb
  have hmaxa : ZetaRieszPrimeEndpoint.largestPrime (pa.1*pa.2)=pa.1 :=
    ZetaRieszPrimeIntervals.largestPrime_mul pa.1 pa.2 hp ha.ne_zero
      (fun r hr => (Nat.le_of_dvd (Nat.pos_of_ne_zero ha.ne_zero)
        (Nat.dvd_of_mem_primeFactors hr)).trans_lt hap)
  have hmaxb : ZetaRieszPrimeEndpoint.largestPrime (pb.1*pb.2)=pb.1 :=
    ZetaRieszPrimeIntervals.largestPrime_mul pb.1 pb.2 hq hb.ne_zero
      (fun r hr => (Nat.le_of_dvd (Nat.pos_of_ne_zero hb.ne_zero)
        (Nat.dvd_of_mem_primeFactors hr)).trans_lt hbq)
  have hpq : pa.1=pb.1 := by rw [← hmaxa,he,hmaxb]
  have hab : pa.2=pb.2 := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    simpa only [← hpq] using he
  exact Prod.ext hpq hab

/-- The all-count rough comparison can retain the ACTUAL native count
crop. Its deleted boundary is paid by the existing independent count
theorem, after unique-owner incidences have been proved injective.
No prime-count mask has been silently replaced by the completed one. -/
theorem eventually_owned_count_boundary :
    ∀ᶠ j : ℕ in atTop, ∀ (E : Finset (ℕ×ℕ)) (A : Finset ℕ) (L u y : ℝ),
      0<L → 0≤u → u≤ZetaRieszWideOwnerAudit.radiusCeiling →
      (∀ pa ∈ E, pa.1.Prime ∧ Squarefree pa.2 ∧ pa.2<pa.1) →
      (∀ pa ∈ E, log (pa.1*pa.2 : ℕ)≤(203/100 : ℝ)*
        ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) →
      ‖(u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ∑ pa ∈ E.filter (fun pa => ZetaRieszNearCriticalCountPayment.countCeiling j≤
          (pa.1*pa.2).primeFactors.card),
          ZetaRieszJointAllocation.residualCoefficient
            (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (pa.1*pa.2)}) L
              (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (pa.1*pa.2)*
            zetaPrimeLogKernel (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
              (3/2+Complex.I*y) (pa.1*pa.2)‖ ≤
        ZetaRieszNearCriticalCountPayment.allowance j := by
  filter_upwards [ZetaRieszNearCriticalCountPayment.eventually_nearCritical_count_sum_bound]
    with j hj E A L u y hL hu hU hE hlog
  let H := E.filter (fun pa => ZetaRieszNearCriticalCountPayment.countCeiling j≤
    (pa.1*pa.2).primeFactors.card)
  let S := H.image (fun pa => pa.1*pa.2)
  let a := fun n => ZetaRieszJointAllocation.residualCoefficient
    (A ∩ {ZetaRieszPrimeEndpoint.largestPrime n}) L
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) n
  have h := hj S a y u hu hU
    (fun n _ => (ZetaRieszJointAllocation.norm_residualCoefficient_le _ hL _ n).trans
      (by linarith [zetaMoebiusLogMajorant_nonneg n]))
    (by
      intro n hn
      obtain ⟨pa,hpa,rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨hp,ha,hap⟩ := hE pa (Finset.mem_filter.mp hpa).1
      exact owned_product_squarefree hp ha hap)
    (by
      intro n hn
      obtain ⟨pa,hpa,rfl⟩ := Finset.mem_image.mp hn
      exact hlog pa (Finset.mem_filter.mp hpa).1)
    (by
      intro n hn
      obtain ⟨pa,hpa,rfl⟩ := Finset.mem_image.mp hn
      have hc := (Finset.mem_filter.mp hpa).2
      have hh := (ZetaRieszNearCriticalCountPayment.countCeiling_bounds j).1
      omega)
  have hinj := owned_rows_injective E hE
  dsimp [S] at h
  rw [Finset.sum_image (by
    intro pa hpa pb hpb he
    exact hinj (Finset.mem_filter.mp hpa).1 (Finset.mem_filter.mp hpb).1 he)] at h
  exact h

/-- The global rough-row comparison price, including the complete owner
harmonic cost, tends to zero at source scale. Its initial threshold is
existential, not an experimentally sampled native order. -/
theorem comparison_budget_tendsto (u y : ℝ) :
    Tendsto (fun N : ℕ =>
      (2*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*((N : ℝ)+1)*
        (1+(203/100 : ℝ)*N))*exp (-(3/500 : ℝ)*N)) atTop (𝓝 0) := by
  have h0 : 0<exp (-3/500 : ℝ) := exp_pos _
  have h1 : exp (-3/500 : ℝ)<1 := exp_lt_one_iff.mpr (by norm_num)
  have hs := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1 h0 h1
  have hq := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 2 h0 h1
  have h := (hq.const_mul
    (2*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*(203/100))).add
      (hs.const_mul (2*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*(1-203/100)))
  simp only [mul_zero,add_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [← exp_nat_mul]
  ring

end RiemannGaussian.ZetaRieszRoughOwnerComparison
