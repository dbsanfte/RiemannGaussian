/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRoughCutoffRows

/-!
# Independent payment of the literal lower radial boundary

The original factorial kernel has a strict geometric margin throughout
`log n <= 197 N / 100` at the current radius ceiling. This estimate is used
only on the discarded lower boundary, never on the central signed main.
Every original mask, allocation and complex phase remains inside the sum.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszLowerRadialPayment
open ZetaRieszSignedConvolution ZetaRieszParityPacket ZetaRieszPrimeEndpoint
open ZetaRieszJointAllocation ZetaRieszPrimeCountFrequency

/-- A genuinely summable reference abscissa for this boundary only. -/
def referenceExponent : ℝ := 1+1/1048576

/-- Explicit geometric saving for the entire retained lower strip. -/
def lowerRate : ℝ := exp (-(1/100000 : ℝ))

theorem lowerRate_bounds : 0 < lowerRate ∧ lowerRate < 1 := by
  exact ⟨exp_pos _,exp_lt_one_iff.mpr (by norm_num [lowerRate])⟩

/-- A rational power certificate, avoiding a floating logarithm or
exponential evaluation. -/
theorem lower_log_certificate :
    log (ZetaRieszWideOwnerAudit.radiusCeiling*(197/100)) ≤ -(18765/1250000 : ℝ) := by
  have hq : (0 : ℝ)<99984988/100000000 := by norm_num
  have hp : ZetaRieszWideOwnerAudit.radiusCeiling*(197/100) ≤
      (99984988/100000000 : ℝ)^100 := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
  have hh := log_le_log
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
      (0 : ℝ)<ZetaRieszWideOwnerAudit.radiusCeiling*(197/100)) hp
  rw [log_pow] at hh
  have hl := log_le_sub_one_of_pos hq
  nlinarith

/-- The normalized Chernoff rate beats a fixed exponential, uniformly
in the entire radius interval. This is a theorem about exact constants. -/
theorem normalized_lower_rate {u : ℝ} (_hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    u*zetaLogMomentRate (3/2-referenceExponent) (197/100) ≤ lowerRate := by
  have hlog : log (ZetaRieszWideOwnerAudit.radiusCeiling*(197/100))+
      (1-(3/2-referenceExponent)*(197/100)) ≤ -(1/100000 : ℝ) := by
    have h := lower_log_certificate
    norm_num [referenceExponent] at *
    linarith
  have he := exp_le_exp.mpr hlog
  rw [exp_add,exp_log (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
    (0 : ℝ)<ZetaRieszWideOwnerAudit.radiusCeiling*(197/100))] at he
  calc
    _ ≤ ZetaRieszWideOwnerAudit.radiusCeiling*
        zetaLogMomentRate (3/2-referenceExponent) (197/100) :=
      mul_le_mul_of_nonneg_right hU (by unfold zetaLogMomentRate; positivity)
    _ ≤ _ := by simpa only [zetaLogMomentRate,lowerRate,mul_assoc] using he

/-- Any dominated literal arithmetic selection in the lower radial
boundary is independently paid. Heights and masks are arbitrary; no
zero or cancellation hypothesis is used. -/
theorem norm_lower_sum_bound (S : Finset ℕ) (c : ℕ → ℂ) {H u : ℝ}
    (hH : 0 ≤ H) (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (N : ℕ) (y : ℝ)
    (hc : ∀ n ∈ S, ‖c n‖ ≤ H*zetaMoebiusLogMajorant n)
    (hS : ∀ n ∈ S, log n ≤ (197/100 : ℝ)*N) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ S, c n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      H*ZetaRieszWideOwnerAudit.radiusCeiling*
        zetaMoebiusLogMajorantMass referenceExponent*lowerRate^N := by
  have hker n (hn : n ∈ S) := norm_zetaPrimeLogKernel_le_lower_chernoff
    N 0 n (3/2+Complex.I*y) (τ := referenceExponent) (by norm_num : (0 : ℝ)<197/100)
    (by norm_num [referenceExponent] :
      ((3/2+Complex.I*(y : ℂ)).re-referenceExponent)*(197/100) ≤ 1) (hS n hn)
  have hs := summable_zetaMoebiusLogMajorant
    (by norm_num [referenceExponent] : (1 : ℝ)<referenceExponent)
  have hmass : (∑ n ∈ S, zetaMoebiusLogMajorant n*zetaPrimeExpWeight referenceExponent n) ≤
      zetaMoebiusLogMajorantMass referenceExponent := by
    exact hs.sum_le_tsum S (fun n _ =>
      mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (exp_pos _).le)
  have hsum : ‖∑ n ∈ S, c n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      H*(zetaLogMomentRate (3/2-referenceExponent) (197/100))^N*
        zetaMoebiusLogMajorantMass referenceExponent := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ n ∈ S, H*zetaMoebiusLogMajorant n*
          ((zetaLogMomentRate (3/2-referenceExponent) (197/100))^N*
            zetaPrimeExpWeight referenceExponent n) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul]
        exact mul_le_mul (hc n hn) (by simpa using hker n hn)
          (norm_nonneg _) (mul_nonneg hH (zetaMoebiusLogMajorant_nonneg n))
      _ = H*(zetaLogMomentRate (3/2-referenceExponent) (197/100))^N*
          ∑ n ∈ S, zetaMoebiusLogMajorant n*zetaPrimeExpWeight referenceExponent n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by
        unfold zetaLogMomentRate
        positivity)
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu]
  apply (mul_le_mul_of_nonneg_left hsum (pow_nonneg hu _)).trans
  have hr := pow_le_pow_left₀ (by unfold zetaLogMomentRate; positivity :
    0 ≤ u*zetaLogMomentRate (3/2-referenceExponent) (197/100))
    (normalized_lower_rate hu hU) N
  have hm := mul_le_mul hU hr (pow_nonneg (by unfold zetaLogMomentRate; positivity) N)
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
      0 ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
  have hf := mul_le_mul_of_nonneg_left hm
    (mul_nonneg hH (zetaMoebiusLogMajorantMass_nonneg referenceExponent))
  convert hf using 1
  · rw [pow_succ,mul_pow]
    ring
  · ring

/-- The same bound pays ANY literal suballocation of owner-divisor
incidences in the lower strip. This is not a completion of those incidences. -/
theorem norm_lower_partial_sum_bound (S : Finset ℕ)
    (A : ℕ → Finset ℕ) (D : ℕ → Finset (ℕ×ℕ)) (p a : ℕ → ℕ)
    {L u : ℝ} (hL : 0 < L) (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ) (y : ℝ)
    (hp : ∀ n ∈ S, 0 < p n) (ha : ∀ n ∈ S, 0 < a n)
    (he : ∀ n ∈ S, p n*a n=n)
    (hD : ∀ n ∈ S, D n ⊆ (a n).divisorsAntidiagonal)
    (hT : ∀ n ∈ S, log n ≤ 2*L)
    (hS : ∀ n ∈ S, log n ≤ (197/100 : ℝ)*N) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ S,
      ZetaRieszUnsignedDivisorError.partialCoefficient (A n) L N (p n) (a n) (D n)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      2*ZetaRieszWideOwnerAudit.radiusCeiling*
        zetaMoebiusLogMajorantMass referenceExponent*lowerRate^N := by
  apply norm_lower_sum_bound S _ (by norm_num : (0 : ℝ)≤2) hu hU N y _ hS
  intro n hn
  have h := ZetaRieszUnsignedDivisorError.partialCoefficient_bound
    (A n) N (hp n hn) (ha n hn) (D n) (hD n hn) hL
    (by simpa only [he n hn] using hT n hn)
  simpa only [he n hn] using h

/-- Universal boundary budget for the full literal owner coefficient. -/
def lowerBudget (N : ℕ) : ℝ :=
  ZetaRieszWideOwnerAudit.radiusCeiling*
    zetaMoebiusLogMajorantMass referenceExponent*lowerRate^N

theorem tendsto_lowerBudget : Tendsto lowerBudget atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one lowerRate_bounds.1.le
    lowerRate_bounds.2).const_mul
      (ZetaRieszWideOwnerAudit.radiusCeiling*zetaMoebiusLogMajorantMass referenceExponent)
  simp only [mul_zero] at h
  convert h using 1
  ext N
  rfl

/-- The original lower boundary, with every original count/radial,
physical-prime, allocation and phase mask retained. -/
def lowerPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ (coreBand u N K).filter (fun n : ℕ => log n ≤ (197/100 : ℝ)*N),
    residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- The SAME original owner sum after the independently paid lower
strip is removed. No factorial order or cofactor count is changed. -/
def centralConvolution (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ (coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N < log n),
    residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n

theorem norm_lowerPacket_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (N K : ℕ) (y : ℝ) :
    ‖(u : ℂ)^(N+1)*lowerPacket u y N K‖ ≤ lowerBudget N := by
  apply (norm_lower_sum_bound _ _ (by norm_num : (0 : ℝ)≤1) hu hU N y ?_ ?_).trans_eq
    (by simp only [one_mul]; rfl)
  · intro n _
    simpa only [one_mul] using norm_residualCoefficient_le _
      (SquarefreeVaughanLogSource.length_pos u N) N n
  · intro n hn
    exact (Finset.mem_filter.mp hn).2

/-- Exact whole-label split; the selected lower boundary is not
estimated prime-count by prime-count. -/
theorem coreConvolution_eq_lower_add_central (u y : ℝ) (N K : ℕ) :
    coreConvolution u y N K=lowerPacket u y N K+centralConvolution u y N K := by
  rw [coreConvolution_eq_owner]
  symm
  simpa only [lowerPacket,centralConvolution,not_le] using
    Finset.sum_filter_add_sum_filter_not (coreBand u N K)
      (fun n : ℕ => log n ≤ (197/100 : ℝ)*N)
      (fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n)

theorem tendsto_lowerPacket (K : ℕ → ℕ) (y : ℕ → ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => (u : ℂ)^(N+1)*lowerPacket u (y N) N (K N)) atTop (𝓝 0) :=
  squeeze_zero_norm (fun N => norm_lowerPacket_bound hu hU N (K N) (y N)) tendsto_lowerBudget

/-- Every surviving physical label has the strictly narrowed radial
support. This is a support theorem, not the remaining numerical floor. -/
theorem central_log_bounds {u : ℝ} {N K n : ℕ}
    (hn : n ∈ (coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N < log n)) :
    (197/100 : ℝ)*N < log n ∧ log n ≤ (203/100 : ℝ)*N := by
  exact ⟨(Finset.mem_filter.mp hn).2,
    (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.2⟩

/-- The unsigned leg of a short-cutoff row in the remaining radial
window has a forty-one-times larger logarithmic gap than the former
rounded-row certificate. All product and endpoint hypotheses are explicit. -/
theorem central_unsigned_gap {N p b d : ℕ}
    (hp : 0 < p) (hb : 0 < b) (hd : 0 < d)
    (hcore : (197/100 : ℝ)*N < log (p*(b*d) : ℕ))
    (hshort : log (p*b : ℕ) ≤ (3899/2000 : ℝ)*N) :
    (41/2000 : ℝ)*N < log d := by
  have he : log (p*(b*d) : ℕ)=log (p*b : ℕ)+log d := by
    rw [← mul_assoc,Nat.cast_mul,log_mul
      (by exact_mod_cast (Nat.mul_pos hp hb).ne') (by exact_mod_cast hd.ne')]
  rw [he] at hcore
  linarith

/-- The narrowed radial main, with the existing independent payments
retained exactly once. Their original lower-boundary pieces remain explicit
in this algebraic ledger; no disjoint-credit assertion is made for them. -/
def centralRemaining (u y : ℝ) (j : ℕ) : ℝ :=
  ZetaRieszRoughCutoffRows.roughCutoffRemaining u y j-
    (lowerPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re

/-- Exact connection to the existing ledger. It neither resets an old
payment nor takes a positive part of any retained signed term. -/
theorem centralRemaining_eq (u y : ℝ) (j : ℕ) :
    centralRemaining u y j=
      (centralConvolution u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
      (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y
        (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
      (ZetaRieszOwnerGapRows.ownerGapLiteralRows u y j+
        ZetaRieszOwnerGapRows.ownerGapEndpointRows u y j)-
      ZetaRieszRoughCutoffRows.literalCutoffPacket u y j := by
  unfold centralRemaining ZetaRieszRoughCutoffRows.roughCutoffRemaining
    ZetaRieszOwnerGapRows.ownerGapRemaining
  rw [coreConvolution_eq_lower_add_central,Complex.add_re]
  ring

/-- No existing comparison cost is duplicated by the radial payment. -/
def centralErrorBudget (y : ℝ) (N : ℕ) : ℝ :=
  ZetaRieszRoughCutoffRows.roughCutoffErrorBudget y N+lowerBudget N

theorem tendsto_centralErrorBudget (y : ℝ) :
    Tendsto (centralErrorBudget y) atTop (𝓝 0) := by
  have h := (ZetaRieszRoughCutoffRows.tendsto_roughCutoffErrorBudget y).add tendsto_lowerBudget
  simp only [add_zero] at h
  convert h using 1
  ext N
  rfl

/-- The entire lower radial population is paid directly in the current
joined-floor ledger. The numerical floor for the central rest is OPEN. -/
theorem eventually_abs_joined_sub_centralRemaining_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop,
      |u^(dyadicMomentOrder j+1)*
        ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
          centralRemaining u y j)| ≤ centralErrorBudget y (dyadicMomentOrder j) := by
  filter_upwards [ZetaRieszRoughCutoffRows.eventually_abs_joined_sub_roughCutoffRemaining_bound
    hu hU hy] with j hj
  have ht := (Complex.abs_re_le_norm ((u : ℂ)^(dyadicMomentOrder j+1)*
    lowerPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j))).trans
      (norm_lowerPacket_bound (by linarith : 0 ≤ u) hU _ _ y)
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at ht
  unfold centralRemaining
  rw [show u^(dyadicMomentOrder j+1)*
      ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
        (ZetaRieszRoughCutoffRows.roughCutoffRemaining u y j-
          (lowerPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re)) =
      u^(dyadicMomentOrder j+1)*
        ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
          ZetaRieszRoughCutoffRows.roughCutoffRemaining u y j)+
      u^(dyadicMomentOrder j+1)*(lowerPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re by ring]
  exact (abs_add_le _ _).trans (add_le_add hj ht)

theorem tendsto_joined_re_sub_centralRemaining {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*
      ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
        centralRemaining u y j)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun j => centralErrorBudget y (dyadicMomentOrder j)) ?_
    ((tendsto_centralErrorBudget y).comp tendsto_dyadicMomentOrder)
  simpa only [Real.norm_eq_abs] using
    eventually_abs_joined_sub_centralRemaining_bound hu hU hy

/-- The sufficient signed floor is still required for the actual central
rest; the new payment makes no assertion about that open inequality. -/
theorem eventually_joined_floor_with_centralRemaining {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop,
      u^(dyadicMomentOrder j+1)*centralRemaining u y j-
        centralErrorBudget y (dyadicMomentOrder j) ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_abs_joined_sub_centralRemaining_bound hu hU hy] with j hj
  have h := (abs_le.mp hj).1
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  nlinarith

end RiemannGaussian.ZetaRieszLowerRadialPayment
