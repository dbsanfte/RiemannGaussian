/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeWeightedSieve

/-!
# Retain the factor-sensitive sieve cost at the cubic prime threshold

The literal rough squarefree counting theorem already keeps the product of
the actual prime corrections. Replacing this product by three per forbidden
prime unnecessarily limits the least-prime crossing payment. Here the same
sieve, phase, owner allocation and radial weights are retained. Only the
counting error is enlarged by a sublinear exponential at cutoff `N^3`.
The independent numerical floor for the entire carrier is not asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszCubicSieveCost
open ZetaRieszUnsignedDivisorError ZetaRieszSignedConvolution
open ZetaRieszSaturatedRowFloor ZetaRieszFreeRadialRows ZetaRieszFineDivisorRows
open ZetaRieszRoughCutoffRows (secondPrime smallPrimes forbidden forbidden_primes
)
open ZetaRieszEdgeDivisorRows (edgeErrorConstant edgeErrorConstant_nonneg)

/-- The actual finite intersection cost at exponent 23/32. -/
def intersectionCost (S : Finset ℕ) : ℝ :=
  ∏ p ∈ S, (1+primeSquareCorrectedWeight (23/32) p)

theorem intersectionCost_nonneg (S : Finset ℕ) : 0 ≤ intersectionCost S := by
  unfold intersectionCost
  exact Finset.prod_nonneg (fun p _ => by
    linarith [primeSquareCorrectedWeight_nonneg (23/32) p])

theorem intersectionCost_le_three (S : Finset ℕ) :
    intersectionCost S ≤ (3 : ℝ)^S.card := by
  have hw p : zetaPrimeExpWeight (23/32) p ≤ 1 := by
    rw [zetaPrimeExpWeight,exp_le_one_iff]
    nlinarith [log_natCast_nonneg p]
  calc
    _ ≤ ∏ _p ∈ S, (3 : ℝ) := by
      apply Finset.prod_le_prod
      · intro p _
        linarith [primeSquareCorrectedWeight_nonneg (23/32) p]
      · intro p _
        have hn : 0 ≤ zetaPrimeExpWeight (23/32) p := by
          unfold zetaPrimeExpWeight; positivity
        unfold primeSquareCorrectedWeight
        nlinarith [hw p,mul_le_mul_of_nonneg_left (hw p) hn]
    _ = _ := by simp

/-- No prime density estimate is used in this cutoff cost. -/
theorem intersectionCost_cutoff_bound (S : Finset ℕ) (Q : ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ Q) :
    intersectionCost S ≤ exp ((64/9 : ℝ)*(Q : ℝ)^(9/32 : ℝ)) := by
  have hsum : (∑ p ∈ S, primeSquareCorrectedWeight (23/32) p) ≤
      (64/9 : ℝ)*(Q : ℝ)^(9/32 : ℝ) := by
    have hterm p (hp : p ∈ S) : primeSquareCorrectedWeight (23/32) p ≤
        2*(p : ℝ)^(-(23/32 : ℝ)) := by
      have hp0 : (0 : ℝ)<p := by exact_mod_cast (hS p hp).1.pos
      have hw : zetaPrimeExpWeight (23/32) p ≤ 1 := by
        rw [zetaPrimeExpWeight,exp_le_one_iff]
        nlinarith [log_natCast_nonneg p]
      rw [rpow_def_of_pos hp0]
      unfold primeSquareCorrectedWeight zetaPrimeExpWeight at *
      rw [mul_comm (log (p : ℝ)) (-(23/32 : ℝ))]
      have hm := mul_le_mul_of_nonneg_left hw (exp_pos (-(23/32 : ℝ)*log p)).le
      nlinarith only [hm]
    calc
      _ ≤ ∑ p ∈ S, 2*(p : ℝ)^(-(23/32 : ℝ)) := Finset.sum_le_sum hterm
      _ ≤ ∑ p ∈ Finset.Icc 1 Q, 2*(p : ℝ)^(-(23/32 : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun p hp => Finset.mem_Icc.mpr ⟨(hS p hp).1.pos,(hS p hp).2⟩)
          (by intros; positivity)
      _ = 2*∑ p ∈ Finset.Icc 1 Q, (p : ℝ)^((9/32 : ℝ)-1) := by
        rw [Finset.mul_sum]
        norm_num
      _ ≤ 2*((Q : ℝ)^(9/32 : ℝ)/(9/32 : ℝ)) :=
        mul_le_mul_of_nonneg_left (ZetaRieszGeneralCofactorTilt.sum_rpow_concave_le
          (by norm_num : (0 : ℝ)<9/32) (by norm_num) Q) (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ ∏ p ∈ S, exp (primeSquareCorrectedWeight (23/32) p) := by
      apply Finset.prod_le_prod
      · intro p _
        linarith [primeSquareCorrectedWeight_nonneg (23/32) p]
      · intro p _
        simpa only [add_comm] using add_one_le_exp (primeSquareCorrectedWeight (23/32) p)
    _ = exp (∑ p ∈ S, primeSquareCorrectedWeight (23/32) p) := (exp_sum _ _).symm
    _ ≤ _ := exp_le_exp.mpr hsum

/-- All forbidden primes up to `N^3` cost a sublinear exponential. -/
def cubicCost (N : ℕ) : ℝ := exp ((64/9 : ℝ)*(N : ℝ)^(27/32 : ℝ))

theorem cubicCost_pos (N : ℕ) : 0 < cubicCost N := exp_pos _

theorem intersectionCost_cubic_bound (S : Finset ℕ) (N : ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N^3) :
    intersectionCost S ≤ cubicCost N := by
  have hb := intersectionCost_cutoff_bound S (N^3) hS
  have he : ((N^3 : ℕ) : ℝ)^(9/32 : ℝ)=(N : ℝ)^(27/32 : ℝ) := by
    rw [Nat.cast_pow,← rpow_natCast_mul (Nat.cast_nonneg N)]
    norm_num
  simpa only [he,cubicCost] using hb

theorem intersectionCost_union (S T : Finset ℕ) :
    intersectionCost (S ∪ T) ≤ intersectionCost S*intersectionCost T := by
  have he : S ∪ T=S ∪ (T \ S) := by ext p; simp
  rw [he,intersectionCost,Finset.prod_union (Finset.disjoint_left.mpr (fun p hp hpt => (Finset.mem_sdiff.mp hpt).2 hp))]
  apply mul_le_mul_of_nonneg_left ?_ (intersectionCost_nonneg S)
  exact Finset.prod_le_prod_of_subset_of_one_le
    (Finset.sdiff_subset : T \ S ⊆ T)
    (fun p _ => by linarith [primeSquareCorrectedWeight_nonneg (23/32) p])
    (fun p _ _ => by linarith [primeSquareCorrectedWeight_nonneg (23/32) p])

/-- The canonical least-pair mask itself is retained exactly. -/
theorem forbidden_intersectionCost {N p b : ℕ} (hsmall : secondPrime b ≤ N^3) :
    intersectionCost (forbidden p b) ≤
      (3 : ℝ)^(p*b).primeFactors.card*cubicCost N := by
  have hs : ∀ q ∈ smallPrimes b, q.Prime ∧ q ≤ N^3 := by
    intro q hq
    obtain ⟨hq,hp⟩ := Finset.mem_filter.mp hq
    exact ⟨hp,(Finset.mem_Icc.mp hq).2.trans hsmall⟩
  exact (intersectionCost_union _ _).trans
    (mul_le_mul (intersectionCost_le_three _) (intersectionCost_cubic_bound _ N hs)
      (intersectionCost_nonneg _) (by positivity))

/-- The certified source rate used below; independent of height. -/
def cubicRate : ℝ := exp (-(1/125000 : ℝ))

/-- Sublinear intersection growth does not consume the proved linear
source saving. The eventual start is not given as a feasible finite order. -/
theorem eventually_cubic_cost_geometric :
    ∀ᶠ N : ℕ in atTop,
      cubicRate^N*cubicCost N ≤ exp (-(1/250000 : ℝ))^N := by
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<5/32)).comp
    tendsto_natCast_atTop_atTop
  have hh := (ht.const_mul (64/9 : ℝ)).eventually
    (eventually_lt_nhds (by norm_num : (64/9 : ℝ)*0<1/250000))
  filter_upwards [hh,eventually_ge_atTop (1 : ℕ)] with N hN hpos
  have hNr : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have he : (N : ℝ)^(27/32 : ℝ)=(N : ℝ)*(N : ℝ)^(-(5/32 : ℝ)) := by
    calc
      _ = (N : ℝ)^((1 : ℝ)+(-(5/32 : ℝ))) := by norm_num
      _ = _ := by rw [rpow_add hNr,rpow_one]
  unfold cubicRate cubicCost
  rw [← exp_nat_mul,← exp_nat_mul,← exp_add]
  apply exp_le_exp.mpr
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hN.le (Nat.cast_nonneg (α := ℝ) N)
  simp only [Function.comp_def] at hm
  nlinarith only [hm]

theorem shell_error_product (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {M X : ℕ} (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (N : ℕ) (hlarge : exp ((N : ℝ)/2016) ≤ M)
    (a : ℕ → ℝ) (y c A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ d ∈ Finset.Ioc M X, |a d| ≤ A) :
    let w := ZetaRieszCofactorDiscrepancy.shellWeight M X a y c
    |(∑ d ∈ Finset.Icc 1 X, w d*sieve S d)-
      density S*(∑ d ∈ Finset.Icc 1 X, w d)| ≤
        countingCostAt (23/32)*intersectionCost S*exp (-9*(N : ℝ)/64512)*
          ((3+|y|)*A+∑ d ∈ Finset.Ico (M+1) X, |a d-a (d+1)|) := by
  have hC := (countingCostAt_pos (23/32)).le
  dsimp only
  have hactive k (_ : k ∈ Finset.Icc 1 X)
      (hz : ZetaRieszCofactorDiscrepancy.shellWeight M X a y c k ≠
        ZetaRieszCofactorDiscrepancy.shellWeight M X a y c (k+1)) : M ≤ k := by
    by_contra hn
    have hkM : k < M := lt_of_not_ge hn
    simp [ZetaRieszCofactorDiscrepancy.shellWeight,show ¬M<k by omega,
      show ¬M<k+1 by omega] at hz
  have hb := ZetaRieszPrimeWeightedSieve.weighted_error_exponential_product S hS (σ := 23/32) (by norm_num) (by norm_num) X N
    (ZetaRieszCofactorDiscrepancy.shellWeight M X a y c) (1/2016)
    (by simp [ZetaRieszCofactorDiscrepancy.shellWeight])
    (fun k hk hz => by
      have hMk : (M : ℝ) ≤ k := by exact_mod_cast hactive k hk hz
      simpa only [div_mul_eq_mul_div,one_mul] using hlarge.trans hMk)
  have he : -((1-(23/32 : ℝ))*(1/2016 : ℝ)*N)=-9*(N : ℝ)/64512 := by ring
  change |_-_| ≤ countingCostAt (23/32)*intersectionCost S*
    exp (-((1-(23/32 : ℝ))*(1/2016 : ℝ)*N))*_ at hb
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (ZetaRieszCofactorDiscrepancy.shellWeight_variation hM hMX hXM a y c A hA ha)
    (by positivity [intersectionCost_nonneg S] : 0 ≤ countingCostAt (23/32)*intersectionCost S*exp (-9*(N : ℝ)/64512)))

theorem owned_shell_error_product (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {N M X : ℕ} (hN : 32 ≤ N) (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (hlarge : exp ((N : ℝ)/2016) ≤ M) {P c : ℝ} (hP : 0 ≤ P)
    (hT : ∀ d ∈ Finset.Icc (M+1) X, 1 ≤ c+log d)
    (hPT : ∀ d ∈ Finset.Icc (M+1) X, P ≤ c+log d) (y : ℝ) :
    let w := ZetaRieszCofactorDiscrepancy.shellWeight M X (ownedAmplitude N P c) y c
    |(∑ d ∈ Finset.Icc 1 X, w d*sieve S d)-
      density S*(∑ d ∈ Finset.Icc 1 X, w d)| ≤
        countingCostAt (23/32)*intersectionCost S*exp (-9*(N : ℝ)/64512)*
          (((N : ℝ)+7+|y|)*radialEnvelope N) := by
  have hb := shell_error_product S hS hM hMX hXM N hlarge (ownedAmplitude N P c) y c
    (radialEnvelope N) (radialEnvelope_pos N).le
    (fun d hd => ownedAmplitude_bound N hP
      (hT d (Finset.mem_Icc.mpr ⟨by have := Finset.mem_Ioc.mp hd; omega,(Finset.mem_Ioc.mp hd).2⟩))
      (hPT d (Finset.mem_Icc.mpr ⟨by have := Finset.mem_Ioc.mp hd; omega,(Finset.mem_Ioc.mp hd).2⟩)))
  apply hb.trans
  have hC := (countingCostAt_pos (23/32)).le
  have ht := ownedAmplitude_variation hN hM hMX hXM hP hT hPT
  calc
    _ ≤ countingCostAt (23/32)*intersectionCost S*exp (-9*(N : ℝ)/64512)*
        ((3+|y|)*radialEnvelope N+((N : ℝ)+4)*radialEnvelope N) :=
      mul_le_mul_of_nonneg_left (add_le_add_right ht ((3+|y|)*radialEnvelope N))
        (by positivity [intersectionCost_nonneg S])
    _ = _ := by ring

/-- Counting constant at the improved exponent, fixed for every order. -/
def cubicErrorConstant : ℝ :=
  6*ZetaRieszWideOwnerAudit.radiusCeiling*countingCostAt (23/32)*
    ZetaRieszPrimeCountMass.countMass (65537/65536)*
      exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536))

theorem cubicErrorConstant_nonneg : 0 ≤ cubicErrorConstant := by
  unfold cubicErrorConstant ZetaRieszWideOwnerAudit.radiusCeiling
  positivity [countingCostAt_pos (23/32),
    ZetaRieszPrimeCountMass.countMass_nonneg (65537/65536)]

theorem cubicRate_bounds : 0 < cubicRate ∧ cubicRate < 1 :=
  ⟨exp_pos _,exp_lt_one_iff.mpr (by norm_num)⟩

theorem cubic_discrepancy_bound {N M X p b : ℕ} (hN : 32 ≤ N)
    (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (hlarge : exp ((N : ℝ)/2016) ≤ M) {L : ℝ} (hL : 0 < L)
    (hp : 0 < p) (hb : 0 < b) (hsmall : secondPrime b ≤ N^3) (hPL : log p ≤ L)
    (hT : ∀ d ∈ Finset.Icc (M+1) X, 1 ≤ log (p*b : ℕ)+log d)
    (y : ℝ) :
    |ZetaRieszRoughCutoffRows.ownedShellDiscrepancy N L y p b M X| ≤
      (countingCostAt (23/32)*exp (-9*(N : ℝ)/64512)*
        (((N : ℝ)+7+|y|)*radialEnvelope N))*
          (cubicCost N*(3^(p*b).primeFactors.card/(p*b : ℕ))) := by
  have hpb : (0 : ℝ)<(p*b : ℕ) := by exact_mod_cast Nat.mul_pos hp hb
  have hlog : log (p*b : ℕ) = log p+log b := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast hb.ne')]
  have hPT d (_ : d ∈ Finset.Icc (M+1) X) : log p ≤ log (p*b : ℕ)+log d := by
    rw [hlog]
    linarith [log_natCast_nonneg b,log_natCast_nonneg d]
  have he := owned_shell_error_product (forbidden p b)
    (forbidden_primes p b) hN hM hMX hXM hlarge
    (log_natCast_nonneg p) hT hPT y
  have hh := pairHinge_bounds L p b
  have hm : |(μ b : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := b)
  have hc : |(μ b : ℝ)*pairHinge L p b/(L*(p*b : ℕ))| ≤ 1/(p*b : ℕ) := by
    rw [abs_div,abs_mul,abs_of_nonneg hh.1,abs_of_pos (mul_pos hL hpb)]
    apply (div_le_iff₀ (mul_pos hL hpb)).mpr
    have hx := mul_le_mul_of_nonneg_right hm hh.1
    have heq : 1/(p*b : ℕ)*(L*(p*b : ℕ))=L := by field_simp
    rw [heq]
    exact hx.trans (by simpa using hh.2.trans hPL)
  have hs := forbidden_intersectionCost (p := p) hsmall
  rw [ZetaRieszRoughCutoffRows.ownedShellDiscrepancy,abs_mul]
  apply (mul_le_mul hc he (abs_nonneg _) (by positivity)).trans
  have hh := mul_le_mul_of_nonneg_right hs
    (by positivity [radialEnvelope_pos N,countingCostAt_pos (23/32)] :
      0 ≤ countingCostAt (23/32)*exp (-9*(N : ℝ)/64512)*
        (((N : ℝ)+7+|y|)*radialEnvelope N)/(p*b : ℕ))
  convert hh using 1 <;> ring



private def shiftedRate (u : ℝ) : ℝ := 2*u*exp (-((9/64512-203/6553600) : ℝ))

private theorem shiftedRate_bounds {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    0 ≤ shiftedRate u ∧ shiftedRate u ≤ cubicRate := by
  refine ⟨by unfold shiftedRate; positivity,?_⟩
  have hlog : log (2*ZetaRieszWideOwnerAudit.radiusCeiling) ≤ 1/10000 := by
    have h := log_le_sub_one_of_pos
      (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
        (0 : ℝ)<2*ZetaRieszWideOwnerAudit.radiusCeiling)
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at h ⊢
    exact h
  calc
    shiftedRate u ≤ 2*ZetaRieszWideOwnerAudit.radiusCeiling*exp (-((9/64512-203/6553600) : ℝ)) := by
      unfold shiftedRate; gcongr
    _ = exp (log (2*ZetaRieszWideOwnerAudit.radiusCeiling)-((9/64512-203/6553600) : ℝ)) := by
      rw [exp_sub,exp_log (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]),exp_neg]
      ring
    _ ≤ cubicRate := by unfold cubicRate; apply exp_le_exp.mpr; linarith

theorem source_scaled_cubic_shell_error (B : Finset (ℕ×ℕ)) {N : ℕ} (hN : 32 ≤ N)
    (M X : ℕ×ℕ → ℕ) (κ : ℕ×ℕ → ℝ)
    (hκ : ∀ pb ∈ B, |κ pb| ≤ 4) {L u : ℝ} (hL : 0 < L)
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (hB : ∀ pb ∈ B, pb.1.Prime ∧ Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2)
    (hlog : ∀ pb ∈ B, log (pb.1*pb.2 : ℕ) ≤ (203/100 : ℝ)*N)
    (hsmall : ∀ pb ∈ B, secondPrime pb.2 ≤ N^3)
    (hM : ∀ pb ∈ B, 0 < M pb)
    (hMX : ∀ pb ∈ B, M pb < X pb)
    (hXM : ∀ pb ∈ B, X pb ≤ 2*M pb)
    (hlarge : ∀ pb ∈ B, exp ((N : ℝ)/2016) ≤ M pb)
    (hPL : ∀ pb ∈ B, log pb.1 ≤ L)
    (hT : ∀ pb ∈ B, ∀ d ∈ Finset.Icc (M pb+1) (X pb),
      1 ≤ log (pb.1*pb.2 : ℕ)+log d) :
    |u^(N+1)*∑ pb ∈ B, κ pb*ZetaRieszRoughCutoffRows.ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| ≤
      4*cubicErrorConstant*((N : ℝ)+1)*((N : ℝ)+7+|y|)*cubicRate^N*cubicCost N := by
  have hc := (countingCostAt_pos (23/32)).le
  have hm := ZetaRieszPrimeCountMass.countMass_nonneg (65537/65536)
  let H := countingCostAt (23/32)*exp (-9*(N : ℝ)/64512)*(((N : ℝ)+7+|y|)*radialEnvelope N)*cubicCost N
  have hH : 0 ≤ H := by dsimp [H]; positivity [radialEnvelope_pos N,cubicCost_pos N]
  have he : |∑ pb ∈ B, κ pb*ZetaRieszRoughCutoffRows.ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| ≤
      4*H*(3*exp ((203/6553600 : ℝ)*N)*ZetaRieszPrimeCountMass.countMass (65537/65536)*
        exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536))) := by
    calc
      _ ≤ ∑ pb ∈ B, |κ pb*ZetaRieszRoughCutoffRows.ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ pb ∈ B, 4*H*(3^(pb.1*pb.2).primeFactors.card/(pb.1*pb.2 : ℕ)) := by
        apply Finset.sum_le_sum
        intro pb hpb
        have hd := cubic_discrepancy_bound hN (hM pb hpb) (hMX pb hpb) (hXM pb hpb)
          (hlarge pb hpb) hL (hB pb hpb).1.pos
          (Nat.pos_of_ne_zero (hB pb hpb).2.1.ne_zero) (hsmall pb hpb) (hPL pb hpb) (hT pb hpb) y
        rw [abs_mul]
        exact (mul_le_mul (hκ pb hpb) hd (abs_nonneg _) (by norm_num)).trans_eq (by ring)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (fine_outer_cost_bound B N hB hlog)
          (by positivity : 0 ≤ 4*H)
  have hex : exp (-9*(N : ℝ)/64512)*exp ((203/6553600 : ℝ)*N) =
      exp (-((9/64512-203/6553600) : ℝ))^N := by
    rw [← exp_add,← exp_nat_mul]
    congr 1
    ring
  have hnorm : |u^(N+1)*∑ pb ∈ B, κ pb*ZetaRieszRoughCutoffRows.ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| ≤
      (24*u*countingCostAt (23/32)*ZetaRieszPrimeCountMass.countMass (65537/65536)*
        exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536)))*
          ((N : ℝ)+1)*((N : ℝ)+7+|y|)*(shiftedRate u)^N*cubicCost N := by
    rw [abs_mul,abs_of_nonneg (pow_nonneg hu _)]
    apply (mul_le_mul_of_nonneg_left he (pow_nonneg hu _)).trans_eq
    dsimp [H,radialEnvelope,shiftedRate]
    rw [mul_pow,mul_pow,pow_succ,pow_succ]
    have heq := hex
    calc
      _ = (24*u*countingCostAt (23/32)*ZetaRieszPrimeCountMass.countMass (65537/65536)*
          exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536)))*
          ((N : ℝ)+1)*((N : ℝ)+7+|y|)*(2^N*u^N)*
            (exp (-9*(N : ℝ)/64512)*exp ((203/6553600 : ℝ)*N))*cubicCost N := by ring
      _ = _ := by rw [heq]; ring
  apply hnorm.trans
  have hr := shiftedRate_bounds hu hU
  have hconst : 24*u*countingCostAt (23/32)*ZetaRieszPrimeCountMass.countMass (65537/65536)*
      exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536)) ≤ 4*cubicErrorConstant := by
    unfold cubicErrorConstant
    calc
      _ ≤ 24*ZetaRieszWideOwnerAudit.radiusCeiling*countingCostAt (23/32)*
          ZetaRieszPrimeCountMass.countMass (65537/65536)*
          exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536)) := by gcongr
      _ = _ := by ring
  have hf : (24*u*countingCostAt (23/32)*ZetaRieszPrimeCountMass.countMass (65537/65536)*
      exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536)))*
        ((N : ℝ)+1)*((N : ℝ)+7+|y|)*(shiftedRate u)^N ≤
      4*cubicErrorConstant*((N : ℝ)+1)*((N : ℝ)+7+|y|)*cubicRate^N := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconst (by positivity)) (by positivity))
      (pow_le_pow_left₀ hr.1 hr.2 N) (pow_nonneg hr.1 N)
      (by positivity [cubicErrorConstant_nonneg,cubicRate_bounds.1])
  exact mul_le_mul_of_nonneg_right hf (cubicCost_pos N).le


/-- All radial shells may be joined before taking the signed comparison
error. A polynomial number of shells leaves the strict geometric saving.
The masks selecting each outer pair and each shell remain arbitrary. -/
theorem source_scaled_cubic_shells_error {ι : Type*} (I : Finset ι)
    (B : ι → Finset (ℕ×ℕ)) {N : ℕ} (hN : 32 ≤ N)
    (M X : ι → ℕ×ℕ → ℕ) (κ : ι → ℕ×ℕ → ℝ)
    (hκ : ∀ i ∈ I, ∀ pb ∈ B i, |κ i pb| ≤ 4) {L u : ℝ} (hL : 0 < L)
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (hI : I.card ≤ N+1)
    (hB : ∀ i ∈ I, ∀ pb ∈ B i, pb.1.Prime ∧ Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2)
    (hlog : ∀ i ∈ I, ∀ pb ∈ B i, log (pb.1*pb.2 : ℕ) ≤ (203/100 : ℝ)*N)
    (hsmall : ∀ i ∈ I, ∀ pb ∈ B i, secondPrime pb.2 ≤ N^3)
    (hM : ∀ i ∈ I, ∀ pb ∈ B i, 0 < M i pb)
    (hMX : ∀ i ∈ I, ∀ pb ∈ B i, M i pb < X i pb)
    (hXM : ∀ i ∈ I, ∀ pb ∈ B i, X i pb ≤ 2*M i pb)
    (hlarge : ∀ i ∈ I, ∀ pb ∈ B i, exp ((N : ℝ)/2016) ≤ M i pb)
    (hPL : ∀ i ∈ I, ∀ pb ∈ B i, log pb.1 ≤ L)
    (hT : ∀ i ∈ I, ∀ pb ∈ B i, ∀ d ∈ Finset.Icc (M i pb+1) (X i pb),
      1 ≤ log (pb.1*pb.2 : ℕ)+log d) :
    |u^(N+1)*∑ i ∈ I, ∑ pb ∈ B i,
      κ i pb*ZetaRieszRoughCutoffRows.ownedShellDiscrepancy N L y pb.1 pb.2 (M i pb) (X i pb)| ≤
      4*cubicErrorConstant*(8+|y|)*((N : ℝ)+1)^3*cubicRate^N*cubicCost N := by
  let C := 4*cubicErrorConstant*((N : ℝ)+1)*((N : ℝ)+7+|y|)*cubicRate^N*cubicCost N
  have hC : 0 ≤ C := by
    dsimp [C]; positivity [cubicErrorConstant_nonneg,cubicRate_bounds.1,cubicCost_pos N]
  calc
    _ ≤ ∑ i ∈ I, |u^(N+1)*∑ pb ∈ B i,
        κ i pb*ZetaRieszRoughCutoffRows.ownedShellDiscrepancy N L y pb.1 pb.2 (M i pb) (X i pb)| := by
      rw [Finset.mul_sum]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ I, C := Finset.sum_le_sum (fun i hi =>
      source_scaled_cubic_shell_error (B i) hN (M i) (X i) (κ i) (hκ i hi) hL hu hU y
        (hB i hi) (hlog i hi) (hsmall i hi) (hM i hi) (hMX i hi) (hXM i hi)
        (hlarge i hi) (hPL i hi) (hT i hi))
    _ = (I.card : ℝ)*C := by simp
    _ ≤ ((N : ℝ)+1)*C := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hI) hC
    _ ≤ _ := by
      have hp : (N : ℝ)+7+|y| ≤ (8+|y|)*((N : ℝ)+1) := by
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (abs_nonneg y)]
      have hh := mul_le_mul_of_nonneg_left hp
        (by positivity [cubicErrorConstant_nonneg,cubicRate_bounds.1,cubicCost_pos N] :
          0 ≤ 4*cubicErrorConstant*((N : ℝ)+1)^2*cubicRate^N*cubicCost N)
      dsimp [C]
      nlinarith only [hh]





end RiemannGaussian.ZetaRieszCubicSieveCost
