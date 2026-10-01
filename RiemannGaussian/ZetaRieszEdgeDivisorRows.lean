/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszUnifiedSignedRows

/-!
# The next literal signed divisor band

The squarefree counting exponent 17/32, rather than 3/4, independently
pays the ORIGINAL unsigned leg down to exp(N/2000). It permits additional
whole radial rows with 1949N/1000 < log(pb) <= 3899N/2000. All counts,
owner allocations, coprimality, core masks and phases remain literal.
The numerical -79/1000 floor is not asserted.
-/

noncomputable section
open Filter Topology Real MeasureTheory Set
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszEdgeDivisorRows
open ZetaRieszUnifiedSignedRows ZetaRieszUnsignedDivisorError ZetaRieszSignedConvolution
open ZetaRieszSaturatedRowFloor ZetaRieszOwnerMaximal ZetaRieszFreeRadialRows
open ZetaRieszFineDivisorRows ZetaRieszPrimeCountFrequency

private theorem edge_shell_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {M X : ℕ} (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (N : ℕ) (hlarge : exp ((N : ℝ)/2000) ≤ M)
    (a : ℕ → ℝ) (y c A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ d ∈ Finset.Ioc M X, |a d| ≤ A) :
    let w := ZetaRieszCofactorDiscrepancy.shellWeight M X a y c
    |(∑ d ∈ Finset.Icc 1 X, w d*sieve S d)-
      density S*(∑ d ∈ Finset.Icc 1 X, w d)| ≤
        countingCostAt (17/32)*3^S.card*exp (-15*(N : ℝ)/64000)*
          ((3+|y|)*A+∑ d ∈ Finset.Ico (M+1) X, |a d-a (d+1)|) := by
  have hC := (countingCostAt_pos (17/32)).le
  dsimp only
  have hactive k (_ : k ∈ Finset.Icc 1 X)
      (hz : ZetaRieszCofactorDiscrepancy.shellWeight M X a y c k ≠
        ZetaRieszCofactorDiscrepancy.shellWeight M X a y c (k+1)) : M ≤ k := by
    by_contra hn
    have hkM : k < M := lt_of_not_ge hn
    simp [ZetaRieszCofactorDiscrepancy.shellWeight,show ¬M<k by omega,
      show ¬M<k+1 by omega] at hz
  have hb := weighted_error_exponential_at S hS (σ := 17/32) (by norm_num) (by norm_num) X N
    (ZetaRieszCofactorDiscrepancy.shellWeight M X a y c) (1/2000)
    (by simp [ZetaRieszCofactorDiscrepancy.shellWeight])
    (fun k hk hz => by
      have hMk : (M : ℝ) ≤ k := by exact_mod_cast hactive k hk hz
      simpa only [div_mul_eq_mul_div,one_mul] using hlarge.trans hMk)
  have he : -((1-(17/32 : ℝ))*(1/2000 : ℝ)*N)=-15*(N : ℝ)/64000 := by ring
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (ZetaRieszCofactorDiscrepancy.shellWeight_variation hM hMX hXM a y c A hA ha)
    (by positivity : 0 ≤ countingCostAt (17/32)*3^S.card*exp (-15*(N : ℝ)/64000)))

private theorem edge_owned_shell_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {N M X : ℕ} (hN : 32 ≤ N) (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (hlarge : exp ((N : ℝ)/2000) ≤ M) {P c : ℝ} (hP : 0 ≤ P)
    (hT : ∀ d ∈ Finset.Icc (M+1) X, 1 ≤ c+log d)
    (hPT : ∀ d ∈ Finset.Icc (M+1) X, P ≤ c+log d) (y : ℝ) :
    let w := ZetaRieszCofactorDiscrepancy.shellWeight M X (ownedAmplitude N P c) y c
    |(∑ d ∈ Finset.Icc 1 X, w d*sieve S d)-
      density S*(∑ d ∈ Finset.Icc 1 X, w d)| ≤
        countingCostAt (17/32)*3^S.card*exp (-15*(N : ℝ)/64000)*
          (((N : ℝ)+7+|y|)*radialEnvelope N) := by
  have hb := edge_shell_error S hS hM hMX hXM N hlarge (ownedAmplitude N P c) y c
    (radialEnvelope N) (radialEnvelope_pos N).le
    (fun d hd => ownedAmplitude_bound N hP
      (hT d (Finset.mem_Icc.mpr ⟨by have := Finset.mem_Ioc.mp hd; omega,(Finset.mem_Ioc.mp hd).2⟩))
      (hPT d (Finset.mem_Icc.mpr ⟨by have := Finset.mem_Ioc.mp hd; omega,(Finset.mem_Ioc.mp hd).2⟩)))
  apply hb.trans
  have hC := (countingCostAt_pos (17/32)).le
  have ht := ownedAmplitude_variation hN hM hMX hXM hP hT hPT
  calc
    _ ≤ countingCostAt (17/32)*3^S.card*exp (-15*(N : ℝ)/64000)*
        ((3+|y|)*radialEnvelope N+((N : ℝ)+4)*radialEnvelope N) :=
      mul_le_mul_of_nonneg_left (add_le_add_right ht ((3+|y|)*radialEnvelope N))
        (by positivity)
    _ = _ := by ring

private theorem edge_discrepancy_bound {N M X p b : ℕ} (hN : 32 ≤ N)
    (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (hlarge : exp ((N : ℝ)/2000) ≤ M) {L : ℝ} (hL : 0 < L)
    (hp : 0 < p) (hb : 0 < b) (hPL : log p ≤ L)
    (hT : ∀ d ∈ Finset.Icc (M+1) X, 1 ≤ log (p*b : ℕ)+log d)
    (y : ℝ) :
    |ownedShellDiscrepancy N L y p b M X| ≤
      (countingCostAt (17/32)*exp (-15*(N : ℝ)/64000)*
        (((N : ℝ)+7+|y|)*radialEnvelope N))*
          (3^(p*b).primeFactors.card/(p*b : ℕ)) := by
  have hpb : (0 : ℝ)<(p*b : ℕ) := by exact_mod_cast Nat.mul_pos hp hb
  have hlog : log (p*b : ℕ) = log p+log b := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast hb.ne')]
  have hPT d (_ : d ∈ Finset.Icc (M+1) X) : log p ≤ log (p*b : ℕ)+log d := by
    rw [hlog]
    linarith [log_natCast_nonneg b,log_natCast_nonneg d]
  have he := edge_owned_shell_error (p*b).primeFactors
    (fun _ h => Nat.prime_of_mem_primeFactors h) hN hM hMX hXM hlarge
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
  rw [ownedShellDiscrepancy,abs_mul]
  exact (mul_le_mul hc he (abs_nonneg _) (by positivity)).trans_eq (by ring)


private def edgeRate (u : ℝ) : ℝ := 2*u*exp (-(1333/6553600 : ℝ))

private theorem edgeRate_bounds {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    0 ≤ edgeRate u ∧ edgeRate u ≤ comparisonRate := by
  refine ⟨by unfold edgeRate; positivity,?_⟩
  have hlog : log (2*ZetaRieszWideOwnerAudit.radiusCeiling) ≤ 1/10000 := by
    have h := log_le_sub_one_of_pos
      (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
        (0 : ℝ)<2*ZetaRieszWideOwnerAudit.radiusCeiling)
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at h ⊢
    exact h
  calc
    edgeRate u ≤ 2*ZetaRieszWideOwnerAudit.radiusCeiling*exp (-(1333/6553600 : ℝ)) := by
      unfold edgeRate; gcongr
    _ = exp (log (2*ZetaRieszWideOwnerAudit.radiusCeiling)-(1333/6553600 : ℝ)) := by
      rw [exp_sub,exp_log (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]),exp_neg]
      ring
    _ ≤ comparisonRate := by unfold comparisonRate; apply exp_le_exp.mpr; linarith

/-- Every original prime-count intersection is included in this finite
constant; it does not depend on order, owner, height or count cutoff. -/
def edgeErrorConstant : ℝ :=
  6*ZetaRieszWideOwnerAudit.radiusCeiling*countingCostAt (17/32)*
    ZetaRieszPrimeCountMass.countMass (65537/65536)*
      exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536))

theorem edgeErrorConstant_nonneg : 0 ≤ edgeErrorConstant := by
  have hc := (countingCostAt_pos (17/32)).le
  have hm := ZetaRieszPrimeCountMass.countMass_nonneg (65537/65536)
  unfold edgeErrorConstant ZetaRieszWideOwnerAudit.radiusCeiling
  positivity

theorem source_scaled_edge_shell_error (B : Finset (ℕ×ℕ)) {N : ℕ} (hN : 32 ≤ N)
    (M X : ℕ×ℕ → ℕ) {L u : ℝ} (hL : 0 < L)
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (hB : ∀ pb ∈ B, pb.1.Prime ∧ Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2)
    (hlog : ∀ pb ∈ B, log (pb.1*pb.2 : ℕ) ≤ (203/100 : ℝ)*N)
    (hM : ∀ pb ∈ B, 0 < M pb)
    (hMX : ∀ pb ∈ B, M pb < X pb)
    (hXM : ∀ pb ∈ B, X pb ≤ 2*M pb)
    (hlarge : ∀ pb ∈ B, exp ((N : ℝ)/2000) ≤ M pb)
    (hPL : ∀ pb ∈ B, log pb.1 ≤ L)
    (hT : ∀ pb ∈ B, ∀ d ∈ Finset.Icc (M pb+1) (X pb),
      1 ≤ log (pb.1*pb.2 : ℕ)+log d) :
    |u^(N+1)*∑ pb ∈ B, ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| ≤
      edgeErrorConstant*((N : ℝ)+1)*((N : ℝ)+7+|y|)*comparisonRate^N := by
  have hc := (countingCostAt_pos (17/32)).le
  have hm := ZetaRieszPrimeCountMass.countMass_nonneg (65537/65536)
  let H := countingCostAt (17/32)*exp (-15*(N : ℝ)/64000)*(((N : ℝ)+7+|y|)*radialEnvelope N)
  have hH : 0 ≤ H := by dsimp [H]; positivity [radialEnvelope_pos N]
  have he : |∑ pb ∈ B, ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| ≤
      H*(3*exp ((203/6553600 : ℝ)*N)*ZetaRieszPrimeCountMass.countMass (65537/65536)*
        exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536))) := by
    calc
      _ ≤ ∑ pb ∈ B, |ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ pb ∈ B, H*(3^(pb.1*pb.2).primeFactors.card/(pb.1*pb.2 : ℕ)) := by
        apply Finset.sum_le_sum
        intro pb hpb
        exact edge_discrepancy_bound hN (hM pb hpb) (hMX pb hpb) (hXM pb hpb)
          (hlarge pb hpb) hL (hB pb hpb).1.pos
          (Nat.pos_of_ne_zero (hB pb hpb).2.1.ne_zero) (hPL pb hpb) (hT pb hpb) y
      _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (fine_outer_cost_bound B N hB hlog) hH
  have hex : exp (-15*(N : ℝ)/64000)*exp ((203/6553600 : ℝ)*N) =
      exp (-(1333/6553600 : ℝ))^N := by
    rw [← exp_add,← exp_nat_mul]
    congr 1
    ring
  have hnorm : |u^(N+1)*∑ pb ∈ B, ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| ≤
      (6*u*countingCostAt (17/32)*ZetaRieszPrimeCountMass.countMass (65537/65536)*
        exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536)))*
          ((N : ℝ)+1)*((N : ℝ)+7+|y|)*(edgeRate u)^N := by
    rw [abs_mul,abs_of_nonneg (pow_nonneg hu _)]
    apply (mul_le_mul_of_nonneg_left he (pow_nonneg hu _)).trans_eq
    dsimp [H,radialEnvelope,edgeRate]
    rw [mul_pow,mul_pow,pow_succ,pow_succ]
    have heq := hex
    calc
      _ = (6*u*countingCostAt (17/32)*ZetaRieszPrimeCountMass.countMass (65537/65536)*
          exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536)))*
          ((N : ℝ)+1)*((N : ℝ)+7+|y|)*(2^N*u^N)*
            (exp (-15*(N : ℝ)/64000)*exp ((203/6553600 : ℝ)*N)) := by ring
      _ = _ := by rw [heq]; ring
  apply hnorm.trans
  have hr := edgeRate_bounds hu hU
  have hconst : 6*u*countingCostAt (17/32)*ZetaRieszPrimeCountMass.countMass (65537/65536)*
      exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536)) ≤ edgeErrorConstant := by
    unfold edgeErrorConstant
    gcongr
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconst (by positivity)) (by positivity))
    (pow_le_pow_left₀ hr.1 hr.2 N) (pow_nonneg hr.1 N)
    (by positivity [edgeErrorConstant_nonneg,comparisonRate_bounds.1])

/-- All radial shells may be joined before taking the signed comparison
error. A polynomial number of shells leaves the strict geometric saving.
The masks selecting each outer pair and each shell remain arbitrary. -/
theorem source_scaled_edge_shells_error {ι : Type*} (I : Finset ι)
    (B : ι → Finset (ℕ×ℕ)) {N : ℕ} (hN : 32 ≤ N)
    (M X : ι → ℕ×ℕ → ℕ) {L u : ℝ} (hL : 0 < L)
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (hI : I.card ≤ N+1)
    (hB : ∀ i ∈ I, ∀ pb ∈ B i, pb.1.Prime ∧ Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2)
    (hlog : ∀ i ∈ I, ∀ pb ∈ B i, log (pb.1*pb.2 : ℕ) ≤ (203/100 : ℝ)*N)
    (hM : ∀ i ∈ I, ∀ pb ∈ B i, 0 < M i pb)
    (hMX : ∀ i ∈ I, ∀ pb ∈ B i, M i pb < X i pb)
    (hXM : ∀ i ∈ I, ∀ pb ∈ B i, X i pb ≤ 2*M i pb)
    (hlarge : ∀ i ∈ I, ∀ pb ∈ B i, exp ((N : ℝ)/2000) ≤ M i pb)
    (hPL : ∀ i ∈ I, ∀ pb ∈ B i, log pb.1 ≤ L)
    (hT : ∀ i ∈ I, ∀ pb ∈ B i, ∀ d ∈ Finset.Icc (M i pb+1) (X i pb),
      1 ≤ log (pb.1*pb.2 : ℕ)+log d) :
    |u^(N+1)*∑ i ∈ I, ∑ pb ∈ B i,
      ownedShellDiscrepancy N L y pb.1 pb.2 (M i pb) (X i pb)| ≤
      edgeErrorConstant*(8+|y|)*((N : ℝ)+1)^3*comparisonRate^N := by
  let C := edgeErrorConstant*((N : ℝ)+1)*((N : ℝ)+7+|y|)*comparisonRate^N
  have hC : 0 ≤ C := by
    dsimp [C]; positivity [edgeErrorConstant_nonneg,comparisonRate_bounds.1]
  calc
    _ ≤ ∑ i ∈ I, |u^(N+1)*∑ pb ∈ B i,
        ownedShellDiscrepancy N L y pb.1 pb.2 (M i pb) (X i pb)| := by
      rw [Finset.mul_sum]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ I, C := Finset.sum_le_sum (fun i hi =>
      source_scaled_edge_shell_error (B i) hN (M i) (X i) hL hu hU y
        (hB i hi) (hlog i hi) (hM i hi) (hMX i hi) (hXM i hi)
        (hlarge i hi) (hPL i hi) (hT i hi))
    _ = (I.card : ℝ)*C := by simp
    _ ≤ ((N : ℝ)+1)*C := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hI) hC
    _ ≤ _ := by
      have hp : (N : ℝ)+7+|y| ≤ (8+|y|)*((N : ℝ)+1) := by
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (abs_nonneg y)]
      have hh := mul_le_mul_of_nonneg_left hp
        (by positivity [edgeErrorConstant_nonneg,comparisonRate_bounds.1] :
          0 ≤ edgeErrorConstant*((N : ℝ)+1)^2*comparisonRate^N)
      dsimp [C]
      nlinarith only [hh]




/-- The exact new outer cutoff corresponding to log(d)>=N/2000. -/
private theorem gap_eq_cut : (39/20 : ℝ)-1/2000 = 3899/2000 := by norm_num

/-- Counting comparison cost, pooled over all original outer counts. -/
def edgeComparisonBudget (y : ℝ) (N : ℕ) : ℝ :=
  edgeErrorConstant*(8+|y|)*((N : ℝ)+1)^3*comparisonRate^N

/-- The new all-count row cost. The radial main is summed with sign first. -/
def edgeRowBudget (y : ℝ) (N : ℕ) : ℝ :=
  fineMainBudget y N+edgeErrorConstant*(8+|y|)*((N : ℝ)+1)^3*comparisonRate^N+
    highCountConstant*((N : ℝ)+1)^2*(49/50 : ℝ)^N

/-- The source-geometric rounded boundary cost on this new band. -/
def edgeEndpointRate : ℝ := exp (-(1/2500 : ℝ))

private theorem edgeEndpointRate_bounds : 0 < edgeEndpointRate ∧ edgeEndpointRate < 1 := by
  exact ⟨exp_pos _,exp_lt_one_iff.mpr (by norm_num)⟩

/-- The independently paid original rounded-endpoint allowance. -/
def edgeEndpointBudget (N : ℕ) : ℝ :=
  18*((N : ℝ)+1)^3*edgeEndpointRate^N

theorem tendsto_edgeRowBudget (y : ℝ) : Tendsto (edgeRowBudget y) atTop (𝓝 0) := by
  have he := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 3
    comparisonRate_bounds.1 comparisonRate_bounds.2).const_mul (edgeErrorConstant*(8+|y|))
  have hce : Tendsto (edgeComparisonBudget y) atTop (𝓝 0) := by
    simp only [mul_zero] at he
    convert he using 1
    ext N
    unfold edgeComparisonBudget
    ring
  have hc := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 2
    (by norm_num : (0 : ℝ)<49/50) (by norm_num : (49/50 : ℝ)<1)).const_mul highCountConstant
  have hcc : Tendsto (fun N : ℕ =>
      highCountConstant*((N : ℝ)+1)^2*(49/50 : ℝ)^N) atTop (𝓝 0) := by
    simp only [mul_zero] at hc
    convert hc using 1
    ext N
    ring
  change Tendsto (fun N : ℕ => fineMainBudget y N+edgeComparisonBudget y N+
    highCountConstant*((N : ℝ)+1)^2*(49/50 : ℝ)^N) atTop (𝓝 0)
  simpa only [zero_add] using ((tendsto_fineMainBudget y).add hce).add hcc

theorem tendsto_edgeEndpointBudget : Tendsto edgeEndpointBudget atTop (𝓝 0) := by
  have h := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 3
    edgeEndpointRate_bounds.1 edgeEndpointRate_bounds.2).const_mul 18
  simp only [mul_zero] at h
  convert h using 1
  ext N
  unfold edgeEndpointBudget
  ring

/-- An auxiliary cutoff for finite ownership only; arithmetic atoms
retain the original moving Riesz length. -/
def ownershipLength (N : ℕ) : ℝ := (31/20 : ℝ)*N

/-- Original finite rows on the finer outer band; no prime or cofactor is completed. -/
def edgeRows (u : ℝ) (N : ℕ) : Finset (ℕ×ℕ) :=
  ((ZetaRieszAnnulusJoint.intermediatePrimes u N).product
    (Finset.Icc 2 ⌊exp ((203/100 : ℝ)*N)⌋₊)).filter fun pb =>
      Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2 ∧
      (∀ q ∈ pb.2.primeFactors, q < pb.1) ∧
      pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2 ≠ 0 ∧
      log (pb.1*pb.2 : ℕ) ≤ (3899/2000 : ℝ)*N ∧
      log pb.1 < (243/200 : ℝ)*N ∧
      (1949/1000 : ℝ)*N < log (pb.1*pb.2 : ℕ) ∧
      (N : ℝ)/2 ≤ log pb.1 ∧
      ownershipLength N < log (pb.1*pb.2 : ℕ) ∧
      ZetaRieszFineDivisorRows.lower N pb.1 pb.2 ≤ ZetaRieszFineDivisorRows.upper N pb.1 pb.2

private theorem row_owner_mem {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (h : pb ∈ edgeRows u N) :
    pb.1 ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N :=
  (Finset.mem_product.mp (Finset.mem_filter.mp h).1).1

private theorem row_large {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (h : pb ∈ edgeRows u N) : exp ((N : ℝ)/2000) ≤ ZetaRieszFineDivisorRows.lower N pb.1 pb.2 := by
  have hc := (Finset.mem_filter.mp h).2.2.2.2.2.1
  exact (exp_le_exp.mpr (by linarith : (N : ℝ)/2000 ≤
    (39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ))).trans (Nat.le_ceil _)

/-- Every new row has full original ownership. The auxiliary length
certifies the finite geometry; it does not replace the actual cutoff. -/
theorem edge_row_geometry {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (h : pb ∈ edgeRows u N) :
    RowGeometry N (ownershipLength N) pb.1 pb.2
      (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) (ZetaRieszFineDivisorRows.upper N pb.1 pb.2) := by
  obtain ⟨hprod,hs,hpd,hmax,_ha,hc,hP,_hOld,hPl,hcl,hlu⟩ := Finset.mem_filter.mp h
  obtain ⟨hp,hb⟩ := Finset.mem_product.mp hprod
  have hp' := (ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp hp
  have hp0 : (0 : ℝ)<pb.1 := by exact_mod_cast hp'.1.pos
  have hb0 : (0 : ℝ)<pb.2 := by
    have hbpos : 0 < pb.2 := by have := (Finset.mem_Icc.mp hb).1; omega
    exact_mod_cast hbpos
  have hlog : log (pb.1*pb.2 : ℕ)=log pb.1+log pb.2 := by
    rw [Nat.cast_mul,log_mul hp0.ne' hb0.ne']
  have hM : 0 < ZetaRieszFineDivisorRows.lower N pb.1 pb.2 := Nat.ceil_pos.mpr (exp_pos _)
  have hX := hM.trans_le hlu
  have hlo : (39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ) ≤ log (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) := by
    simpa only [log_exp,ZetaRieszFineDivisorRows.lower] using log_le_log (exp_pos _)
      (Nat.le_ceil (exp ((39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ))))
  have hhi : log (ZetaRieszFineDivisorRows.upper N pb.1 pb.2) ≤ (203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ) := by
    simpa only [log_exp,ZetaRieszFineDivisorRows.upper] using log_le_log
      (by exact_mod_cast hX : (0 : ℝ)<ZetaRieszFineDivisorRows.upper N pb.1 pb.2)
      (Nat.floor_le (exp_pos ((203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ))).le)
  have hB : log pb.2 ≤ ownershipLength N := by
    dsimp [ownershipLength] at *
    rw [hlog] at hc
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hactive : pairHinge (ownershipLength N) pb.1 pb.2 ≠ 0 := by
    rw [pairHinge,max_eq_left (sub_nonpos.mpr hB),sub_zero,
      max_eq_right (by rw [← hlog]; linarith : 0 ≤ log pb.1+log pb.2-ownershipLength N)]
    rw [← hlog]
    exact (sub_pos.mpr hcl).ne'
  refine ⟨hp'.1,by have := (Finset.mem_Icc.mp hb).1; omega,hs,hpd,hmax,hactive,hM,
    by linarith,by linarith,?_,?_⟩
  · rw [hlog] at hhi
    dsimp [ownershipLength]
    linarith [Nat.cast_nonneg (α := ℝ) N]
  · nlinarith [Nat.cast_nonneg (α := ℝ) N]


private theorem row_data {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (h : pb ∈ edgeRows u N) :
    log (pb.1*pb.2 : ℕ) ≤ (3899/2000 : ℝ)*N ∧
      log pb.1 < (243/200 : ℝ)*N ∧ ZetaRieszFineDivisorRows.lower N pb.1 pb.2 ≤ ZetaRieszFineDivisorRows.upper N pb.1 pb.2 := by
  obtain ⟨_,_,_,_,_,hc,hP,_,_,_,hlu⟩ := Finset.mem_filter.mp h
  exact ⟨hc,hP,hlu⟩

private theorem coefficient_bound {u : ℝ} {N : ℕ} (hN : 32 ≤ N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    {pb : ℕ×ℕ} (hpb : pb ∈ edgeRows u N) :
    |((μ pb.2 : ℝ)*pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2/
        (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)))*
        density (pb.1*pb.2).primeFactors| ≤ (1 : ℝ)/(pb.1*pb.2 : ℕ) := by
  have hg := edge_row_geometry hpb
  have hP := (Finset.mem_filter.mp hpb).2.2.2.2.2.2.1
  have hn : (32 : ℝ)≤N := by exact_mod_cast hN
  have hL0 : 0 < SquarefreeVaughanLogSource.length u N := by linarith
  have hpb0 : (0 : ℝ)<(pb.1*pb.2 : ℕ) := by
    exact_mod_cast Nat.mul_pos hg.1.pos (by have := hg.2.1; omega)
  have hH := pairHinge_bounds (SquarefreeVaughanLogSource.length u N) pb.1 pb.2
  have hHL : pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2 ≤
      SquarefreeVaughanLogSource.length u N := by linarith [hH.2]
  have hd := density_bounds (pb.1*pb.2).primeFactors (fun _ hq => Nat.prime_of_mem_primeFactors hq)
  have hm : |(μ pb.2 : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := pb.2)
  rw [abs_mul,abs_div,abs_mul,abs_of_nonneg hH.1,abs_of_nonneg hd.1,
    abs_of_pos (mul_pos hL0 hpb0)]
  have hnum : |(μ pb.2 : ℝ)| * pairHinge
      (SquarefreeVaughanLogSource.length u N) pb.1 pb.2*density (pb.1*pb.2).primeFactors ≤
      SquarefreeVaughanLogSource.length u N :=
    (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) hH.1) hd.2).trans
      ((mul_le_of_le_one_left hH.1 hm).trans hHL)
  calc
    _ = (|(μ pb.2 : ℝ)| *pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2*
      density (pb.1*pb.2).primeFactors)/(SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)) := by ring
    _ ≤ SquarefreeVaughanLogSource.length u N/
        (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)) :=
      div_le_div_of_nonneg_right hnum (mul_pos hL0 hpb0).le
    _ = _ := by field_simp

set_option backward.isDefEq.respectTransparency false in
/-- All outer counts have only harmonic mass after the unsigned leg is
joined and cancelled. No exponential count majorant is charged here. -/
private theorem outer_harmonic_bound (u : ℝ) (N : ℕ) :
    (∑ pb ∈ edgeRows u N, (1 : ℝ)/(pb.1*pb.2 : ℕ)) ≤
      (1+(203/100 : ℝ)*N)^2 := by
  let B := ⌊exp ((203/100 : ℝ)*N)⌋₊
  have hBn : 0 < B := Nat.floor_pos.mpr (one_le_exp (by positivity))
  have hB : (0 : ℝ)<B := by exact_mod_cast hBn
  have hlogB : log B ≤ (203/100 : ℝ)*N := by
    have hh := log_le_log hB (Nat.floor_le (exp_pos ((203/100 : ℝ)*N)).le)
    simpa only [log_exp] using hh
  have hsub : edgeRows u N ⊆ (Finset.Icc 1 B).product (Finset.Icc 1 B) := by
    intro pb hpb
    have hg := edge_row_geometry hpb
    have hb := (Finset.mem_product.mp (Finset.mem_filter.mp hpb).1).2
    have hp : log pb.1 ≤ (13/20 : ℝ)*((203/100 : ℝ)*N) := by
      have hP := (Finset.mem_filter.mp hpb).2.2.2.2.2.2.1
      have hn := Nat.cast_nonneg (α := ℝ) N
      linarith
    have hpB : pb.1 ≤ B := by
      apply Nat.le_floor
      rw [← exp_log (by exact_mod_cast hg.1.pos : (0 : ℝ)<pb.1)]
      apply exp_le_exp.mpr
      linarith [Nat.cast_nonneg (α := ℝ) N]
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hg.1.pos,hpB⟩,
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hb).1; omega,(Finset.mem_Icc.mp hb).2⟩⟩
  have hhar : (∑ d ∈ Finset.Icc 1 B, (d : ℝ)⁻¹) ≤ 1+(203/100 : ℝ)*N := by
    have hh := harmonic_le_one_add_log B
    rw [harmonic_eq_sum_Icc,Rat.cast_sum] at hh
    push_cast at hh
    exact hh.trans (add_le_add_right hlogB 1)
  have he : (∑ pb ∈ (Finset.Icc 1 B).product (Finset.Icc 1 B), (1 : ℝ)/(pb.1*pb.2 : ℕ)) =
      (∑ d ∈ Finset.Icc 1 B, (d : ℝ)⁻¹)^2 := by
    calc
      _ = ∑ p ∈ Finset.Icc 1 B, ∑ b ∈ Finset.Icc 1 B, (1 : ℝ)/(p*b : ℕ) :=
        Finset.sum_product (Finset.Icc 1 B) (Finset.Icc 1 B)
          (fun pb : ℕ×ℕ => (1 : ℝ)/(pb.1*pb.2 : ℕ))
      _ = _ := by
        simp only [Nat.cast_mul,one_div,mul_inv]
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul,pow_two]
  calc
    _ ≤ ∑ pb ∈ (Finset.Icc 1 B).product (Finset.Icc 1 B), (1 : ℝ)/(pb.1*pb.2 : ℕ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = _ := he
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity)) hhar 2

/-- The actual signed density main on the new original row population. -/
def edgeDensityMain (u y : ℝ) (N : ℕ) : ℝ :=
  ∑ pb ∈ edgeRows u N, densityRow N (SquarefreeVaughanLogSource.length u N) y
    pb.1 pb.2 (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) (ZetaRieszFineDivisorRows.upper N pb.1 pb.2)

/-- The entire signed main is paid before its outer rows/counts are
normed. Saturation is absent; the original allocation and phase remain. -/
theorem source_scaled_edgeDensityMain_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 32 ≤ N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    {y : ℝ} (hy : 54 ≤ |y|) :
    |u^(N+1)*edgeDensityMain u y N| ≤ fineMainBudget y N := by
  have hrow pb (hpb : pb ∈ edgeRows u N) :
      |u^(N+1)*densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
        (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) (ZetaRieszFineDivisorRows.upper N pb.1 pb.2)| ≤
        (1 : ℝ)/(pb.1*pb.2 : ℕ)*
          (((N : ℝ)+1)*(13*(N : ℝ)+33+4*|y|)*fineRateTotal^N) := by
    rw [densityRow_physical]
    rw [show u^(N+1)*
      (((μ pb.2 : ℝ)*pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2/
        (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)))*
        density (pb.1*pb.2).primeFactors*
        (∑ d ∈ Finset.Ioc (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) (ZetaRieszFineDivisorRows.upper N pb.1 pb.2),
          physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))) =
      (((μ pb.2 : ℝ)*pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2/
        (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)))*
        density (pb.1*pb.2).primeFactors)*
        (u^(N+1)*(∑ d ∈ Finset.Ioc (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) (ZetaRieszFineDivisorRows.upper N pb.1 pb.2),
          physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))) by ring,
      abs_mul]
    exact mul_le_mul (coefficient_bound hN hL hpb)
      (full_window_weight_bound_of_gap hu hU hN (β := 1/2000) (by norm_num)
        (by simpa only [gap_eq_cut] using (row_data hpb).1) (row_data hpb).2.1 (row_data hpb).2.2 hy) (abs_nonneg _) (by positivity)
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum hrow)
  have hs : |u^(N+1)*edgeDensityMain u y N| ≤
      (1+(203/100 : ℝ)*N)^2*
        (((N : ℝ)+1)*(13*(N : ℝ)+33+4*|y|)*fineRateTotal^N) := by
    rw [edgeDensityMain,Finset.mul_sum]
    apply hsum.trans
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (outer_harmonic_bound u N)
      (by positivity [fineRateTotal_bounds.1])
  have hp1 : (1+(203/100 : ℝ)*N)^2 ≤ 9*((N : ℝ)+1)^2 := by
    have h : 1+(203/100 : ℝ)*N ≤ 3*((N : ℝ)+1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    exact (pow_le_pow_left₀ (by positivity) h 2).trans_eq (by ring)
  have hp2 : 13*(N : ℝ)+33+4*|y| ≤ (33+4*|y|)*((N : ℝ)+1) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (abs_nonneg y)]
  apply hs.trans
  unfold fineMainBudget
  have h := mul_le_mul hp1
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2
      (show 0 ≤ (N : ℝ)+1 by positivity))
      (pow_nonneg fineRateTotal_bounds.1.le N))
    (by positivity [fineRateTotal_bounds.1]) (by positivity)
  convert h using 1
  ring

private theorem last_boundary {u : ℝ} {N : ℕ} {pb : ℕ×ℕ} (hpb : pb ∈ edgeRows u N)
    (_hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    boundary (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper N pb.1 pb.2) (N+1) =
        ZetaRieszFineDivisorRows.upper N pb.1 pb.2 := by
  have hg := edge_row_geometry hpb
  have ha := pairHinge_active hg.2.2.2.2.2.1
  have hp0 := hg.1.pos
  have hb0 : 0 < pb.2 := by have := hg.2.1; omega
  have hlog : log (pb.1*pb.2 : ℕ)=log pb.1+log pb.2 := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp0.ne') (by exact_mod_cast hb0.ne')]
  have hU : (ZetaRieszFineDivisorRows.upper N pb.1 pb.2 : ℝ) ≤
      exp ((131/200 : ℝ)*N) := by
    have hf := Nat.floor_le (exp_pos (((203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ)))).le
    have he : ((203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ)) ≤ (131/200 : ℝ)*N := by
      rw [← hlog] at ha
      dsimp [ownershipLength] at ha
      linarith [Nat.cast_nonneg (α := ℝ) N]
    exact hf.trans (exp_le_exp.mpr he)
  have hpow : exp ((131/200 : ℝ)*N) ≤
      ((2^(N+1)*ZetaRieszFineDivisorRows.lower N pb.1 pb.2 : ℕ) : ℝ) := by
    have hbase := row_large hpb
    have hrate : (131/200 : ℝ)*N ≤ (N+1 : ℕ)*log 2+(N : ℝ)/2000 := by
      push_cast
      nlinarith [log_two_gt_d9,log_pos (by norm_num : (1 : ℝ)<2)]
    calc
      _ ≤ exp ((N+1 : ℕ)*log 2+(N : ℝ)/2000) := exp_le_exp.mpr hrate
      _ = (2 : ℝ)^(N+1)*exp ((N : ℝ)/2000) := by rw [exp_add,exp_nat_mul,exp_log (by norm_num : (0 : ℝ)<2)]
      _ ≤ (2 : ℝ)^(N+1)*ZetaRieszFineDivisorRows.lower N pb.1 pb.2 := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = _ := by push_cast; rfl
  unfold boundary
  exact min_eq_left (by exact_mod_cast hU.trans hpow)

/-- The dyadic grid on one canonical row. -/
def rowBoundary (_u : ℝ) (N i : ℕ) (pb : ℕ×ℕ) : ℕ :=
  boundary (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)
    (ZetaRieszFineDivisorRows.upper N pb.1 pb.2) i

/-- Empty clamped shells are removed exactly, rather than estimated. -/
def shellRows (u : ℝ) (N i : ℕ) : Finset (ℕ×ℕ) :=
  (edgeRows u N).filter (fun pb => rowBoundary u N i pb < rowBoundary u N (i+1) pb)

private theorem shell_geometry {u : ℝ} {N i : ℕ} {pb : ℕ×ℕ}
    (hpb : pb ∈ shellRows u N i) :
    RowGeometry N (ownershipLength N) pb.1 pb.2
      (rowBoundary u N i pb) (rowBoundary u N (i+1) pb) := by
  obtain ⟨hr,hMX⟩ := Finset.mem_filter.mp hpb
  have hlu := (row_data hr).2.2
  apply geometry_subinterval (edge_row_geometry hr) _ _ hMX
  · exact lower_le_boundary hlu i
  · exact min_le_left _ _

set_option maxHeartbeats 800000 in
private theorem shell_large {u : ℝ} {N i : ℕ} {pb : ℕ×ℕ}
    (hpb : pb ∈ shellRows u N i) : exp ((N : ℝ)/2000) ≤ rowBoundary u N i pb := by
  have hr := (Finset.mem_filter.mp hpb).1
  have hlu := (row_data hr).2.2
  exact (row_large hr).trans
    (by exact_mod_cast lower_le_boundary hlu i)

private theorem coreRow_empty (u y : ℝ) (j p b M : ℕ) : coreRow u y j p b M M=0 := by
  simp [coreRow]

private theorem sum_shellRows_eq (u : ℝ) (N : ℕ)
    (F : (ℕ×ℕ) → ℕ → ℕ → ℝ) (hzero : ∀ pb M, F pb M M=0) :
    (∑ i ∈ Finset.range (N+1), ∑ pb ∈ shellRows u N i,
      F pb (rowBoundary u N i pb) (rowBoundary u N (i+1) pb)) =
        ∑ pb ∈ edgeRows u N, ∑ i ∈ Finset.range (N+1),
          F pb (rowBoundary u N i pb) (rowBoundary u N (i+1) pb) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro pb _ hnot
  have hz : rowBoundary u N i pb=rowBoundary u N (i+1) pb := by
    apply le_antisymm (boundary_mono _ _ (Nat.le_succ i))
    exact le_of_not_gt (fun h => hnot (Finset.mem_filter.mpr ⟨by assumption,h⟩))
  rw [hz,hzero]

/-- All core row atoms are reassembled exactly after the error has been
paid shellwise. Original phases, masks and count cutoff stay inside. -/
private theorem sum_coreRow_shells (u y : ℝ) (j : ℕ)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    (∑ i ∈ Finset.range (dyadicMomentOrder j+1),
      ∑ pb ∈ shellRows u (dyadicMomentOrder j) i,
        coreRow u y j pb.1 pb.2
          (rowBoundary u (dyadicMomentOrder j) i pb)
          (rowBoundary u (dyadicMomentOrder j) (i+1) pb)) =
      ∑ pb ∈ edgeRows u (dyadicMomentOrder j),
        coreRow u y j pb.1 pb.2 (ZetaRieszFineDivisorRows.lower (dyadicMomentOrder j) pb.1 pb.2)
          (ZetaRieszFineDivisorRows.upper (dyadicMomentOrder j) pb.1 pb.2) := by
  rw [sum_shellRows_eq _ _ _ (fun pb M => coreRow_empty u y j pb.1 pb.2 M)]
  apply Finset.sum_congr rfl
  intro pb hpb
  have hlu := (row_data hpb).2.2
  unfold coreRow
  dsimp only
  change (∑ i ∈ Finset.range (dyadicMomentOrder j+1),
    ∑ d ∈ Finset.Ioc (rowBoundary _ _ i _) (rowBoundary _ _ (i+1) _), _) = _
  simp only [rowBoundary]
  rw [sum_boundary_shells _ _ _ _ hlu,last_boundary hpb hL]

/-- The SIGNED density rows are likewise recombined before any main-term
estimate. No norm, positive part or separate prime-count cost is inserted. -/
private theorem sum_densityRow_shells (u y : ℝ) (N : ℕ)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    (∑ i ∈ Finset.range (N+1), ∑ pb ∈ shellRows u N i,
      densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
        (rowBoundary u N i pb) (rowBoundary u N (i+1) pb)) =
      ∑ pb ∈ edgeRows u N,
        densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
          (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) (ZetaRieszFineDivisorRows.upper N pb.1 pb.2) := by
  rw [sum_shellRows_eq _ _ _ (fun pb M => densityRow_empty _ _ _ pb.1 pb.2 M)]
  apply Finset.sum_congr rfl
  intro pb hpb
  have hlu := (row_data hpb).2.2
  simp only [densityRow_interval,← Finset.mul_sum]
  simp only [rowBoundary]
  rw [sum_boundary_shells _ _ _ _ hlu,last_boundary hpb hL]

private theorem overflow_shells_bound {ι : Type*} (I : Finset ι)
    (B : ι → Finset (ℕ×ℕ)) (M X : ι → ℕ×ℕ → ℕ)
    (j : ℕ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hI : I.card ≤ dyadicMomentOrder j+1)
    (hg : ∀ i ∈ I, ∀ pb ∈ B i, RowGeometry (dyadicMomentOrder j)
      (ownershipLength (dyadicMomentOrder j)) pb.1 pb.2 (M i pb) (X i pb))
    (hcount : exp (2*(dyadicPrimeCount j : ℝ)*ZetaRieszPrimeCountMass.countMass (101/100)) ≤
      (101/100 : ℝ)^(dyadicMomentOrder j)) :
    |u^(dyadicMomentOrder j+1)*∑ i ∈ I, ∑ pb ∈ B i,
      overflowRow u y j pb.1 pb.2 (M i pb) (X i pb)| ≤
      highCountConstant*((dyadicMomentOrder j : ℝ)+1)^2*(49/50 : ℝ)^(dyadicMomentOrder j) := by
  let N := dyadicMomentOrder j
  let C := highCountConstant*(N : ℝ)*(97/100 : ℝ)^N*
    exp (2*(dyadicPrimeCount j : ℝ)*ZetaRieszPrimeCountMass.countMass (101/100))
  have hC : 0 ≤ C := by dsimp [C]; positivity [highCountConstant_nonneg]
  calc
    _ ≤ ∑ i ∈ I, |u^(N+1)*∑ pb ∈ B i,
        overflowRow u y j pb.1 pb.2 (M i pb) (X i pb)| := by
      rw [Finset.mul_sum]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ I, C := Finset.sum_le_sum (fun i hi =>
      overflowRows_bound_of_geometry (B i) (M i) (X i) j hu hU y
        (ownershipLength N) hL (hg i hi))
    _ = (I.card : ℝ)*C := by simp
    _ ≤ ((N : ℝ)+1)*C := mul_le_mul_of_nonneg_right (by exact_mod_cast hI) hC
    _ ≤ highCountConstant*((N : ℝ)+1)^2*
        ((97/100 : ℝ)^N*(101/100 : ℝ)^N) := by
      have hp := mul_le_mul_of_nonneg_left hcount
        (by positivity [highCountConstant_nonneg] :
          0 ≤ ((N : ℝ)+1)*highCountConstant*N*(97/100 : ℝ)^N)
      have hn : ((N : ℝ)+1)*N ≤ ((N : ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
      have hpoly := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn highCountConstant_nonneg)
        (by positivity : 0 ≤ (97/100 : ℝ)^N*(101/100 : ℝ)^N)
      dsimp [C]
      nlinarith only [hp,hpoly]
    _ ≤ _ := by
      rw [← mul_pow]
      gcongr
      all_goals first | positivity [highCountConstant_nonneg] | norm_num

/-- Literal signed original core incidences of the finer outer band. -/
def edgeLiteralRows (u y : ℝ) (j : ℕ) : ℝ :=
  ∑ pb ∈ edgeRows u (dyadicMomentOrder j),
    coreRow u y j pb.1 pb.2 (ZetaRieszFineDivisorRows.lower (dyadicMomentOrder j) pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper (dyadicMomentOrder j) pb.1 pb.2)

set_option maxHeartbeats 1200000 in
/-- An INDEPENDENT signed bound for the ORIGINAL fine-threshold row
population, across all counts and radial positions together. No zero,
prime-density approximation or unproved cancellation premise enters. -/
theorem eventually_abs_edgeLiteralRows_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop,
      |u^(dyadicMomentOrder j+1)*edgeLiteralRows u y j| ≤
        edgeRowBudget y (dyadicMomentOrder j) := by
  let I := fun j => Finset.range (dyadicMomentOrder j+1)
  let B := fun j i => shellRows u (dyadicMomentOrder j) i
  let M := fun j i => rowBoundary u (dyadicMomentOrder j) i
  let X := fun j i => rowBoundary u (dyadicMomentOrder j) (i+1)
  have hgeo j i (_hi : i ∈ I j) pb (hpb : pb ∈ B j i) :
      RowGeometry (dyadicMomentOrder j) (ownershipLength (dyadicMomentOrder j))
        pb.1 pb.2 (M j i pb) (X j i pb) := shell_geometry hpb
  have hpA j i (_hi : i ∈ I j) pb (hpb : pb ∈ B j i) :
      pb.1 ∈ ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) :=
    row_owner_mem (Finset.mem_filter.mp hpb).1
  have hI j : (I j).card ≤ dyadicMomentOrder j+1 := by simp [I]
  have hcExp := ZetaRieszPrimeCountMass.eventually_exp_count_le_geometric
    (2*ZetaRieszPrimeCountMass.countMass (101/100)) (by norm_num : (1 : ℝ)<101/100)
  have hl := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [hcExp,tendsto_dyadicMomentOrder.eventually hl,
    eventually_ge_atTop (32 : ℕ),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (32 : ℕ))]
    with j hcExp hlength hj hN
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  have hL : (11/8 : ℝ)*N ≤ L := by change _ ≤ L at hlength; nlinarith only [hlength]
  have hcount := overflow_shells_bound (I j) (B j) (M j) (X j) j
    (by linarith : 0 ≤ u) hU y hL (hI j) (hgeo j)
    (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hcExp)
  have hL0 : 0 < L := by
    have hn : (32 : ℝ)≤N := by exact_mod_cast hN
    linarith
  have hlog i (hi : i ∈ I j) pb (hpb : pb ∈ B j i) :
      log (pb.1*pb.2 : ℕ) ≤ (203/100 : ℝ)*N := by
    have hg := hgeo j i hi pb hpb
    have hh := hg.2.2.2.2.2.2.2.2.1
    change _ ≤ (203/100 : ℝ)*N at hh
    linarith [log_natCast_nonneg (X j i pb)]
  have hPL i (hi : i ∈ I j) pb (hpb : pb ∈ B j i) : log pb.1 ≤ L := by
    have hP := (Finset.mem_filter.mp (Finset.mem_filter.mp hpb).1).2.2.2.2.2.2.1
    change _ < (243/200 : ℝ)*N at hP
    have hn := Nat.cast_nonneg (α := ℝ) N
    linarith
  have hT i (hi : i ∈ I j) pb (hpb : pb ∈ B j i) d
      (hd : d ∈ Finset.Icc (M j i pb+1) (X j i pb)) :
      1 ≤ log (pb.1*pb.2 : ℕ)+log d := by
    have hg := hgeo j i hi pb hpb
    have hm : 0 < M j i pb := hg.2.2.2.2.2.2.1
    have hmd : M j i pb ≤ d := by have := Finset.mem_Icc.mp hd; omega
    have hdlog := log_le_log (by exact_mod_cast hm : (0 : ℝ)<M j i pb)
      (by exact_mod_cast hmd : (M j i pb : ℝ)≤d)
    have hlo := hg.2.2.2.2.2.2.2.1
    change (39/20 : ℝ)*N ≤ _ at hlo
    have hn : (32 : ℝ)≤N := by exact_mod_cast hN
    linarith
  have herr := source_scaled_edge_shells_error (I j) (B j) hN (M j) (X j) hL0
    (by linarith : 0 ≤ u) hU y (hI j)
    (fun i hi pb hpb => ⟨(hgeo j i hi pb hpb).1,
      (hgeo j i hi pb hpb).2.2.1,(hgeo j i hi pb hpb).2.2.2.1⟩)
    hlog (fun i hi pb hpb => (hgeo j i hi pb hpb).2.2.2.2.2.2.1)
    (fun _ _ _ hpb => (Finset.mem_filter.mp hpb).2)
    (fun i _ pb _ => boundary_le_twice _ _ i)
    (fun _ _ _ hpb => shell_large hpb) hPL hT
  have hsum : (∑ i ∈ I j, ∑ pb ∈ B j i,
      coreRow u y j pb.1 pb.2 (M j i pb) (X j i pb)) =
      (∑ i ∈ I j, ∑ pb ∈ B j i, densityRow N L y pb.1 pb.2 (M j i pb) (X j i pb))+
      (∑ i ∈ I j, ∑ pb ∈ B j i, ownedShellDiscrepancy N L y pb.1 pb.2 (M j i pb) (X j i pb))-
      (∑ i ∈ I j, ∑ pb ∈ B j i, overflowRow u y j pb.1 pb.2 (M j i pb) (X j i pb)) := by
    simp only [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro pb hpb
    have h := coreRow_add_overflow_of_geometry (y := y) j hj hu hU hL (hgeo j i hi pb hpb) (hpA j i hi pb hpb)
    change _+_=densityRow N L y _ _ _ _+ownedShellDiscrepancy N L y _ _ _ _ at h
    linarith
  have hm := source_scaled_edgeDensityMain_bound (by linarith : 0 ≤ u) hU hN hL hy
  change |u^(N+1)*edgeLiteralRows u y j| ≤ edgeRowBudget y N
  rw [edgeLiteralRows,← sum_coreRow_shells u y j hL]
  change |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i, coreRow u y j pb.1 pb.2 (M j i pb) (X j i pb))| ≤ _
  rw [hsum,mul_sub,mul_add]
  have hmain : |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i,
      densityRow N L y pb.1 pb.2 (M j i pb) (X j i pb))| ≤ fineMainBudget y N := by
    simpa only [I,B,M,X,N,L,sum_densityRow_shells u y (dyadicMomentOrder j) hL,
      edgeDensityMain] using hm
  calc
    _ ≤ |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i,
          densityRow N L y pb.1 pb.2 (M j i pb) (X j i pb))|+
        |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i,
          ownedShellDiscrepancy N L y pb.1 pb.2 (M j i pb) (X j i pb))|+
        |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i,
          overflowRow u y j pb.1 pb.2 (M j i pb) (X j i pb))| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ fineMainBudget y N+
        edgeErrorConstant*(8+|y|)*((N : ℝ)+1)^3*comparisonRate^N+
        highCountConstant*((N : ℝ)+1)^2*(49/50 : ℝ)^N :=
      add_le_add (add_le_add hmain herr) hcount
    _ = edgeRowBudget y N := rfl

/-- Concrete source-o(1) saving for the ORIGINAL retained signed
prime-incidence sum on the enlarged population. -/
theorem tendsto_edgeLiteralRows {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*edgeLiteralRows u y j) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun j => edgeRowBudget y (dyadicMomentOrder j)) ?_
    ((tendsto_edgeRowBudget y).comp tendsto_dyadicMomentOrder)
  simpa only [Real.norm_eq_abs] using eventually_abs_edgeLiteralRows_bound hu hU hy



private theorem endpoint_cofactor {u : ℝ} {N : ℕ} (hN : 32 ≤ N) {pb : ℕ×ℕ}
    (hpb : pb ∈ edgeRows u N)
    (hsieve : sieve (pb.1*pb.2).primeFactors (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) ≠ 0) :
    Squarefree (pb.2*ZetaRieszFineDivisorRows.lower N pb.1 pb.2) ∧
      2 ≤ (pb.2*ZetaRieszFineDivisorRows.lower N pb.1 pb.2).primeFactors.card ∧
      ∀ q ∈ (pb.2*ZetaRieszFineDivisorRows.lower N pb.1 pb.2).primeFactors, q < pb.1 := by
  have hg := edge_row_geometry hpb
  obtain ⟨hp,hb,hbs,hpd,hmax,ha,hM,_,_,hsat,_⟩ := hg
  have houter : Squarefree (pb.1*pb.2) :=
    Nat.squarefree_mul_iff.mpr ⟨hp.coprime_iff_not_dvd.mpr hpd,hp.squarefree,hbs⟩
  have hwhole : Squarefree ((pb.1*pb.2)*ZetaRieszFineDivisorRows.lower N pb.1 pb.2) := by
    rw [sieve_eq_product_squarefree houter] at hsieve
    split_ifs at hsieve with h
    · exact h
    · contradiction
  have hc : Squarefree (pb.2*ZetaRieszFineDivisorRows.lower N pb.1 pb.2) := by
    rw [mul_assoc] at hwhole
    exact (Nat.squarefree_mul_iff.mp hwhole).2.2
  have hd1 : 1 < ZetaRieszFineDivisorRows.lower N pb.1 pb.2 := by
    have h := row_large hpb
    have he := add_one_le_exp ((N : ℝ)/2000)
    have hnr : (32 : ℝ) ≤ N := by exact_mod_cast hN
    have hr : (1 : ℝ)<ZetaRieszFineDivisorRows.lower N pb.1 pb.2 := by linarith
    exact_mod_cast hr
  have hdmax : ZetaRieszFineDivisorRows.lower N pb.1 pb.2 < pb.1 := by
    have hlog : log (pb.2*ZetaRieszFineDivisorRows.lower N pb.1 pb.2 : ℕ) ≤ ownershipLength N := by
      rw [Nat.cast_mul,log_mul (by exact_mod_cast (by omega : 0 < pb.2).ne')
        (by exact_mod_cast hM.ne')]
      have hmu := (row_data hpb).2.2
      have hm : log (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) ≤
          log (ZetaRieszFineDivisorRows.upper N pb.1 pb.2) :=
        log_le_log (by exact_mod_cast hM : (0 : ℝ)<ZetaRieszFineDivisorRows.lower N pb.1 pb.2)
        (by exact_mod_cast hmu)
      linarith
    exact active_unsigned_lt_owner hp.pos (by omega) hM hlog ha
  have hdis : Disjoint pb.2.primeFactors (ZetaRieszFineDivisorRows.lower N pb.1 pb.2).primeFactors := by
    apply Finset.disjoint_left.mpr
    intro q hq hqd
    have hqp := Nat.prime_of_mem_primeFactors hq
    exact (hqp.coprime_iff_not_dvd.mp
      ((Nat.squarefree_mul_iff.mp hc).1.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hq)))
        (Nat.dvd_of_mem_primeFactors hqd)
  refine ⟨hc,?_,?_⟩
  · rw [Nat.primeFactors_mul (by omega) hM.ne',Finset.card_union_of_disjoint hdis]
    have hbcard := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hb)
    have hdcard := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hd1)
    omega
  · intro q hq
    rw [Nat.primeFactors_mul (by omega) hM.ne',Finset.mem_union] at hq
    exact hq.elim (hmax q) (fun h => (Nat.le_of_dvd hM (Nat.dvd_of_mem_primeFactors h)).trans_lt hdmax)

private theorem endpoint_atom_bound {u : ℝ} {N : ℕ} (hN : 32 ≤ N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    {pb : ℕ×ℕ} (hpb : pb ∈ edgeRows u N) (y : ℝ) :
    |rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u N) N
      (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2 (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)| ≤
        radialEnvelope N*exp (-(N : ℝ)/2000)/(pb.1*pb.2 : ℕ) := by
  have hg := edge_row_geometry hpb
  let d := ZetaRieszFineDivisorRows.lower N pb.1 pb.2
  let L := SquarefreeVaughanLogSource.length u N
  change |rowAtom _ N L y pb.1 pb.2 d| ≤ _
  have hd0 : 0 < d := Nat.ceil_pos.mpr (exp_pos _)
  have hb0 : 0 < pb.2 := by have := hg.2.1; omega
  have hpb0 : (0 : ℝ)<(pb.1*pb.2 : ℕ) := by exact_mod_cast Nat.mul_pos hg.1.pos hb0
  have hnr : (32 : ℝ) ≤ N := by exact_mod_cast hN
  have hL0 : 0 < L := by dsimp [L]; nlinarith
  have hP : log pb.1 ≤ L := by
    have hp := (row_data hpb).2.1
    dsimp [L]
    nlinarith
  by_cases hz : sieve (pb.1*pb.2).primeFactors d=0
  · simp only [rowAtom,hz,mul_zero,abs_zero]
    positivity [radialEnvelope_pos N]
  have hco := endpoint_cofactor hN hpb hz
  have houter : Squarefree (pb.1*pb.2) := Nat.squarefree_mul_iff.mpr
    ⟨hg.1.coprime_iff_not_dvd.mpr hg.2.2.2.1,hg.1.squarefree,hg.2.2.1⟩
  have hsieve : sieve (pb.1*pb.2).primeFactors d=1 := by
    rw [sieve_eq_product_squarefree houter] at hz ⊢
    by_cases hs : Squarefree ((pb.1*pb.2)*d)
    · simp only [if_pos hs]
    · simp only [if_neg hs,not_true_eq_false] at hz
  have hT : 1 ≤ log (pb.1*pb.2 : ℕ)+log d := by
    have hlo := hg.2.2.2.2.2.2.2.1
    change (39/20 : ℝ)*N ≤ log (pb.1*pb.2 : ℕ)+log d at hlo
    linarith
  have hPT : log pb.1 ≤ log (pb.1*pb.2 : ℕ)+log d := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hg.1.ne_zero) (by exact_mod_cast hb0.ne')]
    linarith [log_natCast_nonneg pb.2,log_natCast_nonneg d]
  have hamp := ownedAmplitude_bound N (log_natCast_nonneg pb.1) hT hPT
  have hh := pairHinge_bounds L pb.1 pb.2
  have hm : |(μ pb.2 : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := pb.2)
  rw [rowAtom,owner_phase_eq_amplitude (ZetaRieszAnnulusJoint.intermediatePrimes u N) N L y
    hg.1 hb0 hd0 hco.1 hco.2.1 hco.2.2
    (row_owner_mem hpb),hsieve,mul_one,abs_mul,abs_mul,abs_div,abs_mul,
    abs_of_pos (by positivity : 0 < L*(pb.1*pb.2 : ℕ)*d),abs_of_nonneg hh.1]
  have hc := abs_cos_le_one (y*(log (pb.1*pb.2 : ℕ)+log d))
  have hR := radialEnvelope_pos N
  have hnum : |ownedAmplitude N (log pb.1) (log (pb.1*pb.2 : ℕ)) d|
      *|cos (y*(log (pb.1*pb.2 : ℕ)+log d))| * |(μ pb.2 : ℝ)| * pairHinge L pb.1 pb.2 ≤
      radialEnvelope N*L := by
    have h1 := mul_le_mul hamp hc (abs_nonneg _) (radialEnvelope_pos N).le
    have h2 := mul_le_mul h1 hm (abs_nonneg _) (by positivity : 0 ≤ radialEnvelope N*1)
    exact (mul_le_mul h2 (hh.2.trans hP) hh.1 (by positivity : 0 ≤ radialEnvelope N*1*1)).trans_eq
      (by ring)
  have hdlarge := row_large hpb
  have hinv : (d : ℝ)⁻¹ ≤ exp (-(N : ℝ)/2000) := by
    rw [neg_div,exp_neg]
    exact inv_anti₀ (exp_pos _) hdlarge
  calc
    _ = (|ownedAmplitude N (log pb.1) (log (pb.1*pb.2 : ℕ)) d|
        *|cos (y*(log (pb.1*pb.2 : ℕ)+log d))| * |(μ pb.2 : ℝ)| * pairHinge L pb.1 pb.2)/
          (L*(pb.1*pb.2 : ℕ)*d) := by ring
    _ ≤ radialEnvelope N*L/(L*(pb.1*pb.2 : ℕ)*d) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = radialEnvelope N/(pb.1*pb.2 : ℕ)*(d : ℝ)⁻¹ := by field_simp
    _ ≤ radialEnvelope N/(pb.1*pb.2 : ℕ)*exp (-(N : ℝ)/2000) :=
      mul_le_mul_of_nonneg_left hinv (by positivity [radialEnvelope_pos N])
    _ = _ := by ring



/-- The original core-masked rounded endpoint of each new row. -/
def edgeEndpointRows (u y : ℝ) (j : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  ∑ pb ∈ edgeRows u N,
    if pb.1*(pb.2*ZetaRieszFineDivisorRows.lower N pb.1 pb.2) ∈ ZetaRieszParityPacket.coreBand u N (dyadicPrimeCount j)
      then rowAtom A N L y pb.1 pb.2 (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) else 0


theorem source_scaled_edgeEndpointRows_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (j : ℕ)
    (hN : 32 ≤ dyadicMomentOrder j)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    |u^(dyadicMomentOrder j+1)*edgeEndpointRows u y j| ≤
      edgeEndpointBudget (dyadicMomentOrder j) := by
  let N := dyadicMomentOrder j
  have hsum : |edgeEndpointRows u y j| ≤
      radialEnvelope N*exp (-(N : ℝ)/2000)*(1+(203/100 : ℝ)*N)^2 := by
    unfold edgeEndpointRows
    dsimp only
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ pb ∈ edgeRows u N,
          radialEnvelope N*exp (-(N : ℝ)/2000)/(pb.1*pb.2 : ℕ) := by
        apply Finset.sum_le_sum
        intro pb hpb
        split_ifs
        · exact endpoint_atom_bound hN hL hpb y
        · simp only [abs_zero]
          positivity [radialEnvelope_pos N]
      _ = radialEnvelope N*exp (-(N : ℝ)/2000)*
          (∑ pb ∈ edgeRows u N, (1 : ℝ)/(pb.1*pb.2 : ℕ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro pb _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (outer_harmonic_bound u N)
        (by positivity [radialEnvelope_pos N])
  have h2u : 2*u ≤ exp (1/10000 : ℝ) := by
    have he := add_one_le_exp (1/10000 : ℝ)
    have huU : u ≤ (10001/20000 : ℝ) := hU
    linarith
  have hr : (2*u)^N*exp (-(N : ℝ)/2000) ≤ edgeEndpointRate^N := by
    calc
      _ ≤ (exp (1/10000 : ℝ))^N*exp (-(N : ℝ)/2000) := by gcongr
      _ = exp (-(1/2500 : ℝ))^N := by
        rw [← exp_nat_mul,← exp_add,← exp_nat_mul]
        congr 1
        ring
      _ = _ := rfl
  have hp : (1+(203/100 : ℝ)*N)^2 ≤ 9*((N : ℝ)+1)^2 := by
    have hh : 1+(203/100 : ℝ)*N ≤ 3*((N : ℝ)+1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    exact (pow_le_pow_left₀ (by positivity) hh 2).trans_eq (by ring)
  have hf : 2*u*((N : ℝ)+1) ≤ 2*((N : ℝ)+1) := by
    have huU : u ≤ (10001/20000 : ℝ) := hU
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  rw [abs_mul,abs_of_nonneg (pow_nonneg hu _)]
  apply (mul_le_mul_of_nonneg_left hsum (pow_nonneg hu _)).trans
  have heq : u^(N+1)*(radialEnvelope N*exp (-(N : ℝ)/2000)*
      (1+(203/100 : ℝ)*N)^2) =
      (2*u*((N : ℝ)+1))*((2*u)^N*exp (-(N : ℝ)/2000))*
        (1+(203/100 : ℝ)*N)^2 := by
    unfold radialEnvelope
    rw [pow_succ,pow_succ,mul_pow]
    ring
  rw [heq]
  have hh := mul_le_mul
    (mul_le_mul hf hr (by positivity) (by positivity)) hp
    (sq_nonneg _) (by positivity [edgeEndpointRate_bounds.1])
  convert hh using 1
  unfold edgeEndpointBudget
  ring

/-- The new endpoint payment tends to zero at source scale. -/
theorem tendsto_edgeEndpointRows {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*edgeEndpointRows u y j) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun j => edgeEndpointBudget (dyadicMomentOrder j)) ?_
    (tendsto_edgeEndpointBudget.comp tendsto_dyadicMomentOrder)
  filter_upwards [tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (32 : ℕ)),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
        (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source))] with j hN hL
  have hL' : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by nlinarith only [hL]
  simpa only [Real.norm_eq_abs] using
    source_scaled_edgeEndpointRows_bound (by linarith : 0 ≤ u) hU y j hN hL'


/-- No original integer endpoint is dropped by the closed row identity. -/
theorem edge_rows_closed_eq (u y : ℝ) (j : ℕ) :
    (∑ pb ∈ edgeRows u (dyadicMomentOrder j),
      ∑ d ∈ Finset.Icc (ZetaRieszFineDivisorRows.lower (dyadicMomentOrder j) pb.1 pb.2)
        (ZetaRieszFineDivisorRows.upper (dyadicMomentOrder j) pb.1 pb.2),
        if pb.1*(pb.2*d) ∈ ZetaRieszParityPacket.coreBand u
            (dyadicMomentOrder j) (dyadicPrimeCount j)
          then rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
            (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
            y pb.1 pb.2 d else 0) = edgeLiteralRows u y j+edgeEndpointRows u y j := by
  simp only [edgeLiteralRows,edgeEndpointRows,coreRow]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pb hpb
  have hlu := (Finset.mem_filter.mp hpb).2.2.2.2.2.2.2.2
  have he : Finset.Icc (ZetaRieszFineDivisorRows.lower (dyadicMomentOrder j) pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper (dyadicMomentOrder j) pb.1 pb.2) =
      insert (ZetaRieszFineDivisorRows.lower (dyadicMomentOrder j) pb.1 pb.2)
        (Finset.Ioc (ZetaRieszFineDivisorRows.lower (dyadicMomentOrder j) pb.1 pb.2)
          (ZetaRieszFineDivisorRows.upper (dyadicMomentOrder j) pb.1 pb.2)) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_insert,Finset.mem_Ioc]
    omega
  rw [he,Finset.sum_insert (by simp)]
  ring


theorem edge_literal_row_covered {u : ℝ} {N p b d : ℕ}
    (hp : p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N)
    (hb : 1 < b) (hs : Squarefree b) (hpd : ¬p ∣ b)
    (hmax : ∀ q ∈ b.primeFactors, q < p)
    (ha : pairHinge (SquarefreeVaughanLogSource.length u N) p b ≠ 0)
    (hc : log (p*b : ℕ) ≤ (3899/2000 : ℝ)*N)
    (hP : log p < (243/200 : ℝ)*N)
    (hOld : (1949/1000 : ℝ)*N < log (p*b : ℕ))
    (hPl : (N : ℝ)/2 ≤ log p)
    (hcl : ownershipLength N < log (p*b : ℕ))
    (hlo : (39/20 : ℝ)*N < log (p*b : ℕ)+log d)
    (hhi : log (p*b : ℕ)+log d ≤ (203/100 : ℝ)*N) :
    (p,b) ∈ edgeRows u N ∧ d ∈ Finset.Icc (ZetaRieszFineDivisorRows.lower N p b) (ZetaRieszFineDivisorRows.upper N p b) := by
  have hpP := ((ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp hp).1
  have hb0 : 0 < b := by omega
  have hd0 : 0 < d := by
    by_contra hn
    have hd : d=0 := by omega
    rw [hd,Nat.cast_zero,log_zero,add_zero] at hlo
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hdl : ZetaRieszFineDivisorRows.lower N p b ≤ d := by
    apply Nat.ceil_le.mpr
    have hh := exp_le_exp.mpr (by linarith : (39/20 : ℝ)*N-log (p*b : ℕ) ≤ log d)
    simpa only [exp_log (by exact_mod_cast hd0 : (0 : ℝ)<d)] using hh
  have hdu : d ≤ ZetaRieszFineDivisorRows.upper N p b := by
    apply Nat.le_floor
    have hh := exp_le_exp.mpr (by linarith : log d ≤ (203/100 : ℝ)*N-log (p*b : ℕ))
    simpa only [exp_log (by exact_mod_cast hd0 : (0 : ℝ)<d)] using hh
  have hlog : log (p*b : ℕ)=log p+log b := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hpP.ne_zero) (by exact_mod_cast hb0.ne')]
  have hbB : b ≤ ⌊exp ((203/100 : ℝ)*N)⌋₊ := by
    apply Nat.le_floor
    have hhlog : log b ≤ (203/100 : ℝ)*N := by
      rw [hlog] at hhi
      linarith [log_natCast_nonneg p,log_natCast_nonneg d]
    have hh := exp_le_exp.mpr hhlog
    simpa only [exp_log (by exact_mod_cast hb0 : (0 : ℝ)<b)] using hh
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨hp,Finset.mem_Icc.mpr ⟨by omega,hbB⟩⟩,hs,hpd,hmax,ha,hc,hP,hOld,hPl,hcl,
      hdl.trans hdu⟩,Finset.mem_Icc.mpr ⟨hdl,hdu⟩⟩


/-- The whole closed original finer-band population is independently
source-o(1), including every rounded endpoint and every prime count. -/
theorem tendsto_edgeClosedRows {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*
      (edgeLiteralRows u y j+edgeEndpointRows u y j)) atTop (𝓝 0) := by
  simpa only [mul_add,zero_add] using
    (tendsto_edgeLiteralRows hu hU hy).add (tendsto_edgeEndpointRows hu hU y)


/-- Closed new incidences cannot spend either earlier divisor-row credit.
The label may be shared; the divisor incidence is what is disjoint. -/
theorem edge_closed_incidence_ne_old {u : ℝ} {N : ℕ} {pb pc : ℕ×ℕ}
    (hpb : pb ∈ edgeRows u N)
    (hpc : pc ∈ fineRows u N ∪ ZetaRieszOwnerSafeRows.ownerSafeRows u N) {d e : ℕ}
    (hd : d ∈ Finset.Icc (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper N pb.1 pb.2)) :
    (pb.1*(pb.2*d),(d,pb.2)) ≠ (pc.1*(pc.2*e),(e,pc.2)) := by
  intro he
  have hsecond : (d,pb.2)=(e,pc.2) := congrArg (fun v : ℕ×(ℕ×ℕ) => v.2) he
  have he' : d=e := congrArg Prod.fst hsecond
  have hb : pb.2=pc.2 := by
    simpa only using congrArg (fun v : ℕ×ℕ => v.2) hsecond
  have hn : pb.1*(pb.2*d)=pc.1*(pc.2*e) :=
    congrArg (fun v : ℕ×(ℕ×ℕ) => v.1) he
  rw [← he',← hb] at hn
  have hd0 : 0 < d :=
    (Nat.ceil_pos.mpr (exp_pos _) : 0 < ZetaRieszFineDivisorRows.lower N pb.1 pb.2).trans_le
      (Finset.mem_Icc.mp hd).1
  have hb0 : 0 < pb.2 := by have := (edge_row_geometry hpb).2.1; omega
  have hp : pb.1=pc.1 := Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hb0 hd0) hn
  have hpair : pb=pc := Prod.ext hp hb
  obtain ⟨_,_,_,_,_,_,_,hOld,_,_,_⟩ := Finset.mem_filter.mp hpb
  have hcut : log (pc.1*pc.2 : ℕ) ≤ (1949/1000 : ℝ)*N := by
    rcases Finset.mem_union.mp hpc with hold | hold
    · obtain ⟨_,_,_,_,_,hc,_,_,_⟩ := Finset.mem_filter.mp hold
      exact hc
    · obtain ⟨_,_,_,_,_,hc,_,_,_,_,_⟩ := Finset.mem_filter.mp hold
      exact hc
  rw [hpair] at hOld
  exact (not_lt_of_ge hcut) hOld

/-- The original unsigned unit remains unselected even at the rounded
endpoint of this finer band. -/
theorem edge_unsigned_gt_one {u : ℝ} {N : ℕ} (hN : 0 < N) {pb : ℕ×ℕ}
    (hpb : pb ∈ edgeRows u N) {d : ℕ}
    (hd : d ∈ Finset.Icc (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper N pb.1 pb.2)) : 1 < d := by
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have hle : (ZetaRieszFineDivisorRows.lower N pb.1 pb.2 : ℝ) ≤ d := by
    exact_mod_cast (Finset.mem_Icc.mp hd).1
  have h : (1 : ℝ)<d := (one_lt_exp_iff.mpr (by linarith : (0 : ℝ)<N/2000)).trans_le
    ((row_large hpb).trans hle)
  exact_mod_cast h

/-- The new closed-row credit is disjoint from the already paid WHOLE
large-owner labels, with their actual singleton allocation. -/
theorem edge_closed_label_not_largeOwner {u : ℝ} {N K : ℕ} (hN : 0 < N)
    {pb : ℕ×ℕ} (hpb : pb ∈ edgeRows u N) {d : ℕ}
    (hd : d ∈ Finset.Icc (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper N pb.1 pb.2))
    (hs : sieve (pb.1*pb.2).primeFactors d ≠ 0) :
    pb.1*(pb.2*d) ∉ largeOwnerLabels u N K := by
  intro hn
  have hg := edge_row_geometry hpb
  have hc := closed_row_cofactor_geometry hg hd (edge_unsigned_gt_one hN hpb hd) hs
  have ho := ZetaRieszPrimeIntervals.largestPrime_mul pb.1 (pb.2*d) hg.1 hc.1.ne_zero hc.2.2
  have hP := (row_data hpb).2.1
  have hhigh := (Finset.mem_filter.mp hn).2.2.2.2.1
  rw [ho] at hhigh
  linarith

/-- The SAME retained signed scalar after the new disjoint literal rows
are removed. No positive allowance or new carrier completion is used. -/
def edgeRemaining (u y : ℝ) (j : ℕ) : ℝ :=
  unifiedRemaining u y j-(edgeLiteralRows u y j+edgeEndpointRows u y j)

/-- Shared errors once, and the two new independently paid costs once. -/
def edgeErrorBudget (y : ℝ) (N : ℕ) : ℝ :=
  unifiedErrorBudget y N+edgeRowBudget y N+edgeEndpointBudget N

theorem tendsto_edgeErrorBudget (y : ℝ) :
    Tendsto (edgeErrorBudget y) atTop (𝓝 0) := by
  change Tendsto (fun N => unifiedErrorBudget y N+edgeRowBudget y N+edgeEndpointBudget N)
    atTop (𝓝 0)
  simpa only [zero_add] using
    ((tendsto_unifiedErrorBudget y).add (tendsto_edgeRowBudget y)).add tendsto_edgeEndpointBudget

/-- An independent source-geometric comparison of the WHOLE joined
real carrier with the remaining signed sum after the actual new payment. -/
theorem eventually_abs_joined_sub_edgeRemaining_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop,
      |u^(dyadicMomentOrder j+1)*
        ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
          edgeRemaining u y j)| ≤ edgeErrorBudget y (dyadicMomentOrder j) := by
  have hl := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [eventually_abs_joined_sub_unifiedRemaining_bound hu hU hy,
    eventually_abs_edgeLiteralRows_bound hu hU hy,
    tendsto_dyadicMomentOrder.eventually hl,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (32 : ℕ))]
    with j hOld hNew hlength hN
  have hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by nlinarith only [hlength]
  have hEnd := source_scaled_edgeEndpointRows_bound (by linarith : 0 ≤ u) hU y j hN hL
  rw [edgeRemaining,show u^(dyadicMomentOrder j+1)*
      ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
        (unifiedRemaining u y j-(edgeLiteralRows u y j+edgeEndpointRows u y j))) =
      u^(dyadicMomentOrder j+1)*
        ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
          unifiedRemaining u y j)+u^(dyadicMomentOrder j+1)*edgeLiteralRows u y j+
        u^(dyadicMomentOrder j+1)*edgeEndpointRows u y j by ring]
  exact (abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add hOld hNew)) hEnd)

/-- No source has been lost in the new independent signed arithmetic
payment. The numerical -79/1000 floor for this rest remains open. -/
theorem tendsto_joined_re_sub_edgeRemaining {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*
      ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
        edgeRemaining u y j)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun j => edgeErrorBudget y (dyadicMomentOrder j)) ?_
    ((tendsto_edgeErrorBudget y).comp tendsto_dyadicMomentOrder)
  simpa only [Real.norm_eq_abs] using eventually_abs_joined_sub_edgeRemaining_bound hu hU hy

/-- An independent one-sided comparison after the finer literal band is
paid. The signed scalar itself is not yet given the numerical floor. -/
theorem eventually_joined_floor_with_edgeRemaining {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop,
      u^(dyadicMomentOrder j+1)*edgeRemaining u y j-
        edgeErrorBudget y (dyadicMomentOrder j) ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_abs_joined_sub_edgeRemaining_bound hu hU hy] with j hj
  have h := (abs_le.mp hj).1
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  nlinarith

end RiemannGaussian.ZetaRieszEdgeDivisorRows
