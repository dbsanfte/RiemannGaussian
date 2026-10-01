/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszShortDivisorOrbits

/-!
# Signed payment for the fixed two-prime short-cutoff crossing

The block is 6=2*3. Its clipped cutoff is independent of the original
unsigned variable. Sum that block first, then retain its frozen signed
multiplier on the entire original row. All masks and phases remain literal.
Only the sieve/count/rounded errors are normed. The numerical global floor
is not asserted.
-/

noncomputable section
open Filter Topology Real MeasureTheory Set
open scoped BigOperators Classical Pointwise ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszShortCutoffRows
open ZetaRieszUnifiedSignedRows ZetaRieszUnsignedDivisorError ZetaRieszSignedConvolution
open ZetaRieszSaturatedRowFloor ZetaRieszOwnerMaximal ZetaRieszFreeRadialRows
open ZetaRieszFineDivisorRows ZetaRieszPrimeCountFrequency
open ZetaRieszEdgeDivisorRows (edgeErrorConstant edgeErrorConstant_nonneg
  edgeRowBudget tendsto_edgeRowBudget)

private theorem cutoff_shell_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {M X : ℕ} (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (N : ℕ) (hlarge : exp ((N : ℝ)/2016) ≤ M)
    (a : ℕ → ℝ) (y c A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ d ∈ Finset.Ioc M X, |a d| ≤ A) :
    let w := ZetaRieszCofactorDiscrepancy.shellWeight M X a y c
    |(∑ d ∈ Finset.Icc 1 X, w d*sieve S d)-
      density S*(∑ d ∈ Finset.Icc 1 X, w d)| ≤
        countingCostAt (17/32)*3^S.card*exp (-15*(N : ℝ)/64512)*
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
    (ZetaRieszCofactorDiscrepancy.shellWeight M X a y c) (1/2016)
    (by simp [ZetaRieszCofactorDiscrepancy.shellWeight])
    (fun k hk hz => by
      have hMk : (M : ℝ) ≤ k := by exact_mod_cast hactive k hk hz
      simpa only [div_mul_eq_mul_div,one_mul] using hlarge.trans hMk)
  have he : -((1-(17/32 : ℝ))*(1/2016 : ℝ)*N)=-15*(N : ℝ)/64512 := by ring
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (ZetaRieszCofactorDiscrepancy.shellWeight_variation hM hMX hXM a y c A hA ha)
    (by positivity : 0 ≤ countingCostAt (17/32)*3^S.card*exp (-15*(N : ℝ)/64512)))

private theorem cutoff_owned_shell_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {N M X : ℕ} (hN : 32 ≤ N) (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (hlarge : exp ((N : ℝ)/2016) ≤ M) {P c : ℝ} (hP : 0 ≤ P)
    (hT : ∀ d ∈ Finset.Icc (M+1) X, 1 ≤ c+log d)
    (hPT : ∀ d ∈ Finset.Icc (M+1) X, P ≤ c+log d) (y : ℝ) :
    let w := ZetaRieszCofactorDiscrepancy.shellWeight M X (ownedAmplitude N P c) y c
    |(∑ d ∈ Finset.Icc 1 X, w d*sieve S d)-
      density S*(∑ d ∈ Finset.Icc 1 X, w d)| ≤
        countingCostAt (17/32)*3^S.card*exp (-15*(N : ℝ)/64512)*
          (((N : ℝ)+7+|y|)*radialEnvelope N) := by
  have hb := cutoff_shell_error S hS hM hMX hXM N hlarge (ownedAmplitude N P c) y c
    (radialEnvelope N) (radialEnvelope_pos N).le
    (fun d hd => ownedAmplitude_bound N hP
      (hT d (Finset.mem_Icc.mpr ⟨by have := Finset.mem_Ioc.mp hd; omega,(Finset.mem_Ioc.mp hd).2⟩))
      (hPT d (Finset.mem_Icc.mpr ⟨by have := Finset.mem_Ioc.mp hd; omega,(Finset.mem_Ioc.mp hd).2⟩)))
  apply hb.trans
  have hC := (countingCostAt_pos (17/32)).le
  have ht := ownedAmplitude_variation hN hM hMX hXM hP hT hPT
  calc
    _ ≤ countingCostAt (17/32)*3^S.card*exp (-15*(N : ℝ)/64512)*
        ((3+|y|)*radialEnvelope N+((N : ℝ)+4)*radialEnvelope N) :=
      mul_le_mul_of_nonneg_left (add_le_add_right ht ((3+|y|)*radialEnvelope N))
        (by positivity)
    _ = _ := by ring

private theorem cutoff_discrepancy_bound {N M X p b : ℕ} (hN : 32 ≤ N)
    (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (hlarge : exp ((N : ℝ)/2016) ≤ M) {L : ℝ} (hL : 0 < L)
    (hp : 0 < p) (hb : 0 < b) (hPL : log p ≤ L)
    (hT : ∀ d ∈ Finset.Icc (M+1) X, 1 ≤ log (p*b : ℕ)+log d)
    (y : ℝ) :
    |ownedShellDiscrepancy N L y p b M X| ≤
      (countingCostAt (17/32)*exp (-15*(N : ℝ)/64512)*
        (((N : ℝ)+7+|y|)*radialEnvelope N))*
          (3^(p*b).primeFactors.card/(p*b : ℕ)) := by
  have hpb : (0 : ℝ)<(p*b : ℕ) := by exact_mod_cast Nat.mul_pos hp hb
  have hlog : log (p*b : ℕ) = log p+log b := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast hb.ne')]
  have hPT d (_ : d ∈ Finset.Icc (M+1) X) : log p ≤ log (p*b : ℕ)+log d := by
    rw [hlog]
    linarith [log_natCast_nonneg b,log_natCast_nonneg d]
  have he := cutoff_owned_shell_error (p*b).primeFactors
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


private def cutoffRate (u : ℝ) : ℝ := 2*u*exp (-((15/64512-203/6553600) : ℝ))

private theorem cutoffRate_bounds {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    0 ≤ cutoffRate u ∧ cutoffRate u ≤ comparisonRate := by
  refine ⟨by unfold cutoffRate; positivity,?_⟩
  have hlog : log (2*ZetaRieszWideOwnerAudit.radiusCeiling) ≤ 1/10000 := by
    have h := log_le_sub_one_of_pos
      (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
        (0 : ℝ)<2*ZetaRieszWideOwnerAudit.radiusCeiling)
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at h ⊢
    exact h
  calc
    cutoffRate u ≤ 2*ZetaRieszWideOwnerAudit.radiusCeiling*exp (-((15/64512-203/6553600) : ℝ)) := by
      unfold cutoffRate; gcongr
    _ = exp (log (2*ZetaRieszWideOwnerAudit.radiusCeiling)-((15/64512-203/6553600) : ℝ)) := by
      rw [exp_sub,exp_log (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]),exp_neg]
      ring
    _ ≤ comparisonRate := by unfold comparisonRate; apply exp_le_exp.mpr; linarith

theorem source_scaled_cutoff_shell_error (B : Finset (ℕ×ℕ)) {N : ℕ} (hN : 32 ≤ N)
    (M X : ℕ×ℕ → ℕ) (κ : ℕ×ℕ → ℝ)
    (hκ : ∀ pb ∈ B, |κ pb| ≤ 4) {L u : ℝ} (hL : 0 < L)
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (hB : ∀ pb ∈ B, pb.1.Prime ∧ Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2)
    (hlog : ∀ pb ∈ B, log (pb.1*pb.2 : ℕ) ≤ (203/100 : ℝ)*N)
    (hM : ∀ pb ∈ B, 0 < M pb)
    (hMX : ∀ pb ∈ B, M pb < X pb)
    (hXM : ∀ pb ∈ B, X pb ≤ 2*M pb)
    (hlarge : ∀ pb ∈ B, exp ((N : ℝ)/2016) ≤ M pb)
    (hPL : ∀ pb ∈ B, log pb.1 ≤ L)
    (hT : ∀ pb ∈ B, ∀ d ∈ Finset.Icc (M pb+1) (X pb),
      1 ≤ log (pb.1*pb.2 : ℕ)+log d) :
    |u^(N+1)*∑ pb ∈ B, κ pb*ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| ≤
      4*edgeErrorConstant*((N : ℝ)+1)*((N : ℝ)+7+|y|)*comparisonRate^N := by
  have hc := (countingCostAt_pos (17/32)).le
  have hm := ZetaRieszPrimeCountMass.countMass_nonneg (65537/65536)
  let H := countingCostAt (17/32)*exp (-15*(N : ℝ)/64512)*(((N : ℝ)+7+|y|)*radialEnvelope N)
  have hH : 0 ≤ H := by dsimp [H]; positivity [radialEnvelope_pos N]
  have he : |∑ pb ∈ B, κ pb*ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| ≤
      4*H*(3*exp ((203/6553600 : ℝ)*N)*ZetaRieszPrimeCountMass.countMass (65537/65536)*
        exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536))) := by
    calc
      _ ≤ ∑ pb ∈ B, |κ pb*ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ pb ∈ B, 4*H*(3^(pb.1*pb.2).primeFactors.card/(pb.1*pb.2 : ℕ)) := by
        apply Finset.sum_le_sum
        intro pb hpb
        have hd := cutoff_discrepancy_bound hN (hM pb hpb) (hMX pb hpb) (hXM pb hpb)
          (hlarge pb hpb) hL (hB pb hpb).1.pos
          (Nat.pos_of_ne_zero (hB pb hpb).2.1.ne_zero) (hPL pb hpb) (hT pb hpb) y
        rw [abs_mul]
        exact (mul_le_mul (hκ pb hpb) hd (abs_nonneg _) (by norm_num)).trans_eq (by ring)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (fine_outer_cost_bound B N hB hlog)
          (by positivity : 0 ≤ 4*H)
  have hex : exp (-15*(N : ℝ)/64512)*exp ((203/6553600 : ℝ)*N) =
      exp (-((15/64512-203/6553600) : ℝ))^N := by
    rw [← exp_add,← exp_nat_mul]
    congr 1
    ring
  have hnorm : |u^(N+1)*∑ pb ∈ B, κ pb*ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| ≤
      (24*u*countingCostAt (17/32)*ZetaRieszPrimeCountMass.countMass (65537/65536)*
        exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536)))*
          ((N : ℝ)+1)*((N : ℝ)+7+|y|)*(cutoffRate u)^N := by
    rw [abs_mul,abs_of_nonneg (pow_nonneg hu _)]
    apply (mul_le_mul_of_nonneg_left he (pow_nonneg hu _)).trans_eq
    dsimp [H,radialEnvelope,cutoffRate]
    rw [mul_pow,mul_pow,pow_succ,pow_succ]
    have heq := hex
    calc
      _ = (24*u*countingCostAt (17/32)*ZetaRieszPrimeCountMass.countMass (65537/65536)*
          exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536)))*
          ((N : ℝ)+1)*((N : ℝ)+7+|y|)*(2^N*u^N)*
            (exp (-15*(N : ℝ)/64512)*exp ((203/6553600 : ℝ)*N)) := by ring
      _ = _ := by rw [heq]; ring
  apply hnorm.trans
  have hr := cutoffRate_bounds hu hU
  have hconst : 24*u*countingCostAt (17/32)*ZetaRieszPrimeCountMass.countMass (65537/65536)*
      exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536)) ≤ 4*edgeErrorConstant := by
    unfold edgeErrorConstant
    calc
      _ ≤ 24*ZetaRieszWideOwnerAudit.radiusCeiling*countingCostAt (17/32)*
          ZetaRieszPrimeCountMass.countMass (65537/65536)*
          exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536)) := by gcongr
      _ = _ := by ring
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconst (by positivity)) (by positivity))
    (pow_le_pow_left₀ hr.1 hr.2 N) (pow_nonneg hr.1 N)
    (by positivity [edgeErrorConstant_nonneg,comparisonRate_bounds.1])

/-- All radial shells may be joined before taking the signed comparison
error. A polynomial number of shells leaves the strict geometric saving.
The masks selecting each outer pair and each shell remain arbitrary. -/
theorem source_scaled_cutoff_shells_error {ι : Type*} (I : Finset ι)
    (B : ι → Finset (ℕ×ℕ)) {N : ℕ} (hN : 32 ≤ N)
    (M X : ι → ℕ×ℕ → ℕ) (κ : ι → ℕ×ℕ → ℝ)
    (hκ : ∀ i ∈ I, ∀ pb ∈ B i, |κ i pb| ≤ 4) {L u : ℝ} (hL : 0 < L)
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (hI : I.card ≤ N+1)
    (hB : ∀ i ∈ I, ∀ pb ∈ B i, pb.1.Prime ∧ Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2)
    (hlog : ∀ i ∈ I, ∀ pb ∈ B i, log (pb.1*pb.2 : ℕ) ≤ (203/100 : ℝ)*N)
    (hM : ∀ i ∈ I, ∀ pb ∈ B i, 0 < M i pb)
    (hMX : ∀ i ∈ I, ∀ pb ∈ B i, M i pb < X i pb)
    (hXM : ∀ i ∈ I, ∀ pb ∈ B i, X i pb ≤ 2*M i pb)
    (hlarge : ∀ i ∈ I, ∀ pb ∈ B i, exp ((N : ℝ)/2016) ≤ M i pb)
    (hPL : ∀ i ∈ I, ∀ pb ∈ B i, log pb.1 ≤ L)
    (hT : ∀ i ∈ I, ∀ pb ∈ B i, ∀ d ∈ Finset.Icc (M i pb+1) (X i pb),
      1 ≤ log (pb.1*pb.2 : ℕ)+log d) :
    |u^(N+1)*∑ i ∈ I, ∑ pb ∈ B i,
      κ i pb*ownedShellDiscrepancy N L y pb.1 pb.2 (M i pb) (X i pb)| ≤
      4*edgeErrorConstant*(8+|y|)*((N : ℝ)+1)^3*comparisonRate^N := by
  let C := 4*edgeErrorConstant*((N : ℝ)+1)*((N : ℝ)+7+|y|)*comparisonRate^N
  have hC : 0 ≤ C := by
    dsimp [C]; positivity [edgeErrorConstant_nonneg,comparisonRate_bounds.1]
  calc
    _ ≤ ∑ i ∈ I, |u^(N+1)*∑ pb ∈ B i,
        κ i pb*ownedShellDiscrepancy N L y pb.1 pb.2 (M i pb) (X i pb)| := by
      rw [Finset.mul_sum]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ I, C := Finset.sum_le_sum (fun i hi =>
      source_scaled_cutoff_shell_error (B i) hN (M i) (X i) (κ i) (hκ i hi) hL hu hU y
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
          0 ≤ 4*edgeErrorConstant*((N : ℝ)+1)^2*comparisonRate^N)
      dsimp [C]
      nlinarith only [hh]





/-- The joined hinge is monotone in its signed cofactor log. -/
theorem pairHinge_mono {L : ℝ} {p b B : ℕ} (hlog : log b ≤ log B) :
    pairHinge L p b ≤ pairHinge L p B := by
  have hP := log_natCast_nonneg p
  unfold pairHinge
  rcases le_total 0 (log b-L) with hb | hb
  · rw [max_eq_right hb,max_eq_right (by linarith : 0 ≤ log p+log b-L),
      max_eq_right (by linarith : 0 ≤ log B-L),
      max_eq_right (by linarith : 0 ≤ log p+log B-L)]
    linarith
  · rw [max_eq_left hb]
    rcases le_total 0 (log B-L) with hB | hB
    · rw [max_eq_right hB,max_eq_right (by linarith : 0 ≤ log p+log B-L)]
      rw [show log p+log B-L-(log B-L)=log p by ring]
      simp only [sub_zero]
      exact max_le hP (by linarith)
    · rw [max_eq_left hB]
      simpa only [sub_zero] using
        (max_le_max_left 0 (show log p+log b-L ≤ log p+log B-L by linarith))

/-- The four exact divisor cuts of the fixed block. -/
def cutoffDivisors (N p B : ℕ) : Finset ℕ :=
  (6 : ℕ).divisors.filter (fun δ => log δ < log (p*B : ℕ)-(3899/2000 : ℝ)*N)

/-- One frozen signed arithmetic scalar. Its cutoff does not depend on
 the original unsigned variable e. -/
def cutoffMultiplier (L : ℝ) (N p B : ℕ) : ℝ :=
  (∑ δ ∈ cutoffDivisors N p B, (μ δ : ℝ)*pairHinge L p (B/δ))/pairHinge L p B

/-- The complete clipped block has a fixed factor-four relative bound.
This is used only AFTER the whole unsigned row has been cancelled. -/
theorem cutoffMultiplier_bound {L : ℝ} {N p B : ℕ} (hB : 0 < B)
    (h6 : 6 ∣ B) (hH : pairHinge L p B ≠ 0) :
    |cutoffMultiplier L N p B| ≤ 4 := by
  have hHp := lt_of_le_of_ne (pairHinge_bounds L p B).1 (Ne.symm hH)
  have hterm δ (hδ : δ ∈ cutoffDivisors N p B) :
      |(μ δ : ℝ)*pairHinge L p (B/δ)| ≤ pairHinge L p B := by
    have hd := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hδ).1
    have hdB := hd.trans h6
    have hq : 0 < B/δ := Nat.div_pos (Nat.le_of_dvd hB hdB)
      (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hδ).1)
    have hl : log (B/δ : ℕ) ≤ log B := log_le_log (by exact_mod_cast hq)
      (by exact_mod_cast Nat.div_le_self B δ)
    rw [abs_mul,abs_of_nonneg (pairHinge_bounds L p (B/δ)).1]
    have hm : |(μ δ : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := δ)
    exact (mul_le_of_le_one_left (pairHinge_bounds L p (B/δ)).1 hm).trans
      (pairHinge_mono hl)
  have hcard : (cutoffDivisors N p B).card ≤ 4 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by decide : (6 : ℕ).divisors.card=4)
  have hs : |∑ δ ∈ cutoffDivisors N p B, (μ δ : ℝ)*pairHinge L p (B/δ)| ≤
      4*pairHinge L p B := by
    exact ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)).trans
      (by simp only [Finset.sum_const,nsmul_eq_mul];
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hHp.le)
  rw [cutoffMultiplier,abs_div,abs_of_pos hHp]
  exact (div_le_iff₀ hHp).mpr (by linarith)

/-- The actual short cutoff for d=e*delta depends only on p*B and delta.
No phase, product label, radial mask or allocation is changed. -/
theorem short_cutoff_iff {N p B e δ : ℕ} (hp : 0 < p) (hB : 0 < B)
    (he : 0 < e) (hδ : 0 < δ) :
    log (e*δ : ℕ) < log (p*(B*e) : ℕ)-(3899/2000 : ℝ)*N ↔
      log δ < log (p*B : ℕ)-(3899/2000 : ℝ)*N := by
  rw [show p*(B*e)=(p*B)*e by ac_rfl,Nat.cast_mul,Nat.cast_mul,
    log_mul (by exact_mod_cast he.ne') (by exact_mod_cast hδ.ne'),
    log_mul (by exact_mod_cast (Nat.mul_pos hp hB).ne') (by exact_mod_cast he.ne')]
  constructor <;> intro h <;> linarith

/-- Every frozen scalar term is an ORIGINAL (e*delta,B/delta) incidence.
Its common weight is still evaluated at p*(B*e). -/
theorem cutoff_row_atom_eq (A : Finset ℕ) {L y : ℝ} {N p B e : ℕ}
    (hB : Squarefree B) (h6 : 6 ∣ B) (hH : pairHinge L p B ≠ 0) :
    cutoffMultiplier L N p B*rowAtom A N L y p B e =
      ∑ δ ∈ cutoffDivisors N p B,
        (phaseWeight (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*(B*e))})
          L N y (B*e) p).re*(μ (B/δ) : ℝ)*pairHinge L p (B/δ)*
            sieve (p*B).primeFactors e := by
  have heq : cutoffMultiplier L N p B*pairHinge L p B =
      ∑ δ ∈ cutoffDivisors N p B, (μ δ : ℝ)*pairHinge L p (B/δ) := by
    unfold cutoffMultiplier
    exact div_mul_cancel₀ _ hH
  unfold rowAtom
  calc
    _ = (phaseWeight (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*(B*e))})
          L N y (B*e) p).re*(μ B : ℝ)*
        (cutoffMultiplier L N p B*pairHinge L p B)*sieve (p*B).primeFactors e := by ring
    _ = _ := by
      rw [heq]
      simp_rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro δ hδ
      rw [ZetaRieszSignedConvolution.moebius_cofactor_real hB
        ((Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hδ).1).trans h6)]
      ring

open ZetaRieszOwnerGapRows (ownershipLength weighted_overflowRows_bound_of_geometry)

/-- All original full-window rows satisfying the exact owner gap. -/
def cutoffRows (u : ℝ) (N : ℕ) : Finset (ℕ×ℕ) :=
  ((ZetaRieszAnnulusJoint.intermediatePrimes u N).product
    (Finset.Icc 2 ⌊exp ((203/100 : ℝ)*N)⌋₊)).filter fun pb =>
      Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2 ∧
      (∀ q ∈ pb.2.primeFactors, q < pb.1) ∧
      pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2 ≠ 0 ∧
      log (pb.1*pb.2 : ℕ) ≤ (((39/20)-1/2016) : ℝ)*N ∧
      log pb.1 < (243/200 : ℝ)*N ∧
      (203/100 : ℝ)*N < log (pb.1*pb.2 : ℕ)+log pb.1 ∧
      ZetaRieszFineDivisorRows.lower N pb.1 pb.2 ≤ ZetaRieszFineDivisorRows.upper N pb.1 pb.2 ∧
      6 ∣ pb.2 ∧ (3899/2000 : ℝ)*N < log (pb.1*pb.2 : ℕ) ∧
      log (pb.1*pb.2 : ℕ) ≤ (3899/2000 : ℝ)*N+log 6

private theorem row_owner_mem {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (h : pb ∈ cutoffRows u N) :
    pb.1 ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N :=
  (Finset.mem_product.mp (Finset.mem_filter.mp h).1).1

private theorem row_large {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (h : pb ∈ cutoffRows u N) : exp ((N : ℝ)/2016) ≤ ZetaRieszFineDivisorRows.lower N pb.1 pb.2 := by
  have hc := (Finset.mem_filter.mp h).2.2.2.2.2.1
  exact (exp_le_exp.mpr (by linarith : (N : ℝ)/2016 ≤
    (39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ))).trans (Nat.le_ceil _)

/-- The exact ownership certificate for the whole original radial row. -/
theorem cutoff_row_geometry {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (h : pb ∈ cutoffRows u N) :
    RowGeometry N (ownershipLength N pb.1 pb.2) pb.1 pb.2
      (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper N pb.1 pb.2) := by
  obtain ⟨hprod,hs,hpd,hmax,_ha,hc,hP,hgap,hlu,_hblock⟩ := Finset.mem_filter.mp h
  obtain ⟨hp,hb⟩ := Finset.mem_product.mp hprod
  have hp' := (ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp hp
  have hp0 : (0 : ℝ)<pb.1 := by exact_mod_cast hp'.1.pos
  have hb0 : (0 : ℝ)<pb.2 := by
    have hbpos : 0 < pb.2 := by have := (Finset.mem_Icc.mp hb).1; omega
    exact_mod_cast hbpos
  have hM : 0 < ZetaRieszFineDivisorRows.lower N pb.1 pb.2 := Nat.ceil_pos.mpr (exp_pos _)
  have hX := hM.trans_le hlu
  have hlo : (39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ) ≤ log (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) := by
    simpa only [log_exp,ZetaRieszFineDivisorRows.lower] using log_le_log (exp_pos _)
      (Nat.le_ceil (exp ((39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ))))
  have hhi : log (ZetaRieszFineDivisorRows.upper N pb.1 pb.2) ≤ (203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ) := by
    simpa only [log_exp,ZetaRieszFineDivisorRows.upper] using log_le_log
      (by exact_mod_cast hX : (0 : ℝ)<ZetaRieszFineDivisorRows.upper N pb.1 pb.2)
      (Nat.floor_le (exp_pos ((203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ))).le)
  apply ZetaRieszLowOwnerRows.full_window_geometry_of_owner_gap hp'.1
    (by have := (Finset.mem_Icc.mp hb).1; omega) hs hpd hmax hM
    (by linarith) (by linarith)
    (by linarith [Nat.cast_nonneg (α := ℝ) N]) hgap
    (by nlinarith [Nat.cast_nonneg (α := ℝ) N])

private theorem row_data {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (h : pb ∈ cutoffRows u N) :
    log (pb.1*pb.2 : ℕ) ≤ (((39/20)-1/2016) : ℝ)*N ∧
      log pb.1 < (243/200 : ℝ)*N ∧
      ZetaRieszFineDivisorRows.lower N pb.1 pb.2 ≤ ZetaRieszFineDivisorRows.upper N pb.1 pb.2 := by
  obtain ⟨_,_,_,_,_,hc,hP,_,hlu,_hblock⟩ := Finset.mem_filter.mp h
  exact ⟨hc,hP,hlu⟩

private theorem row_multiplier_bound {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (hpb : pb ∈ cutoffRows u N) :
    |cutoffMultiplier (SquarefreeVaughanLogSource.length u N) N pb.1 pb.2| ≤ 4 := by
  obtain ⟨_,_,_,_,hH,_,_,_,_,h6,_,_⟩ := Finset.mem_filter.mp hpb
  exact cutoffMultiplier_bound (by have := (cutoff_row_geometry hpb).2.1; omega) h6 hH

private theorem coefficient_bound {u : ℝ} {N : ℕ} (hN : 32 ≤ N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    {pb : ℕ×ℕ} (hpb : pb ∈ cutoffRows u N) :
    |((μ pb.2 : ℝ)*pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2/
        (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)))*
        density (pb.1*pb.2).primeFactors| ≤ (1 : ℝ)/(pb.1*pb.2 : ℕ) := by
  have hg := cutoff_row_geometry hpb
  have hP := (row_data hpb).2.1
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
    (∑ pb ∈ cutoffRows u N, (1 : ℝ)/(pb.1*pb.2 : ℕ)) ≤
      (1+(203/100 : ℝ)*N)^2 := by
  let B := ⌊exp ((203/100 : ℝ)*N)⌋₊
  have hBn : 0 < B := Nat.floor_pos.mpr (one_le_exp (by positivity))
  have hB : (0 : ℝ)<B := by exact_mod_cast hBn
  have hlogB : log B ≤ (203/100 : ℝ)*N := by
    have hh := log_le_log hB (Nat.floor_le (exp_pos ((203/100 : ℝ)*N)).le)
    simpa only [log_exp] using hh
  have hsub : cutoffRows u N ⊆ (Finset.Icc 1 B).product (Finset.Icc 1 B) := by
    intro pb hpb
    have hg := cutoff_row_geometry hpb
    have hb := (Finset.mem_product.mp (Finset.mem_filter.mp hpb).1).2
    have hp : log pb.1 ≤ (13/20 : ℝ)*((203/100 : ℝ)*N) := by
      have hP := (row_data hpb).2.1
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
def cutoffDensityMain (u y : ℝ) (N : ℕ) : ℝ :=
  ∑ pb ∈ cutoffRows u N, cutoffMultiplier (SquarefreeVaughanLogSource.length u N) N pb.1 pb.2*
    densityRow N (SquarefreeVaughanLogSource.length u N) y
    pb.1 pb.2 (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) (ZetaRieszFineDivisorRows.upper N pb.1 pb.2)

/-- The entire signed main is paid before its outer rows/counts are
normed. Saturation is absent; the original allocation and phase remain. -/
theorem source_scaled_cutoffDensityMain_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 32 ≤ N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    {y : ℝ} (hy : 54 ≤ |y|) :
    |u^(N+1)*cutoffDensityMain u y N| ≤ 4*fineMainBudget y N := by
  have hrow pb (hpb : pb ∈ cutoffRows u N) :
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
      (full_window_weight_bound_of_gap hu hU hN (β := 1/2016) (by norm_num)
        (row_data hpb).1 (row_data hpb).2.1 (row_data hpb).2.2 hy) (abs_nonneg _) (by positivity)
  have hκ pb (hpb : pb ∈ cutoffRows u N) := row_multiplier_bound hpb
  have hsum : |∑ pb ∈ cutoffRows u N,
      u^(N+1)*(cutoffMultiplier (SquarefreeVaughanLogSource.length u N) N pb.1 pb.2*
        densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
          (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) (ZetaRieszFineDivisorRows.upper N pb.1 pb.2))| ≤
      ∑ pb ∈ cutoffRows u N, 4*((1 : ℝ)/(pb.1*pb.2 : ℕ)*
        (((N : ℝ)+1)*(13*(N : ℝ)+33+4*|y|)*fineRateTotal^N)) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun (pb : ℕ×ℕ) (hpb : pb ∈ cutoffRows u N) =>
      (by
        rw [show u^(N+1)*(cutoffMultiplier (SquarefreeVaughanLogSource.length u N) N pb.1 pb.2*
            densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
              (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) (ZetaRieszFineDivisorRows.upper N pb.1 pb.2)) =
          cutoffMultiplier (SquarefreeVaughanLogSource.length u N) N pb.1 pb.2*
            (u^(N+1)*densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
              (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) (ZetaRieszFineDivisorRows.upper N pb.1 pb.2)) by ring,
          abs_mul]
        exact (mul_le_mul (hκ pb hpb) (hrow pb hpb) (abs_nonneg _) (by norm_num)).trans_eq
          (by ring) : _ ≤ 4*((1 : ℝ)/(pb.1*pb.2 : ℕ)*
            (((N : ℝ)+1)*(13*(N : ℝ)+33+4*|y|)*fineRateTotal^N)))))
  have hs : |u^(N+1)*cutoffDensityMain u y N| ≤
      4*(1+(203/100 : ℝ)*N)^2*
        (((N : ℝ)+1)*(13*(N : ℝ)+33+4*|y|)*fineRateTotal^N) := by
    rw [cutoffDensityMain,Finset.mul_sum]
    apply hsum.trans
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum,← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (outer_harmonic_bound u N)
        (by positivity [fineRateTotal_bounds.1] :
          0 ≤ ((N : ℝ)+1)*((13*(N : ℝ)+33+4*|y|)*fineRateTotal^N)))
      (by norm_num : (0 : ℝ)≤4)
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
  convert mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ)≤4) using 1 <;> ring

private theorem last_boundary {u : ℝ} {N : ℕ} {pb : ℕ×ℕ} (hpb : pb ∈ cutoffRows u N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    boundary (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper N pb.1 pb.2) (N+1) =
        ZetaRieszFineDivisorRows.upper N pb.1 pb.2 := by
  have hg := cutoff_row_geometry hpb
  have ha := pairHinge_active (show pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2 ≠ 0 from (Finset.mem_filter.mp hpb).2.2.2.2.1)
  have hp0 := hg.1.pos
  have hb0 : 0 < pb.2 := by have := hg.2.1; omega
  have hlog : log (pb.1*pb.2 : ℕ)=log pb.1+log pb.2 := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp0.ne') (by exact_mod_cast hb0.ne')]
  have hU : (ZetaRieszFineDivisorRows.upper N pb.1 pb.2 : ℝ) ≤
      exp ((131/200 : ℝ)*N) := by
    have hf := Nat.floor_le (exp_pos (((203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ)))).le
    have he : ((203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ)) ≤ (131/200 : ℝ)*N := by
      rw [← hlog] at ha
      linarith [Nat.cast_nonneg (α := ℝ) N]
    exact hf.trans (exp_le_exp.mpr he)
  have hpow : exp ((131/200 : ℝ)*N) ≤
      ((2^(N+1)*ZetaRieszFineDivisorRows.lower N pb.1 pb.2 : ℕ) : ℝ) := by
    have hbase := row_large hpb
    have hrate : (131/200 : ℝ)*N ≤ (N+1 : ℕ)*log 2+(N : ℝ)/2016 := by
      push_cast
      nlinarith [log_two_gt_d9,log_pos (by norm_num : (1 : ℝ)<2)]
    calc
      _ ≤ exp ((N+1 : ℕ)*log 2+(N : ℝ)/2016) := exp_le_exp.mpr hrate
      _ = (2 : ℝ)^(N+1)*exp ((N : ℝ)/2016) := by rw [exp_add,exp_nat_mul,exp_log (by norm_num : (0 : ℝ)<2)]
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
  (cutoffRows u N).filter (fun pb => rowBoundary u N i pb < rowBoundary u N (i+1) pb)

private theorem shell_geometry {u : ℝ} {N i : ℕ} {pb : ℕ×ℕ}
    (hpb : pb ∈ shellRows u N i) :
    RowGeometry N (ownershipLength N pb.1 pb.2) pb.1 pb.2
      (rowBoundary u N i pb) (rowBoundary u N (i+1) pb) := by
  obtain ⟨hr,hMX⟩ := Finset.mem_filter.mp hpb
  have hlu := (row_data hr).2.2
  apply geometry_subinterval (cutoff_row_geometry hr) _ _ hMX
  · exact lower_le_boundary hlu i
  · exact min_le_left _ _

set_option maxHeartbeats 800000 in
private theorem shell_large {u : ℝ} {N i : ℕ} {pb : ℕ×ℕ}
    (hpb : pb ∈ shellRows u N i) : exp ((N : ℝ)/2016) ≤ rowBoundary u N i pb := by
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
        ∑ pb ∈ cutoffRows u N, ∑ i ∈ Finset.range (N+1),
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
        cutoffMultiplier (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
          (dyadicMomentOrder j) pb.1 pb.2*coreRow u y j pb.1 pb.2
          (rowBoundary u (dyadicMomentOrder j) i pb)
          (rowBoundary u (dyadicMomentOrder j) (i+1) pb)) =
      ∑ pb ∈ cutoffRows u (dyadicMomentOrder j),
        cutoffMultiplier (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
          (dyadicMomentOrder j) pb.1 pb.2*coreRow u y j pb.1 pb.2 (ZetaRieszFineDivisorRows.lower (dyadicMomentOrder j) pb.1 pb.2)
          (ZetaRieszFineDivisorRows.upper (dyadicMomentOrder j) pb.1 pb.2) := by
  rw [sum_shellRows_eq u (dyadicMomentOrder j)
    (fun pb M X => cutoffMultiplier (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
      (dyadicMomentOrder j) pb.1 pb.2*coreRow u y j pb.1 pb.2 M X)
    (fun pb M => by simp only [coreRow_empty,mul_zero])]
  apply Finset.sum_congr rfl
  intro pb hpb
  have hlu := (row_data hpb).2.2
  rw [← Finset.mul_sum]
  congr 1
  unfold coreRow
  dsimp only
  simp only [rowBoundary]
  rw [sum_boundary_shells _ _ _ _ hlu,last_boundary hpb hL]

/-- The SIGNED density rows are likewise recombined before any main-term
estimate. No norm, positive part or separate prime-count cost is inserted. -/
private theorem sum_densityRow_shells (u y : ℝ) (N : ℕ)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    (∑ i ∈ Finset.range (N+1), ∑ pb ∈ shellRows u N i,
      cutoffMultiplier (SquarefreeVaughanLogSource.length u N) N pb.1 pb.2*
      densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
        (rowBoundary u N i pb) (rowBoundary u N (i+1) pb)) =
      ∑ pb ∈ cutoffRows u N,
        cutoffMultiplier (SquarefreeVaughanLogSource.length u N) N pb.1 pb.2*
      densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
          (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) (ZetaRieszFineDivisorRows.upper N pb.1 pb.2) := by
  rw [sum_shellRows_eq u N
    (fun pb M X => cutoffMultiplier (SquarefreeVaughanLogSource.length u N) N pb.1 pb.2*
      densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2 M X)
    (fun pb M => by simp only [densityRow_empty,mul_zero])]
  apply Finset.sum_congr rfl
  intro pb hpb
  have hlu := (row_data hpb).2.2
  simp only [densityRow_interval,← Finset.mul_sum]
  simp only [rowBoundary]
  rw [sum_boundary_shells _ _ _ _ hlu,last_boundary hpb hL]

private theorem weighted_overflow_shells_bound {ι : Type*} (I : Finset ι)
    (B : ι → Finset (ℕ×ℕ)) (M X : ι → ℕ×ℕ → ℕ) (κ : ι → ℕ×ℕ → ℝ)
    (hκ : ∀ i ∈ I, ∀ pb ∈ B i, |κ i pb| ≤ 4)
    (j : ℕ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hI : I.card ≤ dyadicMomentOrder j+1)
    (hg : ∀ i ∈ I, ∀ pb ∈ B i, RowGeometry (dyadicMomentOrder j)
      (ownershipLength (dyadicMomentOrder j) pb.1 pb.2) pb.1 pb.2 (M i pb) (X i pb))
    (hcount : exp (2*(dyadicPrimeCount j : ℝ)*ZetaRieszPrimeCountMass.countMass (101/100)) ≤
      (101/100 : ℝ)^(dyadicMomentOrder j)) :
    |u^(dyadicMomentOrder j+1)*∑ i ∈ I, ∑ pb ∈ B i,
      κ i pb*overflowRow u y j pb.1 pb.2 (M i pb) (X i pb)| ≤
      4*highCountConstant*((dyadicMomentOrder j : ℝ)+1)^2*(49/50 : ℝ)^(dyadicMomentOrder j) := by
  let N := dyadicMomentOrder j
  let C := 4*highCountConstant*(N : ℝ)*(97/100 : ℝ)^N*
    exp (2*(dyadicPrimeCount j : ℝ)*ZetaRieszPrimeCountMass.countMass (101/100))
  have hC : 0 ≤ C := by dsimp [C]; positivity [highCountConstant_nonneg]
  calc
    _ ≤ ∑ i ∈ I, |u^(N+1)*∑ pb ∈ B i,
        κ i pb*overflowRow u y j pb.1 pb.2 (M i pb) (X i pb)| := by
      rw [Finset.mul_sum]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ I, C := Finset.sum_le_sum (fun i hi =>
      weighted_overflowRows_bound_of_geometry (B i) (M i) (X i) j hu hU y
        (fun pb => ownershipLength N pb.1 pb.2) (κ i) (hκ i hi) hL (hg i hi))
    _ = (I.card : ℝ)*C := by simp
    _ ≤ ((N : ℝ)+1)*C := mul_le_mul_of_nonneg_right (by exact_mod_cast hI) hC
    _ ≤ 4*highCountConstant*((N : ℝ)+1)^2*
        ((97/100 : ℝ)^N*(101/100 : ℝ)^N) := by
      have hp := mul_le_mul_of_nonneg_left hcount
        (by positivity [highCountConstant_nonneg] :
          0 ≤ ((N : ℝ)+1)*4*highCountConstant*N*(97/100 : ℝ)^N)
      have hn : ((N : ℝ)+1)*N ≤ ((N : ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
      have hpoly := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn (by positivity [highCountConstant_nonneg] : 0 ≤ 4*highCountConstant))
        (by positivity : 0 ≤ (97/100 : ℝ)^N*(101/100 : ℝ)^N)
      dsimp [C]
      nlinarith only [hp,hpoly]
    _ ≤ _ := by
      rw [← mul_pow]
      gcongr
      all_goals first | positivity [highCountConstant_nonneg] | norm_num

/-- Literal signed original core incidences of the complete ownership-gap population. -/
def cutoffLiteralRows (u y : ℝ) (j : ℕ) : ℝ :=
  ∑ pb ∈ cutoffRows u (dyadicMomentOrder j),
    cutoffMultiplier (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
      (dyadicMomentOrder j) pb.1 pb.2*coreRow u y j pb.1 pb.2 (ZetaRieszFineDivisorRows.lower (dyadicMomentOrder j) pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper (dyadicMomentOrder j) pb.1 pb.2)

set_option maxHeartbeats 1200000 in
/-- An INDEPENDENT signed bound for the ORIGINAL ownership-gap row
population, across all counts and radial positions together. No zero,
prime-density approximation or unproved cancellation premise enters. -/
theorem eventually_abs_cutoffLiteralRows_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop,
      |u^(dyadicMomentOrder j+1)*cutoffLiteralRows u y j| ≤
        4*edgeRowBudget y (dyadicMomentOrder j) := by
  let I := fun j => Finset.range (dyadicMomentOrder j+1)
  let B := fun j i => shellRows u (dyadicMomentOrder j) i
  let M := fun j i => rowBoundary u (dyadicMomentOrder j) i
  let X := fun j i => rowBoundary u (dyadicMomentOrder j) (i+1)
  let κ := fun (j : ℕ) (_i : ℕ) (pb : ℕ×ℕ) => cutoffMultiplier
    (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) pb.1 pb.2
  have hgeo j i (_hi : i ∈ I j) pb (hpb : pb ∈ B j i) :
      RowGeometry (dyadicMomentOrder j) (ownershipLength (dyadicMomentOrder j) pb.1 pb.2)
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
  have hκ i (_hi : i ∈ I j) pb (hpb : pb ∈ B j i) : |κ j i pb| ≤ 4 :=
    row_multiplier_bound (Finset.mem_filter.mp hpb).1
  have hcount := weighted_overflow_shells_bound (I j) (B j) (M j) (X j) (κ j) hκ j
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
    have hP := (row_data (Finset.mem_filter.mp hpb).1).2.1
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
  have herr := source_scaled_cutoff_shells_error (I j) (B j) hN (M j) (X j) (κ j) hκ hL0
    (by linarith : 0 ≤ u) hU y (hI j)
    (fun i hi pb hpb => ⟨(hgeo j i hi pb hpb).1,
      (hgeo j i hi pb hpb).2.2.1,(hgeo j i hi pb hpb).2.2.2.1⟩)
    hlog (fun i hi pb hpb => (hgeo j i hi pb hpb).2.2.2.2.2.2.1)
    (fun _ _ _ hpb => (Finset.mem_filter.mp hpb).2)
    (fun i _ pb _ => boundary_le_twice _ _ i)
    (fun _ _ _ hpb => shell_large hpb) hPL hT
  have hsum : (∑ i ∈ I j, ∑ pb ∈ B j i,
      κ j i pb*coreRow u y j pb.1 pb.2 (M j i pb) (X j i pb)) =
      (∑ i ∈ I j, ∑ pb ∈ B j i, κ j i pb*densityRow N L y pb.1 pb.2 (M j i pb) (X j i pb))+
      (∑ i ∈ I j, ∑ pb ∈ B j i, κ j i pb*ownedShellDiscrepancy N L y pb.1 pb.2 (M j i pb) (X j i pb))-
      (∑ i ∈ I j, ∑ pb ∈ B j i, κ j i pb*overflowRow u y j pb.1 pb.2 (M j i pb) (X j i pb)) := by
    simp only [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro pb hpb
    have h := coreRow_add_overflow_of_geometry (y := y) j hj hu hU hL (hgeo j i hi pb hpb) (hpA j i hi pb hpb)
    change _+_=densityRow N L y _ _ _ _+ownedShellDiscrepancy N L y _ _ _ _ at h
    have hw := congrArg (fun v : ℝ => κ j i pb*v) h
    simp only [mul_add] at hw
    linarith
  have hm := source_scaled_cutoffDensityMain_bound (by linarith : 0 ≤ u) hU hN hL hy
  change |u^(N+1)*cutoffLiteralRows u y j| ≤ 4*edgeRowBudget y N
  rw [cutoffLiteralRows,← sum_coreRow_shells u y j hL]
  change |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i, κ j i pb*coreRow u y j pb.1 pb.2 (M j i pb) (X j i pb))| ≤ _
  rw [hsum,mul_sub,mul_add]
  have hmain : |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i,
      κ j i pb*densityRow N L y pb.1 pb.2 (M j i pb) (X j i pb))| ≤ 4*fineMainBudget y N := by
    simpa only [I,B,M,X,κ,N,L,sum_densityRow_shells u y (dyadicMomentOrder j) hL,
      cutoffDensityMain] using hm
  calc
    _ ≤ |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i,
          κ j i pb*densityRow N L y pb.1 pb.2 (M j i pb) (X j i pb))|+
        |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i,
          κ j i pb*ownedShellDiscrepancy N L y pb.1 pb.2 (M j i pb) (X j i pb))|+
        |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i,
          κ j i pb*overflowRow u y j pb.1 pb.2 (M j i pb) (X j i pb))| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 4*fineMainBudget y N+
        4*edgeErrorConstant*(8+|y|)*((N : ℝ)+1)^3*comparisonRate^N+
        4*highCountConstant*((N : ℝ)+1)^2*(49/50 : ℝ)^N :=
      add_le_add (add_le_add hmain herr) hcount
    _ = 4*edgeRowBudget y N := by unfold edgeRowBudget; ring

/-- Concrete source-o(1) saving for the ORIGINAL retained signed
prime-incidence sum on the enlarged population. -/
theorem tendsto_cutoffLiteralRows {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*cutoffLiteralRows u y j) atTop (𝓝 0) := by
  have ht := ((tendsto_edgeRowBudget y).comp tendsto_dyadicMomentOrder).const_mul 4
  simp only [mul_zero] at ht
  apply squeeze_zero_norm' (a := fun j => 4*edgeRowBudget y (dyadicMomentOrder j)) ?_ ht
  simpa only [Real.norm_eq_abs] using eventually_abs_cutoffLiteralRows_bound hu hU hy



/-- Rounded-boundary error only; no retained signed main is normed. -/
def cutoffEndpointBudget (N : ℕ) : ℝ :=
  72*((N : ℝ)+1)^3*comparisonRate^N

theorem tendsto_cutoffEndpointBudget : Tendsto cutoffEndpointBudget atTop (𝓝 0) := by
  have h := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 3
    comparisonRate_bounds.1 comparisonRate_bounds.2).const_mul 72
  simp only [mul_zero] at h
  convert h using 1
  ext N
  unfold cutoffEndpointBudget
  ring

private theorem endpoint_cofactor {u : ℝ} {N : ℕ} (hN : 32 ≤ N) {pb : ℕ×ℕ}
    (hpb : pb ∈ cutoffRows u N)
    (hsieve : sieve (pb.1*pb.2).primeFactors (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) ≠ 0) :
    Squarefree (pb.2*ZetaRieszFineDivisorRows.lower N pb.1 pb.2) ∧
      2 ≤ (pb.2*ZetaRieszFineDivisorRows.lower N pb.1 pb.2).primeFactors.card ∧
      ∀ q ∈ (pb.2*ZetaRieszFineDivisorRows.lower N pb.1 pb.2).primeFactors, q < pb.1 := by
  have hg := cutoff_row_geometry hpb
  have hd1 : 1 < ZetaRieszFineDivisorRows.lower N pb.1 pb.2 := by
    have h := row_large hpb
    have he := add_one_le_exp ((N : ℝ)/2016)
    have hnr : (32 : ℝ) ≤ N := by exact_mod_cast hN
    have hr : (1 : ℝ)<ZetaRieszFineDivisorRows.lower N pb.1 pb.2 := by linarith
    exact_mod_cast hr
  exact closed_row_cofactor_geometry hg
    (Finset.mem_Icc.mpr ⟨le_rfl,(row_data hpb).2.2⟩) hd1 hsieve


private theorem endpoint_atom_bound {u : ℝ} {N : ℕ} (hN : 32 ≤ N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    {pb : ℕ×ℕ} (hpb : pb ∈ cutoffRows u N) (y : ℝ) :
    |rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u N) N
      (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2 (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)| ≤
        radialEnvelope N*exp (-(N : ℝ)/2016)/(pb.1*pb.2 : ℕ) := by
  have hg := cutoff_row_geometry hpb
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
  have hinv : (d : ℝ)⁻¹ ≤ exp (-(N : ℝ)/2016) := by
    rw [neg_div,exp_neg]
    exact inv_anti₀ (exp_pos _) hdlarge
  calc
    _ = (|ownedAmplitude N (log pb.1) (log (pb.1*pb.2 : ℕ)) d|
        *|cos (y*(log (pb.1*pb.2 : ℕ)+log d))| * |(μ pb.2 : ℝ)| * pairHinge L pb.1 pb.2)/
          (L*(pb.1*pb.2 : ℕ)*d) := by ring
    _ ≤ radialEnvelope N*L/(L*(pb.1*pb.2 : ℕ)*d) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = radialEnvelope N/(pb.1*pb.2 : ℕ)*(d : ℝ)⁻¹ := by field_simp
    _ ≤ radialEnvelope N/(pb.1*pb.2 : ℕ)*exp (-(N : ℝ)/2016) :=
      mul_le_mul_of_nonneg_left hinv (by positivity [radialEnvelope_pos N])
    _ = _ := by ring



/-- The original core-masked rounded endpoint of each new row. -/
def cutoffEndpointRows (u y : ℝ) (j : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  ∑ pb ∈ cutoffRows u N,
    cutoffMultiplier L N pb.1 pb.2*(if pb.1*(pb.2*ZetaRieszFineDivisorRows.lower N pb.1 pb.2) ∈ ZetaRieszParityPacket.coreBand u N (dyadicPrimeCount j)
      then rowAtom A N L y pb.1 pb.2 (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) else 0)


theorem source_scaled_cutoffEndpointRows_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (j : ℕ)
    (hN : 32 ≤ dyadicMomentOrder j)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    |u^(dyadicMomentOrder j+1)*cutoffEndpointRows u y j| ≤
      cutoffEndpointBudget (dyadicMomentOrder j) := by
  let N := dyadicMomentOrder j
  have hsum : |cutoffEndpointRows u y j| ≤
      4*radialEnvelope N*exp (-(N : ℝ)/2016)*(1+(203/100 : ℝ)*N)^2 := by
    unfold cutoffEndpointRows
    dsimp only
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ pb ∈ cutoffRows u N,
          4*radialEnvelope N*exp (-(N : ℝ)/2016)/(pb.1*pb.2 : ℕ) := by
        apply Finset.sum_le_sum
        intro pb hpb
        rw [abs_mul]
        split_ifs
        · exact (mul_le_mul (row_multiplier_bound hpb) (endpoint_atom_bound hN hL hpb y)
            (abs_nonneg _) (by norm_num)).trans_eq (by ring)
        · simp only [abs_zero,mul_zero]
          positivity [radialEnvelope_pos N]
      _ = 4*radialEnvelope N*exp (-(N : ℝ)/2016)*
          (∑ pb ∈ cutoffRows u N, (1 : ℝ)/(pb.1*pb.2 : ℕ)) := by
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
  have hr : (2*u)^N*exp (-(N : ℝ)/2016) ≤ comparisonRate^N := by
    calc
      _ ≤ (exp (1/10000 : ℝ))^N*exp (-(N : ℝ)/2016) := by gcongr
      _ = exp (((1/10000 : ℝ)-1/2016))^N := by
        rw [← exp_nat_mul,← exp_add,← exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := by
        apply pow_le_pow_left₀ (exp_pos _).le
        unfold comparisonRate
        exact exp_le_exp.mpr (by norm_num)
  have hp : (1+(203/100 : ℝ)*N)^2 ≤ 9*((N : ℝ)+1)^2 := by
    have hh : 1+(203/100 : ℝ)*N ≤ 3*((N : ℝ)+1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    exact (pow_le_pow_left₀ (by positivity) hh 2).trans_eq (by ring)
  have hf : 2*u*((N : ℝ)+1) ≤ 2*((N : ℝ)+1) := by
    have huU : u ≤ (10001/20000 : ℝ) := hU
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  rw [abs_mul,abs_of_nonneg (pow_nonneg hu _)]
  apply (mul_le_mul_of_nonneg_left hsum (pow_nonneg hu _)).trans
  have heq : u^(N+1)*(4*radialEnvelope N*exp (-(N : ℝ)/2016)*
      (1+(203/100 : ℝ)*N)^2) =
      4*(2*u*((N : ℝ)+1))*((2*u)^N*exp (-(N : ℝ)/2016))*
        (1+(203/100 : ℝ)*N)^2 := by
    unfold radialEnvelope
    rw [pow_succ,pow_succ,mul_pow]
    ring
  rw [heq]
  have hh := mul_le_mul
    (mul_le_mul hf hr (by positivity) (by positivity)) hp
    (sq_nonneg _) (by positivity [comparisonRate_bounds.1])
  convert mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ)≤4) using 1 <;> simp only [cutoffEndpointBudget,N] <;> ring

/-- The endpoint payment tends to zero at source scale. -/
theorem tendsto_cutoffEndpointRows {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*cutoffEndpointRows u y j) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun j => cutoffEndpointBudget (dyadicMomentOrder j)) ?_
    (tendsto_cutoffEndpointBudget.comp tendsto_dyadicMomentOrder)
  filter_upwards [tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (32 : ℕ)),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
        (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source))] with j hN hL
  have hL' : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by nlinarith only [hL]
  simpa only [Real.norm_eq_abs] using
    source_scaled_cutoffEndpointRows_bound (by linarith : 0 ≤ u) hU y j hN hL'


/-- No original integer endpoint is dropped by the closed row identity. -/
theorem cutoff_rows_closed_eq (u y : ℝ) (j : ℕ) :
    (∑ pb ∈ cutoffRows u (dyadicMomentOrder j),
      cutoffMultiplier (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
        (dyadicMomentOrder j) pb.1 pb.2*∑ d ∈ Finset.Icc (ZetaRieszFineDivisorRows.lower (dyadicMomentOrder j) pb.1 pb.2)
        (ZetaRieszFineDivisorRows.upper (dyadicMomentOrder j) pb.1 pb.2),
        if pb.1*(pb.2*d) ∈ ZetaRieszParityPacket.coreBand u
            (dyadicMomentOrder j) (dyadicPrimeCount j)
          then rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
            (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
            y pb.1 pb.2 d else 0) = cutoffLiteralRows u y j+cutoffEndpointRows u y j := by
  simp only [cutoffLiteralRows,cutoffEndpointRows,coreRow]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pb hpb
  have hlu := (row_data hpb).2.2
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


/-- Literal full closed-row packet: the original count/core selection,
common factorial phase and owner allocation remain inside each block. -/
def literalCutoffPacket (u y : ℝ) (j : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  ∑ pb ∈ cutoffRows u N,
    ∑ e ∈ Finset.Icc (lower N pb.1 pb.2) (upper N pb.1 pb.2),
      if pb.1*(pb.2*e) ∈ ZetaRieszParityPacket.coreBand u N (dyadicPrimeCount j) then
        ∑ δ ∈ cutoffDivisors N pb.1 pb.2,
          (phaseWeight (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (pb.1*(pb.2*e))})
            L N y (pb.2*e) pb.1).re*(μ (pb.2/δ) : ℝ)*pairHinge L pb.1 (pb.2/δ)*
              sieve (pb.1*pb.2).primeFactors e
      else 0

/-- Exact bridge, before any norm: the clipped divisor block is summed
at the SAME original product label and with every original mask. -/
theorem literalCutoffPacket_eq_rows (u y : ℝ) (j : ℕ) :
    literalCutoffPacket u y j = cutoffLiteralRows u y j+cutoffEndpointRows u y j := by
  rw [← cutoff_rows_closed_eq]
  unfold literalCutoffPacket
  dsimp only
  apply Finset.sum_congr rfl
  intro pb hpb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  obtain ⟨_,hs,_,_,hH,_,_,_,_,h6,_,_⟩ := Finset.mem_filter.mp hpb
  by_cases hcore : pb.1*(pb.2*e) ∈ ZetaRieszParityPacket.coreBand u
      (dyadicMomentOrder j) (dyadicPrimeCount j)
  · simp only [if_pos hcore]
    exact (cutoff_row_atom_eq _ hs h6 hH).symm
  · simp only [if_neg hcore,mul_zero]

/-- Concrete independent signed estimate on the ORIGINAL finite prime
and divisor sum, not a density model or a conditional sieve hypothesis. -/
theorem eventually_literalCutoffPacket_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop,
      |u^(dyadicMomentOrder j+1)*literalCutoffPacket u y j| ≤
        4*edgeRowBudget y (dyadicMomentOrder j)+cutoffEndpointBudget (dyadicMomentOrder j) := by
  filter_upwards [eventually_abs_cutoffLiteralRows_bound hu hU hy,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (32 : ℕ)),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
        (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source))] with j hm hN hl
  have hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by nlinarith only [hl]
  rw [literalCutoffPacket_eq_rows,mul_add]
  exact (abs_add_le _ _).trans (add_le_add hm
    (source_scaled_cutoffEndpointRows_bound (by linarith : 0 ≤ u) hU y j hN hL))

/-- This signed boundary population is independently source-o(1).
No zeta-zero or exposed-mode premise enters. -/
theorem tendsto_literalCutoffPacket {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*literalCutoffPacket u y j) atTop (𝓝 0) := by
  simpa only [literalCutoffPacket_eq_rows,mul_add,zero_add] using
    (tendsto_cutoffLiteralRows hu hU hy).add (tendsto_cutoffEndpointRows hu hU y)

private theorem closed_row_data {u : ℝ} {N : ℕ} (hN : 32 ≤ N) {pb : ℕ×ℕ}
    (hr : pb ∈ cutoffRows u N) {e : ℕ}
    (he : e ∈ Finset.Icc (lower N pb.1 pb.2) (upper N pb.1 pb.2))
    (hs : sieve (pb.1*pb.2).primeFactors e ≠ 0) :
    Squarefree (pb.1*(pb.2*e)) ∧
      ZetaRieszPrimeEndpoint.largestPrime (pb.1*(pb.2*e))=pb.1 ∧ e.Coprime 6 := by
  have hg := cutoff_row_geometry hr
  have hlarge : exp ((N : ℝ)/2016) ≤ (e : ℝ) :=
    (row_large hr).trans (by exact_mod_cast (Finset.mem_Icc.mp he).1)
  have he1 : 1 < e := by
    have ha := add_one_le_exp ((N : ℝ)/2016)
    have hn : (32 : ℝ)≤N := by exact_mod_cast hN
    have hx : (1 : ℝ)<e := by linarith
    exact_mod_cast hx
  have hc := closed_row_cofactor_geometry hg he he1 hs
  have hown := ZetaRieszPrimeIntervals.largestPrime_mul pb.1 (pb.2*e)
    hg.1 hc.1.ne_zero hc.2.2
  have houter : Squarefree (pb.1*pb.2) := Nat.squarefree_mul_iff.mpr
    ⟨hg.1.coprime_iff_not_dvd.mpr hg.2.2.2.1,hg.1.squarefree,hg.2.2.1⟩
  have hn : Squarefree ((pb.1*pb.2)*e) := by
    rw [sieve_eq_product_squarefree houter] at hs
    split_ifs at hs with h
    · exact h
    · contradiction
  have hcop := (Nat.squarefree_mul_iff.mp hn).1
  obtain ⟨_,_,_,_,_,_,_,_,_,h6,_,_⟩ := Finset.mem_filter.mp hr
  have h6outer : 6 ∣ pb.1*pb.2 := h6.trans (dvd_mul_left _ _)
  exact ⟨by simpa only [mul_assoc] using hn,hown,hcop.symm.of_dvd_right h6outer⟩

/-- Every nonzero summand is a genuine original squarefree incidence.
The gcd tag makes the marked block uniquely recoverable. -/
theorem cutoff_original_incidence {u : ℝ} {N : ℕ} (hN : 32 ≤ N) {pb : ℕ×ℕ}
    (hr : pb ∈ cutoffRows u N) {e δ : ℕ}
    (he : e ∈ Finset.Icc (lower N pb.1 pb.2) (upper N pb.1 pb.2))
    (hs : sieve (pb.1*pb.2).primeFactors e ≠ 0)
    (hδ : δ ∈ cutoffDivisors N pb.1 pb.2) :
    Squarefree (pb.1*(pb.2*e)) ∧
      ZetaRieszPrimeEndpoint.largestPrime (pb.1*(pb.2*e))=pb.1 ∧
      (e*δ,pb.2/δ) ∈ ((pb.1*(pb.2*e))/ZetaRieszPrimeEndpoint.largestPrime
        (pb.1*(pb.2*e))).divisorsAntidiagonal ∧
      Nat.gcd (e*δ) 6=δ ∧
      (3899/2000 : ℝ)*N < log (pb.1*(pb.2/δ) : ℕ) := by
  have hc := closed_row_data hN hr he hs
  have hd6 := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hδ).1
  obtain ⟨_,hB,_,_,_,_,_,_,_,h6,_,_⟩ := Finset.mem_filter.mp hr
  have hdB := hd6.trans h6
  have hprod : (e*δ)*(pb.2/δ)=pb.2*e := by
    calc
      _ = e*(δ*(pb.2/δ)) := by ac_rfl
      _ = _ := by rw [Nat.mul_div_cancel' hdB]; ac_rfl
  have hb0 := Nat.pos_of_ne_zero hB.ne_zero
  have hd0 := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hδ).1
  have hq0 : 0 < pb.2/δ := Nat.div_pos (Nat.le_of_dvd hb0 hdB) hd0
  have hp := ((ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp (row_owner_mem hr)).1
  have he0 : 0 < e := by have := (Finset.mem_Icc.mp he).1; exact (cutoff_row_geometry hr).2.2.2.2.2.2.1.trans_le this
  have hlog : log (pb.1*pb.2 : ℕ)=log (pb.1*(pb.2/δ) : ℕ)+log δ := by
    conv_lhs => rw [← Nat.mul_div_cancel' hdB]
    rw [show pb.1*(δ*(pb.2/δ))=(pb.1*(pb.2/δ))*δ by ac_rfl,Nat.cast_mul,
      log_mul (by exact_mod_cast (Nat.mul_pos hp.pos hq0).ne') (by exact_mod_cast hd0.ne')]
  refine ⟨hc.1,hc.2.1,?_,Nat.gcd_mul_of_coprime_of_dvd hc.2.2 hd6,?_⟩
  · rw [hc.2.1,Nat.mul_div_cancel_left _ hp.pos]
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨hprod,(Nat.mul_pos hb0 he0).ne'⟩
  · have hh := (Finset.mem_filter.mp hδ).2
    rw [hlog] at hh
    linarith

/-- No marked divisor incidence is duplicated by the frozen-block sum.
The canonical owner and gcd tag determine all three original indices. -/
theorem cutoff_incidence_injective {u : ℝ} {N : ℕ} (hN : 32 ≤ N)
    {pb pc : ℕ×ℕ} (hr : pb ∈ cutoffRows u N) (hc : pc ∈ cutoffRows u N)
    {e f δ ζ : ℕ}
    (he : e ∈ Finset.Icc (lower N pb.1 pb.2) (upper N pb.1 pb.2))
    (hf : f ∈ Finset.Icc (lower N pc.1 pc.2) (upper N pc.1 pc.2))
    (hs : sieve (pb.1*pb.2).primeFactors e ≠ 0)
    (ht : sieve (pc.1*pc.2).primeFactors f ≠ 0)
    (hd : δ ∈ cutoffDivisors N pb.1 pb.2) (hz : ζ ∈ cutoffDivisors N pc.1 pc.2)
    (hv : (pb.1*(pb.2*e),(e*δ,pb.2/δ))=(pc.1*(pc.2*f),(f*ζ,pc.2/ζ))) :
    pb=pc ∧ e=f ∧ δ=ζ := by
  have hl := cutoff_original_incidence hN hr he hs hd
  have hh := cutoff_original_incidence hN hc hf ht hz
  have hp : pb.1=pc.1 := by
    have hw := congrArg ZetaRieszPrimeEndpoint.largestPrime (congrArg Prod.fst hv)
    simpa only [hl.2.1,hh.2.1] using hw
  have hdf := congrArg (fun v : ℕ×(ℕ×ℕ) => v.2.1) hv
  have hδζ : δ=ζ := hl.2.2.2.1.symm.trans
    ((congrArg (fun d => Nat.gcd d 6) hdf).trans hh.2.2.2.1)
  have hb : pb.2=pc.2 := by
    have hvb := congrArg (fun v : ℕ×(ℕ×ℕ) => v.2.2) hv
    change pb.2/δ=pc.2/ζ at hvb
    rw [hδζ] at hvb
    have hdB := (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1).trans
      (Finset.mem_filter.mp hr).2.2.2.2.2.2.2.2.2.1
    have hzC := (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hz).1).trans
      (Finset.mem_filter.mp hc).2.2.2.2.2.2.2.2.2.1
    calc
      pb.2 = δ*(pb.2/δ) := (Nat.mul_div_cancel' hdB).symm
      _ = ζ*(pc.2/ζ) := by rw [hδζ,hvb]
      _ = pc.2 := Nat.mul_div_cancel' hzC
  refine ⟨Prod.ext hp hb,?_,hδζ⟩
  rw [hδζ] at hdf
  exact Nat.mul_right_cancel (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hz).1) hdf

/-- The log(6) strip fits the proved counting gap eventually; it is not
silently discarded from the literal selection. -/
theorem eventually_cutoff_strip_gap :
    ∀ᶠ N : ℕ in atTop, (3899/2000 : ℝ)*N+log 6 ≤ ((39/20 : ℝ)-1/2016)*N := by
  have ht := tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (252000*log 6 : ℝ))
  filter_upwards [ht] with N hN
  nlinarith

/-- One smaller signed rest. Existing shared payments are charged once;
only the independently paid literal crossing packet is newly removed. -/
def cutoffRemaining (u y : ℝ) (j : ℕ) : ℝ :=
  ZetaRieszOwnerGapRows.ownerGapRemaining u y j-literalCutoffPacket u y j

/-- Exact independent whole-carrier comparison after paying the crossing.
This DOES NOT assert the still-open numerical -79/1000 floor. -/
theorem tendsto_joined_re_sub_cutoffRemaining {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*
      ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
        cutoffRemaining u y j)) atTop (𝓝 0) := by
  have ht := (ZetaRieszOwnerGapRows.tendsto_joined_re_sub_ownerGapRemaining hu hU hy).add
    (tendsto_literalCutoffPacket hu hU hy)
  simp only [zero_add] at ht
  convert ht using 1
  ext j
  unfold cutoffRemaining
  ring

/-- A selected crossing incidence is outside every older owner-gap row.
Thus its new payment cannot spend an existing row credit twice. -/
theorem cutoff_incidence_not_ownerGapRows {u : ℝ} {N : ℕ} (hN : 32 ≤ N)
    {pb : ℕ×ℕ} (hr : pb ∈ cutoffRows u N) {e δ : ℕ}
    (he : e ∈ Finset.Icc (lower N pb.1 pb.2) (upper N pb.1 pb.2))
    (hs : sieve (pb.1*pb.2).primeFactors e ≠ 0)
    (hδ : δ ∈ cutoffDivisors N pb.1 pb.2) :
    (pb.1,pb.2/δ) ∉ ZetaRieszOwnerGapRows.ownerGapRows u N := by
  have hx := (cutoff_original_incidence hN hr he hs hδ).2.2.2.2
  intro hpaid
  have hl := (Finset.mem_filter.mp hpaid).2.2.2.2.2.1
  exact (not_lt_of_ge hl) hx

/-- An explicit sufficient owner cone covers the whole fixed-block
short-cutoff strip, independently of the prime count. -/
theorem cutoff_ownership_gap {N p B : ℕ} (hN : 0 < N)
    (hc : (3899/2000 : ℝ)*N < log (p*B : ℕ))
    (hp : (81/1000 : ℝ)*N ≤ log p) :
    (203/100 : ℝ)*N < log (p*B : ℕ)+log p := by
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  linarith

/-- All old shared costs occur once, plus one new signed crossing cost. -/
def cutoffErrorBudget (y : ℝ) (N : ℕ) : ℝ :=
  ZetaRieszOwnerGapRows.ownerGapErrorBudget y N+4*edgeRowBudget y N+cutoffEndpointBudget N

theorem tendsto_cutoffErrorBudget (y : ℝ) :
    Tendsto (cutoffErrorBudget y) atTop (𝓝 0) := by
  have ht := ((ZetaRieszOwnerGapRows.tendsto_ownerGapErrorBudget y).add
    ((tendsto_edgeRowBudget y).const_mul 4)).add tendsto_cutoffEndpointBudget
  simp only [mul_zero,zero_add] at ht
  convert ht using 1
  ext N
  rfl

/-- Independent quantitative comparison to the smaller joined signed rest. -/
theorem eventually_abs_joined_sub_cutoffRemaining_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop,
      |u^(dyadicMomentOrder j+1)*
        ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
          cutoffRemaining u y j)| ≤ cutoffErrorBudget y (dyadicMomentOrder j) := by
  filter_upwards [ZetaRieszOwnerGapRows.eventually_abs_joined_sub_ownerGapRemaining_bound hu hU hy,
    eventually_literalCutoffPacket_bound hu hU hy] with j hbase hnew
  unfold cutoffRemaining
  rw [show u^(dyadicMomentOrder j+1)*
      ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
        (ZetaRieszOwnerGapRows.ownerGapRemaining u y j-literalCutoffPacket u y j)) =
      u^(dyadicMomentOrder j+1)*
        ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
          ZetaRieszOwnerGapRows.ownerGapRemaining u y j)+
        u^(dyadicMomentOrder j+1)*literalCutoffPacket u y j by ring]
  exact ((abs_add_le _ _).trans (add_le_add hbase hnew)).trans_eq (by unfold cutoffErrorBudget; ring)

/-- Whole-carrier floor comparison. The numerical floor for the remaining
signed scalar is still an independent OPEN arithmetic theorem. -/
theorem eventually_joined_floor_with_cutoffRemaining {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop,
      u^(dyadicMomentOrder j+1)*cutoffRemaining u y j-
        cutoffErrorBudget y (dyadicMomentOrder j) ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_abs_joined_sub_cutoffRemaining_bound hu hU hy] with j hj
  have h := (abs_le.mp hj).1
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  nlinarith

private theorem leastPairBlock_eq_six {a : ℕ} (ha : Squarefree a) (h6 : 6 ∣ a) :
    ZetaRieszShortDivisorCancellation.leastPairBlock a=6 := by
  have h2 : 2 ∣ a := (by norm_num : 2 ∣ 6).trans h6
  have hm := (Nat.minFac_eq_two_iff a).mpr h2
  have h3 : 3 ∣ a/2 := (Nat.dvd_div_iff_mul_dvd h2).mpr (by simpa using h6)
  have hco : (2 : ℕ).Coprime (a/2) := Nat.coprime_of_squarefree_mul
    ((Nat.mul_div_cancel' h2).symm ▸ ha)
  have hn2 : ¬2 ∣ a/2 := (Nat.prime_two.coprime_iff_not_dvd.mp hco)
  have hq1 : a/2 ≠ 1 := by intro hh; rw [hh] at h3; norm_num at h3
  have hpq := Nat.minFac_prime hq1
  have hmin3 := Nat.minFac_le_of_dvd (by norm_num : 2 ≤ 3) h3
  have hmn2 : (a/2).minFac ≠ 2 := by
    intro hh
    have hd := Nat.minFac_dvd (a/2)
    rw [hh] at hd
    exact hn2 hd
  have hmq : (a/2).minFac=3 := by have := hpq.two_le; omega
  norm_num [ZetaRieszShortDivisorCancellation.leastPairBlock,hm,hmq]

/-- The clipped cutoff packet cannot break any previously cancelled
complete affine orbit. Its canonical small block is 6, and its base sits
on the complementary side of the strict complete-orbit cutoff. -/
theorem cutoff_incidence_not_cancelledOrbit {u : ℝ} {N : ℕ} (hN : 32 ≤ N)
    {pb : ℕ×ℕ} (hr : pb ∈ cutoffRows u N) {e δ : ℕ}
    (he : e ∈ Finset.Icc (lower N pb.1 pb.2) (upper N pb.1 pb.2))
    (hs : sieve (pb.1*pb.2).primeFactors e ≠ 0)
    (hδ : δ ∈ cutoffDivisors N pb.1 pb.2) :
    (e*δ,pb.2/δ) ∉ ZetaRieszShortDivisorOrbits.cancelledOrbitDivisors u N
      (pb.1*(pb.2*e)) := by
  have hdata := closed_row_data hN hr he hs
  have hinc := cutoff_original_incidence hN hr he hs hδ
  have hB := (cutoff_row_geometry hr).2.2.1
  have hb0 := Nat.pos_of_ne_zero hB.ne_zero
  have he0 : 0 < e := (cutoff_row_geometry hr).2.2.2.2.2.2.1.trans_le (Finset.mem_Icc.mp he).1
  have hpa := ((ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp (row_owner_mem hr)).1
  have ha : Squarefree (pb.2*e) := (Nat.squarefree_mul_iff.mp hdata.1).2.2
  obtain ⟨_,_,_,_,_,_,_,_,_,h6,_,hcross⟩ := Finset.mem_filter.mp hr
  have h6a : 6 ∣ pb.2*e := h6.trans (dvd_mul_right _ _)
  have hR := leastPairBlock_eq_six ha h6a
  have hco6 : (6 : ℕ).Coprime ((pb.2*e)/6) := Nat.coprime_of_squarefree_mul
    ((Nat.mul_div_cancel' h6a).symm ▸ ha)
  intro hcancel
  simp only [ZetaRieszShortDivisorOrbits.cancelledOrbitDivisors,hdata.2.1,
    Nat.mul_div_cancel_left _ hpa.pos,hR] at hcancel
  split_ifs at hcancel with hvalid
  · obtain ⟨f,hf,hblock⟩ := Finset.mem_biUnion.mp hcancel
    simp only [ZetaRieszShortDivisorOrbits.orbitDivisors] at hblock
    obtain ⟨ζ,hζ,hv⟩ := Finset.mem_image.mp hblock
    have hdf : f*ζ=e*δ := congrArg Prod.fst hv
    have hfc : f.Coprime 6 := hco6.symm.of_dvd_left
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hf).1)
    have hgcd : Nat.gcd (f*ζ) 6=ζ := Nat.gcd_mul_of_coprime_of_dvd hfc
      (Nat.dvd_of_mem_divisors hζ)
    have hzδ : ζ=δ := hgcd.symm.trans
      ((congrArg (fun d => Nat.gcd d 6) hdf).trans hinc.2.2.2.1)
    have hfe : f=e := by
      rw [hzδ] at hdf
      exact Nat.mul_right_cancel (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hδ).1) hdf
    have hshort := (Finset.mem_filter.mp hf).2
    dsimp only [ZetaRieszShortDivisorOrbits.ShortOrbit] at hshort
    rw [hdata.2.1,Nat.mul_div_cancel_left _ hpa.pos] at hshort
    have hT : log (pb.1*(pb.2*e) : ℕ)=log (pb.1*pb.2 : ℕ)+log e := by
      rw [show pb.1*(pb.2*e)=(pb.1*pb.2)*e by ac_rfl,Nat.cast_mul,
        log_mul (by exact_mod_cast (Nat.mul_pos hpa.pos hb0).ne') (by exact_mod_cast he0.ne')]
    have hcut := hshort.1
    change log f+log 6 < log (pb.1*(pb.2*e) : ℕ)-(3899/2000 : ℝ)*N at hcut
    rw [hfe,hT] at hcut
    linarith
  · simp at hcancel

/-- Every original integer in the displayed fixed-block row is covered,
including the rounded lower endpoint. The counting-gap predicate stays
explicit here and is discharged eventually by `eventually_cutoff_strip_gap`. -/
theorem cutoff_literal_row_covered {u : ℝ} {N p B e : ℕ}
    (hp : p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N)
    (hB : 1 < B) (hs : Squarefree B) (hpd : ¬p ∣ B)
    (hmax : ∀ q ∈ B.primeFactors, q < p)
    (ha : pairHinge (SquarefreeVaughanLogSource.length u N) p B ≠ 0)
    (hc : log (p*B : ℕ) ≤ ((39/20 : ℝ)-1/2016)*N)
    (hP : log p < (243/200 : ℝ)*N)
    (hgap : (203/100 : ℝ)*N < log (p*B : ℕ)+log p)
    (h6 : 6 ∣ B) (hcut : (3899/2000 : ℝ)*N < log (p*B : ℕ))
    (hcross : log (p*B : ℕ) ≤ (3899/2000 : ℝ)*N+log 6)
    (hlo : (39/20 : ℝ)*N < log (p*B : ℕ)+log e)
    (hhi : log (p*B : ℕ)+log e ≤ (203/100 : ℝ)*N) :
    (p,B) ∈ cutoffRows u N ∧
      e ∈ Finset.Icc (lower N p B) (upper N p B) := by
  have hpP := ((ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp hp).1
  have hB0 : 0 < B := by omega
  have he0 : 0 < e := by
    by_contra hn
    have he : e=0 := by omega
    rw [he,Nat.cast_zero,log_zero,add_zero] at hlo
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hel : lower N p B ≤ e := by
    apply Nat.ceil_le.mpr
    have hh := exp_le_exp.mpr (by linarith : (39/20 : ℝ)*N-log (p*B : ℕ) ≤ log e)
    simpa only [exp_log (by exact_mod_cast he0 : (0 : ℝ)<e)] using hh
  have heu : e ≤ upper N p B := by
    apply Nat.le_floor
    have hh := exp_le_exp.mpr (by linarith : log e ≤ (203/100 : ℝ)*N-log (p*B : ℕ))
    simpa only [exp_log (by exact_mod_cast he0 : (0 : ℝ)<e)] using hh
  have hlog : log (p*B : ℕ)=log p+log B := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hpP.ne_zero) (by exact_mod_cast hB0.ne')]
  have hBB : B ≤ ⌊exp ((203/100 : ℝ)*N)⌋₊ := by
    apply Nat.le_floor
    have hhlog : log B ≤ (203/100 : ℝ)*N := by
      rw [hlog] at hhi
      linarith [log_natCast_nonneg p,log_natCast_nonneg e]
    have hh := exp_le_exp.mpr hhlog
    simpa only [exp_log (by exact_mod_cast hB0 : (0 : ℝ)<B)] using hh
  exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨hp,Finset.mem_Icc.mpr ⟨by omega,hBB⟩⟩,hs,hpd,hmax,ha,hc,hP,hgap,
      hel.trans heu,h6,hcut,hcross⟩,Finset.mem_Icc.mpr ⟨hel,heu⟩⟩

/-- Reverse coverage of an ORIGINAL nonzero based-block crossing. Every
core/count/physical predicate stays on p*B*e. Whole-row ownership is the
explicit geometric hypothesis; no pointwise ownership condition is used
as a substitute for it. -/
theorem cutoff_crossing_covered {u : ℝ} {N K p B e δ : ℕ}
    (hn : p*(B*e) ∈ ZetaRieszParityPacket.coreBand u N K)
    (hs : Squarefree (p*(B*e)))
    (hp : p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N)
    (howner : ZetaRieszPrimeEndpoint.largestPrime (p*(B*e))=p)
    (h6 : 6 ∣ B) (hδ : δ ∈ (6 : ℕ).divisors)
    (hshort : log (e*δ : ℕ) < log (p*(B*e) : ℕ)-(3899/2000 : ℝ)*N)
    (hcross : log (p*(B*e) : ℕ)-(3899/2000 : ℝ)*N ≤ log e+log 6)
    (hgap : (203/100 : ℝ)*N < log (p*B : ℕ)+log p)
    (hP : log p < (243/200 : ℝ)*N)
    (hsmall : (3899/2000 : ℝ)*N+log 6 ≤ ((39/20 : ℝ)-1/2016)*N)
    (hH : pairHinge (SquarefreeVaughanLogSource.length u N) p (B/δ) ≠ 0) :
    (p,B) ∈ cutoffRows u N ∧ e ∈ Finset.Icc (lower N p B) (upper N p B) ∧
      δ ∈ cutoffDivisors N p B ∧ sieve (p*B).primeFactors e=1 := by
  have hpP := ((ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp hp).1
  have hsq := Nat.squarefree_mul_iff.mp hs
  have hco := Nat.squarefree_mul_iff.mp hsq.2.2
  have hB := hco.2.1
  have he := hco.2.2
  have hB0 := Nat.pos_of_ne_zero hB.ne_zero
  have he0 := Nat.pos_of_ne_zero he.ne_zero
  have hδ0 := Nat.pos_of_mem_divisors hδ
  have hδB := (Nat.dvd_of_mem_divisors hδ).trans h6
  have hq0 : 0 < B/δ := Nat.div_pos (Nat.le_of_dvd hB0 hδB) hδ0
  have hpd : ¬p ∣ B := hpP.coprime_iff_not_dvd.mp
    (hsq.1.of_dvd_right (dvd_mul_right B e))
  have hpn : p ∈ (p*(B*e)).primeFactors := Nat.mem_primeFactors.mpr
    ⟨hpP,dvd_mul_right _ _,hs.ne_zero⟩
  have hne : (p*(B*e)).primeFactors.Nonempty := ⟨p,hpn⟩
  have hmax' : (p*(B*e)).primeFactors.max' hne=p := by
    simpa only [ZetaRieszPrimeEndpoint.largestPrime,dif_pos hne] using howner
  have hmax q (hq : q ∈ B.primeFactors) : q < p := by
    have hd : B ∣ p*(B*e) := (dvd_mul_right B e).trans (dvd_mul_left _ _)
    have hqn := Nat.primeFactors_mono hd hs.ne_zero hq
    have hle := (Finset.le_max' _ q hqn).trans_eq hmax'
    have hneq : q ≠ p := by
      intro hh
      rw [hh] at hq
      exact hpd (Nat.dvd_of_mem_primeFactors hq)
    exact lt_of_le_of_ne hle hneq
  have hlog : log (p*(B*e) : ℕ)=log (p*B : ℕ)+log e := by
    rw [show p*(B*e)=(p*B)*e by ac_rfl,Nat.cast_mul,
      log_mul (by exact_mod_cast (Nat.mul_pos hpP.pos hB0).ne') (by exact_mod_cast he0.ne')]
  have hdcut := (short_cutoff_iff hpP.pos hB0 he0 hδ0).mp hshort
  have hc : (3899/2000 : ℝ)*N < log (p*B : ℕ) := by
    linarith [log_natCast_nonneg δ]
  have hcup : log (p*B : ℕ) ≤ (3899/2000 : ℝ)*N+log 6 := by
    rw [hlog] at hcross
    linarith
  have ha : pairHinge (SquarefreeVaughanLogSource.length u N) p B ≠ 0 := by
    intro hz
    have hm := pairHinge_mono (p := p) (L := SquarefreeVaughanLogSource.length u N)
      (log_le_log (by exact_mod_cast hq0) (by exact_mod_cast Nat.div_le_self B δ))
    rw [hz] at hm
    exact hH (le_antisymm hm (pairHinge_bounds _ _ _).1)
  have hw := (Finset.mem_filter.mp hn).2
  rw [hlog] at hw
  have hrow := cutoff_literal_row_covered hp
    (by have := Nat.le_of_dvd hB0 h6; omega) hB hpd hmax ha
    (hcup.trans hsmall) hP hgap h6 hc hcup hw.1 hw.2
  refine ⟨hrow.1,hrow.2,Finset.mem_filter.mpr ⟨hδ,hdcut⟩,?_⟩
  have houter : Squarefree (p*B) := Nat.squarefree_mul_iff.mpr
    ⟨hpP.coprime_iff_not_dvd.mpr hpd,hpP.squarefree,hB⟩
  rw [sieve_eq_product_squarefree houter]
  have hsq' : Squarefree ((p*B)*e) := by simpa only [mul_assoc] using hs
  simp only [if_pos hsq']

/-- Low total count forces the whole-window owner gap, so every such
fixed-block crossing belongs to the SAME paid all-count packet. This is
coverage, not an independent norm bound on a count-truncated subpacket. -/
theorem cutoff_crossing_covered_of_count_le {u : ℝ} {N K p B e δ : ℕ}
    (hn : p*(B*e) ∈ ZetaRieszParityPacket.coreBand u N K)
    (hs : Squarefree (p*(B*e)))
    (hp : p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N)
    (howner : ZetaRieszPrimeEndpoint.largestPrime (p*(B*e))=p)
    (h6 : 6 ∣ B) (hδ : δ ∈ (6 : ℕ).divisors)
    (hshort : log (e*δ : ℕ) < log (p*(B*e) : ℕ)-(3899/2000 : ℝ)*N)
    (hcross : log (p*(B*e) : ℕ)-(3899/2000 : ℝ)*N ≤ log e+log 6)
    (hP : log p < (243/200 : ℝ)*N)
    (hsmall : (3899/2000 : ℝ)*N+log 6 ≤ ((39/20 : ℝ)-1/2016)*N)
    (hH : pairHinge (SquarefreeVaughanLogSource.length u N) p (B/δ) ≠ 0)
    (hcount : (p*(B*e)).primeFactors.card ≤ 24) :
    (p,B) ∈ cutoffRows u N ∧ e ∈ Finset.Icc (lower N p B) (upper N p B) ∧
      δ ∈ cutoffDivisors N p B ∧ sieve (p*B).primeFactors e=1 := by
  have hpP := ((ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp hp).1
  have hsq := Nat.squarefree_mul_iff.mp hs
  have hco := Nat.squarefree_mul_iff.mp hsq.2.2
  have hB0 := Nat.pos_of_ne_zero hco.2.1.ne_zero
  have he0 := Nat.pos_of_ne_zero hco.2.2.ne_zero
  have hcc := ZetaRieszJointPrimeEnergy.core_count hn
  have hne : (p*(B*e)).primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  have hmax : (p*(B*e)).primeFactors.max' hne=p := by
    simpa only [ZetaRieszPrimeEndpoint.largestPrime,dif_pos hne] using howner
  have hlogcount : log (p*(B*e) : ℕ) ≤ (24 : ℝ)*log p := by
    calc
      _ = ∑ q ∈ (p*(B*e)).primeFactors, log q :=
        CoprimeEulerPhase.squarefree_log_eq_prime_sum hs
      _ ≤ ∑ q ∈ (p*(B*e)).primeFactors, log p := by
        apply Finset.sum_le_sum
        intro q hq
        exact log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos)
          (by exact_mod_cast (Finset.le_max' _ q hq).trans_eq hmax)
      _ = ((p*(B*e)).primeFactors.card : ℝ)*log p := by simp
      _ ≤ 24*log p := mul_le_mul_of_nonneg_right (by exact_mod_cast hcount)
        (log_natCast_nonneg p)
  have hlo := (Finset.mem_filter.mp hn).2.1
  have hcp : (3899/2000 : ℝ)*N < log (p*B : ℕ) := by
    have hdcut := (short_cutoff_iff hpP.pos hB0 he0 (Nat.pos_of_mem_divisors hδ)).mp hshort
    linarith [log_natCast_nonneg δ]
  have hgap : (203/100 : ℝ)*N < log (p*B : ℕ)+log p := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  exact cutoff_crossing_covered hn hs hp howner h6 hδ hshort hcross hgap hP hsmall hH

/-- After the independent all-count payment, every still-unselected
nonzero 6-block cutoff crossing has at least 25 prime factors, under the
original owner ceiling and masks. No numerical floor is inferred. -/
theorem eventually_unpaid_six_crossing_count_gt (u : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ K p B e δ : ℕ,
      p*(B*e) ∈ ZetaRieszParityPacket.coreBand u N K →
      Squarefree (p*(B*e)) → p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N →
      ZetaRieszPrimeEndpoint.largestPrime (p*(B*e))=p →
      6 ∣ B → δ ∈ (6 : ℕ).divisors →
      log (e*δ : ℕ) < log (p*(B*e) : ℕ)-(3899/2000 : ℝ)*N →
      log (p*(B*e) : ℕ)-(3899/2000 : ℝ)*N ≤ log e+log 6 →
      log p < (243/200 : ℝ)*N →
      pairHinge (SquarefreeVaughanLogSource.length u N) p (B/δ) ≠ 0 →
      (p,B) ∉ cutoffRows u N → 24 < (p*(B*e)).primeFactors.card := by
  filter_upwards [eventually_cutoff_strip_gap] with N hsmall
  intro K p B e δ hn hs hp howner h6 hδ hshort hcross hP hH hnot
  by_contra hcount
  exact hnot (cutoff_crossing_covered_of_count_le hn hs hp howner h6 hδ hshort
    hcross hP hsmall hH (le_of_not_gt hcount)).1

/-- The precise surviving fixed-block cutoff geometry: below the old
paid owner ceiling, an unselected nonzero crossing has a very small owner
AND high count. These are support restrictions, not a bound on its cost. -/
theorem eventually_unpaid_six_crossing_geometry (u : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ K p B e δ : ℕ,
      p*(B*e) ∈ ZetaRieszParityPacket.coreBand u N K →
      Squarefree (p*(B*e)) → p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N →
      ZetaRieszPrimeEndpoint.largestPrime (p*(B*e))=p →
      6 ∣ B → δ ∈ (6 : ℕ).divisors →
      log (e*δ : ℕ) < log (p*(B*e) : ℕ)-(3899/2000 : ℝ)*N →
      log (p*(B*e) : ℕ)-(3899/2000 : ℝ)*N ≤ log e+log 6 →
      log p < (243/200 : ℝ)*N →
      pairHinge (SquarefreeVaughanLogSource.length u N) p (B/δ) ≠ 0 →
      (p,B) ∉ cutoffRows u N →
      log p < (161/2000 : ℝ)*N ∧ 24 < (p*(B*e)).primeFactors.card := by
  filter_upwards [eventually_cutoff_strip_gap,eventually_unpaid_six_crossing_count_gt u]
    with N hsmall hcount
  intro K p B e δ hn hs hp howner h6 hδ hshort hcross hP hH hnot
  refine ⟨?_,hcount K p B e δ hn hs hp howner h6 hδ hshort hcross hP hH hnot⟩
  have hpP := ((ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp hp).1
  have hsq := Nat.squarefree_mul_iff.mp hs
  have hco := Nat.squarefree_mul_iff.mp hsq.2.2
  have hdcut := (short_cutoff_iff hpP.pos (Nat.pos_of_ne_zero hco.2.1.ne_zero)
    (Nat.pos_of_ne_zero hco.2.2.ne_zero) (Nat.pos_of_mem_divisors hδ)).mp hshort
  have hc : (3899/2000 : ℝ)*N < log (p*B : ℕ) := by
    linarith [log_natCast_nonneg δ]
  by_contra hl
  have hgap : (203/100 : ℝ)*N < log (p*B : ℕ)+log p := by
    have hh := le_of_not_gt hl
    linarith
  exact hnot (cutoff_crossing_covered hn hs hp howner h6 hδ hshort hcross hgap hP hsmall hH).1

private theorem saturated_hinge {L : ℝ} {p b : ℕ} (hL : L ≤ log b) :
    pairHinge L p b=log p := by
  unfold pairHinge
  rw [max_eq_right (by linarith [log_natCast_nonneg p] : 0 ≤ log p+log b-L),
    max_eq_right (by linarith : 0 ≤ log b-L)]
  ring

/-- Inside the middle of the exact cutoff strip, ONLY divisors 1 and 2
survive. The upper endpoint is closed because the literal cutoff is strict. -/
theorem cutoffDivisors_eq_pair {N p B : ℕ}
    (hlo : log 2 < log (p*B : ℕ)-(3899/2000 : ℝ)*N)
    (hhi : log (p*B : ℕ)-(3899/2000 : ℝ)*N ≤ log 3) :
    cutoffDivisors N p B={1,2} := by
  have hd : (6 : ℕ).divisors={1,2,3,6} := by decide
  have h1 : log (1 : ℕ) < log (p*B : ℕ)-(3899/2000 : ℝ)*N := by
    simp only [Nat.cast_one,log_one]
    linarith [log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have h3 : ¬log (3 : ℕ) < log (p*B : ℕ)-(3899/2000 : ℝ)*N := not_lt_of_ge hhi
  have h6 : ¬log (6 : ℕ) < log (p*B : ℕ)-(3899/2000 : ℝ)*N :=
    not_lt_of_ge (hhi.trans (log_le_log (by norm_num) (by norm_num : (3 : ℝ) ≤ 6)))
  ext δ
  simp only [cutoffDivisors,hd,Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨hδ,hcut⟩
    rcases hδ with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (h3 hcut).elim
    · exact (h6 hcut).elim
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl,h1⟩
    · exact ⟨Or.inr (Or.inl rfl),hlo⟩

/-- Exact cancellation of the clipped middle block before any norm.
All original common factorial, allocation and phase weights may be w;
no whole-row ownership or counting estimate is needed. -/
theorem clipped_middle_block_eq_zero {N p B : ℕ} {L : ℝ} (hB : Squarefree B)
    (h6 : 6 ∣ B) (hL : L ≤ log (B/2 : ℕ))
    (hlo : log 2 < log (p*B : ℕ)-(3899/2000 : ℝ)*N)
    (hhi : log (p*B : ℕ)-(3899/2000 : ℝ)*N ≤ log 3) (w : ℂ) :
    (∑ δ ∈ cutoffDivisors N p B,
      w*(μ (B/δ) : ℂ)*(pairHinge L p (B/δ) : ℂ))=0 := by
  have h2B : 2 ∣ B := (by norm_num : 2 ∣ 6).trans h6
  have hB0 := Nat.pos_of_ne_zero hB.ne_zero
  have hq0 : 0 < B/2 := Nat.div_pos (Nat.le_of_dvd hB0 h2B) (by norm_num)
  have hLB : L ≤ log B := hL.trans
    (log_le_log (by exact_mod_cast hq0) (by exact_mod_cast Nat.div_le_self B 2))
  have hm : (μ (B/2) : ℂ)=-(μ B : ℂ) := by
    have hr := moebius_cofactor_real hB h2B
    rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two] at hr
    norm_num at hr
    exact_mod_cast hr
  rw [cutoffDivisors_eq_pair hlo hhi]
  simp only [Finset.sum_insert (by norm_num : (1 : ℕ) ∉ {2}),Finset.sum_singleton,
    Nat.div_one,saturated_hinge hLB,saturated_hinge hL,hm]
  ring

/-- The tiny-owner remainder automatically saturates both surviving
hinges. Its middle cutoff substrip therefore has EXACTLY zero signed
cost at every height and count, even when unsigned integers exceed p. -/
theorem small_owner_middle_block_eq_zero {u : ℝ} (hu : 1/2 ≤ u) {N p B : ℕ}
    (hN : 32 ≤ N) (hp : p.Prime) (hB : Squarefree B) (h6 : 6 ∣ B)
    (hP : log p ≤ (161/2000 : ℝ)*N)
    (hlo : log 2 < log (p*B : ℕ)-(3899/2000 : ℝ)*N)
    (hhi : log (p*B : ℕ)-(3899/2000 : ℝ)*N ≤ log 3) (w : ℂ) :
    (∑ δ ∈ cutoffDivisors N p B, w*(μ (B/δ) : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) p (B/δ) : ℂ))=0 := by
  have h2B : 2 ∣ B := (by norm_num : 2 ∣ 6).trans h6
  have hB0 := Nat.pos_of_ne_zero hB.ne_zero
  have hq0 : 0 < B/2 := Nat.div_pos (Nat.le_of_dvd hB0 h2B) (by norm_num)
  have hprod : log (p*B : ℕ)=log p+log B := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hB0.ne')]
  have hquot : log B=log 2+log (B/2 : ℕ) := by
    conv_lhs => rw [← Nat.mul_div_cancel' h2B]
    rw [Nat.cast_mul,Nat.cast_ofNat,
      log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast hq0.ne')]
  have hLu : SquarefreeVaughanLogSource.length u N ≤ (3/2 : ℝ)*N :=
    ZetaRieszCentralPair.length_le_central_lower hu (by omega)
  have hlog2 : log 2 ≤ (1 : ℝ) := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at h
    exact h
  have hn : (32 : ℝ)≤N := by exact_mod_cast hN
  apply clipped_middle_block_eq_zero hB h6 ?_ hlo hhi w
  rw [hprod,hquot] at hlo
  linarith

/-- An entire selected literal population has ZERO source-scaled complex
cost, with the original core/count mask and common product observation.
This applies to the unpaid middle strip without any ownership-gap premise
or error budget, and does not estimate its divisor terms separately. -/
theorem literal_middle_cutoff_population_eq_zero
    (I : Finset ((ℕ×ℕ)×ℕ)) {u : ℝ} (hu : 1/2 ≤ u) {N : ℕ} (hN : 32 ≤ N)
    (K : ℕ) (y : ℝ)
    (hI : ∀ v ∈ I,
      v.1.1 ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N ∧
      Squarefree (v.1.1*(v.1.2*v.2)) ∧
      ZetaRieszPrimeEndpoint.largestPrime (v.1.1*(v.1.2*v.2))=v.1.1 ∧
      6 ∣ v.1.2 ∧ log v.1.1 ≤ (161/2000 : ℝ)*N ∧
      log 2 < log (v.1.1*v.1.2 : ℕ)-(3899/2000 : ℝ)*N ∧
      log (v.1.1*v.1.2 : ℕ)-(3899/2000 : ℝ)*N ≤ log 3) :
    (u : ℂ)^(N+1)*(∑ v ∈ I,
      if v.1.1*(v.1.2*v.2) ∈ ZetaRieszParityPacket.coreBand u N K then
        ∑ δ ∈ cutoffDivisors N v.1.1 v.1.2,
          phaseWeight ((ZetaRieszAnnulusJoint.intermediatePrimes u N) ∩
              {ZetaRieszPrimeEndpoint.largestPrime (v.1.1*(v.1.2*v.2))})
            (SquarefreeVaughanLogSource.length u N) N y (v.1.2*v.2) v.1.1*
            (μ (v.1.2/δ) : ℂ)*
            (pairHinge (SquarefreeVaughanLogSource.length u N) v.1.1 (v.1.2/δ) : ℂ)
      else 0)=0 := by
  have hz : (∑ v ∈ I,
      if v.1.1*(v.1.2*v.2) ∈ ZetaRieszParityPacket.coreBand u N K then
        ∑ δ ∈ cutoffDivisors N v.1.1 v.1.2,
          phaseWeight ((ZetaRieszAnnulusJoint.intermediatePrimes u N) ∩
              {ZetaRieszPrimeEndpoint.largestPrime (v.1.1*(v.1.2*v.2))})
            (SquarefreeVaughanLogSource.length u N) N y (v.1.2*v.2) v.1.1*
            (μ (v.1.2/δ) : ℂ)*
            (pairHinge (SquarefreeVaughanLogSource.length u N) v.1.1 (v.1.2/δ) : ℂ)
      else 0)=0 := by
    apply Finset.sum_eq_zero
    intro v hv
    obtain ⟨hp,hs,howner,h6,hP,hlo,hhi⟩ := hI v hv
    by_cases hcore : v.1.1*(v.1.2*v.2) ∈ ZetaRieszParityPacket.coreBand u N K
    · rw [if_pos hcore,howner]
      have hB := (Nat.squarefree_mul_iff.mp (Nat.squarefree_mul_iff.mp hs).2.2).2.1
      exact small_owner_middle_block_eq_zero hu hN
        ((ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp hp).1 hB h6 hP hlo hhi _
    · rw [if_neg hcore]
  rw [hz,mul_zero]

end RiemannGaussian.ZetaRieszShortCutoffRows
