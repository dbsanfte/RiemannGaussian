/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCofactorDiscrepancy
import RiemannGaussian.ZetaRieszSignedConvolution
import RiemannGaussian.ZetaRieszSignedDensityMain
import RiemannGaussian.ZetaRieszPrimeWeightedSieve

set_option autoImplicit false

/-!
# A longer signed squarefree cutoff with a genuine power error

Use the convergent divisor square series at 17/16, rather than 9/8.
The unchanged signed prefix then has error X^(3/4) D^(5/16).
Thus D^4 <= X^3 gives the fixed error X^(63/64). This covers
the first translated hinge on the literal core. All mask variation and
the signed density/prime main remain explicit. No whole-carrier floor
or bilinear cancellation assumption is introduced.
-/

noncomputable section
open Real
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszLongCutoffError
open ZetaRieszCofactorDiscrepancy ZetaRieszCofactorPhaseEnergy
open ZetaRieszParityPacket ZetaRieszPrimeEndpoint

set_option maxHeartbeats 800000

private theorem corrected_mark_le {d : ℕ} (hd : Squarefree d) :
    (∏ p ∈ d.primeFactors, primeSquareCorrectedWeight (3/4) p) ≤
      (d.divisors.card : ℝ)*zetaPrimeExpWeight (3/4) d := by
  have hw p : zetaPrimeExpWeight (3/4) p ≤ 1 := by
    rw [zetaPrimeExpWeight,exp_le_one_iff]
    nlinarith [log_natCast_nonneg p]
  calc
    _ ≤ ∏ p ∈ d.primeFactors, (2 : ℝ)*zetaPrimeExpWeight (3/4) p := by
      apply Finset.prod_le_prod (fun p _ => primeSquareCorrectedWeight_nonneg _ _)
      intro p _
      unfold primeSquareCorrectedWeight
      have hp0 : 0 ≤ zetaPrimeExpWeight (3/4) p := (exp_pos _).le
      nlinarith [mul_le_mul_of_nonneg_left (hw p) hp0]
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,RoughCoprimeFactor.card_divisors_eq hd]
      congr 1
      rw [← zetaPrimeExpWeight_prod d.primeFactors
        (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos),
        Nat.prod_primeFactors_of_squarefree hd]

private theorem mark_sum_bound (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, |(μ d : ℝ)| *
      ∏ p ∈ d.primeFactors, primeSquareCorrectedWeight (3/4) p) ≤
      exp ((5/16 : ℝ)*log D)*divisorSquareDirichletMass (17/16) := by
  have ht d (hd : d ∈ Finset.Icc 1 D) :
      |(μ d : ℝ)| *(∏ p ∈ d.primeFactors, primeSquareCorrectedWeight (3/4) p) ≤
      exp ((5/16 : ℝ)*log D)*((d.divisors.card : ℝ)^2*(d : ℝ)^(-(17/16 : ℝ))) := by
    have hd0 : (0 : ℝ)<d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hl : log d ≤ log D := log_le_log hd0 (by exact_mod_cast (Finset.mem_Icc.mp hd).2)
    by_cases hs : Squarefree d
    · have hm : |(μ d : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hc : 1 ≤ d.divisors.card :=
        Finset.one_le_card.mpr ⟨1,Nat.one_mem_divisors.mpr hs.ne_zero⟩
      have hcr : (1 : ℝ) ≤ d.divisors.card := by exact_mod_cast hc
      have hdc : (d.divisors.card : ℝ) ≤ (d.divisors.card : ℝ)^2 := by nlinarith
      have hw : zetaPrimeExpWeight (3/4) d ≤
          exp ((5/16 : ℝ)*log D)*(d : ℝ)^(-(17/16 : ℝ)) := by
        rw [zetaPrimeExpWeight,rpow_def_of_pos hd0,← exp_add]
        apply exp_le_exp.mpr
        linarith
      calc
        _ ≤ (d.divisors.card : ℝ)*zetaPrimeExpWeight (3/4) d :=
          (mul_le_of_le_one_left (Finset.prod_nonneg
            (fun _ _ => primeSquareCorrectedWeight_nonneg _ _)) hm).trans
              (corrected_mark_le hs)
        _ ≤ (d.divisors.card : ℝ)^2*
            (exp ((5/16 : ℝ)*log D)*(d : ℝ)^(-(17/16 : ℝ))) :=
          mul_le_mul hdc hw (exp_pos _).le (sq_nonneg _)
        _ = _ := by ring
    · have hm : (μ d : ℝ)=0 := by
        exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs
      rw [hm,abs_zero,zero_mul]
      positivity
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D,
        exp ((5/16 : ℝ)*log D)*((d.divisors.card : ℝ)^2*(d : ℝ)^(-(17/16 : ℝ))) :=
      Finset.sum_le_sum ht
    _ = exp ((5/16 : ℝ)*log D)*(∑ d ∈ Finset.Icc 1 D,
        (d.divisors.card : ℝ)^2*(d : ℝ)^(-(17/16 : ℝ))) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_card_divisors_sq_mul_rpow_neg (by norm_num : (1 : ℝ)<17/16)).sum_le_tsum _
        (fun _ _ => by positivity)) (exp_pos _).le

/-- A finite arithmetic constant independent of both moving cutoffs. -/
def countingConstant : ℝ :=
  exp (primeSquareWeightMass (3/4))*(divisorSquareDirichletMass (17/16)+1)

theorem countingConstant_pos : 0 < countingConstant := by
  unfold countingConstant
  exact mul_pos (exp_pos _) (by linarith [divisorSquareDirichletMass_nonneg (17/16)])

/-- The SAME literal signed prefix, with a smaller divisor-cutoff loss.
No prime approximation, phase replacement or parity hypothesis occurs. -/
theorem sharp_count_error (X D : ℕ) :
    |(∑ n ∈ Finset.Icc 1 X, if Squarefree n then sharp D n else 0)-
      densityPrefix D*X| ≤
      countingConstant*(X : ℝ)^(3/4 : ℝ)*exp ((5/16 : ℝ)*log D) := by
  rw [count_eq_marks,densityPrefix,Finset.sum_mul,← Finset.sum_sub_distrib]
  have hm d : |(μ d : ℝ)*SquarefreeCounting.count d.primeFactors X-
      (μ d : ℝ)*SquarefreeCounting.density d.primeFactors*X| ≤
      (exp (primeSquareWeightMass (3/4))*(X : ℝ)^(3/4 : ℝ))*
        (|(μ d : ℝ)| *∏ p ∈ d.primeFactors, primeSquareCorrectedWeight (3/4) p) := by
    have hb := SquarefreeCounting.count_centered_bound d.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
      (by norm_num : (1/2 : ℝ)<3/4) (by norm_num : (3/4 : ℝ)≤1) X
    calc
      _ = |(μ d : ℝ)| *|SquarefreeCounting.count d.primeFactors X-
          SquarefreeCounting.density d.primeFactors*X| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_eq (by ring)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D,
        (exp (primeSquareWeightMass (3/4))*(X : ℝ)^(3/4 : ℝ))*
          (|(μ d : ℝ)| *∏ p ∈ d.primeFactors, primeSquareCorrectedWeight (3/4) p) :=
      Finset.sum_le_sum (fun d _ => hm d)
    _ = (exp (primeSquareWeightMass (3/4))*(X : ℝ)^(3/4 : ℝ))*
        (∑ d ∈ Finset.Icc 1 D, |(μ d : ℝ)| *
          ∏ p ∈ d.primeFactors, primeSquareCorrectedWeight (3/4) p) := by rw [Finset.mul_sum]
    _ ≤ (exp (primeSquareWeightMass (3/4))*(X : ℝ)^(3/4 : ℝ))*
        (exp ((5/16 : ℝ)*log D)*divisorSquareDirichletMass (17/16)) :=
      mul_le_mul_of_nonneg_left (mark_sum_bound D) (by positivity)
    _ ≤ _ := by
      unfold countingConstant
      have h : 0 ≤ exp (primeSquareWeightMass (3/4))*(X : ℝ)^(3/4 : ℝ)*
          exp ((5/16 : ℝ)*log D) := by positivity
      nlinarith only [h]

/-- A three-quarter divisor cutoff still has a fixed one-sixty-fourth
power saving. The original square-root restriction is unnecessary here. -/
theorem sharp_count_error_long {X D : ℕ} (hX : 0 < X) (hD : 0 < D)
    (hDX : D^4 ≤ X^3) :
    |(∑ n ∈ Finset.Icc 1 X, if Squarefree n then sharp D n else 0)-
      densityPrefix D*X| ≤ countingConstant*(X : ℝ)^(63/64 : ℝ) := by
  have hxr : (0 : ℝ)<X := by exact_mod_cast hX
  have hdr : (0 : ℝ)<D := by exact_mod_cast hD
  have hl : 4*log D ≤ 3*log X := by
    have h := log_le_log (pow_pos hdr 4)
      (show (D : ℝ)^4 ≤ (X : ℝ)^3 by exact_mod_cast hDX)
    simpa only [log_pow,Nat.cast_ofNat] using h
  apply (sharp_count_error X D).trans
  have hp : (X : ℝ)^(3/4 : ℝ)*exp ((5/16 : ℝ)*log D) ≤ (X : ℝ)^(63/64 : ℝ) := by
    rw [rpow_def_of_pos hxr,rpow_def_of_pos hxr,← exp_add]
    apply exp_le_exp.mpr
    linarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp countingConstant_pos.le

/-- The first translated hinge lies strictly inside the new cutoff range
on EVERY original core label. The exact physical length and
canonical largest prime are used; there is no limiting share replacement. -/
theorem core_translated_log_margin {u : ℝ} (hu : 1/2 ≤ u)
    {N K n : ℕ} (hN : 2 ≤ N) (hn : n ∈ coreBand u N K) :
    4*(SquarefreeVaughanLogSource.length u N-log (largestPrime n))+
      (N : ℝ)/4+log (largestPrime n) < 3*log (n/largestPrime n : ℕ) := by
  have hc := ZetaRieszJointPrimeEnergy.core_count hn
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have he : largestPrime n*(n/largestPrime n)=n :=
    Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
  have ha0 : n/largestPrime n ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at he
    exact (Nat.mem_primeFactors.mp hp).2.2 he.symm
  have hlog : log n=log (largestPrime n)+log (n/largestPrime n : ℕ) := by
    conv_lhs => rw [← he,Nat.cast_mul,log_mul
      (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast ha0)]
  have hlo : (39/20 : ℝ)*N < log n := (Finset.mem_filter.mp hn).2.1
  have hlen := ZetaRieszHeadOrders.length_le_two_log_two hu hN
  have htwo : log 2 ≤ (7/10 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hhi : SquarefreeVaughanLogSource.length u N ≤ (7/5 : ℝ)*N := by
    nlinarith [mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  linarith

/-- Integer divisor cutoffs below the literal translated hinge satisfy
D^4 <= a^3. This discharges the power-range premise, not mask variation. -/
theorem core_translated_cutoff {u : ℝ} (hu : 1/2 ≤ u)
    {N K n D : ℕ} (hN : 2 ≤ N) (hn : n ∈ coreBand u N K)
    (hs : Squarefree n) (hD : 0 < D)
    (hcut : (D : ℝ) ≤ exp (SquarefreeVaughanLogSource.length u N-log (largestPrime n))) :
    D^4 ≤ (n/largestPrime n)^3 := by
  have hdr : (0 : ℝ)<D := by exact_mod_cast hD
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two
    (by have := ZetaRieszJointPrimeEnergy.core_count hn; omega : 2 ≤ n.primeFactors.card)
  have ha := (ZetaRieszMarkedSaturation.cofactor_data hs
    (ZetaRieszJointPrimeEnergy.core_count hn) hp).1
  have har : (0 : ℝ)<(n/largestPrime n : ℕ) := by
    exact_mod_cast Nat.pos_of_ne_zero ha.ne_zero
  have hl : log D ≤ SquarefreeVaughanLogSource.length u N-log (largestPrime n) := by
    simpa only [log_exp] using log_le_log hdr hcut
  have hmargin := core_translated_log_margin hu hN hn
  have hg : 4*log D ≤ 3*log (n/largestPrime n : ℕ) := by
    linarith [log_natCast_nonneg (largestPrime n),Nat.cast_nonneg (α := ℝ) N]
  have hpow : (D : ℝ)^4 ≤ ((n/largestPrime n : ℕ) : ℝ)^3 := by
    rw [← exp_log (pow_pos hdr 4),← exp_log (pow_pos har 3),log_pow,log_pow]
    exact exp_le_exp.mpr (by norm_num only [Nat.cast_ofNat]; exact hg)
  exact_mod_cast hpow

private theorem core_prime_log_le {u : ℝ} {N K n p : ℕ}
    (hn : n ∈ coreBand u N K) (hp : p ∈ n.primeFactors) :
    log p ≤ SquarefreeVaughanLogSource.length u N := by
  have hcen : n ∈ ZetaRieszCentralPrimeLayers.centralUnpairedBand u N := by
    simp only [coreBand,ZetaRieszTypeII.narrowBand,LogarithmicDeviation.deviationBand,
      ZetaRieszDominantAllocation.nondominantBand,ZetaRieszMaskSupport.retainedBand,
      ZetaRieszCompanionMask.originalMask,ZetaRieszHarmonicWindow.fewBand,
      Finset.mem_filter,Finset.mem_sdiff] at hn
    tauto
  have hphys := (Finset.mem_filter.mp (Finset.mem_sdiff.mp
    (Finset.mem_filter.mp hcen).1).1).2 p hp
  have hl := log_le_log (show (0 : ℝ)<p by exact_mod_cast
      (Nat.prime_of_mem_primeFactors hp).pos)
    (show (p : ℝ) ≤ ((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) by
      exact_mod_cast hphys.le)
  simpa only [SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,
    Nat.cast_ofNat] using hl

private theorem row_log_bounds {u : ℝ} (hu : 1/2 ≤ u)
    {N K : ℕ} (hN : 2 ≤ N) (B : Finset ℕ)
    (hB : B ⊆ coreBand u N K) {a p : ℕ}
    (hr : p ∈ ZetaRieszJointPrimeEnergy.ownerRows B a) :
    4*(SquarefreeVaughanLogSource.length u N-log p)+(N : ℝ)/4+log p < 3*log a ∧
      (11/20 : ℝ)*N < log a := by
  obtain ⟨n,hn,hp⟩ := Finset.mem_image.mp hr
  obtain ⟨hn,ha⟩ := Finset.mem_filter.mp hn
  have hcore := hB hn
  change n/largestPrime n=a at ha
  have hm := core_translated_log_margin hu hN hcore
  rw [ha,hp] at hm
  refine ⟨hm,?_⟩
  have hpf := ZetaRieszOwnedCells.largestPrime_mem_of_two
    (by have := ZetaRieszJointPrimeEnergy.core_count hcore; omega : 2 ≤ n.primeFactors.card)
  have hpp := Nat.prime_of_mem_primeFactors hpf
  have he : largestPrime n*(n/largestPrime n)=n :=
    Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hpf)
  have ha0 : n/largestPrime n ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at he
    exact (Nat.mem_primeFactors.mp hpf).2.2 he.symm
  have hlog : log n=log p+log a := by
    conv_lhs => rw [← he,Nat.cast_mul,log_mul
      (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast ha0)]
    change log (largestPrime n)+log (n/largestPrime n : ℕ)=_
    rw [ha,hp]
  have hpl := core_prime_log_le hcore
    (ZetaRieszOwnedCells.largestPrime_mem_of_two
      (by have := ZetaRieszJointPrimeEnergy.core_count hcore; omega))
  rw [hp] at hpl
  have hlen := ZetaRieszHeadOrders.length_le_two_log_two hu hN
  have htwo : log 2 ≤ (7/10 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hhi : SquarefreeVaughanLogSource.length u N ≤ (7/5 : ℝ)*N := by
    nlinarith [mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hlo : (39/20 : ℝ)*N < log n := (Finset.mem_filter.mp hcore).2.1
  linarith

/-- Every nonzero jump of the ACTUAL owner column lies in the long-cutoff
range and above exp(N/2). Squarefree, count, owner and physical masks all
remain in the column; their jumps are not discarded or assumed smooth. -/
theorem literal_masked_support {u : ℝ} (hu : 1/2 ≤ u)
    {N K R : ℕ} (hN : 32 ≤ N) (B : Finset ℕ)
    (hB : B ⊆ coreBand u N K)
    (A : Finset ℕ) (y scale : ℝ) (p : ℕ) (hR : 0 < R)
    (hcut : (R : ℝ) ≤ exp (SquarefreeVaughanLogSource.length u N-log p))
    {k : ℕ} (hk : 0 < k)
    (hz : ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) (SquarefreeVaughanLogSource.length u N)
        y scale N k p ≠
      ZetaRieszJointPrimeEnergy.maskedWeight A
        (ZetaRieszJointPrimeEnergy.ownerRows B) (SquarefreeVaughanLogSource.length u N)
          y scale N (k+1) p) :
    R^4 ≤ k^3 ∧ exp ((N : ℝ)/2) ≤ k := by
  let w := fun a => ZetaRieszJointPrimeEnergy.maskedWeight A
    (ZetaRieszJointPrimeEnergy.ownerRows B) (SquarefreeVaughanLogSource.length u N)
      y scale N a p
  change w k ≠ w (k+1) at hz
  have hrow a (hw : w a ≠ 0) : p ∈ ZetaRieszJointPrimeEnergy.ownerRows B a := by
    by_contra hr
    simp [w,ZetaRieszJointPrimeEnergy.maskedWeight,hr] at hw
  have hsome : ∃ a, (a=k ∨ a=k+1) ∧ p ∈ ZetaRieszJointPrimeEnergy.ownerRows B a := by
    by_cases hw : w k=0
    · exact ⟨k+1,Or.inr rfl,hrow _ (by intro he; exact hz (hw.trans he.symm))⟩
    · exact ⟨k,Or.inl rfl,hrow _ hw⟩
  obtain ⟨a,ha,hr⟩ := hsome
  have ha0 : 0 < a := by rcases ha with rfl|rfl <;> omega
  have hak : a ≤ 2*k := by rcases ha with rfl|rfl <;> omega
  have hkr : (0 : ℝ)<k := by exact_mod_cast hk
  have hnr : (32 : ℝ) ≤ N := by exact_mod_cast hN
  have halog : log a ≤ log k+7/10 := by
    have h := log_le_log (show (0 : ℝ)<a by exact_mod_cast ha0)
      (show (a : ℝ) ≤ 2*k by exact_mod_cast hak)
    rw [log_mul (by norm_num : (2 : ℝ)≠0) hkr.ne'] at h
    linarith [Real.log_two_lt_d9]
  have hb := row_log_bounds hu (by omega : 2 ≤ N) B hB hr
  have hlR : log R ≤ SquarefreeVaughanLogSource.length u N-log p := by
    simpa only [log_exp] using log_le_log
      (show (0 : ℝ)<R by exact_mod_cast hR) hcut
  have hg : 4*log R ≤ 3*log k := by
    linarith [log_natCast_nonneg p]
  have hpw : (R : ℝ)^4 ≤ (k : ℝ)^3 := by
    rw [← exp_log (pow_pos (show (0 : ℝ)<R by exact_mod_cast hR) 4),
      ← exp_log (pow_pos hkr 3),log_pow,log_pow]
    exact exp_le_exp.mpr (by norm_num only [Nat.cast_ofNat]; exact hg)
  refine ⟨by exact_mod_cast hpw,?_⟩
  have hlk : (N : ℝ)/2 ≤ log k := by linarith
  exact (exp_le_exp.mpr hlk).trans_eq (exp_log hkr)

private theorem weighted_error_eq (X D : ℕ) (w : ℕ → ℝ) (hend : w (X+1)=0) :
    (∑ n ∈ Finset.Icc 1 X, w n*(if Squarefree n then sharp D n else 0))-
      densityPrefix D*(∑ n ∈ Finset.Icc 1 X, w n) =
        ∑ k ∈ Finset.Icc 1 X, (w k-w (k+1))*
          ((∑ n ∈ Finset.Icc 1 k, if Squarefree n then sharp D n else 0)-densityPrefix D*k) := by
  have hc k : (∑ n ∈ Finset.Icc 1 k,
      ((if Squarefree n then sharp D n else 0)-densityPrefix D)) =
        (∑ n ∈ Finset.Icc 1 k, if Squarefree n then sharp D n else 0)-densityPrefix D*k := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,
      nsmul_eq_mul,mul_comm]
  rw [← Finset.sum_congr rfl (fun k _ => congrArg (fun z : ℝ => (w k-w (k+1))*z) (hc k))]
  rw [← ZetaRieszSignedCutoffEnergy.abel_profile X w _ hend]
  simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- The full signed weight, including every mask discontinuity, remains
literal. Only its counting error uses the displayed variation. -/
theorem weighted_error_exponential (X D N : ℕ) (w : ℕ → ℝ) (b : ℝ)
    (hend : w (X+1)=0) (hD : 0 < D)
    (hcut : ∀ k ∈ Finset.Icc 1 X, w k ≠ w (k+1) → D^4 ≤ k^3)
    (hlower : ∀ k ∈ Finset.Icc 1 X, w k ≠ w (k+1) → exp (b*N) ≤ k) :
    |(∑ n ∈ Finset.Icc 1 X, w n*(if Squarefree n then sharp D n else 0))-
      densityPrefix D*(∑ n ∈ Finset.Icc 1 X, w n)| ≤
        countingConstant*exp (-(b*N)/64)*
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|w k-w (k+1)|) := by
  rw [weighted_error_eq X D w hend,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  by_cases hz : w k=w (k+1)
  · simp [hz]
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  have hkr : (0 : ℝ)<k := by exact_mod_cast hk0
  have hl : b*N ≤ log k := by
    simpa only [log_exp] using log_le_log (exp_pos _) (hlower k hk hz)
  have hp : (k : ℝ)^(63/64 : ℝ) ≤ exp (-(b*N)/64)*k := by
    conv_rhs => rw [← exp_log hkr]
    rw [rpow_def_of_pos hkr,← exp_add]
    apply exp_le_exp.mpr
    linarith
  rw [abs_mul]
  calc
    _ ≤ |w k-w (k+1)| *(countingConstant*(k : ℝ)^(63/64 : ℝ)) :=
      mul_le_mul_of_nonneg_left (sharp_count_error_long hk0 hD (hcut k hk hz)) (abs_nonneg _)
    _ ≤ |w k-w (k+1)| *(countingConstant*(exp (-(b*N)/64)*k)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp countingConstant_pos.le) (abs_nonneg _)
    _ = _ := by ring

/-- The conditioning denominator is genuinely positive. Its reciprocal
is the already proved total mass of the positive density correction. -/
theorem squarefree_density_pos : 0 < SquarefreeCounting.density ∅ := by
  have hn : SquarefreeCounting.density ∅ ≠ 0 := by
    intro hz
    have h := ZetaRieszSignedDensityMain.density_correction_mass
    rw [hz,zero_mul] at h
    norm_num at h
  exact lt_of_le_of_ne ZetaRieszSignedDensityMain.base_density_bounds.1 hn.symm

/-- Center against the SAME squarefree reference measure. The squarefree
indicator is retained inside both arithmetic sums, rather than being
charged as adjacent variation of the weight. Every other mask is in `q`.
The bound is unconditional; its only remaining cost is variation of `q`. -/
theorem squarefree_reference_error (X D N : ℕ) (q : ℕ → ℝ) (b : ℝ)
    (hend : q (X+1)=0) (hD : 0 < D)
    (hcut : ∀ k ∈ Finset.Icc 1 X, q k ≠ q (k+1) → D^4 ≤ k^3)
    (hlower : ∀ k ∈ Finset.Icc 1 X, q k ≠ q (k+1) → exp (b*N) ≤ k) :
    |SquarefreeCounting.density ∅ *
        (∑ n ∈ Finset.Icc 1 X, q n*(if Squarefree n then sharp D n else 0))-
      densityPrefix D*(∑ n ∈ Finset.Icc 1 X, q n*(if Squarefree n then 1 else 0))| ≤
      3*countingConstant*exp (-(b*N)/64)*
        (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|) := by
  let rho := SquarefreeCounting.density ∅
  let A := ∑ n ∈ Finset.Icc 1 X, q n*(if Squarefree n then sharp D n else 0)
  let B := ∑ n ∈ Finset.Icc 1 X, q n*(if Squarefree n then 1 else 0)
  let S := ∑ n ∈ Finset.Icc 1 X, q n
  let E := countingConstant*exp (-(b*N)/64)*
    (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|)
  have hA : |A-densityPrefix D*S| ≤ E :=
    weighted_error_exponential X D N q b hend hD hcut hlower
  have hB : |B-rho*S| ≤ E := by
    have h1cut : ∀ k ∈ Finset.Icc 1 X, q k ≠ q (k+1) → (1 : ℕ)^4 ≤ k^3 := by
      intro k hk _
      have hk1 := (Finset.mem_Icc.mp hk).1
      simpa only [one_pow] using Nat.pow_le_pow_left hk1 3
    have h := weighted_error_exponential X 1 N q b hend (by omega)
      h1cut hlower
    simpa [sharp,densityPrefix,B,rho,S,E] using h
  have hR : |rho| ≤ 1 := by
    rw [abs_of_nonneg ZetaRieszSignedDensityMain.base_density_bounds.1]
    exact ZetaRieszSignedDensityMain.base_density_bounds.2
  rw [show 3*countingConstant*exp (-(b*N)/64)*
    (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|)=3*E by dsimp [E]; ring]
  change |rho*A-densityPrefix D*B| ≤ 3*E
  have he : rho*A-densityPrefix D*B =
      rho*(A-densityPrefix D*S)-densityPrefix D*(B-rho*S) := by ring
  rw [he]
  calc
    _ ≤ |rho*(A-densityPrefix D*S)|+|densityPrefix D*(B-rho*S)| := abs_sub _ _
    _ = |rho| * |A-densityPrefix D*S|+|densityPrefix D| * |B-rho*S| := by rw [abs_mul,abs_mul]
    _ ≤ 1*E+2*E := add_le_add
      (mul_le_mul hR hA (abs_nonneg _) (by norm_num))
      (mul_le_mul (ZetaRieszSignedDensityMain.densityPrefix_bound D) hB
        (abs_nonneg _) (by norm_num))
    _ = _ := by ring

/-- The joined profile estimate in squarefree coordinates retains ONE
signed density scalar and the full signed squarefree weight sum. Only
variation of the remaining literal masks enters its explicit error. -/
theorem squarefree_profile_reference_error {X R : ℕ}
    (N : ℕ) (q f : ℕ → ℝ) (b : ℝ) (hw : q (X+1)=0) (hf : f (R+1)=0)
    (hcut : ∀ k ∈ Finset.Icc 1 X, q k ≠ q (k+1) → R^4 ≤ k^3)
    (hlower : ∀ k ∈ Finset.Icc 1 X, q k ≠ q (k+1) → exp (b*N) ≤ k) :
    |SquarefreeCounting.density ∅ *
        (∑ n ∈ Finset.Icc 1 X, q n*(if Squarefree n then
          ∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (μ d : ℝ) else 0) else 0))-
      (∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*densityPrefix D)*
        (∑ n ∈ Finset.Icc 1 X, q n*(if Squarefree n then 1 else 0))| ≤
      3*countingConstant*exp (-(b*N)/64)*
        (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|)*
        (∑ D ∈ Finset.Icc 1 R, |f D-f (D+1)|) := by
  have he n : (if Squarefree n then
      ∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (μ d : ℝ) else 0) else 0) =
      ∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*(if Squarefree n then sharp D n else 0) := by
    by_cases hs : Squarefree n
    · simp only [hs,if_true]
      exact ZetaRieszSignedCutoffEnergy.abel_profile R f _ hf
    · simp [hs]
  have hj : (∑ n ∈ Finset.Icc 1 X, q n*(if Squarefree n then
      ∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (μ d : ℝ) else 0) else 0)) =
      ∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*
        (∑ n ∈ Finset.Icc 1 X, q n*(if Squarefree n then sharp D n else 0)) := by
    simp_rw [he,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro D _
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hj,Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ D ∈ Finset.Icc 1 R, |f D-f (D+1)| *
        (3*countingConstant*exp (-(b*N)/64)*
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|)) := by
      apply Finset.sum_le_sum
      intro D hD
      have h := squarefree_reference_error X D N q b hw (Finset.mem_Icc.mp hD).1
        (fun k hk hz => (Nat.pow_le_pow_left (Finset.mem_Icc.mp hD).2 4).trans
          (hcut k hk hz)) hlower
      have heq : SquarefreeCounting.density ∅ *
          ((f D-f (D+1))*(∑ n ∈ Finset.Icc 1 X,
            q n*(if Squarefree n then sharp D n else 0)))-
          (f D-f (D+1))*densityPrefix D*
            (∑ n ∈ Finset.Icc 1 X, q n*(if Squarefree n then 1 else 0)) =
          (f D-f (D+1))*(SquarefreeCounting.density ∅ *
            (∑ n ∈ Finset.Icc 1 X, q n*(if Squarefree n then sharp D n else 0))-
            densityPrefix D*(∑ n ∈ Finset.Icc 1 X,
              q n*(if Squarefree n then 1 else 0))) := by
        ring
      rw [heq,abs_mul]
      exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The signed density and exact prime/unit corrections are retained.
This estimates their difference from actual squarefree composite rows. -/
theorem composite_error_exponential {X D : ℕ} (hX : 0 < X) (hD : 0 < D)
    (N : ℕ) (w : ℕ → ℝ) (b : ℝ) (hend : w (X+1)=0)
    (hcut : ∀ k ∈ Finset.Icc 1 X, w k ≠ w (k+1) → D^4 ≤ k^3)
    (hlower : ∀ k ∈ Finset.Icc 1 X, w k ≠ w (k+1) → exp (b*N) ≤ k) :
    |correlation (compositePrefix X) w D-compositeModel X D w| ≤
      countingConstant*exp (-(b*N)/64)*
        (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|w k-w (k+1)|) := by
  rw [composite_model hX hD w]
  exact weighted_error_exponential X D N w b hend hD hcut hlower

/-- Join the cutoff profile before estimating. The signed main contains
the density, unit and prime corrections with their original signs. -/
theorem profile_error_exponential {X R : ℕ} (hX : 0 < X)
    (N : ℕ) (w f : ℕ → ℝ) (b : ℝ) (hw : w (X+1)=0) (hf : f (R+1)=0)
    (hcut : ∀ k ∈ Finset.Icc 1 X, w k ≠ w (k+1) → R^4 ≤ k^3)
    (hlower : ∀ k ∈ Finset.Icc 1 X, w k ≠ w (k+1) → exp (b*N) ≤ k) :
    |(∑ n ∈ compositePrefix X, w n*(∑ d ∈ Finset.Icc 1 R,
        f d*(if d ∣ n then (μ d : ℝ) else 0)))-
      (∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*compositeModel X D w)| ≤
        countingConstant*exp (-(b*N)/64)*
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|w k-w (k+1)|)*
          (∑ D ∈ Finset.Icc 1 R, |f D-f (D+1)|) := by
  have he : (∑ n ∈ compositePrefix X, w n*(∑ d ∈ Finset.Icc 1 R,
      f d*(if d ∣ n then (μ d : ℝ) else 0))) =
      ∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*correlation (compositePrefix X) w D := by
    simp_rw [ZetaRieszSignedCutoffEnergy.abel_profile R f _ hf,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro D _
    simp only [correlation,sharp,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [he,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ D ∈ Finset.Icc 1 R, |f D-f (D+1)| *
        (countingConstant*exp (-(b*N)/64)*
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|w k-w (k+1)|)) := by
      apply Finset.sum_le_sum
      intro D hD
      rw [← mul_sub,abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact composite_error_exponential hX (Finset.mem_Icc.mp hD).1 N w b hw
        (fun k hk hz => (Nat.pow_le_pow_left (Finset.mem_Icc.mp hD).2 4).trans
          (hcut k hk hz)) hlower
    _ = _ := by rw [← Finset.sum_mul]; ring

private theorem hinge_profile_end (c : ℝ) :
    max 0 (c-log ((⌊exp c⌋₊+1 : ℕ) : ℝ))=0 := by
  have he : exp c < ((⌊exp c⌋₊+1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (exp c)
  have hl : c < log ((⌊exp c⌋₊+1 : ℕ) : ℝ) := by
    simpa only [log_exp] using log_lt_log (exp_pos _) he
  exact max_eq_left (by linarith)

/-- Joining a single literal hinge profile costs precisely its height,
not the number of divisor cutoffs. The signed increments stay intact. -/
theorem hinge_profile_variation (c : ℝ) :
    (∑ D ∈ Finset.Icc 1 ⌊exp c⌋₊,
      |max 0 (c-log D)-max 0 (c-log (D+1 : ℕ))|)=max 0 c := by
  let f : ℕ → ℝ := fun d => max 0 (c-log d)
  have he D (hD : D ∈ Finset.Icc 1 ⌊exp c⌋₊) : |f D-f (D+1)|=f D-f (D+1) := by
    apply abs_of_nonneg
    have hl := log_le_log (show (0 : ℝ)<D by exact_mod_cast (Finset.mem_Icc.mp hD).1)
      (show (D : ℝ) ≤ (D+1 : ℕ) by exact_mod_cast Nat.le_succ D)
    have hm := max_le_max_left 0 (sub_le_sub_left hl c)
    exact sub_nonneg.mpr hm
  change (∑ D ∈ Finset.Icc 1 ⌊exp c⌋₊, |f D-f (D+1)|)=_
  rw [Finset.sum_congr rfl he,← Finset.Ico_add_one_right_eq_Icc]
  calc
    _ = -(∑ D ∈ Finset.Ico 1 (⌊exp c⌋₊+1), (f (D+1)-f D)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ = f 1-f (⌊exp c⌋₊+1) := by rw [Finset.sum_Ico_sub f (by omega)]; ring
    _ = _ := by simp only [f,Nat.cast_one,log_one,sub_zero,hinge_profile_end]

private theorem riesz_eq_hinge_profile (c : ℝ) {n : ℕ} (hn : 0 < n) :
    VaughanLogAverage.riesz c n =
      ∑ d ∈ Finset.Icc 1 ⌊exp c⌋₊,
        max 0 (c-log d)*(if d ∣ n then (μ d : ℝ) else 0) := by
  have hr := Nat.floor_le (exp_pos c).le
  have he : exp c < (⌊exp c⌋₊ : ℝ)+1 := Nat.lt_floor_add_one _
  conv_lhs => rw [← log_exp c,ZetaRieszSieveMean.riesz_eq_log_prefix _ (exp_pos _) hr he hn]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : (0 : ℝ)<d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hdx : (d : ℝ) ≤ exp c :=
    (show (d : ℝ) ≤ ⌊exp c⌋₊ by exact_mod_cast (Finset.mem_Icc.mp hd).2).trans hr
  have hdl : log d ≤ c := by simpa only [log_exp] using log_le_log hd0 hdx
  rw [max_eq_right (sub_nonneg.mpr hdl)]
  by_cases hdn : d ∣ n
  · simp only [hdn,if_true,log_div (exp_pos c).ne' hd0.ne',log_exp]
    ring
  · simp [hdn]

/-- A bound for the literal masked owner column, with EVERY cutoff-range
and radial-support premise discharged. The exact signed scalar stays
multiplied by the exact signed weight sum. The remaining displayed cost
is the actual mask variation, not a claimed source-scale small quantity. -/
theorem literal_translated_error {u : ℝ} (hu : 1/2 ≤ u)
    {N K : ℕ} (hN : 32 ≤ N) (B : Finset ℕ)
    (hB : B ⊆ (coreBand u N K).filter Squarefree)
    (A : Finset ℕ) (y scale : ℝ) (p : ℕ) :
    let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
    let c := SquarefreeVaughanLogSource.length u N-log p
    let R := ⌊exp c⌋₊
    let w := fun n => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) (SquarefreeVaughanLogSource.length u N)
        y scale N n p
    |(∑ n ∈ compositePrefix X, w n*VaughanLogAverage.riesz c n)-
      (∑ D ∈ Finset.Icc 1 R,
        (max 0 (c-log D)-max 0 (c-log (D+1 : ℕ)))*densityPrefix D)*
          (∑ n ∈ Finset.Icc 1 X, w n)| ≤
      countingConstant*exp (-(N : ℝ)/128)*
        (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|w k-w (k+1)|)*max 0 c := by
  dsimp only
  let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
  let c := SquarefreeVaughanLogSource.length u N-log p
  let R := ⌊exp c⌋₊
  let f : ℕ → ℝ := fun d => max 0 (c-log d)
  let w := fun n => ZetaRieszJointPrimeEnergy.maskedWeight A
    (ZetaRieszJointPrimeEnergy.ownerRows B) (SquarefreeVaughanLogSource.length u N)
      y scale N n p
  have hX : 0 < X := by dsimp [X]; omega
  have hBB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card := by
    intro m hm
    have hd := Finset.mem_filter.mp (hB hm)
    exact ⟨hd.2,ZetaRieszJointPrimeEnergy.core_count hd.1⟩
  have hw : w (X+1)=0 := by
    have hn : p ∉ ZetaRieszJointPrimeEnergy.ownerRows B (X+1) := by
      intro hp
      obtain ⟨m,hm,_⟩ := Finset.mem_image.mp hp
      obtain ⟨hm,he⟩ := Finset.mem_filter.mp hm
      have ha : X+1 ∈ ZetaRieszJointPrimeEnergy.cofactors B :=
        Finset.mem_image.mpr ⟨m,hm,he⟩
      have hl := Finset.le_sup (f := id) ha
      dsimp [X] at hl
      omega
    simp [w,ZetaRieszJointPrimeEnergy.maskedWeight,hn]
  have hleft : (∑ n ∈ compositePrefix X, w n*VaughanLogAverage.riesz c n) =
      ∑ n ∈ compositePrefix X, w n*(∑ d ∈ Finset.Icc 1 R,
        f d*(if d ∣ n then (μ d : ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [riesz_eq_hinge_profile c (by have := (Finset.mem_Ioc.mp
      (Finset.mem_filter.mp hn).1).1; omega : 0 < n)]
  change |_ - (∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*densityPrefix D)*
    (∑ n ∈ Finset.Icc 1 X, w n)| ≤ _
  rw [hleft]
  by_cases hR : R=0
  · have hC := countingConstant_pos
    simp [hR]
    positivity
  have hR0 : 0 < R := by omega
  have hs k (hk : k ∈ Finset.Icc 1 X) (hz : w k ≠ w (k+1)) :=
    literal_masked_support hu hN B (fun _ hm => (Finset.mem_filter.mp (hB hm)).1)
      A y scale p hR0
      (Nat.floor_le (exp_pos c).le) (Finset.mem_Icc.mp hk).1 hz
  have h := profile_error_exponential hX N w f (1/2) hw (hinge_profile_end c)
    (fun k hk hz => (hs k hk hz).1)
    (fun k hk hz => by
      have he : (1/2 : ℝ)*N=(N : ℝ)/2 := by ring
      rw [he]
      exact (hs k hk hz).2)
  rw [ZetaRieszCofactorDiscrepancy.literal_profile_factorization A B hBB
    (SquarefreeVaughanLogSource.length u N) y scale N p X R f] at h
  have he : -((1/2 : ℝ)*N)/64=-(N : ℝ)/128 := by ring
  rw [he,hinge_profile_variation c] at h
  exact h

/-- Keep the literal owner/count/physical masks but put squarefreeness
inside the arithmetic reference measure. Repeated-owner labels are
excluded exactly, since they cannot belong to the squarefree carrier. -/
def beforeSquaresWeight (A B : Finset ℕ) (L y scale : ℝ)
    (N a p : ℕ) : ℝ :=
  ZetaRieszJointPrimeEnergy.maskedWeight A
    (ZetaRieszJointPrimeEnergy.ownerRows
      (B.filter (fun n => ¬largestPrime n ∣ ZetaRieszOwnedCells.ownerCofactor n)))
        L y scale N a p

private theorem squarefree_rows_iff (B : Finset ℕ)
    (hB : ∀ n ∈ B, 3 ≤ n.primeFactors.card) (a p : ℕ) :
    p ∈ ZetaRieszJointPrimeEnergy.ownerRows (B.filter Squarefree) a ↔
      Squarefree a ∧ p ∈ ZetaRieszJointPrimeEnergy.ownerRows
        (B.filter (fun n => ¬largestPrime n ∣ ZetaRieszOwnedCells.ownerCofactor n)) a := by
  constructor
  · intro hr
    obtain ⟨n,hn,hp⟩ := Finset.mem_image.mp hr
    obtain ⟨hn,ha⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn,hs⟩ := Finset.mem_filter.mp hn
    have hpf := ZetaRieszOwnedCells.largestPrime_mem_of_two (m := n)
      (by have := hB n hn; omega)
    have hd := ZetaRieszMarkedSaturation.cofactor_data hs (hB n hn) hpf
    change n/largestPrime n=a at ha
    refine ⟨ha ▸ hd.1,Finset.mem_image.mpr ⟨n,?_,hp⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hn,hd.2.2.2⟩,ha⟩
  · rintro ⟨hs,hr⟩
    obtain ⟨n,hn,hp⟩ := Finset.mem_image.mp hr
    obtain ⟨hn,ha⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn,hcop⟩ := Finset.mem_filter.mp hn
    have hpf := ZetaRieszOwnedCells.largestPrime_mem_of_two (m := n)
      (by have := hB n hn; omega)
    have hpp := Nat.prime_of_mem_primeFactors hpf
    have he : largestPrime n*ZetaRieszOwnedCells.ownerCofactor n=n :=
      Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hpf)
    have hsf : Squarefree n := by
      rw [← he]
      exact Nat.squarefree_mul_iff.mpr
        ⟨hpp.coprime_iff_not_dvd.mpr hcop,hpp.squarefree,ha.symm ▸ hs⟩
    exact Finset.mem_image.mpr ⟨n,Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hn,hsf⟩,ha⟩,hp⟩

/-- This is an exact identity on ALL integers, not a completion of the
prime/count support. The carrier's squarefree condition is retained. -/
theorem beforeSquares_eq_literal (A B : Finset ℕ)
    (hB : ∀ n ∈ B, 3 ≤ n.primeFactors.card)
    (L y scale : ℝ) (N a p : ℕ) :
    (if Squarefree a then beforeSquaresWeight A B L y scale N a p else 0) =
      ZetaRieszJointPrimeEnergy.maskedWeight A
        (ZetaRieszJointPrimeEnergy.ownerRows (B.filter Squarefree)) L y scale N a p := by
  by_cases hs : Squarefree a <;>
    simp [beforeSquaresWeight,ZetaRieszJointPrimeEnergy.maskedWeight,
      squarefree_rows_iff B hB a p,hs]

/-- The masked translated hinge is now centered in its actual squarefree
measure. This removes the squarefree zero-extension from the variation
cost exactly, retaining every other literal mask and the signed density
scalar. No unproved bilinear or counting estimate is assumed. -/
theorem literal_squarefree_reference_error {u : ℝ} (hu : 1/2 ≤ u)
    {N K : ℕ} (hN : 32 ≤ N) (B : Finset ℕ) (hB : B ⊆ coreBand u N K)
    (A : Finset ℕ) (y scale : ℝ) (p : ℕ) :
    let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
    let L := SquarefreeVaughanLogSource.length u N
    let c := L-log p
    let R := ⌊exp c⌋₊
    let q := fun n => beforeSquaresWeight A B L y scale N n p
    let w := fun n => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows (B.filter Squarefree)) L y scale N n p
    |SquarefreeCounting.density ∅ *
        (∑ n ∈ Finset.Icc 1 X, w n*VaughanLogAverage.riesz c n)-
      (∑ D ∈ Finset.Icc 1 R,
        (max 0 (c-log D)-max 0 (c-log (D+1 : ℕ)))*densityPrefix D)*
          (∑ n ∈ Finset.Icc 1 X, w n)| ≤
      3*countingConstant*exp (-(N : ℝ)/128)*
        (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|)*max 0 c := by
  dsimp only
  let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
  let L := SquarefreeVaughanLogSource.length u N
  let c := L-log p
  let R := ⌊exp c⌋₊
  let f : ℕ → ℝ := fun d => max 0 (c-log d)
  let B0 := B.filter (fun n => ¬largestPrime n ∣ ZetaRieszOwnedCells.ownerCofactor n)
  let q := fun n => beforeSquaresWeight A B L y scale N n p
  let w := fun n => ZetaRieszJointPrimeEnergy.maskedWeight A
    (ZetaRieszJointPrimeEnergy.ownerRows (B.filter Squarefree)) L y scale N n p
  have hBB : ∀ n ∈ B, 3 ≤ n.primeFactors.card :=
    fun _ hn => ZetaRieszJointPrimeEnergy.core_count (hB hn)
  have hb n : (if Squarefree n then q n else 0)=w n :=
    beforeSquares_eq_literal A B hBB L y scale N n p
  have hX : 0 < X := by dsimp [X]; omega
  have hw : q (X+1)=0 := by
    have hn : p ∉ ZetaRieszJointPrimeEnergy.ownerRows B0 (X+1) := by
      intro hp
      obtain ⟨m,hm,_⟩ := Finset.mem_image.mp hp
      obtain ⟨hm,he⟩ := Finset.mem_filter.mp hm
      have ha : X+1 ∈ ZetaRieszJointPrimeEnergy.cofactors B :=
        Finset.mem_image.mpr ⟨m,(Finset.mem_filter.mp hm).1,he⟩
      have hl := Finset.le_sup (f := id) ha
      dsimp [X] at hl
      omega
    exact if_neg hn
  have hleft : (∑ n ∈ Finset.Icc 1 X, q n*(if Squarefree n then
      ∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (μ d : ℝ) else 0) else 0)) =
      ∑ n ∈ Finset.Icc 1 X, w n*VaughanLogAverage.riesz c n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hbn := hb n
    by_cases hs : Squarefree n
    · simp only [hs,if_true] at hbn ⊢
      rw [hbn,← riesz_eq_hinge_profile c (Finset.mem_Icc.mp hn).1]
    · simp only [hs,if_false] at hbn ⊢
      rw [← hbn,zero_mul,mul_zero]
  have hsum : (∑ n ∈ Finset.Icc 1 X, q n*(if Squarefree n then 1 else 0)) =
      ∑ n ∈ Finset.Icc 1 X, w n := by
    apply Finset.sum_congr rfl
    intro n _
    have h := hb n
    by_cases hs : Squarefree n <;> simpa [hs] using h
  change |SquarefreeCounting.density ∅ * _ -
    (∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*densityPrefix D)*
      (∑ n ∈ Finset.Icc 1 X, w n)| ≤ _
  rw [← hleft,← hsum]
  by_cases hR : R=0
  · have hC := countingConstant_pos
    simp [hR]
    positivity
  have hs k (hk : k ∈ Finset.Icc 1 X) (hz : q k ≠ q (k+1)) :=
    literal_masked_support hu hN B0
      (fun _ hn => hB (Finset.mem_filter.mp hn).1) A y scale p (by omega : 0 < R)
        (Nat.floor_le (exp_pos c).le) (Finset.mem_Icc.mp hk).1 hz
  have h := squarefree_profile_reference_error N q f (1/2) hw (hinge_profile_end c)
    (fun k hk hz => (hs k hk hz).1)
    (fun k hk hz => by
      have he : (1/2 : ℝ)*N=(N : ℝ)/2 := by ring
      rw [he]
      exact (hs k hk hz).2)
  have he : -((1/2 : ℝ)*N)/64=-(N : ℝ)/128 := by ring
  rw [he,hinge_profile_variation c] at h
  exact h

private theorem literal_owner_columns (A S : Finset ℕ)
    (hS : ∀ n ∈ S, Squarefree n ∧ 3 ≤ n.primeFactors.card)
    (X : ℕ) (hX : (ZetaRieszJointPrimeEnergy.cofactors S).sup id ≤ X)
    (L y scale : ℝ) (N : ℕ) :
    scale*(∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re =
      ∑ p ∈ ZetaRieszJointPrimeEnergy.ownerPrimes S, ∑ a ∈ Finset.Icc 1 X,
        ZetaRieszJointPrimeEnergy.maskedWeight A
          (ZetaRieszJointPrimeEnergy.ownerRows S) L y scale N a p*
            (VaughanLogAverage.riesz L a-VaughanLogAverage.riesz (L-log p) a) := by
  open ZetaRieszJointPrimeEnergy in
    have hd a p : divisorResponse (hinge L p) a =
        VaughanLogAverage.riesz L a-VaughanLogAverage.riesz (L-log p) a := by
      simp only [divisorResponse,hinge,VaughanLogAverage.riesz,mul_sub,Finset.sum_sub_distrib]
  have he := ZetaRieszCoupledWindow.sum_owned_products
    (ZetaRieszJointPrimeEnergy.cofactors S) (ZetaRieszJointPrimeEnergy.ownerRows S)
    (fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)
    (fun _ ha => (ZetaRieszJointPrimeEnergy.cofactors_data S hS ha).1.ne_zero)
    (fun _ _ _ hp => ⟨(ZetaRieszJointPrimeEnergy.ownerRows_data S hS hp).1,
      (ZetaRieszJointPrimeEnergy.ownerRows_data S hS hp).2.2⟩)
  rw [ZetaRieszJointPrimeEnergy.owner_labels_eq S hS] at he
  have hcol a : (ZetaRieszJointPrimeEnergy.ownerPrimes S).filter
      (fun p => p ∈ ZetaRieszJointPrimeEnergy.ownerRows S a)=
        ZetaRieszJointPrimeEnergy.ownerRows S a := by
    apply Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr _)
    intro p hp
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨n,(Finset.mem_filter.mp hn).1,he⟩
  rw [he,Complex.re_sum,Finset.mul_sum,Finset.sum_comm]
  have hs : ZetaRieszJointPrimeEnergy.cofactors S ⊆ Finset.Icc 1 X := by
    intro a ha
    have hd := (ZetaRieszJointPrimeEnergy.cofactors_data S hS ha).1.ne_zero
    exact Finset.mem_Icc.mpr ⟨by omega,(Finset.le_sup (f := id) ha).trans hX⟩
  symm
  calc
    _ = ∑ a ∈ ZetaRieszJointPrimeEnergy.cofactors S,
        ∑ p ∈ ZetaRieszJointPrimeEnergy.ownerPrimes S,
          ZetaRieszJointPrimeEnergy.maskedWeight A
            (ZetaRieszJointPrimeEnergy.ownerRows S) L y scale N a p*
              (VaughanLogAverage.riesz L a-VaughanLogAverage.riesz (L-log p) a) := by
      symm
      apply Finset.sum_subset hs
      intro a _ hnot
      apply Finset.sum_eq_zero
      intro p _
      have hp : p ∉ ZetaRieszJointPrimeEnergy.ownerRows S a := by
        intro hp
        obtain ⟨n,hn,_⟩ := Finset.mem_image.mp hp
        obtain ⟨hn,ha⟩ := Finset.mem_filter.mp hn
        exact hnot (Finset.mem_image.mpr ⟨n,hn,ha⟩)
      simp [ZetaRieszJointPrimeEnergy.maskedWeight,hp]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [ZetaRieszJointPrimeEnergy.maskedWeight,ite_mul,zero_mul,
        ← Finset.sum_filter,hcol a,Complex.re_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hpd := ZetaRieszJointPrimeEnergy.ownerRows_data S hS hp
      have hsf := ZetaRieszJointPrimeEnergy.cofactors_data S hS ha
      rw [Nat.mul_comm a p,ZetaRieszJointPrimeEnergy.atom_eq A L y N
        hsf.1 hsf.2 hpd.1 hpd.2.1,hd]
      ring

/-- The whole literal carrier, all counts and both hinges joined, has an
explicit comparison inequality in the squarefree reference measure. The
source-carrying signed main is NOT norm-paid. Every other original mask
is present in `q`, and its remaining variation is shown in full. -/
theorem literal_joined_carrier_estimate {u : ℝ} (hu : 1/2 ≤ u)
    {N K : ℕ} (hN : 32 ≤ N) (B : Finset ℕ) (hB : B ⊆ coreBand u N K)
    (A : Finset ℕ) (y scale : ℝ) :
    let S := B.filter Squarefree
    let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
    let L := SquarefreeVaughanLogSource.length u N
    let P := ZetaRieszJointPrimeEnergy.ownerPrimes S
    let rho := SquarefreeCounting.density ∅
    let w := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows S) L y scale N a p
    let q := fun a p => beforeSquaresWeight A B L y scale N a p
    |rho*(scale*(∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re)-
      (∑ p ∈ P,
        (rho*(∑ a ∈ Finset.Icc 1 X, w a p*VaughanLogAverage.riesz L a)-
          (∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
            (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*densityPrefix D)*
              (∑ a ∈ Finset.Icc 1 X, w a p)))| ≤
      3*countingConstant*exp (-(N : ℝ)/128)*
        (∑ p ∈ P, max 0 (L-log p)*
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k p-q (k+1) p|)) := by
  dsimp only
  let S := B.filter Squarefree
  let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
  let L := SquarefreeVaughanLogSource.length u N
  let P := ZetaRieszJointPrimeEnergy.ownerPrimes S
  let rho := SquarefreeCounting.density ∅
  let w := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
    (ZetaRieszJointPrimeEnergy.ownerRows S) L y scale N a p
  let q := fun a p => beforeSquaresWeight A B L y scale N a p
  have hS : ∀ n ∈ S, Squarefree n ∧ 3 ≤ n.primeFactors.card := by
    intro n hn
    obtain ⟨hn,hs⟩ := Finset.mem_filter.mp hn
    exact ⟨hs,ZetaRieszJointPrimeEnergy.core_count (hB hn)⟩
  have hx : (ZetaRieszJointPrimeEnergy.cofactors S).sup id ≤ X := by
    apply le_trans (Finset.sup_le _) (le_max_right _ _)
    intro a ha
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp ha
    exact Finset.le_sup (f := id) (Finset.mem_image.mpr
      ⟨n,(Finset.mem_filter.mp hn).1,he⟩)
  have hc := literal_owner_columns A S hS X hx L y scale N
  let H := fun p => ∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
    (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*densityPrefix D
  have he : rho*(scale*(∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re)-
      (∑ p ∈ P, (rho*(∑ a ∈ Finset.Icc 1 X, w a p*VaughanLogAverage.riesz L a)-
        H p*(∑ a ∈ Finset.Icc 1 X, w a p))) =
      -(∑ p ∈ P, (rho*(∑ a ∈ Finset.Icc 1 X,
          w a p*VaughanLogAverage.riesz (L-log p) a)-H p*(∑ a ∈ Finset.Icc 1 X, w a p))) := by
    rw [hc]
    simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
    ring
  change |_ - (∑ p ∈ P, (rho*(∑ a ∈ Finset.Icc 1 X, w a p*VaughanLogAverage.riesz L a)-
    H p*(∑ a ∈ Finset.Icc 1 X, w a p)))| ≤ _
  rw [he,abs_neg,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p _
  have h := literal_squarefree_reference_error hu hN B hB A y scale p
  exact h.trans_eq (by dsimp [X,L,H,w,q,rho,P,S] at *; ring)

/-- A genuine arithmetic counting saving survives on complete physical
shells with their full product phase. Extra mask variation is not hidden. -/
theorem shell_composite_error {M X D : ℕ} (hM : 0 < M) (hMX : M < X)
    (hXM : X ≤ 2*M) (hD : 0 < D) (hDM : D^4 ≤ M^3)
    (N : ℕ) (hlarge : exp ((N : ℝ)/2) ≤ M)
    (a : ℕ → ℝ) (y c A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ n ∈ Finset.Ioc M X, |a n| ≤ A) :
    |correlation (compositePrefix X) (shellWeight M X a y c) D-
      compositeModel X D (shellWeight M X a y c)| ≤
        countingConstant*exp (-(N : ℝ)/128)*
          ((3+|y|)*A+(∑ k ∈ Finset.Ico (M+1) X, |a k-a (k+1)|)) := by
  have hactive k (_ : k ∈ Finset.Icc 1 X)
      (hz : shellWeight M X a y c k ≠ shellWeight M X a y c (k+1)) : M ≤ k := by
    by_contra h
    have hkM : k < M := lt_of_not_ge h
    simp [shellWeight,show ¬M<k by omega,show ¬M<k+1 by omega] at hz
  have hb := composite_error_exponential (show 0 < X by omega) hD N
    (shellWeight M X a y c) (1/2) (by simp [shellWeight])
    (fun k hk hz => hDM.trans (Nat.pow_le_pow_left (hactive k hk hz) 3))
    (fun k hk hz => by
      have hMk : (M : ℝ) ≤ k := by exact_mod_cast hactive k hk hz
      have he : (1/2 : ℝ)*N=(N : ℝ)/2 := by ring
      rw [he]
      exact hlarge.trans hMk)
  have he : -((1/2 : ℝ)*N)/64=-(N : ℝ)/128 := by ring
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (shellWeight_variation hM hMX hXM a y c A hA ha)
    (mul_nonneg countingConstant_pos.le (exp_pos _).le))

/-- Only the counting error gets this source-scale gain. The signed
main and the literal mask variation are not replaced by this envelope. -/
theorem source_rate_bound {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ) :
    (2*u)^N*exp (-(N : ℝ)/128) ≤ exp (-(1/200 : ℝ)*N) := by
  have hh : 2*u ≤ exp (9/3200 : ℝ) := by
    have he := Real.add_one_le_exp (9/3200 : ℝ)
    unfold ZetaRieszWideOwnerAudit.radiusCeiling at hu
    linarith
  have hn := pow_le_pow_left₀ (by positivity : 0 ≤ 2*u) hh N
  calc
    _ ≤ exp (9/3200 : ℝ)^N*exp (-(N : ℝ)/128) :=
      mul_le_mul_of_nonneg_right hn (exp_pos _).le
    _ = _ := by rw [← exp_nat_mul,← exp_add]; congr 1; ring

private theorem rough_mark_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (d X : ℕ) :
    ‖RoughSquarefreeCounting.markedCount S d X-
      RoughSquarefreeCounting.markedDensity S d*X‖ ≤
      exp (primeSquareWeightMass (3/4))*(X : ℝ)^(3/4 : ℝ)*
        (∏ p ∈ d.primeFactors, primeSquareCorrectedWeight (3/4) p)*
          ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S := by
  have hcost : 0 ≤ ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S :=
    ZetaRieszPrimeWeightedSieve.sieveCost_nonneg _ _
  have hmark : 0 ≤ ∏ p ∈ d.primeFactors, primeSquareCorrectedWeight (3/4) p :=
    Finset.prod_nonneg (fun p _ => primeSquareCorrectedWeight_nonneg _ p)
  by_cases hd : Squarefree d
  · by_cases hds : ∀ p ∈ d.primeFactors, p ∉ S
    · rw [RoughSquarefreeCounting.markedCount_centered_eq_subsets S hS hd]
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ W ∈ S.powerset,
            exp (primeSquareWeightMass (3/4))*(X : ℝ)^(3/4 : ℝ)*
              (∏ p ∈ d.primeFactors, primeSquareCorrectedWeight (3/4) p)*
                ∏ p ∈ W, primeSquareCorrectedWeight (3/4) p := by
          apply Finset.sum_le_sum
          intro W hW
          have hWp : ∀ p ∈ d.primeFactors ∪ W, p.Prime := by
            intro p hp
            rcases Finset.mem_union.mp hp with hp|hp
            · exact Nat.prime_of_mem_primeFactors hp
            · exact hS p (Finset.mem_powerset.mp hW hp)
          have hdis : Disjoint d.primeFactors W := Finset.disjoint_left.mpr
            (fun p hp hW' => hds p hp (Finset.mem_powerset.mp hW hW'))
          have hb := SquarefreeCounting.count_centered_bound
            (d.primeFactors ∪ W) hWp (by norm_num : (1/2 : ℝ)<3/4)
              (by norm_num : (3/4 : ℝ)≤1) X
          rw [Finset.prod_union hdis] at hb
          rw [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
            ← Complex.ofReal_natCast,← Complex.ofReal_mul,← Complex.ofReal_sub,
            Complex.norm_real,Real.norm_eq_abs]
          exact hb.trans_eq (by ring)
        _ = _ := by
          rw [ZetaRieszPrimeWeightedSieve.sieveCost,Finset.prod_one_add,Finset.mul_sum]
    · push Not at hds
      obtain ⟨p,hp,hpS⟩ := hds
      have hit : ∃ p ∈ S, p ∣ d := ⟨p,hpS,Nat.dvd_of_mem_primeFactors hp⟩
      rw [RoughSquarefreeCounting.markedCount_eq_zero_of_sieve_hit S hit,
        RoughSquarefreeCounting.markedDensity_eq_zero_of_sieve_hit S hS hit]
      simp only [zero_mul,sub_self,norm_zero]
      positivity
  · rw [RoughSquarefreeCounting.markedCount_eq_zero_of_not_squarefree S hd,
      RoughSquarefreeCounting.markedDensity,if_neg hd]
    simp only [zero_mul,sub_self,norm_zero]
    positivity

/-- The signed density prefix with every excluded-prime intersection
retained. This is a reference measure, not a completed carrier. -/
def roughDensityPrefix (S : Finset ℕ) (D : ℕ) : ℝ :=
  (∑ d ∈ Finset.Icc 1 D, (μ d : ℂ)*RoughSquarefreeCounting.markedDensity S d).re

/-- Exact arithmetic bridge for the sharp cutoff in the original
squarefree-coprimality measure. All divisor and exclusion signs remain. -/
theorem rough_count_eq_marks (S : Finset ℕ) (X D : ℕ) :
    ((∑ n ∈ Finset.Icc 1 X, ZetaRieszUnsignedDivisorError.sieve S n*sharp D n : ℝ) : ℂ) =
      ∑ d ∈ Finset.Icc 1 D, (μ d : ℂ)*RoughSquarefreeCounting.markedCount S d X := by
  have hi : Finset.Icc 1 X=Finset.Ioc 0 X := by ext n; simp; omega
  have he n : ((ZetaRieszUnsignedDivisorError.sieve S n*sharp D n : ℝ) : ℂ)=
      ∑ d ∈ Finset.Icc 1 D, (μ d : ℂ)*RoughSquarefreeBare.coefficient S d n := by
    by_cases hs : Squarefree n ∧ ¬∃ p ∈ S, p ∣ n
    · rw [ZetaRieszUnsignedDivisorError.sieve,if_pos hs,one_mul,sharp,Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d ∣ n
      · rw [if_pos hd,RoughSquarefreeBare.coefficient,if_pos ⟨hs.1,hs.2,hd⟩,mul_one]
        norm_cast
      · rw [if_neg hd,RoughSquarefreeBare.coefficient,if_neg (by tauto),mul_zero]
        rfl
    · have hd d : ¬(Squarefree n ∧ (¬∃ p ∈ S, p ∣ n) ∧ d ∣ n) :=
        fun h => hs ⟨h.1,h.2.1⟩
      rw [ZetaRieszUnsignedDivisorError.sieve,if_neg hs,zero_mul,Complex.ofReal_zero]
      symm
      exact Finset.sum_eq_zero (fun d _ => by
        rw [RoughSquarefreeBare.coefficient,if_neg (hd d),mul_zero])
  rw [Complex.ofReal_sum]
  simp_rw [he]
  rw [Finset.sum_comm]
  simp only [RoughSquarefreeCounting.markedCount,hi,Finset.mul_sum]

/-- A genuine power counting error with all physical exclusions inside
the measure. Their exact weighted intersection cost is kept explicitly. -/
theorem rough_sharp_count_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (X D : ℕ) :
    |(∑ n ∈ Finset.Icc 1 X, ZetaRieszUnsignedDivisorError.sieve S n*sharp D n)-
      roughDensityPrefix S D*X| ≤
      countingConstant*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*
        (X : ℝ)^(3/4 : ℝ)*exp ((5/16 : ℝ)*log D) := by
  have hreal : (∑ n ∈ Finset.Icc 1 X,
      ZetaRieszUnsignedDivisorError.sieve S n*sharp D n)-roughDensityPrefix S D*X =
      (∑ d ∈ Finset.Icc 1 D, (μ d : ℂ)*
        (RoughSquarefreeCounting.markedCount S d X-
          RoughSquarefreeCounting.markedDensity S d*X)).re := by
    simp_rw [mul_sub,← mul_assoc]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,← rough_count_eq_marks S X D]
    simp [roughDensityPrefix,Complex.mul_re]
  rw [hreal]
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_sum_le _ _).trans
  have hC : 0 ≤ ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S :=
    ZetaRieszPrimeWeightedSieve.sieveCost_nonneg _ _
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D,
        (exp (primeSquareWeightMass (3/4))*(X : ℝ)^(3/4 : ℝ)*
          ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S)*
            (|(μ d : ℝ)| *∏ p ∈ d.primeFactors, primeSquareCorrectedWeight (3/4) p) := by
      apply Finset.sum_le_sum
      intro d _
      rw [norm_mul,show (μ d : ℂ)=((μ d : ℝ) : ℂ) by norm_cast,
        Complex.norm_real,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (rough_mark_error S hS d X)
        (abs_nonneg _)).trans_eq (by ring)
    _ = (exp (primeSquareWeightMass (3/4))*(X : ℝ)^(3/4 : ℝ)*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S)*
          (∑ d ∈ Finset.Icc 1 D,
            |(μ d : ℝ)| *∏ p ∈ d.primeFactors, primeSquareCorrectedWeight (3/4) p) := by
      rw [Finset.mul_sum]
    _ ≤ (exp (primeSquareWeightMass (3/4))*(X : ℝ)^(3/4 : ℝ)*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S)*
          (exp ((5/16 : ℝ)*log D)*divisorSquareDirichletMass (17/16)) :=
      mul_le_mul_of_nonneg_left (mark_sum_bound D) (by positivity)
    _ ≤ _ := by
      unfold countingConstant
      have hx : 0 ≤ exp (primeSquareWeightMass (3/4))*(X : ℝ)^(3/4 : ℝ)*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*exp ((5/16 : ℝ)*log D) := by positivity
      nlinarith only [hx]

/-- The long translated cutoff retains its fixed power saving with
every excluded-prime intersection still in the reference measure. -/
theorem rough_sharp_count_error_long (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {X D : ℕ} (hX : 0 < X) (hD : 0 < D) (hDX : D^4 ≤ X^3) :
    |(∑ n ∈ Finset.Icc 1 X, ZetaRieszUnsignedDivisorError.sieve S n*sharp D n)-
      roughDensityPrefix S D*X| ≤
      countingConstant*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*
        (X : ℝ)^(63/64 : ℝ) := by
  have hxr : (0 : ℝ)<X := by exact_mod_cast hX
  have hdr : (0 : ℝ)<D := by exact_mod_cast hD
  have hl : 4*log D ≤ 3*log X := by
    have h := log_le_log (pow_pos hdr 4)
      (show (D : ℝ)^4 ≤ (X : ℝ)^3 by exact_mod_cast hDX)
    simpa only [log_pow,Nat.cast_ofNat] using h
  apply (rough_sharp_count_error S hS X D).trans
  have hp : (X : ℝ)^(3/4 : ℝ)*exp ((5/16 : ℝ)*log D) ≤
      (X : ℝ)^(63/64 : ℝ) := by
    rw [rpow_def_of_pos hxr,rpow_def_of_pos hxr,← exp_add]
    apply exp_le_exp.mpr
    linarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp
    (mul_nonneg countingConstant_pos.le
      (ZetaRieszPrimeWeightedSieve.sieveCost_nonneg _ _))

private theorem markedCount_norm_le (S : Finset ℕ) (d X : ℕ) :
    ‖RoughSquarefreeCounting.markedCount S d X‖ ≤ (X/d : ℕ) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 X, if d ∣ n then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro n _
      by_cases hd : d ∣ n
      · simp only [hd,if_true,RoughSquarefreeBare.coefficient]
        split_ifs <;> simp
      · simp only [hd,if_false,RoughSquarefreeBare.coefficient,
          and_false,norm_zero,le_refl]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
        Nat.Ioc_filter_dvd_card_eq_div]

private theorem markedDensity_norm_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {d : ℕ} (hd : 0 < d) :
    ‖RoughSquarefreeCounting.markedDensity S d‖ ≤ (d : ℝ)⁻¹ := by
  apply le_of_tendsto (RoughSquarefreeCounting.markedCount_div_tendsto S hS d).norm
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with X hX
  have hxr : (0 : ℝ)<X := by exact_mod_cast hX
  have hdr : (0 : ℝ)<d := by exact_mod_cast hd
  rw [norm_div,show ‖(X : ℂ)‖=(X : ℝ) by simp]
  calc
    _ ≤ ((X/d : ℕ) : ℝ)/(X : ℝ) :=
      div_le_div_of_nonneg_right (markedCount_norm_le S d X) hxr.le
    _ ≤ ((X : ℝ)/(d : ℝ))/(X : ℝ) :=
      div_le_div_of_nonneg_right (Nat.cast_div_le (m := X) (n := d)) hxr.le
    _ = _ := by field_simp

/-- The signed rough density scalar has only a logarithmic absolute
bound. The arithmetic scalar itself is never replaced in the main term. -/
theorem roughDensityPrefix_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (D : ℕ) :
    |roughDensityPrefix S D| ≤ 1+log D := by
  apply ((Complex.abs_re_le_norm _).trans (norm_sum_le _ _)).trans
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D, (d : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul,show (μ d : ℂ)=((μ d : ℝ) : ℂ) by norm_cast,
        Complex.norm_real,Real.norm_eq_abs]
      exact (mul_le_mul (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d))
        (markedDensity_norm_le S hS (Finset.mem_Icc.mp hd).1) (norm_nonneg _)
          (by norm_num : (0 : ℝ)≤1)).trans_eq (by ring)
    _ ≤ _ := by
      simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
        using harmonic_le_one_add_log D

private theorem roughDensityPrefix_one (S : Finset ℕ) :
    roughDensityPrefix S 1=ZetaRieszUnsignedDivisorError.density S := by
  have hc : (ZetaRieszUnsignedDivisorError.density S : ℂ)=
      RoughSquarefreeCounting.markedDensity S 1 := by
    simp [ZetaRieszUnsignedDivisorError.density,
      RoughSquarefreeCounting.markedDensity,Complex.ofReal_sum]
  simpa [roughDensityPrefix] using congrArg Complex.re hc.symm

/-- Genuine long-cutoff comparison for signed weights with exclusions
inside the arithmetic measure. Remaining literal variation is explicit. -/
theorem rough_weighted_error_exponential (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (X D N : ℕ) (q : ℕ → ℝ) (b : ℝ) (hend : q (X+1)=0) (hD : 0 < D)
    (hcut : ∀ k ∈ Finset.Icc 1 X, q k ≠ q (k+1) → D^4 ≤ k^3)
    (hlower : ∀ k ∈ Finset.Icc 1 X, q k ≠ q (k+1) → exp (b*N) ≤ k) :
    |(∑ n ∈ Finset.Icc 1 X, q n*ZetaRieszUnsignedDivisorError.sieve S n*sharp D n)-
      roughDensityPrefix S D*(∑ n ∈ Finset.Icc 1 X, q n)| ≤
      countingConstant*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*
        exp (-(b*N)/64)*(∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|) := by
  have he : (∑ n ∈ Finset.Icc 1 X, q n*ZetaRieszUnsignedDivisorError.sieve S n*sharp D n)-
      roughDensityPrefix S D*(∑ n ∈ Finset.Icc 1 X, q n) =
      ∑ k ∈ Finset.Icc 1 X, (q k-q (k+1))*
        ((∑ n ∈ Finset.Icc 1 k, ZetaRieszUnsignedDivisorError.sieve S n*sharp D n)-
          roughDensityPrefix S D*k) := by
    have hc (k : ℕ) : (∑ n ∈ Finset.Icc 1 k,
        (ZetaRieszUnsignedDivisorError.sieve S n*sharp D n-roughDensityPrefix S D)) =
        (∑ n ∈ Finset.Icc 1 k, ZetaRieszUnsignedDivisorError.sieve S n*sharp D n)-
          roughDensityPrefix S D*k := by
      simp only [Finset.sum_sub_distrib,Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,
        nsmul_eq_mul,mul_comm]
    rw [← Finset.sum_congr rfl
      (fun k _ => congrArg (fun z : ℝ => (q k-q (k+1))*z) (hc k))]
    rw [← ZetaRieszSignedCutoffEnergy.abel_profile X q _ hend]
    simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum,← mul_assoc]
    congr 1
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [he,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  by_cases hz : q k=q (k+1)
  · simp [hz]
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  have hkr : (0 : ℝ)<k := by exact_mod_cast hk0
  have hl : b*N ≤ log k := by
    simpa only [log_exp] using log_le_log (exp_pos _) (hlower k hk hz)
  have hp : (k : ℝ)^(63/64 : ℝ) ≤ exp (-(b*N)/64)*k := by
    conv_rhs => rw [← exp_log hkr]
    rw [rpow_def_of_pos hkr,← exp_add]
    apply exp_le_exp.mpr
    linarith
  rw [abs_mul]
  calc
    _ ≤ |q k-q (k+1)| *(countingConstant*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(k : ℝ)^(63/64 : ℝ)) :=
      mul_le_mul_of_nonneg_left (rough_sharp_count_error_long S hS hk0 hD
        (hcut k hk hz)) (abs_nonneg _)
    _ ≤ |q k-q (k+1)| *(countingConstant*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(exp (-(b*N)/64)*k)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp
        (mul_nonneg countingConstant_pos.le
          (ZetaRieszPrimeWeightedSieve.sieveCost_nonneg _ _))) (abs_nonneg _)
    _ = _ := by ring

/-- Center BOTH sums in the same actual squarefree-coprimality
measure. The signed rough density prefix remains one arithmetic scalar. -/
theorem rough_reference_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (X D N : ℕ) (q : ℕ → ℝ) (b : ℝ) (hend : q (X+1)=0) (hD : 0 < D)
    (hcut : ∀ k ∈ Finset.Icc 1 X, q k ≠ q (k+1) → D^4 ≤ k^3)
    (hlower : ∀ k ∈ Finset.Icc 1 X, q k ≠ q (k+1) → exp (b*N) ≤ k) :
    |ZetaRieszUnsignedDivisorError.density S*
        (∑ n ∈ Finset.Icc 1 X, q n*ZetaRieszUnsignedDivisorError.sieve S n*sharp D n)-
      roughDensityPrefix S D*
        (∑ n ∈ Finset.Icc 1 X, q n*ZetaRieszUnsignedDivisorError.sieve S n)| ≤
      (2+log D)*countingConstant*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*
        exp (-(b*N)/64)*(∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|) := by
  let rho := ZetaRieszUnsignedDivisorError.density S
  let A := ∑ n ∈ Finset.Icc 1 X, q n*ZetaRieszUnsignedDivisorError.sieve S n*sharp D n
  let B := ∑ n ∈ Finset.Icc 1 X, q n*ZetaRieszUnsignedDivisorError.sieve S n
  let M := ∑ n ∈ Finset.Icc 1 X, q n
  let E := countingConstant*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*
    exp (-(b*N)/64)*(∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|)
  have hA : |A-roughDensityPrefix S D*M| ≤ E :=
    rough_weighted_error_exponential S hS X D N q b hend hD hcut hlower
  have hB : |B-rho*M| ≤ E := by
    have h1cut : ∀ k ∈ Finset.Icc 1 X, q k ≠ q (k+1) → (1 : ℕ)^4 ≤ k^3 := by
      intro k hk _
      simpa only [one_pow] using Nat.pow_le_pow_left (Finset.mem_Icc.mp hk).1 3
    have h := rough_weighted_error_exponential S hS X 1 N q b hend (by omega)
      h1cut hlower
    simpa [sharp,roughDensityPrefix_one,B,rho,M,E] using h
  have hR : |rho| ≤ 1 := by
    simpa [rho,roughDensityPrefix_one] using roughDensityPrefix_bound S hS 1
  change |rho*A-roughDensityPrefix S D*B| ≤ _
  rw [show (2+log D)*countingConstant*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*
    exp (-(b*N)/64)*(∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|)=
      (2+log D)*E by dsimp [E]; ring]
  rw [show rho*A-roughDensityPrefix S D*B =
      rho*(A-roughDensityPrefix S D*M)-roughDensityPrefix S D*(B-rho*M) by ring]
  calc
    _ ≤ |rho*(A-roughDensityPrefix S D*M)|+
        |roughDensityPrefix S D*(B-rho*M)| := abs_sub _ _
    _ = |rho| * |A-roughDensityPrefix S D*M|+
        |roughDensityPrefix S D| * |B-rho*M| := by rw [abs_mul,abs_mul]
    _ ≤ 1*E+(1+log D)*E := add_le_add
      (mul_le_mul hR hA (abs_nonneg _) (by norm_num))
      (mul_le_mul (roughDensityPrefix_bound S hS D) hB (abs_nonneg _)
        (by linarith [log_natCast_nonneg D]))
    _ = _ := by ring

/-- Join the complete cutoff profile before comparing the actual
rough squarefree rows. No divisor-profile sign is lost in the main. -/
theorem rough_profile_reference_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {X R : ℕ} (N : ℕ) (q f : ℕ → ℝ) (b : ℝ) (hw : q (X+1)=0) (hf : f (R+1)=0)
    (hcut : ∀ k ∈ Finset.Icc 1 X, q k ≠ q (k+1) → R^4 ≤ k^3)
    (hlower : ∀ k ∈ Finset.Icc 1 X, q k ≠ q (k+1) → exp (b*N) ≤ k) :
    |ZetaRieszUnsignedDivisorError.density S*
        (∑ n ∈ Finset.Icc 1 X, q n*ZetaRieszUnsignedDivisorError.sieve S n*
          (∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (μ d : ℝ) else 0)))-
      (∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*roughDensityPrefix S D)*
        (∑ n ∈ Finset.Icc 1 X, q n*ZetaRieszUnsignedDivisorError.sieve S n)| ≤
      (2+log R)*countingConstant*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*
        exp (-(b*N)/64)*(∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|)*
      (∑ D ∈ Finset.Icc 1 R, |f D-f (D+1)|) := by
  have he (n : ℕ) : (∑ d ∈ Finset.Icc 1 R,
      f d*(if d ∣ n then (μ d : ℝ) else 0)) =
      ∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*sharp D n := by
    exact ZetaRieszSignedCutoffEnergy.abel_profile R f _ hf
  have hj : (∑ n ∈ Finset.Icc 1 X, q n*ZetaRieszUnsignedDivisorError.sieve S n*
      (∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (μ d : ℝ) else 0))) =
      ∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*
        (∑ n ∈ Finset.Icc 1 X, q n*ZetaRieszUnsignedDivisorError.sieve S n*sharp D n) := by
    simp_rw [he,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro D _
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hj,Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ D ∈ Finset.Icc 1 R, |f D-f (D+1)| *
        ((2+log R)*countingConstant*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*
          exp (-(b*N)/64)*(∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|)) := by
      apply Finset.sum_le_sum
      intro D hD
      have h := rough_reference_error S hS X D N q b hw (Finset.mem_Icc.mp hD).1
        (fun k hk hz => (Nat.pow_le_pow_left (Finset.mem_Icc.mp hD).2 4).trans
          (hcut k hk hz)) hlower
      have hl : log D ≤ log R := log_le_log
        (by exact_mod_cast (Finset.mem_Icc.mp hD).1) (by exact_mod_cast (Finset.mem_Icc.mp hD).2)
      have hcost : 0 ≤ countingConstant*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*
          exp (-(b*N)/64)*(∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|) := by
        positivity [ZetaRieszPrimeWeightedSieve.sieveCost_nonneg (3/4) S,
          countingConstant_pos]
      have hb := h.trans (show (2+log D)*countingConstant*
          ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*exp (-(b*N)/64)*
            (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|) ≤
          (2+log R)*countingConstant*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*
            exp (-(b*N)/64)*(∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|) from by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (add_le_add le_rfl hl) hcost)
      rw [show ZetaRieszUnsignedDivisorError.density S*
          ((f D-f (D+1))*(∑ n ∈ Finset.Icc 1 X,
            q n*ZetaRieszUnsignedDivisorError.sieve S n*sharp D n))-
          (f D-f (D+1))*roughDensityPrefix S D*
            (∑ n ∈ Finset.Icc 1 X, q n*ZetaRieszUnsignedDivisorError.sieve S n) =
          (f D-f (D+1))*(ZetaRieszUnsignedDivisorError.density S*
            (∑ n ∈ Finset.Icc 1 X, q n*ZetaRieszUnsignedDivisorError.sieve S n*sharp D n)-
              roughDensityPrefix S D*
                (∑ n ∈ Finset.Icc 1 X, q n*ZetaRieszUnsignedDivisorError.sieve S n)) by ring,
        abs_mul]
      exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

private theorem rough_rows_iff (B : Finset ℕ)
    (hB : ∀ n ∈ B, 3 ≤ n.primeFactors.card) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) {a p : ℕ} (hpS : p ∉ S) :
    p ∈ ZetaRieszJointPrimeEnergy.ownerRows
        (B.filter (fun n => Squarefree n ∧ ¬∃ q ∈ S, q ∣ n)) a ↔
      (Squarefree a ∧ ¬∃ q ∈ S, q ∣ a) ∧
        p ∈ ZetaRieszJointPrimeEnergy.ownerRows
          (B.filter (fun n => ¬largestPrime n ∣ ZetaRieszOwnedCells.ownerCofactor n)) a := by
  constructor
  · intro hr
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hr
    obtain ⟨hn,ha⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn,hs,hnS⟩ := Finset.mem_filter.mp hn
    have hsrow : p ∈ ZetaRieszJointPrimeEnergy.ownerRows (B.filter Squarefree) a :=
      Finset.mem_image.mpr ⟨n,Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hn,hs⟩,ha⟩,he⟩
    have hd := squarefree_rows_iff B hB a p |>.mp hsrow
    have hpf := ZetaRieszOwnedCells.largestPrime_mem_of_two (m := n)
      (by have := hB n hn; omega)
    have hmul : p*a=n := by
      have h := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hpf)
      change largestPrime n*ZetaRieszOwnedCells.ownerCofactor n=n at h
      rw [ha,he] at h
      exact h
    refine ⟨⟨hd.1,?_⟩,hd.2⟩
    rintro ⟨q,hq,hqa⟩
    exact hnS ⟨q,hq,hqa.trans (hmul ▸ Nat.dvd_mul_left a p)⟩
  · rintro ⟨⟨hs,haS⟩,hr⟩
    have hsrow := (squarefree_rows_iff B hB a p).mpr ⟨hs,hr⟩
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hsrow
    obtain ⟨hn,ha⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn,hnSF⟩ := Finset.mem_filter.mp hn
    have hpf := ZetaRieszOwnedCells.largestPrime_mem_of_two (m := n)
      (by have := hB n hn; omega)
    have hp : p.Prime := he ▸ Nat.prime_of_mem_primeFactors hpf
    have hmul : p*a=n := by
      have h := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hpf)
      change largestPrime n*ZetaRieszOwnedCells.ownerCofactor n=n at h
      rw [ha,he] at h
      exact h
    have hnS : ¬∃ q ∈ S, q ∣ n := by
      rintro ⟨q,hq,hqn⟩
      rw [← hmul] at hqn
      rcases (hS q hq).dvd_mul.mp hqn with hqp|hqa
      · rcases (Nat.dvd_prime hp).mp hqp with hq1|hqp
        · exact (hS q hq).ne_one hq1
        · exact hpS (hqp ▸ hq)
      · exact haS ⟨q,hq,hqa⟩
    exact Finset.mem_image.mpr ⟨n,Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hn,hnSF,hnS⟩,ha⟩,he⟩

/-- The original squarefree/coprimality support is exactly the rough
reference measure times the uncompleted masked weight. -/
theorem beforeSquares_rough_eq_literal (A B : Finset ℕ)
    (hB : ∀ n ∈ B, 3 ≤ n.primeFactors.card) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hpS : p ∉ S)
    (L y scale : ℝ) (N a : ℕ) :
    beforeSquaresWeight A B L y scale N a p*ZetaRieszUnsignedDivisorError.sieve S a =
      ZetaRieszJointPrimeEnergy.maskedWeight A
        (ZetaRieszJointPrimeEnergy.ownerRows
          (B.filter (fun n => Squarefree n ∧ ¬∃ q ∈ S, q ∣ n))) L y scale N a p := by
  unfold beforeSquaresWeight ZetaRieszJointPrimeEnergy.maskedWeight
    ZetaRieszUnsignedDivisorError.sieve
  simp only [rough_rows_iff B hB S hS hpS]
  by_cases hs : Squarefree a ∧ ¬∃ q ∈ S, q ∣ a
  · simp only [hs,not_false_eq_true,if_true,true_and,mul_one]
  · simp only [hs,if_false,false_and,mul_zero]

/-- The translated hinge estimate applies to the literal rough
subpopulation of the original core. All owner/count/phase/allocation
masks stay in `q`; squarefree and exclusion holes do not enter its
variation. No such variation or signed main is assumed paid. -/
theorem literal_rough_reference_error {u : ℝ} (hu : 1/2 ≤ u)
    {N K : ℕ} (hN : 32 ≤ N) (B : Finset ℕ) (hB : B ⊆ coreBand u N K)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (A : Finset ℕ) (y scale : ℝ)
    {p : ℕ} (hpS : p ∉ S) :
    let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
    let L := SquarefreeVaughanLogSource.length u N
    let c := L-log p
    let R := ⌊exp c⌋₊
    let q := fun n => beforeSquaresWeight A B L y scale N n p
    let w := fun n => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows
        (B.filter (fun n => Squarefree n ∧ ¬∃ v ∈ S, v ∣ n))) L y scale N n p
    |ZetaRieszUnsignedDivisorError.density S*
        (∑ n ∈ Finset.Icc 1 X, w n*VaughanLogAverage.riesz c n)-
      (∑ D ∈ Finset.Icc 1 R,
        (max 0 (c-log D)-max 0 (c-log (D+1 : ℕ)))*roughDensityPrefix S D)*
          (∑ n ∈ Finset.Icc 1 X, w n)| ≤
      (2+max 0 c)*countingConstant*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*
        exp (-(N : ℝ)/128)*
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|)*max 0 c := by
  dsimp only
  let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
  let L := SquarefreeVaughanLogSource.length u N
  let c := L-log p
  let R := ⌊exp c⌋₊
  let f : ℕ → ℝ := fun d => max 0 (c-log d)
  let B0 := B.filter (fun n => ¬largestPrime n ∣ ZetaRieszOwnedCells.ownerCofactor n)
  let q := fun n => beforeSquaresWeight A B L y scale N n p
  let w := fun n => ZetaRieszJointPrimeEnergy.maskedWeight A
    (ZetaRieszJointPrimeEnergy.ownerRows
      (B.filter (fun n => Squarefree n ∧ ¬∃ v ∈ S, v ∣ n))) L y scale N n p
  have hBB : ∀ n ∈ B, 3 ≤ n.primeFactors.card :=
    fun _ hn => ZetaRieszJointPrimeEnergy.core_count (hB hn)
  have hb n : q n*ZetaRieszUnsignedDivisorError.sieve S n=w n :=
    beforeSquares_rough_eq_literal A B hBB S hS hpS L y scale N n
  have hw : q (X+1)=0 := by
    have hn : p ∉ ZetaRieszJointPrimeEnergy.ownerRows B0 (X+1) := by
      intro hp
      obtain ⟨m,hm,_⟩ := Finset.mem_image.mp hp
      obtain ⟨hm,he⟩ := Finset.mem_filter.mp hm
      have ha : X+1 ∈ ZetaRieszJointPrimeEnergy.cofactors B :=
        Finset.mem_image.mpr ⟨m,(Finset.mem_filter.mp hm).1,he⟩
      have hl := Finset.le_sup (f := id) ha
      dsimp [X] at hl
      omega
    exact if_neg hn
  have hleft : (∑ n ∈ Finset.Icc 1 X, q n*ZetaRieszUnsignedDivisorError.sieve S n*
      (∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (μ d : ℝ) else 0))) =
      ∑ n ∈ Finset.Icc 1 X, w n*VaughanLogAverage.riesz c n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hb,← riesz_eq_hinge_profile c (Finset.mem_Icc.mp hn).1]
  have hsum : (∑ n ∈ Finset.Icc 1 X, q n*ZetaRieszUnsignedDivisorError.sieve S n)=
      ∑ n ∈ Finset.Icc 1 X, w n := Finset.sum_congr rfl (fun n _ => hb n)
  change |ZetaRieszUnsignedDivisorError.density S*_-
    (∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*roughDensityPrefix S D)*
      (∑ n ∈ Finset.Icc 1 X, w n)| ≤ _
  rw [← hleft,← hsum]
  by_cases hR : R=0
  · simp [hR]
    positivity [countingConstant_pos,ZetaRieszPrimeWeightedSieve.sieveCost_nonneg (3/4) S]
  have hs k (hk : k ∈ Finset.Icc 1 X) (hz : q k ≠ q (k+1)) :=
    literal_masked_support hu hN B0 (fun _ hn => hB (Finset.mem_filter.mp hn).1)
      A y scale p (by omega : 0 < R) (Nat.floor_le (exp_pos c).le)
        (Finset.mem_Icc.mp hk).1 hz
  have h := rough_profile_reference_error S hS N q f (1/2) hw (hinge_profile_end c)
    (fun k hk hz => (hs k hk hz).1)
    (fun k hk hz => by
      have he : (1/2 : ℝ)*N=(N : ℝ)/2 := by ring
      rw [he]
      exact (hs k hk hz).2)
  have he : -((1/2 : ℝ)*N)/64=-(N : ℝ)/128 := by ring
  rw [he,hinge_profile_variation c] at h
  have hlog : log R ≤ max 0 c := by
    have hx : (0 : ℝ)<R := by exact_mod_cast (show 0 < R by omega)
    exact (show log R ≤ c from by
      simpa only [log_exp] using log_le_log hx (Nat.floor_le (exp_pos c).le)).trans
        (le_max_right 0 c)
  exact h.trans (by
    have hn : 0 ≤ countingConstant*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*
        exp (-(N : ℝ)/128)*(∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|)*max 0 c := by
      positivity [countingConstant_pos,ZetaRieszPrimeWeightedSieve.sieveCost_nonneg (3/4) S]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (add_le_add le_rfl hlog) hn)

/-- Assemble the literal rough subpopulation over ALL canonical owners
and counts. Both hinges remain joined in the signed main. Physical
exclusions are in the measure; no support completion is made. -/
theorem literal_rough_joined_carrier_estimate {u : ℝ} (hu : 1/2 ≤ u)
    {N K : ℕ} (hN : 32 ≤ N) (B : Finset ℕ) (hB : B ⊆ coreBand u N K)
    (F : Finset ℕ) (hF : ∀ q ∈ F, q.Prime) (A : Finset ℕ) (y scale : ℝ) :
    let S := B.filter (fun n => Squarefree n ∧ ¬∃ q ∈ F, q ∣ n)
    let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
    let L := SquarefreeVaughanLogSource.length u N
    let P := ZetaRieszJointPrimeEnergy.ownerPrimes S
    let rho := ZetaRieszUnsignedDivisorError.density F
    let w := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows S) L y scale N a p
    let q := fun a p => beforeSquaresWeight A B L y scale N a p
    |rho*(scale*(∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re)-
      (∑ p ∈ P,
        (rho*(∑ a ∈ Finset.Icc 1 X, w a p*VaughanLogAverage.riesz L a)-
          (∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
            (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*
              roughDensityPrefix F D)*(∑ a ∈ Finset.Icc 1 X, w a p)))| ≤
      countingConstant*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) F*
        exp (-(N : ℝ)/128)*
          (∑ p ∈ P, (2+max 0 (L-log p))*max 0 (L-log p)*
            (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k p-q (k+1) p|)) := by
  dsimp only
  let S := B.filter (fun n => Squarefree n ∧ ¬∃ q ∈ F, q ∣ n)
  let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
  let L := SquarefreeVaughanLogSource.length u N
  let P := ZetaRieszJointPrimeEnergy.ownerPrimes S
  let rho := ZetaRieszUnsignedDivisorError.density F
  let w := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
    (ZetaRieszJointPrimeEnergy.ownerRows S) L y scale N a p
  let q := fun a p => beforeSquaresWeight A B L y scale N a p
  have hS : ∀ n ∈ S, Squarefree n ∧ 3 ≤ n.primeFactors.card := by
    intro n hn
    obtain ⟨hn,hs,_⟩ := Finset.mem_filter.mp hn
    exact ⟨hs,ZetaRieszJointPrimeEnergy.core_count (hB hn)⟩
  have hx : (ZetaRieszJointPrimeEnergy.cofactors S).sup id ≤ X := by
    apply le_trans (Finset.sup_le _) (le_max_right _ _)
    intro a ha
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp ha
    exact Finset.le_sup (f := id) (Finset.mem_image.mpr
      ⟨n,(Finset.mem_filter.mp hn).1,he⟩)
  have hc := literal_owner_columns A S hS X hx L y scale N
  let H := fun p => ∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
    (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*roughDensityPrefix F D
  have he : rho*(scale*(∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re)-
      (∑ p ∈ P, (rho*(∑ a ∈ Finset.Icc 1 X, w a p*VaughanLogAverage.riesz L a)-
        H p*(∑ a ∈ Finset.Icc 1 X, w a p))) =
      -(∑ p ∈ P, (rho*(∑ a ∈ Finset.Icc 1 X,
          w a p*VaughanLogAverage.riesz (L-log p) a)-H p*(∑ a ∈ Finset.Icc 1 X, w a p))) := by
    rw [hc]
    simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
    ring
  change |_-(∑ p ∈ P, (rho*(∑ a ∈ Finset.Icc 1 X, w a p*VaughanLogAverage.riesz L a)-
    H p*(∑ a ∈ Finset.Icc 1 X, w a p)))| ≤ _
  rw [he,abs_neg,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hpF : p ∉ F := by
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hp
    have hpf := ZetaRieszOwnedCells.largestPrime_mem_of_two (m := n)
      (by have := (hS n hn).2; omega)
    intro hit
    exact (Finset.mem_filter.mp hn).2.2 ⟨p,hit,he ▸ Nat.dvd_of_mem_primeFactors hpf⟩
  have h := literal_rough_reference_error hu hN B hB F hF A y scale hpF
  exact h.trans_eq (by dsimp [X,L,H,w,q,rho,P,S] at *; ring)

/-- At the stronger counting exponent, exclusions through N² cost only
exp(O(N^(17/32))), rather than an exponential in N. -/
theorem rough_sieveCost_small_primes_bound {N : ℕ} (hN : 0 < N) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N^2) :
    ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S ≤
      exp (2*ZetaRieszPrimeWeightedSieve.prefixMass*(N : ℝ)^(17/32 : ℝ)) := by
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have hw p (hp : p ∈ S) : primeSquareCorrectedWeight (3/4) p ≤
      2*(N : ℝ)^(17/32 : ℝ)*zetaPrimeExpWeight (65/64) p := by
    have ht : 0 ≤ zetaPrimeExpWeight (3/4) p := (exp_pos _).le
    have hu : zetaPrimeExpWeight (3/4) p ≤ 1 := by
      rw [zetaPrimeExpWeight,exp_le_one_iff]
      nlinarith [log_natCast_nonneg p]
    have hl : log p ≤ 2*log N := by
      have h := log_le_log (show (0 : ℝ)<p by exact_mod_cast (hS p hp).1.pos)
        (show (p : ℝ)≤(N : ℝ)^2 by exact_mod_cast (hS p hp).2)
      simpa only [log_pow,Nat.cast_ofNat] using h
    have hh : zetaPrimeExpWeight (3/4) p ≤
        (N : ℝ)^(17/32 : ℝ)*zetaPrimeExpWeight (65/64) p := by
      rw [zetaPrimeExpWeight,zetaPrimeExpWeight,rpow_def_of_pos hn,← exp_add]
      apply exp_le_exp.mpr
      nlinarith
    unfold primeSquareCorrectedWeight
    nlinarith [mul_le_mul_of_nonneg_left hu ht]
  have hm : (∑ p ∈ S, zetaPrimeExpWeight (65/64) p) ≤
      ZetaRieszPrimeWeightedSieve.prefixMass :=
    (summable_zetaPrimeExpWeight (by norm_num : (1 : ℝ)<65/64)).sum_le_tsum S
      (fun _ _ => (exp_pos _).le)
  calc
    _ ≤ exp (∑ p ∈ S, primeSquareCorrectedWeight (3/4) p) :=
      Real.prod_one_add_le_exp_sum S (fun p => primeSquareCorrectedWeight_nonneg _ p)
    _ ≤ exp (2*(N : ℝ)^(17/32 : ℝ)*∑ p ∈ S, zetaPrimeExpWeight (65/64) p) := by
      apply exp_le_exp.mpr
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hw
    _ ≤ _ := by
      apply exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_left hm
        (by positivity : (0 : ℝ)≤2*(N : ℝ)^(17/32 : ℝ))).trans_eq (by ring)

/-- The physical exclusion prefactor is genuinely geometrically small.
This theorem does not replace the remaining literal variation by a
smooth-shell variation, and does not pay the signed arithmetic main. -/
theorem eventually_rough_counting_rate :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ p ≤ N^2) →
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*exp (-(N : ℝ)/128) ≤
          exp (-(N : ℝ)/256) := by
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<15/32)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hm := ht.const_mul (2*ZetaRieszPrimeWeightedSieve.prefixMass)
  simp only [mul_zero] at hm
  filter_upwards [hm.eventually_lt_const (by norm_num : (0 : ℝ)<1/256),
    Filter.eventually_ge_atTop (1 : ℕ)] with N h hN
  simp only [Function.comp_apply] at h
  intro S hS
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have hpow : (N : ℝ)^(17/32 : ℝ)=(N : ℝ)^(-(15/32 : ℝ))*(N : ℝ) := by
    calc
      _ = (N : ℝ)^(-(15/32 : ℝ)+1) := by norm_num
      _ = (N : ℝ)^(-(15/32 : ℝ))*(N : ℝ)^1 := rpow_add hn _ _
      _ = _ := by rw [rpow_one]
  have hs : 2*ZetaRieszPrimeWeightedSieve.prefixMass*(N : ℝ)^(17/32 : ℝ) ≤
      (N : ℝ)/256 := by
    rw [hpow]
    have hh := mul_le_mul_of_nonneg_right h.le hn.le
    nlinarith only [hh]
  calc
    _ ≤ exp (2*ZetaRieszPrimeWeightedSieve.prefixMass*(N : ℝ)^(17/32 : ℝ))*
        exp (-(N : ℝ)/128) :=
      mul_le_mul_of_nonneg_right (rough_sieveCost_small_primes_bound hN S hS) (exp_pos _).le
    _ = exp (2*ZetaRieszPrimeWeightedSieve.prefixMass*(N : ℝ)^(17/32 : ℝ)-(N : ℝ)/128) := by
      rw [← exp_add]; congr 1; ring
    _ ≤ _ := exp_le_exp.mpr (by linarith)

/-- Every physical exclusion density is a positive product. The exact
normalization is retained when the canonical owner is also excluded. -/
theorem rough_density_product (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ZetaRieszUnsignedDivisorError.density S=SquarefreeCounting.density ∅*
      ∏ p ∈ S, (p : ℝ)/((p : ℝ)+1) := by
  have hs : ZetaRieszUnsignedDivisorError.density S=SquarefreeCounting.density ∅*
      (∑ W ∈ S.powerset, (-1 : ℝ)^W.card*∏ p ∈ W, ((p : ℝ)+1)⁻¹) := by
    unfold ZetaRieszUnsignedDivisorError.density
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro W hW
    rw [ZetaRieszSignedDensityMain.density_marks W
      (fun p hp => hS p (Finset.mem_powerset.mp hW hp))]
    ring
  rw [hs]
  have hp : (∏ p ∈ S, (1-((p : ℝ)+1)⁻¹))=
      ∑ W ∈ S.powerset, (-1 : ℝ)^W.card*∏ p ∈ W, ((p : ℝ)+1)⁻¹ := by
    simpa only [Finset.prod_const_one,mul_one] using
      Finset.prod_sub (fun _ : ℕ => (1 : ℝ)) (fun p => ((p : ℝ)+1)⁻¹) S
  rw [← hp]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  have hne : (p : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

/-- Conditioning on the literal finite prime exclusions is never
division by a zero density. -/
theorem rough_density_pos (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    0 < ZetaRieszUnsignedDivisorError.density S := by
  rw [rough_density_product S hS]
  exact mul_pos squarefree_density_pos (Finset.prod_pos (fun p hp =>
    div_pos (by exact_mod_cast (hS p hp).pos) (by positivity)))

private theorem repeated_owner_rows_iff (B : Finset ℕ) (a p : ℕ) :
    p ∈ ZetaRieszJointPrimeEnergy.ownerRows
        (B.filter (fun n => ¬largestPrime n ∣ ZetaRieszOwnedCells.ownerCofactor n)) a ↔
      (¬p ∣ a) ∧ p ∈ ZetaRieszJointPrimeEnergy.ownerRows B a := by
  constructor
  · intro hp
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hp
    obtain ⟨hn,ha⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn,hcop⟩ := Finset.mem_filter.mp hn
    rw [he,ha] at hcop
    exact ⟨hcop,Finset.mem_image.mpr ⟨n,Finset.mem_filter.mpr ⟨hn,ha⟩,he⟩⟩
  · rintro ⟨hcop,hp⟩
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hp
    obtain ⟨hn,ha⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_image.mpr ⟨n,Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hn,?_⟩,ha⟩,he⟩
    simpa only [he,ha] using hcop

private theorem owner_rough_rows_iff (B : Finset ℕ)
    (hB : ∀ n ∈ B, 3 ≤ n.primeFactors.card) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) {a p : ℕ} (hpS : p ∉ S) :
    p ∈ ZetaRieszJointPrimeEnergy.ownerRows
        (B.filter (fun n => Squarefree n ∧ ¬∃ q ∈ S, q ∣ n)) a ↔
      (Squarefree a ∧ ¬∃ q ∈ insert p S, q ∣ a) ∧
        p ∈ ZetaRieszJointPrimeEnergy.ownerRows B a := by
  rw [rough_rows_iff B hB S hS hpS,repeated_owner_rows_iff]
  simp only [Finset.mem_insert,or_and_right,exists_or,exists_eq_left,not_or]
  tauto

/-- Repeated-owner holes are now also part of the actual arithmetic
measure. The variation weight has NONE of the squarefree, coprimality
or repeated-owner zero extensions, and every other mask remains literal. -/
theorem raw_rough_eq_literal (A B : Finset ℕ)
    (hB : ∀ n ∈ B, 3 ≤ n.primeFactors.card) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hpS : p ∉ S)
    (L y scale : ℝ) (N a : ℕ) :
    ZetaRieszJointPrimeEnergy.maskedWeight A (ZetaRieszJointPrimeEnergy.ownerRows B)
        L y scale N a p*ZetaRieszUnsignedDivisorError.sieve (insert p S) a =
      ZetaRieszJointPrimeEnergy.maskedWeight A
        (ZetaRieszJointPrimeEnergy.ownerRows
          (B.filter (fun n => Squarefree n ∧ ¬∃ q ∈ S, q ∣ n))) L y scale N a p := by
  unfold ZetaRieszJointPrimeEnergy.maskedWeight ZetaRieszUnsignedDivisorError.sieve
  simp only [owner_rough_rows_iff B hB S hS hpS]
  by_cases hs : Squarefree a ∧ ¬∃ q ∈ insert p S, q ∣ a
  · simp only [hs,not_false_eq_true,if_true,true_and,mul_one]
  · simp only [hs,if_false,false_and,mul_zero]

/-- An estimate on the actual translated owner column without charging
repeated-owner holes as adjacent variation. The owner-dependent density
is explicit and positive; no carrier support is completed. -/
theorem literal_raw_rough_reference_error {u : ℝ} (hu : 1/2 ≤ u)
    {N K : ℕ} (hN : 32 ≤ N) (B : Finset ℕ) (hB : B ⊆ coreBand u N K)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (A : Finset ℕ) (y scale : ℝ)
    {p : ℕ} (hp : p.Prime) (hpS : p ∉ S) :
    let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
    let L := SquarefreeVaughanLogSource.length u N
    let c := L-log p
    let R := ⌊exp c⌋₊
    let q := fun n => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N n p
    let w := fun n => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows
        (B.filter (fun n => Squarefree n ∧ ¬∃ v ∈ S, v ∣ n))) L y scale N n p
    |ZetaRieszUnsignedDivisorError.density (insert p S)*
        (∑ n ∈ Finset.Icc 1 X, w n*VaughanLogAverage.riesz c n)-
      (∑ D ∈ Finset.Icc 1 R,
        (max 0 (c-log D)-max 0 (c-log (D+1 : ℕ)))*roughDensityPrefix (insert p S) D)*
          (∑ n ∈ Finset.Icc 1 X, w n)| ≤
      (2+max 0 c)*countingConstant*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) (insert p S)*
        exp (-(N : ℝ)/128)*
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|)*max 0 c := by
  dsimp only
  let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
  let L := SquarefreeVaughanLogSource.length u N
  let c := L-log p
  let R := ⌊exp c⌋₊
  let f : ℕ → ℝ := fun d => max 0 (c-log d)
  let q := fun n => ZetaRieszJointPrimeEnergy.maskedWeight A
    (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N n p
  let w := fun n => ZetaRieszJointPrimeEnergy.maskedWeight A
    (ZetaRieszJointPrimeEnergy.ownerRows
      (B.filter (fun n => Squarefree n ∧ ¬∃ v ∈ S, v ∣ n))) L y scale N n p
  have hBB : ∀ n ∈ B, 3 ≤ n.primeFactors.card :=
    fun _ hn => ZetaRieszJointPrimeEnergy.core_count (hB hn)
  have hSp : ∀ v ∈ insert p S, v.Prime := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl|hv
    · exact hp
    · exact hS v hv
  have hb n : q n*ZetaRieszUnsignedDivisorError.sieve (insert p S) n=w n :=
    raw_rough_eq_literal A B hBB S hS hpS L y scale N n
  have hw : q (X+1)=0 := by
    have hn : p ∉ ZetaRieszJointPrimeEnergy.ownerRows B (X+1) := by
      intro hp
      obtain ⟨m,hm,_⟩ := Finset.mem_image.mp hp
      obtain ⟨hm,he⟩ := Finset.mem_filter.mp hm
      have ha : X+1 ∈ ZetaRieszJointPrimeEnergy.cofactors B :=
        Finset.mem_image.mpr ⟨m,hm,he⟩
      have hl := Finset.le_sup (f := id) ha
      dsimp [X] at hl
      omega
    exact if_neg hn
  have hleft : (∑ n ∈ Finset.Icc 1 X, q n*ZetaRieszUnsignedDivisorError.sieve (insert p S) n*
      (∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (μ d : ℝ) else 0))) =
      ∑ n ∈ Finset.Icc 1 X, w n*VaughanLogAverage.riesz c n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hb,← riesz_eq_hinge_profile c (Finset.mem_Icc.mp hn).1]
  have hsum : (∑ n ∈ Finset.Icc 1 X, q n*ZetaRieszUnsignedDivisorError.sieve (insert p S) n)=
      ∑ n ∈ Finset.Icc 1 X, w n := Finset.sum_congr rfl (fun n _ => hb n)
  change |ZetaRieszUnsignedDivisorError.density (insert p S)*_-
    (∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*roughDensityPrefix (insert p S) D)*
      (∑ n ∈ Finset.Icc 1 X, w n)| ≤ _
  rw [← hleft,← hsum]
  by_cases hR : R=0
  · simp [hR]
    positivity [countingConstant_pos,
      ZetaRieszPrimeWeightedSieve.sieveCost_nonneg (3/4) (insert p S)]
  have hs k (hk : k ∈ Finset.Icc 1 X) (hz : q k ≠ q (k+1)) :=
    literal_masked_support hu hN B hB A y scale p (by omega : 0 < R)
      (Nat.floor_le (exp_pos c).le) (Finset.mem_Icc.mp hk).1 hz
  have h := rough_profile_reference_error (insert p S) hSp N q f (1/2) hw (hinge_profile_end c)
    (fun k hk hz => (hs k hk hz).1)
    (fun k hk hz => by
      have he : (1/2 : ℝ)*N=(N : ℝ)/2 := by ring
      rw [he]
      exact (hs k hk hz).2)
  have he : -((1/2 : ℝ)*N)/64=-(N : ℝ)/128 := by ring
  rw [he,hinge_profile_variation c] at h
  have hlog : log R ≤ max 0 c := by
    have hx : (0 : ℝ)<R := by exact_mod_cast (show 0 < R by omega)
    exact (show log R ≤ c from by
      simpa only [log_exp] using log_le_log hx (Nat.floor_le (exp_pos c).le)).trans
        (le_max_right 0 c)
  exact h.trans (by
    have hn : 0 ≤ countingConstant*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) (insert p S)*
        exp (-(N : ℝ)/128)*(∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|)*max 0 c := by
      positivity [countingConstant_pos,
        ZetaRieszPrimeWeightedSieve.sieveCost_nonneg (3/4) (insert p S)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (add_le_add le_rfl hlog) hn)

/-- Exact owner conditioning restores one COMMON density without
approximating its factor or losing the signed owner sum. -/
theorem rough_owner_normalization (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime)
    {p : ℕ} (hp : p.Prime) (hpS : p ∉ S) :
    ((p : ℝ)+1)/(p : ℝ)*ZetaRieszUnsignedDivisorError.density (insert p S)=
      ZetaRieszUnsignedDivisorError.density S := by
  have hSp : ∀ q ∈ insert p S, q.Prime := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl|hq
    · exact hp
    · exact hS q hq
  rw [rough_density_product (insert p S) hSp,rough_density_product S hS,
    Finset.prod_insert hpS]
  have hpp : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ)+1 ≠ 0 := by positivity
  field_simp

private theorem owner_cost_le (S : Finset ℕ) {p : ℕ} (hpS : p ∉ S) :
    ZetaRieszPrimeWeightedSieve.sieveCost (3/4) (insert p S) ≤
      3*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S := by
  have ht : 0 ≤ zetaPrimeExpWeight (3/4) p := (exp_pos _).le
  have hu : zetaPrimeExpWeight (3/4) p ≤ 1 := by
    rw [zetaPrimeExpWeight,exp_le_one_iff]
    nlinarith [log_natCast_nonneg p]
  have hw : 1+primeSquareCorrectedWeight (3/4) p ≤ 3 := by
    unfold primeSquareCorrectedWeight
    nlinarith [mul_le_mul_of_nonneg_left hu ht]
  unfold ZetaRieszPrimeWeightedSieve.sieveCost
  rw [Finset.prod_insert hpS]
  exact mul_le_mul_of_nonneg_right hw
    (ZetaRieszPrimeWeightedSieve.sieveCost_nonneg (3/4) S)

/-- The actual masked column has a common-reference estimate with
squarefree, excluded-prime AND repeated-owner holes all absent from the
variation. The signed scalar is conditioned exactly, not approximated. -/
theorem literal_normalized_raw_reference_error {u : ℝ} (hu : 1/2 ≤ u)
    {N K : ℕ} (hN : 32 ≤ N) (B : Finset ℕ) (hB : B ⊆ coreBand u N K)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (A : Finset ℕ) (y scale : ℝ)
    {p : ℕ} (hp : p.Prime) (hpS : p ∉ S) :
    let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
    let L := SquarefreeVaughanLogSource.length u N
    let c := L-log p
    let R := ⌊exp c⌋₊
    let q := fun n => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N n p
    let w := fun n => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows
        (B.filter (fun n => Squarefree n ∧ ¬∃ v ∈ S, v ∣ n))) L y scale N n p
    |ZetaRieszUnsignedDivisorError.density S*
        (∑ n ∈ Finset.Icc 1 X, w n*VaughanLogAverage.riesz c n)-
      (((p : ℝ)+1)/(p : ℝ))*(∑ D ∈ Finset.Icc 1 R,
        (max 0 (c-log D)-max 0 (c-log (D+1 : ℕ)))*roughDensityPrefix (insert p S) D)*
          (∑ n ∈ Finset.Icc 1 X, w n)| ≤
      6*(2+max 0 c)*countingConstant*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*
        exp (-(N : ℝ)/128)*
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|)*max 0 c := by
  dsimp only
  let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
  let L := SquarefreeVaughanLogSource.length u N
  let c := L-log p
  let R := ⌊exp c⌋₊
  let q := fun n => ZetaRieszJointPrimeEnergy.maskedWeight A
    (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N n p
  let w := fun n => ZetaRieszJointPrimeEnergy.maskedWeight A
    (ZetaRieszJointPrimeEnergy.ownerRows
      (B.filter (fun n => Squarefree n ∧ ¬∃ v ∈ S, v ∣ n))) L y scale N n p
  let H := ∑ D ∈ Finset.Icc 1 R,
    (max 0 (c-log D)-max 0 (c-log (D+1 : ℕ)))*roughDensityPrefix (insert p S) D
  let r := ((p : ℝ)+1)/(p : ℝ)
  let E := (2+max 0 c)*countingConstant*exp (-(N : ℝ)/128)*
    (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|)*max 0 c
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr2 : r ≤ 2 := by
    apply (div_le_iff₀ (show (0 : ℝ)<p by exact_mod_cast hp.pos)).mpr
    have hp2 : (2 : ℝ)≤p := by exact_mod_cast hp.two_le
    linarith
  have hn := rough_owner_normalization S hS hp hpS
  have hE : 0 ≤ E := by dsimp [E]; positivity [countingConstant_pos]
  have hcost : r*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) (insert p S) ≤
      6*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S :=
    (mul_le_mul hr2 (owner_cost_le S hpS)
      (ZetaRieszPrimeWeightedSieve.sieveCost_nonneg (3/4) (insert p S))
        (by norm_num : (0 : ℝ)≤2)).trans_eq (by ring)
  have h := literal_raw_rough_reference_error hu hN B hB S hS A y scale hp hpS
  change |_ - r*H*(∑ n ∈ Finset.Icc 1 X, w n)| ≤ _
  calc
    _ = |r*(ZetaRieszUnsignedDivisorError.density (insert p S)*
        (∑ n ∈ Finset.Icc 1 X, w n*VaughanLogAverage.riesz c n)-
          H*(∑ n ∈ Finset.Icc 1 X, w n))| := by
      congr 1
      rw [mul_sub,← mul_assoc,hn]
      ring
    _ = r*|ZetaRieszUnsignedDivisorError.density (insert p S)*
        (∑ n ∈ Finset.Icc 1 X, w n*VaughanLogAverage.riesz c n)-
          H*(∑ n ∈ Finset.Icc 1 X, w n)| := by rw [abs_mul,abs_of_nonneg hr0]
    _ ≤ r*((2+max 0 c)*countingConstant*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) (insert p S)*exp (-(N : ℝ)/128)*
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|)*max 0 c) :=
      mul_le_mul_of_nonneg_left h hr0
    _ = E*(r*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) (insert p S)) := by dsimp [E]; ring
    _ ≤ E*(6*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S) :=
      mul_le_mul_of_nonneg_left hcost hE
    _ = _ := by dsimp [E,c,L,q,X]; ring

/-- The joined estimate for the literal carrier before ALL squarefree,
coprimality and repeated-owner holes. Choosing F empty gives the entire
original squarefree core; no roughness condition is silently added.
Every remaining count/owner/radial/allocation/phase mask stays in q. -/
theorem literal_normalized_raw_carrier_estimate {u : ℝ} (hu : 1/2 ≤ u)
    {N K : ℕ} (hN : 32 ≤ N) (B : Finset ℕ) (hB : B ⊆ coreBand u N K)
    (F : Finset ℕ) (hF : ∀ q ∈ F, q.Prime) (A : Finset ℕ) (y scale : ℝ) :
    let S := B.filter (fun n => Squarefree n ∧ ¬∃ q ∈ F, q ∣ n)
    let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
    let L := SquarefreeVaughanLogSource.length u N
    let P := ZetaRieszJointPrimeEnergy.ownerPrimes S
    let rho := ZetaRieszUnsignedDivisorError.density F
    let w := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows S) L y scale N a p
    let q := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N a p
    |rho*(scale*(∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re)-
      (∑ p ∈ P,
        (rho*(∑ a ∈ Finset.Icc 1 X, w a p*VaughanLogAverage.riesz L a)-
          (((p : ℝ)+1)/(p : ℝ))*(∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
            (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*
              roughDensityPrefix (insert p F) D)*(∑ a ∈ Finset.Icc 1 X, w a p)))| ≤
      6*countingConstant*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) F*
        exp (-(N : ℝ)/128)*
          (∑ p ∈ P, (2+max 0 (L-log p))*max 0 (L-log p)*
            (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k p-q (k+1) p|)) := by
  dsimp only
  let S := B.filter (fun n => Squarefree n ∧ ¬∃ q ∈ F, q ∣ n)
  let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
  let L := SquarefreeVaughanLogSource.length u N
  let P := ZetaRieszJointPrimeEnergy.ownerPrimes S
  let rho := ZetaRieszUnsignedDivisorError.density F
  let w := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
    (ZetaRieszJointPrimeEnergy.ownerRows S) L y scale N a p
  let q := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N a p
  have hS : ∀ n ∈ S, Squarefree n ∧ 3 ≤ n.primeFactors.card := by
    intro n hn
    obtain ⟨hn,hs,_⟩ := Finset.mem_filter.mp hn
    exact ⟨hs,ZetaRieszJointPrimeEnergy.core_count (hB hn)⟩
  have hx : (ZetaRieszJointPrimeEnergy.cofactors S).sup id ≤ X := by
    apply le_trans (Finset.sup_le _) (le_max_right _ _)
    intro a ha
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp ha
    exact Finset.le_sup (f := id) (Finset.mem_image.mpr
      ⟨n,(Finset.mem_filter.mp hn).1,he⟩)
  have hc := literal_owner_columns A S hS X hx L y scale N
  let H := fun (p : ℕ) => (((p : ℝ)+1)/(p : ℝ))*(∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
    (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*roughDensityPrefix (insert p F) D)
  have he : rho*(scale*(∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re)-
      (∑ p ∈ P, (rho*(∑ a ∈ Finset.Icc 1 X, w a p*VaughanLogAverage.riesz L a)-
        H p*(∑ a ∈ Finset.Icc 1 X, w a p))) =
      -(∑ p ∈ P, (rho*(∑ a ∈ Finset.Icc 1 X,
          w a p*VaughanLogAverage.riesz (L-log p) a)-H p*(∑ a ∈ Finset.Icc 1 X, w a p))) := by
    rw [hc]
    simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
    ring
  change |_-(∑ p ∈ P, (rho*(∑ a ∈ Finset.Icc 1 X, w a p*VaughanLogAverage.riesz L a)-
    H p*(∑ a ∈ Finset.Icc 1 X, w a p)))| ≤ _
  rw [he,abs_neg,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hpF : p ∉ F := by
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hp
    have hpf := ZetaRieszOwnedCells.largestPrime_mem_of_two (m := n)
      (by have := (hS n hn).2; omega)
    intro hit
    exact (Finset.mem_filter.mp hn).2.2 ⟨p,hit,he ▸ Nat.dvd_of_mem_primeFactors hpf⟩
  have hpp : p.Prime := by
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hp
    have hpf := ZetaRieszOwnedCells.largestPrime_mem_of_two (m := n)
      (by have := (hS n hn).2; omega)
    exact he ▸ Nat.prime_of_mem_primeFactors hpf
  have h := literal_normalized_raw_reference_error hu hN B hB F hF A y scale hpp hpF
  exact h.trans_eq (by dsimp [X,L,H,w,q,rho,P,S] at *; ring)

/-- The stronger comparison on the ENTIRE original squarefree core,
with no added roughness condition. The variation uses its original raw
owner rows, not a zero extension by squarefreeness or repeated owners.
All counts and both signed hinges are joined before any error estimate. -/
theorem literal_whole_carrier_estimate {u : ℝ} (hu : 1/2 ≤ u)
    {N K : ℕ} (hN : 32 ≤ N) (B : Finset ℕ) (hB : B ⊆ coreBand u N K)
    (A : Finset ℕ) (y scale : ℝ) :
    let S := B.filter Squarefree
    let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
    let L := SquarefreeVaughanLogSource.length u N
    let P := ZetaRieszJointPrimeEnergy.ownerPrimes S
    let rho := SquarefreeCounting.density ∅
    let w := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows S) L y scale N a p
    let q := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N a p
    |rho*(scale*(∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re)-
      (∑ p ∈ P,
        (rho*(∑ a ∈ Finset.Icc 1 X, w a p*VaughanLogAverage.riesz L a)-
          (((p : ℝ)+1)/(p : ℝ))*(∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
            (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*
              roughDensityPrefix {p} D)*(∑ a ∈ Finset.Icc 1 X, w a p)))| ≤
      6*countingConstant*exp (-(N : ℝ)/128)*
        (∑ p ∈ P, (2+max 0 (L-log p))*max 0 (L-log p)*
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k p-q (k+1) p|)) := by
  have h := literal_normalized_raw_carrier_estimate hu hN B hB ∅ (by simp) A y scale
  simpa [ZetaRieszUnsignedDivisorError.density,ZetaRieszPrimeWeightedSieve.sieveCost] using h

end RiemannGaussian.ZetaRieszLongCutoffError
