/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorBinaryEulerControl
import RiemannGaussian.ArithmeticOperatorFloorInverseAudit
import RiemannGaussian.ZetaPrimeWindow

/-!
# Coherent unit-prime controls preserve bulk density information

The existing binary subset of ordinary primes has a full factorial source
-2, genuine unit Euler factors, all free feature Grams, and every proper
power. Here its deleted Mangoldt mass is independently shown to be o(X).
Even moving bounded (or dyadically polylogarithmic) modular/Gaussian tests
cannot distinguish the control from the actual sequence at density scale.

This is a collapse audit, NOT a bound for the unaltered prime source. The
control still fails complete actual Gamma equalities. Nothing here proves
source-scale closeness, a continuation of the control Euler product, or RH.
-/

namespace RiemannGaussian.ArithmeticOperatorBinaryDensityAudit
noncomputable section
open ArithmeticOperatorBinaryPrimeControl ArithmeticOperatorPrimeTowerControl Filter
open ZetaRieszCeilingPrimeThinningAudit
open scoped BigOperators Classical Topology

/-- The same fixed, unit-weight prime subset used in the Euler audit. -/
def control (u y : ℝ) (n : ℕ) : ℝ := towerCoefficient (retainedBase u y) n

/-- Complete physical loss, including EVERY proper power and endpoint. -/
def loss (u y : ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (X+1), (ArithmeticFunction.vonMangoldt n-control u y n)

/-- Ordinary-prime deleted logarithmic mass before the proper-power payment. -/
def primeLoss (u y : ℝ) (X : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (X+1), Real.log p*removedBase u y p

/-- Exact count of the deleted UNIT primes; not a rounded continuous density. -/
def deletedCount (u y : ℝ) (X : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (X+1), removedBase u y p

theorem control_bounds (u y : ℝ) (n : ℕ) :
    0≤control u y n ∧ control u y n≤ArithmeticFunction.vonMangoldt n :=
  towerCoefficient_bounds _ (fun p => (binaryBase_bounds u y p).2) n

theorem loss_nonneg (u y : ℝ) (X : ℕ) : 0≤loss u y X :=
  Finset.sum_nonneg (fun n _ => sub_nonneg.mpr (control_bounds u y n).2)

theorem loss_monotone (u y : ℝ) : Monotone (loss u y) := by
  intro X Y hXY
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega : X+1≤Y+1))
  intro n _ _
  exact sub_nonneg.mpr (control_bounds u y n).2

/-- Cumulative integer rounding only decreases the complete deleted count. -/
theorem deletedCount_le_prefix (u y : ℝ) (X : ℕ) :
    deletedCount u y X≤primePrefix u y (X+1) := by
  unfold deletedCount removedBase
  rw [binaryPrimeAtom_sum]
  apply Nat.floor_le
  unfold primePrefix
  apply Finset.sum_nonneg
  intro p _
  by_cases hp : p.Prime
  · simp only [hp,ite_true]
    exact (clippedWeight_bounds u y p).1
  · simp only [hp,ite_false,le_refl]

/-- Strictly subunit tail factor as soon as u>1/2; it is NOT the
stronger source-scale factor which would imply actual non-coherence. -/
def densityRate (u : ℝ) : ℝ := Real.exp (-(u-1/2)*Real.log 2)

theorem densityRate_bounds {u : ℝ} (hu : 1/2<u) :
    0<densityRate u ∧ densityRate u<1 := by
  constructor
  · exact Real.exp_pos _
  · apply Real.exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (by linarith) (Real.log_pos (by norm_num))

private theorem clipped_large_le {u : ℝ} (hu : 1/2<u) (y : ℝ)
    {J p : ℕ} (hp : 2^J<p) : clippedWeight u y p≤8*densityRate u^J := by
  have hlo : ((J : ℝ)*Real.log 2)≤Real.log p := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ)<(2 : ℝ)^J)
      (by exact_mod_cast hp.le : (2 : ℝ)^J≤p)
    simpa only [Real.log_pow] using hh
  apply (min_le_right 1 (rawWeight u y p)).trans (rawWeight_le u y p |>.trans ?_)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ Real.exp (-(u-1/2)*((J : ℝ)*Real.log 2)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hlo (by linarith)
    _ = densityRate u^J := by
      unfold densityRate
      rw [←Real.exp_nat_mul]
      congr 1
      ring

/-- Uniform integer head/tail bound for the actual binary deletion.
No prime-density approximation and no phase averaging is used. -/
theorem deletedCount_dyadic_le {u : ℝ} (hu : 1/2<u) (y : ℝ) (J : ℕ) :
    deletedCount u y (2^(2*J))≤
      2*(2 : ℝ)^J+16*(2 : ℝ)^(2*J)*densityRate u^J := by
  apply (deletedCount_le_prefix u y _).trans
  let S := Finset.range (2^(2*J)+1)
  have ht (p : ℕ) :
      (if p.Prime then clippedWeight u y p else 0)≤
        (if p≤2^J then 1 else 8*densityRate u^J) := by
    by_cases hl : p≤2^J
    · rw [ite_eq_left hl]
      by_cases hprime : p.Prime
      · simp only [hprime,ite_true]
        exact (clippedWeight_bounds u y p).2
      · simp only [hprime,ite_false]; norm_num
    · rw [ite_eq_right hl]
      by_cases hprime : p.Prime
      · rw [ite_eq_left hprime]
        exact clipped_large_le hu y (by omega)
      · rw [ite_eq_right hprime]
        exact mul_nonneg (by norm_num) (pow_nonneg (Real.exp_pos _).le _)
  have hs := Finset.sum_le_sum (s := S) (fun p _ => ht p)
  have hhead : ((S.filter (fun p => p≤2^J)).card : ℝ)≤2*(2 : ℝ)^J := by
    have hsub : S.filter (fun p => p≤2^J) ⊆ Finset.range (2^J+1) := by
      intro p hp
      exact Finset.mem_range.mpr (by have hh := (Finset.mem_filter.mp hp).2; omega)
    have hh : (S.filter (fun p => p≤2^J)).card≤2*2^J := by
      have hcard := Finset.card_le_card hsub
      have hpow : 1≤(2 : ℕ)^J := Nat.one_le_pow _ _ (by norm_num)
      simp only [Finset.card_range] at hcard
      omega
    exact_mod_cast hh
  have htail : ((S.filter (fun p => ¬p≤2^J)).card : ℝ)≤2*(2 : ℝ)^(2*J) := by
    have hh : (S.filter (fun p => ¬p≤2^J)).card≤2*2^(2*J) := by
      dsimp only [S]
      have hcard := Finset.card_le_card (Finset.filter_subset (fun p => ¬p≤2^J) S)
      have hpow : 1≤(2 : ℕ)^(2*J) := Nat.one_le_pow _ _ (by norm_num)
      simp only [S,Finset.card_range] at hcard
      omega
    exact_mod_cast hh
  unfold primePrefix
  apply hs.trans
  calc
    _ = ((S.filter (fun p => p≤2^J)).card : ℝ)+
        ((S.filter (fun p => ¬p≤2^J)).card : ℝ)*(8*densityRate u^J) := by
      simp only [Finset.sum_ite,Finset.sum_const,nsmul_eq_mul,mul_one]
    _ ≤ 2*(2 : ℝ)^J+(2*(2 : ℝ)^(2*J))*(8*densityRate u^J) :=
      add_le_add hhead (mul_le_mul_of_nonneg_right htail
        (mul_nonneg (by norm_num) (pow_nonneg (densityRate_bounds hu).1.le _)))
    _ = _ := by ring

/-- Integer endpoint rounding is retained when paying the log weight. -/
theorem primeLoss_le_log_mul_count (u y : ℝ) (X : ℕ) :
    primeLoss u y X≤Real.log X*deletedCount u y X := by
  unfold primeLoss deletedCount
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hlog : Real.log p≤Real.log X := by
    by_cases hp0 : p=0
    · simp only [hp0,Nat.cast_zero,Real.log_zero]
      exact Real.log_natCast_nonneg X
    · have hpX : p≤X := by have hh := Finset.mem_range.mp hp; omega
      exact Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hp0))
        (by exact_mod_cast hpX)
  exact mul_le_mul_of_nonneg_right hlog (binaryBase_bounds u y p).1.1

/-- Every deleted proper power is accounted for by the independent complete
psi-minus-theta budget, without dropping its underlying base weight. -/
theorem loss_le_primeLoss_add_proper (u y : ℝ) (X : ℕ) :
    loss u y X≤primeLoss u y X+Chebyshev.psi X-Chebyshev.theta X := by
  have hs : loss u y X-primeLoss u y X≤
      ∑ n ∈ Finset.range (X+1),
        (ArithmeticFunction.vonMangoldt n-(if n.Prime then Real.log n else 0)) := by
    unfold loss primeLoss
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro n _
    by_cases hn : n.Prime
    · simp only [hn,ite_true,control,towerCoefficient,hn.minFac_eq,
        ArithmeticFunction.vonMangoldt_apply_prime hn,retainedBase]
      ring_nf
      exact le_refl _
    · rw [ite_eq_right hn]
      have hb : removedBase u y n=0 := by
        simpa only [removedBase,Nat.cast_zero] using
          congrArg (fun k : ℕ => (k : ℝ)) (binaryPrimeAtom_composite u y hn)
      simp only [hb,mul_zero,sub_zero]
      exact sub_le_self _ (control_bounds u y n).1
  have he : (∑ n ∈ Finset.range (X+1),
      (ArithmeticFunction.vonMangoldt n-(if n.Prime then Real.log n else 0))) =
      Chebyshev.psi X-Chebyshev.theta X := by
    rw [Chebyshev.psi_eq_sum_Icc,Chebyshev.theta_eq_sum_Icc]
    simp only [Nat.floor_natCast,Finset.sum_filter]
    rw [Nat.range_succ_eq_Icc_zero]
    exact Finset.sum_sub_distrib _ _
  rw [he] at hs
  linarith

/-- Quantitative bulk-density allowance, not a source-scale saving.
The full physical endpoint and all positive prime-power orders are retained. -/
theorem loss_dyadic_le {u : ℝ} (hu : 1/2<u) (y : ℝ) (J : ℕ) :
    loss u y (2^(2*J))≤
      (2*(J : ℝ)*Real.log 2)*(2*(2 : ℝ)^J+16*(2 : ℝ)^(2*J)*densityRate u^J)+
        18*(2 : ℝ)^J := by
  have hproper := chebyshevPsi_sub_theta_le_eighteen_sqrt
    (x := (2^(2*J) : ℕ)) (by
      exact_mod_cast (Nat.one_le_pow _ _ (by norm_num) : 1≤(2 : ℕ)^(2*J)))
  have hsqrt : Real.sqrt ((2^(2*J) : ℕ) : ℝ)=(2 : ℝ)^J := by
    push_cast
    rw [show 2*J=J*2 by omega,pow_mul,Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ)≤(2 : ℝ)^J)]
  rw [hsqrt] at hproper
  have hp := (primeLoss_le_log_mul_count u y (2^(2*J))).trans
    (mul_le_mul_of_nonneg_left (deletedCount_dyadic_le hu y J)
      (Real.log_natCast_nonneg (2^(2*J))))
  have hlog : Real.log ((2^(2*J) : ℕ) : ℝ)=2*(J : ℝ)*Real.log 2 := by
    simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_mul]
  rw [hlog] at hp
  have hh := loss_le_primeLoss_add_proper u y (2^(2*J))
  linarith

/-- Exact normalized budget. Its rate is relative to X, not X^beta. -/
def densityBudget (u : ℝ) (J : ℕ) : ℝ :=
  (4*(J : ℝ)*Real.log 2+18)*(1/2 : ℝ)^J+
    32*(J : ℝ)*Real.log 2*densityRate u^J

theorem loss_div_dyadic_le {u : ℝ} (hu : 1/2<u) (y : ℝ) (J : ℕ) :
    loss u y (2^(2*J))/(2 : ℝ)^(2*J)≤densityBudget u J := by
  apply (div_le_div_of_nonneg_right (loss_dyadic_le hu y J)
    (by positivity : (0 : ℝ)≤(2 : ℝ)^(2*J))).trans_eq
  unfold densityBudget
  rw [show 2*J=J*2 by omega,pow_mul,div_pow,one_pow]
  field_simp
  ring

/-- ANY fixed polylogarithmic amplification still loses the deletion at
density scale. No factorial source envelope is multiplied by this bound. -/
theorem tendsto_polynomial_loss_density {u : ℝ} (hu : 1/2<u) (y : ℝ) (D : ℕ) :
    Tendsto (fun J : ℕ => ((J+1 : ℕ) : ℝ)^D*
      (loss u y (2^(2*J))/(2 : ℝ)^(2*J))) atTop (𝓝 0) := by
  have hhalf := ArithmeticOperatorFloorInverseAudit.tendsto_shifted_polynomial_geometric
    (D+1) (r := 1/2) (by norm_num) (by norm_num)
  have hr := ArithmeticOperatorFloorInverseAudit.tendsto_shifted_polynomial_geometric
    (D+1) (densityRate_bounds hu).1 (densityRate_bounds hu).2
  have hlim := (hhalf.const_mul (4*Real.log 2+18)).add (hr.const_mul (32*Real.log 2))
  simp only [mul_zero,add_zero] at hlim
  apply squeeze_zero (fun J => mul_nonneg (by positivity)
    (div_nonneg (loss_nonneg u y _) (by positivity))) _ hlim
  intro J
  have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hfirst : 4*(J : ℝ)*Real.log 2+18≤(4*Real.log 2+18)*((J+1 : ℕ) : ℝ) := by
    push_cast
    nlinarith only [hlog,show (0 : ℝ)≤J by positivity]
  have hsecond : 32*(J : ℝ)*Real.log 2≤(32*Real.log 2)*((J+1 : ℕ) : ℝ) := by
    push_cast
    nlinarith only [hlog]
  calc
    _ ≤ ((J+1 : ℕ) : ℝ)^D*densityBudget u J :=
      mul_le_mul_of_nonneg_left (loss_div_dyadic_le hu y J) (by positivity)
    _ ≤ ((J+1 : ℕ) : ℝ)^D*
        ((4*Real.log 2+18)*((J+1 : ℕ) : ℝ)*(1/2 : ℝ)^J+
          (32*Real.log 2)*((J+1 : ℕ) : ℝ)*densityRate u^J) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul_of_nonneg_right hfirst (by positivity))
        (mul_le_mul_of_nonneg_right hsecond (pow_nonneg (densityRate_bounds hu).1.le _))
    _ = _ := by rw [pow_succ]; ring

/-- Exact difference of coded physical populations; a code may retain
any literal phase, floor, GCD, modular or Gaussian mask. -/
def codedDifference (u y : ℝ) (X : ℕ) (code : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.range (X+1),
    ((ArithmeticFunction.vonMangoldt n : ℂ)-(control u y n : ℂ))*code n

theorem norm_codedDifference_le {B : ℝ} (u y : ℝ) (X : ℕ)
    (code : ℕ → ℂ) (hcode : ∀ n≤X, ‖code n‖≤B) :
    ‖codedDifference u y X code‖≤B*loss u y X := by
  unfold codedDifference loss
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hpos : 0≤ArithmeticFunction.vonMangoldt n-control u y n :=
    sub_nonneg.mpr (control_bounds u y n).2
  rw [←Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_of_nonneg hpos]
  exact (mul_le_mul_of_nonneg_left (hcode n (by have hh := Finset.mem_range.mp hn; omega))
    hpos).trans_eq (by ring)

/-- Uniform moving polylogarithmic codes cannot distinguish the coherent
control at density scale. This is NOT source-scale mask removal. -/
theorem tendsto_codedDifference_density {u : ℝ} (hu : 1/2<u) (y : ℝ)
    (D : ℕ) {B : ℝ} (code : ℕ → ℕ → ℂ)
    (hcode : ∀ J n, n≤2^(2*J) → ‖code J n‖≤B*((J+1 : ℕ) : ℝ)^D) :
    Tendsto (fun J : ℕ => (((2 : ℝ)^(2*J))⁻¹ : ℂ)*
      codedDifference u y (2^(2*J)) (code J)) atTop (𝓝 0) := by
  have hlim := (tendsto_polynomial_loss_density hu y D).const_mul B
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm (a := fun J : ℕ => B*(((J+1 : ℕ) : ℝ)^D*
    (loss u y (2^(2*J))/(2 : ℝ)^(2*J)))) _ hlim
  intro J
  rw [norm_mul,norm_inv,norm_pow]
  norm_num only [Complex.norm_real,Real.norm_of_nonneg (by norm_num : (0 : ℝ)≤2)]
  apply (mul_le_mul_of_nonneg_left
    (norm_codedDifference_le u y _ (code J) (hcode J)) (by positivity)).trans_eq
  ring

private theorem monotone_density_tendsto (f : ℕ → ℝ) (hf : ∀ n, 0≤f n)
    (hmono : Monotone f)
    (hlim : Tendsto (fun J : ℕ => f (4^J)/(4 : ℝ)^J) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => f n/(n : ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨J0,hJ0⟩ := Metric.tendsto_atTop.mp hlim (eps/4) (by positivity)
  refine ⟨4^J0,fun n hn => ?_⟩
  have hn0 : 0<n := by
    have hh : 1≤(4 : ℕ)^J0 := Nat.one_le_pow _ _ (by norm_num)
    omega
  let J := Nat.log 4 n+1
  have hlarge : n<4^J := Nat.lt_pow_succ_log_self (by norm_num) n
  have hsmall : 4^J≤4*n := by
    have hh := Nat.pow_log_le_self 4 hn0.ne'
    dsimp only [J]
    rw [pow_succ]
    nlinarith only [hh]
  have hJ : J0≤J := by
    by_contra hh
    have hp : 4^J≤4^J0 := Nat.pow_le_pow_right (by norm_num : 0<(4 : ℕ)) (by omega)
    omega
  have hj := hJ0 J hJ
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (hf _) (by positivity))] at hj
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (hf _) (by positivity))]
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn0
  calc
    _ ≤ f (4^J)/(n : ℝ) :=
      div_le_div_of_nonneg_right (hmono hlarge.le) hnR.le
    _ = (f (4^J)/(4 : ℝ)^J)*((4 : ℝ)^J/(n : ℝ)) := by field_simp
    _ ≤ (f (4^J)/(4 : ℝ)^J)*4 := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (hf _) (by positivity))
      apply (div_le_iff₀ hnR).mpr
      exact_mod_cast hsmall
    _ < eps := by linarith

/-- Deleted Mangoldt mass is o(X) at EVERY integer cutoff, not merely
on a cofinal probe sequence. The complete actual sequence is not reweighted
when proving the PNT used subsequently. -/
theorem tendsto_loss_density {u : ℝ} (hu : 1/2<u) (y : ℝ) :
    Tendsto (fun X : ℕ => loss u y X/(X : ℝ)) atTop (𝓝 0) := by
  have hd := tendsto_polynomial_loss_density hu y 0
  simp only [pow_zero,one_mul] at hd
  have h4 : Tendsto (fun J : ℕ => loss u y (4^J)/(4 : ℝ)^J) atTop (𝓝 0) := by
    convert hd using 1
    funext J
    rw [pow_mul,pow_mul]
    norm_num
  exact monotone_density_tendsto (loss u y) (loss_nonneg u y) (loss_monotone u y) h4

/-- A bounded moving matrix/phase/modular test remains indistinguishable
at density scale on ALL integer cutoffs. Its source-scale discrepancy is
not paid by this result. -/
theorem tendsto_bounded_codes_all_cutoffs {u : ℝ} (hu : 1/2<u) (y : ℝ)
    {B : ℝ} (code : ℕ → ℕ → ℂ)
    (hcode : ∀ X n, n≤X → ‖code X n‖≤B) :
    Tendsto (fun X : ℕ => ((X : ℝ)⁻¹ : ℂ)*codedDifference u y X (code X))
      atTop (𝓝 0) := by
  have hlim := (tendsto_loss_density hu y).const_mul B
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm (a := fun X : ℕ => B*(loss u y X/(X : ℝ))) _ hlim
  intro X
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (by positivity : (0 : ℝ)≤X)]
  apply (mul_le_mul_of_nonneg_left (norm_codedDifference_le u y X (code X) (hcode X))
    (by positivity)).trans_eq
  ring

/-- Complete Chebyshev prefix of the SAME unit-prime Euler control. -/
def controlPrefix (u y : ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (X+1), control u y n

theorem controlPrefix_eq_psi_sub_loss (u y : ℝ) (X : ℕ) :
    controlPrefix u y X=Chebyshev.psi X-loss u y X := by
  rw [Chebyshev.psi_eq_sum_Icc]
  simp only [Nat.floor_natCast,←Nat.range_succ_eq_Icc_zero,loss,
    Finset.sum_sub_distrib,controlPrefix]
  ring

/-- The coherent unit-prime Euler system satisfies the actual qualitative
PNT normalization at ALL integer endpoints, despite its -2 factorial source. -/
theorem tendsto_control_prefix_density {u : ℝ} (hu : 1/2<u) (y : ℝ) :
    Tendsto (fun X : ℕ => controlPrefix u y X/(X : ℝ)) atTop (𝓝 1) := by
  have hp := chebyshevPsi_div_tendsto_one.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := hp.sub (tendsto_loss_density hu y)
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [] with X
  rw [controlPrefix_eq_psi_sub_loss]
  simp only [Function.comp_apply]
  ring

/-- Density agreement and literal unit Euler support therefore cannot imply
prime-moment non-coherence: the single established control has BOTH. -/
theorem density_and_coherent_full_source :
    Tendsto (fun X : ℕ => controlPrefix (10001/20000) 54 X/(X : ℝ)) atTop (𝓝 1) ∧
    Tendsto (ArithmeticOperatorPrimeTowerControl.fullMoment
      (retainedBase (10001/20000) 54) (10001/20000) 54) atTop (𝓝 (-2)) :=
  ⟨tendsto_control_prefix_density (by norm_num) 54,
    ArithmeticOperatorBinaryPrimeControl.fullMoment_target_tendsto⟩

/-- Complete, nonseparable two-column operator difference. The SAME
literal complex mask is applied to both populations; every proper power,
the diagonal and every pair incidence remain present. -/
def matrixDifference (u y : ℝ) (X : ℕ) (K : ℕ → ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.range (X+1), ∑ e ∈ Finset.range (X+1),
    ((ArithmeticFunction.vonMangoldt d*ArithmeticFunction.vonMangoldt e-
      control u y d*control u y e : ℝ) : ℂ)*K d e

/-- Exact joined quadratic loss ledger before any norm. -/
theorem matrix_weight_loss_eq (u y : ℝ) (X : ℕ) :
    (∑ d ∈ Finset.range (X+1), ∑ e ∈ Finset.range (X+1),
      (ArithmeticFunction.vonMangoldt d*ArithmeticFunction.vonMangoldt e-
        control u y d*control u y e)) =
      loss u y X*(Chebyshev.psi X+controlPrefix u y X) := by
  have hpsi : (∑ n ∈ Finset.range (X+1),ArithmeticFunction.vonMangoldt n)=
      Chebyshev.psi X := by
    rw [Chebyshev.psi_eq_sum_Icc]
    simp only [Nat.floor_natCast,←Nat.range_succ_eq_Icc_zero]
  simp_rw [Finset.sum_sub_distrib]
  rw [←Finset.sum_mul_sum,←Finset.sum_mul_sum,hpsi]
  change Chebyshev.psi X*Chebyshev.psi X-controlPrefix u y X*controlPrefix u y X=_
  rw [controlPrefix_eq_psi_sub_loss]
  ring

/-- Bulk operator indistinguishability retains correlated prime columns,
not just separate matrix entries. This bound is relative to X^2. -/
theorem norm_matrixDifference_le {B : ℝ} (hB : 0≤B) (u y : ℝ) (X : ℕ)
    (K : ℕ → ℕ → ℂ) (hK : ∀ d≤X, ∀ e≤X, ‖K d e‖≤B) :
    ‖matrixDifference u y X K‖≤2*B*Chebyshev.psi X*loss u y X := by
  have ht (d e : ℕ) :
      0≤ArithmeticFunction.vonMangoldt d*ArithmeticFunction.vonMangoldt e-
        control u y d*control u y e := by
    apply sub_nonneg.mpr
    exact mul_le_mul (control_bounds u y d).2 (control_bounds u y e).2
      (control_bounds u y e).1 ArithmeticFunction.vonMangoldt_nonneg
  unfold matrixDifference
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun d _ => norm_sum_le _ _)).trans
  calc
    _ ≤ ∑ d ∈ Finset.range (X+1), ∑ e ∈ Finset.range (X+1),
        B*(ArithmeticFunction.vonMangoldt d*ArithmeticFunction.vonMangoldt e-
          control u y d*control u y e) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (ht d e)]
      exact (mul_le_mul_of_nonneg_left
        (hK d (by have hh := Finset.mem_range.mp hd; omega)
          e (by have hh := Finset.mem_range.mp he; omega)) (ht d e)).trans_eq (by ring)
    _ = B*(loss u y X*(Chebyshev.psi X+controlPrefix u y X)) := by
      simp_rw [←Finset.mul_sum]
      rw [matrix_weight_loss_eq]
    _ ≤ B*(loss u y X*(2*Chebyshev.psi X)) := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply mul_le_mul_of_nonneg_left _ (loss_nonneg u y X)
      rw [controlPrefix_eq_psi_sub_loss]
      linarith [loss_nonneg u y X]
    _ = _ := by ring

/-- Every moving bounded two-column mask is preserved at bulk density scale
by the coherent unit-prime control. No source-scale pair estimate follows. -/
theorem tendsto_matrixDifference_density {u : ℝ} (hu : 1/2<u) (y : ℝ)
    {B : ℝ} (hB : 0≤B) (K : ℕ → ℕ → ℕ → ℂ)
    (hK : ∀ X d, d≤X → ∀ e, e≤X → ‖K X d e‖≤B) :
    Tendsto (fun X : ℕ => ((X : ℂ)⁻¹)^2*matrixDifference u y X (K X))
      atTop (𝓝 0) := by
  have hpsi := chebyshevPsi_div_tendsto_one.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim := (hpsi.mul (tendsto_loss_density hu y)).const_mul (2*B)
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm (a := fun X : ℕ => 2*B*
    (Chebyshev.psi X/(X : ℝ)*(loss u y X/(X : ℝ)))) _ hlim
  intro X
  rw [norm_mul,norm_pow,norm_inv,Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left (norm_matrixDifference_le hB u y X (K X) (hK X))
    (by positivity)).trans_eq
  ring

end
end RiemannGaussian.ArithmeticOperatorBinaryDensityAudit
