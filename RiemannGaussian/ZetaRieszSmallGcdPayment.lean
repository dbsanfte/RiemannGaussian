/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszNearCriticalCountPayment
import RiemannGaussian.ZetaRieszAntiphaseCredit

/-!
# Pay a wider original shared-factor correlation family

The actual inverse-square common-factor mass admits a 99/100 tail
exponent rather than the preceding 1/2. This pays every selected
original cross pair with log(gcd)>N/4096, at source rate exp(-N/65536),
retaining arbitrary pair masks, phases, allocations and count supports.

The original nonOrbitEnergy is partitioned with its adverse cutoff set
UNCHANGED. The smaller-gcd signed aggregate is still unpaid. No count-
wise allowance, new carrier, phase orthogonality or zero hypothesis enters.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszSmallGcdPayment
open ZetaRieszDiagonalPayment ZetaRieszCofactorPhaseEnergy
open ZetaRieszJointPrimeEnergy ZetaRieszSmoothOwnerDiscrepancy
open ZetaRieszJointAllocation ZetaRieszSharedFactorPayment
open ZetaRieszWideOwnerAudit ZetaRieszCutoffPeriodFloor
open ZetaRieszPostHingeEnergy

/-- Restrict the ACTUAL adverse ordered pair energy by a pair mask.
The common factor is never replaced by an independent divisor model. -/
def maskedSharedEnergy (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    (M : ℕ → ℕ → Prop) : ℝ :=
  ∑ k ∈ ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f,
    (∑ n ∈ S,∑ m ∈ S.erase n,
      if (N : ℝ)/4096 < log (Nat.gcd n m) ∧ M n m then
        (w n*sharp k n)*(w m*sharp k m) else 0)/(k : ℝ)

/-- Reciprocal divisor pairs with a large ACTUAL gcd have an explicit
geometric sparsity bound, uniform in every selected squarefree population. -/
theorem large_common_factor_mass (X N : ℕ) (S : Finset ℕ) (hX : 0 < X)
    (hS : S ⊆ Finset.Icc 1 X) (hSF : ∀ n ∈ S,Squarefree n) :
    (∑ n ∈ S,∑ m ∈ S,
      if (N : ℝ)/4096 < log (Nat.gcd n m) then
        ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) ≤
      (exp (log X/262144)*divisorSquareDirichletMass (1+1/262144))^2*
        (exp (-(99/409600 : ℝ)*N)*divisorSquareDirichletMass (101/100)) := by
  let G := (Finset.Icc 1 X).filter (fun g : ℕ => (N : ℝ)/4096 < log g)
  let z := fun g n : ℕ => if g ∣ n then (n.divisors.card : ℝ)/(n : ℝ) else 0
  have hz g n : 0 ≤ z g n := by dsimp [z]; split_ifs <;> positivity
  have hpair n (hn : n ∈ S) m (hm : m ∈ S) :
      (if (N : ℝ)/4096 < log (Nat.gcd n m) then
        ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) ≤
          ∑ g ∈ G,z g n*z g m := by
    split_ifs with hl
    · have hnp : 0 < n := (Finset.mem_Icc.mp (hS hn)).1
      have hgp : 0 < Nat.gcd n m := Nat.gcd_pos_of_pos_left m hnp
      have hgm : Nat.gcd n m ∈ G := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hgp,
          (Nat.le_of_dvd hnp (Nat.gcd_dvd_left n m)).trans (Finset.mem_Icc.mp (hS hn)).2⟩,hl⟩
      simpa only [z,if_pos (Nat.gcd_dvd_left n m),if_pos (Nat.gcd_dvd_right n m)] using
        Finset.single_le_sum (fun g (_ : g ∈ G) => mul_nonneg (hz g n) (hz g m)) hgm
    · exact Finset.sum_nonneg (fun g _ => mul_nonneg (hz g n) (hz g m))
  have hrows : (∑ n ∈ S,∑ m ∈ S,∑ g ∈ G,z g n*z g m) =
      ∑ g ∈ G,(∑ n ∈ S,z g n)^2 := by
    calc
      _ = ∑ n ∈ S,∑ g ∈ G,∑ m ∈ S,z g n*z g m := by
        apply Finset.sum_congr rfl
        intro n _
        rw [Finset.sum_comm]
      _ = ∑ g ∈ G,∑ n ∈ S,∑ m ∈ S,z g n*z g m := Finset.sum_comm
      _ = _ := by simp only [pow_two,Finset.sum_mul_sum]
  have htail : (∑ g ∈ G,(g.divisors.card : ℝ)^2/(g : ℝ)^2) ≤
      exp (-(99/409600 : ℝ)*N)*divisorSquareDirichletMass (101/100) := by
    have ht g (hg : g ∈ G) :
        (g.divisors.card : ℝ)^2/(g : ℝ)^2 ≤
          exp (-(99/409600 : ℝ)*N)*((g.divisors.card : ℝ)^2*(g : ℝ)^(-(101/100 : ℝ))) := by
      have hp : (0 : ℝ)<g := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hg).1).1
      have hl := (Finset.mem_filter.mp hg).2
      have hi : (g : ℝ)⁻¹=exp (-log g) := by rw [exp_neg,exp_log hp]
      have he : (g : ℝ)⁻¹^2 ≤ exp (-(99/409600 : ℝ)*N)*(g : ℝ)^(-(101/100 : ℝ)) := by
        rw [hi,← exp_nat_mul,rpow_def_of_pos hp,← exp_add]
        apply exp_le_exp.mpr
        norm_num only [Nat.cast_ofNat]
        nlinarith only [hl]
      simpa only [div_eq_mul_inv,inv_pow,mul_assoc,mul_left_comm,mul_comm] using
        mul_le_mul_of_nonneg_left he (sq_nonneg (g.divisors.card : ℝ))
    calc
      _ ≤ ∑ g ∈ G,exp (-(99/409600 : ℝ)*N)*
          ((g.divisors.card : ℝ)^2*(g : ℝ)^(-(101/100 : ℝ))) := Finset.sum_le_sum ht
      _ = exp (-(99/409600 : ℝ)*N)*∑ g ∈ G,
          (g.divisors.card : ℝ)^2*(g : ℝ)^(-(101/100 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((summable_card_divisors_sq_mul_rpow_neg (by norm_num : (1 : ℝ)<101/100)).sum_le_tsum
          G (fun _ _ => by positivity)) (exp_pos _).le
  let C := exp (log X/262144)*divisorSquareDirichletMass (1+1/262144)
  have hC : 0 ≤ C := by dsimp [C]; positivity [divisorSquareDirichletMass_nonneg (1+1/262144)]
  calc
    _ ≤ ∑ n ∈ S,∑ m ∈ S,∑ g ∈ G,z g n*z g m :=
      Finset.sum_le_sum (fun n hn => Finset.sum_le_sum (hpair n hn))
    _ = ∑ g ∈ G,(∑ n ∈ S,z g n)^2 := hrows
    _ ≤ ∑ g ∈ G,((g.divisors.card : ℝ)/(g : ℝ)*C)^2 := by
      apply Finset.sum_le_sum
      intro g hg
      exact pow_le_pow_left₀ (Finset.sum_nonneg (fun n _ => hz g n))
        (common_factor_row_bound hX (Finset.mem_Icc.mp (Finset.mem_filter.mp hg).1).1 S hS hSF) 2
    _ = C^2*(∑ g ∈ G,(g.divisors.card : ℝ)^2/(g : ℝ)^2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_left htail (sq_nonneg C)

/-- The SAME signed cross energy on large shared labels is bounded
only after its common-factor counting has yielded a geometric saving.
All original phase/allocation/funding weights stay inside the left side. -/
theorem maskedSharedEnergy_bound (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (M : ℕ → ℕ → Prop)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X) (hSF : ∀ n ∈ S,Squarefree n)
    {V : ℝ} (hV : 0 ≤ V) (hw : ∀ n ∈ S,|w n| ≤ V/(n : ℝ)) :
    |maskedSharedEnergy X N S w f M| ≤
      (1+log X)*V^2*(exp (log X/262144)*
        divisorSquareDirichletMass (1+1/262144))^2*
          (exp (-(99/409600 : ℝ)*N)*divisorSquareDirichletMass (101/100)) := by
  let P := ∑ n ∈ S,∑ m ∈ S,
    if (N : ℝ)/4096 < log (Nat.gcd n m) ∧ M n m then
      ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0
  have hP : 0 ≤ P := Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity))
  have hs n (hn : n ∈ S) k :
      |w n*sharp k n| ≤ V*((n.divisors.card : ℝ)/(n : ℝ)) := by
    rw [abs_mul]
    exact (mul_le_mul (hw n hn)
      (abs_sharp_le (Finset.mem_Icc.mp (hS hn)).1 k) (abs_nonneg _)
        (div_nonneg hV (Nat.cast_nonneg n))).trans_eq (by ring)
  have hterm n (hn : n ∈ S) m (hm : m ∈ S) k :
      |if (N : ℝ)/4096 < log (Nat.gcd n m) ∧ M n m then
        (w n*sharp k n)*(w m*sharp k m) else 0| ≤
          V^2*(if (N : ℝ)/4096 < log (Nat.gcd n m) ∧ M n m then
            ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) := by
    split_ifs
    · rw [abs_mul]
      exact (mul_le_mul (hs n hn k) (hs m hm k) (abs_nonneg _)
        (by positivity)).trans_eq (by ring)
    · simp
  have hrow k : |∑ n ∈ S,∑ m ∈ S.erase n,
      if (N : ℝ)/4096 < log (Nat.gcd n m) ∧ M n m then
        (w n*sharp k n)*(w m*sharp k m) else 0| ≤ V^2*P := by
    calc
      _ ≤ ∑ n ∈ S,|∑ m ∈ S.erase n,
          if (N : ℝ)/4096 < log (Nat.gcd n m) ∧ M n m then
            (w n*sharp k n)*(w m*sharp k m) else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ S,∑ m ∈ S.erase n,
          |if (N : ℝ)/4096 < log (Nat.gcd n m) ∧ M n m then
            (w n*sharp k n)*(w m*sharp k m) else 0| :=
        Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ n ∈ S,∑ m ∈ S.erase n,
          V^2*(if (N : ℝ)/4096 < log (Nat.gcd n m) ∧ M n m then
            ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) :=
        Finset.sum_le_sum (fun n hn => Finset.sum_le_sum
          (fun m hm => hterm n hn m (Finset.mem_of_mem_erase hm) k))
      _ ≤ ∑ n ∈ S,∑ m ∈ S,
          V^2*(if (N : ℝ)/4096 < log (Nat.gcd n m) ∧ M n m then
            ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) :=
        Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset _ _) (fun _ _ _ => by split_ifs <;> positivity))
      _ = _ := by simp only [P,Finset.mul_sum]
  let K := ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f
  have hK : K ⊆ Finset.Icc 1 X := by
    intro k hk
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).1
  have hh : (∑ k ∈ K,(k : ℝ)⁻¹) ≤ 1+log X :=
    (Finset.sum_le_sum_of_subset_of_nonneg hK (fun _ _ _ => by positivity)).trans
      (by simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
        using harmonic_le_one_add_log X)
  have hmass : P ≤ (exp (log X/262144)*divisorSquareDirichletMass (1+1/262144))^2*
      (exp (-(99/409600 : ℝ)*N)*divisorSquareDirichletMass (101/100)) :=
    by
      apply le_trans ?_ (large_common_factor_mass X N S hX hS hSF)
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      by_cases hg : (N : ℝ)/4096 < log (Nat.gcd n m)
      · by_cases hM : M n m <;> simp only [hg,hM,and_true,and_false,if_true,if_false]
        · exact le_rfl
        · positivity
      · simp only [hg,false_and,if_false,le_refl]

  have hlog : 0 ≤ 1+log X := by
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
    linarith [log_nonneg hX1]
  calc
    _ ≤ ∑ k ∈ K,|∑ n ∈ S,∑ m ∈ S.erase n,
        if (N : ℝ)/4096 < log (Nat.gcd n m) ∧ M n m then
          (w n*sharp k n)*(w m*sharp k m) else 0|/(k : ℝ) := by
      have ha (k : ℕ) : |(k : ℝ)|=(k : ℝ) := abs_of_nonneg (Nat.cast_nonneg k)
      simpa only [maskedSharedEnergy,abs_div,ha] using
        Finset.abs_sum_le_sum_abs (s := K)
          (fun k : ℕ => (∑ n ∈ S,∑ m ∈ S.erase n,
            if (N : ℝ)/4096 < log (Nat.gcd n m) ∧ M n m then
              (w n*sharp k n)*(w m*sharp k m) else 0)/(k : ℝ))
    _ ≤ ∑ k ∈ K,(V^2*P)/(k : ℝ) := Finset.sum_le_sum
      (fun k _ => div_le_div_of_nonneg_right (hrow k) (Nat.cast_nonneg k))
    _ = (∑ k ∈ K,(k : ℝ)⁻¹)*(V^2*P) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ (1+log X)*(V^2*P) := mul_le_mul_of_nonneg_right hh (mul_nonneg (sq_nonneg V) hP)
    _ ≤ (1+log X)*V^2*((exp (log X/262144)*divisorSquareDirichletMass (1+1/262144))^2*
        (exp (-(99/409600 : ℝ)*N)*divisorSquareDirichletMass (101/100))) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hmass (mul_nonneg hlog (sq_nonneg V))
    _ = _ := by ring

/-- Fixed finite constants from genuine convergent divisor masses.
They are not evaluated numerically or used as a finite-start certificate. -/
def sharedConstant (B : ℝ) : ℝ :=
  16*radiusCeiling^2*B^2*divisorSquareDirichletMass (1+1/262144)^2*
    divisorSquareDirichletMass (101/100)*exp (6/262144)

/-- Source-scale price of ALL large-shared-factor cross correlations.
This is a paid error, not a price on the remaining signed cross sum. -/
def sharedPrice (B : ℝ) (N : ℕ) : ℝ :=
  sqrt (4*sharedConstant B)*((N : ℝ)+1)^2*exp (-(1/131072 : ℝ)*N)

private theorem sharedConstant_nonneg (B : ℝ) : 0 ≤ sharedConstant B := by
  unfold sharedConstant
  positivity [divisorSquareDirichletMass_nonneg (101/100)]

/-- The ACTUAL shared-factor gap dominates both source growth and
the fixed Dirichlet-exponent loss at the current outer radius. -/
theorem shared_source_rate {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (N : ℕ) :
    (2*u)^(2*(N+1))*exp ((6/262144-99/409600 : ℝ)*N) ≤
      4*radiusCeiling^2*exp (-(1/65536 : ℝ)*N) := by
  have hlog := ZetaRieszManyBinRateAudit.radius_growth_bounds.2
  have hr : 0 < 2*radiusCeiling := by norm_num [radiusCeiling]
  have he : (2*radiusCeiling)^(2*(N+1)) =
      4*radiusCeiling^2*exp (2*(N : ℝ)*log (2*radiusCeiling)) := by
    rw [show 2*(N+1)=2*N+2 by omega,pow_add,pow_two]
    have hpow : (2*radiusCeiling)^(2*N)=
        exp (((2*N : ℕ) : ℝ)*log (2*radiusCeiling)) := by rw [exp_nat_mul,exp_log hr]
    rw [hpow]
    push_cast
    ring
  calc
    _ ≤ (2*radiusCeiling)^(2*(N+1))*exp ((6/262144-99/409600 : ℝ)*N) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity : 0 ≤ 2*u) (by linarith : 2*u≤2*radiusCeiling) _)
        (exp_pos _).le
    _ = 4*radiusCeiling^2*exp
        ((2*log (2*radiusCeiling)+6/262144-99/409600)*(N : ℝ)) := by
      rw [he,mul_assoc,← exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by
      nlinarith only [hlog,Nat.cast_nonneg (α := ℝ) N])) (by positivity)

/-- Uniform geometric payment of the original source-weighted large-gcd
cross aggregate. Squarefreeness and all literal masks remain in S; the
actual phase, factorial allocation and signed funding remain in q,w. -/
theorem weighted_maskedShared_bound (X N : ℕ) (A S : Finset ℕ) (f q : ℕ → ℝ) (M : ℕ → ℕ → Prop) (y : ℝ)
    {B L u : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X) (hSF : ∀ n ∈ S,Squarefree n)
    (hlog : log X ≤ 3*((N : ℝ)+1)) (hq : ∀ n ∈ S,|q n| ≤ B) :
    |maskedSharedEnergy X N S (fun n => u^(N+1)*q n*primeWeight A L y N n 1) f M| ≤
      sharedConstant B*((N : ℝ)+1)^3*exp (-(1/65536 : ℝ)*N) := by
  let V := u^(N+1)*B*radialCap N
  have hV : 0 ≤ V := by dsimp [V]; positivity [radialCap_nonneg N]
  have hw n (hn : n ∈ S) :
      |u^(N+1)*q n*primeWeight A L y N n 1| ≤ V/(n : ℝ) := by
    rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg hu (N+1))]
    have h := mul_le_mul
      (mul_le_mul_of_nonneg_left (hq n hn) (pow_nonneg hu (N+1)))
      (primeWeight_total_le A N y hL (Finset.mem_Icc.mp (hS hn)).1)
      (abs_nonneg _) (by positivity)
    exact h.trans_eq (by dsimp [V]; ring)
  have hb := maskedSharedEnergy_bound X N S _ f M hX hS hSF hV hw
  have hh : 1+log X ≤ 4*((N : ℝ)+1) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have he : exp (2*(log X/262144)) ≤
      exp (6/262144)*exp ((6/262144 : ℝ)*N) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    linarith only [hlog]
  have hprod := mul_le_mul hh he (exp_pos _).le (show 0 ≤ 4*((N : ℝ)+1) by positivity)
  have hvpow : V^2=B^2*((N : ℝ)+1)^2*(2*u)^(2*(N+1)) := by
    dsimp [V,radialCap]
    rw [show 2*(N+1)=(N+1)*2 by omega,pow_mul]
    simp only [mul_pow]
    ring
  have hQ : 0 ≤ V^2*divisorSquareDirichletMass (1+1/262144)^2*
      exp (-(99/409600 : ℝ)*N)*divisorSquareDirichletMass (101/100) := by
    positivity [divisorSquareDirichletMass_nonneg (101/100)]
  have hc := mul_le_mul_of_nonneg_right hprod hQ
  have hg := mul_le_mul_of_nonneg_left (shared_source_rate hu hU N)
    (show 0 ≤ 4*B^2*((N : ℝ)+1)^3*divisorSquareDirichletMass (1+1/262144)^2*
      divisorSquareDirichletMass (101/100)*exp (6/262144) by
        positivity [divisorSquareDirichletMass_nonneg (101/100)])
  calc
    _ ≤ (1+log X)*V^2*(exp (log X/262144)*
        divisorSquareDirichletMass (1+1/262144))^2*
          (exp (-(99/409600 : ℝ)*N)*divisorSquareDirichletMass (101/100)) := hb
    _ = ((1+log X)*exp (2*(log X/262144)))*
        (V^2*divisorSquareDirichletMass (1+1/262144)^2*
          exp (-(99/409600 : ℝ)*N)*divisorSquareDirichletMass (101/100)) := by
      rw [mul_pow (exp (log X/262144)) (divisorSquareDirichletMass (1+1/262144)) 2,
        ← exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      ring
    _ ≤ (4*((N : ℝ)+1)*(exp (6/262144)*exp ((6/262144 : ℝ)*N)))*
        (V^2*divisorSquareDirichletMass (1+1/262144)^2*
          exp (-(99/409600 : ℝ)*N)*divisorSquareDirichletMass (101/100)) := hc
    _ = (4*B^2*((N : ℝ)+1)^3*divisorSquareDirichletMass (1+1/262144)^2*
        divisorSquareDirichletMass (101/100)*exp (6/262144))*
          ((2*u)^(2*(N+1))*exp ((6/262144-99/409600 : ℝ)*N)) := by
      rw [hvpow]
      have ht : exp ((6/262144 : ℝ)*N)*exp (-(99/409600 : ℝ)*N)=
          exp ((6/262144-99/409600 : ℝ)*N) := by rw [← exp_add]; congr 1; ring
      rw [← ht]
      ring
    _ ≤ _ := hg.trans_eq (by unfold sharedConstant; ring)


/-- Join the original adverse cutoff Gram before partitioning pairs.
The pair mask is independent of the cutoff, but can retain all label
geometry and phase conditions. -/
theorem maskedSharedEnergy_eq_gram (X N : ℕ) (S : Finset ℕ)
    (w f : ℕ → ℝ) (M : ℕ → ℕ → Prop) :
    maskedSharedEnergy X N S w f M =
      ∑ n ∈ S,∑ m ∈ S.erase n,
        if (N : ℝ)/4096 < log (Nat.gcd n m) ∧ M n m then
          w n*w m*ZetaRieszAntiphaseCredit.cutoffGram X S w f n m else 0 := by
  unfold maskedSharedEnergy
  simp only [Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  unfold ZetaRieszAntiphaseCredit.cutoffGram
  by_cases h : (N : ℝ)/4096 < log (Nat.gcd n m) ∧ M n m
  · simp only [if_pos h,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  · simp only [if_neg h,zero_div,Finset.sum_const_zero]

/-- Exactly the actual still-unpaid correlations below the tighter
shared-factor threshold. ALL other original pair signs remain. -/
def remainingEnergy (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ n ∈ S,∑ m ∈ S.erase n,
    if ZetaRieszAntiphaseCredit.retainedPair N y n m ∧
        ¬(N : ℝ)/4096 < log (Nat.gcd n m) then
      w n*w m*ZetaRieszAntiphaseCredit.cutoffGram X S w f n m else 0

/-- The additional paid family lies between the old and new thresholds,
and is disjoint from the previously paid common-factor/near/phase families. -/
theorem paidPair_band {N n m : ℕ} {y : ℝ}
    (h : (N : ℝ)/4096 < log (Nat.gcd n m) ∧
      ZetaRieszAntiphaseCredit.retainedPair N y n m) :
    (N : ℝ)/4096 < log (Nat.gcd n m) ∧
      log (Nat.gcd n m) ≤ (N : ℝ)/1000 :=
  ⟨h.1,le_of_not_gt h.2.1⟩

/-- Exact partition of the CURRENT whole signed energy, using the same
original adverse set. No positive-part, reserve or new mask is spent twice. -/
theorem nonOrbitEnergy_eq (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (y : ℝ) :
    ZetaRieszPhaseOrbitPayment.nonOrbitEnergy X N S w f y =
      maskedSharedEnergy X N S w f (ZetaRieszAntiphaseCredit.retainedPair N y)+
        remainingEnergy X N S w f y := by
  rw [ZetaRieszAntiphaseCredit.nonOrbitEnergy_eq_gram,maskedSharedEnergy_eq_gram]
  simp only [remainingEnergy,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  by_cases hp : ZetaRieszAntiphaseCredit.retainedPair N y n m
  · by_cases hg : (N : ℝ)/4096 < log (Nat.gcd n m) <;> simp [hp,hg]
  · simp [hp]

/-- Only the independent geometric pair payment is priced. The entire
smaller-gcd signed main term remains inside the SAME whole energy. -/
theorem cost_split (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (y : ℝ)
    {P : ℝ} (hP : 0 ≤ P) :
    sqrt (max (ZetaRieszPhaseOrbitPayment.nonOrbitEnergy X N S w f y) 0*P) ≤
      sqrt (max (remainingEnergy X N S w f y) 0*P)+
        sqrt (|maskedSharedEnergy X N S w f
          (ZetaRieszAntiphaseCredit.retainedPair N y)| * P) := by
  let E := maskedSharedEnergy X N S w f (ZetaRieszAntiphaseCredit.retainedPair N y)
  let H := remainingEnergy X N S w f y
  have hm : max (ZetaRieszPhaseOrbitPayment.nonOrbitEnergy X N S w f y) 0 ≤
      max H 0+|E| := by
    apply max_le
    · rw [nonOrbitEnergy_eq X N S w f y]
      linarith only [le_max_left H 0,le_abs_self E]
    · exact add_nonneg (le_max_right _ _) (abs_nonneg _)
  have hb := mul_le_mul_of_nonneg_right hm hP
  have hA : 0 ≤ max H 0*P := mul_nonneg (le_max_right _ _) hP
  have hB : 0 ≤ |E| * P := mul_nonneg (abs_nonneg _) hP
  have hC : 0 ≤ max (ZetaRieszPhaseOrbitPayment.nonOrbitEnergy X N S w f y) 0*P :=
    mul_nonneg (le_max_right _ _) hP
  apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
  rw [sq_sqrt hC]
  nlinarith only [hb,sq_sqrt hA,sq_sqrt hB,
    mul_nonneg (sqrt_nonneg (max H 0*P)) (sqrt_nonneg (|E| * P))]

/-- Source-normalized geometric price for an arbitrary actual pair mask.
No mask removal, density assumption or independent phase approximation enters. -/
theorem weighted_maskedShared_price (X N : ℕ) (A S : Finset ℕ) (f q : ℕ → ℝ)
    (M : ℕ → ℕ → Prop) (y : ℝ)
    {B L u P : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X) (hSF : ∀ n ∈ S,Squarefree n)
    (hlog : log X ≤ 3*((N : ℝ)+1)) (hq : ∀ n ∈ S,|q n| ≤ B)
    (hP : 0 ≤ P) (hPcap : P ≤ 4*((N : ℝ)+1)) :
    sqrt (|maskedSharedEnergy X N S
      (fun n => u^(N+1)*q n*primeWeight A L y N n 1) f M| * P) ≤ sharedPrice B N := by
  have he := weighted_maskedShared_bound X N A S f q M y hB hL hu hU hX hS hSF hlog hq
  have hC := sharedConstant_nonneg B
  have hprod := mul_le_mul he hPcap hP (show 0 ≤
    sharedConstant B*((N : ℝ)+1)^3*exp (-(1/65536 : ℝ)*N) by positivity)
  apply (sq_le_sq₀ (sqrt_nonneg _) (by unfold sharedPrice; positivity)).mp
  rw [sq_sqrt (mul_nonneg (abs_nonneg _) hP)]
  apply hprod.trans_eq
  unfold sharedPrice
  rw [mul_pow,mul_pow,sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC),
    ← exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show exp ((2 : ℝ)*(-(1/131072)*(N : ℝ)))=exp (-(1/65536)*(N : ℝ)) by congr 1; ring]
  ring

/-- The added joint price tends to zero, for every fixed funding envelope. -/
theorem tendsto_sharedPrice (B : ℝ) : Tendsto (sharedPrice B) atTop (𝓝 0) := by
  have ht := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 2
    (exp_pos (-(1/131072 : ℝ))) (exp_lt_one_iff.mpr (by norm_num : -(1/131072 : ℝ) < 0))
  have hh := ht.const_mul (sqrt (4*sharedConstant B))
  simpa only [mul_zero] using hh.congr' (Eventually.of_forall fun N => by
    unfold sharedPrice
    rw [← exp_nat_mul]
    rw [show exp ((N : ℝ)*(-(1/131072)))=exp (-(1/131072)*(N : ℝ)) by congr 1; ring]
    ring)

open ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint ZetaRieszParityPacket

/-- One original joined bridge, four prior pair prices, one actual count
payment and the disjoint newly paid shared-factor band. -/
def joinedError (u y : ℝ) (j : ℕ) : ℝ :=
  ZetaRieszNearCriticalCountPayment.joinedError u y j+sharedPrice 1 (dyadicMomentOrder j)

/-- Every retained source error still tends to zero on the native schedule. -/
theorem tendsto_joinedError {u : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling) (y : ℝ) :
    Tendsto (joinedError u y) atTop (𝓝 0) := by
  change Tendsto (fun j => ZetaRieszNearCriticalCountPayment.joinedError u y j+
    sharedPrice 1 (dyadicMomentOrder j)) atTop (𝓝 0)
  simpa only [Function.comp_def,add_zero] using
    (ZetaRieszNearCriticalCountPayment.tendsto_joinedError hu hU y).add
      ((tendsto_sharedPrice 1).comp tendsto_dyadicMomentOrder)

/-- DIRECT original whole-floor comparison with the additional actual
cross-family removed at geometric source cost. Remaining pairs satisfy
log(gcd)<=N/4096; their joined signed estimate is still OPEN. -/
theorem eventually_joined_floor {u y : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling)
    (hy : 54 ≤ y) :
    ∀ᶠ j : ℕ in atTop,
      let N := dyadicMomentOrder j
      let A := intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
      let X := max 1 (S.sup id)
      let f := correctedProfile X L 1 0
      let w := fun n => u^(N+1)*primeWeight A L y N n 1;
      -sqrt (max (remainingEnergy X N (S.filter Squarefree) w f y) 0*
        ((129/200 : ℝ)*N))-joinedError u y j ≤
          ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
  filter_upwards [ZetaRieszNearCriticalCountPayment.eventually_joined_floor hu hU hy,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (65536 : ℕ))] with j hj hN
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  let X := max 1 (S.sup id)
  let f := correctedProfile X L 1 0
  let w := fun n => u^(N+1)*primeWeight A L y N n 1
  have hSX : S.filter Squarefree ⊆ Finset.Icc 1 X := by
    intro n hn
    obtain ⟨hn,hs⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hs.ne_zero,
      (Finset.le_sup (f := id) hn).trans (le_max_right _ _)⟩
  have hX : 0 < X := by dsimp [X]; omega
  have hlog : log X ≤ 3*((N : ℝ)+1) := by
    have hh := core_sup_log_le u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
      S (Finset.Subset.refl _)
    dsimp [X]
    nlinarith only [hh,Nat.cast_nonneg (α := ℝ) N]
  have hL : 1 ≤ L := by
    have hh := length_ge_rational hN hu hU
    have hn : (65536 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [L]
    linarith only [hh,hn]
  have hsplit := cost_split X N (S.filter Squarefree) w f y
    (by positivity : 0 ≤ (129/200 : ℝ)*N)
  have hpay := weighted_maskedShared_price X N A (S.filter Squarefree) f (fun _ => 1)
    (ZetaRieszAntiphaseCredit.retainedPair N y) y (by norm_num : (0 : ℝ) ≤ 1)
    hL hu.le hU hX hSX (fun n hn => (Finset.mem_filter.mp hn).2) hlog
    (by norm_num) (by positivity : 0 ≤ (129/200 : ℝ)*N)
    (by nlinarith [Nat.cast_nonneg (α := ℝ) N] : (129/200 : ℝ)*N ≤ 4*((N : ℝ)+1))
  simp only [mul_one] at hpay
  dsimp only at hj hsplit hpay ⊢
  unfold joinedError
  linarith only [hj,hsplit,hpay]

end RiemannGaussian.ZetaRieszSmallGcdPayment
