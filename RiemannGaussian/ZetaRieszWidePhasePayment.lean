/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSmallGcdPayment

/-!
# A wider geometric payment across all original phase periods

The sparse reciprocal-neighbour estimate pays log-phase width
exp(-N/4500)/(1+|y|), rather than the old exp(-N/1000)/(1+|y|).
Source growth and the divisor-mass loss are included in the exponent.
The bound is valid for an arbitrary additional pair mask, not inferred
from a norm bound on some larger cancelling signed sum.

Partition the CURRENT small-gcd signed energy at its SAME adverse cutoffs.
Every count, owner, phase, radial and allocation weight stays unchanged.
The phase-separated remainder still needs its independent numerical bound;
neither its mass nor the fraction of the floor deficit removed is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszWidePhasePayment
open ZetaRieszCofactorPhaseEnergy ZetaRieszPhaseOrbitPayment
open ZetaRieszJointPrimeEnergy ZetaRieszDiagonalPayment
open ZetaRieszSmoothOwnerDiscrepancy ZetaRieszJointAllocation
open ZetaRieszWideOwnerAudit ZetaRieszCutoffPeriodFloor ZetaRieszPostHingeEnergy

/-- A wider neighbourhood of every original total-log phase period. -/
def wideWidth (y : ℝ) (N : ℕ) : ℝ := exp (-(N : ℝ)/4500)/(1+|y|)

/-- The literal union of all phase periods, not independent prime modes. -/
def wideNear (y : ℝ) (N n m : ℕ) : Prop :=
  logNear (phaseOffsets y N) (wideWidth y N) n m

/-- Every previously paid phase pair is still included. -/
theorem oldNear_subset (y : ℝ) (N n m : ℕ)
    (h : logNear (phaseOffsets y N) (phaseWidth y N) n m) : wideNear y N n m := by
  obtain ⟨a,ha,he⟩ := h
  refine ⟨a,ha,he.trans ?_⟩
  unfold phaseWidth wideWidth
  exact div_le_div_of_nonneg_right (exp_le_exp.mpr (by
    nlinarith only [Nat.cast_nonneg (α := ℝ) N])) (by positivity)

private theorem wideWidth_bounds {y : ℝ} (hy : 3 ≤ |y|) (N : ℕ) :
    0 ≤ wideWidth y N ∧ wideWidth y N ≤ 1/4 ∧
      wideWidth y N ≤ exp (-(N : ℝ)/4500) := by
  have hd : 0 < 1+|y| := by positivity
  have he : exp (-(N : ℝ)/4500) ≤ 1 :=
    exp_le_one_iff.mpr (by linarith only [Nat.cast_nonneg (α := ℝ) N])
  unfold wideWidth
  refine ⟨by positivity,?_,?_⟩
  · apply (div_le_iff₀ hd).mpr
    linarith only [he,hy]
  · exact div_le_self (exp_pos _).le (by linarith only [abs_nonneg y])

/-- Sparsity on the original integer labels includes the endpoint error.
There is no prime-density approximation or count-separation assumption. -/
theorem wide_pair_mass_bound (X N : ℕ) (S : Finset ℕ) {y : ℝ}
    (hy : 3 ≤ |y|) (hX : S ⊆ Finset.Icc 1 X) (hS : S ⊆ literalWindow N) :
    (∑ n ∈ S,∑ m ∈ S,if wideNear y N n m then
      ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) ≤
      5*phaseCount y*((N : ℝ)+1)*exp (-(N : ℝ)/4500)*
        exp (log X/262144)*divisorSquareDirichletMass (1+1/262144) := by
  have hl n (hn : n ∈ S) : exp ((7/4 : ℝ)*N) ≤ (n : ℝ) := by
    have hp : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp (hX hn)).1
    have hh := ((mem_literalWindow N n).mp (hS hn)).1
    exact (exp_le_exp.mpr hh.le).trans_eq (exp_log hp)
  obtain ⟨he0,he,hew⟩ := wideWidth_bounds hy N
  have hb := logNear_pair_mass_bound X S (phaseOffsets y N) hX
    (phaseOffsets_symm y N) he0 he hl
  have hi : exp (-((7/4 : ℝ)*N)) ≤ exp (-(N : ℝ)/4500) :=
    exp_le_exp.mpr (by nlinarith only [Nat.cast_nonneg (α := ℝ) N])
  have hh : 4*wideWidth y N+exp (-((7/4 : ℝ)*N)) ≤
      5*exp (-(N : ℝ)/4500) := by linarith only [hew,hi]
  have hprod := mul_le_mul (phaseOffsets_card_le y N) hh (by positivity)
    (show 0 ≤ phaseCount y*((N : ℝ)+1) by unfold phaseCount; positivity)
  exact hb.trans ((mul_le_mul_of_nonneg_right hprod
    (by positivity [divisorSquareDirichletMass_nonneg (1+1/262144)])).trans_eq (by ring))

/-- Restrict the SAME joined divisor Gram by an arbitrary literal mask.
The adverse cutoffs are selected on S,w,f once, before this partition. -/
def maskedOrbitEnergy (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    (y : ℝ) (M : ℕ → ℕ → Prop) : ℝ :=
  ∑ n ∈ S,∑ m ∈ S.erase n,
    if wideNear y N n m ∧ M n m then
      w n*w m*ZetaRieszAntiphaseCredit.cutoffGram X S w f n m else 0

/-- A norm bound only on the sparse family, valid even with arbitrary
signed correlated weights and an asymmetric additional pair mask. -/
theorem maskedOrbitEnergy_bound (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    (M : ℕ → ℕ → Prop) {y : ℝ} (hy : 3 ≤ |y|) (hwin : S ⊆ literalWindow N)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X)
    {V : ℝ} (hV : 0 ≤ V) (hw : ∀ n ∈ S,|w n| ≤ V/(n : ℝ)) :
    |maskedOrbitEnergy X N S w f y M| ≤
      (1+log X)*V^2*(5*phaseCount y*((N : ℝ)+1)*exp (-(N : ℝ)/4500)*
        exp (log X/262144)*divisorSquareDirichletMass (1+1/262144)) := by
  have hlog : 0 ≤ 1+log X := by
    have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
    linarith only [log_nonneg hx]
  have hterm n (hn : n ∈ S) m (hm : m ∈ S) :
      |if wideNear y N n m ∧ M n m then
        w n*w m*ZetaRieszAntiphaseCredit.cutoffGram X S w f n m else 0| ≤
      (1+log X)*V^2*(if wideNear y N n m then
        ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) := by
    by_cases h : wideNear y N n m ∧ M n m
    · simp only [if_pos h,if_pos h.1,abs_mul]
      have hb := mul_le_mul
        (mul_le_mul (hw n hn) (hw m hm) (abs_nonneg _) (by positivity))
        (ZetaRieszAntiphaseCredit.cutoffGram_bound X S w f
          (Finset.mem_Icc.mp (hS hn)).1 (Finset.mem_Icc.mp (hS hm)).1)
        (abs_nonneg _) (by positivity)
      exact hb.trans_eq (by ring)
    · rw [if_neg h,abs_zero]
      split_ifs <;> positivity
  let P := ∑ n ∈ S,∑ m ∈ S,if wideNear y N n m then
    ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0
  calc
    _ ≤ ∑ n ∈ S,∑ m ∈ S.erase n,
        |if wideNear y N n m ∧ M n m then
          w n*w m*ZetaRieszAntiphaseCredit.cutoffGram X S w f n m else 0| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum
        (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ n ∈ S,∑ m ∈ S.erase n,(1+log X)*V^2*(if wideNear y N n m then
        ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) :=
      Finset.sum_le_sum (fun n hn => Finset.sum_le_sum
        (fun m hm => hterm n hn m (Finset.mem_of_mem_erase hm)))
    _ ≤ ∑ n ∈ S,∑ m ∈ S,(1+log X)*V^2*(if wideNear y N n m then
        ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) :=
      Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset _ _) (fun _ _ _ => by split_ifs <;> positivity))
    _ = (1+log X)*V^2*P := by simp only [P,Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (wide_pair_mass_bound X N S hy hS hwin)
      (mul_nonneg hlog (sq_nonneg V))

/-- The actual wider-band rate still beats the source growth and divisor
loss at the UNCHANGED radius. This is an exact rational-margin proof. -/
theorem wide_source_rate {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (N : ℕ) :
    (2*u)^(2*(N+1))*exp ((3/262144-1/4500 : ℝ)*N) ≤
      4*radiusCeiling^2*exp (-(1/100000 : ℝ)*N) := by
  have hlog := ZetaRieszManyBinRateAudit.radius_growth_bounds.2
  have hr : 0 < 2*radiusCeiling := by norm_num [radiusCeiling]
  have he : (2*radiusCeiling)^(2*(N+1)) =
      4*radiusCeiling^2*exp (2*(N : ℝ)*log (2*radiusCeiling)) := by
    rw [show 2*(N+1)=2*N+2 by omega,pow_add,pow_two]
    have hp : (2*radiusCeiling)^(2*N)=
        exp (((2*N : ℕ) : ℝ)*log (2*radiusCeiling)) := by rw [exp_nat_mul,exp_log hr]
    rw [hp]
    push_cast
    ring
  calc
    _ ≤ (2*radiusCeiling)^(2*(N+1))*exp ((3/262144-1/4500 : ℝ)*N) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity : 0 ≤ 2*u) (by linarith : 2*u ≤ 2*radiusCeiling) _)
        (exp_pos _).le
    _ = 4*radiusCeiling^2*exp
        ((2*log (2*radiusCeiling)+3/262144-1/4500)*(N : ℝ)) := by
      rw [he,mul_assoc,← exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by
      nlinarith only [hlog,Nat.cast_nonneg (α := ℝ) N])) (by positivity)

/-- Genuine finite constants; no effective start or numerical value is
asserted for the convergent divisor mass or the fixed-height factor. -/
def wideConstant (B y : ℝ) : ℝ :=
  80*radiusCeiling^2*B^2*phaseCount y*
    divisorSquareDirichletMass (1+1/262144)*exp (3/262144)

/-- Price only the newly sparse correlations, keeping the rest signed. -/
def widePrice (B y : ℝ) (N : ℕ) : ℝ :=
  sqrt (4*wideConstant B y)*((N : ℝ)+1)^3*exp (-(1/200000 : ℝ)*N)

private theorem wideConstant_nonneg (B y : ℝ) : 0 ≤ wideConstant B y := by
  unfold wideConstant phaseCount
  positivity [divisorSquareDirichletMass_nonneg (1+1/262144)]

/-- Uniform geometric payment for the ACTUAL source-normalized weights,
retaining every allocation and phase and every original support mask. -/
theorem weighted_maskedOrbit_bound (X N : ℕ) (A S : Finset ℕ) (f q : ℕ → ℝ)
    (M : ℕ → ℕ → Prop) (y : ℝ) (hy : 3 ≤ |y|) (hwin : S ⊆ literalWindow N)
    {B L u : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X)
    (hlog : log X ≤ 3*((N : ℝ)+1)) (hq : ∀ n ∈ S,|q n| ≤ B) :
    |maskedOrbitEnergy X N S (fun n => u^(N+1)*q n*primeWeight A L y N n 1) f y M| ≤
      wideConstant B y*((N : ℝ)+1)^4*exp (-(1/100000 : ℝ)*N) := by
  let V := u^(N+1)*B*radialCap N
  have hV : 0 ≤ V := by dsimp [V]; positivity [radialCap_nonneg N]
  have hw n (hn : n ∈ S) :
      |u^(N+1)*q n*primeWeight A L y N n 1| ≤ V/(n : ℝ) := by
    rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg hu (N+1))]
    have hh := mul_le_mul
      (mul_le_mul_of_nonneg_left (hq n hn) (pow_nonneg hu (N+1)))
      (primeWeight_total_le A N y hL (Finset.mem_Icc.mp (hS hn)).1)
      (abs_nonneg _) (by positivity)
    exact hh.trans_eq (by dsimp [V]; ring)
  have hb := maskedOrbitEnergy_bound X N S _ f M hy hwin hX hS hV hw
  have hh : 1+log X ≤ 4*((N : ℝ)+1) := by linarith only [hlog,Nat.cast_nonneg (α := ℝ) N]
  have he : exp (log X/262144) ≤ exp (3/262144)*exp ((3/262144 : ℝ)*N) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    linarith only [hlog]
  have hprod := mul_le_mul hh he (exp_pos _).le (show 0 ≤ 4*((N : ℝ)+1) by positivity)
  have hvpow : V^2=B^2*((N : ℝ)+1)^2*(2*u)^(2*(N+1)) := by
    dsimp [V,radialCap]
    rw [show 2*(N+1)=(N+1)*2 by omega,pow_mul]
    simp only [mul_pow]
    ring
  have hQ : 0 ≤ V^2*(5*phaseCount y*((N : ℝ)+1)*exp (-(N : ℝ)/4500))*
      divisorSquareDirichletMass (1+1/262144) := by
    positivity [divisorSquareDirichletMass_nonneg (1+1/262144),
      show 0 ≤ phaseCount y by unfold phaseCount; positivity]
  have hc := mul_le_mul_of_nonneg_right hprod hQ
  have hg := mul_le_mul_of_nonneg_left (wide_source_rate hu hU N)
    (show 0 ≤ 20*B^2*phaseCount y*((N : ℝ)+1)^4*
      divisorSquareDirichletMass (1+1/262144)*exp (3/262144) by
      positivity [divisorSquareDirichletMass_nonneg (1+1/262144),
        show 0 ≤ phaseCount y by unfold phaseCount; positivity])
  calc
    _ ≤ (1+log X)*V^2*(5*phaseCount y*((N : ℝ)+1)*exp (-(N : ℝ)/4500)*
        exp (log X/262144)*divisorSquareDirichletMass (1+1/262144)) := hb
    _ = ((1+log X)*exp (log X/262144))*
        (V^2*(5*phaseCount y*((N : ℝ)+1)*exp (-(N : ℝ)/4500))*
          divisorSquareDirichletMass (1+1/262144)) := by ring
    _ ≤ (4*((N : ℝ)+1)*(exp (3/262144)*exp ((3/262144 : ℝ)*N)))*
        (V^2*(5*phaseCount y*((N : ℝ)+1)*exp (-(N : ℝ)/4500))*
          divisorSquareDirichletMass (1+1/262144)) := hc
    _ = (20*B^2*phaseCount y*((N : ℝ)+1)^4*
          divisorSquareDirichletMass (1+1/262144)*exp (3/262144))*
        ((2*u)^(2*(N+1))*exp ((3/262144-1/4500 : ℝ)*N)) := by
      rw [hvpow]
      have ht : exp ((3/262144 : ℝ)*N)*exp (-(N : ℝ)/4500)=
          exp ((3/262144-1/4500 : ℝ)*N) := by rw [← exp_add]; congr 1; ring
      rw [← ht]
      ring
    _ ≤ _ := hg.trans_eq (by unfold wideConstant; ring)

/-- The wider band is paid for arbitrary masks, including the exact
current small-gcd complement. No monotonicity of signed energy is used. -/
theorem weighted_maskedOrbit_price (X N : ℕ) (A S : Finset ℕ) (f q : ℕ → ℝ)
    (M : ℕ → ℕ → Prop) (y : ℝ) (hy : 3 ≤ |y|) (hwin : S ⊆ literalWindow N)
    {B L u P : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X)
    (hlog : log X ≤ 3*((N : ℝ)+1)) (hq : ∀ n ∈ S,|q n| ≤ B)
    (hP : 0 ≤ P) (hPcap : P ≤ 4*((N : ℝ)+1)) :
    sqrt (|maskedOrbitEnergy X N S
      (fun n => u^(N+1)*q n*primeWeight A L y N n 1) f y M| * P) ≤ widePrice B y N := by
  have he := weighted_maskedOrbit_bound X N A S f q M y hy hwin hB hL hu hU hX hS hlog hq
  have hC := wideConstant_nonneg B y
  have hprod := mul_le_mul he hPcap hP (show 0 ≤
    wideConstant B y*((N : ℝ)+1)^4*exp (-(1/100000 : ℝ)*N) by positivity)
  have hp : ((N : ℝ)+1)^5 ≤ ((N : ℝ)+1)^6 := by
    apply pow_le_pow_right₀ (by linarith only [Nat.cast_nonneg (α := ℝ) N])
    norm_num
  have hpoly := mul_le_mul_of_nonneg_left hp (show 0 ≤
    4*wideConstant B y*exp (-(1/100000 : ℝ)*N) by positivity)
  apply (sq_le_sq₀ (sqrt_nonneg _) (by unfold widePrice; positivity)).mp
  rw [sq_sqrt (mul_nonneg (abs_nonneg _) hP)]
  apply hprod.trans
  calc
    _ = 4*wideConstant B y*exp (-(1/100000 : ℝ)*N)*((N : ℝ)+1)^5 := by ring
    _ ≤ 4*wideConstant B y*exp (-(1/100000 : ℝ)*N)*((N : ℝ)+1)^6 := hpoly
    _ = (widePrice B y N)^2 := by
      unfold widePrice
      rw [mul_pow,mul_pow,sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC),
        ← exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show exp ((2 : ℝ)*(-(1/200000)*(N : ℝ)))=
        exp (-(1/100000)*(N : ℝ)) by congr 1; ring]
      ring

/-- Every new price vanishes for each fixed height and weight envelope. -/
theorem tendsto_widePrice (B y : ℝ) : Tendsto (widePrice B y) atTop (𝓝 0) := by
  have ht := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 3
    (exp_pos (-(1/200000 : ℝ))) (exp_lt_one_iff.mpr (by norm_num : -(1/200000 : ℝ) < 0))
  have hh := ht.const_mul (sqrt (4*wideConstant B y))
  simpa only [mul_zero] using hh.congr' (Eventually.of_forall fun N => by
    unfold widePrice
    rw [← exp_nat_mul]
    rw [show exp ((N : ℝ)*(-(1/200000)))=exp (-(1/200000)*(N : ℝ)) by congr 1; ring]
    ring)

/-- Exactly the previously unpaid pair mask, before the new split. -/
def remainingPair (N : ℕ) (y : ℝ) (n m : ℕ) : Prop :=
  ZetaRieszAntiphaseCredit.retainedPair N y n m ∧
    ¬(N : ℝ)/4096 < log (Nat.gcd n m)

/-- All other original pair signs, at the ORIGINAL adverse cutoffs. -/
def wideRemainingEnergy (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ n ∈ S,∑ m ∈ S.erase n,
    if remainingPair N y n m ∧ ¬wideNear y N n m then
      w n*w m*ZetaRieszAntiphaseCredit.cutoffGram X S w f n m else 0

/-- The new payment is a disjoint subset of the old unpaid family.
No old phase, common-factor, near-label or diagonal payment is spent twice. -/
theorem paidPair_outside_old {N n m : ℕ} {y : ℝ}
    (h : wideNear y N n m ∧ remainingPair N y n m) :
    log (Nat.gcd n m) ≤ (N : ℝ)/4096 ∧
      ¬logNear (phaseOffsets y N) (phaseWidth y N) n m :=
  ⟨le_of_not_gt h.2.2,h.2.1.2.2⟩

/-- An EXACT partition of the current signed aggregate, with neither
side reselecting cutoffs or independently clipping counts or labels. -/
theorem remainingEnergy_eq (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (y : ℝ) :
    ZetaRieszSmallGcdPayment.remainingEnergy X N S w f y =
      maskedOrbitEnergy X N S w f y (remainingPair N y)+
        wideRemainingEnergy X N S w f y := by
  simp only [ZetaRieszSmallGcdPayment.remainingEnergy,maskedOrbitEnergy,
    wideRemainingEnergy,remainingPair,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  by_cases hp : ZetaRieszAntiphaseCredit.retainedPair N y n m
  · by_cases hg : (N : ℝ)/4096 < log (Nat.gcd n m)
    · simp only [hp,hg,not_true_eq_false,and_false,false_and,if_false,zero_add]
    · by_cases hw : wideNear y N n m <;>
        simp only [hp,hg,hw,not_false_eq_true,not_true_eq_false,and_true,
          and_false,if_true,if_false,zero_add,add_zero]
  · simp only [hp,false_and,and_false,if_false,zero_add]

/-- Price only the norm-paid difference. No energy monotonicity or
positive lower bound on a favorable reserve is assumed. -/
theorem cost_split (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (y : ℝ)
    {P : ℝ} (hP : 0 ≤ P) :
    sqrt (max (ZetaRieszSmallGcdPayment.remainingEnergy X N S w f y) 0*P) ≤
      sqrt (max (wideRemainingEnergy X N S w f y) 0*P)+
        sqrt (|maskedOrbitEnergy X N S w f y (remainingPair N y)| * P) := by
  let E := maskedOrbitEnergy X N S w f y (remainingPair N y)
  let H := wideRemainingEnergy X N S w f y
  have hm : max (ZetaRieszSmallGcdPayment.remainingEnergy X N S w f y) 0 ≤ max H 0+|E| := by
    apply max_le
    · rw [remainingEnergy_eq X N S w f y]
      linarith only [le_max_left H 0,le_abs_self E]
    · exact add_nonneg (le_max_right _ _) (abs_nonneg _)
  have hb := mul_le_mul_of_nonneg_right hm hP
  have hA : 0 ≤ max H 0*P := mul_nonneg (le_max_right _ _) hP
  have hB : 0 ≤ |E| * P := mul_nonneg (abs_nonneg _) hP
  have hC : 0 ≤ max (ZetaRieszSmallGcdPayment.remainingEnergy X N S w f y) 0*P :=
    mul_nonneg (le_max_right _ _) hP
  apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
  rw [sq_sqrt hC]
  nlinarith only [hb,sq_sqrt hA,sq_sqrt hB,
    mul_nonneg (sqrt_nonneg (max H 0*P)) (sqrt_nonneg (|E| * P))]

open ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint ZetaRieszParityPacket

/-- All old errors ONCE, plus the new disjoint sparse-family price. -/
def joinedError (u y : ℝ) (j : ℕ) : ℝ :=
  ZetaRieszSmallGcdPayment.joinedError u y j+widePrice 1 y (dyadicMomentOrder j)

/-- The complete source error still vanishes on the unchanged schedule. -/
theorem tendsto_joinedError {u : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling) (y : ℝ) :
    Tendsto (joinedError u y) atTop (𝓝 0) := by
  change Tendsto (fun j => ZetaRieszSmallGcdPayment.joinedError u y j+
    widePrice 1 y (dyadicMomentOrder j)) atTop (𝓝 0)
  simpa only [Function.comp_def,add_zero] using
    (ZetaRieszSmallGcdPayment.tendsto_joinedError hu hU y).add
      ((tendsto_widePrice 1 y).comp tendsto_dyadicMomentOrder)

/-- DIRECT whole-floor comparison after the new payment. The same native
core/count crop and actual phase/allocation weights remain. The new
phase-separated signed energy still needs the numerical floor budget. -/
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
      -sqrt (max (wideRemainingEnergy X N (S.filter Squarefree) w f y) 0*
        ((129/200 : ℝ)*N))-joinedError u y j ≤
          ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
  filter_upwards [ZetaRieszSmallGcdPayment.eventually_joined_floor hu hU hy,
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
  have hwin : S.filter Squarefree ⊆ literalWindow N :=
    (Finset.filter_subset _ _).trans (ZetaRieszDirectPhaseFloor.core_subset_window u N _)
  have hyabs : 3 ≤ |y| := by linarith only [hy,le_abs_self y]
  have hsplit := cost_split X N (S.filter Squarefree) w f y
    (by positivity : 0 ≤ (129/200 : ℝ)*N)
  have hpay := weighted_maskedOrbit_price X N A (S.filter Squarefree) f (fun _ => 1)
    (remainingPair N y) y hyabs hwin (by norm_num : (0 : ℝ) ≤ 1) hL hu.le hU hX hSX
    hlog (by norm_num) (by positivity : 0 ≤ (129/200 : ℝ)*N)
    (by nlinarith [Nat.cast_nonneg (α := ℝ) N] : (129/200 : ℝ)*N ≤ 4*((N : ℝ)+1))
  simp only [mul_one] at hpay
  dsimp only at hj hsplit hpay ⊢
  unfold joinedError
  linarith only [hj,hsplit,hpay]

end RiemannGaussian.ZetaRieszWidePhasePayment
