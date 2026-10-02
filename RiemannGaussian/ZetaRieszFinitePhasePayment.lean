/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.NatDivisorSquareHarmonic
import RiemannGaussian.ZetaRieszWidePhasePayment
import RiemannGaussian.ZetaRieszEndgameSlack

/-!
# A finite divisor bound pays wider literal phase correlations

The fourth harmonic divisor bound removes the fixed auxiliary Dirichlet
loss. The original integer phase-period neighbourhood can consequently
be widened to exp(-N/4900)/(1+|y|). All counts, radial periods and actual
adverse cutoffs stay joined. Arbitrary additional masks are allowed.

Only this disjoint difference is norm-paid. The remaining energy keeps
all its signs and still needs an independent numerical upper bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszFinitePhasePayment
open ZetaRieszCofactorPhaseEnergy ZetaRieszPhaseOrbitPayment
open ZetaRieszJointPrimeEnergy ZetaRieszDiagonalPayment
open ZetaRieszSmoothOwnerDiscrepancy ZetaRieszJointAllocation
open ZetaRieszWideOwnerAudit ZetaRieszCutoffPeriodFloor ZetaRieszPostHingeEnergy

/-- A logarithmic pair-capacity bound with an explicit finite divisor factor. -/
theorem logNear_pair_mass_bound (X : ℕ) (S : Finset ℕ) (P : Finset ℝ)
    (hX : S ⊆ Finset.Icc 1 X) (hP : ∀ a ∈ P,-a ∈ P)
    {ε l : ℝ} (hε : 0 ≤ ε) (hεu : ε ≤ 1/4)
    (hS : ∀ n ∈ S,exp l ≤ (n : ℝ)) :
    (∑ n ∈ S,∑ m ∈ S,if logNear P ε n m then
      ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) ≤
      ((P.card : ℝ)*(4*ε+exp (-l)))*(1+log X)^4 := by
  have hpos n (hn : n ∈ S) : 0 < n ∧ exp l ≤ (n : ℝ) :=
    ⟨(Finset.mem_Icc.mp (hX hn)).1,hS n hn⟩
  calc
    _ ≤ ∑ n ∈ S,((n.divisors.card : ℝ)^2/(n : ℝ))*
        (∑ m ∈ S,if logNear P ε n m then (m : ℝ)⁻¹ else 0) :=
      symmetric_reciprocal_capacity S (logNear P ε) (logNear_symm P hP ε)
        (fun n => (n.divisors.card : ℝ))
    _ ≤ ∑ n ∈ S,((n.divisors.card : ℝ)^2/(n : ℝ))*
        ((P.card : ℝ)*(4*ε+exp (-l))) := Finset.sum_le_sum (fun n _ =>
      mul_le_mul_of_nonneg_left (logNear_row_capacity P S n hε hεu hpos) (by positivity))
    _ = ((P.card : ℝ)*(4*ε+exp (-l)))*∑ n ∈ S,(n.divisors.card : ℝ)^2/(n : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_card_divisors_sq_div_le_log_four X S hX) (by positivity)

/-- The wider neighbourhood of every actual total-log phase period. -/
def width (y : ℝ) (N : ℕ) : ℝ := exp (-(N : ℝ)/4900)/(1+|y|)

/-- Genuine integer-label phases; no individual zero mode is norm-paid. -/
def near (y : ℝ) (N n m : ℕ) : Prop :=
  logNear (phaseOffsets y N) (width y N) n m

/-- Every pair paid by the preceding width remains included. -/
theorem wideNear_subset (y : ℝ) (N n m : ℕ)
    (h : ZetaRieszWidePhasePayment.wideNear y N n m) : near y N n m := by
  obtain ⟨a,ha,he⟩ := h
  refine ⟨a,ha,he.trans ?_⟩
  unfold ZetaRieszWidePhasePayment.wideWidth width
  exact div_le_div_of_nonneg_right (exp_le_exp.mpr (by
    nlinarith only [Nat.cast_nonneg (α := ℝ) N])) (by positivity)

private theorem width_bounds {y : ℝ} (hy : 3 ≤ |y|) (N : ℕ) :
    0 ≤ width y N ∧ width y N ≤ 1/4 ∧ width y N ≤ exp (-(N : ℝ)/4900) := by
  have hd : 0 < 1+|y| := by positivity
  have he : exp (-(N : ℝ)/4900) ≤ 1 := exp_le_one_iff.mpr (by
    nlinarith only [Nat.cast_nonneg (α := ℝ) N])
  unfold width
  refine ⟨by positivity,?_,?_⟩
  · apply (div_le_iff₀ hd).mpr
    linarith only [he,hy]
  · exact div_le_self (exp_pos _).le (by linarith only [abs_nonneg y])

/-- All finite labels and every integer endpoint are included in the bound. -/
theorem near_pair_mass_bound (X N : ℕ) (S : Finset ℕ) {y : ℝ}
    (hy : 3 ≤ |y|) (hX : S ⊆ Finset.Icc 1 X) (hS : S ⊆ literalWindow N) :
    (∑ n ∈ S,∑ m ∈ S,if near y N n m then
      ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) ≤
      5*phaseCount y*((N : ℝ)+1)*exp (-(N : ℝ)/4900)*(1+log X)^4 := by
  have hl n (hn : n ∈ S) : exp ((7/4 : ℝ)*N) ≤ (n : ℝ) := by
    have hp : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp (hX hn)).1
    have hh := ((mem_literalWindow N n).mp (hS hn)).1
    exact (exp_le_exp.mpr hh.le).trans_eq (exp_log hp)
  obtain ⟨he0,he,hew⟩ := width_bounds hy N
  have hb := logNear_pair_mass_bound X S (phaseOffsets y N) hX
    (phaseOffsets_symm y N) he0 he hl
  have hi : exp (-((7/4 : ℝ)*N)) ≤ exp (-(N : ℝ)/4900) :=
    exp_le_exp.mpr (by nlinarith only [Nat.cast_nonneg (α := ℝ) N])
  have hh : 4*width y N+exp (-((7/4 : ℝ)*N)) ≤
      5*exp (-(N : ℝ)/4900) := by linarith only [hew,hi]
  have hprod := mul_le_mul (phaseOffsets_card_le y N) hh
    (by positivity : 0 ≤ 4*width y N+exp (-((7/4 : ℝ)*N)))
    (by unfold phaseCount; positivity)
  exact hb.trans ((mul_le_mul_of_nonneg_right hprod (by positivity)).trans_eq (by ring))

/-- The extra mask can select the exact current unpaid family. -/
def maskedEnergy (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    (y : ℝ) (M : ℕ → ℕ → Prop) : ℝ :=
  ∑ n ∈ S,∑ m ∈ S.erase n,
    if near y N n m ∧ M n m then
      w n*w m*ZetaRieszAntiphaseCredit.cutoffGram X S w f n m else 0

/-- A direct arbitrary-mask norm bound; signed-energy monotonicity is not used. -/
theorem maskedEnergy_bound (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    (M : ℕ → ℕ → Prop) {y : ℝ} (hy : 3 ≤ |y|) (hwin : S ⊆ literalWindow N)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X)
    {V : ℝ} (hV : 0 ≤ V) (hw : ∀ n ∈ S,|w n| ≤ V/(n : ℝ)) :
    |maskedEnergy X N S w f y M| ≤
      5*phaseCount y*((N : ℝ)+1)*V^2*exp (-(N : ℝ)/4900)*(1+log X)^5 := by
  have hlog : 0 ≤ 1+log X := by
    have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
    linarith only [log_nonneg hx]
  have hterm n (hn : n ∈ S) m (hm : m ∈ S) :
      |if near y N n m ∧ M n m then
        w n*w m*ZetaRieszAntiphaseCredit.cutoffGram X S w f n m else 0| ≤
      (1+log X)*V^2*(if near y N n m then
        ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) := by
    by_cases h : near y N n m ∧ M n m
    · simp only [if_pos h,if_pos h.1,abs_mul]
      have hb := mul_le_mul
        (mul_le_mul (hw n hn) (hw m hm) (abs_nonneg _) (by positivity))
        (ZetaRieszAntiphaseCredit.cutoffGram_bound X S w f
          (Finset.mem_Icc.mp (hS hn)).1 (Finset.mem_Icc.mp (hS hm)).1)
        (abs_nonneg _) (by positivity)
      exact hb.trans_eq (by ring)
    · rw [if_neg h,abs_zero]
      split_ifs <;> positivity
  let P := ∑ n ∈ S,∑ m ∈ S,if near y N n m then
    ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0
  calc
    _ ≤ ∑ n ∈ S,∑ m ∈ S.erase n,
        |if near y N n m ∧ M n m then
          w n*w m*ZetaRieszAntiphaseCredit.cutoffGram X S w f n m else 0| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum
        (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ n ∈ S,∑ m ∈ S.erase n,(1+log X)*V^2*(if near y N n m then
        ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) :=
      Finset.sum_le_sum (fun n hn => Finset.sum_le_sum
        (fun m hm => hterm n hn m (Finset.mem_of_mem_erase hm)))
    _ ≤ ∑ n ∈ S,∑ m ∈ S,(1+log X)*V^2*(if near y N n m then
        ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) :=
      Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset _ _) (fun _ _ _ => by split_ifs <;> positivity))
    _ = (1+log X)*V^2*P := by simp only [P,Finset.mul_sum]
    _ ≤ (1+log X)*V^2*
        (5*phaseCount y*((N : ℝ)+1)*exp (-(N : ℝ)/4900)*(1+log X)^4) :=
      mul_le_mul_of_nonneg_left (near_pair_mass_bound X N S hy hS hwin)
        (mul_nonneg hlog (sq_nonneg V))
    _ = _ := by ring

/-- A strict rational exponent margin at the unchanged radius ceiling. -/
theorem source_rate {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (N : ℕ) :
    (2*u)^(2*(N+1))*exp (-(N : ℝ)/4900) ≤
      4*radiusCeiling^2*exp (-(1/250000 : ℝ)*N) := by
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
    _ ≤ (2*radiusCeiling)^(2*(N+1))*exp (-(N : ℝ)/4900) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity : 0 ≤ 2*u) (by linarith : 2*u ≤ 2*radiusCeiling) _)
        (exp_pos _).le
    _ = 4*radiusCeiling^2*exp ((2*log (2*radiusCeiling)-1/4900)*(N : ℝ)) := by
      rw [he,mul_assoc,← exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by
      nlinarith only [hlog,Nat.cast_nonneg (α := ℝ) N])) (by positivity)

/-- An explicit finite constant replaces the unevaluated near-critical Dirichlet mass. -/
def energyConstant (B y : ℝ) : ℝ := 20480*radiusCeiling^2*B^2*phaseCount y

/-- The additional sparse-pair floor cost, after profile capacity. -/
def price (B y : ℝ) (N : ℕ) : ℝ :=
  sqrt (4*energyConstant B y)*((N : ℝ)+1)^5*exp (-(1/500000 : ℝ)*N)

private theorem energyConstant_nonneg (B y : ℝ) : 0 ≤ energyConstant B y := by
  unfold energyConstant phaseCount
  positivity

/-- A source-normalized geometric estimate for the original literal weights. -/
theorem weighted_maskedEnergy_bound (X N : ℕ) (A S : Finset ℕ) (f q : ℕ → ℝ)
    (M : ℕ → ℕ → Prop) (y : ℝ) (hy : 3 ≤ |y|) (hwin : S ⊆ literalWindow N)
    {B L u : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X)
    (hlog : log X ≤ 3*((N : ℝ)+1)) (hq : ∀ n ∈ S,|q n| ≤ B) :
    |maskedEnergy X N S (fun n => u^(N+1)*q n*primeWeight A L y N n 1) f y M| ≤
      energyConstant B y*((N : ℝ)+1)^8*exp (-(1/250000 : ℝ)*N) := by
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
  have hb := maskedEnergy_bound X N S _ f M hy hwin hX hS hV hw
  have hx0 : 0 ≤ 1+log X := by
    have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
    linarith only [log_nonneg hx]
  have hh : 1+log X ≤ 4*((N : ℝ)+1) := by linarith only [hlog,Nat.cast_nonneg (α := ℝ) N]
  have hpow := pow_le_pow_left₀ hx0 hh 5
  have hvpow : V^2=B^2*((N : ℝ)+1)^2*(2*u)^(2*(N+1)) := by
    dsimp [V,radialCap]
    rw [show 2*(N+1)=(N+1)*2 by omega,pow_mul]
    simp only [mul_pow]
    ring
  have hC : 0 ≤ 5*phaseCount y*((N : ℝ)+1)*V^2*exp (-(N : ℝ)/4900) := by
    unfold phaseCount
    positivity
  have hp := mul_le_mul_of_nonneg_left hpow hC
  have hg := mul_le_mul_of_nonneg_left (source_rate hu hU N)
    (show 0 ≤ 5120*B^2*phaseCount y*((N : ℝ)+1)^8 by unfold phaseCount; positivity)
  calc
    _ ≤ 5*phaseCount y*((N : ℝ)+1)*V^2*exp (-(N : ℝ)/4900)*(1+log X)^5 := hb
    _ ≤ 5*phaseCount y*((N : ℝ)+1)*V^2*exp (-(N : ℝ)/4900)*(4*((N : ℝ)+1))^5 := hp
    _ = (5120*B^2*phaseCount y*((N : ℝ)+1)^8)*
        ((2*u)^(2*(N+1))*exp (-(N : ℝ)/4900)) := by rw [hvpow]; ring
    _ ≤ _ := hg.trans_eq (by unfold energyConstant; ring)

/-- The same estimate pays only the new difference at the original cutoff capacity. -/
theorem weighted_maskedEnergy_price (X N : ℕ) (A S : Finset ℕ) (f q : ℕ → ℝ)
    (M : ℕ → ℕ → Prop) (y : ℝ) (hy : 3 ≤ |y|) (hwin : S ⊆ literalWindow N)
    {B L u P : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X)
    (hlog : log X ≤ 3*((N : ℝ)+1)) (hq : ∀ n ∈ S,|q n| ≤ B)
    (hP : 0 ≤ P) (hPcap : P ≤ 4*((N : ℝ)+1)) :
    sqrt (|maskedEnergy X N S
      (fun n => u^(N+1)*q n*primeWeight A L y N n 1) f y M| * P) ≤ price B y N := by
  have he := weighted_maskedEnergy_bound X N A S f q M y hy hwin hB hL hu hU hX hS hlog hq
  have hC := energyConstant_nonneg B y
  have hprod := mul_le_mul he hPcap hP (show 0 ≤
    energyConstant B y*((N : ℝ)+1)^8*exp (-(1/250000 : ℝ)*N) by positivity)
  have hp : ((N : ℝ)+1)^9 ≤ ((N : ℝ)+1)^10 := by
    apply pow_le_pow_right₀ (by linarith only [Nat.cast_nonneg (α := ℝ) N])
    norm_num
  have hpoly := mul_le_mul_of_nonneg_left hp (show 0 ≤
    4*energyConstant B y*exp (-(1/250000 : ℝ)*N) by positivity)
  apply (sq_le_sq₀ (sqrt_nonneg _) (by unfold price; positivity)).mp
  rw [sq_sqrt (mul_nonneg (abs_nonneg _) hP)]
  apply hprod.trans
  calc
    _ = 4*energyConstant B y*exp (-(1/250000 : ℝ)*N)*((N : ℝ)+1)^9 := by ring
    _ ≤ 4*energyConstant B y*exp (-(1/250000 : ℝ)*N)*((N : ℝ)+1)^10 := hpoly
    _ = (price B y N)^2 := by
      unfold price
      rw [mul_pow,mul_pow,sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC),
        ← exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show exp ((2 : ℝ)*(-(1/500000)*(N : ℝ)))=
        exp (-(1/250000)*(N : ℝ)) by congr 1; ring]
      ring

/-- The new whole-carrier sparse price tends to zero at every fixed height. -/
theorem tendsto_price (B y : ℝ) : Tendsto (price B y) atTop (𝓝 0) := by
  have ht := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 5
    (exp_pos (-(1/500000 : ℝ))) (exp_lt_one_iff.mpr (by norm_num : -(1/500000 : ℝ) < 0))
  have hh := ht.const_mul (sqrt (4*energyConstant B y))
  simpa only [mul_zero] using hh.congr' (Eventually.of_forall fun N => by
    unfold price
    rw [← exp_nat_mul]
    rw [show exp ((N : ℝ)*(-(1/500000)))=exp (-(1/500000)*(N : ℝ)) by congr 1; ring]
    ring)

/-- The current unpaid pairs, with every preceding payment excluded. -/
def remainingPair (N : ℕ) (y : ℝ) (n m : ℕ) : Prop :=
  ZetaRieszWidePhasePayment.remainingPair N y n m ∧
    ¬ZetaRieszWidePhasePayment.wideNear y N n m

/-- The unpriced remainder retains its exact signed cross-count interactions. -/
def remainingEnergy (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ n ∈ S,∑ m ∈ S.erase n,
    if remainingPair N y n m ∧ ¬near y N n m then
      w n*w m*ZetaRieszAntiphaseCredit.cutoffGram X S w f n m else 0

/-- This is a disjoint additional payment, never a second charge for an old pair. -/
theorem paidPair_outside_old {N n m : ℕ} {y : ℝ}
    (h : near y N n m ∧ remainingPair N y n m) :
    log (Nat.gcd n m) ≤ (N : ℝ)/4096 ∧
      ¬ZetaRieszWidePhasePayment.wideNear y N n m :=
  ⟨le_of_not_gt h.2.1.2,h.2.2⟩

/-- Exact partition using the SAME whole-population adverse cutoff set. -/
theorem remainingEnergy_eq (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (y : ℝ) :
    ZetaRieszWidePhasePayment.wideRemainingEnergy X N S w f y =
      maskedEnergy X N S w f y (remainingPair N y)+remainingEnergy X N S w f y := by
  simp only [ZetaRieszWidePhasePayment.wideRemainingEnergy,maskedEnergy,
    remainingEnergy,remainingPair,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  by_cases hp : ZetaRieszWidePhasePayment.remainingPair N y n m
  · by_cases hw : ZetaRieszWidePhasePayment.wideNear y N n m
    · simp only [hp,hw,not_true_eq_false,and_false,false_and,if_false,zero_add]
    · by_cases hn : near y N n m <;>
        simp only [hp,hw,hn,not_false_eq_true,not_true_eq_false,and_true,
          and_false,if_true,if_false,zero_add,add_zero]
  · simp only [hp,false_and,and_false,if_false,zero_add]

/-- Only the norm-paid difference is charged; no monotonicity of signed energy. -/
theorem cost_split (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (y : ℝ)
    {P : ℝ} (hP : 0 ≤ P) :
    sqrt (max (ZetaRieszWidePhasePayment.wideRemainingEnergy X N S w f y) 0*P) ≤
      sqrt (max (remainingEnergy X N S w f y) 0*P)+
        sqrt (|maskedEnergy X N S w f y (remainingPair N y)| * P) := by
  let E := maskedEnergy X N S w f y (remainingPair N y)
  let H := remainingEnergy X N S w f y
  have hm : max (ZetaRieszWidePhasePayment.wideRemainingEnergy X N S w f y) 0 ≤ max H 0+|E| := by
    apply max_le
    · rw [remainingEnergy_eq X N S w f y]
      linarith only [le_max_left H 0,le_abs_self E]
    · exact add_nonneg (le_max_right _ _) (abs_nonneg _)
  have hb := mul_le_mul_of_nonneg_right hm hP
  have hA : 0 ≤ max H 0*P := mul_nonneg (le_max_right _ _) hP
  have hB : 0 ≤ |E| * P := mul_nonneg (abs_nonneg _) hP
  have hC : 0 ≤ max (ZetaRieszWidePhasePayment.wideRemainingEnergy X N S w f y) 0*P :=
    mul_nonneg (le_max_right _ _) hP
  apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
  rw [sq_sqrt hC]
  nlinarith only [hb,sq_sqrt hA,sq_sqrt hB,
    mul_nonneg (sqrt_nonneg (max H 0*P)) (sqrt_nonneg (|E| * P))]

open ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint ZetaRieszParityPacket

/-- Every earlier source error once, plus this disjoint additional price. -/
def joinedError (u y : ℝ) (j : ℕ) : ℝ :=
  ZetaRieszWidePhasePayment.joinedError u y j+price 1 y (dyadicMomentOrder j)

/-- No new constant source error is introduced. -/
theorem tendsto_joinedError {u : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling) (y : ℝ) :
    Tendsto (joinedError u y) atTop (𝓝 0) := by
  change Tendsto (fun j => ZetaRieszWidePhasePayment.joinedError u y j+
    price 1 y (dyadicMomentOrder j)) atTop (𝓝 0)
  simpa only [Function.comp_def,add_zero] using
    (ZetaRieszWidePhasePayment.tendsto_joinedError hu hU y).add
      ((tendsto_price 1 y).comp tendsto_dyadicMomentOrder)

/-- A direct floor for original joinedPhysical with the new signed energy.
Its numerical budget remains the explicit, unpaid arithmetic target. -/
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
  filter_upwards [ZetaRieszWidePhasePayment.eventually_joined_floor hu hU hy,
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
  have hpay := weighted_maskedEnergy_price X N A (S.filter Squarefree) f (fun _ => 1)
    (remainingPair N y) y hyabs hwin (by norm_num : (0 : ℝ) ≤ 1) hL hu.le hU hX hSX
    hlog (by norm_num) (by positivity : 0 ≤ (129/200 : ℝ)*N)
    (by nlinarith [Nat.cast_nonneg (α := ℝ) N] : (129/200 : ℝ)*N ≤ 4*((N : ℝ)+1))
  simp only [mul_one] at hpay
  dsimp only at hj hsplit hpay ⊢
  unfold joinedError
  linarith only [hj,hsplit,hpay]

/-- The unchanged relaxed budget on the literal NEW signed remainder
would close the simple exposed source. This independent arithmetic
premise is OPEN; the sparse-pair payment does not discharge it. -/
theorem false_of_cofinal_remainingEnergy (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ radiusCeiling) (hy : 54 ≤ rho.1.im)
    (hsimple : analyticZetaZeroMultiplicity rho=1)
    (henergy : ∃ᶠ j : ℕ in atTop,
      let u := 3/2-rho.1.re
      let N := dyadicMomentOrder j
      let A := intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
      let X := max 1 (S.sup id)
      let f := correctedProfile X L 1 0
      let w := fun n => u^(N+1)*primeWeight A L rho.1.im N n 1;
      remainingEnergy X N (S.filter Squarefree) w f rho.1.im ≤
        987/(100000*((N : ℝ)+1))) : False := by
  have hu : 0 < 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  apply ZetaRieszEndgameSlack.false_of_relaxed_floor rho hrho hexposed hU hsimple
    (joinedError (3/2-rho.1.re) rho.1.im) (tendsto_joinedError hu hU rho.1.im)
  have hf := eventually_joined_floor hu hU hy
  exact (henergy.and_eventually hf).mono fun j hj => by
    obtain ⟨he,hf⟩ := hj
    dsimp only at he hf ⊢
    have hc := ZetaRieszEndgameSlack.cost_le_of_relaxed_energy
      (by positivity : 0 ≤ (129/200 : ℝ)*dyadicMomentOrder j)
      (le_refl ((129/200 : ℝ)*dyadicMomentOrder j)) he
    linarith only [hf,hc]

end RiemannGaussian.ZetaRieszFinitePhasePayment
