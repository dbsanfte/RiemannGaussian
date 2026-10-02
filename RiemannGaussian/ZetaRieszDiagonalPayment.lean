/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszManyBinRateAudit
import RiemannGaussian.ZetaRieszSmoothOwnerDiscrepancy
import RiemannGaussian.ZetaRieszOwnerPairFloor

/-!
# Pay the actual whole-floor energy diagonal

The source-normalized diagonal of the EXISTING weighted sharp-prefix
energy decays geometrically across every count, bin and phase. Original
allocation and signed funding coefficients remain in its weight. This is
not a diagonalization: the actual off-diagonal sum remains signed and
unpaid. In particular, an exponential discount relative to a positive L1
envelope is not the necessary target for the actual diagonal.

The finite one-sided inequality at the end separates the paid diagonal
price from the whole signed cross term. No many-bin orthogonality or
arithmetic cancellation premise is inferred.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszDiagonalPayment
open ZetaRieszCofactorPhaseEnergy ZetaRieszJointPrimeEnergy
open ZetaRieszJointAllocation ZetaRieszSmoothOwnerDiscrepancy
open ZetaRieszWideOwnerAudit ZetaRieszCutoffPeriodFloor

/-- The diagonal of the same actual prefix energy, without discarding
any cutoff, count, allocation, phase or signed funding weight. -/
def diagonalEnergy (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ activeCutoffs X f, (∑ n ∈ S,(w n*sharp k n)^2)/(k : ℝ)

/-- Every ordered off-diagonal term of that SAME energy. No absolute
value is taken on individual labels, counts, bins or periods. -/
def crossEnergy (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ activeCutoffs X f, (∑ n ∈ S,∑ m ∈ S.erase n,
    (w n*sharp k n)*(w m*sharp k m))/(k : ℝ)

/-- For the floor only adverse COMPLETE funded prefix increments enter.
Every signed off-diagonal term is joined before this cutoff selection. -/
def adverseCrossEnergy (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f,
    (∑ n ∈ S,∑ m ∈ S.erase n,(w n*sharp k n)*(w m*sharp k m))/(k : ℝ)

/-- The unchanged profile energy on those same adverse whole increments.
Favorable complete cutoffs do not have to be norm-paid for a floor. -/
def adverseProfileEnergy (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f,
    (k : ℝ)*(f k-f (k+1))^2

/-- Exact scope of the diagonal payment: the cross term is still part
of the original energy and can reinforce as well as cancel. -/
theorem phaseEnergy_eq (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) :
    phaseEnergy X S w f = diagonalEnergy X S w f+crossEnergy X S w f :=
  ZetaRieszManyBinRateAudit.phaseEnergy_eq_diagonal_cross X S w f

/-- The sharp Möbius prefix has at most the actual divisor multiplicity.
This bound is used ONLY on the diagonal, not on the signed cross term. -/
theorem abs_sharp_le {n : ℕ} (hn : 0 < n) (k : ℕ) :
    |sharp k n| ≤ (n.divisors.card : ℝ) := by
  have he : (Finset.Icc 1 k).filter (fun d => d ∣ n) =
      n.divisors.filter (fun d => d ≤ k) := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_,hd⟩,hdn⟩
      exact ⟨⟨hdn,hn.ne'⟩,hd⟩
    · rintro ⟨⟨hdn,_⟩,hd⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdn hn,hd⟩,hdn⟩
  rw [sharp,← Finset.sum_filter,he]
  calc
    _ ≤ ∑ d ∈ n.divisors.filter (fun d => d ≤ k),|(μ d : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ n.divisors.filter (fun d => d ≤ k),(1 : ℝ) :=
      Finset.sum_le_sum (fun d _ => by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d))
    _ ≤ ∑ d ∈ n.divisors,(1 : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => zero_le_one)
    _ = _ := by simp

/-- The full original allocation and phase stay inside the weight.
Only its diagonal envelope uses the radial cap. -/
theorem primeWeight_total_le (A : Finset ℕ) (N : ℕ) (y : ℝ)
    {L : ℝ} (hL : 1 ≤ L) {n : ℕ} (hn : 0 < n) :
    |primeWeight A L y N n 1| ≤ radialCap N/(n : ℝ) := by
  have hL0 : 0 < L := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := radial_bounds N (log_natCast_nonneg n)
  have ha : |1-boundedShare A N n| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (boundedShare_bounds A N n).2)]
    linarith [(boundedShare_bounds A N n).1]
  have hc : |1-boundedShare A N n| *|cos (y*log n)| ≤ 1 :=
    (mul_le_mul ha (abs_cos_le_one _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have he : primeWeight A L y N n 1 =
      -(1-boundedShare A N n)*radial N (log n)/L/(n : ℝ)*cos (y*log n) := by
    simp only [primeWeight,one_mul,Nat.cast_one,log_one,zero_add,mul_one,radial]
    ring
  rw [he,abs_mul,abs_div,abs_div,abs_mul,abs_neg,
    abs_of_pos hL0,abs_of_pos hn0,abs_of_nonneg hr.1]
  calc
    _ = (|1-boundedShare A N n| *|cos (y*log n)|)*
        (radial N (log n)/L/(n : ℝ)) := by ring
    _ ≤ radial N (log n)/L/(n : ℝ) :=
      mul_le_of_le_one_left (div_nonneg (div_nonneg hr.1 hL0.le) hn0.le) hc
    _ ≤ radialCap N/(n : ℝ) :=
      div_le_div_of_nonneg_right ((div_le_self hr.1 hL).trans hr.2) hn0.le

private theorem reciprocal_square_tail {n : ℕ} (hn : 0 < n)
    {N : ℕ} (hlog : (7/4 : ℝ)*N < log n) :
    (n : ℝ)⁻¹^2 ≤ exp (-(7/8 : ℝ)*N)*(n : ℝ)^(-(3/2 : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hi : (n : ℝ)⁻¹=exp (-log n) := by rw [exp_neg,exp_log hn0]
  rw [hi,← exp_nat_mul,rpow_def_of_pos hn0,← exp_add]
  apply exp_le_exp.mpr
  nlinarith only [hlog]

/-- A fixed summable divisor-square mass pays all diagonal labels in
the actual radial window. No count/bin restriction is needed. -/
theorem diagonalEnergy_le (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    {V : ℝ} (hV : 0 ≤ V) (hS : S ⊆ literalWindow N)
    (hw : ∀ n ∈ S,|w n| ≤ V/(n : ℝ)) :
    diagonalEnergy X S w f ≤
      (1+log X)*V^2*exp (-(7/8 : ℝ)*N)*divisorSquareDirichletMass (3/2) := by
  have hs n (hn : n ∈ S) : 0 < n := by
    have h := (mem_literalWindow N n).mp (hS hn)
    by_contra hz
    have hn0 : n=0 := by omega
    subst n
    norm_num at h
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hterm n (hn : n ∈ S) k :
      (w n*sharp k n)^2 ≤ V^2*exp (-(7/8 : ℝ)*N)*
        ((n.divisors.card : ℝ)^2*(n : ℝ)^(-(3/2 : ℝ))) := by
    have ht := mul_le_mul (hw n hn) (abs_sharp_le (hs n hn) k)
      (abs_nonneg _) (div_nonneg hV (Nat.cast_nonneg n))
    have ht2 := pow_le_pow_left₀ (abs_nonneg (w n*sharp k n))
      (by simpa only [abs_mul] using ht) 2
    simp only [sq_abs,mul_pow,div_eq_mul_inv,inv_pow] at ht2
    have hb := mul_le_mul_of_nonneg_left
      (reciprocal_square_tail (hs n hn) ((mem_literalWindow N n).mp (hS hn)).1)
      (show 0 ≤ V^2*(n.divisors.card : ℝ)^2 by positivity)
    rw [mul_pow]
    apply ht2.trans
    simpa only [inv_pow,mul_assoc,mul_left_comm,mul_comm] using hb
  have hrow k :
      (∑ n ∈ S,(w n*sharp k n)^2) ≤
        V^2*exp (-(7/8 : ℝ)*N)*divisorSquareDirichletMass (3/2) := by
    calc
      _ ≤ ∑ n ∈ S,V^2*exp (-(7/8 : ℝ)*N)*
          ((n.divisors.card : ℝ)^2*(n : ℝ)^(-(3/2 : ℝ))) :=
        Finset.sum_le_sum (fun n hn => hterm n hn k)
      _ = (V^2*exp (-(7/8 : ℝ)*N))*
          ∑ n ∈ S,(n.divisors.card : ℝ)^2*(n : ℝ)^(-(3/2 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((summable_card_divisors_sq_mul_rpow_neg (by norm_num : (1 : ℝ)<3/2)).sum_le_tsum
          S (fun _ _ => by positivity)) (by positivity)
  have hh : (∑ k ∈ activeCutoffs X f,(k : ℝ)⁻¹) ≤ 1+log X :=
    (Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk => (Finset.mem_filter.mp hk).1) (fun _ _ _ => by positivity)).trans
      (by simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
        using harmonic_le_one_add_log X)
  calc
    _ ≤ ∑ k ∈ activeCutoffs X f,
        (V^2*exp (-(7/8 : ℝ)*N)*divisorSquareDirichletMass (3/2))/(k : ℝ) :=
      Finset.sum_le_sum (fun k _ => div_le_div_of_nonneg_right (hrow k) (Nat.cast_nonneg k))
    _ = (∑ k ∈ activeCutoffs X f,(k : ℝ)⁻¹)*
        (V^2*exp (-(7/8 : ℝ)*N)*divisorSquareDirichletMass (3/2)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ _ := (mul_le_mul_of_nonneg_right hh (by
      positivity [divisorSquareDirichletMass_nonneg (3/2)])).trans_eq (by ring)

/-- At the actual outer radius the radial diagonal has a strict fixed
geometric gap, despite 2u>1 in the positive L1 envelope. -/
theorem diagonal_source_rate {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (N : ℕ) :
    (2*u)^(2*(N+1))*exp (-(7/8 : ℝ)*N) ≤
      4*radiusCeiling^2*exp (-(3/4 : ℝ)*N) := by
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
    _ ≤ (2*radiusCeiling)^(2*(N+1))*exp (-(7/8 : ℝ)*N) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity : 0 ≤ 2*u) (by linarith : 2*u≤2*radiusCeiling) _)
        (exp_pos _).le
    _ = 4*radiusCeiling^2*exp ((2*log (2*radiusCeiling)-7/8)*(N : ℝ)) := by
      rw [he,mul_assoc,← exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by
      nlinarith only [hlog,Nat.cast_nonneg (α := ℝ) N])) (by positivity)

/-- The actual source-normalized energy diagonal is geometrically paid,
with every original signed funding coefficient bounded by the same B. -/
theorem weighted_diagonal_bound (X N : ℕ) (A S : Finset ℕ) (f q : ℕ → ℝ) (y : ℝ)
    {B L u : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hS : S ⊆ literalWindow N) (hX : log X ≤ 3*((N : ℝ)+1))
    (hq : ∀ n ∈ S,|q n| ≤ B) :
    diagonalEnergy X S (fun n => u^(N+1)*q n*primeWeight A L y N n 1) f ≤
      16*radiusCeiling^2*B^2*divisorSquareDirichletMass (3/2)*
        ((N : ℝ)+1)^3*exp (-(3/4 : ℝ)*N) := by
  let V := u^(N+1)*B*radialCap N
  have hV : 0 ≤ V := by dsimp [V]; positivity [radialCap_nonneg N]
  have hw n (hn : n ∈ S) :
      |u^(N+1)*q n*primeWeight A L y N n 1| ≤ V/(n : ℝ) := by
    have hn0 : 0 < n := by
      by_contra h
      have hn0 : n=0 := by omega
      have hh := (mem_literalWindow N n).mp (hS hn)
      simp only [hn0,Nat.cast_zero,log_zero] at hh
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg hu (N+1))]
    have h := mul_le_mul
      (mul_le_mul_of_nonneg_left (hq n hn) (pow_nonneg hu (N+1)))
      (primeWeight_total_le A N y hL hn0) (abs_nonneg _) (by positivity)
    exact h.trans_eq (by dsimp [V]; ring)
  have hd := diagonalEnergy_le X N S _ f hV hS hw
  have hh : 1+log X ≤ 4*((N : ℝ)+1) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hr := mul_le_mul_of_nonneg_left (diagonal_source_rate hu hU N)
    (show 0 ≤ 4*B^2*divisorSquareDirichletMass (3/2)*((N : ℝ)+1)^3 by
      positivity [divisorSquareDirichletMass_nonneg (3/2)])
  have hc := mul_le_mul_of_nonneg_right hh (show 0 ≤
    V^2*exp (-(7/8 : ℝ)*N)*divisorSquareDirichletMass (3/2) by
      positivity [divisorSquareDirichletMass_nonneg (3/2)])
  have hc' : (1+log X)*V^2*exp (-(7/8 : ℝ)*N)*divisorSquareDirichletMass (3/2) ≤
      4*((N : ℝ)+1)*V^2*exp (-(7/8 : ℝ)*N)*divisorSquareDirichletMass (3/2) := by
    simpa only [mul_assoc] using hc
  rw [show 2*(N+1)=(N+1)*2 by omega,pow_mul,mul_pow] at hr
  apply hd.trans (hc'.trans _)
  dsimp [V,radialCap]
  convert hr using 1 <;> ring

private theorem hinge_add_log (L x : ℝ) : max 0 (L-x)+x=max L x := by
  by_cases hx : x ≤ L
  · rw [max_eq_right (sub_nonneg.mpr hx),max_eq_left hx]
    ring
  · rw [max_eq_left (by linarith : L-x ≤ 0),max_eq_right (le_of_not_ge hx)]
    ring

private theorem log_step_le {k : ℕ} (hk : 0 < k) :
    log (k+1 : ℕ)-log k ≤ (k : ℝ)⁻¹ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hb := log_le_sub_one_of_pos (show 0 < ((k : ℝ)+1)/k by positivity)
  rw [log_div (by positivity : (k : ℝ)+1 ≠ 0) hk0.ne'] at hb
  have he : ((k : ℝ)+1)/k-1=(k : ℝ)⁻¹ := by field_simp; ring
  rw [he] at hb
  simpa only [Nat.cast_add,Nat.cast_one] using hb

/-- The unit logarithmic null correction makes the profile increasing
with a step no larger than the actual logarithmic increment. Its finite
last endpoint is zero exactly, not a variation boundary allowance. -/
theorem corrected_profile_step_le {X k : ℕ} (hk : k ∈ Finset.Icc 1 X) (L : ℝ) :
    |correctedProfile X L 1 0 k-correctedProfile X L 1 0 (k+1)| ≤ (k : ℝ)⁻¹ := by
  obtain ⟨hk0,hkX⟩ := Finset.mem_Icc.mp hk
  by_cases he : k=X
  · subst k
    simp [correctedProfile,ZetaRieszCenteredPrimeEnergy.centeredProfile]
  · have hk' : k+1 ≤ X := by omega
    have hl : log k ≤ log (k+1 : ℕ) := log_le_log
      (by exact_mod_cast hk0 : (0 : ℝ)<k) (by exact_mod_cast Nat.le_succ k)
    have hdiff : correctedProfile X L 1 0 k-correctedProfile X L 1 0 (k+1)=
        max L (log k)-max L (log (k+1 : ℕ)) := by
      simp only [correctedProfile,ZetaRieszCenteredPrimeEnergy.centeredProfile,
        if_pos hkX,if_pos hk',zero_mul,add_zero,one_mul]
      linarith only [hinge_add_log L (log k),hinge_add_log L (log (k+1 : ℕ))]
    have hm : max L (log k) ≤ max L (log (k+1 : ℕ)) := max_le_max_left L hl
    have hgap : max L (log (k+1 : ℕ))-max L (log k) ≤ log (k+1 : ℕ)-log k := by
      have h : max L (log (k+1 : ℕ)) ≤ max L (log k)+(log (k+1 : ℕ)-log k) := by
        apply max_le
        · linarith [le_max_left L (log k)]
        · linarith [le_max_right L (log k)]
      linarith
    rw [hdiff,abs_of_nonpos (sub_nonpos.mpr hm)]
    exact (by linarith only [hgap] :
      -(max L (log k)-max L (log (k+1 : ℕ))) ≤ log (k+1 : ℕ)-log k).trans
        (log_step_le (by omega : 0 < k))

/-- The retained post-hinge profile costs at most the literal harmonic
mass. This is polynomial in the moment order on the existing window. -/
theorem corrected_profileEnergy_le (X : ℕ) (L : ℝ) :
    profileEnergy X (correctedProfile X L 1 0) ≤ 1+log X := by
  rw [profileEnergy_eq]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 X,(k : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have h := pow_le_pow_left₀ (abs_nonneg _)
        (corrected_profile_step_le hk L) 2
      rw [sq_abs] at h
      apply (mul_le_mul_of_nonneg_left h hk0.le).trans_eq
      field_simp
    _ ≤ _ := by
      simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
        using harmonic_le_one_add_log X

/-- A polynomial times a fixed geometric rate, paying the diagonal
contribution to the whole signed energy price. The mass is a genuine
convergent arithmetic constant; its numerical value is not assumed. -/
def diagonalPrice (B : ℝ) (N : ℕ) : ℝ :=
  8*radiusCeiling*B*sqrt (divisorSquareDirichletMass (3/2))*
    ((N : ℝ)+1)^2*exp (-(3/8 : ℝ)*N)

/-- The actual diagonal Cauchy price, including the full profile, is
source-o(1). Every signed mask and all prime counts remain in its weight. -/
theorem weighted_diagonal_price (X N : ℕ) (A S : Finset ℕ) (q : ℕ → ℝ) (y : ℝ)
    {B L u : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hS : S ⊆ literalWindow N) (hX : log X ≤ 3*((N : ℝ)+1))
    (hq : ∀ n ∈ S,|q n| ≤ B) :
    sqrt (diagonalEnergy X S (fun n => u^(N+1)*q n*primeWeight A L y N n 1)
        (correctedProfile X L 1 0)*profileEnergy X (correctedProfile X L 1 0)) ≤
      diagonalPrice B N := by
  have hM := divisorSquareDirichletMass_nonneg (3/2)
  have hrad : 0 ≤ radiusCeiling := by norm_num [radiusCeiling]
  have hD : 0 ≤ diagonalEnergy X S (fun n => u^(N+1)*q n*primeWeight A L y N n 1)
      (correctedProfile X L 1 0) :=
    Finset.sum_nonneg (fun _ _ => div_nonneg
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _))
  have hP : 0 ≤ profileEnergy X (correctedProfile X L 1 0) :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hp : profileEnergy X (correctedProfile X L 1 0) ≤ 4*((N : ℝ)+1) :=
    (corrected_profileEnergy_le X L).trans (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hd := weighted_diagonal_bound X N A S (correctedProfile X L 1 0) q y hB hL hu hU
    hS hX hq
  have hb := mul_le_mul hd hp hP (show 0 ≤
    16*radiusCeiling^2*B^2*divisorSquareDirichletMass (3/2)*
      ((N : ℝ)+1)^3*exp (-(3/4 : ℝ)*N) by positivity)
  apply (sq_le_sq₀ (sqrt_nonneg _) (by unfold diagonalPrice; positivity)).mp
  rw [sq_sqrt (mul_nonneg hD hP)]
  apply hb.trans_eq
  unfold diagonalPrice
  rw [mul_pow,mul_pow,mul_pow,mul_pow,mul_pow,sq_sqrt hM,← exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show exp ((2 : ℝ)*(-(3/8)*(N : ℝ)))=exp (-(3/4)*(N : ℝ)) by congr 1; ring]
  ring

/-- This new payment tends to zero independently of height, count,
occupied-bin pattern and every native supply choice. -/
theorem tendsto_diagonalPrice (B : ℝ) :
    Tendsto (diagonalPrice B) atTop (𝓝 0) := by
  have ht := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 2
    (exp_pos (-(3/8 : ℝ))) (exp_lt_one_iff.mpr (by norm_num : -(3/8 : ℝ) < 0))
  have hh := ht.const_mul (8*radiusCeiling*B*sqrt (divisorSquareDirichletMass (3/2)))
  simpa only [mul_zero] using hh.congr' (Eventually.of_forall fun N => by
    unfold diagonalPrice
    rw [← exp_nat_mul]
    rw [show exp ((N : ℝ)*(-(3/8)))=exp (-(3/8)*(N : ℝ)) by congr 1; ring]
    ring)

private theorem adverse_energy_eq (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) :
    (∑ k ∈ ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f,
      correlation S w k^2/(k : ℝ)) =
        (∑ k ∈ ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f,
          (∑ n ∈ S,(w n*sharp k n)^2)/(k : ℝ))+adverseCrossEnergy X S w f := by
  unfold adverseCrossEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← add_div]
  congr 1
  rw [correlation,pow_two,Finset.sum_mul_sum]
  simp only [← Finset.sum_add_distrib,pow_two]
  apply Finset.sum_congr rfl
  intro n hn
  exact (Finset.sum_erase_add S
    (fun m => (w n*sharp k n)*(w m*sharp k m)) hn).symm.trans (by ring_nf)

/-- Removing only the diagonal never enlarges the original adverse
prefix cost. Together with the geometric diagonal payment, the two
costs differ by at most a source-geometric error. -/
theorem adverse_crossCost_le (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) :
    sqrt (max (adverseCrossEnergy X S w f) 0*adverseProfileEnergy X S w f) ≤
      ZetaRieszRejoinedPhaseFloor.negativeCost X S w f := by
  let K := ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f
  let D := ∑ k ∈ K,(∑ n ∈ S,(w n*sharp k n)^2)/(k : ℝ)
  let E := ∑ k ∈ K,correlation S w k^2/(k : ℝ)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => div_nonneg
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _))
  have hE : 0 ≤ E := Finset.sum_nonneg
    (fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have he : E=D+adverseCrossEnergy X S w f := adverse_energy_eq X S w f
  have hP : 0 ≤ adverseProfileEnergy X S w f := Finset.sum_nonneg
    (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hc : max (adverseCrossEnergy X S w f) 0 ≤ E :=
    max_le (by linarith only [he,hD]) hE
  change sqrt (_*adverseProfileEnergy X S w f) ≤ sqrt (E*adverseProfileEnergy X S w f)
  exact sqrt_le_sqrt (mul_le_mul_of_nonneg_right hc hP)

private theorem adverse_price_split (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) :
    ZetaRieszRejoinedPhaseFloor.negativeCost X S w f ≤
      sqrt (max (adverseCrossEnergy X S w f) 0*adverseProfileEnergy X S w f)+
        sqrt (diagonalEnergy X S w f*profileEnergy X f) := by
  let K := ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f
  let D := ∑ k ∈ K,(∑ n ∈ S,(w n*sharp k n)^2)/(k : ℝ)
  let E := ∑ k ∈ K,correlation S w k^2/(k : ℝ)
  have hK : K ⊆ activeCutoffs X f := Finset.filter_subset _ _
  have he : E=D+adverseCrossEnergy X S w f := adverse_energy_eq X S w f
  have hDle : D ≤ diagonalEnergy X S w f :=
    Finset.sum_le_sum_of_subset_of_nonneg hK (fun _ _ _ =>
      div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _))
  have hP' : 0 ≤ adverseProfileEnergy X S w f :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hPle : adverseProfileEnergy X S w f ≤ profileEnergy X f :=
    Finset.sum_le_sum_of_subset_of_nonneg hK (fun _ _ _ =>
      mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hD : 0 ≤ diagonalEnergy X S w f :=
    Finset.sum_nonneg (fun _ _ => div_nonneg
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _))
  have hP : 0 ≤ profileEnergy X f :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hE : 0 ≤ E :=
    Finset.sum_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have hEP := mul_nonneg hE hP'
  have hDP := mul_nonneg hD hP
  have hCP := mul_nonneg (le_max_right (adverseCrossEnergy X S w f) 0) hP'
  have hbound : E*adverseProfileEnergy X S w f ≤
      max (adverseCrossEnergy X S w f) 0*adverseProfileEnergy X S w f+
        diagonalEnergy X S w f*profileEnergy X f := by
    have h := mul_le_mul_of_nonneg_right
      (le_max_left (adverseCrossEnergy X S w f) 0) hP'
    have hd := mul_le_mul hDle hPle hP' hD
    rw [he]
    nlinarith only [h,hd]
  change sqrt (E*adverseProfileEnergy X S w f) ≤ _
  apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
  rw [sq_sqrt hEP]
  nlinarith only [hbound,sq_sqrt hDP,sq_sqrt hCP,
    mul_nonneg (sqrt_nonneg (max (adverseCrossEnergy X S w f) 0*adverseProfileEnergy X S w f))
      (sqrt_nonneg (diagonalEnergy X S w f*profileEnergy X f))]

/-- A one-sided bound on the ORIGINAL signed sum. The diagonal is paid
geometrically; the FULL signed off-diagonal aggregate, including every
funding overlap, is the remaining explicit price. No diagonal-relative
orthogonality or bilinear-cancellation assumption is introduced. -/
theorem weighted_cross_floor (N : ℕ) (A S : Finset ℕ) (q : ℕ → ℝ) (y : ℝ)
    {B L u : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hS : S ⊆ literalWindow N) (hq : ∀ n ∈ S,|q n| ≤ B)
    (hc : ∀ n ∈ S,3 ≤ n.primeFactors.card)
    (hX : log (max 1 (S.sup id) : ℕ) ≤ 3*((N : ℝ)+1)) :
    let X := max 1 (S.sup id)
    let f := correctedProfile X L 1 0
    let w := fun n => u^(N+1)*q n*primeWeight A L y N n 1;
    -sqrt (max (adverseCrossEnergy X (S.filter Squarefree) w f) 0*
        adverseProfileEnergy X (S.filter Squarefree) w f)-
        diagonalPrice B N ≤
      u^(N+1)*(∑ n ∈ S,q n*(residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re) := by
  let X := max 1 (S.sup id)
  let f := correctedProfile X L 1 0
  let w := fun n => u^(N+1)*q n*primeWeight A L y N n 1
  have hw := weighted_corrected_eq_prefix A S N L y 1 0 (fun n => u^(N+1)*q n) hc
  dsimp only at hw
  have hb := ZetaRieszRejoinedPhaseFloor.negative_signed_prefix_bound X (S.filter Squarefree) w f
    (by simp [f,correctedProfile,ZetaRieszCenteredPrimeEnergy.centeredProfile])
  have he : (∑ n ∈ S.filter Squarefree,w n*(∑ d ∈ Finset.Icc 1 X,
      f d*(if d ∣ n then (μ d : ℝ) else 0))) =
        u^(N+1)*(∑ n ∈ S,q n*(residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re) := by
    rw [← hw,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [he] at hb
  have hs : S.filter Squarefree ⊆ literalWindow N :=
    (Finset.filter_subset _ _).trans hS
  have hd := weighted_diagonal_price X N A (S.filter Squarefree) q y hB hL hu hU
    hs hX (fun n hn => hq n (Finset.mem_filter.mp hn).1)
  have hp := adverse_price_split X (S.filter Squarefree) w f
  dsimp only [X,f,w] at hb hp hd ⊢
  linarith only [hb,hp,hd]

/-- The existing literal window already bounds the full finite cutoff
endpoint. No separately assumed upper label or completed support enters. -/
theorem window_sup_log (S : Finset ℕ) {N : ℕ} (hS : S ⊆ literalWindow N) :
    log (max 1 (S.sup id) : ℕ) ≤ 3*((N : ℝ)+1) := by
  rcases S.eq_empty_or_nonempty with hs|hs
  · simp only [hs,Finset.sup_empty,bot_eq_zero,max_eq_left (Nat.zero_le 1),Nat.cast_one,log_one]
    positivity
  · obtain ⟨n,hn,he⟩ := Finset.exists_mem_eq_sup S hs id
    have hw := (mem_literalWindow N n).mp (hS hn)
    have hn0 : 1 ≤ n := by
      by_contra h
      have hz : n=0 := by omega
      simp only [hz,Nat.cast_zero,log_zero] at hw
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    rw [he,id_eq,max_eq_right hn0]
    nlinarith [hw.2,Nat.cast_nonneg (α := ℝ) N]

open ZetaRieszRejoinedPhaseFloor

/-- Spend the diagonal price on the SAME full funded ledger. Positive
credits, their actual phases, every supply overlap and the literal debit
are joined before the cross energy. This is a finite signed inequality,
not an assumed estimate on that remaining cross energy. -/
theorem funded_cross_floor (N : ℕ) (A H P T Y : Finset ℕ) (y debit : ℝ)
    {B L u : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hS : ((H ∪ P) ∪ T) ∪ Y ⊆ literalWindow N)
    (hc : ∀ n ∈ ((H ∪ P) ∪ T) ∪ Y,3 ≤ n.primeFactors.card)
    (hq : ∀ a b : ℝ,0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      ∀ n ∈ ((H ∪ P) ∪ T) ∪ Y,|rejoinedWeights H P T Y a b debit n| ≤ B) :
    let atom := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    let S := ((H ∪ P) ∪ T) ∪ Y
    let X := max 1 (S.sup id)
    let f := correctedProfile X L 1 0
    let a : ℝ := if 0 ≤ (∑ n ∈ P,atom n).re then 1 else 0
    let b : ℝ := if 0 ≤ (∑ n ∈ T,atom n).re then 1 else 0
    let w := fun n => u^(N+1)*rejoinedWeights H P T Y a b debit n*primeWeight A L y N n 1;
    -sqrt (max (adverseCrossEnergy X (S.filter Squarefree) w f) 0*
      adverseProfileEnergy X (S.filter Squarefree) w f)-diagonalPrice B N ≤
      u^(N+1)*((∑ n ∈ H,atom n).re+max (∑ n ∈ P,atom n).re 0+
        max (∑ n ∈ T,atom n).re 0-debit*(∑ n ∈ Y,atom n).re) := by
  let atom := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let a : ℝ := if 0 ≤ (∑ n ∈ P,atom n).re then 1 else 0
  let b : ℝ := if 0 ≤ (∑ n ∈ T,atom n).re then 1 else 0
  have ha : a*(∑ n ∈ P,atom n).re=max (∑ n ∈ P,atom n).re 0 := by
    dsimp [a]
    split_ifs with h
    · rw [one_mul,max_eq_left h]
    · rw [zero_mul,max_eq_right (le_of_lt (lt_of_not_ge h))]
  have hb : b*(∑ n ∈ T,atom n).re=max (∑ n ∈ T,atom n).re 0 := by
    dsimp [b]
    split_ifs with h
    · rw [one_mul,max_eq_left h]
    · rw [zero_mul,max_eq_right (le_of_lt (lt_of_not_ge h))]
  have hq' n (hn : n ∈ ((H ∪ P) ∪ T) ∪ Y) :
      |rejoinedWeights H P T Y a b debit n| ≤ B := by
    apply hq a b (by dsimp [a]; split_ifs <;> norm_num)
      (by dsimp [a]; split_ifs <;> norm_num)
      (by dsimp [b]; split_ifs <;> norm_num)
      (by dsimp [b]; split_ifs <;> norm_num) n hn
  have h := weighted_cross_floor N A (((H ∪ P) ∪ T) ∪ Y)
    (rejoinedWeights H P T Y a b debit) y hB hL hu hU hS hq' hc (window_sup_log _ hS)
  dsimp only at h ⊢
  change -_ - _ ≤ u^(N+1)*(∑ n ∈ ((H ∪ P) ∪ T) ∪ Y,
    rejoinedWeights H P T Y a b debit n*(atom n).re) at h
  rw [rejoined_weight_sum H P T Y a b debit (fun n => (atom n).re)] at h
  simpa only [← Complex.re_sum,ha,hb] using h

open ZetaRieszParityPacket ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint
open ZetaRieszRadialCompensation ZetaRieszBandCompensation
open ZetaRieszRejoinedPopulationFloor ZetaRieszJoinedPopulationFloor ZetaRieszFewBinCoverFloor
open ZetaRieszSevenCountTail
open ZetaRieszLowCountRefund (tailCost)

/-- Native whole-floor reduction after paying the diagonal geometrically.
The sole displayed energy price is the actual signed off-diagonal sum
with ALL original funding/count/bin/radial correlations retained. Its
independent numerical bound, and therefore the final floor, remain open. -/
theorem eventually_joined_cross_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ radiusCeiling) (hy : 54 ≤ y) :
    ∃ h c κ : ℝ,0 < h ∧ h ≤ 1/20 ∧ 0 < c ∧ 0 < κ ∧
      ∀ ε : ℝ,0 < ε → ∃ err : ℕ → ℝ,
        (∀ j,0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
        ∀ᶠ j : ℕ in atTop,∃ v : ℕ → ℝ,
          (∀ M ∈ radialIndices (dyadicMomentOrder j),0 ≤ v M ∧ v M ≤ 1/2) ∧
          let N := dyadicMomentOrder j
          let K := dyadicPrimeCount j
          let A := intermediatePrimes u N
          let L := SquarefreeVaughanLogSource.length u N
          let S₀ := coreBand u N K
          let atom := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
          let Paid := (S₀.filter (fun n : ℕ =>
            3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∪ dense56Band u N K) ∪
              bin56Band u N K
          let H := (S₀\(Paid ∪ wholeTail S₀ N 0))\ZetaRieszSharpOwnerPayment.sector u N K
          let Ts := radialTail S₀ N 0
          let Ys := radialSupply N h v
          let S := ((H ∪ Paid) ∪ Ts) ∪ Ys
          let X := max 1 (S.sup id)
          let f := correctedProfile X L 1 0
          let a : ℝ := if 0 ≤ (∑ n ∈ Paid,atom n).re then 1 else 0
          let b : ℝ := if 0 ≤ (∑ n ∈ Ts,atom n).re then 1 else 0
          let debit := tailCost c N+ε+growingDebit κ N
          let w := fun n => u^(N+1)*rejoinedWeights H Paid Ts Ys a b debit n*primeWeight A L y N n 1;
          0 < (∑ n ∈ Ys,atom n).re ∧
            -sqrt (max (adverseCrossEnergy X (S.filter Squarefree) w f) 0*
              adverseProfileEnergy X (S.filter Squarefree) w f)-err j ≤
              ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  obtain ⟨h,c,κ,hh,hhu,hc,hκ,hbase⟩ :=
    ZetaRieszSharpOwnerPayment.eventually_rejoined_floor hu hU hy
  refine ⟨h,c,κ,hh,hhu,hc,hκ,?_⟩
  intro ε hε
  obtain ⟨err,he0,he,hfloor⟩ := hbase ε hε
  have hrad : 0 ≤ radiusCeiling := by norm_num [radiusCeiling]
  have hB : 0 ≤ 4+|ε| := by positivity
  refine ⟨fun j => err j+diagonalPrice (4+|ε|) (dyadicMomentOrder j),?_,?_,?_⟩
  · intro j
    exact add_nonneg (he0 j) (by unfold diagonalPrice; positivity)
  · simpa only [add_zero,Function.comp_def] using
      he.add ((tendsto_diagonalPrice (4+|ε|)).comp tendsto_dyadicMomentOrder)
  have hut : u < exp (-(1/2 : ℝ)) :=
    (hU.trans_lt radius_lt_source).trans (exp_lt_exp.mpr (by norm_num))
  have hlen := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 1/2) hut
  have hsupply := eventually_radial_supply_in_core hu hU hh hhu
  have hweights := ZetaRieszOwnerPairFloor.eventually_rejoined_weights_bound c κ ε
  filter_upwards [hfloor,hsupply,tendsto_dyadicMomentOrder.eventually hlen,
    tendsto_dyadicMomentOrder.eventually hweights,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1000 : ℕ))]
      with j hj hY hL hq hN
  obtain ⟨v,hv,hpos,hbound⟩ := hj
  refine ⟨v,hv,hpos,?_⟩
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S₀ := coreBand u N K
  let Paid := (S₀.filter (fun n : ℕ =>
    3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∪ dense56Band u N K) ∪ bin56Band u N K
  let H := (S₀\(Paid ∪ wholeTail S₀ N 0))\ZetaRieszSharpOwnerPayment.sector u N K
  let Ts := radialTail S₀ N 0
  let Ys := radialSupply N h v
  have hS : ((H ∪ Paid) ∪ Ts) ∪ Ys ⊆ S₀ := by
    intro n hn
    rcases Finset.mem_union.mp hn with hn|hn
    · rcases Finset.mem_union.mp hn with hn|hn
      · rcases Finset.mem_union.mp hn with hn|hn
        · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hn).1).1
        · rcases Finset.mem_union.mp hn with hn|hn
          · rcases Finset.mem_union.mp hn with hn|hn
            · exact (Finset.mem_filter.mp hn).1
            · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
          · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
      · obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
        exact (Finset.mem_filter.mp hn).1
    · obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
      exact hY M hM (v M) (hv M hM).1 (hv M hM).2 hn
  have hL1 : 1 ≤ L := by
    have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [L,N]
    norm_num at hL
    linarith
  have hprice := funded_cross_floor N A H Paid Ts Ys y
    (tailCost c N+ε+growingDebit κ N) hB hL1 (by linarith : 0 ≤ u) hU
    (hS.trans (ZetaRieszNonownerAllocation.coreBand_subset_literalWindow u N K))
    (fun n hn => ZetaRieszJointPrimeEnergy.core_count (hS hn))
    (fun a b ha ha1 hb hb1 n _ => by
      simpa only [Real.norm_eq_abs] using hq H Paid Ts Ys a b ha ha1 hb hb1 n)
  dsimp only [N,K,A,L,S₀,Paid,H,Ts,Ys] at hprice
  dsimp only at hbound ⊢
  nlinarith only [hprice,hbound]

end RiemannGaussian.ZetaRieszDiagonalPayment
