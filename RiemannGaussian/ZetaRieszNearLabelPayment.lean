/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSharedFactorPayment

/-!
# Geometric payment of nearby actual labels in the joined cross energy

After the existing large-gcd payment, the original signed cross sum is
partitioned by relative integer distance. A symmetric neighbour-count
estimate pays all pairs with |n-m| <= exp(-N/1000) min(n,m). No prime
short-interval estimate or occupancy-to-orthogonality inference is used.
The remaining separated, smaller-gcd cross terms stay signed and joined.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszNearLabelPayment
open ZetaRieszSharedFactorPayment ZetaRieszDiagonalPayment
open ZetaRieszCofactorPhaseEnergy ZetaRieszJointPrimeEnergy
open ZetaRieszSmoothOwnerDiscrepancy ZetaRieszJointAllocation
open ZetaRieszWideOwnerAudit ZetaRieszCutoffPeriodFloor

/-- Distinct actual integer labels, without a prime or continuum model. -/
def nearPair (ε : ℝ) (n m : ℕ) : Prop :=
  n ≠ m ∧ |(n : ℝ)-m| ≤ ε*min (n : ℝ) (m : ℝ)

theorem nearPair_symm {ε : ℝ} {n m : ℕ} : nearPair ε n m ↔ nearPair ε m n := by
  simp only [nearPair,ne_comm,abs_sub_comm,min_comm]

/-- An exponentially close neighbour set has its literal integer
capacity. This is not a statement about primes in a short interval. -/
theorem nearPair_card_le (S : Finset ℕ) {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    ((S.filter (nearPair ε n)).card : ℝ) ≤ 2*ε*n := by
  let H := ⌊ε*(n : ℝ)⌋₊
  have hsub : S.filter (nearPair ε n) ⊆ (Finset.Icc (n-H) (n+H)).erase n := by
    intro m hm
    obtain ⟨_,hne,hclose⟩ := Finset.mem_filter.mp hm
    have hb : |(n : ℝ)-m| ≤ ε*n :=
      hclose.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hε)
    have hlo : n-H ≤ m := by
      by_cases h : n ≤ m
      · omega
      · have hmn : m ≤ n := by omega
        have hgap : ((n-m : ℕ) : ℝ) ≤ ε*n := by
          rw [Nat.cast_sub hmn]
          exact (le_abs_self _).trans hb
        have hnat : n-m ≤ H := Nat.le_floor hgap
        omega
    have hhi : m ≤ n+H := by
      by_cases h : m ≤ n
      · omega
      · have hnm : n ≤ m := by omega
        have hgap : ((m-n : ℕ) : ℝ) ≤ ε*n := by
          rw [Nat.cast_sub hnm]
          linarith only [neg_le_abs ((n : ℝ)-m),hb]
        have hnat : m-n ≤ H := Nat.le_floor hgap
        omega
    exact Finset.mem_erase.mpr ⟨hne.symm,Finset.mem_Icc.mpr ⟨hlo,hhi⟩⟩
  have hmem : n ∈ Finset.Icc (n-H) (n+H) := Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hc : (S.filter (nearPair ε n)).card ≤ 2*H := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hmem,Nat.card_Icc] at hh
    omega
  have hf : (H : ℝ) ≤ ε*n := Nat.floor_le (mul_nonneg hε (Nat.cast_nonneg n))
  have hcR : ((S.filter (nearPair ε n)).card : ℝ) ≤ 2*(H : ℝ) := by exact_mod_cast hc
  linarith only [hcR,hf]

/-- One capacity inequality covers every count, scale bin and phase.
It is used only on the sparse family, not on the remaining signed sum. -/
theorem symmetric_pair_capacity (S : Finset ℕ) (E : ℕ → ℕ → Prop)
    [DecidableRel E] (hE : ∀ n m,E n m ↔ E m n) (a : ℕ → ℝ) :
    (∑ n ∈ S,∑ m ∈ S,if E n m then a n*a m else 0) ≤
      ∑ n ∈ S,((S.filter (E n)).card : ℝ)*(a n)^2 := by
  let D := ∑ n ∈ S,((S.filter (E n)).card : ℝ)*(a n)^2
  have hfirst : (∑ n ∈ S,∑ m ∈ S,if E n m then (a n)^2 else 0)=D := by
    simp [D,← Finset.sum_filter]
  have hsecond : (∑ n ∈ S,∑ m ∈ S,if E n m then (a m)^2 else 0)=D := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ m ∈ S,∑ n ∈ S,if E m n then (a m)^2 else 0 := by
        apply Finset.sum_congr rfl
        intro m _
        apply Finset.sum_congr rfl
        intro n _
        simp only [hE n m]
      _ = D := hfirst
  have hb : 2*(∑ n ∈ S,∑ m ∈ S,if E n m then a n*a m else 0) ≤
      (∑ n ∈ S,∑ m ∈ S,if E n m then (a n)^2 else 0)+
        (∑ n ∈ S,∑ m ∈ S,if E n m then (a m)^2 else 0) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n _
    apply Finset.sum_le_sum
    intro m _
    split_ifs <;> nlinarith only [sq_nonneg (a n-a m)]
  rw [hfirst,hsecond] at hb
  linarith only [hb]

private theorem divisor_square_harmonic (X : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 X) :
    (∑ n ∈ S,(n.divisors.card : ℝ)^2/(n : ℝ)) ≤
      exp (log X/262144)*divisorSquareDirichletMass (1+1/262144) := by
  have hterm n (hn : n ∈ S) : (n.divisors.card : ℝ)^2/(n : ℝ) ≤
      exp (log X/262144)*
        ((n.divisors.card : ℝ)^2*(n : ℝ)^(-(1+1/262144 : ℝ))) := by
    have hn0 := (Finset.mem_Icc.mp (hS hn)).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hl := log_le_log hnR (show (n : ℝ) ≤ X by exact_mod_cast (Finset.mem_Icc.mp (hS hn)).2)
    have he : (n : ℝ)⁻¹ ≤ exp (log X/262144)*
        (n : ℝ)^(-(1+1/262144 : ℝ)) := by
      rw [show (n : ℝ)⁻¹=exp (-log n) by rw [exp_neg,exp_log hnR],
        rpow_def_of_pos hnR,← exp_add]
      apply exp_le_exp.mpr
      linarith only [hl]
    simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm] using
      mul_le_mul_of_nonneg_left he (sq_nonneg (n.divisors.card : ℝ))
  calc
    _ ≤ ∑ n ∈ S,exp (log X/262144)*
        ((n.divisors.card : ℝ)^2*(n : ℝ)^(-(1+1/262144 : ℝ))) := Finset.sum_le_sum hterm
    _ = exp (log X/262144)*∑ n ∈ S,
        (n.divisors.card : ℝ)^2*(n : ℝ)^(-(1+1/262144 : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_card_divisors_sq_mul_rpow_neg
        (by norm_num : (1 : ℝ)<1+1/262144)).sum_le_tsum _ (fun _ _ => by positivity))
      (exp_pos _).le

/-- The reciprocal pair mass itself is exponentially cheap when
epsilon is exponential. No phase or cross sign is assumed. -/
theorem near_pair_mass_bound (X : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 X) {ε : ℝ} (hε : 0 ≤ ε) :
    (∑ n ∈ S,∑ m ∈ S,if nearPair ε n m then
      ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) ≤
        2*ε*exp (log X/262144)*divisorSquareDirichletMass (1+1/262144) := by
  have hb := symmetric_pair_capacity S (nearPair ε) (fun _ _ => nearPair_symm)
    (fun n => (n.divisors.card : ℝ)/(n : ℝ))
  calc
    _ ≤ ∑ n ∈ S,((S.filter (nearPair ε n)).card : ℝ)*
        ((n.divisors.card : ℝ)/(n : ℝ))^2 := hb
    _ ≤ ∑ n ∈ S,(2*ε*n)*((n.divisors.card : ℝ)/(n : ℝ))^2 :=
      Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_right
        (nearPair_card_le S hε n) (sq_nonneg _))
    _ = 2*ε*∑ n ∈ S,(n.divisors.card : ℝ)^2/(n : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp (hS hn)).1)
      field_simp
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (divisor_square_harmonic X S hS) (by positivity : 0 ≤ 2*ε)

/-- Nearby pairs ONLY inside the smaller-gcd cross population already
retained by the previous payment. The original adverse selection stays. -/
def nearEnergy (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f,
    (∑ n ∈ S,∑ m ∈ S.erase n,
      if (N : ℝ)/1000 < log (Nat.gcd n m) then 0 else
        if nearPair (exp (-(N : ℝ)/1000)) n m then
          (w n*sharp k n)*(w m*sharp k m) else 0)/(k : ℝ)

/-- The rest retains the complete signed correlations; it is not an
orthogonality claim. All original funded overlaps and cutoffs remain. -/
def separatedEnergy (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f,
    (∑ n ∈ S,∑ m ∈ S.erase n,
      if (N : ℝ)/1000 < log (Nat.gcd n m) then 0 else
        if nearPair (exp (-(N : ℝ)/1000)) n m then 0 else
          (w n*sharp k n)*(w m*sharp k m))/(k : ℝ)

/-- A disjoint partition inside the existing smaller-gcd energy.
No cutoff is reselected on either subfamily. -/
theorem smallSharedEnergy_eq (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) :
    smallSharedEnergy X N S w f = nearEnergy X N S w f+separatedEnergy X N S w f := by
  simp only [smallSharedEnergy,nearEnergy,separatedEnergy,
    ← Finset.sum_add_distrib,← add_div]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  split_ifs <;> simp

/-- The near-pair price is paid by actual integer capacity and a
convergent divisor-square mass, across every phase and occupied bin. -/
theorem nearEnergy_bound (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X)
    {V : ℝ} (hV : 0 ≤ V) (hw : ∀ n ∈ S,|w n| ≤ V/(n : ℝ)) :
    |nearEnergy X N S w f| ≤
      (1+log X)*V^2*(2*exp (-(N : ℝ)/1000)*exp (log X/262144)*
        divisorSquareDirichletMass (1+1/262144)) := by
  let ε := exp (-(N : ℝ)/1000)
  let P := ∑ n ∈ S,∑ m ∈ S,if nearPair ε n m then
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
      |if (N : ℝ)/1000 < log (Nat.gcd n m) then 0 else
          if nearPair ε n m then (w n*sharp k n)*(w m*sharp k m) else 0| ≤
        V^2*(if nearPair ε n m then
          ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) := by
    split_ifs
    · simp only [abs_zero]
      positivity
    · simp
    · rw [abs_mul]
      exact (mul_le_mul (hs n hn k) (hs m hm k) (abs_nonneg _)
        (by positivity)).trans_eq (by ring)
    · simp
  have hrow k : |∑ n ∈ S,∑ m ∈ S.erase n,
      if (N : ℝ)/1000 < log (Nat.gcd n m) then 0 else
        if nearPair ε n m then (w n*sharp k n)*(w m*sharp k m) else 0| ≤ V^2*P := by
    calc
      _ ≤ ∑ n ∈ S,|∑ m ∈ S.erase n,
          if (N : ℝ)/1000 < log (Nat.gcd n m) then 0 else
            if nearPair ε n m then (w n*sharp k n)*(w m*sharp k m) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ S,∑ m ∈ S.erase n,
          |if (N : ℝ)/1000 < log (Nat.gcd n m) then 0 else
            if nearPair ε n m then (w n*sharp k n)*(w m*sharp k m) else 0| :=
        Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ n ∈ S,∑ m ∈ S.erase n,V^2*(if nearPair ε n m then
          ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) :=
        Finset.sum_le_sum (fun n hn => Finset.sum_le_sum
          (fun m hm => hterm n hn m (Finset.mem_of_mem_erase hm) k))
      _ ≤ ∑ n ∈ S,∑ m ∈ S,V^2*(if nearPair ε n m then
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
  have hmass := near_pair_mass_bound X S hS (show 0 ≤ ε from (exp_pos _).le)
  have hlog : 0 ≤ 1+log X := by
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
    linarith [log_nonneg hX1]
  calc
    _ ≤ ∑ k ∈ K,|∑ n ∈ S,∑ m ∈ S.erase n,
        if (N : ℝ)/1000 < log (Nat.gcd n m) then 0 else
          if nearPair ε n m then (w n*sharp k n)*(w m*sharp k m) else 0|/(k : ℝ) := by
      have ha (k : ℕ) : |(k : ℝ)|=(k : ℝ) := abs_of_nonneg (Nat.cast_nonneg k)
      simpa only [nearEnergy,ε,abs_div,ha] using
        Finset.abs_sum_le_sum_abs (s := K)
          (fun k : ℕ => (∑ n ∈ S,∑ m ∈ S.erase n,
            if (N : ℝ)/1000 < log (Nat.gcd n m) then 0 else
              if nearPair ε n m then (w n*sharp k n)*(w m*sharp k m) else 0)/(k : ℝ))
    _ ≤ ∑ k ∈ K,(V^2*P)/(k : ℝ) := Finset.sum_le_sum
      (fun k _ => div_le_div_of_nonneg_right (hrow k) (Nat.cast_nonneg k))
    _ = (∑ k ∈ K,(k : ℝ)⁻¹)*(V^2*P) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ (1+log X)*(V^2*P) := mul_le_mul_of_nonneg_right hh (mul_nonneg (sq_nonneg V) hP)
    _ ≤ (1+log X)*V^2*(2*ε*exp (log X/262144)*
        divisorSquareDirichletMass (1+1/262144)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmass
        (mul_nonneg hlog (sq_nonneg V))

/-- The fixed convergent divisor mass is not a computed starting-order
constant. The bound is uniform in fixed height and every funding overlap. -/
def nearConstant (B : ℝ) : ℝ :=
  32*radiusCeiling^2*B^2*divisorSquareDirichletMass (1+1/262144)*exp (3/262144)

/-- This is the near-pair energy price, not an allowance on the
unpaid separated signed cross sum. -/
def nearPrice (B : ℝ) (N : ℕ) : ℝ :=
  sqrt (4*nearConstant B)*((N : ℝ)+1)^2*exp (-(1/4000 : ℝ)*N)

private theorem nearConstant_nonneg (B : ℝ) : 0 ≤ nearConstant B := by
  unfold nearConstant
  positivity [divisorSquareDirichletMass_nonneg (1+1/262144)]

/-- The neighbour capacity saving beats actual squared source growth,
including the fixed Dirichlet-exponent cost. -/
theorem near_source_rate {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (N : ℕ) :
    (2*u)^(2*(N+1))*exp ((3/262144-1/1000 : ℝ)*N) ≤
      4*radiusCeiling^2*exp (-(1/2000 : ℝ)*N) := by
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
    _ ≤ (2*radiusCeiling)^(2*(N+1))*exp ((3/262144-1/1000 : ℝ)*N) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity : 0 ≤ 2*u) (by linarith : 2*u≤2*radiusCeiling) _)
        (exp_pos _).le
    _ = 4*radiusCeiling^2*exp
        ((2*log (2*radiusCeiling)+3/262144-1/1000)*(N : ℝ)) := by
      rw [he,mul_assoc,← exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by
      nlinarith only [hlog,Nat.cast_nonneg (α := ℝ) N])) (by positivity)

/-- Exponential bound on the EXISTING near-pair signed cross aggregate;
the full original phase and factorial allocation remain in the weights. -/
theorem weighted_nearEnergy_bound (X N : ℕ) (A S : Finset ℕ) (f q : ℕ → ℝ) (y : ℝ)
    {B L u : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X)
    (hlog : log X ≤ 3*((N : ℝ)+1)) (hq : ∀ n ∈ S,|q n| ≤ B) :
    |nearEnergy X N S (fun n => u^(N+1)*q n*primeWeight A L y N n 1) f| ≤
      nearConstant B*((N : ℝ)+1)^3*exp (-(1/2000 : ℝ)*N) := by
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
  have hb := nearEnergy_bound X N S _ f hX hS hV hw
  have hh : 1+log X ≤ 4*((N : ℝ)+1) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have he : exp (log X/262144) ≤
      exp (3/262144)*exp ((3/262144 : ℝ)*N) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    linarith only [hlog]
  have hprod := mul_le_mul hh he (exp_pos _).le (show 0 ≤ 4*((N : ℝ)+1) by positivity)
  have hvpow : V^2=B^2*((N : ℝ)+1)^2*(2*u)^(2*(N+1)) := by
    dsimp [V,radialCap]
    rw [show 2*(N+1)=(N+1)*2 by omega,pow_mul]
    simp only [mul_pow]
    ring
  have hQ : 0 ≤ V^2*(2*exp (-(N : ℝ)/1000))*divisorSquareDirichletMass (1+1/262144) := by
    positivity [divisorSquareDirichletMass_nonneg (1+1/262144)]
  have hc := mul_le_mul_of_nonneg_right hprod hQ
  have hg := mul_le_mul_of_nonneg_left (near_source_rate hu hU N)
    (show 0 ≤ 8*B^2*((N : ℝ)+1)^3*divisorSquareDirichletMass (1+1/262144)*exp (3/262144) by
      positivity [divisorSquareDirichletMass_nonneg (1+1/262144)])
  calc
    _ ≤ (1+log X)*V^2*(2*exp (-(N : ℝ)/1000)*exp (log X/262144)*
        divisorSquareDirichletMass (1+1/262144)) := hb
    _ = ((1+log X)*exp (log X/262144))*
        (V^2*(2*exp (-(N : ℝ)/1000))*divisorSquareDirichletMass (1+1/262144)) := by ring
    _ ≤ (4*((N : ℝ)+1)*(exp (3/262144)*exp ((3/262144 : ℝ)*N)))*
        (V^2*(2*exp (-(N : ℝ)/1000))*divisorSquareDirichletMass (1+1/262144)) := hc
    _ = (8*B^2*((N : ℝ)+1)^3*divisorSquareDirichletMass (1+1/262144)*exp (3/262144))*
        ((2*u)^(2*(N+1))*exp ((3/262144-1/1000 : ℝ)*N)) := by
      rw [hvpow]
      have ht : exp ((3/262144 : ℝ)*N)*exp (-(N : ℝ)/1000)=
          exp ((3/262144-1/1000 : ℝ)*N) := by rw [← exp_add]; congr 1; ring
      rw [← ht]
      ring
    _ ≤ _ := hg.trans_eq (by unfold nearConstant; ring)

/-- The near-pair error is spent ONCE. Both subfamilies keep the same
original whole-sum adverse selection, including favorable supply phases. -/
theorem near_crossCost_split (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) :
    sqrt (max (smallSharedEnergy X N S w f) 0*adverseProfileEnergy X S w f) ≤
      sqrt (max (separatedEnergy X N S w f) 0*adverseProfileEnergy X S w f)+
        sqrt (|nearEnergy X N S w f| *adverseProfileEnergy X S w f) := by
  let P := adverseProfileEnergy X S w f
  have hP : 0 ≤ P := Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hm : max (smallSharedEnergy X N S w f) 0 ≤
      max (separatedEnergy X N S w f) 0+|nearEnergy X N S w f| := by
    apply max_le
    · rw [smallSharedEnergy_eq X N S w f]
      linarith only [le_max_left (separatedEnergy X N S w f) 0,le_abs_self (nearEnergy X N S w f)]
    · exact add_nonneg (le_max_right _ _) (abs_nonneg _)
  have hb := mul_le_mul_of_nonneg_right hm hP
  have hA : 0 ≤ max (separatedEnergy X N S w f) 0*P := mul_nonneg (le_max_right _ _) hP
  have hB : 0 ≤ |nearEnergy X N S w f| *P := mul_nonneg (abs_nonneg _) hP
  have hC : 0 ≤ max (smallSharedEnergy X N S w f) 0*P := mul_nonneg (le_max_right _ _) hP
  apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
  rw [sq_sqrt hC]
  nlinarith only [hb,sq_sqrt hA,sq_sqrt hB,
    mul_nonneg (sqrt_nonneg (max (separatedEnergy X N S w f) 0*P))
      (sqrt_nonneg (|nearEnergy X N S w f| *P))]

/-- Source-geometric price after joining all native counts and funding
overlaps. No independent price on a count, bin or phase is introduced. -/
theorem weighted_near_price (X N : ℕ) (A S : Finset ℕ) (q : ℕ → ℝ) (y : ℝ)
    {B L u : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X)
    (hlog : log X ≤ 3*((N : ℝ)+1)) (hq : ∀ n ∈ S,|q n| ≤ B) :
    let f := correctedProfile X L 1 0
    let w := fun n => u^(N+1)*q n*primeWeight A L y N n 1;
    sqrt (|nearEnergy X N S w f| *adverseProfileEnergy X S w f) ≤ nearPrice B N := by
  let f := correctedProfile X L 1 0
  let w := fun n => u^(N+1)*q n*primeWeight A L y N n 1
  have he := weighted_nearEnergy_bound X N A S f q y hB hL hu hU hX hS hlog hq
  have hP : 0 ≤ adverseProfileEnergy X S w f := Finset.sum_nonneg (fun _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hp : adverseProfileEnergy X S w f ≤ 4*((N : ℝ)+1) := by
    have hs : ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f ⊆ activeCutoffs X f :=
      Finset.filter_subset _ _
    exact (Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))).trans
        ((corrected_profileEnergy_le X L).trans (by linarith only [hlog,Nat.cast_nonneg (α := ℝ) N]))
  have hC := nearConstant_nonneg B
  have hprod := mul_le_mul he hp hP
    (show 0 ≤ nearConstant B*((N : ℝ)+1)^3*exp (-(1/2000 : ℝ)*N) by positivity)
  apply (sq_le_sq₀ (sqrt_nonneg _) (by unfold nearPrice; positivity)).mp
  rw [sq_sqrt (mul_nonneg (abs_nonneg _) hP)]
  apply hprod.trans_eq
  unfold nearPrice
  rw [mul_pow,mul_pow,sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC),← exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show exp ((2 : ℝ)*(-(1/4000)*(N : ℝ)))=exp (-(1/2000)*(N : ℝ)) by congr 1; ring]
  ring

/-- The whole sparse family is source-o(1), independently of its
coherent phases and any occupied-bin pattern. -/
theorem tendsto_nearPrice (B : ℝ) : Tendsto (nearPrice B) atTop (𝓝 0) := by
  have ht := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 2
    (exp_pos (-(1/4000 : ℝ))) (exp_lt_one_iff.mpr (by norm_num : -(1/4000 : ℝ) < 0))
  have hh := ht.const_mul (sqrt (4*nearConstant B))
  simpa only [mul_zero] using hh.congr' (Eventually.of_forall fun N => by
    unfold nearPrice
    rw [← exp_nat_mul]
    rw [show exp ((N : ℝ)*(-(1/4000)))=exp (-(1/4000)*(N : ℝ)) by congr 1; ring]
    ring)

private theorem relative_gap_log {ε x v : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hx : 0 < x) (hv : 0 < v) (hgap : ε*x < v-x) :
    ε/2 < log v-log x := by
  have hdiv : 1+ε < v/x := (lt_div_iff₀ hx).mpr (by nlinarith only [hgap])
  have hlo : ε/2 ≤ 2*ε/(ε+2) :=
    (le_div_iff₀ (by linarith : 0 < ε+2)).mpr (by nlinarith only [hε,hε1])
  have hh := log_lt_log (by linarith : 0 < 1+ε) hdiv
  rw [log_div hv.ne' hx.ne'] at hh
  exact (hlo.trans (le_log_one_add_of_nonneg hε)).trans_lt hh

/-- The remaining distinct labels have an actual Mellin-frequency
gap. It decreases exponentially: this alone is NOT a fixed-height
large-sieve or automatic many-bin orthogonality estimate. -/
theorem separated_log_gap (N : ℕ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hne : n ≠ m) (hnot : ¬nearPair (exp (-(N : ℝ)/1000)) n m) :
    exp (-(N : ℝ)/1000)/2 < |log n-log m| := by
  let ε := exp (-(N : ℝ)/1000)
  have hε : 0 ≤ ε := (exp_pos _).le
  have hε1 : ε ≤ 1 := exp_le_one_iff.mpr (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hg : ε*min (n : ℝ) (m : ℝ) < |(n : ℝ)-m| := by
    apply lt_of_not_ge
    intro hh
    exact hnot ⟨hne,hh⟩
  rcases lt_or_gt_of_ne hne with h | h
  · have hr : (n : ℝ) < m := by exact_mod_cast h
    rw [min_eq_left hr.le,abs_of_neg (by linarith : (n : ℝ)-m < 0)] at hg
    have hl := relative_gap_log hε hε1 hnR hmR (by linarith only [hg])
    exact hl.trans_le (by linarith only [neg_le_abs (log n-log m)])
  · have hr : (m : ℝ) < n := by exact_mod_cast h
    rw [min_eq_right hr.le,abs_of_pos (by linarith : (0 : ℝ) < n-m)] at hg
    exact (relative_gap_log hε hε1 hmR hnR hg).trans_le (le_abs_self _)

open ZetaRieszParityPacket ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint
open ZetaRieszRadialCompensation ZetaRieszBandCompensation
open ZetaRieszRejoinedPopulationFloor ZetaRieszJoinedPopulationFloor ZetaRieszFewBinCoverFloor
open ZetaRieszSevenCountTail ZetaRieszRejoinedPhaseFloor
open ZetaRieszLowCountRefund (tailCost)

/-- Native whole-floor comparison after paying the diagonal, large-gcd
and nearby-label correlations geometrically. ALL original funding and
physical/count/bin support remains. The one joined separated, smaller-gcd
signed cross cost still needs an independent numerical bound. -/
theorem eventually_joined_separated_floor {u y : ℝ} (hu : 1/2 < u)
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
            -sqrt (max (separatedEnergy X N (S.filter Squarefree) w f) 0*
              adverseProfileEnergy X (S.filter Squarefree) w f)-err j ≤
              ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  obtain ⟨h,c,κ,hh,hhu,hc,hκ,hbase⟩ := ZetaRieszSharedFactorPayment.eventually_joined_small_shared_floor hu hU hy
  refine ⟨h,c,κ,hh,hhu,hc,hκ,?_⟩
  intro ε hε
  obtain ⟨err,he0,he,hfloor⟩ := hbase ε hε
  have hB : 0 ≤ 4+|ε| := by positivity
  refine ⟨fun j => err j+nearPrice (4+|ε|) (dyadicMomentOrder j),?_,?_,?_⟩
  · intro j
    exact add_nonneg (he0 j) (by unfold nearPrice; positivity)
  · simpa only [add_zero,Function.comp_def] using
      he.add ((tendsto_nearPrice (4+|ε|)).comp tendsto_dyadicMomentOrder)
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
  let S := ((H ∪ Paid) ∪ Ts) ∪ Ys
  let X := max 1 (S.sup id)
  let f := correctedProfile X L 1 0
  let atom := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let a : ℝ := if 0 ≤ (∑ n ∈ Paid,atom n).re then 1 else 0
  let b : ℝ := if 0 ≤ (∑ n ∈ Ts,atom n).re then 1 else 0
  let w := fun n => u^(N+1)*rejoinedWeights H Paid Ts Ys a b
    (tailCost c N+ε+growingDebit κ N) n*primeWeight A L y N n 1
  have hS : S ⊆ S₀ := by
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
  have hX : 0 < X := by dsimp [X]; omega
  have hSX : S.filter Squarefree ⊆ Finset.Icc 1 X := by
    intro n hn
    obtain ⟨hn,hSF⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hSF.ne_zero,
      (Finset.le_sup (f := id) hn).trans (le_max_right _ _)⟩
  have hL1 : 1 ≤ L := by
    have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [L,N]
    norm_num at hL
    linarith
  have hq' n (hn : n ∈ S.filter Squarefree) :
      |rejoinedWeights H Paid Ts Ys a b (tailCost c N+ε+growingDebit κ N) n| ≤ 4+|ε| := by
    simpa only [Real.norm_eq_abs] using hq H Paid Ts Ys a b
      (by dsimp [a]; split_ifs <;> norm_num) (by dsimp [a]; split_ifs <;> norm_num)
      (by dsimp [b]; split_ifs <;> norm_num) (by dsimp [b]; split_ifs <;> norm_num) n
  have hprice := weighted_near_price X N A (S.filter Squarefree)
    (rejoinedWeights H Paid Ts Ys a b (tailCost c N+ε+growingDebit κ N)) y
      hB hL1 (by linarith : 0 ≤ u) hU hX hSX
      (window_sup_log S (hS.trans (ZetaRieszNonownerAllocation.coreBand_subset_literalWindow u N K))) hq'
  have hsplit := near_crossCost_split X N (S.filter Squarefree) w f
  dsimp only [N,K,A,L,S₀,Paid,H,Ts,Ys,S,X,f,atom,a,b,w] at hprice hsplit
  dsimp only at hbound ⊢
  nlinarith only [hbound,hprice,hsplit]

end RiemannGaussian.ZetaRieszNearLabelPayment
