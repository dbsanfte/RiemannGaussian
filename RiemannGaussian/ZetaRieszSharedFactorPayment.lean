/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszDiagonalPayment

/-!
# Pay correlations with a large actual shared factor

The original funded prefix weights have reciprocal decay on their
actual integer labels. A common-factor convolution therefore pays all
ordered cross pairs with log(gcd(n,m)) > N/1000 geometrically, even when
their phases reinforce. The complementary cross sum retains every sign,
allocation, cutoff and supply overlap. No many-bin orthogonality or
arithmetic estimate for that remaining sum is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszSharedFactorPayment
open ZetaRieszDiagonalPayment ZetaRieszCofactorPhaseEnergy
open ZetaRieszJointPrimeEnergy ZetaRieszSmoothOwnerDiscrepancy
open ZetaRieszJointAllocation
open ZetaRieszWideOwnerAudit ZetaRieszCutoffPeriodFloor

/-- The exact adverse ordered cross pairs having a large actual gcd.
Their original weights and signed prefix columns are unchanged. -/
def largeSharedEnergy (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f,
    (∑ n ∈ S,∑ m ∈ S.erase n,
      if (N : ℝ)/1000 < log (Nat.gcd n m) then
        (w n*sharp k n)*(w m*sharp k m) else 0)/(k : ℝ)

/-- All remaining cross pairs in the SAME funded adverse prefix sum.
No absolute value is taken on any of their individual phases or signs. -/
def smallSharedEnergy (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f,
    (∑ n ∈ S,∑ m ∈ S.erase n,
      if (N : ℝ)/1000 < log (Nat.gcd n m) then 0 else
        (w n*sharp k n)*(w m*sharp k m))/(k : ℝ)

/-- This is a partition of the existing signed cross term, not a
completed or reweighted carrier. Both funding overlaps are retained. -/
theorem adverseCrossEnergy_eq (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) :
    adverseCrossEnergy X S w f =
      largeSharedEnergy X N S w f+smallSharedEnergy X N S w f := by
  simp only [adverseCrossEnergy,largeSharedEnergy,smallSharedEnergy,
    ← Finset.sum_add_distrib,← add_div]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  split_ifs <;> simp

private theorem divisor_harmonic_bound {X : ℕ} (_hX : 0 < X) :
    (∑ n ∈ Finset.Icc 1 X,(n.divisors.card : ℝ)/(n : ℝ)) ≤
      exp (log X/262144)*divisorSquareDirichletMass (1+1/262144) := by
  have hterm n (hn : n ∈ Finset.Icc 1 X) :
      (n.divisors.card : ℝ)/(n : ℝ) ≤
        exp (log X/262144)*
          ((n.divisors.card : ℝ)^2*(n : ℝ)^(-(1+1/262144 : ℝ))) := by
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hcard : (1 : ℝ) ≤ n.divisors.card := by
      exact_mod_cast Finset.card_pos.mpr
        ⟨1,Nat.mem_divisors.mpr ⟨one_dvd n,hn0.ne'⟩⟩
    have hl : log n ≤ log X := log_le_log hnR
      (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
    have hi : (n : ℝ)⁻¹=exp (-log n) := by rw [exp_neg,exp_log hnR]
    have he : exp (-log n) ≤
        exp (log X/262144)*exp (log n*(-(1+1/262144 : ℝ))) := by
      rw [← exp_add]
      apply exp_le_exp.mpr
      linarith only [hl]
    calc
      _ ≤ (n.divisors.card : ℝ)^2*(n : ℝ)⁻¹ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (by nlinarith only [hcard]) (by positivity)
      _ ≤ _ := by
        rw [hi,rpow_def_of_pos hnR]
        exact (mul_le_mul_of_nonneg_left he (sq_nonneg _)).trans_eq (by ring)
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X,exp (log X/262144)*
        ((n.divisors.card : ℝ)^2*(n : ℝ)^(-(1+1/262144 : ℝ))) :=
      Finset.sum_le_sum hterm
    _ = exp (log X/262144)*∑ n ∈ Finset.Icc 1 X,
        (n.divisors.card : ℝ)^2*(n : ℝ)^(-(1+1/262144 : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_card_divisors_sq_mul_rpow_neg
        (by norm_num : (1 : ℝ)<1+1/262144)).sum_le_tsum _
          (fun _ _ => by positivity)) (exp_pos _).le

/-- Actual squarefree multiples retain the exact divided label. A
finite Dirichlet mass bounds the complete row, with no prime model. -/
theorem common_factor_row_bound {X g : ℕ} (hX : 0 < X) (hg : 0 < g)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 X) (hSF : ∀ n ∈ S,Squarefree n) :
    (∑ n ∈ S,if g ∣ n then (n.divisors.card : ℝ)/(n : ℝ) else 0) ≤
      ((g.divisors.card : ℝ)/(g : ℝ))*
        (exp (log X/262144)*divisorSquareDirichletMass (1+1/262144)) := by
  let U := S.filter (fun n => g ∣ n)
  let Q := U.image (fun n => n/g)
  have hU n (hn : n ∈ U) : n ∈ S ∧ g ∣ n := Finset.mem_filter.mp hn
  have hpos n (hn : n ∈ U) : 0 < n := (Finset.mem_Icc.mp (hS (hU n hn).1)).1
  have hquot n (hn : n ∈ U) : 0 < n/g :=
    Nat.div_pos (Nat.le_of_dvd (hpos n hn) (hU n hn).2) hg
  have hinj : Set.InjOn (fun n : ℕ => n/g) U := by
    intro n hn m hm he
    calc
      n = g*(n/g) := (Nat.mul_div_cancel' (hU n hn).2).symm
      _ = g*(m/g) := congrArg (fun a : ℕ => g*a) he
      _ = m := Nat.mul_div_cancel' (hU m hm).2
  have hQ : Q ⊆ Finset.Icc 1 X := by
    intro a ha
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_Icc.mpr ⟨hquot n hn,
      (Nat.div_le_self n g).trans (Finset.mem_Icc.mp (hS (hU n hn).1)).2⟩
  have he : (∑ n ∈ U,(n.divisors.card : ℝ)/(n : ℝ)) =
      ((g.divisors.card : ℝ)/(g : ℝ))*
        ∑ a ∈ Q,(a.divisors.card : ℝ)/(a : ℝ) := by
    rw [Finset.mul_sum,Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    have hf := Nat.mul_div_cancel' (hU n hn).2
    have hc : g.Coprime (n/g) := Nat.coprime_of_squarefree_mul (by
      rw [hf]; exact hSF n (hU n hn).1)
    have ht : n.divisors.card=g.divisors.card*(n/g).divisors.card := by
      calc
        _ = (g*(n/g)).divisors.card := congrArg (fun a : ℕ => a.divisors.card) hf.symm
        _ = _ := hc.card_divisors_mul
    have hfR : (g : ℝ)*(n/g : ℕ)=(n : ℝ) := by exact_mod_cast hf
    rw [ht,Nat.cast_mul,← hfR]
    field_simp
  rw [← Finset.sum_filter]
  change (∑ n ∈ U,_) ≤ _
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hQ
    (fun _ _ _ => by positivity)).trans (divisor_harmonic_bound hX)

/-- Reciprocal divisor pairs with a large ACTUAL gcd have an explicit
geometric sparsity bound, uniform in every selected squarefree population. -/
theorem large_common_factor_mass (X N : ℕ) (S : Finset ℕ) (hX : 0 < X)
    (hS : S ⊆ Finset.Icc 1 X) (hSF : ∀ n ∈ S,Squarefree n) :
    (∑ n ∈ S,∑ m ∈ S,
      if (N : ℝ)/1000 < log (Nat.gcd n m) then
        ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) ≤
      (exp (log X/262144)*divisorSquareDirichletMass (1+1/262144))^2*
        (exp (-(1/2000 : ℝ)*N)*divisorSquareDirichletMass (3/2)) := by
  let G := (Finset.Icc 1 X).filter (fun g : ℕ => (N : ℝ)/1000 < log g)
  let z := fun g n : ℕ => if g ∣ n then (n.divisors.card : ℝ)/(n : ℝ) else 0
  have hz g n : 0 ≤ z g n := by dsimp [z]; split_ifs <;> positivity
  have hpair n (hn : n ∈ S) m (hm : m ∈ S) :
      (if (N : ℝ)/1000 < log (Nat.gcd n m) then
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
      exp (-(1/2000 : ℝ)*N)*divisorSquareDirichletMass (3/2) := by
    have ht g (hg : g ∈ G) :
        (g.divisors.card : ℝ)^2/(g : ℝ)^2 ≤
          exp (-(1/2000 : ℝ)*N)*((g.divisors.card : ℝ)^2*(g : ℝ)^(-(3/2 : ℝ))) := by
      have hp : (0 : ℝ)<g := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hg).1).1
      have hl := (Finset.mem_filter.mp hg).2
      have hi : (g : ℝ)⁻¹=exp (-log g) := by rw [exp_neg,exp_log hp]
      have he : (g : ℝ)⁻¹^2 ≤ exp (-(1/2000 : ℝ)*N)*(g : ℝ)^(-(3/2 : ℝ)) := by
        rw [hi,← exp_nat_mul,rpow_def_of_pos hp,← exp_add]
        apply exp_le_exp.mpr
        norm_num only [Nat.cast_ofNat]
        nlinarith only [hl]
      simpa only [div_eq_mul_inv,inv_pow,mul_assoc,mul_left_comm,mul_comm] using
        mul_le_mul_of_nonneg_left he (sq_nonneg (g.divisors.card : ℝ))
    calc
      _ ≤ ∑ g ∈ G,exp (-(1/2000 : ℝ)*N)*
          ((g.divisors.card : ℝ)^2*(g : ℝ)^(-(3/2 : ℝ))) := Finset.sum_le_sum ht
      _ = exp (-(1/2000 : ℝ)*N)*∑ g ∈ G,
          (g.divisors.card : ℝ)^2*(g : ℝ)^(-(3/2 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((summable_card_divisors_sq_mul_rpow_neg (by norm_num : (1 : ℝ)<3/2)).sum_le_tsum
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
theorem largeSharedEnergy_bound (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X) (hSF : ∀ n ∈ S,Squarefree n)
    {V : ℝ} (hV : 0 ≤ V) (hw : ∀ n ∈ S,|w n| ≤ V/(n : ℝ)) :
    |largeSharedEnergy X N S w f| ≤
      (1+log X)*V^2*(exp (log X/262144)*
        divisorSquareDirichletMass (1+1/262144))^2*
          (exp (-(1/2000 : ℝ)*N)*divisorSquareDirichletMass (3/2)) := by
  let P := ∑ n ∈ S,∑ m ∈ S,
    if (N : ℝ)/1000 < log (Nat.gcd n m) then
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
      |if (N : ℝ)/1000 < log (Nat.gcd n m) then
        (w n*sharp k n)*(w m*sharp k m) else 0| ≤
          V^2*(if (N : ℝ)/1000 < log (Nat.gcd n m) then
            ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) := by
    split_ifs
    · rw [abs_mul]
      exact (mul_le_mul (hs n hn k) (hs m hm k) (abs_nonneg _)
        (by positivity)).trans_eq (by ring)
    · simp
  have hrow k : |∑ n ∈ S,∑ m ∈ S.erase n,
      if (N : ℝ)/1000 < log (Nat.gcd n m) then
        (w n*sharp k n)*(w m*sharp k m) else 0| ≤ V^2*P := by
    calc
      _ ≤ ∑ n ∈ S,|∑ m ∈ S.erase n,
          if (N : ℝ)/1000 < log (Nat.gcd n m) then
            (w n*sharp k n)*(w m*sharp k m) else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ S,∑ m ∈ S.erase n,
          |if (N : ℝ)/1000 < log (Nat.gcd n m) then
            (w n*sharp k n)*(w m*sharp k m) else 0| :=
        Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ n ∈ S,∑ m ∈ S.erase n,
          V^2*(if (N : ℝ)/1000 < log (Nat.gcd n m) then
            ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) :=
        Finset.sum_le_sum (fun n hn => Finset.sum_le_sum
          (fun m hm => hterm n hn m (Finset.mem_of_mem_erase hm) k))
      _ ≤ ∑ n ∈ S,∑ m ∈ S,
          V^2*(if (N : ℝ)/1000 < log (Nat.gcd n m) then
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
      (exp (-(1/2000 : ℝ)*N)*divisorSquareDirichletMass (3/2)) :=
    large_common_factor_mass X N S hX hS hSF
  have hlog : 0 ≤ 1+log X := by
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
    linarith [log_nonneg hX1]
  calc
    _ ≤ ∑ k ∈ K,|∑ n ∈ S,∑ m ∈ S.erase n,
        if (N : ℝ)/1000 < log (Nat.gcd n m) then
          (w n*sharp k n)*(w m*sharp k m) else 0|/(k : ℝ) := by
      have ha (k : ℕ) : |(k : ℝ)|=(k : ℝ) := abs_of_nonneg (Nat.cast_nonneg k)
      simpa only [largeSharedEnergy,abs_div,ha] using
        Finset.abs_sum_le_sum_abs (s := K)
          (fun k : ℕ => (∑ n ∈ S,∑ m ∈ S.erase n,
            if (N : ℝ)/1000 < log (Nat.gcd n m) then
              (w n*sharp k n)*(w m*sharp k m) else 0)/(k : ℝ))
    _ ≤ ∑ k ∈ K,(V^2*P)/(k : ℝ) := Finset.sum_le_sum
      (fun k _ => div_le_div_of_nonneg_right (hrow k) (Nat.cast_nonneg k))
    _ = (∑ k ∈ K,(k : ℝ)⁻¹)*(V^2*P) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ (1+log X)*(V^2*P) := mul_le_mul_of_nonneg_right hh (mul_nonneg (sq_nonneg V) hP)
    _ ≤ (1+log X)*V^2*((exp (log X/262144)*divisorSquareDirichletMass (1+1/262144))^2*
        (exp (-(1/2000 : ℝ)*N)*divisorSquareDirichletMass (3/2))) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hmass (mul_nonneg hlog (sq_nonneg V))
    _ = _ := by ring

/-- Fixed finite constants from genuine convergent divisor masses.
They are not evaluated numerically or used as a finite-start certificate. -/
def sharedConstant (B : ℝ) : ℝ :=
  16*radiusCeiling^2*B^2*divisorSquareDirichletMass (1+1/262144)^2*
    divisorSquareDirichletMass (3/2)*exp (6/262144)

/-- Source-scale price of ALL large-shared-factor cross correlations.
This is a paid error, not a price on the remaining signed cross sum. -/
def sharedPrice (B : ℝ) (N : ℕ) : ℝ :=
  sqrt (4*sharedConstant B)*((N : ℝ)+1)^2*exp (-(1/8000 : ℝ)*N)

private theorem sharedConstant_nonneg (B : ℝ) : 0 ≤ sharedConstant B := by
  unfold sharedConstant
  positivity [divisorSquareDirichletMass_nonneg (3/2)]

/-- The ACTUAL shared-factor gap dominates both source growth and
the fixed Dirichlet-exponent loss at the current outer radius. -/
theorem shared_source_rate {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (N : ℕ) :
    (2*u)^(2*(N+1))*exp ((6/262144-1/2000 : ℝ)*N) ≤
      4*radiusCeiling^2*exp (-(1/4000 : ℝ)*N) := by
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
    _ ≤ (2*radiusCeiling)^(2*(N+1))*exp ((6/262144-1/2000 : ℝ)*N) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity : 0 ≤ 2*u) (by linarith : 2*u≤2*radiusCeiling) _)
        (exp_pos _).le
    _ = 4*radiusCeiling^2*exp
        ((2*log (2*radiusCeiling)+6/262144-1/2000)*(N : ℝ)) := by
      rw [he,mul_assoc,← exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by
      nlinarith only [hlog,Nat.cast_nonneg (α := ℝ) N])) (by positivity)

/-- Uniform geometric payment of the original source-weighted large-gcd
cross aggregate. Squarefreeness and all literal masks remain in S; the
actual phase, factorial allocation and signed funding remain in q,w. -/
theorem weighted_largeShared_bound (X N : ℕ) (A S : Finset ℕ) (f q : ℕ → ℝ) (y : ℝ)
    {B L u : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X) (hSF : ∀ n ∈ S,Squarefree n)
    (hlog : log X ≤ 3*((N : ℝ)+1)) (hq : ∀ n ∈ S,|q n| ≤ B) :
    |largeSharedEnergy X N S (fun n => u^(N+1)*q n*primeWeight A L y N n 1) f| ≤
      sharedConstant B*((N : ℝ)+1)^3*exp (-(1/4000 : ℝ)*N) := by
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
  have hb := largeSharedEnergy_bound X N S _ f hX hS hSF hV hw
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
      exp (-(1/2000 : ℝ)*N)*divisorSquareDirichletMass (3/2) := by
    positivity [divisorSquareDirichletMass_nonneg (3/2)]
  have hc := mul_le_mul_of_nonneg_right hprod hQ
  have hg := mul_le_mul_of_nonneg_left (shared_source_rate hu hU N)
    (show 0 ≤ 4*B^2*((N : ℝ)+1)^3*divisorSquareDirichletMass (1+1/262144)^2*
      divisorSquareDirichletMass (3/2)*exp (6/262144) by
        positivity [divisorSquareDirichletMass_nonneg (3/2)])
  calc
    _ ≤ (1+log X)*V^2*(exp (log X/262144)*
        divisorSquareDirichletMass (1+1/262144))^2*
          (exp (-(1/2000 : ℝ)*N)*divisorSquareDirichletMass (3/2)) := hb
    _ = ((1+log X)*exp (2*(log X/262144)))*
        (V^2*divisorSquareDirichletMass (1+1/262144)^2*
          exp (-(1/2000 : ℝ)*N)*divisorSquareDirichletMass (3/2)) := by
      rw [mul_pow (exp (log X/262144)) (divisorSquareDirichletMass (1+1/262144)) 2,
        ← exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      ring
    _ ≤ (4*((N : ℝ)+1)*(exp (6/262144)*exp ((6/262144 : ℝ)*N)))*
        (V^2*divisorSquareDirichletMass (1+1/262144)^2*
          exp (-(1/2000 : ℝ)*N)*divisorSquareDirichletMass (3/2)) := hc
    _ = (4*B^2*((N : ℝ)+1)^3*divisorSquareDirichletMass (1+1/262144)^2*
        divisorSquareDirichletMass (3/2)*exp (6/262144))*
          ((2*u)^(2*(N+1))*exp ((6/262144-1/2000 : ℝ)*N)) := by
      rw [hvpow]
      have ht : exp ((6/262144 : ℝ)*N)*exp (-(1/2000 : ℝ)*N)=
          exp ((6/262144-1/2000 : ℝ)*N) := by rw [← exp_add]; congr 1; ring
      rw [← ht]
      ring
    _ ≤ _ := hg.trans_eq (by unfold sharedConstant; ring)

/-- Removing the now-paid cross pairs leaves exactly the complementary
signed cross cost plus its explicit shared-factor error. The adverse
cutoffs are still selected using the ORIGINAL whole funded prefix. -/
theorem shared_crossCost_split (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) :
    sqrt (max (adverseCrossEnergy X S w f) 0*adverseProfileEnergy X S w f) ≤
      sqrt (max (smallSharedEnergy X N S w f) 0*adverseProfileEnergy X S w f)+
        sqrt (|largeSharedEnergy X N S w f| *adverseProfileEnergy X S w f) := by
  let P := adverseProfileEnergy X S w f
  have hP : 0 ≤ P := Finset.sum_nonneg (fun _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hm : max (adverseCrossEnergy X S w f) 0 ≤
      max (smallSharedEnergy X N S w f) 0+|largeSharedEnergy X N S w f| := by
    apply max_le
    · rw [adverseCrossEnergy_eq X N S w f]
      linarith only [le_max_left (smallSharedEnergy X N S w f) 0,
        le_abs_self (largeSharedEnergy X N S w f)]
    · exact add_nonneg (le_max_right _ _) (abs_nonneg _)
  have hb := mul_le_mul_of_nonneg_right hm hP
  have hA : 0 ≤ max (smallSharedEnergy X N S w f) 0*P :=
    mul_nonneg (le_max_right _ _) hP
  have hB : 0 ≤ |largeSharedEnergy X N S w f| *P := mul_nonneg (abs_nonneg _) hP
  have hC : 0 ≤ max (adverseCrossEnergy X S w f) 0*P :=
    mul_nonneg (le_max_right _ _) hP
  apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
  rw [sq_sqrt hC]
  nlinarith only [hb,sq_sqrt hA,sq_sqrt hB,
    mul_nonneg (sqrt_nonneg (max (smallSharedEnergy X N S w f) 0*P))
      (sqrt_nonneg (|largeSharedEnergy X N S w f| *P))]

/-- Source-geometric price of every large shared-factor cross pair on
the actual corrected profile. No count, bin, phase or funding subcost is
introduced; all smaller-gcd correlations remain joined and signed. -/
theorem weighted_shared_price (X N : ℕ) (A S : Finset ℕ) (q : ℕ → ℝ) (y : ℝ)
    {B L u : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X) (hSF : ∀ n ∈ S,Squarefree n)
    (hlog : log X ≤ 3*((N : ℝ)+1)) (hq : ∀ n ∈ S,|q n| ≤ B) :
    let f := correctedProfile X L 1 0
    let w := fun n => u^(N+1)*q n*primeWeight A L y N n 1;
    sqrt (|largeSharedEnergy X N S w f| *adverseProfileEnergy X S w f) ≤ sharedPrice B N := by
  let f := correctedProfile X L 1 0
  let w := fun n => u^(N+1)*q n*primeWeight A L y N n 1
  have he := weighted_largeShared_bound X N A S f q y hB hL hu hU hX hS hSF hlog hq
  have hP : 0 ≤ adverseProfileEnergy X S w f := Finset.sum_nonneg (fun _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hp : adverseProfileEnergy X S w f ≤ 4*((N : ℝ)+1) := by
    have hs : ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f ⊆ activeCutoffs X f :=
      Finset.filter_subset _ _
    exact (Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))).trans
        ((corrected_profileEnergy_le X L).trans
          (by linarith only [hlog,Nat.cast_nonneg (α := ℝ) N]))
  have hC := sharedConstant_nonneg B
  have hprod := mul_le_mul he hp hP (show 0 ≤
    sharedConstant B*((N : ℝ)+1)^3*exp (-(1/4000 : ℝ)*N) by positivity)
  apply (sq_le_sq₀ (sqrt_nonneg _) (by unfold sharedPrice; positivity)).mp
  rw [sq_sqrt (mul_nonneg (abs_nonneg _) hP)]
  apply hprod.trans_eq
  unfold sharedPrice
  rw [mul_pow,mul_pow,sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC),
    ← exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show exp ((2 : ℝ)*(-(1/8000)*(N : ℝ)))=exp (-(1/4000)*(N : ℝ)) by congr 1; ring]
  ring

/-- This is a genuine new arithmetic payment across the actual cross
pairs, independent of their signs and every occupied-bin pattern. -/
theorem tendsto_sharedPrice (B : ℝ) :
    Tendsto (sharedPrice B) atTop (𝓝 0) := by
  have ht := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 2
    (exp_pos (-(1/8000 : ℝ))) (exp_lt_one_iff.mpr (by norm_num : -(1/8000 : ℝ) < 0))
  have hh := ht.const_mul (sqrt (4*sharedConstant B))
  simpa only [mul_zero] using hh.congr' (Eventually.of_forall fun N => by
    unfold sharedPrice
    rw [← exp_nat_mul]
    rw [show exp ((N : ℝ)*(-(1/8000)))=exp (-(1/8000)*(N : ℝ)) by congr 1; ring]
    ring)

/-- A shared actual cofactor qualifies regardless of its occupied bins
or the number of primes. This removes coherent owner fibres by sparsity,
not by an invalid assumption that their columns are orthogonal. -/
theorem common_cofactor_large {N p q a : ℕ} (hp : 0 < p) (ha : 0 < a)
    (hshare : (N : ℝ)/1000 < log a) :
    (N : ℝ)/1000 < log (Nat.gcd (p*a) (q*a)) := by
  have hg : a ∣ Nat.gcd (p*a) (q*a) := Nat.dvd_gcd (by simp) (by simp)
  have hgp : 0 < Nat.gcd (p*a) (q*a) := Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hp ha)
  exact hshare.trans_le (log_le_log (by exact_mod_cast ha)
    (by exact_mod_cast Nat.le_of_dvd hgp hg))

/-- The original radial window and actual paid owner crop put the
entire common cofactor well above the large-shared-factor cutoff. -/
theorem cropped_cofactor_large {N p a : ℕ} (hp : 0 < p) (ha : 0 < a)
    (hwin : p*a ∈ literalWindow N)
    (howner : log p < (60069/100000 : ℝ)*log (p*a : ℕ)) :
    (N : ℝ)/1000 < log a := by
  have ht := (mem_literalWindow N (p*a)).mp hwin
  have he : log (p*a : ℕ)=log p+log a := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast ha.ne')]
  rw [he] at ht howner
  nlinarith only [ht.1,howner,Nat.cast_nonneg (α := ℝ) N]

open ZetaRieszParityPacket ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint
open ZetaRieszRadialCompensation ZetaRieszBandCompensation
open ZetaRieszRejoinedPopulationFloor ZetaRieszJoinedPopulationFloor ZetaRieszFewBinCoverFloor
open ZetaRieszSevenCountTail ZetaRieszRejoinedPhaseFloor
open ZetaRieszLowCountRefund (tailCost)

/-- Native whole-floor comparison after geometrically paying ALL
large-gcd cross pairs. Original counts, bin masks, radial tail, credit
selectors, physical support, positive supply witness and debit remain.
The actual SMALLER-gcd signed cross cost is the still-open arithmetic
target; no independent estimate for it or whole numerical floor is assumed. -/
theorem eventually_joined_small_shared_floor {u y : ℝ} (hu : 1/2 < u)
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
            -sqrt (max (smallSharedEnergy X N (S.filter Squarefree) w f) 0*
              adverseProfileEnergy X (S.filter Squarefree) w f)-err j ≤
              ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  obtain ⟨h,c,κ,hh,hhu,hc,hκ,hbase⟩ := eventually_joined_cross_floor hu hU hy
  refine ⟨h,c,κ,hh,hhu,hc,hκ,?_⟩
  intro ε hε
  obtain ⟨err,he0,he,hfloor⟩ := hbase ε hε
  have hB : 0 ≤ 4+|ε| := by positivity
  refine ⟨fun j => err j+sharedPrice (4+|ε|) (dyadicMomentOrder j),?_,?_,?_⟩
  · intro j
    exact add_nonneg (he0 j) (by unfold sharedPrice; positivity)
  · simpa only [add_zero,Function.comp_def] using
      he.add ((tendsto_sharedPrice (4+|ε|)).comp tendsto_dyadicMomentOrder)
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
  have hprice := weighted_shared_price X N A (S.filter Squarefree)
    (rejoinedWeights H Paid Ts Ys a b (tailCost c N+ε+growingDebit κ N)) y
      hB hL1 (by linarith : 0 ≤ u) hU hX hSX
      (fun n hn => (Finset.mem_filter.mp hn).2)
      (window_sup_log S (hS.trans (ZetaRieszNonownerAllocation.coreBand_subset_literalWindow u N K))) hq'
  have hsplit := shared_crossCost_split X N (S.filter Squarefree) w f
  dsimp only [N,K,A,L,S₀,Paid,H,Ts,Ys,S,X,f,atom,a,b,w] at hprice hsplit
  dsimp only at hbound ⊢
  nlinarith only [hbound,hprice,hsplit]

end RiemannGaussian.ZetaRieszSharedFactorPayment
