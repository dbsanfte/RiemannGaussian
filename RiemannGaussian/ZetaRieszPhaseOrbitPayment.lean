/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPostHingeEnergy

/-!
# Sparse phase-period correlations in the actual joined energy

Close total-label phases may occur in different radial periods. Their
reciprocal neighbour capacity is nevertheless small. This module pays
an exponentially narrow union of ALL such periods, retaining the original
adverse cutoff selection and every signed funding overlap. The wider
phase-separated aggregate remains unpaid; no orthogonality is inferred.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszPhaseOrbitPayment
open ZetaRieszCofactorPhaseEnergy ZetaRieszDiagonalPayment
open ZetaRieszNearLabelPayment ZetaRieszSharedFactorPayment
open ZetaRieszJointPrimeEnergy ZetaRieszJointAllocation
open ZetaRieszSmoothOwnerDiscrepancy
open ZetaRieszWideOwnerAudit ZetaRieszCutoffPeriodFloor

/-- An actual finite log band, with its integer endpoints retained. -/
theorem log_band_reciprocal (S : Finset ℕ) {a ε l : ℝ}
    (hε : 0 ≤ ε) (hεu : ε ≤ 1/4)
    (hS : ∀ n ∈ S,0 < n ∧ exp l ≤ (n : ℝ)) :
    (∑ n ∈ S.filter (fun n : ℕ => |log n-a| ≤ ε),(n : ℝ)⁻¹) ≤
      4*ε+exp (-l) := by
  let T := S.filter (fun n : ℕ => |log n-a| ≤ ε)
  change (∑ n ∈ T,(n : ℝ)⁻¹) ≤ _
  rcases T.eq_empty_or_nonempty with he|he
  · rw [he,Finset.sum_empty]
    positivity
  let p : ℕ := T.min' he
  let q : ℕ := T.max' he
  have hp := Finset.min'_mem T he
  have hq := Finset.max'_mem T he
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (hS p (Finset.mem_filter.mp hp).1).1
  have hq0 : (0 : ℝ) < q := by
    exact_mod_cast (hS q (Finset.mem_filter.mp hq).1).1
  have hpq : p ≤ q := Finset.min'_le T q hq
  have hsub : T ⊆ Finset.Icc p q := fun n hn =>
    Finset.mem_Icc.mpr ⟨Finset.min'_le T n hn,Finset.le_max' T n hn⟩
  have hcard : (T.card : ℝ) ≤ (q : ℝ)-p+1 := by
    have h := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h
    have hnat : T.card ≤ q-p+1 := by omega
    have hc : (T.card : ℝ) ≤ ((q-p+1 : ℕ) : ℝ) := by exact_mod_cast hnat
    simpa only [Nat.cast_add,Nat.cast_sub hpq,Nat.cast_one] using hc
  have hr : (q : ℝ)/(p : ℝ) ≤ exp (2*ε) := by
    have hpl := (Finset.mem_filter.mp hp).2
    have hql := (Finset.mem_filter.mp hq).2
    have hl : log q-log p ≤ 2*ε := by
      linarith only [le_abs_self (log q-a),neg_le_abs (log p-a),hpl,hql]
    have h := exp_le_exp.mpr hl
    rwa [exp_sub,exp_log hq0,exp_log hp0] at h
  have hi : (p : ℝ)⁻¹ ≤ exp (-l) := by
    have h := (hS p (Finset.mem_filter.mp hp).1).2
    simpa only [exp_neg] using (inv_le_inv₀ hp0 (exp_pos l)).mpr h
  have hex : exp (2*ε)-1 ≤ 4*ε := by
    have he := exp_bound_div_one_sub_of_interval (by linarith : 0 ≤ 2*ε)
      (by linarith : 2*ε < 1)
    have hd : 0 < 1-2*ε := by linarith
    have hu : 1/(1-2*ε) ≤ 1+4*ε := by
      apply (div_le_iff₀ hd).mpr
      nlinarith only [hε,hεu]
    linarith only [he,hu]
  calc
    _ ≤ ∑ _n ∈ T,(p : ℝ)⁻¹ := Finset.sum_le_sum (fun n hn =>
      (inv_le_inv₀ (by exact_mod_cast (hS n (Finset.mem_filter.mp hn).1).1) hp0).mpr
        (by exact_mod_cast Finset.min'_le T n hn))
    _ = (T.card : ℝ)/(p : ℝ) := by simp [div_eq_mul_inv]
    _ ≤ ((q : ℝ)-p+1)/(p : ℝ) :=
      div_le_div_of_nonneg_right hcard hp0.le
    _ = (q : ℝ)/(p : ℝ)-1+(p : ℝ)⁻¹ := by field_simp
    _ ≤ exp (2*ε)-1+exp (-l) := by linarith only [hr,hi]
    _ ≤ _ := by linarith only [hex]

/-- A union of logarithmic neighbourhoods; no continuum labels enter. -/
def logNear (P : Finset ℝ) (ε : ℝ) (n m : ℕ) : Prop :=
  ∃ a ∈ P,|log n-log m-a| ≤ ε

theorem logNear_symm (P : Finset ℝ) (hP : ∀ a ∈ P,-a ∈ P)
    (ε : ℝ) (n m : ℕ) : logNear P ε n m ↔ logNear P ε m n := by
  have h (n m : ℕ) : logNear P ε n m → logNear P ε m n := by
    rintro ⟨a,ha,he⟩
    refine ⟨-a,hP a ha,?_⟩
    rwa [show log m-log n- -a=-(log n-log m-a) by ring,abs_neg]
  exact ⟨h n m,h m n⟩

/-- Reciprocal capacity does not grow with the multiplicative distance
between radial periods. Its integer endpoint error is explicit. -/
theorem logNear_row_capacity (P : Finset ℝ) (S : Finset ℕ) (n : ℕ)
    {ε l : ℝ} (hε : 0 ≤ ε) (hεu : ε ≤ 1/4)
    (hS : ∀ m ∈ S,0 < m ∧ exp l ≤ (m : ℝ)) :
    (∑ m ∈ S,if logNear P ε n m then (m : ℝ)⁻¹ else 0) ≤
      (P.card : ℝ)*(4*ε+exp (-l)) := by
  calc
    _ ≤ ∑ m ∈ S,∑ a ∈ P,
        if |log m-(log n-a)| ≤ ε then (m : ℝ)⁻¹ else 0 := by
      apply Finset.sum_le_sum
      intro m _
      split_ifs with hm
      · obtain ⟨a,ha,he⟩ := hm
        have he' : |log m-(log n-a)| ≤ ε := by
          rwa [show log m-(log n-a)=-(log n-log m-a) by ring,abs_neg]
        have hh := Finset.single_le_sum (s := P)
          (f := fun a : ℝ => if |log m-(log n-a)| ≤ ε then (m : ℝ)⁻¹ else 0)
          (fun _ _ => by split_ifs <;> positivity) ha
        simpa only [if_pos he'] using hh
      · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
    _ = ∑ a ∈ P,∑ m ∈ S.filter (fun m : ℕ => |log m-(log n-a)| ≤ ε),(m : ℝ)⁻¹ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ ∑ _a ∈ P,(4*ε+exp (-l)) := Finset.sum_le_sum
      (fun _ _ => log_band_reciprocal S hε hεu hS)
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]

/-- Weighted symmetric incidence retains the natural reciprocal row
mass. A raw neighbour cardinality would lose the large period ratios. -/
theorem symmetric_reciprocal_capacity (S : Finset ℕ) (E : ℕ → ℕ → Prop)
    [DecidableRel E] (hE : ∀ n m,E n m ↔ E m n) (a : ℕ → ℝ) :
    (∑ n ∈ S,∑ m ∈ S,if E n m then
      (a n/(n : ℝ))*(a m/(m : ℝ)) else 0) ≤
      ∑ n ∈ S,((a n)^2/(n : ℝ))*
        (∑ m ∈ S,if E n m then (m : ℝ)⁻¹ else 0) := by
  let D := ∑ n ∈ S,((a n)^2/(n : ℝ))*
    (∑ m ∈ S,if E n m then (m : ℝ)⁻¹ else 0)
  have hfirst : (∑ n ∈ S,∑ m ∈ S,
      if E n m then (a n)^2/(n : ℝ)/(m : ℝ) else 0)=D := by
    simp only [D,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro m _
    split_ifs <;> simp [div_eq_mul_inv]
  have hsecond : (∑ n ∈ S,∑ m ∈ S,
      if E n m then (a m)^2/(m : ℝ)/(n : ℝ) else 0)=D := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ m ∈ S,∑ n ∈ S,if E m n then (a m)^2/(m : ℝ)/(n : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro m _
        exact Finset.sum_congr rfl (fun n _ => by simp only [hE n m])
      _ = D := hfirst
  have h : 2*(∑ n ∈ S,∑ m ∈ S,if E n m then
      (a n/(n : ℝ))*(a m/(m : ℝ)) else 0) ≤
      (∑ n ∈ S,∑ m ∈ S,if E n m then (a n)^2/(n : ℝ)/(m : ℝ) else 0)+
      (∑ n ∈ S,∑ m ∈ S,if E n m then (a m)^2/(m : ℝ)/(n : ℝ) else 0) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n _
    apply Finset.sum_le_sum
    intro m _
    split_ifs
    · have hh := mul_le_mul_of_nonneg_right
        (show 2*a n*a m ≤ (a n)^2+(a m)^2 by nlinarith only [sq_nonneg (a n-a m)])
        (show 0 ≤ (n : ℝ)⁻¹*(m : ℝ)⁻¹ by positivity)
      convert hh using 1 <;> simp only [div_eq_mul_inv] <;> ring
    · simp
  rw [hfirst,hsecond] at h
  linarith only [h]

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


/-- All signed labels may be used; only the sparse edge family is
bounded absolutely. No count-wise norm or density approximation enters. -/
theorem logNear_pair_mass_bound (X : ℕ) (S : Finset ℕ) (P : Finset ℝ)
    (hX : S ⊆ Finset.Icc 1 X) (hP : ∀ a ∈ P,-a ∈ P)
    {ε l : ℝ} (hε : 0 ≤ ε) (hεu : ε ≤ 1/4)
    (hS : ∀ n ∈ S,exp l ≤ (n : ℝ)) :
    (∑ n ∈ S,∑ m ∈ S,if logNear P ε n m then
      ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) ≤
      ((P.card : ℝ)*(4*ε+exp (-l)))*
        (exp (log X/262144)*divisorSquareDirichletMass (1+1/262144)) := by
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
    _ ≤ _ := mul_le_mul_of_nonneg_left (divisor_square_harmonic X S hX) (by positivity)

/-- A finite bound covering every phase period on the original core. -/
def phaseRadius (y : ℝ) (N : ℕ) : ℕ := 4*(⌈|y|⌉₊+1)*(N+1)

/-- Genuine total-log phase shifts; these are not prime mode coordinates. -/
def phaseOffsets (y : ℝ) (N : ℕ) : Finset ℝ :=
  (Finset.Icc (-(phaseRadius y N : ℤ)) (phaseRadius y N : ℤ)).image
    (fun k : ℤ => 2*Real.pi*(k : ℝ)/y)

/-- Dependence on the FIXED phase height is explicit. -/
def phaseCount (y : ℝ) : ℝ := 8*(⌈|y|⌉₊+1 : ℕ)+1

/-- The shrinking width is in log space and retains the actual height. -/
def phaseWidth (y : ℝ) (N : ℕ) : ℝ := exp (-(N : ℝ)/1000)/(1+|y|)

theorem phaseOffsets_symm (y : ℝ) (N : ℕ) :
    ∀ a ∈ phaseOffsets y N,-a ∈ phaseOffsets y N := by
  rintro a ha
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp ha
  refine Finset.mem_image.mpr ⟨-k,Finset.mem_Icc.mpr ?_,?_⟩
  · obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hk
    constructor <;> omega
  · push_cast
    ring

theorem phaseOffsets_card_le (y : ℝ) (N : ℕ) :
    ((phaseOffsets y N).card : ℝ) ≤ phaseCount y*((N : ℝ)+1) := by
  have hh := Finset.card_image_le
    (s := Finset.Icc (-(phaseRadius y N : ℤ)) (phaseRadius y N : ℤ))
    (f := fun k : ℤ => 2*Real.pi*(k : ℝ)/y)
  have hcard : (phaseOffsets y N).card ≤ 2*phaseRadius y N+1 := by
    unfold phaseOffsets
    rw [Int.card_Icc] at hh
    change _ ≤ _ at hh
    omega
  have h : ((phaseOffsets y N).card : ℝ) ≤ (2*phaseRadius y N+1 : ℕ) := by
    exact_mod_cast hcard
  unfold phaseCount
  simp only [phaseRadius,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at h ⊢
  nlinarith only [h,Nat.cast_nonneg (α := ℝ) N]

theorem phaseWidth_bounds {y : ℝ} (hy : 3 ≤ |y|) (N : ℕ) :
    0 ≤ phaseWidth y N ∧ phaseWidth y N ≤ 1/4 ∧
      phaseWidth y N ≤ exp (-(N : ℝ)/1000) := by
  have hd : 0 < 1+|y| := by positivity
  have he : exp (-(N : ℝ)/1000) ≤ 1 :=
    exp_le_one_iff.mpr (by linarith only [Nat.cast_nonneg (α := ℝ) N])
  unfold phaseWidth
  refine ⟨by positivity,?_,?_⟩
  · apply (div_le_iff₀ hd).mpr
    linarith only [he,hy]
  · exact div_le_self (exp_pos _).le (by linarith only [abs_nonneg y])

/-- The complete period union is sparse even when its members lie far
apart as integers. All actual total-label phases and counts are allowed. -/
theorem phase_pair_mass_bound (X N : ℕ) (S : Finset ℕ) {y : ℝ}
    (hy : 3 ≤ |y|) (hX : S ⊆ Finset.Icc 1 X) (hS : S ⊆ literalWindow N) :
    (∑ n ∈ S,∑ m ∈ S,if logNear (phaseOffsets y N) (phaseWidth y N) n m then
      ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) ≤
      5*phaseCount y*((N : ℝ)+1)*exp (-(N : ℝ)/1000)*
        exp (log X/262144)*divisorSquareDirichletMass (1+1/262144) := by
  have hl n (hn : n ∈ S) : exp ((7/4 : ℝ)*N) ≤ (n : ℝ) := by
    have hp : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp (hX hn)).1
    have hh := ((mem_literalWindow N n).mp (hS hn)).1
    exact (exp_le_exp.mpr hh.le).trans_eq (exp_log hp)
  obtain ⟨he0,he,hew⟩ := phaseWidth_bounds hy N
  have hb := logNear_pair_mass_bound X S (phaseOffsets y N) hX
    (phaseOffsets_symm y N) he0 he hl
  have hi : exp (-((7/4 : ℝ)*N)) ≤ exp (-(N : ℝ)/1000) :=
    exp_le_exp.mpr (by nlinarith only [Nat.cast_nonneg (α := ℝ) N])
  have hh : 4*phaseWidth y N+exp (-((7/4 : ℝ)*N)) ≤
      5*exp (-(N : ℝ)/1000) := by linarith only [hew,hi]
  have hprod := mul_le_mul (phaseOffsets_card_le y N) hh (by positivity)
    (show 0 ≤ phaseCount y*((N : ℝ)+1) by unfold phaseCount; positivity)
  exact hb.trans ((mul_le_mul_of_nonneg_right hprod
    (by positivity [divisorSquareDirichletMass_nonneg (1+1/262144)])).trans_eq (by ring))

/-- No actual phase period inside the literal finite label range is
omitted by the canonical finite union. The phase tolerance is exact. -/
theorem phaseNear_of_resonance {X N n m : ℕ} {y ε : ℝ} (hy : 1 ≤ y)
    (hεu : ε ≤ 1)
    (hn : n ∈ Finset.Icc 1 X) (hm : m ∈ Finset.Icc 1 X)
    (hX : log X ≤ 3*((N : ℝ)+1)) {k : ℤ}
    (hk : |y*(log n-log m)-2*Real.pi*(k : ℝ)| ≤ y*ε) :
    logNear (phaseOffsets y N) ε n m := by
  have hy0 : 0 < y := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hnX : log n ≤ log X := log_le_log hn0
    (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
  have hmX : log m ≤ log X := log_le_log hm0
    (by exact_mod_cast (Finset.mem_Icc.mp hm).2)
  have hdiff : |log n-log m| ≤ 3*((N : ℝ)+1) := by
    rw [abs_le]
    constructor <;> linarith only [hnX,hmX,hX,log_natCast_nonneg n,log_natCast_nonneg m]
  have hY : y ≤ (⌈|y|⌉₊+1 : ℕ) := by
    have hh := Nat.le_ceil |y|
    push_cast
    linarith only [hh,le_abs_self y]
  have ht : |2*Real.pi*(k : ℝ)| ≤ y*ε+y*(3*((N : ℝ)+1)) := by
    have hh := abs_sub_le (2*Real.pi*(k : ℝ)) (y*(log n-log m)) 0
    simp only [sub_zero] at hh
    rw [abs_sub_comm (2*Real.pi*(k : ℝ)),
      abs_mul y,abs_of_pos hy0] at hh
    linarith only [hh,hk,mul_le_mul_of_nonneg_left hdiff hy0.le]
  have hp : 1 ≤ 2*Real.pi := by linarith only [Real.pi_gt_three]
  have ht' : |(k : ℝ)| ≤ y*(4*((N : ℝ)+1)) := by
    rw [abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)] at ht
    have hh := mul_le_mul_of_nonneg_left hεu hy0.le
    have hlo := le_mul_of_one_le_left (abs_nonneg (k : ℝ)) hp
    linarith only [ht,hh,hlo,mul_nonneg hy0.le (Nat.cast_nonneg (α := ℝ) N)]
  have hkQ : |(k : ℝ)| ≤ (phaseRadius y N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hY (show 0 ≤ 4*((N : ℝ)+1) by positivity)
    apply ht'.trans
    simpa only [phaseRadius,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,mul_comm,mul_left_comm] using hh
  have hki : k ∈ Finset.Icc (-(phaseRadius y N : ℤ)) (phaseRadius y N : ℤ) := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp hkQ
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hlo,by exact_mod_cast hhi⟩
  refine ⟨2*Real.pi*(k : ℝ)/y,Finset.mem_image.mpr ⟨k,hki,rfl⟩,?_⟩
  have he : log n-log m-2*Real.pi*(k : ℝ)/y=
      (y*(log n-log m)-2*Real.pi*(k : ℝ))/y := by field_simp
  rw [he,abs_div,abs_of_pos hy0]
  exact (div_le_iff₀ hy0).mpr (by linarith only [hk])

/-- The newly paid phase-period pairs ONLY inside the original residual
cross population. Its adverse cutoffs are never reselected. -/
def orbitEnergy (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ k ∈ ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f,
    (∑ n ∈ S,∑ m ∈ S.erase n,
      if (N : ℝ)/1000 < log (Nat.gcd n m) then 0 else
        if nearPair (exp (-(N : ℝ)/1000)) n m then 0 else
          if logNear (phaseOffsets y N) (phaseWidth y N) n m then
            (w n*sharp k n)*(w m*sharp k m) else 0)/(k : ℝ)

/-- Every unaligned pair remains SIGNED in the same global aggregate. -/
def nonOrbitEnergy (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ k ∈ ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f,
    (∑ n ∈ S,∑ m ∈ S.erase n,
      if (N : ℝ)/1000 < log (Nat.gcd n m) then 0 else
        if nearPair (exp (-(N : ℝ)/1000)) n m then 0 else
          if logNear (phaseOffsets y N) (phaseWidth y N) n m then 0 else
            (w n*sharp k n)*(w m*sharp k m))/(k : ℝ)

/-- One exact partition of the existing residual, with no new credits. -/
theorem separatedEnergy_eq (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (y : ℝ) :
    separatedEnergy X N S w f = orbitEnergy X N S w f y+nonOrbitEnergy X N S w f y := by
  simp only [separatedEnergy,orbitEnergy,nonOrbitEnergy,
    ← Finset.sum_add_distrib,← add_div]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  split_ifs <;> simp

/-- An absolute bound ONLY on the sparse, already isolated phase edges. -/
theorem orbitEnergy_bound (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (y : ℝ)
    (hy : 3 ≤ |y|) (hwin : S ⊆ literalWindow N)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X)
    {V : ℝ} (hV : 0 ≤ V) (hw : ∀ n ∈ S,|w n| ≤ V/(n : ℝ)) :
    |orbitEnergy X N S w f y| ≤
      (1+log X)*V^2*(5*phaseCount y*((N : ℝ)+1)*exp (-(N : ℝ)/1000)*exp (log X/262144)*
        divisorSquareDirichletMass (1+1/262144)) := by
  let ε := phaseWidth y N
  let P := ∑ n ∈ S,∑ m ∈ S,if logNear (phaseOffsets y N) ε n m then
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
          if nearPair (exp (-(N : ℝ)/1000)) n m then 0 else
            if logNear (phaseOffsets y N) ε n m then (w n*sharp k n)*(w m*sharp k m) else 0| ≤
        V^2*(if logNear (phaseOffsets y N) ε n m then
          ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) := by
    split_ifs
    all_goals first
      | solve | simp only [abs_zero]; positivity
      | solve | rw [abs_mul]; exact (mul_le_mul (hs n hn k) (hs m hm k) (abs_nonneg _)
          (by positivity)).trans_eq (by ring)
  have hrow k : |∑ n ∈ S,∑ m ∈ S.erase n,
      if (N : ℝ)/1000 < log (Nat.gcd n m) then 0 else
        if nearPair (exp (-(N : ℝ)/1000)) n m then 0 else
            if logNear (phaseOffsets y N) ε n m then (w n*sharp k n)*(w m*sharp k m) else 0| ≤ V^2*P := by
    calc
      _ ≤ ∑ n ∈ S,|∑ m ∈ S.erase n,
          if (N : ℝ)/1000 < log (Nat.gcd n m) then 0 else
            if nearPair (exp (-(N : ℝ)/1000)) n m then 0 else
            if logNear (phaseOffsets y N) ε n m then (w n*sharp k n)*(w m*sharp k m) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ S,∑ m ∈ S.erase n,
          |if (N : ℝ)/1000 < log (Nat.gcd n m) then 0 else
            if nearPair (exp (-(N : ℝ)/1000)) n m then 0 else
            if logNear (phaseOffsets y N) ε n m then (w n*sharp k n)*(w m*sharp k m) else 0| :=
        Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ n ∈ S,∑ m ∈ S.erase n,V^2*(if logNear (phaseOffsets y N) ε n m then
          ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) :=
        Finset.sum_le_sum (fun n hn => Finset.sum_le_sum
          (fun m hm => hterm n hn m (Finset.mem_of_mem_erase hm) k))
      _ ≤ ∑ n ∈ S,∑ m ∈ S,V^2*(if logNear (phaseOffsets y N) ε n m then
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
  have hmass := phase_pair_mass_bound X N S hy hS hwin
  have hlog : 0 ≤ 1+log X := by
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
    linarith [log_nonneg hX1]
  calc
    _ ≤ ∑ k ∈ K,|∑ n ∈ S,∑ m ∈ S.erase n,
        if (N : ℝ)/1000 < log (Nat.gcd n m) then 0 else
          if nearPair (exp (-(N : ℝ)/1000)) n m then 0 else
            if logNear (phaseOffsets y N) ε n m then (w n*sharp k n)*(w m*sharp k m) else 0|/(k : ℝ) := by
      have ha (k : ℕ) : |(k : ℝ)|=(k : ℝ) := abs_of_nonneg (Nat.cast_nonneg k)
      simpa only [orbitEnergy,ε,abs_div,ha] using
        Finset.abs_sum_le_sum_abs (s := K)
          (fun k : ℕ => (∑ n ∈ S,∑ m ∈ S.erase n,
            if (N : ℝ)/1000 < log (Nat.gcd n m) then 0 else
              if nearPair (exp (-(N : ℝ)/1000)) n m then 0 else
            if logNear (phaseOffsets y N) ε n m then (w n*sharp k n)*(w m*sharp k m) else 0)/(k : ℝ))
    _ ≤ ∑ k ∈ K,(V^2*P)/(k : ℝ) := Finset.sum_le_sum
      (fun k _ => div_le_div_of_nonneg_right (hrow k) (Nat.cast_nonneg k))
    _ = (∑ k ∈ K,(k : ℝ)⁻¹)*(V^2*P) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ (1+log X)*(V^2*P) := mul_le_mul_of_nonneg_right hh (mul_nonneg (sq_nonneg V) hP)
    _ ≤ (1+log X)*V^2*(5*phaseCount y*((N : ℝ)+1)*exp (-(N : ℝ)/1000)*exp (log X/262144)*
        divisorSquareDirichletMass (1+1/262144)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmass
        (mul_nonneg hlog (sq_nonneg V))


/-- A fixed finite arithmetic constant; its height dependence is retained.
No numerical value or effective floor start is asserted. -/
def orbitConstant (B y : ℝ) : ℝ :=
  80*radiusCeiling^2*B^2*phaseCount y*
    divisorSquareDirichletMass (1+1/262144)*exp (3/262144)

/-- This prices only the isolated period-alignment edges. -/
def orbitPrice (B y : ℝ) (N : ℕ) : ℝ :=
  sqrt (4*orbitConstant B y)*((N : ℝ)+1)^3*exp (-(1/4000 : ℝ)*N)

private theorem orbitConstant_nonneg (B y : ℝ) : 0 ≤ orbitConstant B y := by
  unfold orbitConstant phaseCount
  positivity [divisorSquareDirichletMass_nonneg (1+1/262144)]

/-- The shrinking phase-band capacity beats the ACTUAL squared source
growth across all original prime counts, radial periods and weights. -/
theorem weighted_orbitEnergy_bound (X N : ℕ) (A S : Finset ℕ) (f q : ℕ → ℝ) (y : ℝ)
    (hy : 3 ≤ |y|) (hwin : S ⊆ literalWindow N)
    {B L u : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X)
    (hlog : log X ≤ 3*((N : ℝ)+1)) (hq : ∀ n ∈ S,|q n| ≤ B) :
    |orbitEnergy X N S (fun n => u^(N+1)*q n*primeWeight A L y N n 1) f y| ≤
      orbitConstant B y*((N : ℝ)+1)^4*exp (-(1/2000 : ℝ)*N) := by
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
  have hb := orbitEnergy_bound X N S _ f y hy hwin hX hS hV hw
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
  have hQ : 0 ≤ V^2*(5*phaseCount y*((N : ℝ)+1)*exp (-(N : ℝ)/1000))*divisorSquareDirichletMass (1+1/262144) := by
    positivity [divisorSquareDirichletMass_nonneg (1+1/262144),show 0 ≤ phaseCount y by unfold phaseCount; positivity]
  have hc := mul_le_mul_of_nonneg_right hprod hQ
  have hg := mul_le_mul_of_nonneg_left (near_source_rate hu hU N)
    (show 0 ≤ 20*B^2*phaseCount y*((N : ℝ)+1)^4*divisorSquareDirichletMass (1+1/262144)*exp (3/262144) by
      positivity [divisorSquareDirichletMass_nonneg (1+1/262144),show 0 ≤ phaseCount y by unfold phaseCount; positivity])
  calc
    _ ≤ (1+log X)*V^2*(5*phaseCount y*((N : ℝ)+1)*exp (-(N : ℝ)/1000)*exp (log X/262144)*
        divisorSquareDirichletMass (1+1/262144)) := hb
    _ = ((1+log X)*exp (log X/262144))*
        (V^2*(5*phaseCount y*((N : ℝ)+1)*exp (-(N : ℝ)/1000))*divisorSquareDirichletMass (1+1/262144)) := by ring
    _ ≤ (4*((N : ℝ)+1)*(exp (3/262144)*exp ((3/262144 : ℝ)*N)))*
        (V^2*(5*phaseCount y*((N : ℝ)+1)*exp (-(N : ℝ)/1000))*divisorSquareDirichletMass (1+1/262144)) := hc
    _ = (20*B^2*phaseCount y*((N : ℝ)+1)^4*divisorSquareDirichletMass (1+1/262144)*exp (3/262144))*
        ((2*u)^(2*(N+1))*exp ((3/262144-1/1000 : ℝ)*N)) := by
      rw [hvpow]
      have ht : exp ((3/262144 : ℝ)*N)*exp (-(N : ℝ)/1000)=
          exp ((3/262144-1/1000 : ℝ)*N) := by rw [← exp_add]; congr 1; ring
      rw [← ht]
      ring
    _ ≤ _ := hg.trans_eq (by unfold orbitConstant; ring)


/-- Split the SAME whole price; no adverse cutoffs are reselected. -/
theorem orbit_crossCost_split (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (y : ℝ)
    {P : ℝ} (hP : 0 ≤ P) :
    sqrt (max (separatedEnergy X N S w f) 0*P) ≤
      sqrt (max (nonOrbitEnergy X N S w f y) 0*P)+
        sqrt (|orbitEnergy X N S w f y| *P) := by
  have hb : max (separatedEnergy X N S w f) 0 ≤
      max (nonOrbitEnergy X N S w f y) 0+|orbitEnergy X N S w f y| := by
    rw [separatedEnergy_eq X N S w f y]
    apply max_le
    · linarith only [le_max_left (nonOrbitEnergy X N S w f y) 0,
        le_abs_self (orbitEnergy X N S w f y)]
    · positivity
  have hm := mul_le_mul_of_nonneg_right hb hP
  have ha : 0 ≤ max (separatedEnergy X N S w f) 0*P := by positivity
  have hc : 0 ≤ max (nonOrbitEnergy X N S w f y) 0*P := by positivity
  have he : 0 ≤ |orbitEnergy X N S w f y| *P := by positivity
  apply (sq_le_sq₀ (sqrt_nonneg _)
    (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _))).mp
  nlinarith only [hm,sq_sqrt ha,sq_sqrt hc,sq_sqrt he,
    mul_nonneg (sqrt_nonneg (max (nonOrbitEnergy X N S w f y) 0*P))
      (sqrt_nonneg (|orbitEnergy X N S w f y| *P))]

/-- The explicit source-geometric price also covers the actual
post-hinge cap. It assumes no bound on the unpaid remainder energy. -/
theorem weighted_orbit_price (X N : ℕ) (A S : Finset ℕ) (f q : ℕ → ℝ) (y : ℝ)
    (hy : 3 ≤ |y|) (hwin : S ⊆ literalWindow N)
    {B L u P : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X)
    (hlog : log X ≤ 3*((N : ℝ)+1)) (hq : ∀ n ∈ S,|q n| ≤ B)
    (hP : 0 ≤ P) (hPu : P ≤ 4*((N : ℝ)+1)^2) :
    sqrt (|orbitEnergy X N S (fun n => u^(N+1)*q n*primeWeight A L y N n 1) f y| *P) ≤
      orbitPrice B y N := by
  have he := weighted_orbitEnergy_bound X N A S f q y hy hwin hB hL hu hU hX hS hlog hq
  have hC := orbitConstant_nonneg B y
  have hprod := mul_le_mul he hPu hP
    (show 0 ≤ orbitConstant B y*((N : ℝ)+1)^4*exp (-(1/2000 : ℝ)*N) by positivity)
  apply (sq_le_sq₀ (sqrt_nonneg _) (by unfold orbitPrice; positivity)).mp
  rw [sq_sqrt (mul_nonneg (abs_nonneg _) hP)]
  apply hprod.trans_eq
  unfold orbitPrice
  rw [mul_pow,mul_pow,sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC),← exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show exp ((2 : ℝ)*(-(1/4000)*(N : ℝ)))=exp (-(1/2000)*(N : ℝ)) by congr 1; ring]
  ring

/-- Fixed-height phase-period alignment costs source-o(1), with no
bin-occupancy or fixed-count orthogonality premise. -/
theorem tendsto_orbitPrice (B y : ℝ) : Tendsto (orbitPrice B y) atTop (𝓝 0) := by
  have ht := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 3
    (exp_pos (-(1/4000 : ℝ))) (exp_lt_one_iff.mpr (by norm_num : -(1/4000 : ℝ) < 0))
  have hh := ht.const_mul (sqrt (4*orbitConstant B y))
  simpa only [mul_zero] using hh.congr' (Eventually.of_forall fun N => by
    unfold orbitPrice
    rw [← exp_nat_mul]
    rw [show exp ((N : ℝ)*(-(1/4000)))=exp (-(1/4000)*(N : ℝ)) by congr 1; ring]
    ring)

open ZetaRieszParityPacket ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint
open ZetaRieszRadialCompensation ZetaRieszBandCompensation
open ZetaRieszRejoinedPopulationFloor ZetaRieszJoinedPopulationFloor ZetaRieszFewBinCoverFloor
open ZetaRieszSevenCountTail ZetaRieszRejoinedPhaseFloor
open ZetaRieszLowCountRefund (tailCost)

/-- The new geometric phase-period price is spent ONCE on the original
whole funded floor. Diagonal/shared/near prices and every original overlap
remain. The unaligned aggregate still needs its independent bound; this
does not prove the final numerical floor. -/
theorem eventually_joined_nonOrbit_floor {u y : ℝ} (hu : 1/2 < u)
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
            -sqrt (max (nonOrbitEnergy X N (S.filter Squarefree) w f y) 0*
              ((129/200 : ℝ)*N))-err j ≤
              ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  obtain ⟨h,c,κ,hh,hhu,hc,hκ,hbase⟩ := ZetaRieszPostHingeEnergy.eventually_joined_calibrated_floor hu hU hy
  refine ⟨h,c,κ,hh,hhu,hc,hκ,?_⟩
  intro ε hε
  obtain ⟨err,he0,he,hfloor⟩ := hbase ε hε
  have hB : 0 ≤ 4+|ε| := by positivity
  refine ⟨fun j => err j+orbitPrice (4+|ε|) y (dyadicMomentOrder j),?_,?_,?_⟩
  · intro j
    exact add_nonneg (he0 j) (by unfold orbitPrice; positivity)
  · simpa only [add_zero,Function.comp_def] using
      he.add ((tendsto_orbitPrice (4+|ε|) y).comp tendsto_dyadicMomentOrder)
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
  have hwin : S.filter Squarefree ⊆ literalWindow N :=
    (Finset.filter_subset _ _).trans
      (hS.trans (ZetaRieszNonownerAllocation.coreBand_subset_literalWindow u N K))
  have hphase : 3 ≤ |y| := by linarith only [hy,le_abs_self y]
  have hcap : (129/200 : ℝ)*N ≤ 4*((N : ℝ)+1)^2 := by
    nlinarith only [Nat.cast_nonneg (α := ℝ) N,sq_nonneg (N : ℝ)]
  have hprice := weighted_orbit_price X N A (S.filter Squarefree) f
    (rejoinedWeights H Paid Ts Ys a b (tailCost c N+ε+growingDebit κ N)) y
      hphase hwin hB hL1 (by linarith : 0 ≤ u) hU hX hSX
      (window_sup_log S (hS.trans (ZetaRieszNonownerAllocation.coreBand_subset_literalWindow u N K))) hq'
      (show 0 ≤ (129/200 : ℝ)*N by positivity) hcap
  have hsplit := orbit_crossCost_split X N (S.filter Squarefree) w f y
    (P := (129/200 : ℝ)*N) (by positivity)
  change -sqrt (((129/200 : ℝ)*N)*max (separatedEnergy X N (S.filter Squarefree) w f) 0)-err j ≤
    ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re at hbound
  rw [mul_comm ((129/200 : ℝ)*N)] at hbound
  change -sqrt (max (nonOrbitEnergy X N (S.filter Squarefree) w f y) 0*((129/200 : ℝ)*N))-
    (err j+orbitPrice (4+|ε|) y N) ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re
  nlinarith only [hbound,hprice,hsplit]

end RiemannGaussian.ZetaRieszPhaseOrbitPayment
