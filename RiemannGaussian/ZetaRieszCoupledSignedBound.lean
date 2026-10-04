/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointSecondDifference
import RiemannGaussian.ZetaRieszSelbergMaskCancellation

/-!
# A signed bound after joining both native factorial degrees

Align the adjacent cofactor orders before estimating. The resulting signed
coefficient is reflected before its energy is formed; the opposite-sign
correlation credit stays negative. Only the adjacent-order discrepancy and
the previously paid whole-mask/square errors receive norm budgets.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCoupledSignedBound
open ZetaRieszFactorialCutoff ZetaRieszPairPrefixConvolution
open ZetaRieszPairPrimePowerPayment ZetaRieszSelbergSourceAudit

/-- All positive slots, with the central integer cutoff retained. -/
def positiveWeight (N K i : ℕ) : ℝ :=
  1/(N : ℝ)+(if K ≤ i ∧ i < N-K then 1/((N-i : ℕ) : ℝ) else 0)

/-- The literal successor prefix at the same native order. -/
def successorWeight (N K i : ℕ) : ℝ :=
  if i ≤ N-K then 1/((N+1-i : ℕ) : ℝ) else 0

/-- The exact moving length normalization, not its asymptotic value. -/
def lengthFactor (u : ℝ) (N : ℕ) : ℝ :=
  (N+1 : ℕ)/(u*SquarefreeVaughanLogSource.length u N)

/-- Cancellation between adjacent degrees occurs inside this coefficient. -/
def joinedWeight (N K : ℕ) (b : ℝ) (i : ℕ) : ℝ :=
  positiveWeight N K i-b*successorWeight N K i

/-- Swapped incidences are joined before the coefficient is priced. -/
def symmetricWeight (N K : ℕ) (b : ℝ) (i : ℕ) : ℝ :=
  (joinedWeight N K b i+joinedWeight N K b (N-1-i))/2

/-- One exact adjacent-order error, with its original complex correlation. -/
def advanceError (a : ℕ → ℂ) (N K : ℕ) (b : ℝ) : ℂ :=
  (b : ℂ)*∑ i∈Finset.range N, (successorWeight N K i : ℂ)*a i*
    (a (N-1-i)-a (N-i))

/-- A norm allowance only for the adjacent-order discrepancy. -/
def advancePrice (a : ℕ → ℂ) (N K : ℕ) (b : ℝ) : ℝ :=
  |b| * ∑ i∈Finset.range N, successorWeight N K i*‖a i‖*
    ‖a (N-1-i)-a (N-i)‖

private theorem central_reindex (a : ℕ → ℂ) {N K : ℕ} (hK : 0 < K)
    (hKN : 2*K ≤ N) :
    (∑ k∈centralOrders (N+1) K,
      a (k-1)*a (N-k)/((N+1-k : ℕ) : ℂ))=
    ∑ i∈(Finset.range N).filter (fun i => K ≤ i ∧ i < N-K),
      a i*a (N-1-i)/((N-i : ℕ) : ℂ) := by
  apply Finset.sum_bij (fun k _ => k-1)
  · intro k hk
    simp only [centralOrders,Finset.mem_filter,Finset.mem_range] at hk
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  · intro k hk j hj he
    simp only [centralOrders,Finset.mem_filter,Finset.mem_range] at hk hj
    omega
  · intro i hi
    simp only [Finset.mem_filter,Finset.mem_range] at hi
    refine ⟨i+1,?_,by omega⟩
    simp only [centralOrders,Finset.mem_filter,Finset.mem_range]
    omega
  · intro k hk
    simp only [centralOrders,Finset.mem_filter,Finset.mem_range] at hk
    rw [show N-1-(k-1) = N-k by omega,show N-(k-1) = N+1-k by omega]

private theorem successor_reindex (a : ℕ → ℂ) {N K : ℕ} (hK : 0 < K)
    (hKN : 2*K ≤ N) :
    (∑ k∈Finset.Icc 1 (N+1-K),
      a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ))=
    ∑ i∈(Finset.range N).filter (fun i => i ≤ N-K),
      a i*a (N-i)/((N+1-i : ℕ) : ℂ) := by
  apply Finset.sum_bij (fun k _ => k-1)
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  · intro k hk j hj he
    simp only [Finset.mem_Icc] at hk hj
    omega
  · intro i hi
    simp only [Finset.mem_filter,Finset.mem_range] at hi
    refine ⟨i+1,?_,by omega⟩
    simp only [Finset.mem_Icc]
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [show N-(k-1) = N+1-k by omega,
      show N+1-(k-1) = N+2-k by omega]

/-- This is the existing evaluator, not a new physical carrier. All
factorial orders and both prefixes are included before the inequality. -/
theorem evaluation_eq_joined_add_advance (a : ℕ → ℂ) (u : ℝ) {N K : ℕ}
    (hK : 0 < K) (hKN : 2*K ≤ N) :
    evaluation a u N K=
      (∑ i∈Finset.range N, (joinedWeight N K (lengthFactor u N) i : ℂ)*
        a i*a (N-1-i))+advanceError a N K (lengthFactor u N) := by
  rw [evaluation,central_reindex a hK hKN,successor_reindex a hK hKN]
  simp only [Finset.sum_filter,advanceError,joinedWeight,positiveWeight,
    successorWeight,lengthFactor,Complex.ofReal_sub,Complex.ofReal_mul,
    Complex.ofReal_div,Complex.ofReal_natCast,Finset.mul_sum,
    Finset.sum_div,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> push_cast <;> ring

/-- Exact reflection of the whole joined coefficient, including endpoints. -/
theorem joined_sum_eq_symmetric (a : ℕ → ℂ) (N K : ℕ) (b : ℝ) :
    (∑ i∈Finset.range N, (joinedWeight N K b i : ℂ)*a i*a (N-1-i))=
      ∑ i∈Finset.range N, (symmetricWeight N K b i : ℂ)*a i*a (N-1-i) := by
  have hr := Finset.sum_range_reflect
    (fun i => (joinedWeight N K b i : ℂ)*a i*a (N-1-i)) N
  have hf : (∑ i∈Finset.range N,
      (joinedWeight N K b (N-1-i) : ℂ)*a i*a (N-1-i))=
      ∑ i∈Finset.range N, (joinedWeight N K b i : ℂ)*a i*a (N-1-i) := by
    convert hr using 1
    apply Finset.sum_congr rfl
    intro i hi
    have hiN := Finset.mem_range.mp hi
    rw [show N-1-(N-1-i) = i by omega]
    ring
  have hh : (∑ i∈Finset.range N, (symmetricWeight N K b i : ℂ)*a i*a (N-1-i))=
      ((∑ i∈Finset.range N, (joinedWeight N K b i : ℂ)*a i*a (N-1-i))+
        ∑ i∈Finset.range N, (joinedWeight N K b (N-1-i) : ℂ)*a i*a (N-1-i))/2 := by
    simp only [symmetricWeight,Complex.ofReal_div,Complex.ofReal_add,
      Complex.ofReal_ofNat,←Finset.sum_add_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hh,hf]
  ring

/-- Align or oppose the conjugated incidence according to the joined sign. -/
def correlationSign (r : ℝ) : ℝ := if 0 ≤ r then 1 else -1

/-- One diagonal energy after joining the two degrees and swapped rows. -/
def diagonalEnergy (a : ℕ → ℂ) (N K : ℕ) (b : ℝ) : ℝ :=
  ∑ i∈Finset.range N, |symmetricWeight N K b i|/2*
    (‖a i‖^2+‖a (N-1-i)‖^2)

/-- The full nonnegative correlation credit is kept with a negative sign.
It is never split by prime count, phase sector or Peano component. -/
def correlationCredit (a : ℕ → ℂ) (N K : ℕ) (b : ℝ) : ℝ :=
  ∑ i∈Finset.range N, |symmetricWeight N K b i|/2*
    ‖a i-(correlationSign (symmetricWeight N K b i) : ℂ)*
      star (a (N-1-i))‖^2

theorem correlationCredit_nonneg (a : ℕ → ℂ) (N K : ℕ) (b : ℝ) :
    0 ≤ correlationCredit a N K b :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (by positivity) (sq_nonneg _))

/-- The energy identity includes the original complex product, not its
modulus or the product of separate real parts. -/
theorem real_product_energy (r : ℝ) (z w : ℂ) :
    r*(z*w).re=|r|/2*(‖z‖^2+‖w‖^2)-
      |r|/2*‖z-(correlationSign r : ℂ)*star w‖^2 := by
  simp only [correlationSign]
  split_ifs with hr
  · rw [abs_of_nonneg hr]
    simp only [Complex.ofReal_one,one_mul,Complex.sq_norm,Complex.normSq_sub,
      starRingEnd_apply,star_star]
    rw [Complex.star_def,Complex.normSq_conj]
    ring
  · rw [abs_of_neg (lt_of_not_ge hr)]
    simp only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul,sub_neg_eq_add,
      Complex.sq_norm,Complex.normSq_add,starRingEnd_apply,star_star]
    rw [Complex.star_def,Complex.normSq_conj]
    ring

theorem advancePrice_nonneg (a : ℕ → ℂ) (N K : ℕ) (b : ℝ) :
    0 ≤ advancePrice a N K b := by
  unfold advancePrice successorWeight
  positivity

theorem norm_advanceError_le (a : ℕ → ℂ) (N K : ℕ) (b : ℝ) :
    ‖advanceError a N K b‖ ≤ advancePrice a N K b := by
  unfold advanceError advancePrice
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg b)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hv : 0 ≤ successorWeight N K i := by unfold successorWeight; positivity
  simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hv]
  exact le_rfl

/-- Coefficient price after adjacent degrees and reflected rows are joined. -/
def weightVariation (N K : ℕ) (b : ℝ) : ℝ :=
  ∑ i∈Finset.range N, |symmetricWeight N K b i|

/-- The old separated price, used only to measure the new contraction. -/
def separateVariation (N K : ℕ) (b : ℝ) : ℝ :=
  ∑ i∈Finset.range N, (positiveWeight N K i+b*successorWeight N K i)

/-- The symmetric price never exceeds the already joined unsymmetric one. -/
theorem weightVariation_le_joined (N K : ℕ) (b : ℝ) :
    weightVariation N K b ≤ ∑ i∈Finset.range N, |joinedWeight N K b i| := by
  have hr := Finset.sum_range_reflect (fun i => |joinedWeight N K b i|) N
  calc
    _ ≤ ∑ i∈Finset.range N,
        (|joinedWeight N K b i|+|joinedWeight N K b (N-1-i)|)/2 := by
      apply Finset.sum_le_sum
      intro i _
      unfold symmetricWeight
      rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
    _ = _ := by
      rw [←Finset.sum_div,Finset.sum_add_distrib,hr]
      ring

private theorem abs_sub_overlap {x y t : ℝ} (hx : t ≤ x) (hy : t ≤ y) :
    |x-y| ≤ x+y-2*t := by
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Every central row pays the same fixed overlap before any coefficient
absolute value. This covers the whole factorial band, not prime samples. -/
theorem joined_weight_overlap {N K i : ℕ} {b : ℝ} (hi : i < N) (hb : 1 ≤ b)
    (hcentral : K ≤ i ∧ i < N-K) :
    |joinedWeight N K b i| ≤ positiveWeight N K i+b*successorWeight N K i-
      2/((N+1 : ℕ) : ℝ) := by
  have hN : 0 < N := by omega
  have hNi : 0 < N+1-i := by omega
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnr : (0 : ℝ) < ((N+1-i : ℕ) : ℝ) := by exact_mod_cast hNi
  have hsum : ((N+1-i : ℕ) : ℝ) ≤ ((N+1 : ℕ) : ℝ) := by exact_mod_cast (show N+1-i ≤ N+1 by omega)
  have hp : 1/((N+1 : ℕ) : ℝ) ≤ positiveWeight N K i := by
    unfold positiveWeight
    rw [if_pos hcentral]
    have he : (1 : ℝ)/((N+1 : ℕ) : ℝ) ≤ 1/(N : ℝ) :=
      one_div_le_one_div_of_le hnR (by norm_cast; omega)
    exact he.trans (le_add_of_nonneg_right (by positivity))
  have hv : 1/((N+1 : ℕ) : ℝ) ≤ b*successorWeight N K i := by
    unfold successorWeight
    rw [if_pos (by omega : i ≤ N-K)]
    exact (one_div_le_one_div_of_le hnr hsum).trans
      (le_mul_of_one_le_left (by positivity) hb)
  unfold joinedWeight
  convert abs_sub_overlap hp hv using 1
  ring

/-- A proved fixed coefficient saving on the ENTIRE native order band.
The `1/3` is independent of the prime phases and selected-zero data. -/
theorem weightVariation_native_contraction {N : ℕ} (hN : 65536 ≤ N)
    {b : ℝ} (hb : 1 ≤ b) :
    weightVariation N (13*N/32) b ≤ separateVariation N (13*N/32) b-1/3 := by
  let K := 13*N/32
  let S := (Finset.range N).filter (fun i => K ≤ i ∧ i < N-K)
  have hcard : S.card = N-2*K := by
    have hs : S = Finset.Ico K (N-K) := by
      ext i
      simp only [S,Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
      dsimp [K]
      omega
    rw [hs,Nat.card_Ico]
    dsimp [K]
    omega
  have hcost : (1/3 : ℝ) ≤ 2/((N+1 : ℕ) : ℝ)*S.card := by
    have hR : ((N+1 : ℕ) : ℝ) ≤ 6*((N-2*K : ℕ) : ℝ) := by
      exact_mod_cast (show N+1 ≤ 6*(N-2*K) by dsimp [K]; omega)
    rw [hcard]
    have hp : (0 : ℝ) < ((N+1 : ℕ) : ℝ) := by positivity
    rw [show 2/((N+1 : ℕ) : ℝ)*((N-2*K : ℕ) : ℝ)=
      (2*((N-2*K : ℕ) : ℝ))/((N+1 : ℕ) : ℝ) by ring] at *
    apply (le_div_iff₀ hp).mpr
    linarith only [hR]
  have hp : (∑ i∈Finset.range N, |joinedWeight N K b i|) ≤
      separateVariation N K b-2/((N+1 : ℕ) : ℝ)*S.card := by
    have hs : (∑ i∈Finset.range N,
        if K ≤ i ∧ i < N-K then (2/((N+1 : ℕ) : ℝ)) else 0)=
        2/((N+1 : ℕ) : ℝ)*S.card := by
      rw [←Finset.sum_filter]
      simp [S,mul_comm]
    rw [←hs, separateVariation,←Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hiN := Finset.mem_range.mp hi
    split_ifs with hc
    · exact joined_weight_overlap hiN hb hc
    · simp only [sub_zero]
      unfold joinedWeight
      have hp : 0 ≤ positiveWeight N K i := by unfold positiveWeight; positivity
      have hv : 0 ≤ b*successorWeight N K i := by
        have hb0 : 0 ≤ b := by linarith only [hb]
        unfold successorWeight
        positivity
      rw [abs_sub_comm]
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg hv,abs_of_nonneg hp]; ring)
  exact (weightVariation_le_joined N K b).trans (hp.trans (by linarith only [hcost]))

/-- A uniform envelope is applied only AFTER the signed incidence join. -/
theorem diagonalEnergy_le_variation (a : ℕ → ℂ) {N K : ℕ} (b : ℝ)
    {C : ℝ} (ha : ∀ i < N, ‖a i‖ ≤ C) :
    diagonalEnergy a N K b ≤ C^2*weightVariation N K b := by
  unfold diagonalEnergy weightVariation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hiN := Finset.mem_range.mp hi
  have hjN : N-1-i < N := by omega
  have hp := pow_le_pow_left₀ (norm_nonneg (a i)) (ha i hiN) 2
  have hq := pow_le_pow_left₀ (norm_nonneg (a (N-1-i))) (ha _ hjN) 2
  have hs := mul_le_mul_of_nonneg_left (add_le_add hp hq)
    (show 0≤|symmetricWeight N K b i|/2 by positivity)
  exact hs.trans_eq (by ring)

/-- Every adjacent-order difference is retained. The finite error mass is
measured around an arbitrary complex center, not assumed arithmetically small. -/
theorem advancePrice_le_centered_mass (a : ℕ → ℂ) (c : ℂ) {N K : ℕ}
    (hKN : K ≤ N) (b : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i < N, ‖a i‖ ≤ C) :
    advancePrice a N K b ≤ 2*|b| * C/((K+1 : ℕ) : ℝ)*
      ∑ j∈Finset.range (N+1), ‖a j-c‖ := by
  let e := fun j => ‖a j-c‖
  have he (j : ℕ) : 0 ≤ e j := norm_nonneg _
  have hr := Finset.sum_range_reflect e N
  have hs : (∑ i∈Finset.range N, e (N-i))=
      ∑ i∈Finset.range N, e (i+1) := by
    have hh := Finset.sum_range_reflect (fun i => e (i+1)) N
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [show N-1-i+1 = N-i by have := Finset.mem_range.mp hi; omega]
  have hlo : (∑ i∈Finset.range N, e i) ≤ ∑ i∈Finset.range (N+1), e i := by
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (he N)
  have hhi : (∑ i∈Finset.range N, e (i+1)) ≤ ∑ i∈Finset.range (N+1), e i := by
    rw [Finset.sum_range_succ']
    exact le_add_of_nonneg_right (he 0)
  have hp : (∑ i∈Finset.range N, successorWeight N K i*‖a i‖*
        ‖a (N-1-i)-a (N-i)‖) ≤
      C/((K+1 : ℕ) : ℝ)*∑ i∈Finset.range N, (e (N-1-i)+e (N-i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hiN := Finset.mem_range.mp hi
    have he : ‖a (N-1-i)-a (N-i)‖ ≤ e (N-1-i)+e (N-i) := by
      have hid : a (N-1-i)-a (N-i) = (a (N-1-i)-c)-(a (N-i)-c) := by ring
      rw [hid]
      exact norm_sub_le _ _
    have hv : successorWeight N K i ≤ 1/((K+1 : ℕ) : ℝ) := by
      unfold successorWeight
      split_ifs with hactive
      · apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast (show K+1 ≤ N+1-i by omega)
      · positivity
    have hv0 : 0 ≤ successorWeight N K i := by unfold successorWeight; positivity
    have hw := mul_le_mul hv (ha i hiN) (norm_nonneg _) (by positivity)
    exact (mul_le_mul hw he (norm_nonneg _) (by positivity)).trans_eq (by ring)
  unfold advancePrice
  calc
    _ ≤ |b| *(C/((K+1 : ℕ) : ℝ)*∑ i∈Finset.range N, (e (N-1-i)+e (N-i))) :=
      mul_le_mul_of_nonneg_left hp (abs_nonneg b)
    _ = |b| *(C/((K+1 : ℕ) : ℝ)*
        ((∑ i∈Finset.range N,e i)+∑ i∈Finset.range N,e (i+1))) := by
      rw [Finset.sum_add_distrib,hr,hs]
    _ ≤ |b| *(C/((K+1 : ℕ) : ℝ)*
        ((∑ i∈Finset.range (N+1),e i)+∑ i∈Finset.range (N+1),e i)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add hlo hhi) (by positivity)) (abs_nonneg b)
    _ = _ := by dsimp [e]; ring

/-- The old moving length gives both normalization bounds independently. -/
theorem lengthFactor_bounds {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536 ≤ N) :
    1 ≤ lengthFactor u N ∧ lengthFactor u N ≤ 3/2 := by
  have hu0 : 0 < u := by linarith only [hu]
  have hL := SquarefreeVaughanLogSource.length_pos u N
  have hlo := ZetaRieszPostHingeEnergy.length_ge_rational hN hu0 hU
  have hhi := ZetaRieszHeadOrders.length_le_two_log_two hu (by omega : 2 ≤ N)
  have hprod := mul_nonneg (show 0 ≤ u-1/2 by linarith only [hu]) hL.le
  have hNr : (65536 : ℝ) ≤ N := by exact_mod_cast hN
  have huq : u ≤ 3/5 := by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU; linarith only [hU]
  have hLL : SquarefreeVaughanLogSource.length u N ≤ (7/5 : ℝ)*N := by
    nlinarith only [hhi,log_two_lt_d9,Nat.cast_nonneg (α:=ℝ) N]
  have hUL := mul_le_mul_of_nonneg_left hLL hu0.le
  have hUN := mul_le_mul_of_nonneg_right huq (show 0 ≤ (7/5 : ℝ)*N by positivity)
  unfold lengthFactor
  constructor
  · apply (le_div_iff₀ (mul_pos hu0 hL)).mpr
    push_cast
    nlinarith only [hUL,hUN,hNr]
  · apply (div_le_iff₀ (mul_pos hu0 hL)).mpr
    push_cast
    nlinarith only [hlo,hprod,hNr]

/-- Under the existing exposed-zero analytic hypotheses ONLY the
adjacent-order payment is source-o(1). The signed main credit is not paid. -/
theorem advancePrice_ordinary_le (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    {N : ℕ} (hN : 65536 ≤ N) :
    advancePrice (ordinaryArray (3/2-rho.1.re) rho.1.im) N (13*N/32)
      (lengthFactor (3/2-rho.1.re) N) ≤
      12*((analyticZetaZeroMultiplicity rho : ℝ)+ZetaRieszJoinedSourceError.sourceErrorMass rho)*
        ZetaRieszJoinedSourceError.sourceErrorMass rho/((N+1 : ℕ) : ℝ) := by
  let m := analyticZetaZeroMultiplicity rho
  let M := ZetaRieszJoinedSourceError.sourceErrorMass rho
  have hM : 0 ≤ M := ZetaRieszJoinedSourceError.sourceErrorMass_nonneg rho
  have ha k : ‖ordinaryArray (3/2-rho.1.re) rho.1.im k‖≤(m : ℝ)+M := by
    have he := ZetaRieszJoinedSourceError.sum_source_error_le rho hrho hexposed hU {k}
    simp only [Finset.sum_singleton] at he
    have hi : ordinaryArray (3/2-rho.1.re) rho.1.im k=
        (ordinaryArray (3/2-rho.1.re) rho.1.im k+(m : ℂ))-(m : ℂ) := by ring
    rw [hi]
    exact ((norm_sub_le _ _).trans (add_le_add he le_rfl)).trans_eq (by
      rw [Complex.norm_natCast]
      dsimp [M]
      ring)
  have hmass := ZetaRieszJoinedSourceError.sum_source_error_le rho hrho hexposed hU
    (Finset.range (N+1))
  have hu : 1/2 ≤ 3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  have hb := lengthFactor_bounds hu hU hN
  have hb0 : 0 ≤ lengthFactor (3/2-rho.1.re) N := by linarith only [hb.1]
  have hprice := advancePrice_le_centered_mass (ordinaryArray (3/2-rho.1.re) rho.1.im)
    (-(m : ℂ)) (show 13*N/32 ≤ N by omega) (lengthFactor (3/2-rho.1.re) N)
    (show 0 ≤ (m : ℝ)+M by positivity) (fun i _ => ha i)
  rw [abs_of_nonneg (by linarith only [hb.1] : 0 ≤ lengthFactor (3/2-rho.1.re) N)] at hprice
  simp only [sub_neg_eq_add] at hprice
  have hrec : (1 : ℝ)/((13*N/32+1 : ℕ) : ℝ) ≤ 4/((N+1 : ℕ) : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [one_mul]
    exact_mod_cast (show N+1 ≤ 4*(13*N/32+1) by omega)
  calc
    _ ≤ (2*lengthFactor (3/2-rho.1.re) N*((m : ℝ)+M)/((13*N/32+1 : ℕ) : ℝ))*M :=
      hprice.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
    _ ≤ (2*(3/2)*((m : ℝ)+M)*M)*(4/((N+1 : ℕ) : ℝ)) := by
      have hfac := mul_le_mul_of_nonneg_right hb.2 (show 0 ≤ 2*((m : ℝ)+M)*M by positivity)
      have he := mul_le_mul hfac hrec (by positivity) (by positivity)
      simpa only [div_eq_mul_inv,one_mul,mul_assoc,mul_comm,mul_left_comm] using he
    _ = _ := by dsimp [m,M]; ring

/-- The whole reflected incidence has this signed energy identity. -/
theorem joined_real_eq_energy_sub_credit (a : ℕ → ℂ) (N K : ℕ) (b : ℝ) :
    (∑ i∈Finset.range N, (symmetricWeight N K b i : ℂ)*a i*a (N-1-i)).re=
      diagonalEnergy a N K b-correlationCredit a N K b := by
  rw [Complex.re_sum]
  unfold diagonalEnergy correlationCredit
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc,Complex.re_ofReal_mul,real_product_energy]

/-- An unconditional SIGNED bound for the entire coupled evaluator.
Only the exact adjacent-order error is given an absolute price. -/
theorem evaluation_signed_upper (a : ℕ → ℂ) (u : ℝ) {N K : ℕ}
    (hK : 0 < K) (hKN : 2*K ≤ N) :
    (evaluation a u N K).re ≤
      diagonalEnergy a N K (lengthFactor u N)-
        correlationCredit a N K (lengthFactor u N)+
          advancePrice a N K (lengthFactor u N) := by
  rw [evaluation_eq_joined_add_advance a u hK hKN,joined_sum_eq_symmetric,
    Complex.add_re,joined_real_eq_energy_sub_credit]
  exact add_le_add_right ((Complex.re_le_norm _).trans
    (norm_advanceError_le a N K (lengthFactor u N))) _

/-- The fixed `1/3` contraction and the entire correlation credit are
retained together in the signed bound. No separate Peano costs appear. -/
theorem evaluation_signed_upper_contracted (a : ℕ → ℂ) (u : ℝ) {N : ℕ}
    (hN : 65536 ≤ N) (hb : 1 ≤ lengthFactor u N)
    {C : ℝ} (ha : ∀ i < N, ‖a i‖ ≤ C) :
    (evaluation a u N (13*N/32)).re ≤
      C^2*(separateVariation N (13*N/32) (lengthFactor u N)-1/3)-
        correlationCredit a N (13*N/32) (lengthFactor u N)+
          advancePrice a N (13*N/32) (lengthFactor u N) := by
  have hd := (diagonalEnergy_le_variation a (lengthFactor u N) ha).trans
    (mul_le_mul_of_nonneg_left (weightVariation_native_contraction hN hb) (sq_nonneg C))
  have hh := evaluation_signed_upper a u (show 0 < 13*N/32 by omega)
    (show 2*(13*N/32) ≤ N by omega)
  linarith only [hd,hh]

/-- The signed inequality is attained by a constant array. Thus a free
additional correlation credit is not supplied by the coefficient algebra. -/
theorem constant_bound_attained (c : ℂ) (u : ℝ) {N K : ℕ}
    (hK : 0 < K) (hKN : 2*K ≤ N) :
    (evaluation (fun _ => c) u N K).re=
      diagonalEnergy (fun _ => c) N K (lengthFactor u N)-
        correlationCredit (fun _ => c) N K (lengthFactor u N) := by
  rw [evaluation_eq_joined_add_advance (fun _ => c) u hK hKN,
    joined_sum_eq_symmetric]
  simp only [advanceError,sub_self,mul_zero,Finset.sum_const_zero,add_zero]
  exact joined_real_eq_energy_sub_credit _ _ _ _

/-- The SAME signed inequality applies to the literal prime sum after
the previously proved whole-support and single-diagonal payments. No zero
hypothesis, new mask completion or proper-power approximation is added. -/
theorem prefix_signed_upper {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|)
    {N : ℕ} (hN : 65536 ≤ N) :
    (ZetaRieszPairPrefixPayment.prefixPairDefect u y N).re ≤
      diagonalEnergy (ordinaryArray u y) N (13*N/32) (lengthFactor u N)-
        correlationCredit (ordinaryArray u y) N (13*N/32) (lengthFactor u N)+
          advancePrice (ordinaryArray u y) N (13*N/32) (lengthFactor u N)+
            ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
              ZetaRieszPairJointQuadratic.squareBudget u N := by
  have he := evaluation_signed_upper (ordinaryArray u y) u
    (show 0 < 13*N/32 by omega) (show 2*(13*N/32) ≤ N by omega)
  rw [evaluation_original] at he
  have hb := (Complex.re_le_norm _).trans
    (ZetaRieszJoinedPhaseRadius.norm_prefix_sub_ordinary_le hu hU hy hN)
  rw [Complex.sub_re] at hb
  linarith only [he,hb]

/-- A uniform ordinary-prime envelope receives the proved `1/3` joined
coefficient reduction, while the entire signed credit stays on the right.
The envelope is not assumed to imply the independent endgame target. -/
theorem prefix_signed_upper_contracted {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|)
    {N : ℕ} (hN : 65536 ≤ N) {C : ℝ}
    (ha : ∀ i<N, ‖ordinaryArray u y i‖ ≤ C) :
    (ZetaRieszPairPrefixPayment.prefixPairDefect u y N).re ≤
      C^2*(separateVariation N (13*N/32) (lengthFactor u N)-1/3)-
        correlationCredit (ordinaryArray u y) N (13*N/32) (lengthFactor u N)+
          advancePrice (ordinaryArray u y) N (13*N/32) (lengthFactor u N)+
            ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
              ZetaRieszPairJointQuadratic.squareBudget u N := by
  have he := evaluation_signed_upper_contracted (ordinaryArray u y) u hN
    (lengthFactor_bounds hu hU hN).1 ha
  rw [evaluation_original] at he
  have hb := (Complex.re_le_norm _).trans
    (ZetaRieszJoinedPhaseRadius.norm_prefix_sub_ordinary_le hu hU hy hN)
  rw [Complex.sub_re] at hb
  linarith only [he,hb]

/-- The original balanced contribution AND its original complement receive
ONE signed bound. Neither piece is priced or completed on its own. -/
theorem balanced_and_rest_signed_upper {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|)
    {N : ℕ} (hN : 65536 ≤ N) :
    (ZetaRieszSelbergMaskCancellation.balancedPrefix u y N+
      ZetaRieszSelbergMaskCancellation.maskRest u y N).re ≤
      diagonalEnergy (ordinaryArray u y) N (13*N/32) (lengthFactor u N)-
        correlationCredit (ordinaryArray u y) N (13*N/32) (lengthFactor u N)+
          advancePrice (ordinaryArray u y) N (13*N/32) (lengthFactor u N)+
            ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
              ZetaRieszPairJointQuadratic.squareBudget u N := by
  rw [ZetaRieszSelbergMaskCancellation.balanced_add_rest hN hy]
  exact prefix_signed_upper hu hU hy hN

/-- This final inequality pays the adjacent-order error under the exposed
analytic hypotheses. The independent arithmetic `D-credit` bound remains open. -/
theorem exposed_prefix_signed_upper (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    {N : ℕ} (hN : 65536 ≤ N) :
    (ZetaRieszPairPrefixPayment.prefixPairDefect (3/2-rho.1.re) rho.1.im N).re ≤
      diagonalEnergy (ordinaryArray (3/2-rho.1.re) rho.1.im) N (13*N/32)
        (lengthFactor (3/2-rho.1.re) N)-
      correlationCredit (ordinaryArray (3/2-rho.1.re) rho.1.im) N (13*N/32)
        (lengthFactor (3/2-rho.1.re) N)+
      12*((analyticZetaZeroMultiplicity rho : ℝ)+ZetaRieszJoinedSourceError.sourceErrorMass rho)*
        ZetaRieszJoinedSourceError.sourceErrorMass rho/((N+1 : ℕ) : ℝ)+
      ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
        ZetaRieszPairJointQuadratic.squareBudget (3/2-rho.1.re) N := by
  have hu : 1/2 ≤ 3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  have hy := (ZetaRieszShiftedCenter.height_gt_fiftyFour rho hrho).le
  have hh := prefix_signed_upper hu hU hy hN
  have he := advancePrice_ordinary_le rho hrho hexposed hU hN
  linarith only [hh,he]

/-- The coherent regression keeps the exact old source. This is a model
sharpness theorem, not a prime-population estimate or a zero assertion. -/
theorem constant_credit_source_limit {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => diagonalEnergy (fun _ => (-1 : ℂ)) N (13*N/32) (lengthFactor u N)-
      correlationCredit (fun _ => (-1 : ℂ)) N (13*N/32) (lengthFactor u N)) atTop
      (𝓝 (1-ZetaRieszMaskSupport.retainedCost u)) := by
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (harmonicEvaluation_tendsto (fun _ => (-1 : ℂ)) tendsto_const_nhds
      (show 0 < u by linarith only [hu])
      (show u ≤ 3/5 by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU; linarith only [hU]))
  simp only [Complex.ofReal_re] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (65536 : ℕ)] with N hN
  simp only [Function.comp_apply]
  rw [←evaluation_original]
  exact constant_bound_attained (-1) u (by omega) (by omega)

/-- No extra `399/5000` credit can be obtained for ALL arrays from this
coefficient algebra. This is not an impossibility theorem for actual primes. -/
theorem no_generic_constant_credit_target {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (orders : ℕ → ℕ) (horders : Tendsto orders atTop atTop)
    (err : ℕ → ℝ) (he : Tendsto err atTop (𝓝 0)) :
    ¬∃ᶠ j in atTop,
      diagonalEnergy (fun _ => (-1 : ℂ)) (orders j) (13*orders j/32) (lengthFactor u (orders j))-
      correlationCredit (fun _ => (-1 : ℂ)) (orders j) (13*orders j/32) (lengthFactor u (orders j))
        ≤ 399/5000+err j := by
  intro hf
  have hs := (constant_credit_source_limit hu hU).comp horders
  have hb : 1-ZetaRieszMaskSupport.retainedCost u-0 ≤ (399/5000 : ℝ) :=
    le_of_tendsto_of_frequently (hs.sub he) (hf.mono fun j hj => by
      dsimp only [Function.comp_apply]
      linarith only [hj])
  have ht := ZetaRieszPairFloorAllMultiplicity.target_lt_multiple_source hu hU
    (m:=1) (by norm_num : 0<(1 : ℕ))
  norm_num only [Nat.cast_one,one_pow,one_mul] at ht
  linarith only [hb,ht]

end RiemannGaussian.ZetaRieszCoupledSignedBound
