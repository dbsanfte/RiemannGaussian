/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSaddleCenters
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# The joined two-center response before any separate estimate

One exact central difference and its triangular integral retain the original
prime mask and phase. Factorial summation by parts below keeps every order
and every first/second difference of the literal order weight. The joint
operator preserves the stationary channel; no independent floor follows
from a central-difference multiplier alone.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszJointSecondDifference
open ZetaRieszSaddleCenters

/-- The same finite mask along the straight line joining the two centers. -/
def responsePath (E : Finset (ℕ×ℕ×ℕ×ℕ)) (w : ℕ×ℕ×ℕ×ℕ → ℂ)
    (s : ℂ) (theta delta t : ℝ) : ℂ :=
  comparison E w s (t*theta) (t*delta)

/-- The signed second-derivative symbol is summed before any norm. -/
def secondSymbol (E : Finset (ℕ×ℕ×ℕ×ℕ)) (w : ℕ×ℕ×ℕ×ℕ → ℂ)
    (s : ℂ) (theta delta t : ℝ) : ℂ :=
  ∑ e∈E, w e*(mismatch theta delta e.2.1 e.2.2.1 e.1 e.2.2.2^2 : ℝ)*
    (cos (t*mismatch theta delta e.2.1 e.2.2.1 e.1 e.2.2.2) : ℂ)*
      (zetaPrimeLogKernel e.2.1 s e.1*zetaPrimeLogKernel e.2.2.1 s e.2.2.2)

/-- The first derivative is also retained as one signed finite sum. -/
def firstSymbol (E : Finset (ℕ×ℕ×ℕ×ℕ)) (w : ℕ×ℕ×ℕ×ℕ → ℂ)
    (s : ℂ) (theta delta t : ℝ) : ℂ :=
  ∑ e∈E, w e*(-sin (t*mismatch theta delta e.2.1 e.2.2.1 e.1 e.2.2.2)*
    mismatch theta delta e.2.1 e.2.2.1 e.1 e.2.2.2 : ℝ)*
      (zetaPrimeLogKernel e.2.1 s e.1*zetaPrimeLogKernel e.2.2.1 s e.2.2.2)

/-- Every phase and every selected factorial order remains in the path. -/
theorem responsePath_eq (E : Finset (ℕ×ℕ×ℕ×ℕ))
    (w : ℕ×ℕ×ℕ×ℕ → ℂ) (s : ℂ) (theta delta t : ℝ) :
    responsePath E w s theta delta t =
      ∑ e∈E, w e*(cos (t*mismatch theta delta e.2.1 e.2.2.1 e.1 e.2.2.2) : ℂ)*
        (zetaPrimeLogKernel e.2.1 s e.1*zetaPrimeLogKernel e.2.2.1 s e.2.2.2) := by
  simp only [responsePath,comparison,pair_eq_cos_mul]
  apply Finset.sum_congr rfl
  intro e _
  have hm : mismatch (t*theta) (t*delta) e.2.1 e.2.2.1 e.1 e.2.2.2=
      t*mismatch theta delta e.2.1 e.2.2.1 e.1 e.2.2.2 := by
    unfold mismatch
    ring
  rw [hm]
  ring

theorem responsePath_zero (E : Finset (ℕ×ℕ×ℕ×ℕ))
    (w : ℕ×ℕ×ℕ×ℕ → ℂ) (s : ℂ) (theta delta : ℝ) :
    responsePath E w s theta delta 0 = original E w s := by
  rw [responsePath_eq]
  simp only [zero_mul,cos_zero,Complex.ofReal_one,mul_one,original]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Differentiation stays inside the original finite mask. -/
theorem responsePath_hasDerivAt (E : Finset (ℕ×ℕ×ℕ×ℕ))
    (w : ℕ×ℕ×ℕ×ℕ → ℂ) (s : ℂ) (theta delta t : ℝ) :
    HasDerivAt (responsePath E w s theta delta)
      (firstSymbol E w s theta delta t) t := by
  have he : responsePath E w s theta delta=
      (fun v : ℝ => ∑ e∈E, w e*
        (cos (v*mismatch theta delta e.2.1 e.2.2.1 e.1 e.2.2.2) : ℂ)*
          (zetaPrimeLogKernel e.2.1 s e.1*zetaPrimeLogKernel e.2.2.1 s e.2.2.2)) := by
    funext v
    exact responsePath_eq E w s theta delta v
  rw [he]
  unfold firstSymbol
  apply HasDerivAt.fun_sum
  intro e _
  let a := mismatch theta delta e.2.1 e.2.2.1 e.1 e.2.2.2
  simpa only [Function.comp_def,id_eq,one_mul] using
    ((((Real.hasDerivAt_cos (t*a)).comp t ((hasDerivAt_id t).mul_const a)).ofReal_comp).const_mul (w e)).mul_const
        (zetaPrimeLogKernel e.2.1 s e.1*zetaPrimeLogKernel e.2.2.1 s e.2.2.2)

/-- The new symbol is exactly minus the second derivative, including all
low orders and stationary frequencies. -/
theorem firstSymbol_hasDerivAt (E : Finset (ℕ×ℕ×ℕ×ℕ))
    (w : ℕ×ℕ×ℕ×ℕ → ℂ) (s : ℂ) (theta delta t : ℝ) :
    HasDerivAt (firstSymbol E w s theta delta)
      (-secondSymbol E w s theta delta t) t := by
  unfold firstSymbol secondSymbol
  rw [←Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro e _
  let a := mismatch theta delta e.2.1 e.2.2.1 e.1 e.2.2.2
  have hd : HasDerivAt (fun v : ℝ => -sin (v*a)*a) (-a^2*cos (t*a)) t := by
    convert (((Real.hasDerivAt_sin (t*a)).comp t
      ((hasDerivAt_id t).mul_const a)).neg.mul_const a) using 1
    all_goals first | rfl | ring
  simpa only [Complex.ofReal_neg,Complex.ofReal_mul,mul_neg,neg_mul,mul_assoc] using
    ((hd.ofReal_comp).const_mul (w e)).mul_const
      (zetaPrimeLogKernel e.2.1 s e.1*zetaPrimeLogKernel e.2.2.1 s e.2.2.2)

/-- The full central difference equals minus twice the signed curvature. -/
theorem central_difference_eq (E : Finset (ℕ×ℕ×ℕ×ℕ))
    (w : ℕ×ℕ×ℕ×ℕ → ℂ) (s : ℂ) (theta delta : ℝ) :
    responsePath E w s theta delta 1+responsePath E w s theta delta (-1)-
      2*responsePath E w s theta delta 0=
      -2*curvature E w s theta delta := by
  have he : responsePath E w s theta delta (-1)=
      responsePath E w s theta delta 1 := by
    simp only [responsePath_eq,neg_one_mul,one_mul,cos_neg]
  rw [he,responsePath_zero]
  have hl := same_mask_ledger E w s theta delta
  simp only [responsePath,one_mul]
  linear_combination -2*hl

/-- Exact Peano kernel, including the stationary frequency zero. -/
theorem one_sub_cos_eq_triangular_integral (a : ℝ) :
    1-cos a=∫ t in (0 : ℝ)..1, (1-t)*a^2*cos (t*a) := by
  have hd (t : ℝ) : HasDerivAt
      (fun v : ℝ => (1-v)*a*sin (v*a)-cos (v*a))
      ((1-t)*a^2*cos (t*a)) t := by
    convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const a |>.mul
      ((Real.hasDerivAt_sin (t*a)).comp t ((hasDerivAt_id t).mul_const a))).sub
      ((Real.hasDerivAt_cos (t*a)).comp t ((hasDerivAt_id t).mul_const a)) using 1
    all_goals first | rfl | (dsimp; ring)
  have hi : IntervalIntegrable (fun t : ℝ => (1-t)*a^2*cos (t*a))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simpa [sub_eq_add_neg,add_comm] using he.symm

/-- Integrability is literal: a finite sum of continuous phase atoms. -/
theorem secondSymbol_integrable (E : Finset (ℕ×ℕ×ℕ×ℕ))
    (w : ℕ×ℕ×ℕ×ℕ → ℂ) (s : ℂ) (theta delta : ℝ) :
    IntervalIntegrable (fun t : ℝ => (1-t : ℝ)*secondSymbol E w s theta delta t)
      MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  unfold secondSymbol
  fun_prop

/-- The triangular integral is the actual signed curvature, not its norm. -/
theorem curvature_eq_triangular_integral (E : Finset (ℕ×ℕ×ℕ×ℕ))
    (w : ℕ×ℕ×ℕ×ℕ → ℂ) (s : ℂ) (theta delta : ℝ) :
    curvature E w s theta delta=
      ∫ t in (0 : ℝ)..1, (1-t : ℝ)*secondSymbol E w s theta delta t := by
  unfold secondSymbol
  simp only [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro e _
    let a := mismatch theta delta e.2.1 e.2.2.1 e.1 e.2.2.2
    have hc := one_sub_cos_eq_triangular_integral a
    have hreal := intervalIntegral.integral_ofReal
      (f := fun t : ℝ => (1-t)*a^2*cos (t*a)) (a := 0) (b := 1)
      (μ := MeasureTheory.volume)
    have hint : (∫ t in (0 : ℝ)..1, (1-t : ℝ)*
        (w e*(a^2 : ℝ)*(cos (t*a) : ℂ)*
          (zetaPrimeLogKernel e.2.1 s e.1*zetaPrimeLogKernel e.2.2.1 s e.2.2.2)))=
        w e*(1-cos a : ℝ)*
          (zetaPrimeLogKernel e.2.1 s e.1*zetaPrimeLogKernel e.2.2.1 s e.2.2.2) := by
      have hf : (fun t : ℝ => (1-t : ℝ)*
          (w e*(a^2 : ℝ)*(cos (t*a) : ℂ)*
            (zetaPrimeLogKernel e.2.1 s e.1*zetaPrimeLogKernel e.2.2.1 s e.2.2.2)))=
          (fun t : ℝ => (((1-t)*a^2*cos (t*a) : ℝ) : ℂ)*
            (w e*(zetaPrimeLogKernel e.2.1 s e.1*
              zetaPrimeLogKernel e.2.2.1 s e.2.2.2))) := by
        funext t
        push_cast
        ring
      rw [hf,intervalIntegral.integral_mul_const,hreal,←hc]
      ring
    exact hint.symm
  · intro e _
    apply Continuous.intervalIntegrable
    fun_prop

/-- A single signed operator acts on the joined object before estimating it. -/
theorem joint_eq_path_and_secondSymbol (E : Finset (ℕ×ℕ×ℕ×ℕ))
    (w : ℕ×ℕ×ℕ×ℕ → ℂ) (s : ℂ) (theta delta : ℝ) :
    comparison E w s theta delta+curvature E w s theta delta=
      responsePath E w s theta delta 1+
        ∫ t in (0 : ℝ)..1, (1-t : ℝ)*secondSymbol E w s theta delta t := by
  rw [curvature_eq_triangular_integral]
  simp only [responsePath,one_mul]

/-- The joined multiplier preserves every frequency, including resonance. -/
theorem joint_multiplier_eq_one (a : ℝ) :
    cos a+(∫ t in (0 : ℝ)..1, (1-t)*a^2*cos (t*a)) = 1 := by
  rw [←one_sub_cos_eq_triangular_integral]
  ring

/-- The original literal sum is one exact signed Peano operator; comparison
and curvature are not given separate prices or separate sign hypotheses. -/
theorem original_eq_joint_Peano (E : Finset (ℕ×ℕ×ℕ×ℕ))
    (w : ℕ×ℕ×ℕ×ℕ → ℂ) (s : ℂ) (theta delta : ℝ) :
    original E w s = responsePath E w s theta delta 1+
      ∫ t in (0 : ℝ)..1, (1-t : ℝ)*secondSymbol E w s theta delta t := by
  rw [same_mask_ledger,joint_eq_path_and_secondSymbol]

/-- Exact finite binomial functional. Arbitrary complex weights can retain
all prime phases, order masks and signed coefficient components. -/
def binomialSum (M : ℕ) (a : ℂ) (f : ℕ → ℂ) : ℂ :=
  ∑ i∈Finset.range (M+1), f i*(M.choose i : ℂ)*a^i*(1-a)^(M-i)

/-- The forward order difference keeps the literal mask jump. -/
def orderDifference (f : ℕ → ℂ) (i : ℕ) : ℂ := f (i+1)-f i

/-- The second difference includes both adjacent mask jumps. -/
def orderSecondDifference (f : ℕ → ℂ) (i : ℕ) : ℂ :=
  f (i+2)-2*f (i+1)+f i

theorem binomialSum_succ (M : ℕ) (a : ℂ) (f : ℕ → ℂ) :
    binomialSum (M+1) a f=
      binomialSum M a (fun i => (1-a)*f i+a*f (i+1)) := by
  have he := Finset.sum_choose_succ_mul
    (R := ℂ) (fun i j => f i*a^i*(1-a)^j) M
  have hl : (∑ i∈Finset.range (M+2), ((M+1).choose i : ℂ)*
      (f i*a^i*(1-a)^(M+1-i))) = binomialSum (M+1) a f := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hl] at he
  rw [he,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hle : i ≤ M := by simpa using Finset.mem_range.mp hi
  rw [show M+1-i = (M-i)+1 by omega,pow_succ,pow_succ]
  ring

/-- First raw factorial moment, including both boundary orders. -/
theorem binomialSum_first_moment (M : ℕ) (a : ℂ) (f : ℕ → ℂ) :
    binomialSum (M+1) a (fun i => (i : ℂ)*f i)=
      (M+1 : ℂ)*a*binomialSum M a (fun i => f (i+1)) := by
  unfold binomialSum
  rw [show M+1+1 = M+1+1 by rfl,Finset.sum_range_succ']
  simp only [Nat.cast_zero,zero_mul,add_zero,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hc : ((i+1 : ℕ) : ℂ)*((M+1).choose (i+1) : ℂ)=
      (M+1 : ℂ)*(M.choose i : ℂ) := by
    have hh := (Nat.add_one_mul_choose_eq M i).symm
    rw [Nat.mul_comm ((M+1).choose (i+1)) (i+1)] at hh
    exact_mod_cast hh
  rw [show M+1-(i+1) = M-i by omega,pow_succ]
  linear_combination (f (i+1)*a^i*(1-a)^(M-i)*a)*hc

/-- Mask-compatible first summation by parts. No order or endpoint is deleted. -/
theorem binomialSum_centered_first (M : ℕ) (a : ℂ) (f : ℕ → ℂ) :
    binomialSum (M+1) a (fun i => ((i : ℂ)-(M+1 : ℂ)*a)*f i)=
      (M+1 : ℂ)*a*(1-a)*binomialSum M a (orderDifference f) := by
  have he : binomialSum (M+1) a (fun i => ((i : ℂ)-(M+1 : ℂ)*a)*f i)=
      binomialSum (M+1) a (fun i => (i : ℂ)*f i)-
        (M+1 : ℂ)*a*binomialSum (M+1) a f := by
    simp only [binomialSum,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,binomialSum_first_moment,binomialSum_succ]
  simp only [binomialSum,orderDifference,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Full factorial mass, with neither boundary order deleted. -/
theorem binomialSum_one (M : ℕ) (a : ℂ) : binomialSum M a (fun _ => 1) = 1 := by
  calc
    _ = ∑ i∈Finset.range (M+1), a^i*(1-a)^(M-i)*(M.choose i : ℂ) := by
      unfold binomialSum
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (a+(1-a))^M := (add_pow a (1-a) M).symm
    _ = 1 := by simp

/-- The complete first factorial-order moment. -/
theorem binomialSum_index (M : ℕ) (a : ℂ) :
    binomialSum (M+1) a (fun i => (i : ℂ)) = (M+1 : ℂ)*a := by
  simpa only [mul_one,binomialSum_one] using
    binomialSum_first_moment M a (fun _ => 1)

/-- The two marked slots have their exact coupled factorial moment. -/
theorem binomialSum_cross_moment (M : ℕ) (a : ℂ) :
    binomialSum (M+2) a (fun i => (i : ℂ)*((M+2 : ℂ)-i))=
      (M+2 : ℂ)*(M+1)*a*(1-a) := by
  have hs : binomialSum (M+1) a (fun i => (M+1 : ℂ)-(i : ℂ))=
      (M+1 : ℂ)*(1-a) := by
    have he : binomialSum (M+1) a (fun i => (M+1 : ℂ)-(i : ℂ))=
        (M+1 : ℂ)*binomialSum (M+1) a (fun _ => 1)-
          binomialSum (M+1) a (fun i => (i : ℂ)) := by
      simp only [binomialSum,Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he,binomialSum_one,binomialSum_index]
    ring
  have hf : (fun i : ℕ => (M+2 : ℂ)-((i+1 : ℕ) : ℂ))=
      (fun i : ℕ => (M+1 : ℂ)-(i : ℂ)) := by
    funext i
    push_cast
    ring
  have hfirst := binomialSum_first_moment (M+1) a (fun i => (M+2 : ℂ)-(i : ℂ))
  rw [hf,hs] at hfirst
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two,mul_assoc,
    mul_left_comm,mul_comm] using hfirst

/-- Mask-compatible second summation by parts. The first term is the
stationary variance, and the second retains the signed mask curvature. -/
theorem binomialSum_centered_second (M : ℕ) (a : ℂ) (f : ℕ → ℂ) :
    binomialSum (M+2) a (fun i => ((i : ℂ)-(M+2 : ℂ)*a)^2*f i)=
      (M+2 : ℂ)*a*(1-a)*
        binomialSum (M+1) a (fun i => a*f i+(1-a)*f (i+1))+
      (M+2 : ℂ)*(M+1)*a^2*(1-a)^2*
        binomialSum M a (orderSecondDifference f) := by
  have hfirst := binomialSum_centered_first (M+1) a
    (fun i => ((i : ℂ)-(M+2 : ℂ)*a)*f i)
  push_cast at hfirst
  have hleft : binomialSum (M+1+1) a
      (fun i => ((i : ℂ)-(M+1+1 : ℂ)*a)*
        (((i : ℂ)-(M+2 : ℂ)*a)*f i))=
      binomialSum (M+2) a (fun i => ((i : ℂ)-(M+2 : ℂ)*a)^2*f i) := by
    simp only [binomialSum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hleft] at hfirst
  rw [hfirst]
  have hexpand : binomialSum (M+1) a
      (orderDifference (fun i => ((i : ℂ)-(M+2 : ℂ)*a)*f i))=
      binomialSum (M+1) a
        (fun i => ((i : ℂ)-(M+1 : ℂ)*a)*orderDifference f i)+
      binomialSum (M+1) a (fun i => a*f i+(1-a)*f (i+1)) := by
    simp only [binomialSum,orderDifference,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  rw [hexpand,binomialSum_centered_first]
  have hdiff : orderDifference (orderDifference f) = orderSecondDifference f := by
    funext i
    simp only [orderDifference,orderSecondDifference]
    rw [show i+1+1 = i+2 by omega]
    ring
  rw [hdiff]
  ring

/-- General detuning from the factorial saddle, still with one signed weight. -/
theorem binomialSum_detuned_second (M : ℕ) (a c d : ℂ) (f : ℕ → ℂ) :
    binomialSum (M+2) a (fun i => (c*((i : ℂ)-(M+2 : ℂ)*a)+d)^2*f i)=
      d^2*binomialSum (M+2) a f+
      2*c*d*(M+2)*a*(1-a)*binomialSum (M+1) a (orderDifference f)+
      c^2*((M+2)*a*(1-a)*
        binomialSum (M+1) a (fun i => a*f i+(1-a)*f (i+1))+
        (M+2)*(M+1)*a^2*(1-a)^2*
          binomialSum M a (orderSecondDifference f)) := by
  have hexpand : binomialSum (M+2) a
      (fun i => (c*((i : ℂ)-(M+2 : ℂ)*a)+d)^2*f i)=
      d^2*binomialSum (M+2) a f+
      2*c*d*binomialSum (M+2) a (fun i => ((i : ℂ)-(M+2 : ℂ)*a)*f i)+
      c^2*binomialSum (M+2) a (fun i => ((i : ℂ)-(M+2 : ℂ)*a)^2*f i) := by
    simp only [binomialSum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hfirst := binomialSum_centered_first (M+1) a f
  simp only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] at hfirst
  rw [hexpand,hfirst,binomialSum_centered_second]
  ring

/-- Multiplying an order mask by a phase retains its second difference,
the phase curvature and BOTH cross jumps. -/
theorem second_difference_product (f g : ℕ → ℂ) (i : ℕ) :
    orderSecondDifference (fun j => f j*g j) i=
      g (i+1)*orderSecondDifference f i+
      f (i+1)*orderSecondDifference g i+
      orderDifference f (i+1)*orderDifference g (i+1)+
      orderDifference f i*orderDifference g i := by
  simp only [orderSecondDifference,orderDifference]
  rw [show i+1+1 = i+2 by omega]
  ring

/-- Exact return from the binomial coordinates to the literal prime kernels.
Any original prime mask multiplies this equality without a completion. -/
theorem weighted_pair_eq_binomialSum (M : ℕ) (f : ℕ → ℂ) {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hpq : 1 < p*q) (s : ℂ) :
    (∑ i∈Finset.range (M+1), f i*zetaPrimeLogKernel i s p*
      zetaPrimeLogKernel (M-i) s q)=
      zetaPrimeLogKernel M s (p*q)*
        binomialSum M (log p/log (p*q : ℕ) : ℝ) f := by
  unfold binomialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hle : i ≤ M := by simpa using Finset.mem_range.mp hi
  have he := ZetaRieszSkewAllocation.split_mass_kernel M i p q hle hp hq hpq s
  rw [mul_assoc,←he]
  simp only [ZetaRieszJointAllocation.mass,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_natCast]
  ring

/-- The literal central-order indicator. Its jumps are never discarded. -/
def centralIndicator (M K i : ℕ) : ℂ := if K < i ∧ K < M-i then 1 else 0

/-- The four possible second-difference boundaries of the exact indicator. -/
def centralJumps (M K : ℕ) : Finset ℕ := {K-1,K,M-K-2,M-K-1}

/-- Away from these FOUR original boundaries, the mask's second difference
is exactly zero, not a variation allowance. -/
theorem centralIndicator_second_difference_zero {M K i : ℕ}
    (hK : 0 < K) (hMK : 2*K+3 ≤ M) (hi : i∉centralJumps M K) :
    orderSecondDifference (centralIndicator M K) i = 0 := by
  have hj : i≠K-1 ∧ i≠K ∧ i≠M-K-2 ∧ i≠M-K-1 := by
    simpa only [centralJumps,Finset.mem_insert,Finset.mem_singleton,
      not_or] using hi
  have hc0 : (K < i ∧ K < M-i) ↔ (K < i+1 ∧ K < M-(i+1)) := by omega
  have hc1 : (K < i+1 ∧ K < M-(i+1)) ↔ (K < i+2 ∧ K < M-(i+2)) := by omega
  unfold orderSecondDifference centralIndicator
  simp only [←hc1,←hc0]
  split_ifs <;> norm_num

/-- The actual degree N+1 joined order weight: both prefix endpoints and
the logged two-prime trace have already been collected algebraically. -/
def firstOrderWeight (N K i : ℕ) : ℂ :=
  2*(i : ℂ)*((N+1 : ℂ)-i)/(N : ℂ)+(N+1)*centralIndicator (N+1) K i

/-- In the first joined degree the ONLY nonconstant second curvature lies
on the literal four-jump mask; the polynomial part is exact. -/
theorem firstOrderWeight_second_difference (N K i : ℕ) :
    orderSecondDifference (firstOrderWeight N K) i=
      -(4 : ℂ)/(N : ℂ)+(N+1)*orderSecondDifference (centralIndicator (N+1) K) i := by
  simp only [orderSecondDifference,firstOrderWeight]
  push_cast
  ring

/-- The degree N+2 weight retains the exact joined endpoint cancellation. -/
def secondOrderWeight (N K : ℕ) (L : ℂ) (i : ℕ) : ℂ :=
  -(N+1 : ℂ)/L*(if K < i ∧ K < N+2-i then (N+2 : ℂ)
    else ((min i (N+2-i) : ℕ) : ℂ))

/-- The second joined degree has no bulk order curvature: only the exact
four prefix boundaries can survive. -/
theorem secondOrderWeight_second_difference_zero {N K i : ℕ}
    (hK : 0 < K) (hNK : 2*K+3 ≤ N+2) (hiN : i+2 ≤ N+2)
    (hi : i∉centralJumps (N+2) K) (L : ℂ) :
    orderSecondDifference (secondOrderWeight N K L) i = 0 := by
  have hj : i≠K-1 ∧ i≠K ∧ i≠N+2-K-2 ∧ i≠N+2-K-1 := by
    simpa only [centralJumps,Finset.mem_insert,Finset.mem_singleton,
      not_or] using hi
  have hcases : i+2 ≤ K ∨ N+2-K ≤ i ∨ (K < i ∧ i+2 < N+2-K) := by omega
  have hlo (j : ℕ) (hj : j ≤ K) :
      secondOrderWeight N K L j=-(N+1 : ℂ)/L*(j : ℂ) := by
    unfold secondOrderWeight
    rw [if_neg (by omega),Nat.min_eq_left (by omega)]
  have hhi (j : ℕ) (hj : N+2-K ≤ j) (hjN : j ≤ N+2) :
      secondOrderWeight N K L j=-(N+1 : ℂ)/L*((N+2 : ℂ)-(j : ℂ)) := by
    unfold secondOrderWeight
    rw [if_neg (by omega),Nat.min_eq_right (by omega),Nat.cast_sub hjN]
    push_cast
    rfl
  have hmid (j : ℕ) (hj : K < j) (hjN : j < N+2-K) :
      secondOrderWeight N K L j=-(N+1 : ℂ)/L*(N+2) := by
    unfold secondOrderWeight
    rw [if_pos (by omega)]
  rcases hcases with hl|hh|hm
  · unfold orderSecondDifference
    rw [hlo (i+2) hl,hlo (i+1) (by omega),hlo i (by omega)]
    push_cast
    ring
  · unfold orderSecondDifference
    rw [hhi (i+2) (by omega) hiN,hhi (i+1) (by omega) (by omega),
      hhi i hh (by omega)]
    push_cast
    ring
  · unfold orderSecondDifference
    rw [hmid (i+2) (by omega) hm.2,hmid (i+1) (by omega) (by omega),
      hmid i hm.1 (by omega)]
    ring

/-- Reflection of the same factorial row, with the weight retained. -/
theorem reflected_order_sum (M : ℕ) (c v w : ℕ → ℂ) :
    (∑ i∈Finset.range (M+1), c i*w i*v (M-i))=
      ∑ i∈Finset.range (M+1), c (M-i)*v i*w (M-i) := by
  have he := Finset.sum_range_reflect (fun i => c i*w i*v (M-i)) (M+1)
  simp only [Nat.add_sub_cancel] at he
  rw [←he]
  apply Finset.sum_congr rfl
  intro i hi
  have hiM : i ≤ M := by simpa using Finset.mem_range.mp hi
  rw [Nat.sub_sub_self hiM]
  ring

/-- Collect both swapped central incidences on the original order mask. -/
theorem central_order_sum (M K : ℕ) (v w : ℕ → ℂ) :
    (∑ i∈ZetaRieszPairPrefixConvolution.centralOrders M K,
      (v i*w (M-i)+w i*v (M-i)))=
      2*∑ i∈Finset.range (M+1), centralIndicator M K i*v i*w (M-i) := by
  simp only [ZetaRieszPairPrefixConvolution.centralOrders,Finset.sum_filter,
    Finset.sum_add_distrib]
  have hswap : (∑ i∈Finset.range (M+1),
      if K < i ∧ K < M-i then w i*v (M-i) else 0)=
      ∑ i∈Finset.range (M+1), centralIndicator M K i*v i*w (M-i) := by
    have he := reflected_order_sum M (centralIndicator M K) v w
    have hl : (∑ i∈Finset.range (M+1),
        if K < i ∧ K < M-i then w i*v (M-i) else 0)=
        ∑ i∈Finset.range (M+1), centralIndicator M K i*w i*v (M-i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [centralIndicator]
      split_ifs <;> simp
    rw [hl,he]
    apply Finset.sum_congr rfl
    intro i hi
    have hiM : i ≤ M := by simpa using Finset.mem_range.mp hi
    simp only [centralIndicator,Nat.sub_sub_self hiM,and_comm]
  rw [hswap]
  have hfirst : (∑ i∈Finset.range (M+1),
      if K < i ∧ K < M-i then v i*w (M-i) else 0)=
      ∑ i∈Finset.range (M+1), centralIndicator M K i*v i*w (M-i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [centralIndicator]
    split_ifs <;> simp
  rw [hfirst]
  ring

/-- The two original logged prefixes become a single signed min-weight;
their order-zero terms are exactly zero. -/
theorem outer_order_sum (M K : ℕ) (hMK : 2*K < M) (v w : ℕ → ℂ) :
    (∑ i∈(Finset.range (K+1)).filter (fun i => 0 < i),
      (i : ℂ)*(v i*w (M-i)+w i*v (M-i)))=
      ∑ i∈Finset.range (M+1), (1-centralIndicator M K i)*
        ((min i (M-i) : ℕ) : ℂ)*v i*w (M-i) := by
  have hlow (f : ℕ → ℂ) :
      (∑ i∈Finset.range (M+1), (if i ≤ K then (i : ℂ) else 0)*f i)=
        ∑ i∈(Finset.range (K+1)).filter (fun i => 0 < i), (i : ℂ)*f i := by
    have hset : (Finset.range (M+1)).filter (fun i => i ≤ K) = Finset.range (K+1) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_range]
      omega
    rw [show (∑ i∈Finset.range (M+1), (if i ≤ K then (i : ℂ) else 0)*f i)=
      ∑ i∈Finset.range (M+1), if i ≤ K then (i : ℂ)*f i else 0 by
        apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp,
      ←Finset.sum_filter,hset]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 < i
    · simp [hi]
    · have hi0 : i = 0 := by omega
      subst i
      simp
  have hscalar (i : ℕ) (hi : i ≤ M) :
      (1-centralIndicator M K i)*((min i (M-i) : ℕ) : ℂ)=
        (if i ≤ K then (i : ℂ) else 0)+
        (if M-i ≤ K then ((M-i : ℕ) : ℂ) else 0) := by
    unfold centralIndicator
    by_cases hl : i ≤ K
    · have hh : ¬M-i ≤ K := by omega
      simp [show ¬K < i by omega,hl,hh,Nat.min_eq_left (by omega : i ≤ M-i)]
    · by_cases hh : M-i ≤ K
      · simp [show ¬K < M-i by omega,hl,hh,
          Nat.min_eq_right (by omega : M-i ≤ i)]
      · simp [show K < i by omega,show K < M-i by omega,hl,hh]
  have hswap := reflected_order_sum M (fun i => if i ≤ K then (i : ℂ) else 0) v w
  have hrhs : (∑ i∈Finset.range (M+1), (1-centralIndicator M K i)*
      ((min i (M-i) : ℕ) : ℂ)*v i*w (M-i))=
      (∑ i∈Finset.range (M+1), (if i ≤ K then (i : ℂ) else 0)*v i*w (M-i))+
      ∑ i∈Finset.range (M+1), (if M-i ≤ K then ((M-i : ℕ) : ℂ) else 0)*v i*w (M-i) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hscalar i (by simpa using Finset.mem_range.mp hi)]
    ring
  rw [hrhs,←hswap]
  simp only [mul_assoc] at hlow ⊢
  rw [hlow,hlow]
  simp only [Finset.sum_add_distrib,mul_add]

/-- Exact collection of both joined degrees before factorial differencing. -/
theorem collected_order_weights (N K : ℕ) (hK : 2*K < N+1) (L : ℂ)
    (v w : ℕ → ℂ) :
    (N+1 : ℂ)/2*(∑ i∈ZetaRieszPairPrefixConvolution.centralOrders (N+1) K,
      (v i*w (N+1-i)+w i*v (N+1-i)))-
      (N+1 : ℂ)*(N+2)/(2*L)*
        (∑ i∈ZetaRieszPairPrefixConvolution.centralOrders (N+2) K,
          (v i*w (N+2-i)+w i*v (N+2-i)))-
      (N+1 : ℂ)/L*(∑ i∈(Finset.range (K+1)).filter (fun i => 0 < i),
        (i : ℂ)*(v i*w (N+2-i)+w i*v (N+2-i)))+
      (∑ i∈Finset.range (N+2),
        2*(i : ℂ)*((N+1 : ℂ)-i)/(N : ℂ)*v i*w (N+1-i))=
    (∑ i∈Finset.range (N+2), firstOrderWeight N K i*v i*w (N+1-i))+
      ∑ i∈Finset.range (N+3), secondOrderWeight N K L i*v i*w (N+2-i) := by
  rw [central_order_sum,central_order_sum,outer_order_sum _ _ (by omega) v w]
  have hf : (∑ i∈Finset.range (N+2), firstOrderWeight N K i*v i*w (N+1-i))=
      (∑ i∈Finset.range (N+2), 2*(i : ℂ)*((N+1 : ℂ)-i)/(N : ℂ)*v i*w (N+1-i))+
      (N+1 : ℂ)*(∑ i∈Finset.range (N+2), centralIndicator (N+1) K i*v i*w (N+1-i)) := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [firstOrderWeight]
    ring
  have hs : (∑ i∈Finset.range (N+3), secondOrderWeight N K L i*v i*w (N+2-i))=
      -(N+1 : ℂ)/L*(N+2)*
        (∑ i∈Finset.range (N+3), centralIndicator (N+2) K i*v i*w (N+2-i))-
      (N+1 : ℂ)/L*(∑ i∈Finset.range (N+3), (1-centralIndicator (N+2) K i)*
        ((min i (N+2-i) : ℕ) : ℂ)*v i*w (N+2-i)) := by
    simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [secondOrderWeight,centralIndicator]
    split_ifs <;> ring
  rw [hf,hs]
  ring

/-- The collected polynomial trace is exactly the original signed Selberg
pair term, with the full phase and the same pair unchanged. -/
theorem trace_order_sum {N : ℕ} (hN : 0 < N) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (s : ℂ) :
    (∑ i∈Finset.range (N+2), 2*(i : ℂ)*((N+1 : ℂ)-i)/(N : ℂ)*
      zetaPrimeLogKernel i s p*zetaPrimeLogKernel (N+1-i) s q)=
      -ZetaRieszLowCountSelbergAudit.selbergCoefficient (p*q)*
        zetaPrimeLogKernel N s (p*q) := by
  have hpair : 1 < p*q := by nlinarith [hp.two_le,hq.two_le]
  let a : ℝ := log p/log (p*q : ℕ)
  rw [weighted_pair_eq_binomialSum _ _ hp.pos hq.pos hpair s]
  have hb : binomialSum (N+1) (a : ℂ)
      (fun i => (i : ℂ)*((N+1 : ℂ)-i)) = (N+1 : ℂ)*N*(a : ℂ)*(1-a) := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    simpa only [Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one,add_assoc,
      one_add_one_eq_two] using binomialSum_cross_moment n (a : ℂ)
  have hscale : binomialSum (N+1) (a : ℂ)
      (fun i => 2*(i : ℂ)*((N+1 : ℂ)-i)/(N : ℂ))=
      2/(N : ℂ)*binomialSum (N+1) (a : ℂ)
        (fun i => (i : ℂ)*((N+1 : ℂ)-i)) := by
    simp only [binomialSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change zetaPrimeLogKernel (N+1) s (p*q)*binomialSum (N+1) (a : ℂ) _ = _
  rw [hscale,hb,ZetaRieszSignedSelbergPayment.selbergCoefficient_pair_ne hp hq hpq]
  have hlog : log (p*q : ℕ) = log p+log q := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast hq.ne_zero)]
  have hT : (log (p*q : ℕ) : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hpair)).ne'
  have hNC : (N : ℂ)≠0 := by exact_mod_cast hN.ne'
  have hc : 1-(a : ℂ) = (log q : ℂ)/(log (p*q : ℕ) : ℂ) := by
    dsimp [a]
    rw [Complex.ofReal_div]
    field_simp [hT]
    have hlogC : (log (p*q : ℕ) : ℂ) = (log p : ℂ)+(log q : ℂ) := by
      rw [hlog,Complex.ofReal_add]
    linear_combination hlogC
  rw [hc]
  dsimp [a]
  simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_neg,
    Complex.ofReal_ofNat]
  have hk := ZetaRieszHeadOrders.log_mul_kernel N (p*q) s
  simp only [Nat.cast_add,Nat.cast_one] at hk
  field_simp [hT,hNC]
  linear_combination -((log p : ℂ)*(log q : ℂ))*hk

/-- This is the actual literal joined pair coefficient, with no additional
completion, prime mask or native-order replacement. The original distinct
pair condition is explicit. -/
theorem literal_joined_atom_collected {N : ℕ} (hN : 0 < N) {L : ℝ} (hL : L≠0)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (s : ℂ) :
    ((ZetaRieszPairPrefixPayment.prefixLogCoefficient N L (log p) (log q) : ℂ)-
      ZetaRieszLowCountSelbergAudit.selbergCoefficient (p*q))*
        zetaPrimeLogKernel N s (p*q)=
      (∑ i∈Finset.range (N+2), firstOrderWeight N (13*N/32) i*
        zetaPrimeLogKernel i s p*zetaPrimeLogKernel (N+1-i) s q)+
      ∑ i∈Finset.range (N+3), secondOrderWeight N (13*N/32) L i*
        zetaPrimeLogKernel i s p*zetaPrimeLogKernel (N+2-i) s q := by
  have hpair : 1 < p*q := by nlinarith [hp.two_le,hq.two_le]
  have hprefix := ZetaRieszPairPrefixConvolution.prefix_atom_eq_central_logged
    N L hL p q hp.pos hq.pos hpair s
  have he := collected_order_weights N (13*N/32) (by omega) (L : ℂ)
    (fun i => zetaPrimeLogKernel i s p) (fun i => zetaPrimeLogKernel i s q)
  rw [←hprefix,trace_order_sum hN hp hq hpq s] at he
  linear_combination he

/-- The two neighbouring factorial degrees share only FIVE possible mask
curvature boundaries. This is not a support claim for the whole response. -/
def joinedJumps (N K : ℕ) : Finset ℕ := {K-1,K,N-K-1,N-K,N-K+1}

/-- Every other order retains only the exact polynomial curvature; no
absolute mask variation or endpoint completion enters this statement. -/
theorem joined_weights_second_difference_off {N K i : ℕ}
    (hK : 0 < K) (hN : 2*K+3 ≤ N+1) (hiN : i+2 ≤ N+1)
    (hi : i∉joinedJumps N K) (L : ℂ) :
    orderSecondDifference (firstOrderWeight N K) i=-(4 : ℂ)/(N : ℂ) ∧
    orderSecondDifference (secondOrderWeight N K L) i = 0 := by
  have hi0 : i∉centralJumps (N+1) K := by
    simp only [joinedJumps,centralJumps,Finset.mem_insert,Finset.mem_singleton,
      not_or] at hi ⊢
    omega
  have hi1 : i∉centralJumps (N+2) K := by
    simp only [joinedJumps,centralJumps,Finset.mem_insert,Finset.mem_singleton,
      not_or] at hi ⊢
    omega
  rw [firstOrderWeight_second_difference,
    centralIndicator_second_difference_zero hK hN hi0,mul_zero,add_zero]
  exact ⟨rfl,secondOrderWeight_second_difference_zero hK (by omega) (by omega) hi1 L⟩

end RiemannGaussian.ZetaRieszJointSecondDifference
