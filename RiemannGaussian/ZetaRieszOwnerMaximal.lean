/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnerVariation
import RiemannGaussian.ZetaRieszCrossCutoff
import RiemannGaussian.FiniteAbelVariation

/-!
# Joint bounds with the actual varying owner allocation

The unpaid factorial orders form one literal interval. Its two binomial
cumulative functions control allocation variation before the signed cutoff
family is bounded. No cofactor or prime series is completed.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszOwnerMaximal
open ZetaRieszJointAllocation

/-- The original unpaid order selection is exactly one integer interval. -/
theorem unpaidOrders_eq (N : ℕ) : ZetaRieszWingHighOrders.unpaidOrders N =
    Finset.Icc (N/5+2) (13*N/32) := by
  ext k
  simp only [ZetaRieszWingHighOrders.unpaidOrders, ZetaRieszReflectedCompletion.lowerWing,
    ZetaRieszPairOrders.middleOrders, ZetaRieszWingReserve.reserveOrders,
    ZetaRieszWingHighOrders.highOrders, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_range, Finset.mem_Icc]
  omega

/-- A binomial cumulative mass used only to bound the original allocation. -/
def lowerMass (n k : ℕ) (x : ℝ) : ℝ := ∑ j ∈ Finset.range (k+1), mass n j x

private theorem derivative_prefix (n k : ℕ) :
    Polynomial.derivative (∑ j ∈ Finset.range (k+1), bernsteinPolynomial ℝ n j) =
      -(n : Polynomial ℝ)*bernsteinPolynomial ℝ (n-1) k := by
  induction k with
  | zero => simp [bernsteinPolynomial.derivative_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ,Polynomial.derivative_add,ih,
      bernsteinPolynomial.derivative_succ]
    ring

/-- The exact derivative telescopes to a single endpoint mass. -/
theorem hasDerivAt_lowerMass (n k : ℕ) (x : ℝ) :
    HasDerivAt (lowerMass n k) (-(n : ℝ)*mass (n-1) k x) x := by
  change HasDerivAt (fun y => ∑ j ∈ Finset.range (k+1), mass n j y) _ x
  have hd := (∑ j ∈ Finset.range (k+1), bernsteinPolynomial ℝ n j).hasDerivAt x
  rw [derivative_prefix] at hd
  simpa [lowerMass,mass,bernsteinPolynomial,Polynomial.eval_finsetSum,
    mul_assoc,mul_comm,mul_left_comm] using hd

/-- Each cumulative mass decreases with the cofactor share. -/
theorem lowerMass_antitone (n k : ℕ) : AntitoneOn (lowerMass n k) (Set.Icc (0 : ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (fun x _ => (hasDerivAt_lowerMass n k x).continuousAt.continuousWithinAt)
  · intro x _
    exact (hasDerivAt_lowerMass n k x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hasDerivAt_lowerMass n k x).deriv]
    have hx' := interior_subset hx
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n))
      (mass_nonneg (n-1) k hx'.1 hx'.2)

/-- The cumulative mass is a probability, including cutoffs beyond its degree. -/
theorem lowerMass_bounds (n k : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ lowerMass n k x ∧ lowerMass n k x ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun j _ => mass_nonneg n j hx hx1),?_⟩
  by_cases hk : k ≤ n
  · exact (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega : k+1 ≤ n+1))
      (fun j _ _ => mass_nonneg n j hx hx1)).trans_eq (mass_total n x)
  · have he : lowerMass n k x = ∑ j ∈ Finset.range (n+1), mass n j x := by
      unfold lowerMass
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega : n+1 ≤ k+1))
      intro j _ hj
      have hjn : n < j := by simp only [Finset.mem_range] at hj; omega
      simp [mass,Nat.choose_eq_zero_of_lt hjn]
    rw [he,mass_total]

/-- The actual owner interval equals the difference of its two cumulative
masses, with its original integer endpoints unchanged. -/
theorem ownerMass_eq_difference {N : ℕ} (hN : 32 ≤ N) (x : ℝ) :
    (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x) =
      lowerMass (N+1) (13*N/32) x-lowerMass (N+1) (N/5+1) x := by
  rw [unpaidOrders_eq,lowerMass,lowerMass]
  have he : Finset.Icc (N/5+2) (13*N/32) = Finset.Ico (N/5+2) (13*N/32+1) := by
    ext k
    simp only [Finset.mem_Icc,Finset.mem_Ico]
    omega
  rw [he,Finset.sum_Ico_eq_sub _ (by omega : N/5+2 ≤ 13*N/32+1)]

/-- The literal unassigned single-owner factorial weight. -/
def ownerWeight (N : ℕ) (x : ℝ) : ℝ :=
  1-∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x

/-- No owner allocation is removed or estimated by a limiting share. -/
theorem ownerWeight_bounds (N : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ ownerWeight N x ∧ ownerWeight N x ≤ 1 := by
  have hn : 0 ≤ ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x :=
    Finset.sum_nonneg (fun k _ => mass_nonneg (N+1) k hx hx1)
  have hs : ZetaRieszWingHighOrders.unpaidOrders N ⊆ Finset.range (N+1+1) := by
    intro k hk
    have hk' := (ZetaRieszWingHighOrders.unpaidOrders_support hk).1
    have := ZetaRieszReflectedCompletion.lowerWing_bounds hk'
    simp only [Finset.mem_range]
    omega
  have hu := (Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun k _ _ => mass_nonneg (N+1) k hx hx1)).trans_eq (mass_total (N+1) x)
  dsimp [ownerWeight]
  constructor <;> linarith

/-- The total variation of the ACTUAL unpaid owner weight is at most two
along any decreasing list of cofactor shares. There is no order/count factor. -/
theorem ownerWeight_variation_le_two {N : ℕ} (hN : 32 ≤ N) (m : ℕ) (x : ℕ → ℝ)
    (hx : ∀ i ≤ m, x i ∈ Set.Icc (0 : ℝ) 1)
    (hdec : ∀ i < m, x (i+1) ≤ x i) :
    (∑ i ∈ Finset.range m, |ownerWeight N (x i)-ownerWeight N (x (i+1))|) ≤ 2 := by
  let H := fun i => lowerMass (N+1) (13*N/32) (x i)
  let L := fun i => lowerMass (N+1) (N/5+1) (x i)
  have hH i (hi : i < m) : H i ≤ H (i+1) :=
    lowerMass_antitone _ _ (hx (i+1) (by omega)) (hx i (by omega)) (hdec i hi)
  have hL i (hi : i < m) : L i ≤ L (i+1) :=
    lowerMass_antitone _ _ (hx (i+1) (by omega)) (hx i (by omega)) (hdec i hi)
  have he i : ownerWeight N (x i) = 1-H i+L i := by
    rw [ownerWeight,ownerMass_eq_difference hN]
    dsimp [H,L]
    ring
  have hp i (hi : i ∈ Finset.range m) :
      |ownerWeight N (x i)-ownerWeight N (x (i+1))| ≤
        (H (i+1)-H i)+(L (i+1)-L i) := by
    rw [he i,he (i+1)]
    have hh := hH i (Finset.mem_range.mp hi)
    have hl := hL i (Finset.mem_range.mp hi)
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  calc
    _ ≤ ∑ i ∈ Finset.range m, ((H (i+1)-H i)+(L (i+1)-L i)) := Finset.sum_le_sum hp
    _ = (H m-H 0)+(L m-L 0) := by rw [Finset.sum_add_distrib,Finset.sum_range_sub,Finset.sum_range_sub]
    _ ≤ 2 := by
      have hH0 := lowerMass_bounds (N+1) (13*N/32) (hx 0 (by omega)).1 (hx 0 (by omega)).2
      have hHm := lowerMass_bounds (N+1) (13*N/32) (hx m le_rfl).1 (hx m le_rfl).2
      have hL0 := lowerMass_bounds (N+1) (N/5+1) (hx 0 (by omega)).1 (hx 0 (by omega)).2
      have hLm := lowerMass_bounds (N+1) (N/5+1) (hx m le_rfl).1 (hx m le_rfl).2
      dsimp [H,L]
      linarith only [hH0.1,hHm.2,hL0.1,hLm.2]

/-- Signed partial-sum cancellation survives the exact varying owner factor
at cost at most three, independently of every order and cofactor share. -/
theorem owner_weighted_partial_bound {N : ℕ} (hN : 32 ≤ N) (m : ℕ)
    (x : ℕ → ℝ) (z : ℕ → ℂ) {B : ℝ}
    (hx : ∀ i ≤ m, x i ∈ Set.Icc (0 : ℝ) 1)
    (hdec : ∀ i < m, x (i+1) ≤ x i)
    (hB : ∀ k ≤ m, ‖∑ i ∈ Finset.range (k+1), z i‖ ≤ B) :
    ‖∑ i ∈ Finset.range (m+1), (ownerWeight N (x i) : ℂ)*z i‖ ≤ 3*B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by omega))
  have hw := ownerWeight_bounds N (hx m le_rfl).1 (hx m le_rfl).2
  have hv := ownerWeight_variation_le_two hN m x hx hdec
  have ht : ‖(ownerWeight N (x m) : ℂ)‖+
      (∑ i ∈ Finset.range m, ‖(ownerWeight N (x i) : ℂ)-(ownerWeight N (x (i+1)) : ℂ)‖) ≤ 3 := by
    simp_rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_nonneg hw.1]
    linarith only [hw.2,hv]
  exact (FiniteAbelVariation.weighted_bound (fun i => (ownerWeight N (x i) : ℂ)) z m hB).trans
    (by nlinarith [mul_le_mul_of_nonneg_left ht hB0])

/-- Sum of the actual block costs in a finite binary subdivision. This is
an error budget for partial sums, not a replacement arithmetic carrier. -/
def dyadicCost (F : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, o => F o 1
  | b+1, o => F o (2^(b+1))+dyadicCost F b o+dyadicCost F b (o+2^b)

private theorem dyadicCost_nonneg (F : ℕ → ℕ → ℝ)
    (hF : ∀ o m, 0 ≤ F o m) (b o : ℕ) : 0 ≤ dyadicCost F b o := by
  induction b generalizing o with
  | zero => exact hF _ _
  | succ b ih => simp only [dyadicCost]; exact add_nonneg (add_nonneg (hF _ _) (ih _)) (ih _)

private theorem root_le_dyadicCost (F : ℕ → ℕ → ℝ)
    (hF : ∀ o m, 0 ≤ F o m) (b o : ℕ) : F o (2^b) ≤ dyadicCost F b o := by
  cases b with
  | zero => simp [dyadicCost]
  | succ b =>
    dsimp only [dyadicCost]
    linarith only [dyadicCost_nonneg F hF b o,dyadicCost_nonneg F hF b (o+2^b)]

private theorem weighted_two_square {x y E c : ℝ} (hc : 0 < c) (hy : y^2 ≤ c*E) :
    (x+y)^2 ≤ (c+1)*(x^2+E) := by
  apply le_of_mul_le_mul_left (a := c) ?_ hc
  nlinarith [sq_nonneg (c*x-y),mul_nonneg (show 0 ≤ c+1 by linarith) (sub_nonneg.mpr hy)]

/-- Every prefix is controlled by only one block per binary level.
The price is the number of levels, not the number of periods. -/
theorem prefix_sq_le_dyadicCost (f : ℕ → ℝ) (b o : ℕ) {j : ℕ} (hj : j ≤ 2^b) :
    (∑ i ∈ Finset.Ico o (o+j), f i)^2 ≤
      ((b+1 : ℕ) : ℝ)*dyadicCost (fun a m => (∑ i ∈ Finset.Ico a (a+m), f i)^2) b o := by
  let F := fun a m => (∑ i ∈ Finset.Ico a (a+m), f i)^2
  have hF a m : 0 ≤ F a m := sq_nonneg _
  change _ ≤ _*dyadicCost F b o
  induction b generalizing o j with
  | zero =>
    have hj' : j = 0 ∨ j = 1 := by simp only [pow_zero] at hj; omega
    rcases hj' with rfl | rfl
    · simp only [Nat.add_zero,Finset.Ico_self,Finset.sum_empty,zero_pow (by omega : 2 ≠ 0)]
      exact mul_nonneg (by positivity) (dyadicCost_nonneg F hF 0 o)
    · simp [dyadicCost,F]
  | succ b ih =>
    have hpow : 2^(b+1) = 2^b+2^b := by rw [pow_succ]; omega
    have hleft := dyadicCost_nonneg F hF b o
    have hright := dyadicCost_nonneg F hF b (o+2^b)
    have hroot := hF o (2^(b+1))
    by_cases hjl : j ≤ 2^b
    · have h := ih o hjl
      simp only [dyadicCost]
      push_cast at h ⊢
      nlinarith [mul_nonneg (show 0 ≤ (b : ℝ)+2 by positivity) hroot,
        mul_nonneg (show 0 ≤ (b : ℝ)+2 by positivity) hright]
    · have hjr : j-2^b ≤ 2^b := by rw [hpow] at hj; omega
      have hi := ih (o+2^b) hjr
      have he : o+2^b+(j-2^b) = o+j := by omega
      rw [he] at hi
      have hs := (Finset.sum_Ico_consecutive f
        (show o ≤ o+2^b by omega) (show o+2^b ≤ o+j by omega)).symm
      rw [hs]
      have hsq := weighted_two_square (x := ∑ i ∈ Finset.Ico o (o+2^b), f i)
        (by positivity : (0 : ℝ) < ((b+1 : ℕ) : ℝ)) hi
      have hfull := root_le_dyadicCost F hF b o
      change (∑ i ∈ Finset.Ico o (o+2^b), f i)^2 ≤ _ at hfull
      simp only [dyadicCost]
      push_cast at hsq ⊢
      nlinarith [mul_le_mul_of_nonneg_left hfull (show 0 ≤ (b : ℝ)+2 by positivity),
        mul_nonneg (show 0 ≤ (b : ℝ)+2 by positivity) hroot]

private theorem dyadicCost_mono (F G : ℕ → ℕ → ℝ) (M b o : ℕ)
    (ho : o+2^b ≤ M) (hFG : ∀ a m, a+m ≤ M → F a m ≤ G a m) :
    dyadicCost F b o ≤ dyadicCost G b o := by
  induction b generalizing o with
  | zero => exact hFG o 1 (by simpa using ho)
  | succ b ih =>
    have hp : 2^(b+1) = 2^b+2^b := by rw [pow_succ]; omega
    have hl : o+2^b ≤ M := (Nat.add_le_add_left (Nat.le_add_right (2^b) (2^b)) o).trans
      (by simpa only [hp] using ho)
    have hr : o+2^b+2^b ≤ M := by simpa only [hp,Nat.add_assoc] using ho
    simp only [dyadicCost]
    exact add_le_add (add_le_add (hFG _ _ ho) (ih o hl)) (ih (o+2^b) hr)

private theorem dyadicCost_sum {ι : Type*} (S : Finset ι) (F : ι → ℕ → ℕ → ℝ) (b o : ℕ) :
    (∑ n ∈ S, dyadicCost (F n) b o) = dyadicCost (fun a m => ∑ n ∈ S, F n a m) b o := by
  induction b generalizing o with
  | zero => rfl
  | succ b ih => simp only [dyadicCost,Finset.sum_add_distrib,ih]

private theorem dyadicCost_add (F G : ℕ → ℕ → ℝ) (b o : ℕ) :
    dyadicCost (fun a m => F a m+G a m) b o = dyadicCost F b o+dyadicCost G b o := by
  induction b generalizing o with
  | zero => rfl
  | succ b ih => simp only [dyadicCost,ih]; ring

private theorem dyadicCost_mul (F : ℕ → ℕ → ℝ) (c : ℝ) (b o : ℕ) :
    dyadicCost (fun a m => c*F a m) b o = c*dyadicCost F b o := by
  induction b generalizing o with
  | zero => rfl
  | succ b ih => simp only [dyadicCost,ih]; ring

private theorem dyadicCost_interval_sum (f : ℕ → ℝ) (b o : ℕ) :
    dyadicCost (fun a m => ∑ i ∈ Finset.Ico a (a+m), f i) b o =
      ((b+1 : ℕ) : ℝ)*(∑ i ∈ Finset.Ico o (o+2^b), f i) := by
  induction b generalizing o with
  | zero => simp [dyadicCost]
  | succ b ih =>
    have hp : 2^(b+1) = 2^b+2^b := by rw [pow_succ]; omega
    have hs := Finset.sum_Ico_consecutive f (Nat.le_add_right o (2^b))
      (show o+2^b ≤ o+2^(b+1) by rw [hp]; exact Nat.add_le_add_left (Nat.le_add_right _ _) o)
    simp only [dyadicCost,ih]
    have he : o+2^b+2^b = o+2^(b+1) := by rw [hp]; omega
    rw [he]
    push_cast
    linear_combination ((b : ℝ)+1)*hs

private theorem shifted_sum (f : ℕ → ℝ) (o m : ℕ) :
    (∑ j ∈ Finset.range m, f (o+j)) = ∑ i ∈ Finset.Ico o (o+m), f i := by
  simpa only [Nat.Ico_zero_eq_range,Nat.zero_add,Nat.add_zero,Nat.add_comm] using
    Finset.sum_Ico_add f 0 m o

private theorem interval_sum_le_twice (f : ℕ → ℝ) {M lo hi : ℕ} {B : ℝ}
    (hlo : lo ≤ hi) (hhi : hi ≤ M)
    (hB : ∀ k ≤ M, |∑ i ∈ Finset.range k, f i| ≤ B) :
    |∑ i ∈ Finset.Ico lo hi, f i| ≤ 2*B := by
  rw [Finset.sum_Ico_eq_sub _ hlo]
  exact (abs_sub _ _).trans (by linarith only [hB hi hhi,hB lo (hlo.trans hhi)])

/-- Moving the first and last retained periods costs only two endpoint
partial sums. The true owner allocation then costs at most three more. -/
theorem owner_weighted_interval_bound {N : ℕ} (hN : 32 ≤ N)
    (M lo hi : ℕ) (f x : ℕ → ℝ) {B : ℝ}
    (hlo : lo ≤ hi) (hhi : hi ≤ M)
    (hx : ∀ i ∈ Finset.Ico lo hi, x i ∈ Set.Icc (0 : ℝ) 1)
    (hdec : ∀ i, lo ≤ i → i+1 < hi → x (i+1) ≤ x i)
    (hB : ∀ k ≤ M, |∑ i ∈ Finset.range k, f i| ≤ B) :
    |∑ i ∈ Finset.Ico lo hi, ownerWeight N (x i)*f i| ≤ 6*B := by
  have hB0 : 0 ≤ B := by simpa using hB 0 (Nat.zero_le M)
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hlo
  cases m with
  | zero => simp only [Nat.add_zero,Finset.Ico_self,Finset.sum_empty,abs_zero]; positivity
  | succ m =>
    have hx' i (hi : i ≤ m) : x (lo+i) ∈ Set.Icc (0 : ℝ) 1 :=
      hx _ (Finset.mem_Ico.mpr ⟨by omega,by omega⟩)
    have hd i (hi : i < m) : x (lo+(i+1)) ≤ x (lo+i) := by
      simpa only [Nat.add_assoc] using hdec (lo+i) (by omega) (by omega)
    have hb k (hk : k ≤ m) : ‖∑ j ∈ Finset.range (k+1), (f (lo+j) : ℂ)‖ ≤ 2*B := by
      rw [← Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,shifted_sum]
      exact interval_sum_le_twice f (by omega) (by omega) hB
    have ht := owner_weighted_partial_bound hN m (fun i => x (lo+i))
      (fun i => (f (lo+i) : ℂ)) hx' hd hb
    simp_rw [← Complex.ofReal_mul,← Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs] at ht
    rw [shifted_sum (fun i => ownerWeight N (x i)*f i)] at ht
    simpa only [show (3 : ℝ)*(2*B) = 6*B by ring] using ht

/-- The literal varying allocation and any cofactor-dependent interval
of retained periods are controlled jointly with only logarithmic-depth cost. -/
theorem owner_interval_sq_le_dyadicCost {N : ℕ} (hN : 32 ≤ N)
    (b lo hi : ℕ) (f x : ℕ → ℝ)
    (hlo : lo ≤ hi) (hhi : hi ≤ 2^b)
    (hx : ∀ i ∈ Finset.Ico lo hi, x i ∈ Set.Icc (0 : ℝ) 1)
    (hdec : ∀ i, lo ≤ i → i+1 < hi → x (i+1) ≤ x i) :
    (∑ i ∈ Finset.Ico lo hi, ownerWeight N (x i)*f i)^2 ≤
      36*((b+1 : ℕ) : ℝ)*dyadicCost
        (fun o m => (∑ i ∈ Finset.Ico o (o+m), f i)^2) b 0 := by
  let E := dyadicCost (fun o m => (∑ i ∈ Finset.Ico o (o+m), f i)^2) b 0
  have hE : 0 ≤ E := dyadicCost_nonneg _ (fun _ _ => sq_nonneg _) _ _
  have hcost : 0 ≤ ((b+1 : ℕ) : ℝ)*E := by positivity
  have hp k (hk : k ≤ 2^b) : |∑ i ∈ Finset.range k, f i| ≤
      Real.sqrt (((b+1 : ℕ) : ℝ)*E) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs,Real.sq_sqrt hcost]
    simpa only [Nat.zero_add,Nat.Ico_zero_eq_range] using prefix_sq_le_dyadicCost f b 0 hk
  have h := owner_weighted_interval_bound hN (2^b) lo hi f x hlo hhi hx hdec hp
  have hh := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs,mul_pow,Real.sq_sqrt hcost] at hh
  simpa only [show (6 : ℝ)^2 = 36 by norm_num,mul_assoc,E] using hh

/-- The exact combined divisor coefficient at one binary block. Signs
are retained before the finite integer-floor error is charged. -/
def blockFloorCost (R : ℕ → ℕ) (a : ℕ → ℝ) (o m : ℕ) : ℝ :=
  (∑ d ∈ Finset.Icc 1 ((Finset.Ico o (o+m)).sup R),
    |∑ i ∈ Finset.Ico o (o+m), if d ≤ R i then a i*(μ d : ℝ) else 0|)^2

/-- One independent arithmetic mean bound for varying owner allocations,
arbitrary prime counts, and label-dependent clipped intervals of periods.
The remaining exact binary-block floor cost is displayed, not assumed small. -/
theorem exists_owner_interval_mean_bound {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (b N X Y : ℕ) (S : Finset ℕ) (R : ℕ → ℕ)
      (a : ℕ → ℝ) (x : ℕ → ℕ → ℝ) (lo hi : ℕ → ℕ),
      32 ≤ N → Y ≤ X → S ⊆ Finset.Ioc Y X →
      (∀ i < 2^b, 0 < R i) →
      (∀ (i : ℕ), i < 2^b → ∀ (j : ℕ), j < 2^b →
        h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n), x n i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ n ∈ S, ∀ i, lo n ≤ i → i+1 < hi n → x n (i+1) ≤ x n i) →
      (∑ n ∈ S, (∑ i ∈ Finset.Ico (lo n) (hi n),
        ownerWeight N (x n i)*a i*
          (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0))^2) ≤
        36*((b+1 : ℕ) : ℝ)*
          (E*((X : ℝ)-Y)*((b+1 : ℕ) : ℝ)*(∑ i ∈ Finset.range (2^b), (a i)^2)+
            dyadicCost (blockFloorCost R a) b 0) := by
  obtain ⟨E,hE,hmean⟩ := ZetaRieszCrossCutoff.exists_separated_cancellation_mean_bound hh
  refine ⟨E,hE,fun b N X Y S R a x lo hi hN hYX hS hR hsep hr hx hdec => ?_⟩
  let f := fun n i => a i*(∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0)
  let F := fun n o m => (∑ i ∈ Finset.Ico o (o+m), f n i)^2
  have hs : (∑ n ∈ S, (∑ i ∈ Finset.Ico (lo n) (hi n), ownerWeight N (x n i)*f n i)^2) ≤
      36*((b+1 : ℕ) : ℝ)*(∑ n ∈ S, dyadicCost (F n) b 0) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun n hn => owner_interval_sq_le_dyadicCost hN b (lo n) (hi n)
      (f n) (x n) (hr n hn).1 (hr n hn).2 (hx n hn) (hdec n hn))
  have hb o m (hom : o+m ≤ 2^b) : (∑ n ∈ S, F n o m) ≤
      E*((X : ℝ)-Y)*(∑ i ∈ Finset.Ico o (o+m), (a i)^2)+blockFloorCost R a o m := by
    have hI i (hi : i ∈ Finset.Ico o (o+m)) : i < 2^b := by
      have := (Finset.mem_Ico.mp hi).2
      omega
    exact (Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => sq_nonneg _)).trans
      (hmean (Finset.Ico o (o+m)) R a X Y hYX (fun i hi => hR i (hI i hi))
        (fun i hi j hj => hsep i (hI i hi) j (hI j hj)))
  rw [dyadicCost_sum] at hs
  have hd := dyadicCost_mono (fun o m => ∑ n ∈ S, F n o m)
    (fun o m => E*((X : ℝ)-Y)*(∑ i ∈ Finset.Ico o (o+m), (a i)^2)+blockFloorCost R a o m)
    (2^b) b 0 (by omega) hb
  rw [dyadicCost_add,dyadicCost_mul,dyadicCost_interval_sum] at hd
  simp only [Nat.zero_add,Nat.Ico_zero_eq_range] at hd
  have ht := hs.trans (mul_le_mul_of_nonneg_left hd (by positivity))
  simpa only [f,mul_assoc] using ht

private theorem blockFloorCost_le (R : ℕ → ℕ) (a : ℕ → ℝ) (o m : ℕ) :
    blockFloorCost R a o m ≤ (∑ i ∈ Finset.Ico o (o+m), |a i| *(R i : ℝ))^2 := by
  let I := Finset.Ico o (o+m)
  let M := I.sup R
  have he : (∑ d ∈ Finset.Icc 1 M, |∑ i ∈ I, if d ≤ R i then a i*(μ d : ℝ) else 0|) ≤
      ∑ i ∈ I, |a i| *(R i : ℝ) := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 M, ∑ i ∈ I, if d ≤ R i then |a i| else 0 := by
        apply Finset.sum_le_sum
        intro d _
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro i _
        by_cases hdi : d ≤ R i
        · simp only [if_pos hdi,abs_mul]
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (abs_real_moebius_le_one d) (abs_nonneg (a i))
        · simp [hdi]
      _ ≤ _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_le_sum
        intro i _
        rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
        have hs : (Finset.Icc 1 M).filter (fun d => d ≤ R i) ⊆ Finset.Icc 1 (R i) := by
          intro d hd
          exact Finset.mem_Icc.mpr
            ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1,(Finset.mem_filter.mp hd).2⟩
        have hc : ((Finset.Icc 1 M).filter (fun d => d ≤ R i)).card ≤ R i := by
          simpa using Finset.card_le_card hs
        have hc' : (((Finset.Icc 1 M).filter (fun d => d ≤ R i)).card : ℝ) ≤ R i := by exact_mod_cast hc
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hc' (abs_nonneg (a i))
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) he 2

private theorem dyadicCost_square_sum_le (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (b o : ℕ) :
    dyadicCost (fun a m => (∑ i ∈ Finset.Ico a (a+m), f i)^2) b o ≤
      ((b+1 : ℕ) : ℝ)*(∑ i ∈ Finset.Ico o (o+2^b), f i)^2 := by
  induction b generalizing o with
  | zero => simp [dyadicCost]
  | succ b ih =>
    have hp : 2^(b+1) = 2^b+2^b := by rw [pow_succ]; omega
    have he : o+2^b+2^b = o+2^(b+1) := by rw [hp]; omega
    have hs := Finset.sum_Ico_consecutive f (Nat.le_add_right o (2^b))
      (show o+2^b ≤ o+2^(b+1) by rw [hp]; exact Nat.add_le_add_left (Nat.le_add_right _ _) o)
    have hl := ih o
    have hr := ih (o+2^b)
    rw [he] at hr
    have hprod := mul_nonneg
      (Finset.sum_nonneg (s := Finset.Ico o (o+2^b)) (fun i _ => hf i))
      (Finset.sum_nonneg (s := Finset.Ico (o+2^b) (o+2^(b+1))) (fun i _ => hf i))
    simp only [dyadicCost]
    push_cast at hl hr ⊢
    rw [← hs]
    nlinarith [mul_nonneg (show 0 ≤ (b : ℝ)+1 by positivity) hprod]

/-- Even the coarse bound for all binary-block counting errors costs
only one factor for the number of levels. The sharper signed cost remains
available in the main theorem. -/
theorem dyadic_floor_cost_le (R : ℕ → ℕ) (a : ℕ → ℝ) (b : ℕ) :
    dyadicCost (blockFloorCost R a) b 0 ≤
      ((b+1 : ℕ) : ℝ)*(∑ i ∈ Finset.range (2^b), |a i| *(R i : ℝ))^2 := by
  have h := dyadicCost_mono (blockFloorCost R a)
    (fun o m => (∑ i ∈ Finset.Ico o (o+m), |a i| *(R i : ℝ))^2)
    (2^b) b 0 (by omega) (fun o m _ => blockFloorCost_le R a o m)
  exact h.trans (by simpa only [Nat.zero_add,Nat.Ico_zero_eq_range] using
    dyadicCost_square_sum_le (fun i => |a i| *(R i : ℝ)) (fun _ => by positivity) b 0)

/-- Both one-sided bounds now allow the original owner factor to depend
on the cofactor, and allow both retained period endpoints to move with it. -/
theorem exists_owner_interval_signed_bounds {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (b N X Y : ℕ) (S : Finset ℕ) (R : ℕ → ℕ)
      (a w : ℕ → ℝ) (x : ℕ → ℕ → ℝ) (lo hi : ℕ → ℕ),
      32 ≤ N → Y ≤ X → S ⊆ Finset.Ioc Y X →
      (∀ i < 2^b, 0 < R i) →
      (∀ (i : ℕ), i < 2^b → ∀ (j : ℕ), j < 2^b →
        h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n), x n i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ n ∈ S, ∀ i, lo n ≤ i → i+1 < hi n → x n (i+1) ≤ x n i) →
      let J := ∑ n ∈ S, w n*(∑ i ∈ Finset.Ico (lo n) (hi n),
        ownerWeight N (x n i)*a i*
          (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0));
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*36*((b+1 : ℕ) : ℝ)*
          (E*((X : ℝ)-Y)*((b+1 : ℕ) : ℝ)*(∑ i ∈ Finset.range (2^b), (a i)^2)+
            dyadicCost (blockFloorCost R a) b 0));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_owner_interval_mean_bound hh
  refine ⟨E,hE,fun b N X Y S R a w x lo hi hN hYX hS hR hsep hr hx hd => ?_⟩
  dsimp only
  let F := fun n => ∑ i ∈ Finset.Ico (lo n) (hi n), ownerWeight N (x n i)*a i*
    (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0)
  have hm := hmean b N X Y S R a x lo hi hN hYX hS hR hsep hr hx hd
  have hw : 0 ≤ ∑ n ∈ S, (w n)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsq := (Finset.sum_mul_sq_le_sq_mul_sq S w F).trans
    (mul_le_mul_of_nonneg_left hm hw)
  have hD : 0 ≤ dyadicCost (blockFloorCost R a) b 0 :=
    dyadicCost_nonneg _ (fun _ _ => sq_nonneg _) _ _
  have hl : 0 ≤ (X : ℝ)-Y := sub_nonneg.mpr (by exact_mod_cast hYX)
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs,Real.sq_sqrt (by positivity)]
  simpa only [F,mul_assoc] using hsq

/-- Exact identification with the retained unique-largest-prime
allocation already used by the campaign; no limiting share is substituted. -/
theorem ownerWeight_eq_fibre (A : Finset ℕ) (N : ℕ) {a p : ℕ}
    (ha : Squarefree a) (hc : 2 ≤ a.primeFactors.card) (hp : p.Prime)
    (hmax : ∀ q ∈ a.primeFactors, q < p) (hpA : p ∈ A) :
    ownerWeight N (Real.log a/Real.log (p*a : ℕ)) =
      1-boundedShare (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) N (p*a) := by
  rw [ZetaRieszOwnerVariation.owner_share_fibre A N ha hc hp hmax hpA]
  rfl

/-- The joint bound applies to the original cutoff slopes with literal
cofactor-log owner shares. Radial lengths and the retained interval may
depend on the cofactor. Other coefficient dependence remains explicit. -/
theorem exists_owner_slope_bounds {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (b N X Y : ℕ) (S : Finset ℕ) (R : ℕ → ℕ)
      (D a w : ℕ → ℝ) (T : ℕ → ℕ → ℝ) (lo hi : ℕ → ℕ),
      32 ≤ N → Y ≤ X → S ⊆ Finset.Ioc Y X →
      (∀ i < 2^b, 0 < R i) →
      (∀ i < 2^b, (R i : ℝ) < Real.exp (D i) ∧ Real.exp (D i) ≤ R i+1) →
      (∀ (i : ℕ), i < 2^b → ∀ (j : ℕ), j < 2^b →
        h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n), 0 < T n i ∧ Real.log n ≤ T n i) →
      (∀ n ∈ S, ∀ i, lo n ≤ i → i+1 < hi n → T n i ≤ T n (i+1)) →
      let J := ∑ n ∈ S, w n*(∑ i ∈ Finset.Ico (lo n) (hi n),
        ownerWeight N (Real.log n/T n i)*a i*ZetaRieszGlobalCurvature.cutoffSlope (D i) n);
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*36*((b+1 : ℕ) : ℝ)*
          (E*((X : ℝ)-Y)*((b+1 : ℕ) : ℝ)*(∑ i ∈ Finset.range (2^b), (a i)^2)+
            dyadicCost (blockFloorCost R a) b 0));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_owner_interval_signed_bounds hh
  refine ⟨E,hE,fun b N X Y S R D a w T lo hi hN hYX hS hR hD hsep hr hT hmono => ?_⟩
  let x : ℕ → ℕ → ℝ := fun n i => Real.log n/T n i
  have hx n (hn : n ∈ S) i (hi : i ∈ Finset.Ico (lo n) (hi n)) :
      x n i ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (Real.log_natCast_nonneg n) (hT n hn i hi).1.le,
      (div_le_one (hT n hn i hi).1).mpr (hT n hn i hi).2⟩
  have hd n (hn : n ∈ S) i (hli : lo n ≤ i) (hih : i+1 < hi n) : x n (i+1) ≤ x n i :=
    div_le_div_of_nonneg_left (Real.log_natCast_nonneg n)
      (hT n hn i (Finset.mem_Ico.mpr ⟨hli,by omega⟩)).1 (hmono n hn i hli hih)
  have ht := hbound b N X Y S R a w x lo hi hN hYX hS hR hsep hr hx hd
  dsimp only at ht ⊢
  have he : (∑ n ∈ S, w n*(∑ i ∈ Finset.Ico (lo n) (hi n),
      ownerWeight N (Real.log n/T n i)*a i*ZetaRieszGlobalCurvature.cutoffSlope (D i) n)) =
      ∑ n ∈ S, w n*(∑ i ∈ Finset.Ico (lo n) (hi n), ownerWeight N (x n i)*a i*
        (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    apply Finset.sum_congr rfl
    intro i hi'
    have hiB : i < 2^b := ((Finset.mem_Ico.mp hi').2).trans_le (hr n hn).2
    rw [ZetaRieszCrossCutoff.cutoffSlope_eq_prefix (R i) (D i) (hD i hiB).1 (hD i hiB).2
      (by have := (Finset.mem_Ioc.mp (hS hn)).1; omega)]
  rw [he]
  exact ht

/-- For the actual ordered prime fibre, partial-sum cancellation before
allocation survives its EXACT owner weight at constant cost. This retains
the complete complex phase and the signed Riesz coefficient; the needed
raw partial-sum bound is an explicit premise, not asserted here. -/
theorem literal_owner_prime_partial_bound (A : Finset ℕ) {N : ℕ} (hN : 32 ≤ N)
    (m : ℕ) (L y : ℝ) {a : ℕ} (ha : Squarefree a) (hc : 2 ≤ a.primeFactors.card)
    (p : ℕ → ℕ)
    (hp : ∀ i ≤ m, (p i).Prime ∧ p i ∈ A ∧ ∀ q ∈ a.primeFactors, q < p i)
    (hmono : ∀ i < m, p i ≤ p (i+1)) {B : ℝ}
    (hB : ∀ k ≤ m, ‖∑ i ∈ Finset.range (k+1),
      SquarefreeVaughanLogSource.coefficient L (p i*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p i*a)‖ ≤ B) :
    ‖∑ i ∈ Finset.range (m+1), residualCoefficient (A ∩ {p i}) L N (p i*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p i*a)‖ ≤ 3*B := by
  let x := fun i => Real.log a/Real.log (p i*a : ℕ)
  let z := fun i => SquarefreeVaughanLogSource.coefficient L (p i*a)*
    zetaPrimeLogKernel N (3/2+Complex.I*y) (p i*a)
  have ha0 : 0 < a := Nat.pos_of_ne_zero ha.ne_zero
  have hlog i (hi : i ≤ m) : 0 < Real.log (p i*a : ℕ) ∧ Real.log a ≤ Real.log (p i*a : ℕ) := by
    have hpa : 2 ≤ p i*a := (hp i hi).1.two_le.trans
      (by simpa only [mul_one] using Nat.mul_le_mul_left (p i) (show 1 ≤ a by omega))
    refine ⟨Real.log_pos (by exact_mod_cast (show 1 < p i*a by omega)),?_⟩
    exact Real.log_le_log (by exact_mod_cast ha0)
      (by exact_mod_cast Nat.le_mul_of_pos_left a (hp i hi).1.pos)
  have hx i (hi : i ≤ m) : x i ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (Real.log_natCast_nonneg a) (hlog i hi).1.le,
      (div_le_one (hlog i hi).1).mpr (hlog i hi).2⟩
  have hd i (hi : i < m) : x (i+1) ≤ x i := by
    apply div_le_div_of_nonneg_left (Real.log_natCast_nonneg a) (hlog i (by omega)).1
    apply Real.log_le_log (by exact_mod_cast Nat.mul_pos (hp i (by omega)).1.pos ha0)
    exact_mod_cast Nat.mul_le_mul_right a (hmono i hi)
  have ht := owner_weighted_partial_bound hN m x z hx hd hB
  have he : (∑ i ∈ Finset.range (m+1), residualCoefficient (A ∩ {p i}) L N (p i*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p i*a)) =
      ∑ i ∈ Finset.range (m+1), (ownerWeight N (x i) : ℂ)*z i := by
    apply Finset.sum_congr rfl
    intro i hi
    have him : i ≤ m := by have := Finset.mem_range.mp hi; omega
    have hw := ownerWeight_eq_fibre A N ha hc (hp i him).1 (hp i him).2.2 (hp i him).2.1
    rw [ZetaRieszPrimeIntervals.largestPrime_mul (p i) a (hp i him).1 ha.ne_zero (hp i him).2.2] at hw
    dsimp only [x,z]
    rw [residualCoefficient,hw,mul_assoc]
  rw [he]
  exact ht

end RiemannGaussian.ZetaRieszOwnerMaximal
