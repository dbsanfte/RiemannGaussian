/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszShiftedAllocation
import RiemannGaussian.ZetaRieszParityGoodPhase
import RiemannGaussian.ZetaRieszCausalSurface

/-!
# Joint shifted configurations and the two cutoff clocks

Subset configurations are summed with their signs before any estimate.
The identities allow arbitrary finite masks, including zero/one orders.
The Riesz cutoff is not rescaled when a factorial prime leg is shifted.
Consequently cancellation of the one-variable logarithmic pole is not
cancellation of its two-variable count factor.
-/

namespace RiemannGaussian.ZetaRieszJointShift
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Classical
open ZetaRieszShiftedCenter

/-- Every nonempty shifted configuration, with its exact inclusion sign. -/
def correction {ι : Type*} (S : Finset ι) (f g : ι → ℂ) : ℂ :=
  -∑ B ∈ S.powerset.erase ∅,
    (-1 : ℂ)^B.card*(∏ i ∈ S \ B, f i)*∏ i ∈ B, g i

/-- The joint identity holds before a phase or a share mask is estimated. -/
theorem product_joint {ι : Type*} (S : Finset ι) (f g : ι → ℂ) :
    (∏ i ∈ S, (f i-g i))+correction S f g = ∏ i ∈ S, f i := by
  rw [Finset.prod_sub, correction,
    ← S.powerset.add_sum_erase _ (Finset.empty_mem_powerset S)]
  simp

/-- All label-dependent and order-dependent masks remain inside W. -/
theorem masked_joint {ι κ : Type*} (D : Finset κ) (S : κ → Finset ι)
    (W : κ → ℂ) (f g : κ → ι → ℂ) :
    (∑ d ∈ D, W d*∏ i ∈ S d, (f d i-g d i))+
      (∑ d ∈ D, W d*correction (S d) (f d) (g d)) =
        ∑ d ∈ D, W d*∏ i ∈ S d, f d i := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun d _ => by rw [← mul_add, product_joint])

/-- Summing the factorial orders first gives an exact complex tilted
multinomial. Orders zero and one are included, without exceptional sets. -/
theorem factorial_subset_sum {ι : Type*} (S B : Finset ι) (x : ι → ℂ) (C : ℂ) (M : ℕ) :
    (∑ d ∈ Finset.piAntidiag S M, (Nat.multinomial S d : ℂ)*
      ∏ i ∈ S, x i^(d i)*(if i ∈ B then C^(d i) else 1)) =
        (∑ i ∈ S, x i*(if i ∈ B then C else 1))^M := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp [mul_pow]

/-- The full factorial tilt depends on the TOTAL selected log share;
separate worst-order estimates discard this exact coupling. -/
theorem factorial_subset_normalized {ι : Type*} (S B : Finset ι) (x : ι → ℂ)
    (C : ℂ) (M : ℕ) (hB : B ⊆ S) (hx : ∑ i ∈ S, x i = 1) :
    (∑ d ∈ Finset.piAntidiag S M, (Nat.multinomial S d : ℂ)*
      ∏ i ∈ S, x i^(d i)*(if i ∈ B then C^(d i) else 1)) =
        (1+(C-1)*∑ i ∈ B, x i)^M := by
  rw [factorial_subset_sum]
  congr 1
  have hid (i : ι) : x i*(if i ∈ B then C else 1) =
      x i+(C-1)*(if i ∈ B then x i else 0) := by split_ifs <;> ring
  simp_rw [hid]
  rw [Finset.sum_add_distrib, hx, ← Finset.mul_sum, ← Finset.sum_filter]
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hB]

/-- Literal positive-order prime legs, including the totalized order zero.
This is an exact finite arithmetic identity, not a completed-leg limit. -/
theorem arithmetic_joint (A : Finset ℕ) (k : ℕ → ℕ) (u y : ℝ) :
    (∏ p ∈ A, leg u y (k p) p)+
      correction A
        (fun p => (k p : ℂ)*(u : ℂ)^(k p)*zetaPrimeLogKernel (k p) (center y) p)
        (fun p => (k p : ℂ)*(u : ℂ)^(k p)*ratio y^(k p)*
          zetaPrimeLogKernel (k p) (center y+1) p) =
        ∏ p ∈ A, (k p : ℂ)*(u : ℂ)^(k p)*zetaPrimeLogKernel (k p) (center y) p := by
  convert product_joint A
    (fun p => (k p : ℂ)*(u : ℂ)^(k p)*zetaPrimeLogKernel (k p) (center y) p)
    (fun p => (k p : ℂ)*(u : ℂ)^(k p)*ratio y^(k p)*
      zetaPrimeLogKernel (k p) (center y+1) p) using 1
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  dsimp [leg]
  ring

/-- The literal cutoff difference uses log(p) at both moment centers. -/
theorem cutoff_leg_identity (k p : ℕ) (u y z : ℝ) (hp : 0 < p) :
    leg u y k p*(1-Complex.exp (-(z*Real.log p : ℝ))) =
      (1-ratio y^k/(p : ℂ))*
        ((k : ℂ)*(u : ℂ)^k*zetaPrimeLogKernel k (center y) p*
          (1-Complex.exp (-(z*Real.log p : ℝ)))) := by
  rw [leg_eq_multiplier u y k p hp]
  ring

/-- Kernel-level form, retaining the nonzero order-zero boundary atom.
It does not multiply that atom by its derivative order. -/
theorem kernel_multiplier_all_orders (k p : ℕ) (y : ℝ) (hp : 0 < p) :
    zetaPrimeLogKernel k (center y) p-ratio y^k*zetaPrimeLogKernel k (center y+1) p =
      (1-ratio y^k/(p : ℂ))*zetaPrimeLogKernel k (center y) p := by
  rw [kernel_shift k p (center y) hp]
  ring

theorem kernel_product_all_orders (S : Finset ℕ) (k : ℕ → ℕ) (y : ℝ)
    (hp : ∀ p ∈ S, 0 < p) :
    (∏ p ∈ S, (zetaPrimeLogKernel (k p) (center y) p-
      ratio y^(k p)*zetaPrimeLogKernel (k p) (center y+1) p)) =
      (∏ p ∈ S, (1-ratio y^(k p)/(p : ℂ)))*
        ∏ p ∈ S, zetaPrimeLogKernel (k p) (center y) p := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun p hpS => kernel_multiplier_all_orders (k p) p y (hp p hpS))

/-- The positive pole's two-variable count factor after affine alignment.
The same additive cutoff z occurs at the shifted center, without C*z. -/
theorem pole_count_quotient (a C z : ℂ) (ha : a ≠ 0) (hC : C ≠ 0) :
    ((a+z)/a)/((C*a+z)/(C*a)) = C*(a+z)/(C*a+z) := by
  field_simp

/-- The surviving pole response is a tilted diagonal, not zero. -/
theorem pole_count_response (a C z : ℂ) (hz : z ≠ 0) (hd : C*a+z ≠ 0) :
    (1-C*(a+z)/(C*a+z))/z^2 = (1-C)/(z*(C*a+z)) := by
  field_simp
  ring

/-- At a nonzero cutoff the original shifted-center operator has a
nontrivial pole count factor, even though its one-variable pole cancels. -/
theorem pole_count_ne_one (y : ℝ) {a z : ℂ} (hz : z ≠ 0)
    (hd : ratio y*a+z ≠ 0) : ratio y*(a+z)/(ratio y*a+z) ≠ 1 := by
  intro h
  have hC : ratio y ≠ 1 := by
    intro he
    have hh := ratio_mul_pole y
    rw [he, one_mul, pole] at hh
    have : (1 : ℂ) = 0 := by linear_combination -hh
    exact one_ne_zero this
  apply hC
  have hh := (div_eq_one_iff_eq hd).mp h
  have he : (ratio y-1)*z = 0 := by linear_combination hh
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hz)

/-- The complete shifted correction cancels jointly in the count
exponential. It returns the ORIGINAL response, including its pole. -/
theorem count_joint (P H z : ℂ) (hH : H ≠ 0) :
    (1-P/H)/z^2+(P/H)*((1-H)/z^2) = (1-P)/z^2 := by
  have he : P/H*H = P := div_mul_cancel₀ P hH
  linear_combination -he/z^2

/-- After the shifted configurations cancel, the original positive pole
is still coupled to the ENTIRE negative-mode product Q. -/
theorem original_pole_split (Q w z b : ℂ) (hz : z ≠ 0) (hw : w-b ≠ 0) :
    (1-((w+z-b)/(w-b))*Q)/z^2 = (1-Q)/z^2-Q/(z*(w-b)) := by
  field_simp
  ring

end
end RiemannGaussian.ZetaRieszJointShift
