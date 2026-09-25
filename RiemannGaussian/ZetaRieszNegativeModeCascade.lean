/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszZeroParityCascade

/-!
# Finite negative-mode count algebra

The all-count exponential is evaluated before expanding any mode. The
two- and three-mode identities retain the diagonal boundary channels.
These rational identities alone are not a literal arithmetic transfer.
-/

namespace RiemannGaussian.ZetaRieszNegativeModeCascade
noncomputable section
open Complex Filter Set Topology
open scoped BigOperators Classical

/-- A complete nonempty count sum, with the largest-prime minus sign.
Repeated entries in the finite index set represent genuine multiplicity. -/
def countTerm {ι : Type*} (A : Finset ι) (J : ι → ℂ) (z : ℂ) (k : ℕ) : ℂ :=
  -(-(∑ i ∈ A, J i))^k/((k.factorial : ℂ)*z^2)

theorem hasSum_counts {ι : Type*} (A : Finset ι) (J : ι → ℂ) (z : ℂ) :
    HasSum (fun k : ℕ => countTerm A J z (k+1))
      ((1-∏ i ∈ A, Complex.exp (-J i))/z^2) := by
  have he : HasSum (fun k : ℕ => (-(∑ i ∈ A, J i))^k/(k.factorial : ℂ))
      (Complex.exp (-(∑ i ∈ A, J i))) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have ht := (hasSum_nat_add_iff' 1).mpr he
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at ht
  have hp : Complex.exp (-(∑ i ∈ A, J i)) = ∏ i ∈ A, Complex.exp (-J i) := by
    rw [← Finset.sum_neg_distrib, Complex.exp_sum]
  rw [hp] at ht
  simpa only [countTerm, div_div, neg_div, neg_sub] using ht.neg.div_const (z^2)

/-- At zero cutoff the logarithmic primitive of one mode gives its exact
rational factor. No choice of logarithm is passed through a power. -/
theorem mode_factor (w z xi : ℂ) (hw : w-xi ≠ 0) (hwz : w+z-xi ≠ 0) :
    Complex.exp (-(Complex.log (w+z-xi)-Complex.log (w-xi))) =
      (w-xi)/(w+z-xi) := by
  rw [neg_sub, Complex.exp_sub, Complex.exp_log hw, Complex.exp_log hwz]

/-- The rational zero-cutoff response of a finite all-negative mode family. -/
def response {ι : Type*} (A : Finset ι) (xi : ι → ℂ) (w z : ℂ) : ℂ :=
  (1-∏ i ∈ A, ((w-xi i)/(w+z-xi i)))/z^2

/-- The finite all-negative product is deduced from the convergent count
exponential with the same largest-prime sign. -/
theorem hasSum_zero_cutoff_counts {ι : Type*} (A : Finset ι) (xi : ι → ℂ)
    (w z : ℂ) (hw : ∀ i ∈ A, w-xi i ≠ 0) (hwz : ∀ i ∈ A, w+z-xi i ≠ 0) :
    HasSum (fun k : ℕ => countTerm A (fun i =>
      Complex.log (w+z-xi i)-Complex.log (w-xi i)) z (k+1)) (response A xi w z) := by
  convert hasSum_counts A (fun i => Complex.log (w+z-xi i)-Complex.log (w-xi i)) z using 1
  unfold response
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  exact (mode_factor w z (xi i) (hw i hi) (hwz i hi)).symm

/-- Adjoining a single negative mode preserves the shifted-pole algebra.
The final term is a diagonal convolution followed by a d derivative;
its boundary contribution must be retained. -/
theorem response_insert {ι : Type*} (A : Finset ι) (xi : ι → ℂ) (i : ι)
    (hi : i ∉ A) (w z : ℂ) (hz : z ≠ 0) (hd : w+z-xi i ≠ 0) :
    response (insert i A) xi w z = response A xi w z+
      1/(z*(w+z-xi i))-z/(w+z-xi i)*response A xi w z := by
  unfold response
  rw [Finset.prod_insert hi]
  field_simp
  ring

theorem two_modes (w z a b : ℂ) (hz : z ≠ 0)
    (ha : w+z-a ≠ 0) (hb : w+z-b ≠ 0) :
    (1-((w-a)/(w+z-a))*((w-b)/(w+z-b)))/z^2 =
      1/(z*(w+z-a))+1/(z*(w+z-b))-1/((w+z-a)*(w+z-b)) := by
  field_simp
  ring

theorem three_modes (w z a b c : ℂ) (hz : z ≠ 0)
    (ha : w+z-a ≠ 0) (hb : w+z-b ≠ 0) (hc : w+z-c ≠ 0) :
    (1-((w-a)/(w+z-a))*((w-b)/(w+z-b))*((w-c)/(w+z-c)))/z^2 =
      1/(z*(w+z-a))+1/(z*(w+z-b))+1/(z*(w+z-c))-
      1/((w+z-a)*(w+z-b))-1/((w+z-a)*(w+z-c))-
      1/((w+z-b)*(w+z-c))+z/((w+z-a)*(w+z-b)*(w+z-c)) := by
  field_simp
  ring

/-- One integration in d per additional mode makes the boundary terms
ordinary supported kernels. This exact recurrence is the transform-level
version of the supported primitive recurrence. -/
theorem primitive_response_insert {ι : Type*} (A : Finset ι) (xi : ι → ℂ) (i : ι)
    (hi : i ∉ A) (w z : ℂ) (hz : z ≠ 0) (hd : w+z-xi i ≠ 0) :
    response (insert i A) xi w z/z^(A.card+1) =
      (response A xi w z/z^A.card)/z+
      1/(z^(A.card+2)*(w+z-xi i))-
      (response A xi w z/z^A.card)/(w+z-xi i) := by
  rw [response_insert A xi i hi w z hz hd]
  simp only [pow_succ]
  field_simp

end
end RiemannGaussian.ZetaRieszNegativeModeCascade
