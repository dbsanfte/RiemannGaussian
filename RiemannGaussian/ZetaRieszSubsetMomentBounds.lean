/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLayerVariance

/-!
# Signed finite-input crossing enclosures from complete moments

Arbitrary subset bins retain their true parity and complete multiplicity.
Cauchy--Schwarz and the extremal chord supply pointwise hinge bounds using
only exact first/second moments and extrema. The final signed inequality
joins every bin before evaluating the floor. No prime-measure transport,
native numerical budget, or asymptotic floor follows from these enclosures.
-/

set_option autoImplicit false
noncomputable section
open Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszSubsetMomentBounds

private theorem hinge_eq_abs (v : ℝ) : max 0 v=(v+|v|)/2 := by
  rcases le_total 0 v with hv | hv
  · rw [max_eq_right hv,abs_of_nonneg hv]
    ring
  · rw [max_eq_left hv,abs_of_nonpos hv]
    ring

/-- The complete first moment supplies a lower bound without sampling
the population in a bin or assigning a sign to its unresolved crossing. -/
theorem hinge_sum_lower {ι : Type*} (S : Finset ι) (x : ι → ℝ) (D : ℝ) :
    max 0 ((S.card : ℝ)*D-∑ i∈S,x i) ≤ ∑ i∈S,max 0 (D-x i) := by
  apply max_le
  · exact Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  · have hh := Finset.sum_le_sum (s := S) (fun i _ => le_max_right 0 (D-x i))
    simpa only [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul] using hh

/-- A rational upper radius can enclose the Cauchy square root. This is
the exact inequality used by the detector's integer square-root bound. -/
theorem hinge_sum_upper_of_second_moment {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) (D B : ℝ) (hB : 0 ≤ B)
    (hsecond : (S.card : ℝ)*(∑ i∈S,(D-x i)^2) ≤ B^2) :
    (∑ i∈S,max 0 (D-x i)) ≤ ((S.card : ℝ)*D-(∑ i∈S,x i)+B)/2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => |D-x i|) (fun _ => (1 : ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,nsmul_eq_mul,sq_abs] at hcs
  have hs : (∑ i∈S,|D-x i|) ≤ B :=
    (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hB).mp
      (hcs.trans (by simpa only [mul_comm] using hsecond))
  have he : (∑ i∈S,max 0 (D-x i))=
      ((S.card : ℝ)*D-(∑ i∈S,x i)+(∑ i∈S,|D-x i|))/2 := by
    simp_rw [hinge_eq_abs]
    rw [← Finset.sum_div,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const]
    simp only [nsmul_eq_mul]
  rw [he]
  linarith only [hs]

/-- Centering is exact; the radicand can be computed with INTEGER
moments without subtracting a sum of rounded subset logarithms. -/
theorem centered_second_moment_identity {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) (D : ℝ) :
    (S.card : ℝ)*(∑ i∈S,(D-x i)^2)=
      ((S.card : ℝ)*D-(∑ i∈S,x i))^2+
        (S.card : ℝ)*(∑ i∈S,x i^2)-(∑ i∈S,x i)^2 := by
  have he : (∑ i∈S,(D-x i)^2)=
      (S.card : ℝ)*D^2-2*D*(∑ i∈S,x i)+(∑ i∈S,x i^2) := by
    calc
      _ = ∑ i∈S,(D^2-2*D*x i+x i^2) :=
        Finset.sum_congr rfl (fun _ _ => by ring)
      _ = _ := by
        rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
          ← Finset.mul_sum]
        simp only [nsmul_eq_mul]
  rw [he]
  ring

/-- The extremal chord is a second independent upper bound for a
crossing bin. Every subset lies in the stated interval. -/
theorem hinge_sum_upper_of_chord {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {D l h : ℝ} (hlh : l < h) (hlD : l ≤ D) (hDh : D ≤ h)
    (hx : ∀ i∈S,l ≤ x i ∧ x i ≤ h) :
    (∑ i∈S,max 0 (D-x i)) ≤
      (((S.card : ℝ)*h-∑ i∈S,x i)*(D-l))/(h-l) := by
  have hp i (hi : i∈S) : (h-l)*max 0 (D-x i) ≤ (h-x i)*(D-l) := by
    rcases le_total (x i) D with hh | hh
    · rw [max_eq_right (by linarith : 0 ≤ D-x i)]
      have hm := mul_nonneg (show 0 ≤ x i-l by linarith [(hx i hi).1])
        (show 0 ≤ h-D by linarith)
      nlinarith only [hm]
    · rw [max_eq_left (by linarith : D-x i ≤ 0),mul_zero]
      exact mul_nonneg (by linarith [(hx i hi).2]) (by linarith)
  have hs := Finset.sum_le_sum hp
  rw [← Finset.mul_sum,← Finset.sum_mul,Finset.sum_sub_distrib,Finset.sum_const] at hs
  simp only [nsmul_eq_mul] at hs
  apply (le_div_iff₀ (by linarith : 0 < h-l)).mpr
  simpa only [mul_comm] using hs

/-- Exact signed lower/upper enclosures for arbitrary complete parity
bins. No absolute value is taken over the central signed aggregate. -/
theorem signed_bin_bounds {κ ι : Type*} (T : Finset κ) (S : κ → Finset ι)
    (x : κ → ι → ℝ) (odd : κ → Bool) (D : ℝ) (lo hi : κ → ℝ)
    (hb : ∀ b∈T,lo b ≤ (∑ i∈S b,max 0 (D-x b i)) ∧
      (∑ i∈S b,max 0 (D-x b i)) ≤ hi b) :
    (∑ b∈T,if odd b then -hi b else lo b) ≤
      (∑ b∈T,(if odd b then -(∑ i∈S b,max 0 (D-x b i)) else
        (∑ i∈S b,max 0 (D-x b i)))) ∧
    (∑ b∈T,(if odd b then -(∑ i∈S b,max 0 (D-x b i)) else
        (∑ i∈S b,max 0 (D-x b i)))) ≤
      (∑ b∈T,if odd b then -lo b else hi b) := by
  constructor <;> apply Finset.sum_le_sum <;> intro b hbt <;>
    cases odd b <;> simp only [Bool.false_eq_true,if_false,if_true] <;>
    have hh := hb b hbt <;> linarith only [hh.1,hh.2]

end RiemannGaussian.ZetaRieszSubsetMomentBounds
