/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1CrossingModulo
import RiemannGaussian.SemiprimeD1CrossingBit

/-! # Original-input same-bit D.12 endpoint
The caller supplies original grid/node/row/tile indices, not a displacement
valuation or an integrality certificate. Local interpolation scalars are integers.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1CrossingPaper
open scoped BigOperators
open SemiprimeD1WireKernelFactors SemiprimeD1WireKernelEntry
  SemiprimeD1WireKernelOriginal SemiprimeD1WireKernelPaper SemiprimeD1CrossingCoefficient
  SemiprimeD1CrossingExpansion SemiprimeD1CrossingOriginal SemiprimeD1CrossingResidue
  SemiprimeD1CrossingModulo SemiprimeD1CrossingBit

/-- Actual original grid index for the base column's displacement. -/
def baseIndex (a : ℕ) (x y₀ : Fin (2^a)) : ℕ :=
  (SemiprimeD1WireKernelOriginal.displacement a x y₀).val

/-- Original dyadic grid membership is derived from actual row and column indices. -/
theorem baseIndex_lt (a : ℕ) (x y₀ : Fin (2^a)) : baseIndex a x y₀<2^(a+1) :=
  (SemiprimeD1WireKernelOriginal.displacement a x y₀).isLt

/-- Grid-index difference equals the original signed scalar crossing displacement. -/
theorem original_difference (a : ℕ) (t : Fin (size a)) (x y₀ : Fin (2^a)) :
    difference t.val (baseIndex a x y₀)=point a t.val-y₀.val+x.val := by
  have h := displacement_point a x y₀
  change (baseIndex a x y₀:ℤ)-(center a:ℤ)=(y₀.val:ℤ)-(x.val:ℤ) at h
  unfold difference point
  omega

/-- Actual crossing-bit condition derives BOTH nonzero and order bounds. -/
theorem original_crossing (a i : ℕ) (t : Fin (size a)) (x y₀ : Fin (2^a))
    (ht : point a t.val≠0) (hi : padicValInt 2 (point a t.val)=i)
    (hbit : x.val.testBit i=y₀.val.testBit i) :
    baseIndex a x y₀≠t.val ∧ padicValInt 2 (difference t.val (baseIndex a x y₀))≤ i := by
  have h := crossing_of_valuation (point a t.val) x.val y₀.val i ht hi hbit
  rw [← original_difference] at h
  refine ⟨?_,h.2⟩
  intro he
  apply h.1
  simp [difference,he]

/-- The original b-th mode integer fraction, acquired without coefficient answers. -/
def acquireOriginalMode (a i b : ℕ) (t : Fin (size a)) (x y₀ : Fin (2^a))
    (z : ℤ) : Coefficient :=
  SemiprimeD1CrossingCoefficient.acquire (a+1) (center a) i t.val (baseIndex a x y₀) b z

/-- Original same-bit mode coefficients have actual odd denominators and weight b+1. -/
theorem original_mode_integral (a i b : ℕ) (t : Fin (size a)) (x y₀ : Fin (2^a))
    (z : ℤ) (ht : point a t.val≠0) (hi : padicValInt 2 (point a t.val)=i)
    (hia : i<a) (hbit : x.val.testBit i=y₀.val.testBit i) :
    Odd (acquireOriginalMode a i b t x y₀ z).denominator ∧
      (2:ℤ)^(b+1)∣(acquireOriginalMode a i b t x y₀ z).numerator := by
  obtain ⟨hn,hv⟩ := original_crossing a i t x y₀ ht hi hbit
  exact ⟨acquire_odd (a+1) (center a) i t.val (baseIndex a x y₀) b z
      (center_lt a) t.isLt (baseIndex_lt a x y₀) hn,
    acquire_divisible (a+1) (center a) i t.val (baseIndex a x y₀) b z
      t.isLt (baseIndex_lt a x y₀) (by omega) hn hv⟩

/-- Actual original mode equals W at the base column times the positive geometric ratio. -/
theorem original_mode_value (a i b : ℕ) (t : Fin (size a)) (x y₀ : Fin (2^a))
    (z : ℤ) (ht : point a t.val≠0) (hi : padicValInt 2 (point a t.val)=i)
    (hbit : x.val.testBit i=y₀.val.testBit i) :
    value (acquireOriginalMode a i b t x y₀ z)=
      ((kernel a (baseIndex a x y₀)).comp (affine a t.val)).eval (z:ℚ)*
        ((2:ℚ)^(i+1)/(point a t.val+(2:ℤ)^(a+1)*z-y₀.val+x.val:ℤ))^b := by
  obtain ⟨hn,hv⟩ := original_crossing a i t x y₀ ht hi hbit
  rw [kernel_local]
  have h := acquire_value (a+1) (center a) i t.val (baseIndex a x y₀) b z
    (center_lt a) t.isLt (baseIndex_lt a x y₀) hn hv
  have he : SemiprimeD1CrossingCoefficient.displacement (a+1) t.val (baseIndex a x y₀) z=
      point a t.val+(2:ℤ)^(a+1)*z-y₀.val+x.val := by
    rw [SemiprimeD1CrossingCoefficient.displacement,original_difference]
    ring
  simpa only [acquireOriginalMode,he] using h

/-- Actual tile column shifts its original displacement index by the positive tile step. -/
theorem original_tile_index (a i tile : ℕ) (x y₀ y : Fin (2^a))
    (hy : y.val=y₀.val+2^(i+1)*tile) :
    (SemiprimeD1WireKernelOriginal.displacement a x y).val=
      baseIndex a x y₀+2^(i+1)*tile := by
  have h₀ := displacement_point a x y₀
  have h₁ := displacement_point a x y
  change (baseIndex a x y₀:ℤ)-(center a:ℤ)=(y₀.val:ℤ)-(x.val:ℤ) at h₀
  unfold point at h₁
  omega

/-- Complete ORIGINAL scalar D.12 modulo2^p: actual same-bit crossing, actual finite
unit evaluation, and exactly the strict cutoff b+1<p. No crossing-valuation premise. -/
theorem original_D12 (a i tile p : ℕ) (t : Fin (size a)) (x y₀ y : Fin (2^a))
    (z : ℤ) (ht : point a t.val≠0) (hi : padicValInt 2 (point a t.val)=i)
    (hia : i<a) (hbit : x.val.testBit i=y₀.val.testBit i)
    (hy : y.val=y₀.val+2^(i+1)*tile) (hp : 0<p) :
    evaluate p (acquireOriginal a t x y) (z:ZMod (2^p))=
      ∑ b∈Finset.range (p-1),residue p (acquireOriginalMode a i b t x y₀ z)*
        (tile:ZMod (2^p))^b := by
  obtain ⟨hn,hv⟩ := original_crossing a i t x y₀ ht hi hbit
  have hidx := original_tile_index a i tile x y₀ y hy
  have hd : baseIndex a x y₀+2^(i+1)*tile<2^(a+1) := by
    rw [← hidx]
    exact (SemiprimeD1WireKernelOriginal.displacement a x y).isLt
  have h := original_modulo (a+1) (center a) i t.val (baseIndex a x y₀) tile p z
    (center_lt a) t.isLt (baseIndex_lt a x y₀) hd (by omega) hn hv hp
  simpa only [acquireOriginalMode,acquireOriginal,← hidx] using h

end RiemannGaussian.SemiprimeD1CrossingPaper
