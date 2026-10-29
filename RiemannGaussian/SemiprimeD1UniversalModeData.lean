/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1UniversalModes

/-! # Executable original-input universal mode data and algebra evaluation
Runtime records contain the original acquired factors and an actually generated
finite inverse coefficient list. Polynomials occur only in correctness proofs.
The generic algebra's arithmetic implementation/physical clock is not supplied
or claimed by these identities.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1UniversalModeData
open scoped BigOperators
open Polynomial SemiprimeD1WireKernelFactors SemiprimeD1WireKernelEntry
  SemiprimeD1WireKernelOriginal SemiprimeD1WireKernelPaper SemiprimeD1CrossingCoefficient
  SemiprimeD1CrossingExpansion SemiprimeD1CrossingOriginal SemiprimeD1CrossingPaper
  SemiprimeD1OddAffineInverse SemiprimeD1UniversalModes

/-- Original finite mode data, with an acquired inverse list instead of an inverse oracle. -/
structure ModeData (p : ℕ) where
  /-- Original actual base entry factors and normalizer. -/
  base : Entry
  /-- Actual finite inverse coefficients generated from the stripped denominator. -/
  inverseCoefficients : List (ZMod (2^p))
  /-- Positive stripped tile step. -/
  tileStep : ℤ
  /-- Original mode index. -/
  degree : ℕ

/-- Acquire all universal mode data directly from original grid indices. -/
def acquire (p k center i j d b : ℕ) : ModeData p :=
  ⟨SemiprimeD1WireKernelEntry.acquire k center j d,
    coefficients p (normalizedFactor k j d).constant (normalizedFactor k j d).slope,
    step k i j d,b⟩

/-- The actual inverse cache has p scalar coefficients, regardless of extension rank. -/
theorem acquire_inverse_length (p k center i j d b : ℕ) :
    (acquire p k center i j d b).inverseCoefficients.length=p := by
  simp only [acquire,coefficients_length]

/-- Original factor acquisition retains at most the actual grid size, no dense table. -/
theorem acquire_factors_length (p k center i j d b : ℕ) :
    (acquire p k center i j d b).base.factors.length≤2^k := by
  simpa only [acquire,SemiprimeD1WireKernelEntry.acquire,List.length_map] using indices_length k d

/-- Execute a concrete acquired original entry in any implemented modular algebra. -/
def entryValue {A : Type*} [CommRing A] (p : ℕ) (f : ZMod (2^p) →+* A)
    (z : A) (e : Entry) : A :=
  f ((e.denominator:ZMod (2^p))⁻¹)*f (2:ZMod (2^p))^e.power*
    (e.factors.map (fun l => f (l.constant:ZMod (2^p))+f (l.slope:ZMod (2^p))*z)).prod

/-- Evaluate the actually generated finite list; no polynomial runtime argument is present. -/
def inverseValue {A : Type*} [CommRing A] (p : ℕ) (f : ZMod (2^p) →+* A)
    (z : A) (cs : List (ZMod (2^p))) : A :=
  ∑ r∈Finset.range cs.length,f (cs[r]?.getD 0)*z^r

/-- Execute a concrete mode from its actual acquired original finite data. -/
def evaluate {A : Type*} [CommRing A] (p : ℕ) (f : ZMod (2^p) →+* A)
    (z : A) (m : ModeData p) : A :=
  entryValue p f z m.base*
    (f (m.tileStep:ZMod (2^p))*inverseValue p f z m.inverseCoefficients)^m.degree

/-- Entry execution equals the original acquired modular numerator interpretation. -/
theorem entryValue_spec {A : Type*} [CommRing A] (p k center j d : ℕ)
    (f : ZMod (2^p) →+* A) (z : A) :
    entryValue p f z (SemiprimeD1WireKernelEntry.acquire k center j d)=
      (normalizer p k center*reducedNumerator p k center j d).eval₂ f z := by
  simp only [entryValue,normalizer,reducedNumerator,numerator,Polynomial.eval₂_mul,
    Polynomial.eval₂_C,Polynomial.map_mul,Polynomial.map_pow,Polynomial.eval₂_pow,Polynomial.map_C,Polynomial.map_list_prod,
    Polynomial.eval₂_list_prod,List.map_map,Function.comp_def,linearPolynomial,
    Polynomial.map_add,Polynomial.map_X,Polynomial.eval₂_add,Polynomial.eval₂_X,
    Int.coe_castRingHom,Int.cast_ofNat,map_pow,
    SemiprimeD1WireKernelEntry.acquire]
  ring

/-- Explicit finite list execution equals the proven odd-affine inverse polynomial. -/
theorem inverseValue_spec {A : Type*} [CommRing A] (p : ℕ)
    (f : ZMod (2^p) →+* A) (z : A) (constant slope : ℤ) :
    inverseValue p f z (coefficients p constant slope)=
      (SemiprimeD1OddAffineInverse.inverse p constant slope).eval₂ f z := by
  rw [inverse_from_coefficients]
  simp only [inverseValue,coefficients_length,Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_pow,Polynomial.eval₂_X]

/-- Actual mode data execution is exactly the universal mode polynomial. -/
theorem evaluate_spec {A : Type*} [CommRing A] (p k center i j d b : ℕ)
    (f : ZMod (2^p) →+* A) (z : A) :
    evaluate p f z (acquire p k center i j d b)=
      (mode p k center i j d b).eval₂ f z := by
  simp only [evaluate,acquire,entryValue_spec,inverseValue_spec,mode,
    Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_C,unitInverse]

/-- Original node/row/base-column acquisition of a universal mode. -/
def acquireOriginal (p a i b : ℕ) (t : Fin (size a)) (x y₀ : Fin (2^a)) : ModeData p :=
  acquire p (a+1) (center a) i t.val (baseIndex a x y₀) b

/-- Original same-bit crossing mode has weight b+1 in EVERY modular algebra.
All coefficients and finite inverses are acquired, not supplied to this theorem. -/
theorem original_weight {A : Type*} [CommRing A] (p a i b : ℕ)
    (f : ZMod (2^p) →+* A) (z : A) (t : Fin (size a)) (x y₀ : Fin (2^a))
    (ht : point a t.val≠0) (hi : padicValInt 2 (point a t.val)=i)
    (hia : i<a) (hbit : x.val.testBit i=y₀.val.testBit i) :
    ∃ c:A,evaluate p f z (acquireOriginal p a i b t x y₀)=f (2:ZMod (2^p))^(b+1)*c := by
  obtain ⟨hn,hv⟩ := original_crossing a i t x y₀ ht hi hbit
  obtain ⟨c,hc⟩ := mode_divisible p (a+1) (center a) i t.val (baseIndex a x y₀) b
    t.isLt (baseIndex_lt a x y₀) (by omega) hn hv
  refine ⟨c.eval₂ f z,?_⟩
  rw [acquireOriginal,evaluate_spec,hc]
  simp only [Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_pow,map_pow]

/-- COMPLETE ORIGINAL D.12 at arbitrary algebra/extension scalar, strict cutoff
b+1<p, with no local-scalar or supplied denominator/coefficient/inverse hypothesis. -/
theorem original_D12 {A : Type*} [CommRing A] (p a i tile : ℕ)
    (f : ZMod (2^p) →+* A) (z : A) (t : Fin (size a)) (x y₀ y : Fin (2^a))
    (ht : point a t.val≠0) (hi : padicValInt 2 (point a t.val)=i)
    (hia : i<a) (hbit : x.val.testBit i=y₀.val.testBit i)
    (hy : y.val=y₀.val+2^(i+1)*tile) (hp : 0<p) :
    entryValue p f z (SemiprimeD1WireKernelOriginal.acquireOriginal a t x y)=
      ∑ b∈Finset.range (p-1),evaluate p f z (acquireOriginal p a i b t x y₀)*
        f ((tile:ZMod (2^p))^b) := by
  obtain ⟨hn,hv⟩ := original_crossing a i t x y₀ ht hi hbit
  have hidx := original_tile_index a i tile x y₀ y hy
  have hd : baseIndex a x y₀+2^(i+1)*tile<2^(a+1) := by
    rw [← hidx]
    exact (SemiprimeD1WireKernelOriginal.displacement a x y).isLt
  have h := evaluated_expansion p (a+1) (center a) i t.val (baseIndex a x y₀) tile f z
    (center_lt a) t.isLt (baseIndex_lt a x y₀) hd (by omega) hn hv hp
  simp_rw [acquireOriginal,evaluate_spec]
  rw [SemiprimeD1WireKernelOriginal.acquireOriginal,entryValue_spec]
  simpa only [← hidx] using h

end RiemannGaussian.SemiprimeD1UniversalModeData
