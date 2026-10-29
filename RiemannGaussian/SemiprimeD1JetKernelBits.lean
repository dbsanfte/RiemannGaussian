/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetPolynomialBitsBounds
import RiemannGaussian.SemiprimeD1OddInverseBits
import RiemannGaussian.SemiprimeD1UniversalModeData

/-! # Physical original acquired-factor wire entries in the concrete jet algebra
Original integer constructors remain native. Source digits are acquired in p
actual div/rem stages; signed negation and inversion use only physical circuits.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1JetKernelBits
open scoped BigOperators
open SemiprimeBitArithmetic SemiprimeD1JetAxes SemiprimeD1JetInterpretation
open SemiprimeD1JetAffineCoefficient (JetRun)
open SemiprimeD1JetPolynomialBits

/-- Actual p-digit signed source residue, with the modular minus-one product paid. -/
def integer (p : ℕ) (z : ℤ) : SemiprimeSourceCompactBits.Report :=
  let unsigned:=magnitude p z.natAbs
  if z<0 then
    let negative:=SemiprimeD1OddInverseBits.negativeOne p
    let out:=SemiprimeD1JetScalarBits.mul p negative.bits unsigned.bits
    ⟨out.bits,unsigned.clock+negative.clock+out.clock+5⟩
  else ⟨unsigned.bits,unsigned.clock+3⟩

/-- Signed source acquisition has the original integer residue, not an advised word. -/
theorem integer_value (p : ℕ) (z : ℤ) :
    (bitValue (integer p z).bits:ZMod (2^p))=(z:ZMod (2^p)) := by
  unfold integer
  split_ifs with hz
  · change (bitValue (SemiprimeD1JetScalarBits.mul p
      (SemiprimeD1OddInverseBits.negativeOne p).bits (magnitude p z.natAbs).bits).bits:ZMod (2^p))=_
    rw [SemiprimeD1JetScalarBits.mul_zmod,magnitude_value]
    change SemiprimeD1OddInverseBits.value p (SemiprimeD1OddInverseBits.negativeOne p).bits*
      (z.natAbs:ZMod (2^p))=_
    rw [SemiprimeD1OddInverseBits.negativeOne_zmod,neg_one_mul]
    have he : -(z.natAbs:ℤ)=z := by rw [Int.natCast_natAbs,abs_of_neg hz];ring
    simpa only [Int.cast_neg,Int.cast_natCast] using congrArg (fun x : ℤ=>(x:ZMod (2^p))) he
  · change (bitValue (magnitude p z.natAbs).bits:ZMod (2^p))=_
    rw [magnitude_value]
    have he : (z.natAbs:ℤ)=z := by rw [Int.natCast_natAbs,abs_of_nonneg (by omega : 0≤z)]
    simpa only [Int.cast_natCast] using congrArg (fun x : ℤ=>(x:ZMod (2^p))) he

/-- Positive precision preserves genuine source oddness in the physically acquired residue. -/
theorem integer_odd (p : ℕ) (z : ℤ) (hp : 0<p) (hz : Odd z) :
    Odd (bitValue (integer p z).bits) := by
  let f : ZMod (2^p)→+*ZMod 2:=ZMod.castHom (dvd_pow_self 2 (Nat.ne_of_gt hp)) (ZMod 2)
  have he:=congrArg f (integer_value p z)
  simp only [map_natCast,map_intCast] at he
  apply ZMod.natCast_eq_one_iff_odd.mp
  exact he.trans (ZMod.intCast_eq_one_iff_odd.mpr hz)

/-- The physical odd inverse is exactly the original source residue inverse. -/
theorem inverse_value (p : ℕ) (z : ℤ) (hp : 0<p) (hz : Odd z) :
    (bitValue (SemiprimeD1OddInverseBits.inverse p (integer p z).bits).bits:ZMod (2^p))=
      (z:ZMod (2^p))⁻¹ := by
  have h:=SemiprimeD1OddInverseBits.inverse_correct p (integer p z).bits (integer_odd p z hp hz)
  change (bitValue (integer p z).bits:ZMod (2^p))*
    (bitValue (SemiprimeD1OddInverseBits.inverse p (integer p z).bits).bits:ZMod (2^p))=1 at h
  rw [integer_value] at h
  exact (ZMod.inv_eq_of_mul_eq_one _ _ _ h).symm

/-- Acquire an actual original integer as a concrete dense constant vector. -/
def integerVector (ctx : Context) (z : ℤ) : JetRun :=
  let input:=integer ctx.precision z
  let out:=scalar ctx input.bits
  ⟨out.words,input.clock+out.clock+3⟩

/-- Actual acquired integer vectors are the concrete constant-map images. -/
theorem integerVector_value (ctx : Context) (z : ℤ) (hpos : ∀q∈ctx.axes,0<q) :
    interpret ctx (integerVector ctx z).words=
      SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes) (z:ZMod (2^ctx.precision)) := by
  change interpret ctx (scalar ctx (integer ctx.precision z).bits).words=_
  rw [scalar_value ctx _ hpos,integer_value]

/-- Evaluate the actual unexpanded acquired affine integer factor. -/
def linear (ctx : Context) (z : List (List Bool)) (l : SemiprimeD1WireKernelFactors.Linear) : JetRun :=
  let constant:=integerVector ctx l.constant
  let slope:=integerVector ctx l.slope
  let term:=SemiprimeD1JetRingBits.mul ctx slope.words z
  let out:=SemiprimeD1JetRingBits.add ctx constant.words term.words
  ⟨out.words,constant.clock+slope.clock+term.clock+out.clock+5⟩

/-- Physical affine evaluation equals the literal acquired integer pair. -/
theorem linear_value (ctx : Context) (z : List (List Bool))
    (l : SemiprimeD1WireKernelFactors.Linear) (hpos : ∀q∈ctx.axes,0<q) :
    interpret ctx (linear ctx z l).words=
      SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes) (l.constant:ZMod (2^ctx.precision))+
      SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes) (l.slope:ZMod (2^ctx.precision))*interpret ctx z := by
  change interpret ctx (SemiprimeD1JetRingBits.add ctx (integerVector ctx l.constant).words
    (SemiprimeD1JetRingBits.mul ctx (integerVector ctx l.slope).words z).words).words=_
  rw [SemiprimeD1JetOperations.interpret_add ctx _ _ hpos,
    SemiprimeD1JetOperations.interpret_mul ctx _ _ hpos,
    integerVector_value ctx _ hpos,integerVector_value ctx _ hpos]

/-- Evaluate original acquired integer factors, normalizer and power using physical circuits.
The input jet report is retained once; every factor report is cached once. -/
def entry (ctx : Context) (z : JetRun) (e : SemiprimeD1WireKernelEntry.Entry) : JetRun :=
  let denominator:=integer ctx.precision e.denominator
  let inverse:=SemiprimeD1OddInverseBits.inverse ctx.precision denominator.bits
  let normalizer:=scalar ctx inverse.bits
  let two:=integerVector ctx 2
  let extra:=power ctx two.words e.power
  let factors:=product ctx (e.factors.map (linear ctx z.words))
  let left:=SemiprimeD1JetRingBits.mul ctx normalizer.words extra.words
  let out:=SemiprimeD1JetRingBits.mul ctx left.words factors.words
  ⟨out.words,z.clock+denominator.clock+inverse.clock+normalizer.clock+two.clock+extra.clock+
    factors.clock+left.clock+out.clock+20⟩

/-- The actual acquired-factor physical entry is exactly UniversalModeData.entryValue. -/
theorem entry_value (ctx : Context) (z : JetRun) (e : SemiprimeD1WireKernelEntry.Entry)
    (hpos : ∀q∈ctx.axes,0<q) (hp : 0<ctx.precision) (he : Odd e.denominator) :
    interpret ctx (entry ctx z e).words=
      SemiprimeD1UniversalModeData.entryValue ctx.precision
        (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)) (interpret ctx z.words) e := by
  change interpret ctx (SemiprimeD1JetRingBits.mul ctx
    (SemiprimeD1JetRingBits.mul ctx
      (scalar ctx (SemiprimeD1OddInverseBits.inverse ctx.precision (integer ctx.precision e.denominator).bits).bits).words
      (power ctx (integerVector ctx 2).words e.power).words).words
    (product ctx (e.factors.map (linear ctx z.words))).words).words=_
  rw [SemiprimeD1JetOperations.interpret_mul ctx _ _ hpos,
    SemiprimeD1JetOperations.interpret_mul ctx _ _ hpos,scalar_value ctx _ hpos,
    inverse_value ctx.precision e.denominator hp he,power_value ctx _ e.power hpos,
    integerVector_value ctx 2 hpos,product_value ctx _ hpos]
  simp only [List.map_map,Function.comp_def,linear_value ctx _ _ hpos,
    SemiprimeD1UniversalModeData.entryValue,Int.cast_ofNat]

/-- Original-input constructor, with no supplied entry/factor/inverse answer.
The report covers physical encoding/evaluation after the explicitly native integer constructor. -/
def acquireOriginal (ctx : Context) (z : JetRun) (a : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (x y : Fin (2^a)) : JetRun :=
  entry ctx z (SemiprimeD1WireKernelOriginal.acquireOriginal a t x y)

/-- Every original acquired grid entry discharges its own odd-denominator requirement. -/
theorem acquireOriginal_value (ctx : Context) (z : JetRun) (a : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (x y : Fin (2^a))
    (hpos : ∀q∈ctx.axes,0<q) (hp : 0<ctx.precision) :
    interpret ctx (acquireOriginal ctx z a t x y).words=
      SemiprimeD1UniversalModeData.entryValue ctx.precision
        (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)) (interpret ctx z.words)
        (SemiprimeD1WireKernelOriginal.acquireOriginal a t x y) := by
  apply entry_value ctx z _ hpos hp
  exact (SemiprimeD1WireKernelOriginal.original_integrality a t x y).1

end RiemannGaussian.SemiprimeD1JetKernelBits
