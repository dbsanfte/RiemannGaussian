/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetKernelBits

/-! # Actual physical finite inverse caches and universal crossing modes
No native modular inversion or requested coefficient list executes. The cache
is acquired by scalar multiplication from the physically acquired odd inverse.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1JetModeBits
open scoped BigOperators
open SemiprimeBitArithmetic SemiprimeD1JetAxes SemiprimeD1JetInterpretation
open SemiprimeD1JetAffineCoefficient (JetRun)
open SemiprimeD1JetPolynomialBits SemiprimeD1JetKernelBits

/-- Acquired ascending scalar coefficient words and all retained work. -/
structure Cache where
  /-- Physical coefficient array in the original degree order. -/
  words : List (List Bool)
  /-- Actual copies, products, allocation and control. -/
  clock : ℕ

/-- Acquire each finite geometric coefficient once, then cache its physical word. -/
def geometric (p : ℕ) (ratio current : List Bool) : ℕ→Cache
  | 0 => ⟨[],1⟩
  | n+1 =>
    let here:=SemiprimeSourceCompactBits.copy current
    let next:=SemiprimeD1JetScalarBits.mul p ratio current
    let tail:=geometric p ratio next.bits n
    ⟨here.bits::tail.words,here.clock+next.clock+tail.clock+5⟩

/-- Actual finite cache length is the requested number of acquired coefficients. -/
theorem geometric_length (p : ℕ) (ratio current : List Bool) (n : ℕ) :
    (geometric p ratio current n).words.length=n := by
  induction n generalizing current with
  | zero => rfl
  | succ n ih => simp only [geometric,List.length_cons,ih]

/-- Every acquired geometric coefficient has its original multiplicative meaning. -/
theorem geometric_coefficient (p : ℕ) (ratio current : List Bool) (n i : ℕ) (hi : i<n) :
    (bitValue ((geometric p ratio current n).words.getD i []):ZMod (2^p))=
      (bitValue current:ZMod (2^p))*(bitValue ratio:ZMod (2^p))^i := by
  induction n generalizing current i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp only [geometric,List.getD_cons_zero,SemiprimeSourceCompactBits.copy_bits,pow_zero,mul_one]
    | succ i =>
      change (bitValue ((geometric p ratio (SemiprimeD1JetScalarBits.mul p ratio current).bits n).words.getD i []):ZMod (2^p))=_
      rw [ih _ i (by omega),SemiprimeD1JetScalarBits.mul_zmod,pow_succ]
      ring

/-- Acquire the inverse constant and the signed slope ratio by physical operations. -/
def inverseCache (p : ℕ) (constant slope : ℤ) : Cache :=
  let c:=integer p constant
  let s:=integer p slope
  let inverse:=SemiprimeD1OddInverseBits.inverse p c.bits
  let negative:=SemiprimeD1OddInverseBits.negativeOne p
  let opposite:=SemiprimeD1JetScalarBits.mul p negative.bits s.bits
  let ratio:=SemiprimeD1JetScalarBits.mul p opposite.bits inverse.bits
  let out:=geometric p ratio.bits inverse.bits p
  ⟨out.words,c.clock+s.clock+inverse.clock+negative.clock+opposite.clock+ratio.clock+out.clock+15⟩

/-- The acquired inverse cache has exactly the original precision length. -/
theorem inverseCache_length (p : ℕ) (constant slope : ℤ) :
    (inverseCache p constant slope).words.length=p := geometric_length _ _ _ _

/-- Cache values agree with the original finite inverse coefficient formula. -/
theorem inverseCache_coefficient (p : ℕ) (constant slope : ℤ) (hp : 0<p) (hc : Odd constant)
    (i : ℕ) (hi : i<p) :
    (bitValue ((inverseCache p constant slope).words.getD i []):ZMod (2^p))=
      (SemiprimeD1OddAffineInverse.coefficients p constant slope).getD i 0 := by
  change (bitValue ((geometric p
    (SemiprimeD1JetScalarBits.mul p
      (SemiprimeD1JetScalarBits.mul p (SemiprimeD1OddInverseBits.negativeOne p).bits (integer p slope).bits).bits
      (SemiprimeD1OddInverseBits.inverse p (integer p constant).bits).bits).bits
    (SemiprimeD1OddInverseBits.inverse p (integer p constant).bits).bits p).words.getD i []):ZMod (2^p))=_
  rw [geometric_coefficient _ _ _ _ _ hi,SemiprimeD1JetScalarBits.mul_zmod,
    SemiprimeD1JetScalarBits.mul_zmod,inverse_value p constant hp hc,integer_value]
  have hn:=SemiprimeD1OddInverseBits.negativeOne_zmod p
  change (bitValue (SemiprimeD1OddInverseBits.negativeOne p).bits:ZMod (2^p)) = -1 at hn
  rw [hn,neg_one_mul]
  simp [SemiprimeD1OddAffineInverse.coefficients,hi]

/-- Actual Horner evaluation of the acquired inverse cache equals the original finite list value. -/
theorem inverseCache_value (ctx : Context) (z : List (List Bool)) (constant slope : ℤ)
    (hpos : ∀q∈ctx.axes,0<q) (hp : 0<ctx.precision) (hc : Odd constant) :
    interpret ctx (horner ctx z (inverseCache ctx.precision constant slope).words).words=
      SemiprimeD1UniversalModeData.inverseValue ctx.precision
        (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)) (interpret ctx z)
        (SemiprimeD1OddAffineInverse.coefficients ctx.precision constant slope) := by
  rw [horner_sum ctx z _ hpos]
  simp only [inverseCache_length,SemiprimeD1UniversalModeData.inverseValue,
    SemiprimeD1OddAffineInverse.coefficients_length]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inverseCache_coefficient ctx.precision constant slope hp hc i (Finset.mem_range.mp hi)]
  rfl

/-- Complete concrete mode evaluation from original native grid indices.
All physical base/cache/Horner/step/power reports are retained exactly once. -/
def mode (ctx : Context) (z : JetRun) (k center i j d b : ℕ) : JetRun :=
  let base:=entry ctx z (SemiprimeD1WireKernelEntry.acquire k center j d)
  let factor:=SemiprimeD1WireKernelFactors.normalizedFactor k j d
  let cache:=inverseCache ctx.precision factor.constant factor.slope
  let inverse:=horner ctx z.words cache.words
  let step:=integerVector ctx (SemiprimeD1CrossingExpansion.step k i j d)
  let ratio:=SemiprimeD1JetRingBits.mul ctx step.words inverse.words
  let raised:=power ctx ratio.words b
  let out:=SemiprimeD1JetRingBits.mul ctx base.words raised.words
  ⟨out.words,base.clock+cache.clock+inverse.clock+step.clock+ratio.clock+raised.clock+out.clock+20⟩

/-- Concrete physical modes equal the original universal mode-data evaluation. -/
theorem mode_value (ctx : Context) (z : JetRun) (k center i j d b : ℕ)
    (hpos : ∀q∈ctx.axes,0<q) (hp : 0<ctx.precision) (hcenter : center<2^k) (hne : d≠j) :
    interpret ctx (mode ctx z k center i j d b).words=
      SemiprimeD1UniversalModeData.evaluate ctx.precision
        (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)) (interpret ctx z.words)
        (SemiprimeD1UniversalModeData.acquire ctx.precision k center i j d b) := by
  change interpret ctx (SemiprimeD1JetRingBits.mul ctx
    (entry ctx z (SemiprimeD1WireKernelEntry.acquire k center j d)).words
    (power ctx (SemiprimeD1JetRingBits.mul ctx
      (integerVector ctx (SemiprimeD1CrossingExpansion.step k i j d)).words
      (horner ctx z.words (inverseCache ctx.precision
        (SemiprimeD1WireKernelFactors.normalizedFactor k j d).constant
        (SemiprimeD1WireKernelFactors.normalizedFactor k j d).slope).words).words).words b).words).words=_
  rw [SemiprimeD1JetOperations.interpret_mul ctx _ _ hpos,
    entry_value ctx z _ hpos hp (SemiprimeD1WireKernelEntry.denominator_odd k center hcenter),
    power_value ctx _ b hpos,SemiprimeD1JetOperations.interpret_mul ctx _ _ hpos,
    integerVector_value ctx _ hpos,inverseCache_value ctx _ _ _ hpos hp
      (SemiprimeD1CrossingCoefficient.normalized_constant_odd k j d hne)]
  rfl

/-- Original crossing-mode producer from actual grid, row and column indices. -/
def acquireOriginal (ctx : Context) (z : JetRun) (a i b : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (x y₀ : Fin (2^a)) : JetRun :=
  mode ctx z (a+1) (SemiprimeD1WireKernelOriginal.center a) i t.val
    (SemiprimeD1CrossingPaper.baseIndex a x y₀) b

/-- Actual same-bit source conditions discharge all mode units and inverse-data requirements. -/
theorem acquireOriginal_value (ctx : Context) (z : JetRun) (a i b : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (x y₀ : Fin (2^a))
    (hpos : ∀q∈ctx.axes,0<q) (hp : 0<ctx.precision)
    (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i)
    (hbit : x.val.testBit i=y₀.val.testBit i) :
    interpret ctx (acquireOriginal ctx z a i b t x y₀).words=
      SemiprimeD1UniversalModeData.evaluate ctx.precision
        (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)) (interpret ctx z.words)
        (SemiprimeD1UniversalModeData.acquireOriginal ctx.precision a i b t x y₀) := by
  obtain ⟨hne,_⟩:=SemiprimeD1CrossingPaper.original_crossing a i t x y₀ ht hi hbit
  exact mode_value ctx z (a+1) (SemiprimeD1WireKernelOriginal.center a) i t.val
    (SemiprimeD1CrossingPaper.baseIndex a x y₀) b hpos hp
    (SemiprimeD1WireKernelOriginal.center_lt a) hne

end RiemannGaussian.SemiprimeD1JetModeBits
