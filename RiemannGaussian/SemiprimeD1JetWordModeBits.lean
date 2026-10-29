/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetWordKernelBits
import RiemannGaussian.SemiprimeD1JetWordModeScalarBounds

/-! # Full original crossing modes from acquired words
The original base entry and scalar suppliers execute once each. Every physical
source/cache/Horner/vector product/power report is retained. Original native
mode data appear only in the literal-byte correctness theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1JetWordModeBits
open SemiprimeBitArithmetic SemiprimeD1JetAxes SemiprimeD1JetInterpretation
open SemiprimeD1JetAffineCoefficient (JetRun)
open SemiprimeD1JetPolynomialBits SemiprimeD1RecoveryIntegerBits
open SemiprimeD1WireKernelOriginal
attribute [local irreducible] SemiprimeD1JetWordModeScalarBits.acquireOriginal
  SemiprimeD1JetWordKernelBits.acquireOriginal

/-- Full actual original mode from the acquired base, scalar cache and step words. -/
def acquireOriginal (ctx : Context) (z : JetRun) (a i b : ℕ)
    (t : Fin (size a)) (x y₀ : Fin (2^a)) : JetRun :=
  let base:=SemiprimeD1JetWordKernelBits.acquireOriginal ctx z a t x y₀
  let source:=SemiprimeD1JetWordModeScalarBits.acquireOriginal ctx.precision a i t x y₀
  let inverse:=horner ctx z.words source.cache.words
  let tile:=SemiprimeD1JetWordSourceBits.constant ctx (positive source.step)
  let ratio:=SemiprimeD1JetRingBits.mul ctx tile.words inverse.words
  let raised:=power ctx ratio.words b
  let out:=SemiprimeD1JetRingBits.mul ctx base.words raised.words
  ⟨out.words,base.clock+source.clock+inverse.clock+tile.clock+ratio.clock+raised.clock+out.clock+20⟩

/-- Literal output bytes agree with the frozen original mode. Distinct source
and arithmetic reports are not identified or transferred by this equality. -/
theorem acquireOriginal_words (ctx : Context) (hpos : ctx.Positive) (z : JetRun)
    (a i b : ℕ) (t : Fin (size a)) (x y₀ : Fin (2^a)) :
    (acquireOriginal ctx z a i b t x y₀).words=
      (SemiprimeD1JetModeBits.acquireOriginal ctx z a i b t x y₀).words := by
  have hstep:(positive (SemiprimeD1JetWordModeScalarBits.acquireOriginal
      ctx.precision a i t x y₀).step).value=
      SemiprimeD1CrossingExpansion.step (a+1) i t.val (displacement a x y₀).val :=
    SemiprimeD1JetWordModeScalarBits.acquire_step_value ctx.precision a i t x y₀
  dsimp only [acquireOriginal,SemiprimeD1JetModeBits.acquireOriginal,SemiprimeD1JetModeBits.mode]
  rw [SemiprimeD1JetWordKernelBits.acquireOriginal_words ctx hpos z a t x y₀,
    SemiprimeD1JetWordModeScalarBits.acquire_cache_words,
    SemiprimeD1JetWordSourceBits.constant_words_eq_integerVector ctx _ _ hstep]
  rfl

/-- The full physical output has its current context's rank and precision. -/
theorem acquireOriginal_good (ctx : Context) (z : JetRun) (a i b : ℕ)
    (t : Fin (size a)) (x y₀ : Fin (2^a)) :
    SemiprimeD1JetAffineCoefficientBounds.Good ctx (acquireOriginal ctx z a i b t x y₀).words :=
  SemiprimeD1JetAffineCoefficientBounds.mul_good _ _ _
/-- The actual word-only original mode has the universal crossing interpretation
under the original point/valuation/same-bit conditions, with no supplied unit. -/
theorem acquireOriginal_value (ctx : Context) (z : JetRun) (a i b : ℕ)
    (t : Fin (size a)) (x y₀ : Fin (2^a))
    (hpos:ctx.Positive) (hp:0<ctx.precision)
    (ht:point a t.val≠0) (hi:padicValInt 2 (point a t.val)=i)
    (hbit:x.val.testBit i=y₀.val.testBit i) :
    interpret ctx (acquireOriginal ctx z a i b t x y₀).words=
      SemiprimeD1UniversalModeData.evaluate ctx.precision
        (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes))
        (interpret ctx z.words)
        (SemiprimeD1UniversalModeData.acquireOriginal ctx.precision a i b t x y₀) := by
  rw [acquireOriginal_words ctx hpos]
  exact SemiprimeD1JetModeBits.acquireOriginal_value ctx z a i b t x y₀ hpos hp ht hi hbit
end RiemannGaussian.SemiprimeD1JetWordModeBits
