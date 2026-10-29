/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseCoefficient
/-! # Honest physical outer-loop state: retained inputs, acquired prefix/count and no private work -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseOuterView
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseReadBuffers SemiprimeD1StackNormalizedInverseCoefficient
/-- Proof specification of the actual retained/controller words at an outer-loop boundary. -/
def outerAux (a : List SemiprimeRationalBits.RationalWord) (q remaining built : ℕ)
    (reversed : List SemiprimeRationalBits.RationalWord) : Aux→List Bool
  | .denominator=>tape a | .originalQ=>unary q | .remaining=>unary remaining | .built=>unary built
  | .prefixReverse=>tape reversed | .output=>[false] | _=>[]
/-- All58 actual fields are specified, including the35 empty arithmetic fields and all8 empty caches. -/
def outer (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool)
    (remaining built : ℕ) (reversed : List SemiprimeRationalBits.RationalWord) : Words :=
  {rational:=emptyRational width,auxiliary:=outerAux a q remaining built reversed}
/-- The real remaining-marker pop changes exactly the actual remaining count. -/
theorem update_remaining (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool)
    (remaining built fresh : ℕ) (reversed : List SemiprimeRationalBits.RationalWord) :
    Function.update (store (outer a q width remaining built reversed)) (aux .remaining) (unary fresh)=
      store (outer a q width fresh built reversed) := by
  rw [update_aux]
  apply congrArg (fun f=>store ({outer a q width remaining built reversed with auxiliary:=f}:Words))
  funext k;cases k <;> simp [outer,outerAux]
/-- The real built-marker push follows actual frame-before-clear and preserves the new complete newest-first row. -/
theorem update_built (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool)
    (remaining built : ℕ) (reversed : List SemiprimeRationalBits.RationalWord)
    (word : SemiprimeRationalBits.RationalWord) :
    Function.update (store (SemiprimeD1StackNormalizedInverseCoefficient.result
      (outer a q width remaining built reversed) word)) (aux .built) (true::unary built)=
      store (outer a q width remaining (built+1) (word::reversed)) := by
  rw [update_aux]
  funext k
  rcases k with k|k
  · rfl
  · rcases k with ⟨r,den⟩|k
    · rfl
    · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackNormalizedInverseOuterView
