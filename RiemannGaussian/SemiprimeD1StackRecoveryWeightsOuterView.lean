/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsIndices
/-! # Exact six-original-word outer boundary, with all helper/cache/shadow work empty -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsOuterView
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView SemiprimeD1StackRecoveryWeightsIndices
open SemiprimeRationalBits (RationalWord)
/-- Actual stopped original input bank, with only the reached remaining markers and acquired output added. -/
def outer (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool) (remaining:Nat) (out:List Bool):Words:=
  {rational:=Old.emptyRational width,
   auxiliary:=fun k=>match k with
     | .denominator=>SemiprimeD1StackNormalizedInverse.tape inverse
     | .prefixReverse=>SemiprimeD1StackNormalizedInverse.tape powers
     | .originalQ=>unary q | .remaining=>unary remaining | .output=>out | _=>[],
   scalarInputs:=fun k=>match k with | .signed=>SemiprimeD1StackNormalizedInverse.signed scalar | .den=>scalar.denominator}
/-- One physical outer-count pop changes only its actual remaining marker word. -/
theorem update_remaining (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool) (r n:Nat) (out:List Bool):
    Function.update (bank (outer inverse powers scalar q width r out)) (aux .remaining) (unary n)=
      bank (outer inverse powers scalar q width n out):=by
  rw [update_aux]
  unfold outer
  apply congrArg (fun f:I.Aux→List Bool=>bank {rational:=Old.emptyRational width,auxiliary:=f,scalarInputs:=fun k=>match k with | .signed=>SemiprimeD1StackNormalizedInverse.signed scalar | .den=>scalar.denominator})
  funext k
  cases k <;> rfl
/-- A completed physical row preserves every original word and every restored helper field. -/
theorem update_output (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool) (remaining:Nat) (out fresh:List Bool):
    {outer inverse powers scalar q width remaining out with auxiliary:=Function.update (outer inverse powers scalar q width remaining out).auxiliary .output fresh}=
      outer inverse powers scalar q width remaining fresh:=by
  unfold outer
  apply congrArg (fun f:I.Aux→List Bool=>({rational:=Old.emptyRational width,auxiliary:=f,scalarInputs:=fun k=>match k with | .signed=>SemiprimeD1StackNormalizedInverse.signed scalar | .den=>scalar.denominator}:Words))
  funext k
  cases k <;> rfl
/-- No rational cache/shadow contains a hidden initial coefficient. -/
theorem registers_empty (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool) (remaining:Nat) (out:List Bool):
    ∀r den,(outer inverse powers scalar q width remaining out).registers (r,den)=[]:=fun _ _=>rfl
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsOuterView
