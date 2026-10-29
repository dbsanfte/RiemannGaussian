/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseBankBounds
/-! # Physical input size and all actual outer/indexed cached-prefix word capacities -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseStateBounds
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseReadBuffers SemiprimeD1StackNormalizedInverseIndices
open SemiprimeD1StackNormalizedInverseOuterView SemiprimeD1StackNormalizedInverseWidths
open SemiprimeD1StackNormalizedInverseBankBounds
/-- Actual complete three-word source size; q is paid by q physically present unary markers. -/
def inputSize (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) : ℕ :=
  (tape a).length+q+width.length+1
/-- All physical inputs and the literal constant are charged. -/
theorem inputSize_caps (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    1 ≤ inputSize a q width ∧ (tape a).length ≤ inputSize a q width ∧
      q ≤ inputSize a q width ∧ width.length ≤ inputSize a q width := by unfold inputSize;omega
/-- Each actual outer-loop word is bounded independently, before any call-specific real scratch allocation. -/
theorem outer_bound (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool)
    (remaining built : ℕ) (reversed : List SemiprimeRationalBits.RationalWord) (s c u : ℕ)
    (hw : width.length ≤ s) (ha : (tape a).length ≤ u) (hq : q ≤ u) (hr : remaining ≤ u)
    (hb : built ≤ u) (hp : (tape reversed).length ≤ u) (hu : 1 ≤ u) :
    BoundedBank (outer a q width remaining built reversed) s c u := by
  refine ⟨?_,?_,?_⟩
  · intro k
    change (if k=R.aux .template then width else []).length ≤ s
    split
    · exact hw
    · exact Nat.zero_le _
  · intro r den;exact Nat.zero_le _
  · intro k
    cases k <;> simp only [outer,outerAux,unary,List.length_replicate,List.length_cons,List.length_nil] <;> omega
/-- ALL raw cached coefficients have small fields, independently of validity and empty W. -/
theorem cached_words (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) (n : ℕ) :
    ∀word∈(SemiprimeNormalizedInverseBits.build width a.toArray n).words.toList.reverse,
      bytes word ≤ 5*inputSize a q width := by
  intro word hw
  have h:=build_bytes width a.toArray n word (List.mem_reverse.mp hw)
  have hs:=inputSize_caps a q width
  omega
/-- All physically framed cached-prefix bytes are paid by q/W VALUES and their original input cells. -/
theorem prefix_le (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool)
    (n : ℕ) (hn : n ≤ q) :
    (tape (SemiprimeNormalizedInverseBits.build width a.toArray n).words.toList.reverse).length ≤
      14*(inputSize a q width)^2 := by
  let s:=inputSize a q width
  have hs:=inputSize_caps a q width
  have hp:=build_tape_bytes width a.toArray n
  have hns:n ≤ s:=hn.trans hs.2.2.1
  have hprod:n*width.length ≤ s*s:=Nat.mul_le_mul hns hs.2.2.2
  have hs2:s ≤ s^2:=Nat.le_pow (by decide:0<2)
  change _ ≤ 14*s^2
  nlinarith only [hp,hns,hprod,hs.1,hs2]
/-- Full actual indexed accumulator bank stays bounded while all query markers are physically popped. -/
theorem indexed_bound (w : Words) (s : ℕ) (hs : 1 ≤ s) (h : BoundedBank w s (5*s) (14*s^2))
    (terms a b : ℕ) (ht : terms ≤ s) (ha : a ≤ s) (hb : b ≤ s)
    (word : SemiprimeRationalBits.RationalWord) (hw : bytes word ≤ 5*s) :
    BoundedBank (indexed w terms a b word) s (5*s) (14*s^2) := by
  have hs2:s ≤ s^2:=Nat.le_pow (by decide:0<2)
  apply put_bound _ _ _ _ (counters_bound w s (5*s) (14*s^2) h terms a b (by nlinarith) (by nlinarith) (by nlinarith)) .acc word hw
/-- Fixed inventory mass includes all58 data words and every allocated arithmetic shadow. -/
theorem mass_small (w : Words) (s : ℕ) (_hs : 1 ≤ s) (h : BoundedBank w s (5*s) (14*s^2)) :
    SemiprimeD1StackNormalizedInverseCleanup.mass (store w) ≤ 300*s^2 := by
  have hm:=mass_le w s (5*s) (14*s^2) h
  have hs2:s ≤ s^2:=Nat.le_pow (by decide:0<2)
  nlinarith only [hm,hs2]
end RiemannGaussian.SemiprimeD1StackNormalizedInverseStateBounds
