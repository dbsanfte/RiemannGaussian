/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineExecution
/-! # Semantic fitted-word, original multiplicity and physical vector byte caps
No arithmetic operand width is obtained from an elapsed clock. Literal ONE
and ZERO exceptions are charged even W0; every actual fit retains W bytes.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineByteCaps
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeRationalBits (RationalWord)
/-- Fitted raw fields or the literal one-byte seeds, including W0. -/
def Small (width:List Bool) (x:RationalWord):Prop:=
  x.numerator.magnitude.length≤width.length+1 ∧ x.denominator.length≤width.length+1
/-- Literal ONE always has both actual one-byte fields, independently of fitted W. -/
theorem one_small (width:List Bool):Small width SemiprimeJetBits.oneWord:=by
  simp [Small,SemiprimeJetBits.oneWord]
/-- Missing-array literal ZERO has an EMPTY binary magnitude and actual denominatorONE. -/
theorem zero_small (width:List Bool):Small width SemiprimeRationalBits.zeroWord:=by
  simp [Small,SemiprimeRationalBits.zeroWord]
/-- Every actually executed ordered dot ends in a real twice-fitted scalar addition. -/
theorem descend_lengths (width:List Bool) (xs:List RationalWord) (c:RationalWord) (part:Part) (n:Nat) (suffix:RationalWord):
    let x:=SemiprimeD1StackRecoveryAffineConvolution.descend width xs c part n suffix
    x.numerator.magnitude.length=width.length ∧ x.denominator.length=width.length:=by
  induction n generalizing part suffix with
  | zero=>exact SemiprimeD1StackRecoveryGridByteBounds.operation_lengths .add _ _ width
  | succ n ih=>exact ih (nextPart part) _
/-- Current-coefficient source words retain their semantic fit width even W0. -/
theorem coefficient_small (width:List Bool) (xs:List RationalWord) (c:RationalWord) (n:Nat):
    Small width (SemiprimeD1StackRecoveryAffineCoefficient.answer xs c width n):=by
  obtain ⟨hn,hd⟩:=descend_lengths width xs c .unit n SemiprimeRationalBits.zeroWord
  exact ⟨hn.le.trans (by omega),hd.le.trans (by omega)⟩
/-- An actual indexed read returns a retained small word or the physical literal ZERO. -/
theorem read_small (width:List Bool) (xs:List RationalWord) (n:Nat) (hx:∀x∈xs,Small width x):
    Small width (SemiprimeD1StackRecoveryAffineReadLoop.wordAt xs n):=by
  induction xs generalizing n with
  | nil=>exact zero_small width
  | cons x xs ih=>cases n with
    | zero=>exact hx x List.mem_cons_self
    | succ n=>exact ih n (fun y hy=>hx y (List.mem_cons_of_mem x hy))
/-- The fixed finite factor branch has bounded literal/acquired physical words. -/
theorem factor_small (width:List Bool) (part:Part) (c:RationalWord) (hc:Small width c):
    Small width (SemiprimeD1StackRecoveryAffineFactor.value part c):=by
  cases part with
  | unit=>exact one_small width
  | slope=>exact hc
  | zero=>exact zero_small width
/-- Every acquired output coefficient has the actual fit width, without assuming values fit semantically. -/
theorem multiply_small (width:List Bool) (xs:List RationalWord) (c:RationalWord) (q:Nat):
    ∀x∈SemiprimeD1StackRecoveryAffineLoopView.multiply width xs c q,Small width x:=by
  intro x hx
  change x∈(SemiprimeJetBits.multiplyBits width xs.toArray #[SemiprimeJetBits.oneWord,c] q).words.toList at hx
  rw [←SemiprimeD1StackRecoveryAffineCoefficientsOriginal.values_original] at hx
  rcases List.mem_map.mp hx with ⟨i,_,rfl⟩
  exact coefficient_small width xs c i
/-- Physical output array cardinality is the actual q countdown, including q0. -/
theorem multiply_length (width:List Bool) (xs:List RationalWord) (c:RationalWord) (q:Nat):
    (SemiprimeD1StackRecoveryAffineLoopView.multiply width xs c q).length=q:=by
  change (SemiprimeJetBits.multiplyBits width xs.toArray #[SemiprimeJetBits.oneWord,c] q).words.toList.length=q
  rw [←SemiprimeD1StackRecoveryAffineCoefficientsOriginal.values_original]
  simp only [SemiprimeD1StackRecoveryAffineCoefficientsOriginal.values,List.length_map,List.length_range]
/-- All original slope repetitions have exactly W-byte fitted raw fields. -/
theorem slopes_lengths (a M u:Nat) (selected:Fin (2^(a+1))) (width:List Bool):
    ∀x∈SemiprimeD1StackRecoveryAffineOriginalInput.slopes a M u selected width,
      x.numerator.magnitude.length=width.length ∧ x.denominator.length=width.length:=by
  have h:=SemiprimeD1StackRecoveryGridByteBounds.loop_lengths width a (SemiprimeD1TaperedLoss.height M u) u selected.val
    (SemiprimeD1RecoveryWeightRun.geometry a selected.val)
    (SemiprimeD1RecoveryPowerBits.power width SemiprimeD1RecoveryGridBits.twoWord a).word
    (SemiprimeD1RecoveryPowerBits.power width SemiprimeD1RecoveryGridBits.twoWord (a+1)).word
    (SemiprimeD1RecoveryGridBits.index a selected.val).word
    (SemiprimeD1RecoveryScalarRun.indices (SemiprimeD1RecoveryWeightRun.geometry a selected.val).size).value
  exact h.2.2.2.2
/-- Actual acquired slope words, including every repeated occurrence, have the paid fit/literal cap. -/
theorem slopes_small (a M u:Nat) (selected:Fin (2^(a+1))) (width:List Bool):
    ∀x∈SemiprimeD1StackRecoveryAffineOriginalInput.slopes a M u selected width,Small width x:=by
  intro x hx
  obtain ⟨hn,hd⟩:=slopes_lengths a M u selected width x hx
  exact ⟨hn.le.trans (by omega),hd.le.trans (by omega)⟩
/-- True acquired q is bounded by actually acquired M/u metadata VALUES, including u0. -/
theorem retained_le (a M u:Nat) (selected:Fin (2^(a+1))):
    SemiprimeD1StackRecoveryAffineEncoding.retained a M u selected≤3*M+u:=by
  apply le_trans (Nat.mul_le_mul_left (SemiprimeD1TaperedLoss.height M u) (Nat.sub_le _ _))
  exact SemiprimeD1StackRecoveryGridByteBounds.height_product M u
/-- True acquired slope count pays all grid rows and all original multiplicity repetitions. -/
theorem slopes_count (a M u:Nat) (selected:Fin (2^(a+1))) (width:List Bool):
    (SemiprimeD1StackRecoveryAffineOriginalInput.slopes a M u selected width).length≤2^(a+1)*(3*M+u):=by
  have h:=SemiprimeD1StackRecoveryGridByteBounds.loop_slope_count width a (SemiprimeD1TaperedLoss.height M u) u selected.val
    (SemiprimeD1RecoveryWeightRun.geometry a selected.val)
    (SemiprimeD1RecoveryPowerBits.power width SemiprimeD1RecoveryGridBits.twoWord a).word
    (SemiprimeD1RecoveryPowerBits.power width SemiprimeD1RecoveryGridBits.twoWord (a+1)).word
    (SemiprimeD1RecoveryGridBits.index a selected.val).word
    (SemiprimeD1RecoveryScalarRun.indices (SemiprimeD1RecoveryWeightRun.geometry a selected.val).size).value
  rw [SemiprimeD1RecoveryScalarRun.indices_value,SemiprimeD1RecoveryWeightRun.geometry_size,List.length_range] at h
  simpa only [SemiprimeD1StackRecoveryAffineOriginalInput.slopes,SemiprimeD1RecoveryGridBits.acquire,
    SemiprimeD1RecoveryScalarRun.indices_value,SemiprimeD1RecoveryWeightRun.geometry_size,SemiprimeD1WireKernelOriginal.size] using
    h.trans (Nat.mul_le_mul_left _ (SemiprimeD1StackRecoveryGridByteBounds.height_product M u))
/-- Complete framed byte mass includes sign/tag/delimiters and every repeated fitted word. -/
theorem vector_length (width:List Bool) (xs:List RationalWord) (hx:∀x∈xs,Small width x):
    (vector xs).length≤xs.length*(4*width.length+9)+1:=by
  have h:=SemiprimeD1StackRecoveryGridByteBounds.slopeTape_length xs (2*(width.length+1))
    (by intro x hm;obtain ⟨hn,hd⟩:=hx x hm;omega)
  change (vector xs).length≤xs.length*(2*(2*(width.length+1))+5)+1 at h
  rw [show 2*(2*(width.length+1))+5=4*width.length+9 by omega] at h
  exact h
end RiemannGaussian.SemiprimeD1StackRecoveryAffineByteCaps
