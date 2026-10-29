/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortCatalogueLoop
/-! # Actual finite-loop transition and output bounds of the original port transducer -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortCatalogueLoopBounds
open SemiprimeD1StackPortCatalogueLoop SemiprimeD1StackPortCatalogueEmit
open SemiprimeD1EdgeCatalogueEncoding (Record record)
open SemiprimeD1StackEdgeCatalogueParse (wordMass)
open SemiprimeD1StackUnaryDivmod (unary)
/-- Exact actual control-field byte mass, including the physically pushed unary ordinals. -/
theorem mass8_unary (words:Record) (n f slot:ℕ) :
    mass8 words (unary slot) (unary f) (unary n)=n+f+slot+wordMass words := by
  simp only [mass8,unary,List.length_replicate]
/-- A bound for EVERY recursive loop prefix, rather than only a normalized final count. -/
theorem loopTime_le (words:Record) (fuel n f slot:ℕ) :
    loopTime words fuel n f slot≤fuel*(10*(n+f+slot+2*fuel+wordMass words)+83)+1 := by
  induction fuel generalizing n slot with
  | zero => simp [loopTime]
  | succ fuel ih =>
    rw [loopTime,mass8_unary]
    have h:=ih (n+1) (slot+1)
    nlinarith
/-- Literal eight-field output length, including every delimiter. -/
theorem record8_length (words:Record) (slot factor occurrence tail:List Bool) :
    (record8 words slot factor occurrence tail).length=
      2*(occurrence.length+factor.length+slot.length+wordMass words)+tail.length+8 := by
  unfold record8
  simp only [SemiprimeSourceHistogramKeyBits.frame_length,SemiprimeD1StackEdgeCatalogueScan.record_length]
  omega
/-- Every actual recursive output prefix is bounded by its own finite counter/control dimensions. -/
theorem records_length_le (words:Record) (fuel n f slot:ℕ) (tail:List Bool) :
    (records words fuel n f slot tail).length≤
      fuel*(2*(n+f+slot+2*fuel+wordMass words)+8)+tail.length := by
  induction fuel generalizing n slot with
  | zero => simp [records]
  | succ fuel ih =>
    rw [records,record8_length]
    simp only [unary,List.length_replicate]
    have h:=ih (n+1) (slot+1)
    nlinarith
/-- Actual original descriptor arity is bounded by its parsed index and readonly parameters. -/
theorem value_le (code:Fin 18) (index radius first second digits:ℕ) :
    SemiprimeD1StackVertexArityRecipes.value code index radius first second digits≤
      10*(index+radius+first+second+digits+1)^2 := by
  generalize hS:index+radius+first+second+digits+1=S
  have hR:radius≤S:=by omega
  have hF:first≤S:=by omega
  have hT:second≤S:=by omega
  have hS1:1≤S:=by omega
  have hS2:S≤S^2:=Nat.le_pow (by omega)
  have hf:first*radius≤S^2:=by simpa only [pow_two] using Nat.mul_le_mul hF hR
  have ht:second*radius≤S^2:=by simpa only [pow_two] using Nat.mul_le_mul hT hR
  have hff:(first+first)*radius≤2*S^2:=by nlinarith only [hf]
  have htt:(second+second)*radius≤2*S^2:=by nlinarith only [ht]
  fin_cases code <;> norm_num [SemiprimeD1StackVertexArityRecipes.value] <;> (try split_ifs) <;> omega
/-- The original arity follows from the actual descriptor theorem, without an arity supplier. -/
theorem original_arity_le {r t digits:ℕ} (v:SemiprimeMacroGraph.SubdividedVertex r t digits) :
    SemiprimeMacroGraph.subdividedArity v≤
      10*(SemiprimeD1StackVertexArityOriginal.indexValue v+(r*t+1)+r+t+digits+1)^2 := by
  rw [←SemiprimeD1StackVertexArityOriginal.value_original]
  exact value_le _ _ _ _ _ _
end RiemannGaussian.SemiprimeD1StackPortCatalogueLoopBounds
