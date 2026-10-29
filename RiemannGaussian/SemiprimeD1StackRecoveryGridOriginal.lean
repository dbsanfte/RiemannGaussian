/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridFinishMeaning
import RiemannGaussian.SemiprimeD1StackRecoveryGridLoopMeaning
/-! # Exact entire original recovery-grid byte bank
All old reports occur only in semantic byte/value equalities. The whole actual
five-input program and its own clock were already closed independently.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridOriginal
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridOperationInput
namespace Exec
export SemiprimeD1StackRecoveryGridExecution (result done source_run runBound)
end Exec
namespace Finish
export SemiprimeD1StackRecoveryGridFinishMeaning (result source_result scalar argument point inverse negative)
end Finish
namespace Model
export SemiprimeD1StackRecoveryGridModel (node node_original)
end Model
namespace Old
export SemiprimeD1RecoveryGridBits (acquire index)
export SemiprimeD1StackRecoveryGridOriginalStep (payload)
end Old
/-- Exact retained actual node bytes, including canonical old high padding. -/
theorem node_original (a:Nat) (selected:Fin (2^(a+1))) (t:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) :Model.node a t=(Old.index a selected.val).word:=
  Model.node_original a selected.val t ht selected.isLt
/-- The actual final local argument equals the authoritative original byte word, even W0 and negative-zero cases. -/
theorem argument_original (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) :Finish.argument a t width=(Old.acquire width a M u selected).argument:=by
  dsimp only [Finish.argument,Finish.point,Finish.negative,Finish.inverse]
  rw [node_original a selected t ht]
  rfl
/-- Exact complete physical register file, including both outputs and all16 cleared transient fields. -/
theorem registers_original (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) :
    (Finish.result a M u t width (Old.payload (Old.acquire width a M u selected).grid)).registers=
      SemiprimeD1StackRecoveryGridEncoding.registerBank a selected.val (Old.acquire width a M u selected):=by
  have hn:=node_original a selected t ht
  have ha:=argument_original a M u selected t width ht
  funext k
  rcases k with ⟨r,b⟩
  cases r <;> cases b <;> first
    | rfl
    | exact congrArg signed hn
    | exact congrArg (fun x:SemiprimeRationalBits.RationalWord=>x.denominator) hn
    | exact congrArg signed ha
    | exact congrArg (fun x:SemiprimeRationalBits.RationalWord=>x.denominator) ha
/-- Every104 actual stopped word equals EXACT legacy acquire bytes; source/height/template caches and all cleared helpers are included. -/
theorem result_original (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) :
    Exec.result a M u t width=SemiprimeD1StackRecoveryGridEncoding.result a M u selected t width:=by
  rw [Finish.source_result,SemiprimeD1StackRecoveryGridLoopMeaning.acquire_payload a M u selected t width ht]
  funext k
  rcases k with k|k
  · change emptyRational width k=Function.update (fun _=>[]) (SemiprimeD1StackRationalOperation.aux .template) width k
    rw [SemiprimeD1StackRecoveryGridOperation.emptyRational_explicit]
    by_cases hk:k=SemiprimeD1StackRationalOperation.aux .template
    · subst k;rfl
    · simp only [ite_eq_right hk,Function.update_of_ne hk]
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · rcases k with k|k
          · exact congrFun (registers_original a M u selected t width ht) k
          · cases k <;> rfl
/-- The SAME actual five-input source, not a prepared answer boundary, produces all original grid bytes within its own whole clock. -/
theorem source_run_original (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) :
    ∃q≤ Exec.runBound a M u t width,SemiprimeD1StackCalls.run program q
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)=
        some (SemiprimeD1StackRecoveryGridEncoding.done a M u selected t width):=by
  obtain ⟨q,hq,h⟩:=Exec.source_run a M u t width
  have he:Exec.done a M u t width=SemiprimeD1StackRecoveryGridEncoding.done a M u selected t width:=by
    unfold Exec.done SemiprimeD1StackRecoveryGridEncoding.done
    rw [result_original a M u selected t width ht]
  rw [he] at h
  exact ⟨q,hq,h⟩
end RiemannGaussian.SemiprimeD1StackRecoveryGridOriginal
