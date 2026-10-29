/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipeSpec
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRecipeCalls
open SemiprimeD1StackPortOwnerRecipe
open SemiprimeD1StackProcedureTrace (Runs included_call)
open SemiprimeD1StackUnaryDivmod (unary)
namespace Rel
export SemiprimeD1StackMultiplierLink (DataRel)
end Rel
/-- A physical local update has exactly its included global update, preserving all foreign roles. -/
theorem update_rel {A K:Type} [DecidableEq A] [DecidableEq K]
    (stack:A→K) (hi:Function.Injective stack) (original:K→List Bool)
    (source:A→List Bool) (target:K→List Bool) (hr:Rel.DataRel stack original source target)
    (role:A) (word:List Bool) :
    Rel.DataRel stack original (Function.update source role word) (Function.update target (stack role) word) := by
  constructor
  · intro k
    simp only [Function.update_apply,hi.eq_iff]
    split_ifs <;> first | rfl | exact hr.1 k
  · intro k hk
    rw [Function.update_of_ne (fun he=>hk role he.symm)]
    exact hr.2 k hk
/-- Every actually used copy inclusion has three distinct data roles. -/
theorem copy_injective : ∀task:Copy,Function.Injective (copyStack task) := by decide
/-- Every actual arithmetic inclusion has seven distinct physical data roles. -/
theorem madd_injective : ∀task:Madd,Function.Injective (maddStack task) := by decide
/-- Both divisions have six distinct physical data roles. -/
theorem divide_injective : ∀second:Bool,Function.Injective (divideStack second) := by decide
/-- All three real comparisons have four distinct physical roles. -/
theorem less_injective : ∀check:Check,Function.Injective (lessStack check) := by decide
/-- Each physical field has its own distinct output and scratch roles. -/
theorem frame_injective : ∀recipe:Recipe,∀part:Fin 6,Function.Injective (frameStack recipe part) := by decide
/-- Actual preserving Copy; the endpoint compiler supplies no copied-word answer. -/
theorem copy_call (task:Copy) (store:Stack→List Bool) (pc next:Label)
    (hs:store (aux .copyScratch)=[])
    (hc:program pc=.call (.copy task 0) next) :
    Runs program (5*(store (copyOperands task).1).length+4) pc store next
      (Function.update store (copyOperands task).2
        (store (copyOperands task).1++store (copyOperands task).2)) := by
  let source:=SemiprimeD1StackCopy.state 0 none (store (copyOperands task).1) (store (copyOperands task).2) []
  let finish:=SemiprimeD1StackCopy.done (store (copyOperands task).1)
    (store (copyOperands task).1++store (copyOperands task).2)
  apply included_call program (copyStack task) (Label.copy task) (copy_injective task)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc _ source finish
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words _ _ none
  · constructor
    · intro k;fin_cases k <;> simp [source,copyStack,SemiprimeD1StackCopy.state,SemiprimeD1StackCopy.payload,hs]
    · intro k _;rfl
  · have hi:Rel.DataRel (copyStack task) store source.store store:=by
      constructor
      · intro k;fin_cases k <;> simp [source,copyStack,SemiprimeD1StackCopy.state,SemiprimeD1StackCopy.payload,hs]
      · intro k _;rfl
    have he:Function.update source.store (1:Fin 3)
        (store (copyOperands task).1++store (copyOperands task).2)=finish.store:=by
      funext k;fin_cases k <;> rfl
    simpa only [he,copyStack,show ¬(1:Fin 3)=0 by decide,ite_false,ite_true] using
      update_rel (copyStack task) (copy_injective task) store source.store store hi 1
        (store (copyOperands task).1++store (copyOperands task).2)
/-- Actual nested Copy/Product/Copy from acquired unary operands, retaining all foreign roles. -/
theorem madd_call (task:Madd) (store:Stack→List Bool) (pc next:Label) (a b c:ℕ)
    (ha:store (maddStack task (.inl .a))=unary a)
    (hb:store (maddStack task (.inl .b))=unary b)
    (hc:store (maddStack task (.inl .c))=unary c)
    (hm:store (aux .multiplier)=[]) (hp:store (aux .productScratch)=[])
    (hs:store (aux .maddScratch)=[]) (ho:store (maddStack task (.inr .output))=[])
    (hcall:program pc=.call (.madd task (.inl .start)) next) :
    ∃time≤SemiprimeD1StackPortOwnerMaddBounds.budget a b c+1,
      Runs program time pc store next
        (Function.update store (maddStack task (.inr .output)) (unary (a*b+c))) := by
  obtain ⟨time,ht,hr⟩:=SemiprimeD1StackPortOwnerMaddExecution.source_run a b c
  simp only [maddStack] at ha hb hc ho
  refine ⟨time+1,by exact Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program (maddStack task) (Label.madd task)
    (madd_injective task) M.program (.inl .start) (fun _=>rfl) pc next hcall time
    (SemiprimeD1StackPortOwnerMaddExecution.initial a b c)
    (SemiprimeD1StackPortOwnerMaddExecution.done a b c)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;rcases k with k|k <;> cases k <;>
        simp [SemiprimeD1StackPortOwnerMaddExecution.initial,SemiprimeD1StackPortOwnerMadd.data,
          ha,hb,hc,maddStack,hm,hp,hs,ho]
    · intro k _;rfl
  · let before:=(SemiprimeD1StackPortOwnerMaddExecution.initial a b c).data
    let after:=(SemiprimeD1StackPortOwnerMaddExecution.done a b c).data
    have hi:Rel.DataRel (maddStack task) store before store:=by
      constructor
      · intro k;rcases k with k|k <;> cases k <;>
          simp [before,SemiprimeD1StackPortOwnerMaddExecution.initial,SemiprimeD1StackPortOwnerMadd.data,
            ha,hb,hc,maddStack,hm,hp,hs,ho]
      · intro k _;rfl
    have he:Function.update before (.inr .output) (unary (a*b+c))=after:=by
      funext k;rcases k with k|k <;> cases k <;> rfl
    simpa only [he] using update_rel (maddStack task) (madd_injective task) store before store hi
      (.inr .output) (unary (a*b+c))
/-- Actual unary division from a copied coordinate; all scratch/quotient/remainder work is retained. -/
theorem divide_call (second:Bool) (store:Stack→List Bool) (pc next:Label) (n d:ℕ)
    (hn:store (divideStack second .input)=unary n) (hd:store (divideStack second .divisor)=unary d)
    (hc:store (divideStack second .copied)=[]) (hs:store (divideStack second .scratch)=[])
    (hq:store (divideStack second .quotient)=[]) (hr:store (divideStack second .remainder)=[])
    (hcall:program pc=.call (.divide second D.entry) next) :
    ∃time≤100*(n+d+1)+1,Runs program time pc store next
      (Function.update (Function.update (Function.update store (divideStack second .input) [])
        (divideStack second .quotient) (unary (n/d))) (divideStack second .remainder) (unary (n%d))) := by
  obtain ⟨time,ht,hbody⟩:=SemiprimeD1StackUnaryDivmodBytecode.divide_run n d
  refine ⟨time+1,Nat.add_le_add_right ht 1,?_⟩
  let before:=SemiprimeD1StackUnaryDivmod.contents (unary n) (unary d) [] [] [] []
  let after:=SemiprimeD1StackUnaryDivmod.contents [] (unary d) [] [] (unary (n/d)) (unary (n%d))
  have hi:Rel.DataRel (divideStack second) store before store:=by
    constructor
    · intro k;cases k <;> simp [before,SemiprimeD1StackUnaryDivmod.contents,hn,hd,hc,hs,hq,hr]
    · intro k _;rfl
  apply included_call program (divideStack second) (Label.divide second) (divide_injective second)
    D.code D.entry (fun _=>rfl) pc next hcall time
    (⟨some D.entry,none,before⟩:SemiprimeD1StackBytecode.State D.Stack D.Label)
    (⟨none,none,after⟩:SemiprimeD1StackBytecode.State D.Stack D.Label)
  · rfl
  · rfl
  · exact hbody
  · exact hi
  · have h0:=update_rel (divideStack second) (divide_injective second) store before store hi .input []
    have h1:=update_rel (divideStack second) (divide_injective second) store _ _ h0 .quotient (unary (n/d))
    have h2:=update_rel (divideStack second) (divide_injective second) store _ _ h1 .remainder (unary (n%d))
    have he:Function.update (Function.update (Function.update before .input []) .quotient (unary (n/d)))
        .remainder (unary (n%d))=after:=by
      funext k;cases k <;> rfl
    simpa only [he] using h2
/-- Actual strict unary comparison, including both operand clears and the physically written bit. -/
theorem less_call (check:Check) (store:Stack→List Bool) (pc next:Label) (n d:ℕ)
    (hn:store (lessStack check .left)=unary n) (hz:store (lessStack check .right)=[])
    (hd:store (lessStack check .limit)=unary d) (hv:store (lessStack check .valid)=[])
    (hcall:program pc=.call (.less check L.entry) next) :
    ∃time≤30*(n+d+1)+11,Runs program time pc store next
      (Function.update (Function.update (Function.update store (lessStack check .left) [])
        (lessStack check .limit) []) (lessStack check .valid) [decide (n<d)]) := by
  obtain ⟨time,ht,hbody⟩:=SemiprimeD1StackUnarySumLessBytecode.compare_run n 0 d
  simp only [Nat.add_zero] at ht hbody
  refine ⟨time+1,by omega,?_⟩
  let before:=SemiprimeD1StackUnarySumLess.contents (unary n) [] (unary d) []
  let after:=SemiprimeD1StackUnarySumLess.contents [] [] [] [decide (n<d)]
  have hi:Rel.DataRel (lessStack check) store before store:=by
    constructor
    · intro k;cases k <;> simp [before,SemiprimeD1StackUnarySumLess.contents,hn,hz,hd,hv]
    · intro k _;rfl
  apply included_call program (lessStack check) (Label.less check) (less_injective check)
    L.code L.entry (fun _=>rfl) pc next hcall time
    (⟨some L.entry,none,before⟩:SemiprimeD1StackBytecode.State L.Stack L.Label)
    (⟨none,none,after⟩:SemiprimeD1StackBytecode.State L.Stack L.Label)
  · rfl
  · rfl
  · exact hbody
  · exact hi
  · have h0:=update_rel (lessStack check) (less_injective check) store before store hi .left []
    have h1:=update_rel (lessStack check) (less_injective check) store _ _ h0 .limit []
    have h2:=update_rel (lessStack check) (less_injective check) store _ _ h1 .valid [decide (n<d)]
    have he:Function.update (Function.update (Function.update before .left []) .limit [])
        .valid [decide (n<d)]=after:=by
      funext k;cases k <;> rfl
    simpa only [he] using h2
/-- Real field framing prepends one acquired scalar word to the real existing key suffix. -/
theorem frame_call (recipe:Recipe) (part:Fin 6) (store:Stack→List Bool) (pc next:Label)
    (hs:store (aux .frameScratch)=[]) (hc:program pc=.call (.frame recipe part 0) next) :
    Runs program (6*(store (fields recipe ⟨5-part.val,by omega⟩)).length+5) pc store next
      (Function.update store (aux .output)
        (SemiprimeSourceHistogramKeyBits.frame (store (fields recipe ⟨5-part.val,by omega⟩)) (store (aux .output)))) := by
  let word:=store (fields recipe ⟨5-part.val,by omega⟩)
  let tail:=store (aux .output)
  let source:=SemiprimeD1StackFrame.state 0 none word tail []
  let finish:=SemiprimeD1StackFrame.done word (SemiprimeSourceHistogramKeyBits.frame word tail)
  have hi:Rel.DataRel (frameStack recipe part) store source.store store:=by
    constructor
    · intro k;fin_cases k <;> simp [source,SemiprimeD1StackFrame.state,SemiprimeD1StackFrame.payload,frameStack,word,tail,hs]
    · intro k _;rfl
  apply included_call program (frameStack recipe part) (Label.frame recipe part) (frame_injective recipe part)
    SemiprimeD1StackFrame.code 0 (fun _=>rfl) pc next hc _ source finish
  · rfl
  · rfl
  · exact SemiprimeD1StackFrame.frame_words word tail none
  · exact hi
  · have he:Function.update source.store (1:Fin 3) (SemiprimeSourceHistogramKeyBits.frame word tail)=finish.store:=by
      funext k;fin_cases k <;> rfl
    simpa only [he,frameStack,show ¬(1:Fin 3)=0 by decide,ite_false,ite_true] using
      update_rel (frameStack recipe part) (frame_injective recipe part) store source.store store hi 1
        (SemiprimeSourceHistogramKeyBits.frame word tail)
end RiemannGaussian.SemiprimeD1StackPortOwnerRecipeCalls
