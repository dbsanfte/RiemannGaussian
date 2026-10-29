/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootNetworkRecords

/-! # Actual preserving copies, byte reversals and root-record caller stores -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootNetworkRecordsPrimitives
open SemiprimeD1StackRootNetworkRecords SemiprimeD1StackProcedureTrace
local notation "ctl" => (Sum.inl : Control→Label)
/-- Actual trace concatenation in this one literal caller. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after) :
    Runs program (m+n) pc before next after :=runs_trans program m n pc mid next before between after h g
/-- A physical write inside the retained factor bank changes that role alone. -/
theorem update_factor (f:F.Stack→List Bool) (o:O.Stack→List Bool) (a:Aux→List Bool)
    (k:F.Stack) (xs:List Bool) :
    Function.update (data f o a) (factorStack k) xs=data (Function.update f k xs) o a := by
  unfold data factorStack
  rw [Sum.update_elim_inl]
/-- A physical write inside the retained owner bank changes that role alone. -/
theorem update_owner (f:F.Stack→List Bool) (o:O.Stack→List Bool) (a:Aux→List Bool)
    (k:O.Stack) (xs:List Bool) :
    Function.update (data f o a) (ownerStack k) xs=data f (Function.update o k xs) a := by
  unfold data ownerStack
  rw [Sum.update_elim_inr,Sum.update_elim_inl]
/-- A caller-work write leaves both whole acquired source banks unchanged. -/
theorem update_aux (f:F.Stack→List Bool) (o:O.Stack→List Bool) (a:Aux→List Bool)
    (k:Aux) (xs:List Bool) :
    Function.update (data f o a) (aux k) xs=data f o (Function.update a k xs) := by
  unfold data aux
  rw [Sum.update_elim_inr,Sum.update_elim_inr]
/-- Actual join-stage boundary, with the restoring scratch physically empty. -/
def work (f:F.Stack→List Bool) (o:O.Stack→List Bool) (number pre left rev out:List Bool) : Stack→List Bool :=
  data f o (words number pre left rev out [])
/-- The physical left-copy destination update has its exact boundary form. -/
theorem update_left (f:F.Stack→List Bool) (o:O.Stack→List Bool) (number pre left rev out xs:List Bool) :
    Function.update (work f o number pre left rev out) (aux .left) xs=work f o number pre xs rev out := by
  unfold work
  rw [update_aux]
  congr 1
  funext k;cases k <;> simp [words,Function.update]
/-- The physical reverse workspace update has its exact boundary form. -/
theorem update_reverse (f:F.Stack→List Bool) (o:O.Stack→List Bool) (number pre left rev out xs:List Bool) :
    Function.update (work f o number pre left rev out) (aux .reverse) xs=work f o number pre left xs out := by
  unfold work
  rw [update_aux]
  congr 1
  funext k;cases k <;> simp [words,Function.update]
/-- The actual joined-output write preserves the two retained source banks. -/
theorem update_output (f:F.Stack→List Bool) (o:O.Stack→List Bool) (number pre left rev out xs:List Bool) :
    Function.update (work f o number pre left rev out) output xs=work f o number pre left rev xs := by
  unfold output work
  rw [update_aux]
  congr 1
  funext k;cases k <;> simp [words,Function.update]
/-- Every real copy reads a distinct retained source and target. -/
theorem copy_source_ne_target (site:Copy) : copySource site≠copyTarget site := by cases site <;> decide
/-- The real restoring scratch is disjoint from every copy target. -/
theorem copy_scratch_ne_target (site:Copy) : aux .scratch≠copyTarget site := by cases site <;> decide
/-- The actual complete restoring-copy call charges all source cells and the real return. -/
theorem copy_call (site:Copy) (pc next:Control)
    (hcode:program (ctl pc)=.call (copyLabel site 0) (ctl next))
    (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (copySource site)=xs) (hy:before (copyTarget site)=ys) (hz:before (aux .scratch)=[]) :
    Runs program (5*xs.length+4) (ctl pc) before (ctl next)
      (Function.update before (copyTarget site) (xs++ys)) := by
  apply included_call program (copyStack site) (copyLabel site) (copy_injective site)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (ctl pc) (ctl next) hcode (5*xs.length+3)
    (SemiprimeD1StackCopy.state 0 none xs ys []) (SemiprimeD1StackCopy.done xs (xs++ys)) before _
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words xs ys none
  · constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hz
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k
      · change Function.update before (copyTarget site) (xs++ys) (copySource site)=xs
        rw [Function.update_of_ne (copy_source_ne_target site),hx]
      · exact Function.update_self _ _ _
      · change Function.update before (copyTarget site) (xs++ys) (aux .scratch)=[]
        rw [Function.update_of_ne (copy_scratch_ne_target site),hz]
    · intro k hk
      exact Function.update_of_ne (fun he=>hk 1 he.symm) _ _
/-- Each real reversal has distinct input and output roles. -/
theorem reverse_ne (second:Bool) : reverseStack second 0≠reverseStack second 1 := by cases second <;> decide
/-- One real consuming reversal call includes every pop/push, EOF, halt and caller return. -/
theorem reverse_call (second:Bool) (pc next:Control)
    (hcode:program (ctl pc)=.call (reverseLabel second 0) (ctl next))
    (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (reverseStack second 0)=xs) (hy:before (reverseStack second 1)=ys) :
    Runs program (2*xs.length+3) (ctl pc) before (ctl next)
      (Function.update (Function.update before (reverseStack second 0) [])
        (reverseStack second 1) (xs.reverse++ys)) := by
  apply included_call program (reverseStack second) (reverseLabel second) (reverse_injective second)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) (ctl pc) (ctl next) hcode (2*xs.length+2)
    (SemiprimeD1StackReverseWord.state none xs ys) (SemiprimeD1StackReverseWord.done (xs.reverse++ys)) before _
  · rfl
  · rfl
  · exact SemiprimeD1StackReverseWord.reverse_run xs ys none
  · constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k
      · change Function.update (Function.update before (reverseStack second 0) [])
          (reverseStack second 1) (xs.reverse++ys) (reverseStack second 0)=[]
        rw [Function.update_of_ne (reverse_ne second),Function.update_self]
      · exact Function.update_self _ _ _
    · intro k hk
      rw [Function.update_of_ne (fun he=>hk 1 he.symm),Function.update_of_ne (fun he=>hk 0 he.symm)]
/-- Exactly one physically read false marker is removed before the second reversal. -/
theorem strip_run (before:Stack→List Bool) (xs:List Bool) (hx:before (aux .reverse)=false::xs) :
    Runs program 1 (ctl .strip) before (ctl .append) (Function.update before (aux .reverse) xs) := by
  apply one_base program (ctl .strip) (ctl .append)
    (.pop (aux .reverse) (ctl .abort) (ctl .append) (ctl .abort)) before _ rfl
  · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,hx]
  · simp [SemiprimeD1StackBytecode.execute,hx]
/-- The whole original-N entry physically acquires its own empty-prefix terminator. -/
theorem seed_run (bits:List Bool) :
    Runs program 1 (ctl .start) (input bits) (ctl .main) (initialPrefix bits [false]).data := by
  apply one_base program (ctl .start) (ctl .main) (.push (aux .prefix) false (ctl .main)) _ _ rfl
  · rfl
  · change Function.update (input bits) (aux .prefix) (false::[])=_
    unfold input initialPrefix
    rw [update_aux]
    congr 1
    funext k;cases k <;> simp [words,Function.update]
end RiemannGaussian.SemiprimeD1StackRootNetworkRecordsPrimitives
