/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffinePrimitives
import RiemannGaussian.SemiprimeD1StackRecoveryAffineView
/-! # Actual old-array drain and two paid reversals move the complete next array -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineArrayMove
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackProcedureTrace
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join drain_loop reverse_call)
end T
/-- Exactly two actual added array words change; every original104 word is restored. -/
def result (w:Words) (bytes:List Bool):Words:=
  {w with added:=Function.update (Function.update w.added .array bytes) .nextArray []}
/-- Every old byte, both real reversal EOF/caller returns and all new bytes are paid. -/
def runBound (old bytes:List Bool):Nat:=old.length+4*bytes.length+7
/-- No host append/move replaces actual I/O: the fixed source drains old then executes both real reversals. -/
theorem source_run (w:Words) (old bytes:List Bool)
    (ho:w.added .array=old) (hn:w.added .nextArray=bytes) (hc:w.auxiliary .copyScratch=[]):
    Runs program (runBound old bytes) (.local .clearArray) (bank w)
      (.local (.clearSlope true false)) (bank (result w bytes)):=by
  let w0:Words:={w with added:=Function.update w.added .array []}
  let w1:Words:={w0 with added:=Function.update w0.added .nextArray []}
  let w2:Words:={w1 with auxiliary:=Function.update w1.auxiliary .copyScratch bytes.reverse}
  let w3:Words:={w2 with auxiliary:=Function.update w2.auxiliary .copyScratch []}
  have h0:=T.drain_loop (.local .clearArray) (.local (.move false)) (aux .array) rfl (bank w) old ho
  rw [update_added] at h0
  change Runs program _ _ _ _ (bank w0) at h0
  have h1:=T.reverse_call false (.local (.move false)) (.local (.move true)) rfl (bank w0) bytes [] hn hc
  change Runs program _ _ _ _ (Function.update (Function.update (bank w0) (aux .nextArray) [])
    (oldAux .copyScratch) (bytes.reverse++[])) at h1
  rw [List.append_nil,update_added,update_oldAux] at h1
  change Runs program _ _ _ _ (bank w2) at h1
  have hsource:bank w2 (reverseStack true 0)=bytes.reverse:=by
    change Function.update w1.auxiliary .copyScratch bytes.reverse .copyScratch=bytes.reverse
    exact Function.update_self _ _ _
  have hdest:bank w2 (reverseStack true 1)=[]:=by
    change Function.update (Function.update w.added .array []) .nextArray [] .array=[]
    simp only [Function.update_of_ne (show Aux.array≠.nextArray from by decide),Function.update_self]
  have h2:=T.reverse_call true (.local (.move true)) (.local (.clearSlope true false)) rfl (bank w2) bytes.reverse []
    hsource hdest
  change Runs program _ _ _ _ (Function.update (Function.update (bank w2) (oldAux .copyScratch) [])
    (aux .array) (bytes.reverse.reverse++[])) at h2
  rw [List.reverse_reverse,List.append_nil,update_oldAux,update_added] at h2
  have hclear:Function.update w.auxiliary .copyScratch []=w.auxiliary:=by rw [←hc,Function.update_eq_self]
  have he:{w3 with added:=Function.update w3.added .array bytes}=result w bytes:=by
    dsimp only [w3,w2,w1,w0,result]
    simp only [Function.update_idem,hclear]
    congr 1
    funext slot
    cases slot <;> simp
  change Runs program _ _ _ _ (bank {w3 with added:=Function.update w3.added .array bytes}) at h2
  rw [he] at h2
  have h:=T.join (T.join h0 h1) h2
  convert h using 1
  simp only [runBound,List.length_reverse]
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryAffineArrayMove
