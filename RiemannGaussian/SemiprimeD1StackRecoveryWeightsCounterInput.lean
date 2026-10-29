/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsSubtract
/-! # Actual q/j copies, paid difference acquisition and both initial physical indices
No decoded count is supplied: proof-side q=j+(n+1) specifies the actual q word
and the actual remaining outer j word. Real scans acquire all derived markers.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsCounterInput
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsCalls SemiprimeD1StackRecoveryWeightsIndices SemiprimeD1StackProcedureTrace
namespace S
export SemiprimeD1StackRecoveryWeightsSubtract (buffers subtract_run)
end S
/-- Exact physical controller-word update. -/
def put (w:Words) (k:I.Aux) (xs:List Bool):Words:={w with auxiliary:=Function.update w.auxiliary k xs}
/-- Actual subtraction has truly disposed of its copied j markers. -/
theorem buffers_done (w:Words) (n:Nat) (ht:w.auxiliary .readTodo=[]):S.buffers w n 0=put w .terms (unary n):=by
  unfold S.buffers put
  apply congrArg (fun f:I.Aux→List Bool=>({w with auxiliary:=f}:Words))
  funext k
  cases k <;> simp [ht,unary]
/-- Every actual input marker, restoring copy/return, subtraction pop and initial index pop is paid. -/
def timeBound (j n:Nat):Nat:=10*(j+(n+1))+5*(n+1)+7*j+19
/-- All three derived physical counters are acquired from ONLY the original q and actual j words. -/
theorem counters_run (w:Words) (j n:Nat)
    (hq:w.auxiliary .originalQ=unary (j+(n+1))) (hj:w.auxiliary .remaining=unary j)
    (ht:w.auxiliary .terms=[]) (hread:w.auxiliary .readTodo=[])
    (ha:w.auxiliary .aIndex=[]) (hb:w.auxiliary .bIndex=[]) (hs:w.auxiliary .copyScratch=[]):
    Runs program (timeBound j n) (.local .copyTerms) (bank w) (.local .terms)
      (bank (counters w (n+1) n (j+n))):=by
  let q:=j+(n+1)
  let w1:=put w .terms (unary q)
  let w2:=put w1 .readTodo (unary j)
  let w3:=put w .terms (unary (n+1))
  let w4:=put w3 .aIndex (unary (n+1))
  let w5:=put w3 .aIndex (unary n)
  let w6:=put w5 .bIndex (unary q)
  let w7:=put w5 .bIndex (unary (j+n))
  have h0:=P.copy_call .terms (.local .copyTerms) (.local .copySubtract) rfl (bank w) (unary q) [] hq ht hs
  change Runs program _ _ _ _ (Function.update (bank w) (aux .terms) (unary q++[])) at h0
  rw [List.append_nil,update_aux] at h0
  have h1:=P.copy_call .subtract (.local .copySubtract) (.local .subtract) rfl (bank w1) (unary j) [] hj
    (by change Function.update w.auxiliary .terms (unary q) .readTodo=[];simpa using hread) hs
  change Runs program _ _ _ _ (Function.update (bank w1) (aux .readTodo) (unary j++[])) at h1
  rw [List.append_nil,update_aux] at h1
  have h2:=S.subtract_run w (n+1) j
  have hbefore:w2=S.buffers w ((n+1)+j) j:=by
    change {w with auxiliary:=Function.update (Function.update w.auxiliary .terms (unary q)) .readTodo (unary j)}=_
    rw [show q=(n+1)+j by omega]
    rfl
  rw [buffers_done w (n+1) hread,←hbefore] at h2
  have h3:=P.copy_call .aIndex (.local .copyA) (.local .predecessorA) rfl (bank w3) (unary (n+1)) []
    (by change Function.update w.auxiliary .terms (unary (n+1)) .terms=unary (n+1);exact Function.update_self _ _ _)
    (by change Function.update w.auxiliary .terms (unary (n+1)) .aIndex=[];simpa using ha) hs
  change Runs program _ _ _ _ (Function.update (bank w3) (aux .aIndex) (unary (n+1)++[])) at h3
  rw [List.append_nil,update_aux] at h3
  have h4:=P.pop_run (.local .predecessorA) abort abort (.local .copyB) (aux .aIndex) (bank w4) (true::unary n) rfl
    (by change Function.update w3.auxiliary .aIndex (unary (n+1)) .aIndex=true::unary n;simp [unary,List.replicate_succ])
  change Runs program 1 _ _ (.local .copyB) (Function.update (bank w4) (aux .aIndex) (unary n)) at h4
  rw [update_aux] at h4
  have hfour:put w4 .aIndex (unary n)=w5:=by simp only [w4,w5,put,Function.update_idem]
  change Runs program 1 _ _ _ (bank (put w4 .aIndex (unary n))) at h4
  rw [hfour] at h4
  have h5:=P.copy_call .bIndex (.local .copyB) (.local .predecessorB) rfl (bank w5) (unary q) [] hq
    (by change Function.update (Function.update w.auxiliary .terms (unary (n+1))) .aIndex (unary n) .bIndex=[];simpa using hb) hs
  change Runs program _ _ _ _ (Function.update (bank w5) (aux .bIndex) (unary q++[])) at h5
  rw [List.append_nil,update_aux] at h5
  have h6:=P.pop_run (.local .predecessorB) abort abort (.local .terms) (aux .bIndex) (bank w6) (true::unary (j+n)) rfl
    (by change Function.update w5.auxiliary .bIndex (unary q) .bIndex=true::unary (j+n)
        rw [Function.update_self]
        change List.replicate (j+(n+1)) true=true::List.replicate (j+n) true
        rw [show j+(n+1)=(j+n)+1 by omega,List.replicate_succ])
  change Runs program 1 _ _ (.local .terms) (Function.update (bank w6) (aux .bIndex) (unary (j+n))) at h6
  rw [update_aux] at h6
  have hsix:put w6 .bIndex (unary (j+n))=w7:=by simp only [w6,w7,put,Function.update_idem]
  change Runs program 1 _ _ _ (bank (put w6 .bIndex (unary (j+n)))) at h6
  rw [hsix] at h6
  have hend:w7=counters w (n+1) n (j+n):=rfl
  rw [hend] at h6
  have hh:=P.join (P.join (P.join (P.join (P.join (P.join h0 h1) h2) h3) h4) h5) h6
  convert hh using 1
  simp only [timeBound,unary,List.length_replicate,q]
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsCounterInput
