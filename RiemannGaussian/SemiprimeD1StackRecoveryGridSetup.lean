/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridGrowth
import RiemannGaussian.SemiprimeD1StackRecoveryGridLiterals
/-! # Original-input literal and grid-dimension acquisition prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridSetup
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackRecoveryGridGrowth SemiprimeD1StackRecoveryGridLiterals
open SemiprimeD1StackProcedureTrace
/-- Complete actual bank after the fixed fifteen physical literal pushes. -/
def seeded (a M u t width:List Bool) :Words:=
  {rational:=(originals a M u t width).rational,
   registers:=fun k=>match k with
    | (.two,false)=>[false,false,true] | (.two,true)=>[true]
    | (.gridNum,false)|(.gridDen,false)=>[false,true]
    | (.gridNum,true)|(.gridDen,true)=>[true] | _=>[],
   auxiliary:=fun k=>match k with
    | .originalA=>a | .originalM=>M | .originalU=>u | .originalT=>t
    | .todo=>[true,true] | .indexTemplate=>[false,false] | .slopes=>[false] | _=>[]}
/-- The fixed literal writes have exactly their original five-input complete-store effect. -/
theorem seeded_eq (a M u t width:List Bool) :
    pushed (input a M u t width) 15=bank (seeded a M u t width):=by
  funext k
  rcases k with k|k
  · by_cases hk:k=SemiprimeD1StackRationalOperation.aux .template
    · subst k
      rfl
    · simp only [pushed,literals,List.take,List.foldl_cons,List.foldl_nil]
      change (if k=SemiprimeD1StackRationalOperation.aux .template then width else [])=Function.update (fun _=>[]) (SemiprimeD1StackRationalOperation.aux .template) width k
      simp only [ite_eq_right hk,Function.update_of_ne hk]
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · rcases k with k|k
          · rcases k with ⟨r,b⟩
            cases r <;> cases b <;> rfl
          · cases k <;> rfl
/-- Growth buffers initially are exactly the physically seeded cells. -/
theorem seeded_buffers (a M u t width:List Bool) :
    buffers (seeded a M u t width) [] [true,true] [] [false,false]=seeded a M u t width:=by
  unfold buffers
  congr 1
  funext k
  cases k <;> rfl
/-- Actual source bank after acquiring N by real marker doubling, retaining all five original tapes. -/
def grown (a:Nat) (M u t width:List Bool) :Words:=
  buffers (seeded (List.replicate a true) M u t width) []
    (List.replicate (2^(a+1)) true) [] (List.replicate (a+2) false)
/-- Own complete original-input prefix budget; the exponential marker output is physically paid. -/
def runBound (a:Nat) :Nat:=16+(5*a+4)+growTime a 2
/-- From the honest original five physical tapes to actual height acquisition, with no supplied grid size. -/
theorem setup_run (a:Nat) (M u t width:List Bool) :
    Runs program (runBound a) (.local .start) (input (List.replicate a true) M u t width)
      (.local .heightCheck) (bank (grown a M u t width)):=by
  let w:=seeded (List.replicate a true) M u t width
  have h0:=literals_run (input (List.replicate a true) M u t width)
  rw [seeded_eq] at h0
  have h1:=PTrace.copy_call .originalA (.local .copyA) (.local .grow) rfl (bank w)
    (List.replicate a true) [] rfl rfl rfl
  change Runs program (5*(List.replicate a true).length+4) _ _ _
    (Function.update (bank w) (aux .scan) (List.replicate a true++[])) at h1
  rw [List.append_nil] at h1
  have hw:buffers w [] [true,true] [] [false,false]=w:=seeded_buffers _ _ _ _ _
  have he:Function.update (bank w) (aux .scan) (List.replicate a true)=
      bank (buffers w (List.replicate a true) [true,true] [] [false,false]):=by
    conv_lhs=>rw [←hw]
    rw [update_scan]
  rw [he] at h1
  have h2:=grow_run w a 2 2
  change Runs program (growTime a 2) (.local .grow)
    (bank (buffers w (List.replicate a true) [true,true] [] [false,false])) _ _ at h2
  have hn:2*2^a=2^(a+1):=by rw [pow_succ];omega
  rw [hn,show 2+a=a+2 by omega] at h2
  simpa only [runBound,List.length_replicate,grown,w] using PTrace.join (PTrace.join h0 h1) h2
/-- Prefix time is polynomial in the genuinely emitted N cells, not merely its binary length. -/
theorem runBound_le (a:Nat) :runBound a≤100*(a+2)*(2^(a+1)+1):=by
  have h:=growTime_le a 2
  have hn:2*2^a=2^(a+1):=by rw [pow_succ];omega
  rw [hn] at h
  have hp:1≤2^(a+1):=Nat.one_le_pow (a+1) 2 (by decide)
  unfold runBound
  nlinarith
end RiemannGaussian.SemiprimeD1StackRecoveryGridSetup
