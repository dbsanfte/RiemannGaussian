/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFactorScopePairParse
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
/-! # Actual pair framing and physical erasure of all nine parsed payloads -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackFactorScopePairEmit
open SemiprimeD1StackFactorScopePairs SemiprimeD1FactorScopePairEncoding
open SemiprimeD1StackFactorScopePairView SemiprimeD1StackFactorScopePairPrimitives
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeSourceHistogramKeyBits (frame frame_length)
/-- Exact physically selected key or scope payload. -/
def word (scope : Bool) (w : Record) : List Bool := if scope then w 0 else w 2
/-- Real preserving Frame then consuming Reverse, with all calls and returns. -/
theorem field_run (scope : Bool) (base : S.Stack→List Bool) (reader : List Bool) (w : Record) (raw : List Bool) :
    Runs program (10*(word scope w).length+10) (.local (.frame scope)) (clean base reader w raw)
      (if scope then .local (.clear 0) else .local (.frame true))
      (clean base reader w ((frame (word scope w) []).reverse++raw)) := by
  have hf:=frame_call scope (clean base reader w raw) rfl rfl
  have he:(clean base reader w raw) (frameSource scope)=word scope w:=by cases scope <;> rfl
  rw [he] at hf
  unfold clean at hf
  rw [update_buffer] at hf
  have hr:=reverse_call false (data base reader w raw (frame (word scope w) []) [] [])
    (.local (.reverse scope)) (if scope then .local (.clear 0) else .local (.frame true)) rfl
  change Runs program (2*(frame (word scope w) []).length+3) _ _ _
    (Function.update (Function.update (data base reader w raw (frame (word scope w) []) [] [])
      (aux .frameBuffer) []) (aux .reversed) ((frame (word scope w) []).reverse++raw)) at hr
  rw [update_buffer,update_raw] at hr
  have h:=hf.trans hr
  simpa only [clean,frame_length,List.length_nil,show (6*(word scope w).length+5)+
      (2*(2*(word scope w).length+0+1)+3)=10*(word scope w).length+10 by omega] using h
/-- One actual row tag and both original physical fields form the exact pair row. -/
theorem row_run (base : S.Stack→List Bool) (reader : List Bool) (w : Record) (raw : List Bool) :
    Runs program (10*((w 2).length+(w 0).length)+21) (.local .tag) (clean base reader w raw)
      (.local (.clear 0)) (clean base reader w ((row w).reverse++raw)) := by
  have ht : Runs program 1 (.local .tag) (clean base reader w raw) (.local (.frame false))
      (clean base reader w (true::raw)) := by
    apply one_base program (.local .tag) (.local (.frame false)) (.push (aux .reversed) true (.local (.frame false))) _ _ rfl
    · rfl
    · exact update_raw _ _ _ _ _ _ _ _
  have h:=ht.trans ((field_run false base reader w (true::raw)).trans
    (field_run true base reader w ((frame (w 2) []).reverse++true::raw)))
  have ht':1+((10*(w 2).length+10)+(10*(w 0).length+10))=10*((w 2).length+(w 0).length)+21:=by omega
  change Runs program (1+((10*(w 2).length+10)+(10*(w 0).length+10))) _ _ _ _ at h
  rw [ht'] at h
  have hb:(frame (w 0) []).reverse++((frame (w 2) []).reverse++true::raw)=(row w).reverse++raw := by
    unfold row
    rw [SemiprimeD1StackEdgeCatalogueEmit.frame_append (w 2) (frame (w 0) [])]
    simp only [List.reverse_cons,List.reverse_append,List.append_assoc,List.cons_append,List.nil_append]
  simp only [word,ite_true] at h
  rw [hb] at h
  exact h
/-- Finite view of caches after exactly n physically erased payloads. -/
def cleared (n : Nat) (w : Record) : Record :=fun k=>if k.val<n then [] else w k
/-- Every fixed cache is actually erased once, including the seven discarded fields. -/
theorem cleared_step (w : Record) (part : Fin 9) :
    Function.update (cleared part.val w) part []=cleared (part.val+1) w := by
  funext k;fin_cases part <;> fin_cases k <;> rfl
/-- All nine physical payloads are actually erased. -/
theorem cleared_end (w : Record) : cleared 9 w=fun _=>[] := by funext k;fin_cases k <;> rfl
/-- Each erasure pays every payload pop and its final EOF pop. -/
theorem clear_run (part : Fin 9) (base : S.Stack→List Bool) (reader : List Bool) (w : Record) (raw : List Bool) :
    Runs program ((w part).length+1) (.local (.clear part))
      (clean base reader (cleared part.val w) raw) (nextClear part)
      (clean base reader (cleared (part.val+1) w) raw) := by
  let before:=clean base reader (cleared part.val w) raw
  have hp:before (cache part)=w part:=by change (if part.val<part.val then [] else w part)=_;simp
  have hi:Function.update before (cache part) (w part)=before:=by rw [←hp];exact Function.update_eq_self _ _
  have h:=SemiprimeD1StackPhysicalLoops.drain program (.local (.clear part)) (nextClear part)
    (cache part) rfl before (w part)
  rw [hi] at h
  change Runs program _ _ _ _ (Function.update (data base reader (cleared part.val w) raw [] [] []) (cache part) []) at h
  rw [update_cache,cleared_step] at h
  exact h
/-- Complete nine-cache erasure, leaving the next physical input row and history. -/
theorem all_clear (base : S.Stack→List Bool) (reader : List Bool) (w : Record) (raw : List Bool) :
    Runs program (mass w+9) (.local (.clear 0)) (clean base reader w raw)
      (.local .loop) (clean base reader (fun _=>[]) raw) := by
  have h:=(clear_run 0 base reader w raw).trans ((clear_run 1 base reader w raw).trans
    ((clear_run 2 base reader w raw).trans ((clear_run 3 base reader w raw).trans
      ((clear_run 4 base reader w raw).trans ((clear_run 5 base reader w raw).trans
        ((clear_run 6 base reader w raw).trans ((clear_run 7 base reader w raw).trans (clear_run 8 base reader w raw))))))))
  have hm : mass w=(w 0).length+((w 1).length+((w 2).length+((w 3).length+((w 4).length+
      ((w 5).length+((w 6).length+((w 7).length+((w 8).length+0)))))))) := rfl
  have ht:((w 0).length+1)+(((w 1).length+1)+(((w 2).length+1)+(((w 3).length+1)+
      (((w 4).length+1)+(((w 5).length+1)+(((w 6).length+1)+(((w 7).length+1)+((w 8).length+1))))))))=mass w+9:=by omega
  rw [ht] at h
  change Runs program (mass w+9) (.local (.clear 0)) (clean base reader (cleared 0 w) raw)
    (.local .loop) (clean base reader (cleared 9 w) raw) at h
  have hz:cleared 0 w=w:=by funext k;simp [cleared]
  rw [cleared_end,hz] at h
  exact h
end RiemannGaussian.SemiprimeD1StackFactorScopePairEmit
