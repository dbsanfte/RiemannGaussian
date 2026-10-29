/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFactorScopePairEmit
/-! # Exact EOF-controlled all-row projection in unchanged factor-major order -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackFactorScopePairScan
open SemiprimeD1StackFactorScopePairs SemiprimeD1FactorScopePairEncoding
open SemiprimeD1StackFactorScopePairView SemiprimeD1StackFactorScopePairEmit SemiprimeD1StackFactorScopePairPrimitives
open SemiprimeD1StackProcedureFragments (Runs one_base)
/-- Actual row clock includes nine parses, two frames and every cache erasure. -/
def rowTime (w : Record) : Nat :=9*mass w+10*((w 2).length+(w 0).length)+103
/-- Every input row is processed once, including its initial physical peek. -/
theorem row_run (base : S.Stack→List Bool) (w : Record) (tail raw : List Bool) :
    Runs program (rowTime w) (.local .loop) (clean base (record w tail) (fun _=>[]) raw)
      (.local .loop) (clean base tail (fun _=>[]) ((row w).reverse++raw)) := by
  have hp:Runs program 1 (.local .loop) (clean base (record w tail) (fun _=>[]) raw)
      (.local (.field 0)) (clean base (record w tail) (fun _=>[]) raw) := by
    apply one_base program (.local .loop) (.local (.field 0))
      (.peek (aux .reader) (.local .finish) (.local (.field 0)) (.local (.field 0))) _ _ rfl
    · change some (SemiprimeD1StackBytecode.choose _ _ _ (record w tail).head?)=_
      rw [show record w tail=SemiprimeSourceHistogramKeyBits.frame (w 0) (suffix w 1 tail) from suffix_step w 0 tail]
      cases w 0 <;> rfl
    · rfl
  have h:=hp.trans ((SemiprimeD1StackFactorScopePairParse.all_fields base w tail raw).trans
    ((SemiprimeD1StackFactorScopePairEmit.row_run base tail w raw).trans
      (all_clear base tail w ((row w).reverse++raw))))
  simpa only [rowTime,show 1+((8*mass w+72)+((10*((w 2).length+(w 0).length)+21)+(mass w+9)))=
      9*mass w+10*((w 2).length+(w 0).length)+103 by omega] using h
/-- Exact source loop clock, ending at the physical EOF branch. -/
def loopTime : List Record→Nat
  | []=>1
  | w::ws=>rowTime w+loopTime ws
/-- No record list is runtime advice: this theorem describes the actual EOF loop. -/
theorem loop_run (rows : List Record) (base : S.Stack→List Bool) (old : List Bool) :
    Runs program (loopTime rows) (.local .loop) (clean base (stream rows []) (fun _=>[]) old)
      (.local .finish) (clean base [] (fun _=>[]) ((raw rows).reverse++old)) := by
  induction rows generalizing old with
  | nil=>
    apply one_base program (.local .loop) (.local .finish)
      (.peek (aux .reader) (.local .finish) (.local (.field 0)) (.local (.field 0))) _ _ rfl
    · rfl
    · rfl
  | cons w ws ih=>
    have h:=(row_run base w (stream ws []) old).trans (ih ((row w).reverse++old))
    simpa only [loopTime,stream,List.foldr_cons,raw,List.reverse_append,List.append_assoc] using h
/-- Real EOF tag push and final physical reversal, preserving every old source role. -/
theorem finish_run (base : S.Stack→List Bool) (rows : List Record) :
    Runs program (2*(raw rows).length+6) (.local .finish)
      (clean base [] (fun _=>[]) (raw rows).reverse) (.local .done)
      (data base [] (fun _=>[]) [] [] (SemiprimeD1StackOwnerFibre.records (rows.map pair) []) []) := by
  have ht:Runs program 1 (.local .finish) (clean base [] (fun _=>[]) (raw rows).reverse)
      (.local .finalReverse) (clean base [] (fun _=>[]) (false::(raw rows).reverse)) := by
    apply one_base program (.local .finish) (.local .finalReverse)
      (.push (aux .reversed) false (.local .finalReverse)) _ _ rfl
    · rfl
    · exact update_raw _ _ _ _ _ _ _ _
  have hr:=reverse_call true (clean base [] (fun _=>[]) (false::(raw rows).reverse))
    (.local .finalReverse) (.local .done) rfl
  change Runs program (2*(false::(raw rows).reverse).length+3) _ _ _
    (Function.update (Function.update (data base [] (fun _=>[]) (false::(raw rows).reverse) [] [] [])
      (aux .reversed) []) (aux .output) ((false::(raw rows).reverse).reverse++[])) at hr
  rw [update_raw,update_output] at hr
  have h:=ht.trans hr
  simpa only [List.length_cons,List.length_reverse,List.reverse_cons,List.reverse_reverse,List.append_nil,
    raw_records,show 1+(2*((raw rows).length+1)+3)=2*(raw rows).length+6 by omega] using h
/-- Complete actual projection time, including final literal halt. -/
def totalTime (rows : List Record) : Nat :=loopTime rows+2*(raw rows).length+7
/-- Whole fixed source scan; every acquired field is consumed and every output bit written. -/
theorem scan_run (base : S.Stack→List Bool) (rows : List Record) :
    C.run program (totalTime rows)
      ⟨some (.local .loop),none,none,clean base (stream rows []) (fun _=>[]) [],[]⟩=
      some ⟨none,none,none,data base [] (fun _=>[]) [] [] (SemiprimeD1StackOwnerFibre.records (rows.map pair) []) [],[]⟩ := by
  have hl:=loop_run rows base []
  simp only [List.append_nil] at hl
  have h:=hl.trans (finish_run base rows)
  obtain ⟨finish,hr,hAt⟩:=h [] (⟨some (.local .loop),none,none,clean base (stream rows []) (fun _=>[]) [],[]⟩ : C.State Stack Label) ⟨rfl,rfl,rfl⟩
  have he:=SemiprimeD1StackProcedureTrace.halt_run program (.local .done) rfl
    (data base [] (fun _=>[]) [] [] (SemiprimeD1StackOwnerFibre.records (rows.map pair) []) []) [] finish hAt
  rw [show totalTime rows=(loopTime rows+(2*(raw rows).length+6))+1 by unfold totalTime;omega,
    SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,he]
end RiemannGaussian.SemiprimeD1StackFactorScopePairScan
