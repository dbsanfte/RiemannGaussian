/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexPrimitives
/-! # Actual source copies and acquired-width binary owner-counter initialization
The unary left-count input is copied and physically traversed to allocate a
zero binary word of width n+1. No native bit-length, counter or zero-word answer
is an instruction or initially supplied payload.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexSetup
open SemiprimeD1StackNetworkOwnerIndex SemiprimeD1StackNetworkOwnerIndexPrimitives
open SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Whole source boundary: all unlisted parser/frame/counter work words are physically empty. -/
def view (vertices count reader todo ports owner history:List Bool) :Stack→List Bool
  | .vertices=>vertices | .leftCount=>count | .reader=>reader | .todo=>todo
  | .ports=>ports | .owner=>owner | .history=>history | _=>[]
/-- Literal input has no acquired counter, dictionary, work or factor-reader suffix yet. -/
theorem input_view (vertices count:List Bool) :input vertices count=view vertices count [] [] [] [] [] :=by
  funext k;cases k <;> rfl
/-- Updating the physical record reader leaves every original input/cache word unchanged. -/
theorem view_reader (vertices count reader todo ports owner history xs:List Bool) :
    Function.update (view vertices count reader todo ports owner history) .reader xs=
      view vertices count xs todo ports owner history :=by
  funext k;cases k <;> simp [view,Function.update]
/-- Updating the physical countdown leaves the acquired original count unchanged. -/
theorem view_todo (vertices count reader todo ports owner history xs:List Bool) :
    Function.update (view vertices count reader todo ports owner history) .todo xs=
      view vertices count reader xs ports owner history :=by
  funext k;cases k <;> simp [view,Function.update]
/-- Updating the current port-vector reader does not alter either original tape. -/
theorem view_ports (vertices count reader todo ports owner history xs:List Bool) :
    Function.update (view vertices count reader todo ports owner history) .ports xs=
      view vertices count reader todo xs owner history :=by
  funext k;cases k <;> simp [view,Function.update]
/-- Updating the physical binary owner word changes exactly its actual counter address. -/
theorem view_owner (vertices count reader todo ports owner history xs:List Bool) :
    Function.update (view vertices count reader todo ports owner history) .owner xs=
      view vertices count reader todo ports xs history :=by
  funext k;cases k <;> simp [view,Function.update]
/-- Updating actual reverse pair history retains the current owner and unconsumed vertex/port bytes. -/
theorem view_history (vertices count reader todo ports owner history xs:List Bool) :
    Function.update (view vertices count reader todo ports owner history) .history xs=
      view vertices count reader todo ports owner xs :=by
  funext k;cases k <;> simp [view,Function.update]
/-- The source physically copies the whole record tape exactly once. -/
theorem records_copy (vertices count:List Bool) :
    Runs program (5*vertices.length+4) (ctl .start) (input vertices count) (ctl .zeroCount)
      (view vertices count vertices [] [] [] []) :=by
  rw [input_view]
  have h:=copy_call .vertices .start .zeroCount rfl (view vertices count [] [] [] [] []) vertices [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view vertices count [] [] [] [] []) .reader (vertices++[])) at h
  simpa only [List.append_nil,view_reader] using h
/-- Each count copy reads the retained original left-count word and charges every marker. -/
theorem count_copy (pc next:Control) (vertices count reader ports owner history:List Bool)
    (hc:program (ctl pc)=.call (.copy .count 0) (ctl next)) :
    Runs program (5*count.length+4) (ctl pc) (view vertices count reader [] ports owner history) (ctl next)
      (view vertices count reader count ports owner history) :=by
  have h:=copy_call .count pc next hc (view vertices count reader [] ports owner history) count [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view vertices count reader [] ports owner history) .todo (count++[])) at h
  simpa only [List.append_nil,view_todo] using h
/-- One literal false bit seeds the original width before the actual marker loop. -/
theorem zero_seed (vertices count reader todo ports history:List Bool) :
    Runs program 1 (ctl .zeroSeed) (view vertices count reader todo ports [] history) (ctl .zeroLoop)
      (view vertices count reader todo ports [false] history) :=by
  have h:=push_run .zeroSeed (ctl .zeroLoop) .owner false (view vertices count reader todo ports [] history) rfl
  simpa only [view_owner,view] using h
/-- Actual count-marker traversal allocates the zero's width; m is proof-side initial physical width. -/
theorem zero_loop (vertices count reader ports history:List Bool) (n m:Nat) :
    Runs program (2*n+1) (ctl .zeroLoop)
      (view vertices count reader (List.replicate n true) ports (List.replicate m false) history) (ctl .copyCount)
      (view vertices count reader [] ports (List.replicate (n+m) false) history) :=by
  induction n generalizing m with
  | zero=>
    have h:=pop_run .zeroLoop (ctl .copyCount) (ctl .abort) (ctl .zeroPush) .todo
      (view vertices count reader [] ports (List.replicate m false) history) [] rfl rfl
    rw [view_todo] at h
    change Runs program 1 (ctl .zeroLoop) _ (ctl .copyCount)
      (view vertices count reader [] ports (List.replicate m false) history) at h
    simpa only [Nat.mul_zero,Nat.zero_add,List.replicate_zero] using h
  | succ n ih=>
    have h0:=pop_run .zeroLoop (ctl .copyCount) (ctl .abort) (ctl .zeroPush) .todo
      (view vertices count reader (List.replicate (n+1) true) ports (List.replicate m false) history)
      (true::List.replicate n true) rfl rfl
    change Runs program 1 (ctl .zeroLoop) _ (ctl .zeroPush)
      (Function.update (view vertices count reader (List.replicate (n+1) true) ports
        (List.replicate m false) history) .todo (List.replicate n true)) at h0
    rw [view_todo] at h0
    have h1:=push_run .zeroPush (ctl .zeroLoop) .owner false
      (view vertices count reader (List.replicate n true) ports (List.replicate m false) history) rfl
    rw [view_owner] at h1
    change Runs program 1 _ _ _
      (view vertices count reader (List.replicate n true) ports (List.replicate (m+1) false) history) at h1
    have h2:=ih (m+1)
    have h:=join (join h0 h1) h2
    have hc:(1+1)+(2*n+1)=2*(n+1)+1:=by omega
    have hw:n+(m+1)=(n+1)+m:=by omega
    simpa only [hc,hw] using h
/-- Whole original physical source setup: paid record/count copies and physically allocated binary zero. -/
theorem setup_trace (vertices:List Bool) (n:Nat) :
    Runs program (5*vertices.length+12*n+14) (ctl .start)
      (initial vertices (List.replicate n true)).data (ctl .owners)
      (view vertices (List.replicate n true) vertices (List.replicate n true) [] (List.replicate (n+1) false) []) :=by
  have h0:=records_copy vertices (List.replicate n true)
  have h1:=count_copy .zeroCount .zeroSeed vertices (List.replicate n true) vertices [] [] [] rfl
  have h2:=zero_seed vertices (List.replicate n true) vertices (List.replicate n true) [] []
  have h3:=zero_loop vertices (List.replicate n true) vertices [] [] n 1
  have h4:=count_copy .copyCount .owners vertices (List.replicate n true) vertices [] (List.replicate (n+1) false) [] rfl
  have h:=join (join (join (join h0 h1) h2) h3) h4
  have hc:((((5*vertices.length+4)+(5*(List.replicate n true).length+4))+1)+(2*n+1))+
      (5*(List.replicate n true).length+4)=5*vertices.length+12*n+14 :=by
    simp only [List.length_replicate]
    omega
  simpa only [hc,initial] using h
end RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexSetup
