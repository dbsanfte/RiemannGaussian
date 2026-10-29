/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexPrimitives
/-! # Actual final pair-history reversal and trace-derived byte growth
The real source pays its own emitted history bytes. Their resource bound follows
from the same already executed source prefix, without a supplied output-size
oracle or a transported native acquisition clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexFinish
open SemiprimeD1StackNetworkOwnerIndex SemiprimeD1StackNetworkOwnerIndexPrimitives
open SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- The source physically seeds its only false terminal, reverses every emitted pair, and returns. -/
theorem finish_trace (before:Stack→List Bool) (hist:List Bool)
    (hh:before .history=hist) (ho:before .output=[]) :
    Runs program (2*hist.length+6) (ctl .finish) before (ctl .done)
      (Function.update (Function.update before .history []) .output (hist.reverse++[false])) :=by
  have h0:=push_run .finish (ctl .reverseOutput) .history false before rfl
  rw [hh] at h0
  have hi:(Function.update before .history (false::hist)) (reverseStack .finish 0)=false::hist:=
    Function.update_self _ _ _
  have hd:(Function.update before .history (false::hist)) (reverseStack .finish 1)=[]:=by
    change Function.update before .history (false::hist) .output=[]
    rw [Function.update_of_ne (by decide:Stack.output≠.history),ho]
  have h1:=reverse_call .finish .reverseOutput .done rfl
    (Function.update before .history (false::hist)) (false::hist) [] hi hd
  change Runs program _ _ _ _
    (Function.update (Function.update (Function.update before .history (false::hist)) .history [])
      .output ((false::hist).reverse++[])) at h1
  simp only [Function.update_idem,List.reverse_cons,List.append_nil] at h1
  have h:=join h0 h1
  have hc:1+(2*(false::hist).length+3)=2*hist.length+6:=by simp only [List.length_cons];omega
  simpa only [hc] using h
/-- Actual source initialization has exactly the two physical inputs and no cached answer. -/
theorem initial_length (vertices count:List Bool) (k:Stack) :
    ((initial vertices count).data k).length ≤ vertices.length+count.length :=by
  cases k <;> simp only [initial,input,List.length_nil] <;> omega
/-- Every actually acquired pair-history byte is paid by the same source prefix that produced it. -/
theorem history_length (vertices count:List Bool) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial vertices count)=some out) :
    (out.data .history).length ≤vertices.length+count.length+fuel :=
  SemiprimeD1StackReturnLink.run_data_bound program fuel (vertices.length+count.length)
    (initial vertices count) out (initial_length vertices count) hr .history
end RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexFinish
