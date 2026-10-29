/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkRowsPrimitives
/-! # Sole final outer-row reversal and actual-prefix byte-growth certificate -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkRowsFinish
open SemiprimeD1StackNetworkRows SemiprimeD1StackNetworkRowsPrimitives SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Actual final false seed and real outer-history reverse retain all index/counters/metadata words. -/
theorem finish_trace (before:Stack→List Bool) (history:List Bool)
    (hh:before (aux .history)=history) (ho:before (aux .output)=[]) :
    Runs program (2*history.length+4) (ctl .finish) before (ctl .done)
      (Function.update (Function.update before (aux .history) []) (aux .output) (history.reverse++[false])) :=by
  have h0:=push_run .finish (ctl .outputReverse) (aux .output) false before rfl
  rw [ho] at h0
  have h1:=reverse_call .output .outputReverse .done rfl (Function.update before (aux .output) [false]) history [false]
    (by change Function.update before (aux .output) [false] (aux .history)=history
        rw [Function.update_of_ne (by decide :aux .history≠aux .output),hh]) rfl
  have he:Function.update (Function.update (Function.update before (aux .output) [false]) (aux .history) []) (aux .output)
      (history.reverse++[false])=
      Function.update (Function.update before (aux .history) []) (aux .output) (history.reverse++[false]):=by
    funext k
    rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · cases k <;> simp only [Function.update,aux] <;> rfl
  change Runs program (2*history.length+3) (ctl .outputReverse) _ (ctl .done)
    (Function.update (Function.update (Function.update before (aux .output) [false]) (aux .history) []) (aux .output) (history.reverse++[false])) at h1
  rw [he] at h1
  have h:=join h0 h1
  have hc:1+(2*history.length+3)=2*history.length+4:=by omega
  rw [hc] at h
  exact h
/-- Whole48-role initialization contains exactly the two physical input words, no output/index/routing advice. -/
theorem initial_length (vertices count:List Bool) (k:Stack) :
    ((initial vertices count).data k).length≤ vertices.length+count.length :=by
  rcases k with k|k
  · cases k <;> simp only [initial,input,SemiprimeD1StackNetworkOwnerIndex.input,Sum.elim_inl,List.length_nil] <;> omega
  · exact Nat.zero_le _
/-- Final output-history cost is derived from the SAMEACTUALsource prefix which physically produced it. -/
theorem history_length (vertices count:List Bool) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial vertices count)=some out) :
    (out.data (aux .history)).length≤ vertices.length+count.length+fuel :=
  SemiprimeD1StackReturnLink.run_data_bound program fuel (vertices.length+count.length) _ out (initial_length vertices count) hr (aux .history)
end RiemannGaussian.SemiprimeD1StackNetworkRowsFinish
