/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexRecordSpliceMeaning
/-! # Complete physical storage for singleton-record EOF cancellation
Runtime is independent of accumulated history length; space honestly includes
that existing history, the new row and every actual saved return cell.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackVertexRecordSpliceStorage
open SemiprimeD1StackVertexRecordSplice SemiprimeD1StackVertexRecordSpliceExecution
/-- No successful actual source prefix exceeds the exact new-row-only halt clock. -/
theorem prefix_fuel (row history : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial (row++[false]) history)=some out) : fuel≤timeBound row := by
  have hs:=source_run row history
  by_contra hn
  have he : fuel=timeBound row+(1+(fuel-(timeBound row+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,hs,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
  have hh : SemiprimeD1StackCalls.run program 1 (done (row.reverse++history))=none := rfl
  rw [hh,Option.bind_none] at hr
  cases hr
/-- Both actual initialized input words are physically counted, including the old history. -/
theorem initial_length (row history : List Bool) (k : Stack) :
    ((initial (row++[false]) history).data k).length≤row.length+history.length+1 := by
  fin_cases k
  · change (row++[false]).length≤_
    simp only [List.length_append,List.length_singleton]
    omega
  · change history.length≤_
    omega
/-- Every actual source prefix counts both data words AND every real return cell, with a fixed linear cap. -/
theorem prefix_cells (row history : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial (row++[false]) history)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤30*(row.length+history.length+1) := by
  have hf:=prefix_fuel row history fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (row.length+history.length+1)
    _ out (initial_length row history) hr
  have hm : (∑k : Stack,(out.data k).length)≤2*(row.length+history.length+1+fuel) := by
    calc
      _≤∑_k : Stack,(row.length+history.length+1+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel (initial (row++[false]) history) out hr
  change out.frames.length≤0+fuel at hframes
  unfold timeBound at hf
  omega
/-- Actual fixed FinTM2 execution has the SAME two-word-plus-return storage cap at every prefix. -/
theorem machine_prefix_cells (row history : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial (row++[false]) history)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤30*(row.length+history.length+1) := by
  have heq:=SemiprimeD1StackCalls.run_correct 0 1 (.local .start) program fuel (initial (row++[false]) history)
  have hh:=heq.trans hr
  cases hout : SemiprimeD1StackCalls.run program fuel (initial (row++[false]) history) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg : cfg=SemiprimeD1StackCalls.configuration out:=(Option.some.inj hh).symm
    subst cfg
    exact prefix_cells row history fuel out hout
end RiemannGaussian.SemiprimeD1StackVertexRecordSpliceStorage
