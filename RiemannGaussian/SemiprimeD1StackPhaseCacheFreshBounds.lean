/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseCacheFreshExecution
/-! # Own physical-input/VALUE clock and ALL143 roles, including48unused shadows
Old/new unary rank and precision-width VALUE expansion is explicitly charged.
Only the producer heap/count/reference/header words are runtime inputs.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPhaseCacheFreshBounds
open SemiprimeD1StackPhaseCacheFresh SemiprimeD1StackPhaseCacheFreshComponents
open SemiprimeD1StackPhaseCacheFreshExecution
local notation "ctl" => (Sum.inl : Control→Label)
/-- Actual heap/count/reference bytes, old header, and BOTH context-rank/precision VALUE inventories. -/
def resource (banks:List (P.Stack→List Bool)) (i:Fin banks.length) (a u edges:Nat) (t p:List Bool) (axes:List Nat) :Nat :=
  SemiprimeD1StackPhaseBankRestoreBounds.inputSize banks i+
  (SemiprimeD1StackPhaseChildContextPrimitives.header axes).length+
  SemiprimeD1StackPhaseChildContextFreshBounds.resource a u edges t p axes+1
/-- Own whole time pays the real physical heap consumer and actual cache-ready Fresh pipeline. -/
theorem run_polynomial (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (a u edges:Nat) (t p:List Bool) (axes:List Nat) (hp:∀x∈axes,0<x) :
    runBound banks i a u edges t p axes≤ 1000000000000*(resource banks i a u edges t p axes+1)^2 :=by
  have hR:=SemiprimeD1StackPhaseBankRestoreBounds.runBound_le banks i
  change SemiprimeD1StackPhaseBankRestoreExecution.runBound banks i≤ 1000*SemiprimeD1StackPhaseBankRestoreBounds.inputSize banks i at hR
  have hF:=SemiprimeD1StackPhaseChildContextFreshBounds.phase_ready_polynomial a u edges t p axes hp
  have hi:SemiprimeD1StackPhaseBankRestoreBounds.inputSize banks i≤ resource banks i a u edges t p axes+1:=by unfold resource;omega
  have hv:SemiprimeD1StackPhaseChildContextFreshBounds.resource a u edges t p axes+1≤ resource banks i a u edges t p axes+1:=by unfold resource;omega
  have hsq:(SemiprimeD1StackPhaseChildContextFreshBounds.resource a u edges t p axes+1)^2≤(resource banks i a u edges t p axes+1)^2:=by gcongr
  have hz:resource banks i a u edges t p axes+1≤(resource banks i a u edges t p axes+1)^2:=Nat.le_pow (by decide :0<(2:Nat))
  unfold runBound
  omega
/-- Before restore, every private Fresh field is either the actual old header or EMPTY. -/
theorem fresh_input_bound (axes:List Bool) (k:F.Stack) :
    (freshReadyBank (fun _=>[]) axes k).length≤ axes.length :=by
  rcases k with k|k
  · rcases k with k|k
    · exact Nat.zero_le _
    · rcases k with k|k
      · exact SemiprimeD1StackPhaseChildContextBounds.old_input_bound axes k
      · rcases k with k|k
        · change (H.emptyContext k).length≤ axes.length
          rw [SemiprimeD1StackPhaseChildContextBounds.empty_context]
          exact Nat.zero_le _
        · cases k <;> exact Nat.zero_le _
  · cases k <;> exact Nat.zero_le _
/-- Every allocated shared/private/shadow field is bounded when both actual bank views are bounded. -/
theorem data_bound (heap:Heap.Stack→List Bool) (fresh:F.Stack→List Bool) (B:Nat)
    (hh:∀k,(heap k).length≤ B) (hf:∀k,(fresh k).length≤ B) (k:Stack) :
    (data heap fresh k).length≤ B :=by
  rcases k with k|k
  · rcases k with k|k
    · exact hf _
    · exact hh k
  · rcases k with k|k
    · rcases k with k|k
      · exact Nat.zero_le _
      · exact hf (.inl (.inr k))
    · exact hf (.inr k)
/-- Whole initial bank contains the actual four encoded input words ONLY; every48shadow is EMPTY. -/
theorem initial_bound (heap counter reference axes:List Bool) (k:Stack) :
    ((initial heap counter reference axes).data k).length≤
      SemiprimeD1StackPhaseBankRestoreBounds.resource heap counter reference+axes.length :=by
  apply data_bound _ _ _ _ _ k
  · intro j
    have h:=SemiprimeD1StackPhaseBankRestoreBounds.initial_length heap counter reference (R.heapStack j)
    exact h.trans (by omega)
  · intro j
    exact (fresh_input_bound axes j).trans (by omega)
/-- No successful source prefix can exceed the SAME actual compiled program's proved halt. -/
theorem prefix_fuel (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (a u edges:Nat) (t p:List Bool) (axes:List Nat) (hp:∀x∈axes,0<x)
    (hbank:banks[i.val]=phase a u edges t p) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (source banks i axes)=some out) :
    fuel≤ runBound banks i a u edges t p axes :=by
  obtain ⟨q,hq,hstop⟩:=source_run banks i a u edges t p axes hp hbank
  have ht:fuel≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 (done banks i a u edges t p axes)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact ht.trans hq
/-- Complete all143-role inventory explicitly includes ALL48unused shadow slots and real return cells. -/
theorem prefix_cells (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (a u edges:Nat) (t p:List Bool) (axes:List Nat) (hp:∀x∈axes,0<x)
    (hbank:banks[i.val]=phase a u edges t p) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (source banks i axes)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤ 1000000000000000*(resource banks i a u edges t p axes+1)^2 :=by
  let B:=SemiprimeD1StackPhaseBankRestoreBounds.inputSize banks i+
    (SemiprimeD1StackPhaseChildContextPrimitives.header axes).length
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel B (source banks i axes) out
    (initial_bound (heap banks) (List.replicate banks.length true) (List.replicate i.val true)
      (SemiprimeD1StackPhaseChildContextPrimitives.header axes)) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (source banks i axes) out hr
  change out.frames.length≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤ 143*(B+fuel):=by
    calc
      _≤∑_k:Stack,(B+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:fuel≤ 1000000000000*(resource banks i a u edges t p axes+1)^2:=
    (prefix_fuel banks i a u edges t p axes hp hbank fuel out hr).trans (run_polynomial banks i a u edges t p axes hp)
  have hB:B≤ resource banks i a u edges t p axes+1:=by unfold B resource;omega
  have hz:resource banks i a u edges t p axes+1≤(resource banks i a u edges t p axes+1)^2:=Nat.le_pow (by decide :0<(2:Nat))
  omega
/-- SAME complete all143/shadow48/real-return bound for every actual compiled-machine source prefix. -/
theorem machine_prefix_cells (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (a u edges:Nat) (t p:List Bool) (axes:List Nat) (hp:∀x∈axes,0<x)
    (hbank:banks[i.val]=phase a u edges t p) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (source banks i axes)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤ 1000000000000000*(resource banks i a u edges t p axes+1)^2 :=by
  have he:=SemiprimeD1StackCalls.run_correct originalInput output (ctl .start) program fuel (source banks i axes)
  change (SemiprimeD1StackCalls.run program fuel (source banks i axes)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (source banks i axes))) at he
  have hh:=he.trans hr
  cases hc:SemiprimeD1StackCalls.run program fuel (source banks i axes) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells banks i a u edges t p axes hp hbank fuel out hc
end RiemannGaussian.SemiprimeD1StackPhaseCacheFreshBounds
