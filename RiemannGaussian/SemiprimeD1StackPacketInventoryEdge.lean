/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryClass
/-! # Actual positive occurrence-counter update from its retained binary word
The class OLD-j word and every map/row/packet word are preserved. Only actual
copy/counter/drain instructions execute; no occurrence number is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryEdge
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryPrimitives
open SemiprimeD1StackPacketInventoryView SemiprimeD1StackPacketInventoryClass
open SemiprimeD1StackProcedureTrace
namespace Counter
export SemiprimeD1StackSourceEnvironmentEncoding (successor successor_length)
end Counter
local notation "ctl"=>Label.local
/-- One paid real occurrence increment, with the exact OLD class-index cache retained through the entire counter call. -/
theorem edge_run (source stream key dictionary index oldEdge:List Bool) (r:R.Stack→List Bool) (o:O.Stack→List Bool):
    ∃t ≤ 100*(oldEdge.length+1),Runs program t (ctl .copyEdgeOperand)
      (view {(fresh source stream key dictionary oldEdge) with frameScratch:=index} r o) (ctl .clearHigh)
      (view {(fresh source stream key dictionary (Counter.successor oldEdge)) with frameScratch:=index} r o) :=by
  let f:W.Words:={(fresh source stream key dictionary oldEdge) with frameScratch:=index}
  let next:=Counter.successor oldEdge
  have h0:=copy_call .edgeOperand .copyEdgeOperand .incrementEdge rfl (view f r o) oldEdge [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f r o) (frequencyStack (F.lookupStack (.inr .output))) (oldEdge++[])) at h0
  rw [List.append_nil,update_oldCount] at h0
  let f1:W.Words:={f with oldCount:=oldEdge}
  obtain ⟨t1,ht1,h1⟩:=counter_call .incrementEdge .clearEdge rfl (view f1 r o) oldEdge rfl rfl rfl rfl rfl rfl rfl
  change Runs program t1 _ _ _ (Function.update (Function.update (view f1 r o)
    (frequencyStack (F.lookupStack (.inr .output))) []) (frequencyStack (F.aux .count)) next) at h1
  rw [update_oldCount,update_count] at h1
  let f2:W.Words:={f1 with oldCount:=[],count:=next}
  have h2:=drain_loop .clearEdge (ctl .saveEdge) edge rfl (view f2 r o) oldEdge rfl
  change Runs program _ _ _ _ (Function.update (view f2 r o) (frequencyStack (F.aux .maximum)) []) at h2
  rw [update_maximum] at h2
  let f3:W.Words:={f2 with maximum:=[]}
  have h3:=copy_call .edge .saveEdge .clearEdgeCount rfl (view f3 r o) next [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f3 r o) (frequencyStack (F.aux .maximum)) (next++[])) at h3
  rw [List.append_nil,update_maximum] at h3
  let f4:W.Words:={f3 with maximum:=next}
  have h4:=drain_loop .clearEdgeCount (ctl .clearHigh) count rfl (view f4 r o) next rfl
  change Runs program _ _ _ _ (Function.update (view f4 r o) (frequencyStack (F.aux .count)) []) at h4
  rw [update_count] at h4
  have h:=join (join (join (join h0 h1) h2) h3) h4
  have hn:=Counter.successor_length oldEdge
  change next.length ≤ oldEdge.length+1 at hn
  exact ⟨_,by omega,h⟩
end RiemannGaussian.SemiprimeD1StackPacketInventoryEdge
