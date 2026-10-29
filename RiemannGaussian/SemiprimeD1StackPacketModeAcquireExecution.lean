/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketModeAcquireOrder
/-! # One actual packet/order/WIDTH source through the complete feasible enumeration
Packet and tile counts are physically acquired before the real catalogue call.
The entire35-role stopped callee and both original caller words are retained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketModeAcquireExecution
open SemiprimeD1StackPacketModeAcquire SemiprimeD1StackPacketModeAcquireEncoding
open SemiprimeD1StackPacketModeAcquireCount SemiprimeD1StackPacketModeAcquireOrder
open SemiprimeD1StackPacketModeAcquirePrimitives SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace B
export SemiprimeD1StackWeightedModeCatalogueBounds (runBound source_run_bounded)
end B
local notation "ctl"=>Label.local
/-- Honest physically acquired catalogue-entry bank, with all other work cleared. -/
def ready (packets:List (List Bool)) (i precision:Nat):Stack→List Bool:=
  bank {modes:=M.input (List.replicate packets.length true) (List.replicate (2^(i+1)) true) (List.replicate precision true),packets:=vectorBits packets,order:=List.replicate i true}
/-- Real complete catalogue/feasible-DFS call, receiving only the actual acquired source words. -/
theorem enumerate_call (packets:List (List Bool)) (i precision:Nat):
    ∃q ≤ B.runBound packets.length (2^(i+1)) precision+1,
      Runs program q (ctl .enumerate) (ready packets i precision) (ctl .done) (result packets i precision):=by
  obtain ⟨q,hq,hr⟩:=B.source_run_bounded packets.length (2^(i+1)) precision
  refine ⟨q+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program modeStack Label.modes
    Sum.inl_injective M.program (.inl .start) (fun _=>rfl) (ctl .enumerate) (ctl .done) rfl q
    (M.initial (List.replicate packets.length true) (List.replicate (2^(i+1)) true)
      (List.replicate precision true)) (modeDone packets i precision)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · cases k <;> rfl
/-- Both actual source copies, all field counts, all tile doublings and the whole real catalogue call are paid. -/
def timeBound (packets:List (List Bool)) (i precision:Nat):Nat:=
  5*(vectorBits packets).length+4+countTime packets+orderTime i+
    B.runBound packets.length (2^(i+1)) precision+2
/-- Actual complete source prefix through the genuine final-halt label. -/
theorem source_trace (packets:List (List Bool)) (i precision:Nat):
    ∃q,q+1 ≤ timeBound packets i precision ∧
      Runs program q (ctl .start) (source packets i precision).data
        (ctl .done) (result packets i precision):=by
  have h0:=source_count_run packets (List.replicate i true) (List.replicate precision true)
  have h1:=source_order_run (vectorBits packets) (List.replicate precision true) packets.length i
  obtain ⟨q,hq,h2⟩:=enumerate_call packets i precision
  refine ⟨_,?_,join (join h0 h1) h2⟩
  unfold timeBound
  omega
/-- SAME finite44-role program actually halts after counting and enumerating from the three physical source inputs. -/
theorem source_run (packets:List (List Bool)) (i precision:Nat):
    ∃q ≤ timeBound packets i precision,
      SemiprimeD1StackCalls.run program q (source packets i precision)=some (done packets i precision):=by
  obtain ⟨q,hq,hr⟩:=source_trace packets i precision
  obtain ⟨out,he,ha⟩:=hr [] (source packets i precision) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result packets i precision) [] out ha
  refine ⟨q+1,hq,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,he,Option.bind_some]
  exact hh
/-- Exact original feasible-mode tuple vector, with native order and the actual tile count2^(i+1). -/
theorem output_original (packets:List (List Bool)) (i precision:Nat):
    (done packets i precision).data output=vectorBits
      ((SemiprimeD1WeightedTuples.tuples
        (SemiprimeD1ModeCatalog.weights (packets.length*2^(i+1)) (precision-1)) (precision-1)).map
          SemiprimeD1StackWeightedModeView.vector):=by
  exact SemiprimeD1StackWeightedModeCatalogueExecution.output_original packets.length (2^(i+1)) precision
/-- Every actual callee role, including acquired counts/product/labels/DFS work, is retained exactly. -/
theorem modes_retained (packets:List (List Bool)) (i precision:Nat) (k:M.Stack):
    (done packets i precision).data (modeStack k)=(modeDone packets i precision).data k:=rfl
/-- Both original caller words survive the whole source. -/
theorem inputs_retained (packets:List (List Bool)) (i precision:Nat):
    (done packets i precision).data (aux .packets)=vectorBits packets ∧
      (done packets i precision).data (aux .order)=List.replicate i true:=⟨rfl,rfl⟩
end RiemannGaussian.SemiprimeD1StackPacketModeAcquireExecution
