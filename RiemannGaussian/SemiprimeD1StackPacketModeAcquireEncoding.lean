/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketModeAcquire
/-! # Complete44-word proof view and exact actual packet/order source family
These functions describe physical banks only. No view, count, packet getter or
natural evaluator occurs in the fixed finite program's input/control.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketModeAcquireEncoding
open SemiprimeD1StackPacketModeAcquire
/-- Exact proof-side physical bank, retaining every one of35 actual mode-source words. -/
structure Words where
  /-- Complete physical mode-source subbank, not an evaluator operand. -/
  modes:M.Stack→List Bool:=fun _=>[]
  /-- Actual packets Boolean word. -/
  packets:List Bool:=[]
  /-- Actual order Boolean word. -/
  order:List Bool:=[]
  /-- Actual reader Boolean word. -/
  reader:List Bool:=[]
  /-- Actual payload Boolean word. -/
  payload:List Bool:=[]
  /-- Actual fieldScratch Boolean word. -/
  fieldScratch:List Bool:=[]
  /-- Actual valid Boolean word. -/
  valid:List Bool:=[]
  /-- Actual copyScratch Boolean word. -/
  copyScratch:List Bool:=[]
  /-- Actual todo Boolean word. -/
  todo:List Bool:=[]
  /-- Actual tileScan Boolean word. -/
  tileScan:List Bool:=[]
/-- Every actual44-role word is present in this view. -/
def bank (w:Words) :Stack→List Bool:=data w.modes (fun k=>match k with
  | .packets=>w.packets
  | .order=>w.order
  | .reader=>w.reader
  | .payload=>w.payload
  | .fieldScratch=>w.fieldScratch
  | .valid=>w.valid
  | .copyScratch=>w.copyScratch
  | .todo=>w.todo
  | .tileScan=>w.tileScan)
/-- A mode-source word update preserves all actual caller words. -/
theorem update_mode (w:Words) (k:M.Stack) (xs:List Bool) :
    Function.update (bank w) (modeStack k) xs=bank {w with modes:=Function.update w.modes k xs} :=by
  funext p
  rcases p with p|p
  · simp only [bank,data,modeStack,Function.update_apply,Sum.elim_inl,Sum.inl.injEq]
  · rfl
/-- A literal packets write retains every other actual source/cache/work word. -/
theorem update_packets (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .packets) xs=bank {w with packets:=xs} :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A literal order write retains every other actual source/cache/work word. -/
theorem update_order (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .order) xs=bank {w with order:=xs} :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A literal reader write retains every other actual source/cache/work word. -/
theorem update_reader (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .reader) xs=bank {w with reader:=xs} :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A literal payload write retains every other actual source/cache/work word. -/
theorem update_payload (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .payload) xs=bank {w with payload:=xs} :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A literal fieldScratch write retains every other actual source/cache/work word. -/
theorem update_fieldScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .fieldScratch) xs=bank {w with fieldScratch:=xs} :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A literal valid write retains every other actual source/cache/work word. -/
theorem update_valid (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .valid) xs=bank {w with valid:=xs} :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A literal copyScratch write retains every other actual source/cache/work word. -/
theorem update_copyScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .copyScratch) xs=bank {w with copyScratch:=xs} :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A literal todo write retains every other actual source/cache/work word. -/
theorem update_todo (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .todo) xs=bank {w with todo:=xs} :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A literal tileScan write retains every other actual source/cache/work word. -/
theorem update_tileScan (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .tileScan) xs=bank {w with tileScan:=xs} :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Static actual packet-input role inside the complete mode source. -/
def packetRole:M.Stack:=M.multiply (.inl .a)
/-- Static actual tile-input role inside the complete mode source. -/
def tileRole:M.Stack:=M.multiply (.inl .b)
/-- Writing the actual counted packet word produces the honest mode-source packet operand. -/
theorem input_packet (p t w xs:List Bool) :
    Function.update (M.input p t w) packetRole xs=M.input xs t w :=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
/-- Writing the actual doubled tile word produces the honest mode-source tile operand. -/
theorem input_tile (p t w xs:List Bool) :
    Function.update (M.input p t w) tileRole xs=M.input p xs w :=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
/-- Actual packet input update, derived for abstract input words before concrete tape instantiation. -/
theorem update_packet_count (work:Words) (p t w xs:List Bool) :
    Function.update (bank {work with modes:=M.input p t w}) packetCount xs=
      bank {work with modes:=M.input xs t w} :=by
  rw [show packetCount=modeStack packetRole from rfl,update_mode,input_packet]
/-- Actual tile input update, with every other44-role word retained. -/
theorem update_tile_count (work:Words) (p t w xs:List Bool) :
    Function.update (bank {work with modes:=M.input p t w}) tileCount xs=
      bank {work with modes:=M.input p xs w} :=by
  rw [show tileCount=modeStack tileRole from rfl,update_mode,input_tile]
/-- Exactly the actual three source inputs are initialized. -/
theorem initial_bank (packets order precision:List Bool) :
    (initial packets order precision).data=bank {modes:=M.input [] [] precision,packets:=packets,order:=order} :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Actual original input family; the logical packet list is only a proof interpretation of real vector bytes. -/
def source (packets:List (List Bool)) (i precision:Nat):C.State Stack Label:=
  initial (SemiprimeD1TensorTapeCodec.vectorBits packets) (List.replicate i true) (List.replicate precision true)
/-- Actual complete stopped mode-source state from the acquired packet/tile counts. -/
def modeDone (packets:List (List Bool)) (i precision:Nat):C.State M.Stack M.Label:=
  SemiprimeD1StackWeightedModeCatalogueExecution.done packets.length (2^(i+1)) precision
/-- All44 actual words at the final halt, retaining both original caller inputs and complete mode metadata/output. -/
def result (packets:List (List Bool)) (i precision:Nat):Stack→List Bool:=
  bank { modes := (modeDone packets i precision).data
         packets := SemiprimeD1TensorTapeCodec.vectorBits packets
         order := List.replicate i true }
/-- Full true halt after all genuine nested returns. -/
def done (packets:List (List Bool)) (i precision:Nat):C.State Stack Label:=⟨none,none,none,result packets i precision,[]⟩
/-- Honest materialized-input/resource envelope explicitly pays the computed tile count by VALUE. -/
def inputSize (packets:List (List Bool)) (i precision:Nat):Nat:=
  (SemiprimeD1TensorTapeCodec.vectorBits packets).length+i+2^(i+1)+precision+1
end RiemannGaussian.SemiprimeD1StackPacketModeAcquireEncoding
