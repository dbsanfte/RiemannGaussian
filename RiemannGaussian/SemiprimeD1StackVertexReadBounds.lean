/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexReadExecution
import Mathlib.Tactic.Linarith

/-! # Actual finite-machine vertex-read time and all-prefix state
The argument tapes are explicit physical inputs. Their acquisition/serialization
is not silently included or treated as free random access.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackVertexReadBounds
open SemiprimeD1StackVertexRead SemiprimeD1StackVertexReadExecution
open SemiprimeD1TensorTapeCodec (tape vectorBits)
local notation "ctl" => SemiprimeD1StackVertexRead.control

/-- Genuine target-machine certificate for the actual original vertex read.
Only proved exact path-length selection is noncomputable; runtime code is not. -/
noncomputable def vertexInTime (v : SemiprimeD1LeafCounter.Vertex)
    (assignment portTail tableTail : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        ⟨some (ctl .start),none,none,input v assignment portTail tableTail,[]⟩)
      (some (SemiprimeD1StackCalls.configuration
        ⟨none,none,none,output v assignment portTail tableTail,[]⟩))
      (budget assignment.length (portTape v.ports).length (tape v.table).length) := by
  have hx := vertex_run v assignment portTail tableTail
  let m := Classical.choose hx
  have hm := Classical.choose_spec hx
  apply SemiprimeD1StackCalls.evalsCorrect Stack.tableTape Stack.output (ctl .start) code
  exact ⟨⟨m,hm.2⟩,hm.1⟩

/-- The actual physical unary-port tape is polynomial in original address magnitude. -/
theorem portTape_length (M : ℕ) (ports : List ℕ) (hp : ∀p∈ports,p<M) :
    (portTape ports).length≤2*ports.length*(M+1)+1 := by
  induction ports with
  | nil => simp [portTape,vectorBits]
  | cons p ps ih =>
    have hh := hp p (by simp)
    have ht := ih (fun q hq => hp q (by simp [hq]))
    simp only [portTape,List.map_cons,vectorBits,List.length_cons,
      SemiprimeSourceHistogramKeyBits.frame_length,List.length_replicate] at ht ⊢
    nlinarith

/-- Closed fixed-polynomial monotonicity, without substituting an exponential arity. -/
theorem budget_mono {W W' P P' T T' : ℕ} (hW : W≤W') (hP : P≤P') (hT : T≤T') :
    budget W P T≤budget W' P' T' := by
  unfold budget SemiprimeD1StackGatherBytecode.budget SemiprimeD1StackBitGatherBounds.budget
    SemiprimeD1StackTreeBytecode.budget
  have hg := Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hW) 8)
    (Nat.add_le_add_right hP 1)
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 5 hg)
    (Nat.mul_le_mul_left 8 (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hT) 3))) 3

/-- Actual original scope/degree/literal table inventory bounds the executed read. -/
theorem sized_vertex_run (M : ℕ) (v : SemiprimeD1LeafCounter.Vertex)
    (assignment portTail tableTail : List Bool) (hb : assignment.length=M)
    (hp : ∀p∈v.ports,p<M) :
    ∃m≤budget M (2*v.ports.length*(M+1)+1) (SemiprimeD1TensorTables.storage v.table),
      C.run code m ⟨some (ctl .start),none,none,input v assignment portTail tableTail,[]⟩=
      some ⟨none,none,none,output v assignment portTail tableTail,[]⟩ := by
  obtain ⟨m,hm,hr⟩ := vertex_run v assignment portTail tableTail
  exact ⟨m,hm.trans (budget_mono (by omega) (portTape_length M v.ports hp)
    (SemiprimeD1TensorTapeCodec.tape_le_storage v.table)),hr⟩

/-- Total actual prepared argument payload, including unconsumed suffixes. -/
def argumentSize (v : SemiprimeD1LeafCounter.Vertex) (assignment portTail tableTail : List Bool) : ℕ :=
  (portTape v.ports++portTail).length+assignment.length+(tape v.table++tableTail).length

/-- Every actual source-prefix Boolean cell and finite return-stack symbol is counted. -/
theorem prefix_cells (v : SemiprimeD1LeafCounter.Vertex) (assignment portTail tableTail : List Bool)
    (fuel : ℕ) (out : C.State Stack Label)
    (h : C.run code fuel ⟨some (ctl .start),none,none,input v assignment portTail tableTail,[]⟩=some out) :
    (out.data .ports).length+(out.data .assignment).length+(out.data .reader).length+
      (out.data .scratch).length+(out.data .accumulator).length+(out.data .path).length+
      (out.data .tableTape).length+(out.data .tasks).length+(out.data .output).length+
      out.frames.length≤10*(argumentSize v assignment portTail tableTail+fuel) := by
  have hd := SemiprimeD1StackReturnLink.run_data_bound code fuel
    (argumentSize v assignment portTail tableTail) _ out (by
      intro k
      cases k <;> simp [input,data,argumentSize] <;> omega) h
  have hf := SemiprimeD1StackCalls.run_frame_bound code fuel _ out h
  change out.frames.length≤0+fuel at hf
  have h0 := hd .ports
  have h1 := hd .assignment
  have h2 := hd .reader
  have h3 := hd .scratch
  have h4 := hd .accumulator
  have h5 := hd .path
  have h6 := hd .tableTape
  have h7 := hd .tasks
  have h8 := hd .output
  omega

/-- All actually visited target configurations obey the same complete storage bound. -/
theorem machine_prefix_cells (v : SemiprimeD1LeafCounter.Vertex)
    (assignment portTail tableTail : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (h : (fun c => c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        ⟨some (ctl .start),none,none,input v assignment portTail tableTail,[]⟩))=some cfg) :
    (cfg.stk (some Stack.ports)).length+(cfg.stk (some Stack.assignment)).length+
      (cfg.stk (some Stack.reader)).length+(cfg.stk (some Stack.scratch)).length+
      (cfg.stk (some Stack.accumulator)).length+(cfg.stk (some Stack.path)).length+
      (cfg.stk (some Stack.tableTape)).length+(cfg.stk (some Stack.tasks)).length+
      (cfg.stk (some Stack.output)).length+(cfg.stk none).length≤
      10*(argumentSize v assignment portTail tableTail+fuel) := by
  dsimp only [SemiprimeD1StackVertexRead.machine] at cfg h ⊢
  let start : C.State Stack Label :=
    ⟨some (ctl .start),none,none,input v assignment portTail tableTail,[]⟩
  have he := SemiprimeD1StackCalls.run_correct Stack.tableTape Stack.output (ctl .start) code fuel start
  change (C.run code fuel start).map SemiprimeD1StackCalls.configuration=
    (fun c => c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  have hefinal := he.trans h
  cases hs : C.run code fuel start with
  | none => rw [hs] at hefinal; cases hefinal
  | some out =>
    rw [hs] at hefinal
    have hc : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hefinal
    rw [←hc]
    exact prefix_cells v assignment portTail tableTail fuel out hs

end RiemannGaussian.SemiprimeD1StackVertexReadBounds
