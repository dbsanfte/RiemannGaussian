/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexRows
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexFinish
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexPorts
/-! # Complete actual left-owner loop with physical factor-suffix retention
Each vertex consumes one actual todo marker, physically parses/drains both full
record fields, emits all occurrence pairs, and physically increments/transfers
its binary owner counter. The native sum below sums ONLY actual primitive caps.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexLoop
open SemiprimeD1StackNetworkOwnerIndex SemiprimeD1StackNetworkOwnerIndexPrimitives
open SemiprimeD1StackNetworkOwnerIndexSetup SemiprimeD1StackNetworkOwnerIndexOperations
open SemiprimeD1StackNetworkOwnerIndexEncoding SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
/-- Exact original vertex-record bytes before its unconsumed following records. -/
def vertexBytes (v:SemiprimeD1LeafCounter.Vertex) :List Bool :=
  true::frame (SemiprimeD1StackVertexReadExecution.portTape v.ports)
    (frame (SemiprimeD1TensorTapeCodec.tape v.table) [])
/-- Complete remaining left-record prefix, with no false vector terminator inserted before factors. -/
def vertexPrefix (vertices:List SemiprimeD1LeafCounter.Vertex) :List Bool :=
  vertices.foldr (fun v tail=>vertexBytes v++tail) []
/-- Both actual record fields preserve the literal following factor/vertex bytes. -/
theorem vertexBytes_append (v:SemiprimeD1LeafCounter.Vertex) (tail:List Bool) :
    vertexBytes v++tail=true::frame (SemiprimeD1StackVertexReadExecution.portTape v.ports)
      (frame (SemiprimeD1TensorTapeCodec.tape v.table) tail) :=by
  unfold vertexBytes
  rw [List.cons_append,SemiprimeD1TensorTapeCodec.frame_append,SemiprimeD1TensorTapeCodec.frame_append,List.nil_append]
/-- Actual two-field byte inventory, including every literal constructor and delimiter. -/
theorem vertexBytes_length (v:SemiprimeD1LeafCounter.Vertex) :
    (vertexBytes v).length=2*(SemiprimeD1StackVertexReadExecution.portTape v.ports).length+
      2*(SemiprimeD1TensorTapeCodec.tape v.table).length+3 :=by
  simp only [vertexBytes,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
  omega
/-- Literal actual source-record split retains the complete factor-record suffix, including its terminator. -/
theorem records_split (left right:List SemiprimeD1LeafCounter.Vertex) :
    SemiprimeD1StackVertexProduct.records (left++right)=vertexPrefix left++SemiprimeD1StackVertexProduct.records right :=by
  induction left with
  | nil=>rfl
  | cons v left ih=>
    change true::frame (SemiprimeD1StackVertexReadExecution.portTape v.ports)
      (frame (SemiprimeD1TensorTapeCodec.tape v.table) (SemiprimeD1StackVertexProduct.records (left++right)))=
      (vertexBytes v++vertexPrefix left)++SemiprimeD1StackVertexProduct.records right
    rw [List.append_assoc,vertexBytes_append,ih]
/-- Conservative actual row cap: todo pop +paid fields/table drain +paid port loop +real binary increment/transfer. -/
def rowBudget (n:Nat) (v:SemiprimeD1LeafCounter.Vertex) :Nat :=
  100*(n+2)*(SemiprimeD1StackVertexReadExecution.portTape v.ports).length+
  8*(SemiprimeD1StackVertexReadExecution.portTape v.ports).length+
  9*(SemiprimeD1TensorTapeCodec.tape v.table).length+14*(n+1)+42
/-- Actual binary increment changes only the owner's physical word at a clean boundary. -/
theorem increment_view (vertices count reader todo ports hist:List Bool) (n start:Nat) (hs:start<n) :
    ∃q≤ 14*(n+1)+23,Runs program q (ctl .increment)
      (view vertices count reader todo ports (ownerWord n start) hist) (ctl .owners)
      (view vertices count reader todo ports (ownerWord n (start+1)) hist) :=by
  obtain ⟨q,hq,hr⟩:=increment_transfer (view vertices count reader todo ports (ownerWord n start) hist)
    n start hs rfl rfl rfl
  rw [view_owner] at hr
  exact ⟨q,hq,hr⟩
/-- One actual left vertex executes all record/port/table/counter work and retains its raw following suffix. -/
theorem owner_step (vertices count suffix todo hist:List Bool) (n start:Nat) (v:SemiprimeD1LeafCounter.Vertex)
    (hs:start<n) :
    ∃q≤ rowBudget n v,Runs program q (ctl .owners)
      (view vertices count (vertexBytes v++suffix) (true::todo) [] (ownerWord n start) hist) (ctl .owners)
      (view vertices count suffix todo [] (ownerWord n (start+1))
        ((payload (portPairs n start v.ports)).reverse++hist)) :=by
  have h0:=pop_run .owners (ctl .finish) (ctl .abort) (ctl .vertexTag) .todo
    (view vertices count (vertexBytes v++suffix) (true::todo) [] (ownerWord n start) hist) (true::todo) rfl rfl
  change Runs program 1 (ctl .owners) _ (ctl .vertexTag)
    (Function.update (view vertices count (vertexBytes v++suffix) (true::todo) [] (ownerWord n start) hist) .todo todo) at h0
  rw [view_todo] at h0
  have h1:=SemiprimeD1StackNetworkOwnerIndexRows.vertex_fields vertices count todo (ownerWord n start) hist
    (SemiprimeD1StackVertexReadExecution.portTape v.ports) (SemiprimeD1TensorTapeCodec.tape v.table) suffix
  rw [←vertexBytes_append] at h1
  have h2:=SemiprimeD1StackNetworkOwnerIndexPorts.ports_run vertices count suffix todo (ownerWord n start) hist
    (v.ports.map SemiprimeD1StackUnaryDivmod.unary)
  rw [SemiprimeD1StackNetworkOwnerIndexPorts.rows_unary] at h2
  obtain ⟨b,hb,h3⟩:=increment_view vertices count suffix todo []
    ((payload (portPairs n start v.ports)).reverse++hist) n start hs
  have hh:=join (join (join h0 h1) h2) h3
  have hp:=SemiprimeD1StackNetworkOwnerIndexPorts.portClock_le (ownerWord n start)
    (v.ports.map SemiprimeD1StackUnaryDivmod.unary)
  rw [ownerWord_length n start (by omega)] at hp
  change SemiprimeD1StackNetworkOwnerIndexPorts.portClock (ownerWord n start) (v.ports.map SemiprimeD1StackUnaryDivmod.unary)≤
    100*((n+1)+1)*(SemiprimeD1StackVertexReadExecution.portTape v.ports).length at hp
  refine ⟨1+(8*(SemiprimeD1StackVertexReadExecution.portTape v.ports).length+
    9*(SemiprimeD1TensorTapeCodec.tape v.table).length+18)+
    SemiprimeD1StackNetworkOwnerIndexPorts.portClock (ownerWord n start) (v.ports.map SemiprimeD1StackUnaryDivmod.unary)+b,?_,hh⟩
  have hsimpl:(n+1)+1=n+2:=by omega
  rw [hsimpl] at hp
  unfold rowBudget
  omega
/-- One real emptytodo pop ends ONLYthe owner prefix, leaving every following factor byte untouched. -/
theorem owners_end (vertices count suffix owner hist:List Bool) :
    Runs program 1 (ctl .owners) (view vertices count suffix [] [] owner hist) (ctl .finish)
      (view vertices count suffix [] [] owner hist) :=by
  have h:=pop_run .owners (ctl .finish) (ctl .abort) (ctl .vertexTag) .todo
    (view vertices count suffix [] [] owner hist) [] rfl rfl
  rw [view_todo] at h
  exact h
/-- Whole actual left-owner loop; native cost is ONLYthe sum of ACTUALrow primitive caps plus emptytodo. -/
theorem owners_loop (vertices count suffix hist:List Bool) (n start:Nat)
    (left:List SemiprimeD1LeafCounter.Vertex) (hn:start+left.length≤ n) :
    ∃q≤(left.map (rowBudget n)).sum+1,Runs program q (ctl .owners)
      (view vertices count (vertexPrefix left++suffix) (List.replicate left.length true) [] (ownerWord n start) hist)
      (ctl .finish)
      (view vertices count suffix [] [] (ownerWord n (start+left.length))
        ((payload (ownerPairs n start left)).reverse++hist)) :=by
  induction left generalizing start hist with
  | nil=>
    refine ⟨1,by simp,?_⟩
    exact owners_end vertices count suffix (ownerWord n start) hist
  | cons v left ih=>
    have hs:start<n:=by simp only [List.length_cons] at hn;omega
    obtain ⟨b,hb,h0⟩:=owner_step vertices count (vertexPrefix left++suffix) (List.replicate left.length true) hist n start v hs
    obtain ⟨c,hc,h1⟩:=ih ((payload (portPairs n start v.ports)).reverse++hist) (start+1) (by
      simp only [List.length_cons] at hn
      omega)
    have hh:=join h0 h1
    refine ⟨b+c,?_,?_⟩
    · simp only [List.map_cons,List.sum_cons]
      omega
    · have he:start+1+left.length=start+(left.length+1):=by omega
      simpa only [vertexPrefix,List.foldr_cons,List.append_assoc,List.length_cons,List.replicate_succ,
        ownerPairs,payload_append,List.reverse_append,he] using hh
/-- Actual row caps are paid by the actual physical vertex bytes and acquired counter width. -/
theorem rowBudget_le (n:Nat) (v:SemiprimeD1LeafCounter.Vertex) :
    rowBudget n v≤ 1000*(n+2)*(vertexBytes v).length :=by
  rw [vertexBytes_length]
  unfold rowBudget
  nlinarith [Nat.zero_le (n*(SemiprimeD1StackVertexReadExecution.portTape v.ports).length),
    Nat.zero_le (n*(SemiprimeD1TensorTapeCodec.tape v.table).length)]
/-- Sum of ACTUALrow primitive caps is linear in actual prefix bytes at fixed acquired counter width. -/
theorem sumBudget_le (n:Nat) (left:List SemiprimeD1LeafCounter.Vertex) :
    (left.map (rowBudget n)).sum≤ 1000*(n+2)*(vertexPrefix left).length :=by
  induction left with
  | nil=>simp only [List.map_nil,List.sum_nil,vertexPrefix,List.foldr_nil,List.length_nil,Nat.mul_zero,Nat.le_refl]
  | cons v left ih=>
    have hv:=rowBudget_le n v
    change rowBudget n v+(left.map (rowBudget n)).sum≤ 1000*(n+2)*(vertexBytes v++vertexPrefix left).length
    rw [List.length_append,Nat.mul_add]
    exact Nat.add_le_add hv ih
end RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexLoop
