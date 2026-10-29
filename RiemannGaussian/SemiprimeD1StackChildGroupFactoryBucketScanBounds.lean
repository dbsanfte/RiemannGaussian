/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketOperationBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketScan
/-! # Complete actual packet scan and its two real reversal byte clocks
Raw generated counter width is paid by actual visits. The bound is uniform in
prior accumulated output history, which the real preserving loggers retain.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketScanBounds
namespace E
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint payload records)
end E
namespace Scan
export SemiprimeD1StackChildGroupFactoryBucketLoopView (selected portWords portRecords records)
end Scan
namespace Loop
export SemiprimeD1StackChildGroupFactoryBucketLoop (timeBound)
end Loop
namespace Step
export SemiprimeD1StackChildGroupFactoryBucketVisitView (nextPosition)
end Step
namespace Op
export SemiprimeD1StackChildGroupFactoryOperationBounds (endpointBytes)
export SemiprimeD1StackChildGroupFactoryBucketOperationBounds (visit_time)
end Op
namespace Count
export SemiprimeD1StackChildGroupFactoryCounterBounds (successor_length selected_length selected_word_bounds)
end Count
/-- Every selected field tuple actually came from this physically scanned endpoint source. -/
theorem selected_source (es:List E.Endpoint) (packet position:List Bool) (p:E.Endpoint×List Bool)
    (hp:p∈Scan.selected es packet position):p.1∈es:=by
  induction es generalizing position with
  | nil=>simp only [Scan.selected,List.not_mem_nil] at hp
  | cons e es ih=>
    by_cases h:e.packet=packet
    · simp only [Scan.selected,h,ite_true,List.mem_cons] at hp
      rcases hp with rfl|hp
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem e (ih _ hp)
    · exact List.mem_cons_of_mem e (ih position (by simpa only [Scan.selected,h,ite_false] using hp))
private theorem flat_length {T:Type} (xs:List T) (row:T→List Bool) (cap:Nat)
    (hc:∀x∈xs,(row x).length≤cap):(xs.flatMap row).length≤xs.length*cap:=by
  induction xs with
  | nil=>simp only [List.flatMap_nil,List.length_nil,Nat.zero_mul,le_refl]
  | cons x xs ih=>
    have hh:=hc x List.mem_cons_self
    have ht:=ih (fun y h=>hc y (List.mem_cons_of_mem x h))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith
/-- Literal tagged five-field source records have linear raw-byte size. -/
theorem endpoint_records (es:List E.Endpoint) (B:Nat) (hc:∀e∈es,Op.endpointBytes e≤B):
    (E.records es).length≤12*B*es.length+1:=by
  induction es with
  | nil=>simp only [E.records,List.length_cons,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons e es ih=>
    have hh:=hc e List.mem_cons_self
    have ht:=ih (fun p h=>hc p (List.mem_cons_of_mem e h))
    simp only [E.records,E.payload,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
    dsimp only [Op.endpointBytes] at hh
    nlinarith
/-- Emitted real child records charge actual raw endpoints and actual full binary counter words. -/
theorem child_bytes (es:List E.Endpoint) (packet position:List Bool) (B L:Nat)
    (hc:∀e∈es,Op.endpointBytes e≤B) (hp:position.length+2*es.length≤L):
    (Scan.records es packet position).length≤20*(B+L+1)*es.length:=by
  have h:=flat_length (Scan.selected es packet position)
    (fun p=>SemiprimeD1StackChildGroupFactoryBucketEmit.row p.1 p.2) (20*(B+L+1)) (by
      intro p hp'
      have he:=hc p.1 (selected_source es packet position p hp')
      have hl:=(Count.selected_word_bounds es packet position p hp').1
      simp only [SemiprimeD1StackChildGroupFactoryBucketEmit.row,
        SemiprimeD1StackChildGroupFactoryBucketEmit.payload,List.length_cons,List.length_nil,
        SemiprimeSourceHistogramKeyBits.frame_length]
      dsimp only [Op.endpointBytes] at he
      omega)
  have hn:=Count.selected_length es packet position
  dsimp only [Scan.records]
  nlinarith
/-- Actual binary port bank/reversal bytes are paid before any unary conversion occurs. -/
theorem port_bytes (es:List E.Endpoint) (packet position:List Bool) (L:Nat)
    (hp:position.length+2*es.length≤L):
    (Scan.portRecords es packet position).length≤(2*L+2)*es.length:=by
  have h:=flat_length (Scan.portWords es packet position)
    SemiprimeD1StackChildGroupFactoryBucketEmit.portRow (2*L+2) (by
      intro w hw
      obtain ⟨p,hp',rfl⟩:=List.mem_map.mp hw
      have hl:=(Count.selected_word_bounds es packet position p hp').1
      simp only [SemiprimeD1StackChildGroupFactoryBucketEmit.portRow,List.length_cons,
        SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
      omega)
  have hn:=Count.selected_length es packet position
  change (Scan.selected es packet position).length≤es.length at hn
  dsimp only [Scan.portRecords,Scan.portWords] at ⊢
  simp only [Scan.portWords,List.length_map] at h
  nlinarith
/-- The SAME physical next-counter instruction has at most two new raw cells. -/
theorem next_length (e:E.Endpoint) (packet position:List Bool):
    (Step.nextPosition e packet position).length≤position.length+2:=by
  by_cases h:e.packet=packet
  · simp only [Step.nextPosition,h,ite_true];exact Count.successor_length _
  · simp only [Step.nextPosition,h,ite_false];omega
/-- All actual per-endpoint parse/test/emit/increment/cleanup traces are linear in the paid remaining visits. -/
theorem loop_time (es:List E.Endpoint) (packet position:List Bool) (B L:Nat)
    (hc:∀e∈es,Op.endpointBytes e≤B) (hp:position.length+2*es.length≤L):
    Loop.timeBound es packet position≤10000*(B+packet.length+L+1)*(es.length+1):=by
  induction es generalizing position with
  | nil=>simp only [Loop.timeBound,List.length_nil,Nat.zero_add,Nat.mul_one];omega
  | cons e es ih=>
    have hh:=hc e List.mem_cons_self
    have hr:=Op.visit_time e packet position
    have ha:=next_length e packet position
    have ht:=ih (Step.nextPosition e packet position) (fun p h=>hc p (List.mem_cons_of_mem e h))
      (by simp only [List.length_cons] at hp;omega)
    simp only [Loop.timeBound,List.length_cons]
    simp only [List.length_cons] at hp
    nlinarith
/-- Complete paid source copy, all endpoint visits and both genuine seed/reversals. -/
theorem source_time (es:List E.Endpoint) (packet position:List Bool) (B L:Nat)
    (hc:∀e∈es,Op.endpointBytes e≤B) (hp:position.length+2*es.length≤L):
    SemiprimeD1StackChildGroupFactoryBucketScan.timeBound es packet position≤
      1000000*(B+packet.length+L+1)*(es.length+1):=by
  have hs:=endpoint_records es B hc
  have hl:=loop_time es packet position B L hc hp
  have hch:=child_bytes es packet position B L hc hp
  have hport:=port_bytes es packet position L hp
  dsimp only [SemiprimeD1StackChildGroupFactoryBucketScan.timeBound,
    SemiprimeD1StackChildGroupFactoryBucketScan.reverseTime]
  nlinarith
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketScanBounds
