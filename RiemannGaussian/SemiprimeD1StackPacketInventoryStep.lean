/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryStepEncoding
import RiemannGaussian.SemiprimeD1StackPacketInventoryDiscovery
import RiemannGaussian.SemiprimeD1StackPacketInventorySlots
import RiemannGaussian.SemiprimeD1StackPacketInventoryEdge
import RiemannGaussian.SemiprimeD1StackPacketInventoryLog
import RiemannGaussian.SemiprimeD1StackPacketInventoryCleanup
import RiemannGaussian.SemiprimeD1StackPacketInventoryStream
/-! # Whole actual sparse-inventory occurrence replay step
Every source, lookup, counter, map write, row logger and cleanup is an actual
call or literal instruction of the SAME fixed fifty-nine-role program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryStep
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryPrimitives
open SemiprimeD1StackPacketInventoryView SemiprimeD1StackPacketInventoryBanks
open SemiprimeD1StackPacketInventoryEncoding SemiprimeD1StackPacketInventoryClass
open SemiprimeD1StackPacketInventoryStepEncoding SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
namespace Reader
export SemiprimeD1StackPacketRowsMeaning (fields)
end Reader
local notation "ctl"=>Label.local
/-- Exact sum of the actual component caps for one physically parsed real occurrence. -/
def rowBound (a:Nat) (s:Summary) (owner factor:List Bool):Nat:=
  1+(8*(key owner factor).length+8)+classBound s.classes (key owner factor)+
    SemiprimeD1StackPacketInventoryRows.rowsBound a owner factor (index s owner factor)+100*(s.edge.length+1)+
    200*((oriented a s owner factor).key.length+(oriented a s owner factor).slots.length+
      (oriented a s owner factor).high.length+(nextEdge s).length+1)+
    SemiprimeD1StackPacketInventoryDiscovery.seenBound s.seen (oriented a s owner factor).key+
    1000*((key owner factor).length+(index s owner factor).length+(oriented a s owner factor).key.length+
      (oriented a s owner factor).slots.length+(nextEdge s).length+1)+
    ((vectorBits (Reader.fields 64 a owner)).length+(vectorBits (Reader.fields 64 a factor)).length+17)+
    ((oriented a s owner factor).key.length+(oriented a s owner factor).slots.length+16)
/-- Complete one-occurrence actual kernel trace, exact old cache update and chronological placement, preserving all source words. -/
theorem row_run (a:Nat) (s:Summary) (owner factor source tail:List Bool)
    (ho:owner∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (hf:factor∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (hm:SemiprimeD1StackPacketInventorySeen.Markers s.seen):
    ∃t ≤ rowBound a s owner factor,Runs program t (ctl .header)
      (boundary source (alphabet a) (true::frame (key owner factor) tail) s) (ctl .header)
      (boundary source (alphabet a) tail (step a s (key owner factor))) :=by
  let rawKey:=key owner factor
  let old:=index s owner factor
  let countNext:=Counter.successor old
  let edgeNext:=nextEdge s
  let cl:=Dict.dictionary ((rawKey,countNext)::s.classes)
  let seenOld:=Dict.dictionary s.seen
  let slotOld:=Dict.dictionary s.slots
  let pp:=oriented a s owner factor
  let slotNew:=Dict.dictionary ((frame pp.key pp.slots,edgeNext)::s.slots)
  let seenNew:=Dict.dictionary ((pp.key,[true])::s.seen)
  let ps:=SemiprimeD1StackPacketInventoryDiscovery.nextPackets s.seen pp.key s.packets
  let cat:=alphabet a
  let oldHist:=(history s.placements).reverse
  let vl:=vectorBits (Reader.fields 64 a owner)
  let vr:=vectorBits (Reader.fields 64 a factor)
  let rr:=reader (vectorBits s.packets) oldHist [] [] []
  let oo:=orientation cat seenOld slotOld [] [] [] []
  let f0:=fresh source (true::frame rawKey tail) [] (Dict.dictionary s.classes) s.edge
  have h0:=pop_run .header (ctl .abort) (ctl .eof) (ctl .parse) stream (view f0 rr oo)
    (true::frame rawKey tail) rfl rfl
  change Runs program 1 _ _ _ (Function.update (view f0 rr oo) (frequencyStack (F.aux .reader)) (frame rawKey tail)) at h0
  rw [update_reader] at h0
  have h1:=SemiprimeD1StackPacketInventoryStream.parse_run
    (fresh source (frame rawKey tail) [] (Dict.dictionary s.classes) s.edge) rr oo rawKey tail rfl rfl rfl rfl
  obtain ⟨t2,ht2,h2⟩:=bump_run source tail rawKey s.edge s.classes rr oo
  let fc:W.Words:={(fresh source tail rawKey cl s.edge) with frameScratch:=old}
  obtain ⟨t3,ht3,h3⟩:=SemiprimeD1StackPacketInventoryRows.rows_run a owner factor ho hf fc
    (vectorBits s.packets) oldHist seenOld slotOld rfl
  let rr1:=reader (vectorBits s.packets) oldHist vl vr []
  let oo1:=orientation cat seenOld slotOld pp.key pp.slots pp.high []
  obtain ⟨t4,ht4,h4⟩:=SemiprimeD1StackPacketInventoryEdge.edge_run source tail rawKey cl old s.edge rr1 oo1
  let fe:W.Words:={(fresh source tail rawKey cl edgeNext) with frameScratch:=old}
  obtain ⟨t5,ht5,h5⟩:=SemiprimeD1StackPacketInventorySlots.slots_run source tail rawKey cl old edgeNext cat seenOld
    pp.key pp.slots pp.high s.slots rr1
  obtain ⟨t6,ht6,h6⟩:=SemiprimeD1StackPacketInventoryDiscovery.seen_run source tail rawKey cl old edgeNext cat slotNew
    pp.key pp.slots s.seen s.packets oldHist vl vr hm
  obtain ⟨t7,ht7,h7⟩:=SemiprimeD1StackPacketInventoryLog.log_run source tail rawKey cl old edgeNext cat seenNew slotNew
    pp.key pp.slots (vectorBits ps) oldHist vl vr
  let newHist:=(true::frame (SemiprimeD1StackPacketInventoryLog.rowWord rawKey old pp.key pp.slots edgeNext) []).reverse++oldHist
  let ff:=fresh source tail [] cl edgeNext
  have h8:=SemiprimeD1StackPacketInventoryCleanup.reader_run ff (orientation cat seenNew slotNew pp.key pp.slots [] [])
    (vectorBits ps) newHist vl vr
  have h9:=SemiprimeD1StackPacketInventoryCleanup.orientation_run ff (reader (vectorBits ps) newHist [] [] [])
    cat seenNew slotNew pp.key pp.slots
  have h:=join (join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8) h9
  have he:boundary source cat tail (step a s rawKey)=
      view ff (reader (vectorBits ps) newHist [] [] []) (orientation cat seenNew slotNew [] [] [] []):=by
    rw [step_eq a s owner factor ho hf]
    unfold boundary
    dsimp only
    rw [history_append,List.reverse_append]
    rfl
  rw [←he] at h
  refine ⟨_,?_,h⟩
  unfold rowBound
  dsimp only [rawKey,old,countNext,edgeNext,cl,seenOld,slotOld,pp,slotNew,seenNew,ps,cat,oldHist,vl,vr,fc]
    at ht2 ht3 ht4 ht5 ht6 ht7 ⊢
  omega
end RiemannGaussian.SemiprimeD1StackPacketInventoryStep
