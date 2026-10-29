/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryRead
/-! # Actual class bump preserving its physically acquired OLD index
Only actual sentinel/copy/lookup/counter/Frame/drain procedures execute. The
OLD count is copied before increment and remains separate from NEW Frame scratch.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryClass
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryPrimitives
open SemiprimeD1StackPacketInventoryView SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace D
export SemiprimeD1StackSourceKeyFrequencyEncoding (Rows dictionary read coded encoded)
end D
namespace Counter
export SemiprimeD1StackSourceEnvironmentEncoding (successor)
end Counter
local notation "ctl"=>Label.local
/-- Actual clean frequency/counter bank with its retained source, real stream, raw key, class map and positive edge word. -/
def fresh (source stream raw dictionary edge:List Bool):W.Words:=
  {source:=source,reader:=stream,raw:=raw,dictionary:=dictionary,maximum:=edge}
/-- Own sum of actual sentinel/read/copy/counter/two-frame/tag/drain bounds for one class update. -/
def classBound (rows:D.Rows) (key:List Bool):Nat:=
  (5*key.length+7)+SemiprimeD1StackPacketInventoryRead.readBound (D.encoded key) (D.coded rows)+
    (5*(D.read rows key).length+4)+(40*((D.read rows key).length+1)+2)+
    (6*(Counter.successor (D.read rows key)).length+5)+(6*(D.encoded key).length+5)+1+
    ((D.encoded key).length+1)+((Counter.successor (D.read rows key)).length+1)
/-- Complete real class update: actual OLD index retained through both NEW Frame calls and all query/count cleanup. -/
theorem bump_run (source stream key edge:List Bool) (rows:D.Rows) (r:R.Stack→List Bool) (o:O.Stack→List Bool):
    ∃t ≤ classBound rows key,Runs program t (ctl .encodeClass)
      (view (fresh source stream key (D.dictionary rows) edge) r o) (ctl .readRows)
      (view {(fresh source stream key (D.dictionary ((key,Counter.successor (D.read rows key))::rows)) edge)
        with frameScratch:=D.read rows key} r o) :=by
  let base:=fresh source stream key (D.dictionary rows) edge
  let old:=D.read rows key
  let next:=Counter.successor old
  let encoded:=D.encoded key
  let dict:=D.dictionary rows
  have h0:=sentinel_call .class .encodeClass (.copyMap .classes) rfl (view base r o) key rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view base r o) (frequencyStack (F.lookupStack (.inr .query))) encoded) at h0
  rw [update_query] at h0
  have hready:∀k,view {base with query:=encoded} r o (lookupStack k)=
      (SemiprimeD1StackOwnerLookup.initial encoded []).data k:=by
    intro k;rcases k with k|k <;> cases k <;> rfl
  obtain ⟨t1,ht1,h1⟩:=SemiprimeD1StackPacketInventoryRead.read_run .classes {base with query:=encoded} r o
    encoded (D.coded rows) hready rfl
  change Runs program t1 _ _ _ (view {base with query:=encoded,lookupReader:=[],oldCount:=old} r o) at h1
  let f1:W.Words:={base with query:=encoded,lookupReader:=[],oldCount:=old}
  have h2:=copy_call .oldIndex .copyOldIndex .incrementClass rfl (view f1 r o) old [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f1 r o) (frequencyStack (F.aux .frameScratch)) (old++[])) at h2
  rw [List.append_nil,update_frameScratch] at h2
  let f2:W.Words:={f1 with frameScratch:=old}
  obtain ⟨t3,ht3,h3⟩:=counter_call .incrementClass (.frameValue .classes) rfl (view f2 r o) old rfl rfl rfl rfl rfl rfl rfl
  change Runs program t3 _ _ _ (Function.update (Function.update (view f2 r o)
    (frequencyStack (F.lookupStack (.inr .output))) []) (frequencyStack (F.aux .count)) next) at h3
  rw [update_oldCount,update_count] at h3
  let f3:W.Words:={f2 with oldCount:=[],count:=next}
  have h4:=frame_call (.value .classes) (.frameValue .classes) (.frameKey .classes) rfl (view f3 r o) next dict rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f3 r o) (frequencyStack (F.aux .dictionary)) (frame next dict)) at h4
  rw [update_dictionary] at h4
  let f4:W.Words:={f3 with dictionary:=frame next dict}
  have h5:=frame_call (.key .classes) (.frameKey .classes) (.tagMap .classes) rfl (view f4 r o) encoded (frame next dict) rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f4 r o) (frequencyStack (F.aux .dictionary))
    (frame encoded (frame next dict))) at h5
  rw [update_dictionary] at h5
  let f5:W.Words:={f4 with dictionary:=frame encoded (frame next dict)}
  have h6:=push_run (.tagMap .classes) (ctl .clearClassQuery) classes true (view f5 r o) rfl
  change Runs program 1 _ _ _ (Function.update (view f5 r o) (frequencyStack (F.aux .dictionary))
    (true::frame encoded (frame next dict))) at h6
  rw [update_dictionary] at h6
  let f6:W.Words:={f5 with dictionary:=true::frame encoded (frame next dict)}
  have h7:=drain_loop .clearClassQuery (ctl .clearClassCount) query rfl (view f6 r o) encoded rfl
  change Runs program _ _ _ _ (Function.update (view f6 r o) (frequencyStack (F.lookupStack (.inr .query))) []) at h7
  rw [update_query] at h7
  let f7:W.Words:={f6 with query:=[]}
  have h8:=drain_loop .clearClassCount (ctl .readRows) count rfl (view f7 r o) next rfl
  change Runs program _ _ _ _ (Function.update (view f7 r o) (frequencyStack (F.aux .count)) []) at h8
  rw [update_count] at h8
  have h:=join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8
  refine ⟨_,?_,h⟩
  unfold classBound
  dsimp only [old,next,encoded] at ht1 ht3 ⊢
  omega
end RiemannGaussian.SemiprimeD1StackPacketInventoryClass
