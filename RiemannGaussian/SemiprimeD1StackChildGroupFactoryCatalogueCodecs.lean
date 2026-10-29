/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointLoopView
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketsLoopView
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsLoop
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortParse
/-! # Byte identities joining actual forward, bucket and original-order scans
Every decoded record below is a proof interpretation of emitted actual fields.
There is no additional physical input, permutation or classification premise.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryCatalogueCodecs
namespace End
export SemiprimeD1StackChildGroupFactoryEndpointLoop (Row)
export SemiprimeD1StackChildGroupFactoryEndpointLoopView (oldRecords selectedRecords chosen)
end End
namespace Old
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point payload records)
export SemiprimeD1StackChildGroupFactoryEndpointOldLog (oldPoint row)
end Old
namespace Emit
export SemiprimeD1StackChildGroupFactoryEndpointEmit (endpoint row)
end Emit
namespace E
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint payload records)
end E
namespace B
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket payload records)
end B
namespace Child
export SemiprimeD1StackChildGroupFactoryLeftPortsInner (records)
export SemiprimeD1StackChildGroupFactoryBucketEmit (payload row)
end Child
namespace Scan
export SemiprimeD1StackChildGroupFactoryBucketLoopView (selected records portWords finalPosition)
end Scan
namespace Bank
export SemiprimeD1StackChildGroupFactoryBucketsLoopView (records)
end Bank
open SemiprimeSourceHistogramKeyBits (frame)
/-- Framing retains the literal tail, without interpreting any raw packet bits. -/
theorem frame_tail (word xs ys:List Bool):frame word (xs++ys)=frame word xs++ys:=by
  induction word with
  | nil=>rfl
  | cons b bs ih=>simp only [frame,ih,List.cons_append]
/-- The two real old-endpoint rows are owner before factor at every occurrence. -/
def oldPoints (rows:List End.Row):List Old.Point:=rows.flatMap fun r=>
  [⟨r.fields.owner,r.fields.edge,[true]⟩,⟨r.fields.factor,r.fields.edge,[false]⟩]
/-- Proof interpretation of each actual selected side's five emitted raw fields. -/
def side (owner:Bool) (r:End.Row):E.Endpoint:=
  ⟨if owner then r.fields.owner else r.fields.factor,r.fields.packet,r.fields.slot,r.fields.edge,[owner]⟩
/-- Exact owner-before-factor selected endpoint fields in physical source order. -/
def selected :List End.Row→List E.Endpoint
  | []=>[]
  | r::rows=>(if r.ownerFlag then [side true r] else [])++
      (if r.factorFlag then [side false r] else [])++selected rows
/-- Joining the old endpoint parser adds no newly supplied table or order. -/
theorem oldPoints_records (rows:List End.Row):Old.records (oldPoints rows)=End.oldRecords rows++[false]:=by
  induction rows with
  | nil=>rfl
  | cons r rs ih=>
    simp only [oldPoints,List.flatMap_cons,List.cons_append,List.nil_append,Old.records,End.oldRecords]
    change true::frame (Old.oldPoint true r.fields.owner r.fields.edge)
      (true::frame (Old.oldPoint false r.fields.factor r.fields.edge) (Old.records (oldPoints rs)))=_
    rw [ih]
    simp only [Old.row,List.cons_append,←frame_tail,List.nil_append]
/-- Exact selected endpoint record joining, including both/one/neither sides. -/
theorem selected_records (rows:List End.Row):E.records (selected rows)=End.selectedRecords rows++[false]:=by
  induction rows with
  | nil=>rfl
  | cons r rs ih=>
    cases ho:r.ownerFlag <;> cases hf:r.factorFlag
    all_goals simp only [selected,ho,hf,Bool.false_eq_true,ite_false,ite_true,
      List.nil_append,List.cons_append,List.append_nil,E.records,End.selectedRecords,End.chosen,ih,
      side,E.payload,Emit.row,Emit.endpoint,←frame_tail]
/-- Every actual six-field child record retains its raw endpoint and generated ID word. -/
theorem child_records (children:List (E.Endpoint×List Bool)):
    Child.records children=children.flatMap (fun c=>Child.row c.1 c.2)++[false]:=by
  induction children with
  | nil=>rfl
  | cons c cs ih=>
    simp only [Child.records,List.flatMap_cons,Child.row,ih,List.cons_append,←frame_tail,List.nil_append]
/-- Typed view of real buckets emitted in actual observed-packet order. -/
def buckets : List (List Bool)→List E.Endpoint→List Bool→List B.Bucket
  | [],_,_=>[]
  | packet::packets,es,position=>
      ⟨packet,Scan.selected es packet position,SemiprimeD1StackPortOrdinalStream.result (Scan.portWords es packet position)⟩::
        buckets packets es (Scan.finalPosition es packet position)
/-- Exact byte bridge from emitted chronological buckets to the real subsequent parser. -/
theorem buckets_records (packets:List (List Bool)) (es:List E.Endpoint) (position:List Bool):
    B.records (buckets packets es position)=Bank.records packets es position++[false]:=by
  induction packets generalizing position with
  | nil=>rfl
  | cons packet packets ih=>
    simp only [buckets,B.records,B.payload,child_records,ih,Bank.records,
      SemiprimeD1StackChildGroupFactoryBucketOneView.bucketRow,Scan.records,
      SemiprimeD1StackChildGroupFactoryBucketRecord.row,List.cons_append,←frame_tail,List.nil_append]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryCatalogueCodecs
