import RiemannGaussian.SemiprimeD1StackRecoveryEntriesExecution
import RiemannGaussian.SemiprimeD1RecoveryChildBits
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
open RiemannGaussian SemiprimeD1StackRecoveryEntries
open SemiprimeD1StackRecoveryEntriesEncoding
open SemiprimeD1StackRecoveryDenominatorEncoding (Row tape)
private instance:BEq Stack:=⟨fun a b=>decide (a=b)⟩
private instance:LawfulBEq Stack where
  eq_of_beq:=by intro a b h;exact of_decide_eq_true h
  rfl:=by intro a;exact decide_eq_true rfl
private def adder:List SemiprimeD1StackAdder.Stack:=[.left,.right,.scratch,.output]
private def indexedAux:List I.Aux:=[.cache,.query,.counter,.reader,.parser,.value,.valid,.copy]
private def auxiliary:List Aux:=[.rows,.reader,.node,.index,.sign,.magnitude,.denominator,.selectedRow,.child,
  .valid,.history,.frameBuffer,.output]
private def indexedKeys:List I.Stack:=adder.map Sum.inl++indexedAux.map Sum.inr
private def keys:List Stack:=indexedKeys.map indexed++auxiliary.map aux
private theorem keys_complete:∀k:Stack,k∈keys:=by decide
private class HostIndex (K:Type) where
  size:Nat
  index:K→Nat
private abbrev indexList {K:Type} [BEq K] (ks:List K):HostIndex K:=⟨ks.length,fun k=>ks.idxOf k⟩
private instance:HostIndex SemiprimeD1StackAdder.Stack:=indexList adder
private instance:HostIndex I.Aux:=indexList indexedAux
private instance:HostIndex Aux:=indexList auxiliary
private instance {K L:Type} [HostIndex K] [HostIndex L]:HostIndex (K⊕L):=
  ⟨HostIndex.size K+HostIndex.size L,fun | .inl k=>HostIndex.index k | .inr l=>HostIndex.size K+HostIndex.index l⟩
private theorem index_keys:∀k:Stack,HostIndex.index k=keys.idxOf k:=by decide
private def snapshot (d:Stack→List Bool):Stack→List Bool:=
  let values:=(keys.map d).toArray
  fun k=>(values[HostIndex.index k]?).getD []
private theorem snapshot_eq (d:Stack→List Bool):snapshot d=d:=by
  funext k
  simp only [snapshot,index_keys,List.getElem?_toArray,List.getElem?_map,List.getElem?_idxOf (keys_complete k),Option.map_some,Option.getD_some]
private def drive:Nat→C.State Stack Label→Nat→Nat→Nat→Nat→Nat→Option (C.State Stack Label×Nat×Nat×Nat×Nat×Nat)
  | 0,_,_,_,_,_,_=>none
  | fuel+1,s,steps,fields,lookups,frames,reverses=>
    match s.pc with
    | none=>some (s,steps,fields,lookups,frames,reverses)
    | some pc=>
      let fields:=match pc with | .local (.field _)=>fields+1 | _=>fields
      let lookups:=match pc with | .local .outer|.local .inner=>lookups+1 | _=>lookups
      let frames:=match pc with | .local (.frame _)=>frames+1 | _=>frames
      let reverses:=match pc with | .local .rowReverse|.local .finish=>reverses+1 | _=>reverses
      match SemiprimeD1StackCalls.step program s with
      | none=>none
      | some q=>
        let values:=(keys.map q.data).toArray
        let freshData:Stack→List Bool:=fun k=>(values[HostIndex.index k]?).getD []
        drive fuel {q with data:=freshData} (steps+1) fields lookups frames reverses
private def row (node coordinate:List Bool) (negative:Bool) (mag d:List Bool):Row:=![node,coordinate,[negative],mag,d]
private def expectedEntry (cs:List (List (List Bool))) (r:Row):Entry:=
  ![r 2,r 3,r 4,(SemiprimeD1RecoveryChildBits.read cs (r 0) (r 1)).bits]
private def check (rs:List Row) (cs:List (List (List Bool))):Bool:=
  let original:=tape rs
  let bank:=childTape cs
  let answer:=records (rs.map (expectedEntry cs))
  match drive 1000000 (initial original bank) 0 0 0 0 0 with
  | none=>false
  | some (s,steps,fields,lookups,frames,reverses)=>s.flag.isNone && s.returned.isNone && s.frames.isEmpty &&
    keys.all (fun k=>s.data k==(if k=output then answer else input original bank k)) &&
    fields==5*rs.length && lookups==2*rs.length && frames==4*rs.length && reverses==rs.length+1 &&
    steps==SemiprimeD1StackRecoveryEntriesExecution.timeBound rs cs
private def huge:List Bool:=List.replicate 79 false++[true]
#eval [check [] [],
  check [row [] [] false [] [true]] [[[]]],
  check [row [false,false] [true,false,false] true [true,false] [false,true]] [[[true],[false,true,false]]],
  check [row huge [] false [false] [true,false]] [[[true]],[]],
  check [row [] huge true [true,true] [true]] [[[true],[false,false]]],
  check [row [true,false] [] true [] [true],row [] [true] false [true,false] [false,true],
    row [true,false] [] true [] [true]] [[[true],[false,true,false]],[[false,false,false]]]]
