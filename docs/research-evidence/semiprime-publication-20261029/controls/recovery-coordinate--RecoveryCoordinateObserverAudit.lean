import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateExecution
import RiemannGaussian.SemiprimeD1JetBlockBits
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
open RiemannGaussian SemiprimeD1StackRecoveryCoordinate
open SemiprimeD1StackRecoveryCoordinateEncoding
private instance:BEq Stack:=⟨fun a b=>decide (a=b)⟩
private instance:LawfulBEq Stack where
  eq_of_beq:=by intro a b h;exact of_decide_eq_true h
  rfl:=by intro a;exact decide_eq_true rfl
private def adder:List SemiprimeD1StackAdder.Stack:=[.left,.right,.scratch,.output]
private def indexedAux:List I.Aux:=[.cache,.query,.counter,.reader,.parser,.value,.valid,.copy]
private def auxiliary:List Aux:=[.phases,.reader,.blocks,.valid,.rowHistory,.rowOutput,.history,.buffer,.output]
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
      let fields:=match pc with | .local .phaseField|.local .blockField=>fields+1 | _=>fields
      let lookups:=match pc with | .local .lookup=>lookups+1 | _=>lookups
      let frames:=match pc with | .local .coefficientFrame|.local .phaseFrame=>frames+1 | _=>frames
      let reverses:=match pc with | .local .coefficientReverse|.local .rowReverse|.local .phaseReverse|.local .finish=>reverses+1 | _=>reverses
      match SemiprimeD1StackCalls.step program s with
      | none=>none
      | some q=>
        let values:=(keys.map q.data).toArray
        let freshData:Stack→List Bool:=fun k=>(values[HostIndex.index k]?).getD []
        drive fuel {q with data:=freshData} (steps+1) fields lookups frames reverses
private def expected (phases:Phases) (key:List Bool):List Bool:=
  SemiprimeD1TensorTapeCodec.vectorBits (phases.map (fun blocks=>
    SemiprimeD1TensorTapeCodec.vectorBits (blocks.map (fun words=>
      (SemiprimeD1JetBlockBits.readCopy words (SemiprimeBitArithmetic.bitValue key)).bits))))
private def check (phases:Phases) (key:List Bool):Bool:=
  let original:=tape phases
  let answer:=expected phases key
  let blocks:=(phases.map List.length).sum
  match drive 1000000 (initial original key) 0 0 0 0 0 with
  | none=>false
  | some (s,steps,fields,lookups,frames,reverses)=>s.flag.isNone && s.returned.isNone && s.frames.isEmpty &&
    keys.all (fun k=>s.data k==(if k=output then answer else input original key k)) &&
    fields==phases.length+blocks && lookups==blocks && frames==phases.length+blocks &&
    reverses==blocks+2*phases.length+1 && steps==SemiprimeD1StackRecoveryCoordinateExecution.timeBound phases key
private def huge:List Bool:=List.replicate 79 false++[true]
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, ci) in env.constants.toList do
    if (env.getModuleIdxFor? name).isSome then continue
    if ci.isAxiom then throwError "unexpected observer axiom {name}"
    for ax in (← Lean.collectAxioms name) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "unexpected observer axiom in {name}: {ax}"
    checked := checked+1
  unless checked > 0 do throwError "observer declarations missing"
  logInfo m!"OBSERVER standard_axioms_only=true declarations={checked}"
