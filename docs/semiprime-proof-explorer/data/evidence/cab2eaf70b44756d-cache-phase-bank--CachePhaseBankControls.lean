import RiemannGaussian
import RiemannGaussian.SemiprimeD1StackCachePhaseBankExecution
import RiemannGaussian.SemiprimeD1StackCachePhaseBankAbort
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace CachePhaseBankControls
open RiemannGaussian SemiprimeD1StackCachePhaseBank
open SemiprimeD1StackJetFoldWords (Modes modeTape)
open SemiprimeD1TensorTapeCodec (vectorBits)
instance:BEq Stack:=⟨fun a b=>decide (a=b)⟩
instance:LawfulBEq Stack where
  eq_of_beq:=by intro a b h;exact of_decide_eq_true h
  rfl:=by intro a;exact decide_eq_true rfl
class HostIndex (K:Type) where
  size:Nat
  keys:List K
  index:K→Nat
abbrev indexList {K:Type} [BEq K] (ks:List K):HostIndex K:=⟨ks.length,ks,fun k=>ks.idxOf k⟩
instance (n:Nat):HostIndex (Fin n):=⟨n,List.finRange n,Fin.val⟩
instance:HostIndex Bool:=indexList [false,true]
instance:HostIndex Unit:=indexList [()]
instance {K L:Type} [HostIndex K] [HostIndex L]:HostIndex (K⊕L):=
  ⟨HostIndex.size K+HostIndex.size L,(HostIndex.keys (K:=K)).map Sum.inl++(HostIndex.keys (K:=L)).map Sum.inr,
    fun | .inl k=>HostIndex.index k | .inr l=>HostIndex.size K+HostIndex.index l⟩
instance:HostIndex SemiprimeD1StackAdder.Stack:=indexList SemiprimeD1StackRootPhaseParametersInventory.subtraction
instance:HostIndex SemiprimeD1StackPhaseGeometry.Aux:=indexList SemiprimeD1StackRootPhaseParametersInventory.geometry
instance:HostIndex SemiprimeD1StackPhaseGeometryGuard.Aux:=indexList SemiprimeD1StackRootPhaseParametersInventory.guards
instance:HostIndex SemiprimeD1StackUnaryDivmod.Stack:=indexList SemiprimeD1StackRootPhaseParametersInventory.division
instance:HostIndex SemiprimeD1StackPhaseWorkingPrecisionMetadata.Aux:=indexList SemiprimeD1StackRootPhaseParametersInventory.metadata
instance:HostIndex SemiprimeD1StackPhaseWorkingPrecision.Aux:=indexList SemiprimeD1StackRootPhaseParametersInventory.binary
instance:HostIndex SemiprimeD1StackJetSuffix.Stack:=indexList SemiprimeD1StackRootPhaseFreshRecordsInventory.suffixRoles
instance:HostIndex SemiprimeD1StackPhaseChildContext.Aux:=indexList SemiprimeD1StackRootPhaseFreshRecordsInventory.headerAux
instance:HostIndex SemiprimeD1StackPhaseChildContextFresh.Aux:=indexList SemiprimeD1StackRootPhaseFreshRecordsInventory.freshAux
instance:HostIndex SemiprimeD1StackHeapRead.Stack:=indexList SemiprimeD1StackRootPhaseFreshRecordsInventory.heapRoles
instance:HostIndex SemiprimeD1StackJetRoute.Stack:=indexList [.axes,.reverseAxes,.axis,.radix,.product,.records,.scratch,.valid,.left,.right,.result,.q,.d,.copied,.divScratch,.quotLeft,.remLeft,.quotRight,.remRight]
instance:HostIndex SemiprimeD1StackJetPoint.Aux:=indexList [.a,.b,.axes,.rank,.i,.j,.target,.acc,.reader,.index,.parser,.skipped,.valid,.readCopy,.eqRight,.eqValid,.eqScratch,.addWork,.copyWork]
instance:HostIndex SemiprimeD1StackJetAdd.Aux:=indexList [.leftTape,.rightTape,.rank,.active,.reverseOut,.output,.valid,.parser,.copy]
instance:HostIndex SemiprimeD1StackJetFold.Aux:=indexList [.children,.modes,.group,.frames,.fieldScratch,.valid,.copyScratch,.frameScratch,.precision,.tailSum,.sum]
instance:HostIndex SemiprimeD1StackJetBlocks.Aux:=indexList [.coefficients,.blocks,.todo,.reader,.rankTodo,.word,.fieldScratch,.valid,.copyScratch,.frameBuffer,.frameScratch,.rowHistory,.row,.logScratch,.history,.output]
instance:HostIndex Aux:=indexList [.references,.children,.referenceReader,.childReader,.valid,.history,.buffer,.output]
def keys:List Stack:=HostIndex.keys (K:=Stack)
theorem keys_complete:∀k:Stack,k∈keys:=by decide
theorem index_keys:∀k:Stack,HostIndex.index k=keys.idxOf k:=by decide
def snapshot (d:Stack→List Bool):Stack→List Bool:=
  let values:=(keys.map d).toArray
  fun k=>(values[HostIndex.index k]?).getD []
theorem snapshot_eq (d:Stack→List Bool):snapshot d=d:=by
  funext k
  simp only [snapshot,index_keys,List.getElem?_toArray,List.getElem?_map,List.getElem?_idxOf (keys_complete k),Option.map_some,Option.getD_some]
def drive:Nat→C.State Stack Label→Nat→Nat→Nat→Option (C.State Stack Label×Nat×Nat×Nat)
  | 0,_,_,_,_=>none
  | fuel+1,s,steps,calls,clears=>
    match s.pc with
    | none=>some (s,steps,calls,clears)
    | some pc=>
      let calls:=match pc with | .local .phase=>calls+1 | _=>calls
      let clears:=match pc with | .local (.clear _ _) =>clears+1 | _=>clears
      match SemiprimeD1StackCalls.step program s with
      | none=>none
      | some out=>
        let values:=(keys.map out.data).toArray
        let freshData:Stack→List Bool:=fun k=>(values[HostIndex.index k]?).getD []
        drive fuel {out with data:=freshData} (steps+1) calls clears
def bank (axes:List Nat) (p:List Bool) (q:Nat) (newP:List Bool) (valid:Bool):SemiprimeD1StackCachePhase.Fresh.Stack→List Bool:=
  let header:=Function.update (SemiprimeD1StackPhaseChildContext.store (fun _=>[])
    (SemiprimeD1StackJetContextCorrectness.finalData axes p)
    (SemiprimeD1StackJetContextCorrectness.finalData (q::axes) newP) [valid] []) SemiprimeD1StackCachePhase.Header.blocks (List.replicate q true)
  Sum.elim header (fun k=>if k=SemiprimeD1StackPhaseChildContextFresh.Aux.output then [true,false,true] else [])
def outer:List Label:=[.local .start,.local .header]
def outerEq:List Label→Bool
  | [.local .start,.local .header]=>true
  | _=>false
def nativePayload (p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes):List Bool:=
  vectorBits ((List.range q).map (fun j=>vectorBits
    (SemiprimeD1JetBlockBits.extract (⟨[],SemiprimeBitArithmetic.bitValue p⟩:SemiprimeD1JetAxes.Context) j
      (SemiprimeD1StackCachePhaseExecution.coefficients [] q newP modes)).words))
def check (label:String) (banks:List (SemiprimeD1StackCachePhase.Fresh.Stack→List Bool))
    (refs childWords expected:List Bool) (ok:Bool) (expectedCalls:Nat):IO Nat:=do
  let hp:=SemiprimeD1StackHeapAllocate.heapBytes (banks.map SemiprimeD1StackFreshBankRestore.record)
  let cn:=List.replicate banks.length true
  let before:C.State Stack Label:=⟨some (.local .start),some true,some (.local .header),input hp cn refs childWords,outer⟩
  let some (out,steps,calls,clears):=drive 500000 before 0 0 0
    | throw (IO.userError s!"phase-bank failed to halt: {label}")
  let wanted:=Function.update (Function.update (input hp cn refs childWords) output expected) status [ok]
  unless out.flag.isNone && out.returned.isNone && outerEq out.frames && calls==expectedCalls &&
      clears>=238*calls && keys.all (fun k=>out.data k==wanted k) do
    throw (IO.userError s!"phase-bank all246/calls/cleanup/returns/status mismatch: {label}; steps={steps}; calls={calls}")
  IO.println s!"CACHE_PHASE_BANK case={label} steps={steps} calls={calls} all246=true status={ok}"
  return steps
def run:IO Unit:=do
  let p:List Bool:=[false,true]
  let newP:List Bool:=[true]
  let inactive:=bank [] p 2 newP false
  let active:=bank [] p 2 newP true
  let pzero:=bank [] [] 1 [] true
  let modes:Modes:=[[[[true,false,false],[false,true]]]]
  let mut total:=0
  total:=total+(←check "empty" [] (vectorBits []) (vectorBits []) [false] true 0)
  total:=total+(←check "rejected" [inactive] (vectorBits [[]]) (vectorBits [modeTape []]) (vectorBits [[false]]) true 1)
  total:=total+(←check "precision0" [pzero] (vectorBits [[]]) (vectorBits [modeTape []]) (vectorBits [nativePayload [] 1 [] []]) true 1)
  total:=total+(←check "mixed" [inactive,active] (vectorBits [[],[true]])
    (vectorBits [modeTape [],modeTape modes]) (vectorBits [[false],nativePayload p 2 newP modes]) true 2)
  total:=total+(←check "repeat" [active] (vectorBits [[],[]])
    (vectorBits [modeTape modes,modeTape []]) (vectorBits [nativePayload p 2 newP modes,nativePayload p 2 newP []]) true 2)
  total:=total+(←check "missing-child" [inactive] (vectorBits [[]]) (vectorBits []) [] false 0)
  total:=total+(←check "trailing-ref" [] [false,true] (vectorBits []) [] false 0)
  total:=total+(←check "missing-child-eof" [inactive] (vectorBits [[]])
    (true::SemiprimeSourceHistogramKeyBits.frame (modeTape []) []) [] false 1)
  IO.println s!"CACHE_PHASE_BANK cases=8 actual_transitions={total} all246=true retained_four_inputs=true chronological_repeats=true rejected_rows=true actual_restore_guard=true real236_cleanup=true flags_returns=true eof_validation=true"
#eval run
end CachePhaseBankControls
open Lean Elab Command
run_cmd do
  let env←getEnv
  let mut checked:Nat:=0
  for (name,_) in env.constants.toList do
    unless (`CachePhaseBankControls).isPrefixOf name do continue
    for ax in (←Lean.collectAxioms name) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "unexpected observer axiom {name}: {ax}"
    checked:=checked+1
  logInfo m!"CACHE_PHASE_BANK_OBSERVER_STD3 {checked}"
