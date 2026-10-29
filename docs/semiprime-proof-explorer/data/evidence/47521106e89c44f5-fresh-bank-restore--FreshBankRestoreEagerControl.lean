import RiemannGaussian.SemiprimeD1StackFreshBankRestore
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
open RiemannGaussian SemiprimeD1StackFreshBankRestore
private instance:BEq Stack:=⟨fun a b=>decide (a=b)⟩
private instance:LawfulBEq Stack where
  eq_of_beq:=by intro a b h;exact of_decide_eq_true h
  rfl:=by intro a;exact decide_eq_true rfl
private def keys:List Stack:=I.roles.map freshStack++
  SemiprimeD1StackRootPhaseFreshRecordsInventory.heapRoles.map heapStack
private theorem keys_complete (k:Stack):k∈keys:=by
  rcases k with k|k
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨k,I.roles_complete k,rfl⟩)
  · apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨k,by cases k <;> simp [SemiprimeD1StackRootPhaseFreshRecordsInventory.heapRoles],rfl⟩
private class HostIndex (K:Type) where
  size:Nat
  index:K→Nat
private abbrev indexList {K:Type} [BEq K] (ks:List K):HostIndex K:=⟨ks.length,fun k=>ks.idxOf k⟩
private instance (n:Nat):HostIndex (Fin n):=⟨n,Fin.val⟩
private instance {K L:Type} [HostIndex K] [HostIndex L]:HostIndex (K⊕L):=
  ⟨HostIndex.size K+HostIndex.size L,fun | .inl k=>HostIndex.index k | .inr l=>HostIndex.size K+HostIndex.index l⟩
private instance:HostIndex SemiprimeD1StackAdder.Stack:=indexList SemiprimeD1StackRootPhaseParametersInventory.subtraction
private instance:HostIndex SemiprimeD1StackPhaseGeometry.Aux:=indexList SemiprimeD1StackRootPhaseParametersInventory.geometry
private instance:HostIndex SemiprimeD1StackPhaseGeometryGuard.Aux:=indexList SemiprimeD1StackRootPhaseParametersInventory.guards
private instance:HostIndex SemiprimeD1StackUnaryDivmod.Stack:=indexList SemiprimeD1StackRootPhaseParametersInventory.division
private instance:HostIndex SemiprimeD1StackPhaseWorkingPrecisionMetadata.Aux:=indexList SemiprimeD1StackRootPhaseParametersInventory.metadata
private instance:HostIndex SemiprimeD1StackPhaseWorkingPrecision.Aux:=indexList SemiprimeD1StackRootPhaseParametersInventory.binary
private instance:HostIndex SemiprimeD1StackJetSuffix.Stack:=indexList SemiprimeD1StackRootPhaseFreshRecordsInventory.suffixRoles
private instance:HostIndex SemiprimeD1StackPhaseChildContext.Aux:=indexList SemiprimeD1StackRootPhaseFreshRecordsInventory.headerAux
private instance:HostIndex SemiprimeD1StackPhaseChildContextFresh.Aux:=indexList SemiprimeD1StackRootPhaseFreshRecordsInventory.freshAux
private instance:HostIndex SemiprimeD1StackHeapRead.Stack:=indexList SemiprimeD1StackRootPhaseFreshRecordsInventory.heapRoles
private theorem index_keys:∀k:Stack,HostIndex.index k=keys.idxOf k:=by decide
private def snapshot (d:Stack→List Bool):Stack→List Bool:=
  let values:=(keys.map d).toArray
  fun k=>(values[HostIndex.index k]?).getD []
private theorem snapshot_eq (d:Stack→List Bool):snapshot d=d:=by
  funext k
  simp only [snapshot,index_keys,List.getElem?_toArray,List.getElem?_map,List.getElem?_idxOf (keys_complete k),Option.map_some,Option.getD_some]
private def drive:Nat→C.State Stack Label→Nat→Nat→Option (C.State Stack Label×Nat×Nat)
  | 0,_,_,_=>none
  | fuel+1,s,fields,heaps=>
    match s.pc with
    | none=>some (s,fields,heaps)
    | some pc=>
      let fields:=match pc with | .inl (.field _)=>fields+1 | _=>fields
      let heaps:=match pc with | .inl .start=>heaps+1 | _=>heaps
      match SemiprimeD1StackCalls.step program s with
      | none=>none
      | some q=>
        let values:=(keys.map q.data).toArray
        let freshData:Stack→List Bool:=fun k=>(values[HostIndex.index k]?).getD []
        drive fuel {q with data:=freshData} fields heaps
private def empty:F.Stack→List Bool:=fun _=>[]
private def pattern:F.Stack→List Bool:=fun k=>
  let i:=I.roles.idxOf k
  [i%2==1,i%3==1,i%5==1]
private def separated:F.Stack→List Bool:=fun k=>
  if k=SemiprimeD1StackPhaseChildContextFresh.contextStack
      (SemiprimeD1StackPhaseChildContext.oldStack SemiprimeD1StackJetContext.precisionBits) then [false,true]
  else if k=SemiprimeD1StackPhaseChildContextFresh.contextStack
      (SemiprimeD1StackPhaseChildContext.childStack SemiprimeD1StackJetContext.precisionBits) then [true,true]
  else if k=F.aux .output then [true,false,true,true,false] else []
private def check (banks:List (F.Stack→List Bool)) (i:Nat):Bool:=
  let rows:=banks.map record
  let heap:=SemiprimeD1StackHeapAllocate.heapBytes rows
  let counter:=List.replicate rows.length true
  let reference:=List.replicate i true
  let expected:=done ((banks[i]?).getD empty) heap counter reference
  match drive 100000 (initial heap counter reference) 0 0 with
  | none=>false
  | some (s,fields,heaps)=>s.pc.isNone && s.flag.isNone && s.returned.isNone && s.frames.isEmpty &&
      fields==85 && heaps==1 && keys.all (fun k=>s.data k==expected.data k)
#eval [check [empty] 0,check [pattern,empty,pattern] 0,check [pattern,empty,pattern] 1,
  check [pattern,empty,pattern] 2,check [separated] 0]
