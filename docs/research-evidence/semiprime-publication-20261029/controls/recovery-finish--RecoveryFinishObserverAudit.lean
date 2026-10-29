import RiemannGaussian.SemiprimeD1StackRecoveryFinishRetention
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
open RiemannGaussian SemiprimeD1StackRecoveryFinish
private instance:BEq Stack:=⟨fun a b=>decide (a=b)⟩
private instance:LawfulBEq Stack where
  eq_of_beq:=by intro a b h;exact of_decide_eq_true h
  rfl:=by intro a;exact decide_eq_true rfl
private def adder:List Raw.Stack:=[.left,.right,.scratch,.output]
private def auxiliary:List Aux:=[.numerator,.denominator,.sign,.numeratorWork,.denominatorWork,.content,.lost,.todo,
  .inverseInput,.negative,.two,.current,.numeratorResidue,.signedResidue,.product,.opposite,.correction,.copyScratch]
private def multiplier:List SemiprimeD1StackMultiplier.Stack:=adder.map Sum.inl++
  ([0,1,2]:List (Fin 3)).map (Sum.inr ∘ Sum.inl)++[.inr (.inr false),.inr (.inr true)]
private def mul:List M.Stack:=multiplier.map Sum.inl++[.inr false,.inr true]
private def add:List A.Stack:=adder.map Sum.inl++[.inr false,.inr true]
private def keys:List Stack:=mul.map Sum.inl++add.map (Sum.inr ∘ Sum.inl)++auxiliary.map (Sum.inr ∘ Sum.inr)
private theorem keys_complete:∀k:Stack,k∈keys:=by decide
private class HostIndex (K:Type) where
  size:Nat
  index:K→Nat
private abbrev indexList {K:Type} [BEq K] (ks:List K):HostIndex K:=⟨ks.length,fun k=>ks.idxOf k⟩
private instance (n:Nat):HostIndex (Fin n):=⟨n,Fin.val⟩
private instance:HostIndex Bool:=⟨2,fun b=>if b then 1 else 0⟩
private instance:HostIndex Raw.Stack:=indexList adder
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
private def drive:Nat→C.State Stack Label→Nat→Option (C.State Stack Label×Nat)
  | 0,_,_=>none
  | fuel+1,s,steps=>
    match s.pc with
    | none=>some (s,steps)
    | some _=>match SemiprimeD1StackCalls.step program s with
      | none=>none
      | some q=>
        let values:=(keys.map q.data).toArray
        let freshData:Stack→List Bool:=fun k=>(values[HostIndex.index k]?).getD []
        drive fuel {q with data:=freshData} (steps+1)
private def check (negative:Bool) (mag denominator:List Bool) (p:Nat):Bool:=
  let n:SemiprimeBitIndexClipping.SignedWord:=⟨negative,mag⟩
  let tape:=negative::mag
  let markers:=List.replicate p true
  let answer:=(SemiprimeD1RecoveryStripBits.finish p n denominator).bits
  match drive 100000 (initial tape denominator markers) 0 with
  | none=>false
  | some (s,steps)=>s.flag.isNone && s.returned.isNone && s.frames.isEmpty &&
    keys.all (fun k=>s.data k==(if k=output then answer else input tape denominator markers k)) && steps<100000
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
