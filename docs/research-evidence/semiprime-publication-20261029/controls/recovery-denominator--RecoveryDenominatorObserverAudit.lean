import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorExecution
import RiemannGaussian.SemiprimeD1RecoveryIntegerBits
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
open RiemannGaussian SemiprimeD1StackRecoveryDenominator
open SemiprimeD1StackRecoveryDenominatorEncoding
private instance:BEq Stack:=⟨fun a b=>decide (a=b)⟩
private instance:LawfulBEq Stack where
  eq_of_beq:=by intro a b h;exact of_decide_eq_true h
  rfl:=by intro a;exact decide_eq_true rfl
private def adder:List SemiprimeD1StackAdder.Stack:=[.left,.right,.scratch,.output]
private def auxiliary:List Aux:=[.rows,.reader,.discard,.valid,.output]
private def multiplier:List M.Stack:=adder.map Sum.inl++
  ([0,1,2]:List (Fin 3)).map (Sum.inr ∘ Sum.inl)++[.inr (.inr false),.inr (.inr true)]
private def keys:List Stack:=multiplier.map main++([0,1,2,3,4]:List (Fin 5)).map fitWork++auxiliary.map aux
private theorem keys_complete:∀k:Stack,k∈keys:=by decide
private class HostIndex (K:Type) where
  size:Nat
  index:K→Nat
private abbrev indexList {K:Type} [BEq K] (ks:List K):HostIndex K:=⟨ks.length,fun k=>ks.idxOf k⟩
private instance (n:Nat):HostIndex (Fin n):=⟨n,Fin.val⟩
private instance:HostIndex Bool:=⟨2,fun b=>if b then 1 else 0⟩
private instance:HostIndex SemiprimeD1StackAdder.Stack:=indexList adder
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
private def drive:Nat→C.State Stack Label→Nat→Nat→Nat→Nat→Option (C.State Stack Label×Nat×Nat×Nat×Nat)
  | 0,_,_,_,_,_=>none
  | fuel+1,s,steps,fields,products,fits=>
    match s.pc with
    | none=>some (s,steps,fields,products,fits)
    | some pc=>
      let fields:=match pc with | .local (.field _)=>fields+1 | _=>fields
      let products:=match pc with | .local .multiply=>products+1 | _=>products
      let fits:=match pc with | .local .fit=>fits+1 | _=>fits
      match SemiprimeD1StackCalls.step program s with
      | none=>none
      | some q=>
        let values:=(keys.map q.data).toArray
        let freshData:Stack→List Bool:=fun k=>(values[HostIndex.index k]?).getD []
        drive fuel {q with data:=freshData} (steps+1) fields products fits
private def row (d:List Bool):Row:=![[true,false],[false,true],[true],[true,false,true,false],d]
private def check (ds:List (List Bool)) (widthTemplate:List Bool):Bool:=
  let rs:=ds.map row
  let original:=tape rs
  let entries:=ds.map fun d=>({numerator:=⟨true,[true,false,true,false]⟩,denominator:=d,child:=[]}:SemiprimeD1RecoveryIntegerBits.Entry)
  let answer:=(SemiprimeD1RecoveryIntegerBits.denominator widthTemplate entries).bits
  match drive 100000 (initial original widthTemplate) 0 0 0 0 with
  | none=>false
  | some (s,steps,fields,products,fits)=>s.flag.isNone && s.returned.isNone && s.frames.isEmpty &&
    keys.all (fun k=>s.data k==(if k=output then answer else input original widthTemplate k)) &&
    fields==5*ds.length && products==ds.length && fits==(if ds.isEmpty then 0 else 1) &&
    steps==SemiprimeD1StackRecoveryDenominatorExecution.timeBound rs widthTemplate
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
