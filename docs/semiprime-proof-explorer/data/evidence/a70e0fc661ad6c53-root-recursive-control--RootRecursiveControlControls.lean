import RiemannGaussian
import RiemannGaussian.SemiprimeD1StackRootRecursiveControlOriginal
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RootRecursiveControlControls
open RiemannGaussian SemiprimeD1StackRootRecursiveControl
def outer : List Label := [.inl .start,.inl .gate]
def outerEq : List Label→Bool
  | [.inl .start,.inl .gate]=>true
  | _=>false
def atFinal : Option Label→Bool
  | some (.inl .done)=>true
  | _=>false
def returnedFinal : Option Label→Bool
  | some (.inl .done)=>true
  | _=>false
def walk : Nat→Nat→machine.Cfg→Option (Nat×machine.Cfg)
  | 0,_,_=>none
  | fuel+1,time,cfg=>if atFinal cfg.l then some (time,cfg)
    else (machine.step cfg).bind (walk fuel (time+1))
def cases : List (Nat×Nat×Nat×Nat) :=
  [(0,0,0,0),(0,0,0,1),(1,0,0,1),(0,3,2,10),(0,3,3,3),(0,3,4,3),
   (1,3,3,4),(2,3,2,10),(3,3,3,3),(4,2,2,3),(0,1,0,1),(0,0,1,1),
   (0,0,2,1),(1,116,512,600)]
def source (leaf minimum levels edges:Nat) (a:List Bool) (k:P.Stack) : List Bool :=
  if k=P.leaf then List.replicate leaf true
  else if k=P.minimum then List.replicate minimum true
  else if k=P.levels then List.replicate levels true
  else if k=P.edges then List.replicate edges true
  else if k=P.exponent then a else [false,true,false,true,true]
def fresh (active:Bool) (levels:Nat) (a:List Bool) : Fresh→List Bool
  | .output=>[active]
  | .nextLevels=>if active then List.replicate (levels/2) true else []
  | .nextExponent=>if active then List.replicate (levels/2) true++List.replicate (levels/2) true++a else []
  | _=>[]
def check : IO Unit := do
  let mut total:=0
  let mut activeCount:=0
  for (leaf,minimum,levels,edges) in cases do
    let a:=[false,true,false,true]
    let cache:=source leaf minimum levels edges a
    let before:C.State Stack Label:=⟨some (.inl .gate),some true,some (.inl .start),
      data cache (fun _=>[]),outer⟩
    let some (time,cfg):=walk 500000 0 (SemiprimeD1StackCalls.configuration before)
      | throw (IO.userError "prepared119 actual gate call did not return")
    let active:=decide (leaf<edges ∧ minimum≤levels ∧ levels≤edges)
    let expected:=data cache (fresh active levels a)
    unless time+1≤300*(leaf+minimum+levels+edges+a.length+1)+2 &&
        atFinal cfg.l && returnedFinal cfg.var.2 && outerEq (show List Label from cfg.stk none) &&
        decide (∀k:Stack,(show List Bool from cfg.stk (some k))=expected k) do
      throw (IO.userError "prepared119 guard/child/allroles/aliases/actualreturn mismatch")
    let some final:=machine.step cfg | throw (IO.userError "prepared119 final halt failed")
    unless final.l.isNone && final.var.1.isNone && final.var.2.isNone &&
        outerEq (show List Label from final.stk none) &&
        decide (∀k:Stack,(show List Bool from final.stk (some k))=expected k) do
      throw (IO.userError "prepared119 halt/flags/realframes/allroles mismatch")
    total:=total+time+1
    if active then activeCount:=activeCount+1
  IO.println s!"ROOT_RECURSIVE_CONTROL_PREPARED cases={cases.length} active={activeCount} actual_transitions={total} all119roles=true all108source_cells_retained=true five_acquired_aliases=true eleven_fresh_roles=true inactive_child_empty=true active_exact_child=true actual_nested_return=true real_outer_frames_preserved=true halt_flags_clear=true own_gate_clock=true"
#eval check
end RootRecursiveControlControls
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name,_) in env.constants.toList do
    unless (`RootRecursiveControlControls).isPrefixOf name do continue
    for ax in (← Lean.collectAxioms name) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "unexpected observer axiom in {name}: {ax}"
    checked := checked+1
  logInfo m!"OBSERVER standard_axioms_only=true declarations={checked}"
