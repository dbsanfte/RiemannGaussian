import RiemannGaussian
import RiemannGaussian.SemiprimeD1StackRootRecoveryWidthInput
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RootRecoveryWidthControls
open RiemannGaussian SemiprimeD1StackRootRecoveryWidth
open Lean Elab Command Term Meta
run_cmd liftTermElabM do
  let ty←elabTerm (←`(Stack)) none
  let e←elabTerm (←`((Finset.univ :Finset Stack).val)) none
  let e←Meta.whnf e
  unless e.isAppOfArity ``Quot.mk 3 do throwError "expected literal physical inventory"
  addAndCompile (.defnDecl {
    name:=`RootRecoveryWidthControls.roles,levelParams:=[],
    type:=mkApp (mkConst ``List [Level.zero]) ty,value:=e.getAppArgs[2]!,
    hints:=.regular 0,safety:=.safe })
run_cmd liftTermElabM do
  let ty←elabTerm (←`(W.Stack)) none
  let e←elabTerm (←`((Finset.univ :Finset W.Stack).val)) none
  let e←Meta.whnf e
  unless e.isAppOfArity ``Quot.mk 3 do throwError "expected literal physical inventory"
  addAndCompile (.defnDecl {
    name:=`RootRecoveryWidthControls.activeRoles,levelParams:=[],
    type:=mkApp (mkConst ``List [Level.zero]) ty,value:=e.getAppArgs[2]!,
    hints:=.regular 0,safety:=.safe })
theorem active_complete (k:W.Stack):k∈activeRoles:=by
  have h:k∈(Finset.univ :Finset W.Stack):=Finset.mem_univ k
  exact h
instance activeBEq:BEq W.Stack:=⟨fun a b=>decide (a=b)⟩
instance activeLawful:LawfulBEq W.Stack where
  eq_of_beq:=by intro a b h;exact of_decide_eq_true h
  rfl:=by intro a;exact decide_eq_true rfl
@[noinline] def materialize (d:W.Stack→List Bool):List (W.Stack×List Bool):=activeRoles.map (fun k=>(k,d k))
@[noinline] def cells (root:R.Stack→List Bool) (values:List (W.Stack×List Bool)) (frames:List Label):
    (k:machine.K)→List (machine.Γ k)
  | none=>frames
  | some (.inl k)=>root k
  | some (.inr k)=>(values.lookup k).getD []
theorem materialize_eq (d:W.Stack→List Bool) (k:W.Stack):
    ((materialize d).lookup k).getD []=d k:=by
  rw [materialize,List.lookup_graph d (active_complete k)]
  rfl
@[noinline] def rebuild (pc:Option Label) (flags:Option Bool×Option Label)
    (root:R.Stack→List Bool) (values:List (W.Stack×List Bool)) (frames:List Label):machine.Cfg:=⟨pc,flags,cells root values frames⟩
def snapshot (cfg:machine.Cfg):machine.Cfg:=rebuild cfg.l cfg.var
  (fun k=>cfg.stk (some (rootStack k)))
  (materialize (fun k=>cfg.stk (some (widthStack k)))) (cfg.stk none)
theorem snapshot_eq (cfg:machine.Cfg):snapshot cfg=cfg:=by
  cases cfg with
  | mk pc flags data=>
    apply congrArg (Turing.TM2.Cfg.mk pc flags)
    funext k
    cases k with
    | none=>rfl
    | some k=>
      rcases k with k|k
      · rfl
      · exact materialize_eq (fun k=>data (some (widthStack k))) k
theorem step_snapshot (cfg:machine.Cfg):machine.step (snapshot cfg)=machine.step cfg:=by rw [snapshot_eq]
def walk (start:machine.Cfg):IO (Nat×machine.Cfg×Nat×Nat):=do
  let mut cfg:=start
  let mut steps:=0
  let mut copies:=0
  let mut width:=0
  while !cfg.l.isNone do
    if steps≥1000000 then throw (IO.userError "prepared root-width actual-step cap")
    match cfg.l with
    | some (.local (.copy _))=>copies:=copies+1
    | some (.local .width)=>width:=width+1
    | _=>pure ()
    let some next:=machine.step cfg | throw (IO.userError "actual compiled step returned none")
    steps:=steps+1
    cfg:=if steps%32=0 then snapshot next else next
  return (steps,cfg,copies,width)
def allData (cfg:machine.Cfg) (expected:Stack→List Bool):Bool:=
  roles.all (fun k=>(show List Bool from cfg.stk (some k))==expected k)
def outer:List Label:=[.local .done,.local .start]
def outerEq:List Label→Bool | [.local .done,.local .start]=>true | _=>false
/-- Supplementary prepared retained root bank; every foreign/cache/shadow word is nonempty except actual scratch. -/
def rootBank (a M:Nat):R.Stack→List Bool:=
  Function.update (Function.update (Function.update (fun _=>[true,false,true]) R.copyScratch [])
    O.exponentRole (List.replicate a true)) O.edgesRole (List.replicate M true)
/-- Prepared continuation only; the universal N-only theorem is verified separately. -/
def check (a M:Nat):IO Nat:=do
  let root:=rootBank a M
  let start:C.State Stack Label:=⟨some (.local (.copy .exponent)),some true,some (.local .start),data root (fun _=>[]),outer⟩
  let (steps,cfg,copies,width)←walk (SemiprimeD1StackCalls.configuration start)
  let clockCap:=SemiprimeD1StackRootRecoveryWidthInput.widthCopyTime root+
    SemiprimeD1StackRecoveryWidthBounds.polynomial a M+2
  unless allData cfg (data root (SemiprimeD1StackRecoveryWidthEncoding.done a M).data) &&
      cfg.var.1.isNone && cfg.var.2.isNone && outerEq (show List Label from cfg.stk none) &&
      copies==2 && width==1 && decide (steps≤clockCap) do
    throw (IO.userError "prepared root-width2211 data/source/clock/flag/return mismatch")
  IO.println s!"ROOT_WIDTH_PREPARED a={a} M={M} actual_transitions={steps} all2211=true within_own_clock=true all_foreign_retained=true copies=2 width_source=1"
  return steps
def run:IO Unit:=do
  let mut steps:=0
  steps:=steps+(←check 0 0)
  steps:=steps+(←check 1 0)
  steps:=steps+(←check 0 1)
  steps:=steps+(←check 2 0)
  IO.println s!"ROOT_WIDTH_CONTROLS cases=4 actual_transitions={steps} all2211=true prepared_continuations_only=true within_own_clock=true all_foreign_words_retained=true flags_clear=true two_real_outer_returns=true"
#eval run
end RootRecoveryWidthControls
open Lean Elab Command
run_cmd do
  let env←getEnv
  let mut checked:Nat:=0
  for (name,_) in env.constants.toList do
    unless (`RootRecoveryWidthControls).isPrefixOf name do continue
    for ax in (←Lean.collectAxioms name) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "unexpected observer axiom {name}: {ax}"
    checked:=checked+1
  logInfo m!"ROOT_WIDTH_OBSERVER declarations={checked} standard3_only=true"
