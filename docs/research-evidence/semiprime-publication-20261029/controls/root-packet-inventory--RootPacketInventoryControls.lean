import RiemannGaussian
import RiemannGaussian.SemiprimeD1StackRootPacketInventoryInput
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RootPacketInventoryControls
open RiemannGaussian SemiprimeD1StackRootPacketInventory
open Lean Elab Command Term Meta
run_cmd liftTermElabM do
  let ty←elabTerm (←`(Stack)) none
  let e←elabTerm (←`((Finset.univ :Finset Stack).val)) none
  let e←Meta.whnf e
  unless e.isAppOfArity ``Quot.mk 3 do throwError "expected literal physical inventory"
  addAndCompile (.defnDecl {
    name:=`RootPacketInventoryControls.roles,levelParams:=[],
    type:=mkApp (mkConst ``List [Level.zero]) ty,value:=e.getAppArgs[2]!,
    hints:=.regular 0,safety:=.safe })
run_cmd liftTermElabM do
  let ty←elabTerm (←`(I.Stack)) none
  let e←elabTerm (←`((Finset.univ :Finset I.Stack).val)) none
  let e←Meta.whnf e
  unless e.isAppOfArity ``Quot.mk 3 do throwError "expected literal physical inventory"
  addAndCompile (.defnDecl {
    name:=`RootPacketInventoryControls.activeRoles,levelParams:=[],
    type:=mkApp (mkConst ``List [Level.zero]) ty,value:=e.getAppArgs[2]!,
    hints:=.regular 0,safety:=.safe })
theorem active_complete (k:I.Stack):k∈activeRoles:=by
  have h:k∈(Finset.univ :Finset I.Stack):=Finset.mem_univ k
  exact h
instance activeBEq:BEq I.Stack:=⟨fun a b=>decide (a=b)⟩
instance activeLawful:LawfulBEq I.Stack where
  eq_of_beq:=by intro a b h;exact of_decide_eq_true h
  rfl:=by intro a;exact decide_eq_true rfl
@[noinline] def materialize (d:I.Stack→List Bool):List (I.Stack×List Bool):=activeRoles.map (fun k=>(k,d k))
@[noinline] def cells (root:R.Stack→List Bool) (values:List (I.Stack×List Bool)) (frames:List Label):
    (k:machine.K)→List (machine.Γ k)
  | none=>frames
  | some (.inl k)=>root k
  | some (.inr k)=>(values.lookup k).getD []
theorem materialize_eq (d:I.Stack→List Bool) (k:I.Stack):
    ((materialize d).lookup k).getD []=d k:=by
  rw [materialize,List.lookup_graph d (active_complete k)]
  rfl
@[noinline] def rebuild (pc:Option Label) (flags:Option Bool×Option Label)
    (root:R.Stack→List Bool) (values:List (I.Stack×List Bool)) (frames:List Label):machine.Cfg:=⟨pc,flags,cells root values frames⟩
def snapshot (cfg:machine.Cfg):machine.Cfg:=rebuild cfg.l cfg.var
  (fun k=>cfg.stk (some (rootStack k)))
  (materialize (fun k=>cfg.stk (some (inventoryStack k)))) (cfg.stk none)
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
      · exact materialize_eq (fun k=>data (some (inventoryStack k))) k
theorem step_snapshot (cfg:machine.Cfg):machine.step (snapshot cfg)=machine.step cfg:=by rw [snapshot_eq]
def walk (start:machine.Cfg):IO (Nat×machine.Cfg×Nat×Nat×Nat×Nat):=do
  let mut cfg:=start
  let mut steps:=0
  let mut copies:=0
  let mut inventory:=0
  let mut classes:=0
  let mut edges:=0
  while !cfg.l.isNone do
    if steps≥1000000 then throw (IO.userError "prepared root-inventory actual-step cap")
    match cfg.l with
    | some (.local (.copy _))=>copies:=copies+1
    | some (.local .inventory)=>inventory:=inventory+1
    | some (.inventory (.local .incrementClass))=>classes:=classes+1
    | some (.inventory (.local .incrementEdge))=>edges:=edges+1
    | _=>pure ()
    let some next:=machine.step cfg | throw (IO.userError "actual compiled step returned none")
    steps:=steps+1
    cfg:=if steps%32=0 then snapshot next else next
  return (steps,cfg,copies,inventory,classes,edges)
def allData (cfg:machine.Cfg) (expected:Stack→List Bool):Bool:=
  roles.all (fun k=>(show List Bool from cfg.stk (some k))==expected k)
def outer:List Label:=[.local .done,.local .start]
def outerEq:List Label→Bool | [.local .done,.local .start]=>true | _=>false
/-- Prepared retained root bank; every foreign/cache/width/shadow word is nonempty except actual scratch. -/
def rootBank (keys:List (List Bool)) (a:Nat):R.Stack→List Bool:=
  Function.update (Function.update (Function.update (fun _=>[true,false,true]) R.copyScratch [])
    Source.keysRole (SemiprimeD1TensorTapeCodec.vectorBits keys))
    Source.catalogueRole (SemiprimeD1StackPacketInventoryEncoding.alphabet a)
/-- Prepared continuation only; universal N-only acquisition is a separate kernel theorem. -/
def check (keys:List (List Bool)) (a:Nat):IO Nat:=do
  let root:=rootBank keys a
  let start:C.State Stack Label:=⟨some (.local (.copy .keys)),some true,some (.local .start),data root (fun _=>[]),outer⟩
  let (steps,cfg,copies,inventory,classes,edges)←walk (SemiprimeD1StackCalls.configuration start)
  let clockCap:=SemiprimeD1StackRootPacketInventoryInput.inventoryCopyTime root+
    SemiprimeD1StackPacketInventoryBounds.byteBound (SemiprimeD1TensorTapeCodec.vectorBits keys)
      (SemiprimeD1StackPacketInventoryEncoding.alphabet a)+2
  let expected:=SemiprimeD1StackPacketInventoryEncoding.done (SemiprimeD1TensorTapeCodec.vectorBits keys)
    (SemiprimeD1StackPacketInventoryEncoding.alphabet a) (SemiprimeD1StackPacketInventoryEncoding.acquire a keys)
  unless allData cfg (data root expected.data) && cfg.var.1.isNone && cfg.var.2.isNone &&
      outerEq (show List Label from cfg.stk none) && copies==2 && inventory==1 &&
      classes==keys.length && edges==keys.length && decide (steps≤clockCap) do
    throw (IO.userError "prepared root-inventory2270 data/source/clock/flag/return mismatch")
  IO.println s!"ROOT_INVENTORY_PREPARED keys={keys.length} a={a} actual_transitions={steps} all2270=true within_own_clock=true all_foreign_retained=true copies=2 inventory_source=1 real_class_edge_bumps=true"
  return steps
def run:IO Unit:=do
  let key:=SemiprimeSourceHistogramKeyBits.frame [] []
  let mut steps:=0
  steps:=steps+(←check [] 0)
  steps:=steps+(←check [key] 0)
  steps:=steps+(←check [key,key] 0)
  steps:=steps+(←check [key,key,key] 0)
  IO.println s!"ROOT_INVENTORY_CONTROLS cases=4 actual_transitions={steps} all2270=true prepared_continuations_only=true within_own_clock=true all_foreign_words_retained=true flags_clear=true two_real_outer_returns=true"
#eval run
end RootPacketInventoryControls
open Lean Elab Command
run_cmd do
  let env←getEnv
  let mut checked:Nat:=0
  for (name,_) in env.constants.toList do
    unless (`RootPacketInventoryControls).isPrefixOf name do continue
    for ax in (←Lean.collectAxioms name) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "unexpected observer axiom {name}: {ax}"
    checked:=checked+1
  logInfo m!"ROOT_INVENTORY_OBSERVER declarations={checked} standard3_only=true"
