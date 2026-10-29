import RiemannGaussian
import RiemannGaussian.SemiprimeD1StackPacketModeAcquireResources
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace PacketModeAcquireControls
open RiemannGaussian SemiprimeD1StackPacketModeAcquire
open SemiprimeD1StackPacketModeAcquireEncoding
open Lean Elab Command Term Meta
run_cmd liftTermElabM do
  let ty←elabTerm (←`(Stack)) none
  let e←elabTerm (←`((Finset.univ :Finset Stack).val)) none
  let e←Meta.whnf e
  unless e.isAppOfArity ``Quot.mk 3 do throwError "expected literal physical inventory"
  addAndCompile (.defnDecl {
    name:=`PacketModeAcquireControls.roles,levelParams:=[],
    type:=mkApp (mkConst ``List [Level.zero]) ty,value:=e.getAppArgs[2]!,
    hints:=.regular 0,safety:=.safe })

theorem roles_complete (k:Stack):k∈roles:=by
  have h:k∈(Finset.univ :Finset Stack):=Finset.mem_univ k
  exact h
instance roleBEq:BEq Stack:=⟨fun a b=>decide (a=b)⟩
instance roleLawful:LawfulBEq Stack where
  eq_of_beq:=by intro a b h;exact of_decide_eq_true h
  rfl:=by intro a;exact decide_eq_true rfl
@[noinline] def materialize (d:Stack→List Bool):List (Stack×List Bool):=roles.map (fun k=>(k,d k))
@[noinline] def cells (values:List (Stack×List Bool)) (frames:List Label):
    (k:machine.K)→List (machine.Γ k)
  | none=>frames
  | some k=>(values.lookup k).getD []
theorem materialize_eq (d:Stack→List Bool) (k:Stack):
    ((materialize d).lookup k).getD []=d k:=by
  rw [materialize,List.lookup_graph d (roles_complete k)]
  rfl
@[noinline] def rebuild (pc:Option Label) (flags:Option Bool×Option Label)
    (values:List (Stack×List Bool)) (frames:List Label):machine.Cfg:=⟨pc,flags,cells values frames⟩
def snapshot (cfg:machine.Cfg):machine.Cfg:=rebuild cfg.l cfg.var
  (materialize (fun k=>cfg.stk (some k))) (cfg.stk none)
theorem snapshot_eq (cfg:machine.Cfg):snapshot cfg=cfg:=by
  cases cfg with
  | mk pc flags data=>
    apply congrArg (Turing.TM2.Cfg.mk pc flags)
    funext k
    cases k with
    | none=>rfl
    | some k=>exact materialize_eq (fun k=>data (some k)) k
theorem step_snapshot (cfg:machine.Cfg):machine.step (snapshot cfg)=machine.step cfg:=by rw [snapshot_eq]
def outer:List Label:=[.local .done,.local .start]
def outerEq:List Label→Bool | [.local .done,.local .start]=>true | _=>false
def allData (cfg:machine.Cfg) (expected:Stack→List Bool):Bool:=
  roles.all (fun k=>(show List Bool from cfg.stk (some k))==expected k)
def walk (start:machine.Cfg):IO (Nat×machine.Cfg×Nat×Nat×Nat):=do
  let mut cfg:=start
  let mut steps:=0
  let mut counted:=0
  let mut doubled:=0
  let mut calls:=0
  while !cfg.l.isNone do
    if steps≥2000000 then throw (IO.userError "packet mode actual-step cap")
    match cfg.l with
    | some (.local .countPacket)=>counted:=counted+1
    | some (.local .reverseTiles)=>doubled:=doubled+1
    | some (.local .enumerate)=>calls:=calls+1
    | _=>pure ()
    let some next:=machine.step cfg | throw (IO.userError "actual compiled step returned none")
    steps:=steps+1
    cfg:=if steps%32=0 then snapshot next else next
  return (steps,cfg,counted,doubled,calls)
def check (packets:List (List Bool)) (i precision:Nat):IO Nat:=do
  let start:C.State Stack Label:={source packets i precision with flag:=some true,returned:=some (.local .start),frames:=outer}
  let (steps,cfg,counted,doubled,calls)←walk (SemiprimeD1StackCalls.configuration start)
  unless allData cfg (done packets i precision).data && cfg.var.1.isNone && cfg.var.2.isNone &&
      outerEq (show List Label from cfg.stk none) && counted==packets.length && doubled==i && calls==1 &&
      decide (steps≤SemiprimeD1StackPacketModeAcquireExecution.timeBound packets i precision) do
    throw (IO.userError "packet mode all44/source/count/tile/clock/flag/return mismatch")
  IO.println s!"PACKET_MODE packets={packets.length} i={i} WIDTH={precision} actual_transitions={steps} all44=true counted=true doubled=true catalogue_calls=1 within_own_clock=true"
  return steps
def run:IO Unit:=do
  let mut total:=0
  total:=total+(←check [] 0 0)
  total:=total+(←check [] 2 3)
  total:=total+(←check [[]] 0 1)
  total:=total+(←check [[false,false]] 0 2)
  total:=total+(←check [[],[false],[],[false,false]] 1 2)
  total:=total+(←check [[true,false,true]] 2 2)
  IO.println s!"PACKET_MODE_CONTROLS cases=6 actual_transitions={total} all44=true counts_acquired=true tile_value_paid=true flags_clear=true two_real_outer_returns=true"
#eval run
end PacketModeAcquireControls
open Lean Elab Command
run_cmd do
  let env←getEnv
  let mut checked:Nat:=0
  for (name,_) in env.constants.toList do
    unless (`PacketModeAcquireControls).isPrefixOf name do continue
    for ax in (←Lean.collectAxioms name) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "unexpected observer axiom {name}: {ax}"
    checked:=checked+1
  logInfo m!"PACKET_MODE_OBSERVER declarations={checked} standard3_only=true"
