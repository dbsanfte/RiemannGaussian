import RiemannGaussian
import RiemannGaussian.SemiprimeD1StackPackedRootContextExecution
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
namespace PackedRootContextControls
open RiemannGaussian SemiprimeD1StackPackedRootContext
open SemiprimeD1StackPackedRootContextEncoding SemiprimeD1StackPackedRootContextExecution
open Lean Elab Command Term Meta
run_cmd liftTermElabM do
  let ty ← elabTerm (←`(Stack)) none
  let e ← elabTerm (←`((Finset.univ : Finset Stack).val)) none
  let e ← Meta.whnf e
  unless e.isAppOfArity ``Quot.mk 3 do throwError "expected literal physical inventory"
  addAndCompile (.defnDecl {
    name:=`PackedRootContextControls.roles,levelParams:=[],
    type:=mkApp (mkConst ``List [Level.zero]) ty,value:=e.getAppArgs[2]!,
    hints:=.regular 0,safety:=.safe })
theorem roles_complete (k : Stack) : k∈roles := by
  have h : k∈(Finset.univ : Finset Stack) := Finset.mem_univ k
  exact h
instance stackBEq : BEq Stack := ⟨fun a b => decide (a=b)⟩
instance stackLawful : LawfulBEq Stack where
  eq_of_beq := by intro a b h;exact of_decide_eq_true h
  rfl := by intro a;exact decide_eq_true rfl
@[noinline] def materialize (d : Stack→List Bool) : List (Stack×List Bool) := roles.map (fun k => (k,d k))
@[noinline] def cells (values : List (Stack×List Bool)) (frames : List Label) :
    (k : machine.K)→List (machine.Γ k)
  | none => frames
  | some k => (values.lookup k).getD []
theorem materialize_eq (d : Stack→List Bool) (k : Stack) : ((materialize d).lookup k).getD []=d k := by
  rw [materialize,List.lookup_graph d (roles_complete k)]
  rfl
@[noinline] def rebuild (pc : Option Label) (flags : Option Bool×Option Label)
    (values : List (Stack×List Bool)) (frames : List Label) : machine.Cfg := ⟨pc,flags,cells values frames⟩
def snapshot (cfg : machine.Cfg) : machine.Cfg :=
  rebuild cfg.l cfg.var (materialize (fun k => cfg.stk (some k))) (cfg.stk none)
theorem snapshot_eq (cfg : machine.Cfg) : snapshot cfg=cfg := by
  cases cfg with
  | mk pc flags data =>
    apply congrArg (Turing.TM2.Cfg.mk pc flags)
    funext k
    cases k with
    | none => rfl
    | some k => exact materialize_eq (fun k => data (some k)) k
theorem step_snapshot (cfg : machine.Cfg) : machine.step (snapshot cfg)=machine.step cfg := by rw [snapshot_eq]
def outer : List Label := [.inl .done,.inl .start]
def outerEq : List Label→Bool | [.inl .done,.inl .start] => true | _ => false
def walk (start : machine.Cfg) : IO (Nat×machine.Cfg×Nat×Nat×Nat×Nat) := do
  let mut cfg := start
  let mut steps := 0
  let mut metaCalls := 0
  let mut copies := 0
  let mut axesWrites := 0
  let mut contextCalls := 0
  while !cfg.l.isNone do
    if steps≥100000 then throw (IO.userError "packed root context actual-step cap")
    match cfg.l with
    | some (.inl .start) => metaCalls := metaCalls+1
    | some (.inl .copyPrecision) => copies := copies+1
    | some (.inl .seedAxes) => axesWrites := axesWrites+1
    | some (.inl .acquireContext) => contextCalls := contextCalls+1
    | _ => pure ()
    let some next := machine.step cfg | throw (IO.userError "actual compiled step returned none")
    steps := steps+1
    cfg := if steps%16=0 then snapshot next else next
  return (steps,cfg,metaCalls,copies,axesWrites,contextCalls)
def allData (cfg : machine.Cfg) (expected : Stack→List Bool) : Bool :=
  roles.all (fun k => (show List Bool from cfg.stk (some k))==expected k)
def check (bits : List Bool) (cached : Bool) : IO Nat := do
  let initialState := if cached then ready bits else initial bits
  let start : C.State Stack Label := ⟨initialState.pc,some true,some (.inl .start),initialState.data,outer⟩
  let (steps,cfg,metas,copies,axes,contexts) ← walk (SemiprimeD1StackCalls.configuration start)
  let cap := if cached then readyPolynomial bits else polynomial bits
  unless allData cfg (result bits) && cfg.var.1.isNone && cfg.var.2.isNone &&
      outerEq (show List Label from cfg.stk none) && metas==(if cached then 0 else 1) &&
      copies==1 && axes==1 && contexts==1 && decide (steps≤cap) &&
      (show List Bool from cfg.stk (some rank))==[true] &&
      (show List Bool from cfg.stk (some width))==List.replicate (2*bits.length) true do
    throw (IO.userError "packed root context28 data/cache/source/clock/flag/return mismatch")
  IO.println s!"PACKED_ROOT_CTX_CASE bytes={bits.length} actual_cached_entry={cached} actual_transitions={steps} all28=true metadata_calls={metas} actual_precision_copy=1 axes_FALSE_write=1 context_source=1 rank1=true TRUEwidth2ell=true within_own_clock=true flags_clear=true two_outer_returns=true"
  return steps
def run : IO Unit := do
  let mut steps := 0
  for bits in [[],[true],[false,true],[true,false,true],[false,false,false],[true,false,false,false,true]] do
    steps := steps+(←check bits false)
    steps := steps+(←check bits true)
  IO.println s!"PACKED_ROOT_CTX_CONTROLS cases=12 actual_transitions={steps} all28=true whole_cases=6 same_cache_ready_cases=6 no_supplied_precision_rank_width=true all_metadata_retained=true flags_clear=true two_real_outer_returns=true"
#eval run
end PackedRootContextControls
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name,_) in env.constants.toList do
    unless (`PackedRootContextControls).isPrefixOf name do continue
    for ax in (←Lean.collectAxioms name) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "unexpected observer axiom {name}: {ax}"
    checked := checked+1
  logInfo m!"PACKED_ROOT_CTX_OBSERVER declarations={checked} standard3_only=true"
