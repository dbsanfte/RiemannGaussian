import RiemannGaussian
import RiemannGaussian.SemiprimeD1StackPackedRootMetadataExecution
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
namespace PackedRootMetadataControls
open RiemannGaussian SemiprimeD1StackPackedRootMetadata
open SemiprimeD1StackPackedRootMetadataEncoding SemiprimeD1StackPackedRootMetadataExecution
open Lean Elab Command
/-- Literal ALL13 allocations, including the allocated adder-left shadow. -/
def roles : List Stack := [boot .input,boot .reverse,boot .width,boot .nonzero,
  adderAllocation .left,adderAllocation .right,adderAllocation .scratch,adderAllocation .output,
  aux .reader,aux .copyScratch,aux .precision,aux .base,aux .template]
theorem roles_complete (k : Stack) : k∈roles := by
  rcases k with k|k|k <;> cases k <;> simp [roles,boot,adderAllocation,aux]
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
def outer : List Label := [.local .done,.local .start]
def outerEq : List Label→Bool | [.local .done,.local .start] => true | _ => false
def walk (start : machine.Cfg) : IO (Nat×machine.Cfg×Nat×Nat×Nat×Nat) := do
  let mut cfg := start
  let mut steps := 0
  let mut bootCalls := 0
  let mut addCalls := 0
  let mut copies := 0
  let mut widthWrites := 0
  while !cfg.l.isNone do
    if steps≥100000 then throw (IO.userError "packed metadata actual-step cap")
    match cfg.l with
    | some (.local .start) => bootCalls := bootCalls+1
    | some (.local .add) => addCalls := addCalls+1
    | some (.local .copyWidth) | some (.local .copySum) => copies := copies+1
    | some (.local .growFirst) | some (.local .growSecond) => widthWrites := widthWrites+1
    | _ => pure ()
    let some next := machine.step cfg | throw (IO.userError "actual compiled step returned none")
    steps := steps+1
    cfg := if steps%16=0 then snapshot next else next
  return (steps,cfg,bootCalls,addCalls,copies,widthWrites)
def allData (cfg : machine.Cfg) (expected : Stack→List Bool) : Bool :=
  roles.all (fun k => (show List Bool from cfg.stk (some k))==expected k)
def check (bits : List Bool) : IO Nat := do
  let start : C.State Stack Label := ⟨some (.local .start),some true,some (.local .start),input bits,outer⟩
  let (steps,cfg,boots,adds,copies,widths) ← walk (SemiprimeD1StackCalls.configuration start)
  unless allData cfg (result bits) && cfg.var.1.isNone && cfg.var.2.isNone &&
      outerEq (show List Label from cfg.stk none) && boots==1 && adds==bits.length &&
      copies==bits.length+1 && widths==2*bits.length && decide (steps≤polynomial bits) do
    throw (IO.userError "packed metadata13 data/source/clock/flag/return mismatch")
  IO.println s!"PACKED_ROOT_META_INPUT bytes={bits.length} actual_transitions={steps} all13=true bootstrap_calls={boots} real_adds={adds} copies={copies} false_width_writes={widths} within_own_clock=true flags_clear=true two_outer_returns=true"
  return steps
def run : IO Unit := do
  let mut steps := 0
  steps := steps+(←check [])
  steps := steps+(←check [true])
  steps := steps+(←check [false,true])
  steps := steps+(←check [true,false,true])
  steps := steps+(←check [false,false,false])
  steps := steps+(←check [true,false,false,false,true])
  IO.println s!"PACKED_ROOT_META_CONTROLS cases=6 actual_transitions={steps} all13=true whole_input_words_only=true no_supplied_length_precision_base=true original_and_full_boot_retained=true private_shadow_clear=true flags_clear=true two_real_outer_returns=true"
#eval run
end PackedRootMetadataControls
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name,_) in env.constants.toList do
    unless (`PackedRootMetadataControls).isPrefixOf name do continue
    for ax in (←Lean.collectAxioms name) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "unexpected observer axiom {name}: {ax}"
    checked := checked+1
  logInfo m!"PACKED_ROOT_META_OBSERVER declarations={checked} standard3_only=true"
