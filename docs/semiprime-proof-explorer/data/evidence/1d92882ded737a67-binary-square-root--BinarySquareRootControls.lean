import RiemannGaussian
import RiemannGaussian.SemiprimeD1StackBinarySquareRoot
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace BinarySquareRootControls
open RiemannGaussian SemiprimeD1StackBinarySquareRoot

open Lean Elab Command Term Meta
run_cmd liftTermElabM do
  let ty ← elabTerm (←`(Stack)) none
  let e ← elabTerm (←`((Finset.univ : Finset Stack).val)) none
  let e ← Meta.whnf e
  unless e.isAppOfArity ``Quot.mk 3 do throwError "expected literal physical inventory"
  addAndCompile (.defnDecl {
    name:=`BinarySquareRootControls.roles,levelParams:=[],
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
def walk (start : machine.Cfg) : IO (Nat×machine.Cfg×Nat×Nat×Nat×Nat×Nat) := do
  let mut cfg := start
  let mut steps := 0
  let mut metaCalls := 0
  let mut trials := 0
  let mut squares := 0
  let mut compares := 0
  let mut shifts := 0
  while !cfg.l.isNone do
    if steps≥2000000 then throw (IO.userError "binary square root actual-step cap")
    match cfg.l with
    | some (.inl .start) => metaCalls := metaCalls+1
    | some (.inl .rootCopy) => trials := trials+1
    | some (.inl .square) => squares := squares+1
    | some (.inl .compare) => compares := compares+1
    | some (.inl .shift) => shifts := shifts+1
    | _ => pure ()
    let some next := machine.step cfg | throw (IO.userError "actual compiled step returned none")
    steps := steps+1
    cfg := if steps%16=0 then snapshot next else next
  return (steps,cfg,metaCalls,trials,squares,compares,shifts)
def allData (cfg : machine.Cfg) (expected : Stack→List Bool) : Bool :=
  roles.all (fun k => (show List Bool from cfg.stk (some k))==expected k)
def expected (bits : List Bool) : Stack→List Bool :=
  bank (Function.update (SemiprimeD1StackPackedRootMetadataEncoding.result bits)
    (M.aux .base) []) (fun _ => []) (fun _ => []) (fun _ => [])
    (fun k => match k with | .root => [] | .output => SemiprimeD1StackBinarySquareRootArithmetic.output bits)
def check (bits : List Bool) : IO Nat := do
  let init := initial bits
  let start : C.State Stack Label := ⟨init.pc,some true,some (.inl .start),init.data,outer⟩
  let (steps,cfg,metas,trials,squares,compares,shifts) ← walk (SemiprimeD1StackCalls.configuration start)
  unless allData cfg (expected bits) && cfg.var.1.isNone && cfg.var.2.isNone &&
      outerEq (show List Label from cfg.stk none) && metas==1 &&
      trials==bits.length+1 && squares==trials && compares==trials && shifts==trials &&
      (show List Bool from cfg.stk (some originalInput))==bits &&
      decide (SemiprimeBitArithmetic.bitValue (show List Bool from cfg.stk (some (aux .output)))=
        Nat.sqrt (SemiprimeBitArithmetic.bitValue bits)) do
    throw (IO.userError "binary sqrt33 whole-bank/source/trial/value/flag/return mismatch")
  IO.println s!"BINARY_SQRT_CASE bytes={bits.length} D={SemiprimeBitArithmetic.bitValue bits} actual_transitions={steps} all33=true metadata_calls=1 trials={trials} squares={squares} compares={compares} shifts={shifts} sqrt={Nat.sqrt (SemiprimeBitArithmetic.bitValue bits)} compact_byte_ABI=true all18_private_clear=true originalD_retained=true flags_clear=true two_outer_returns=true"
  return steps
def run : IO Unit := do
  let mut steps := 0
  for bits in [[],[true],[false,true],[false,false,true],[true,false,false,true],[true,false,false,true,true],[false,false,false],[true,false,false,false,false]] do
    steps := steps+(←check bits)
  IO.println s!"BINARY_SQRT_CONTROLS cases=8 actual_transitions={steps} all33=true original_binary_only=true zero_and_padding=true exact_Lplus1_trials=true real_add_multiply_compare=true physical18word_sweep=true exact_compact_sqrt=true flags_clear=true two_real_outer_returns=true"
#eval run
end BinarySquareRootControls
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name,_) in env.constants.toList do
    unless (`BinarySquareRootControls).isPrefixOf name do continue
    for ax in (←Lean.collectAxioms name) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "unexpected observer axiom {name}: {ax}"
    checked := checked+1
  logInfo m!"BINARY_SQRT_OBSERVER declarations={checked} standard3_only=true"
