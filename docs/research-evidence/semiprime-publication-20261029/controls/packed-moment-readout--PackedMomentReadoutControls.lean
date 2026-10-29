import RiemannGaussian
import RiemannGaussian.SemiprimeD1StackPackedMomentReadoutOriginal
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace PackedMomentReadoutControls
open RiemannGaussian SemiprimeD1StackPackedMomentReadout
open SemiprimeD1StackPackedMomentReadoutEncoding SemiprimeD1StackPackedMomentReadoutExecution
open SemiprimeD1StackPackedMomentReadoutCost
open Lean Elab Command Term Meta
run_cmd liftTermElabM do
  let ty ← elabTerm (←`(Stack)) none
  let e ← elabTerm (←`((Finset.univ : Finset Stack).val)) none
  let e ← Meta.whnf e
  unless e.isAppOfArity ``Quot.mk 3 do throwError "expected literal physical inventory"
  addAndCompile (.defnDecl {
    name:=`PackedMomentReadoutControls.roles,levelParams:=[],
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
  let mut digitCalls := 0
  let mut highSeeds := 0
  while !cfg.l.isNone do
    if steps≥100000 then throw (IO.userError "packed moment readout actual-step cap")
    match cfg.l with
    | some (.inl .start) => metaCalls := metaCalls+1
    | some (.inl (.copyWidth _)) | some (.inl (.copyScalar _)) | some (.inl (.copyOutput _)) => copies := copies+1
    | some (.inl (.acquire _)) => digitCalls := digitCalls+1
    | some (.inl .seedIndex) => highSeeds := highSeeds+1
    | _ => pure ()
    let some next := machine.step cfg | throw (IO.userError "actual compiled step returned none")
    steps := steps+1
    cfg := if steps%16=0 then snapshot next else next
  return (steps,cfg,metaCalls,copies,digitCalls,highSeeds)
def allData (cfg : machine.Cfg) (expected : Stack→List Bool) : Bool :=
  roles.all (fun k => (show List Bool from cfg.stk (some k))==expected k)
def check (bits scalar : List Bool) (cached : Bool) : IO Nat := do
  let init := if cached then ready bits scalar else initial bits scalar
  let start : C.State Stack Label := ⟨init.pc,some true,some (.inl .start),init.data,outer⟩
  let (steps,cfg,metas,copies,digits,seeds) ← walk (SemiprimeD1StackCalls.configuration start)
  let cap := if cached then readyPolynomial bits scalar else polynomial bits scalar
  let base := 2^bits.length
  let v := SemiprimeBitArithmetic.bitValue scalar
  let c := SemiprimeBitArithmetic.bitValue (show List Bool from cfg.stk (some (aux .count)))
  let sm := SemiprimeBitArithmetic.bitValue (show List Bool from cfg.stk (some (aux .sum)))
  unless allData cfg (result bits scalar) && cfg.var.1.isNone && cfg.var.2.isNone &&
      outerEq (show List Label from cfg.stk none) && metas==(if cached then 0 else 1) &&
      copies==6 && digits==2 && seeds==1 && decide (steps≤cap) &&
      (show List Bool from cfg.stk (some originalInput))==bits &&
      (show List Bool from cfg.stk (some scalarInput))==scalar && c==v%base && sm==(v/base)%base do
    throw (IO.userError "packed readout22 data/copies/digits/indices/value/clock/flag/return mismatch")
  IO.println s!"PACKED_READOUT_CASE Nbytes={bits.length} Vbytes={scalar.length} actual_cached_entry={cached} actual_transitions={steps} count={c} sum={sm} all22=true metadata_calls={metas} real_copies=6 radix_calls=2 literal_high_index=1 compact_outputs=true six_radix_roles_clear=true inputs_retained=true within_own_clock=true flags_clear=true two_outer_returns=true"
  return steps
def run : IO Unit := do
  let mut steps := 0
  let cases : List (List Bool×List Bool) := [([],[]),([],[true,false,true]),([true],[false,true,true]),
    ([false,false,true],[true,false,false,false,true]),
    ([false,true,true],[false,true,false,true,false,true]),
    ([true,false,false,true],[true,false,false,false,true,true]),
    ([true,true,true,true],[false,true,false,false,false,false,false,true]),
    ([false,false,false],[true,false,false,false,false,false,true]),
    ([false,false,true],[true,false,false,false,true,false,false])]
  for (bits,scalar) in cases do
    steps := steps+(←check bits scalar false)
    steps := steps+(←check bits scalar true)
  IO.println s!"PACKED_READOUT_CONTROLS cases=18 actual_transitions={steps} all22=true whole_two_input_cases=9 same_actual_metadata_ready_cases=9 two_actual_radix_calls=true six_actual_copies=true no_supplied_count_sum_width=true zero_width_and_padding=true original_inputs_retained=true flags_clear=true two_real_outer_returns=true"
#eval run
end PackedMomentReadoutControls
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name,_) in env.constants.toList do
    unless (`PackedMomentReadoutControls).isPrefixOf name do continue
    for ax in (←Lean.collectAxioms name) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "unexpected observer axiom {name}: {ax}"
    checked := checked+1
  logInfo m!"PACKED_READOUT_OBSERVER declarations={checked} standard3_only=true"
