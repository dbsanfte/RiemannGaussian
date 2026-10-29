import RiemannGaussian
import RiemannGaussian.SemiprimeD1StackPacketOrientation
import RiemannGaussian.SemiprimeD1OrientationBits
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace PacketOrientationControls
open RiemannGaussian SemiprimeD1StackPacketOrientation
open Lean Elab Command Term Meta
/- Materialize the literal finite inventory from its checked quotient constructor.
The new declaration is kernel checked; no choice operation appears in its code. -/
run_cmd liftTermElabM do
  let ty←elabTerm (←`(Stack)) none
  let e←elabTerm (←`((Finset.univ : Finset Stack).val)) none
  let e←Meta.whnf e
  unless e.isAppOfArity ``Quot.mk 3 do throwError "expected literal physical inventory"
  let decl : DefinitionVal := {
    name := `PacketOrientationControls.roles
    levelParams := []
    type := mkApp (mkConst ``List [Level.zero]) ty
    value := e.getAppArgs[2]!
    hints := .regular 0
    safety := .safe
  }
  addAndCompile (.defnDecl decl)
/-- Every19 physical field appears in the host-only materialization. -/
theorem roles_complete (k:Stack) : k∈roles :=by
  have h:k∈(Finset.univ : Finset Stack):=Finset.mem_univ k
  exact h
/-- Fixed physical equality observer for the host-only materialized store. -/
instance stackBEq : BEq Stack :=⟨fun a b=>decide (a=b)⟩
/-- The physical equality observer is actual equality. -/
instance stackLawfulBEq : LawfulBEq Stack where
  eq_of_beq:=by intro a b h;exact of_decide_eq_true h
  rfl:=by intro a;exact decide_eq_true rfl
/-- Eager data materialization cannot retain an old configuration closure. -/
@[noinline] def materialize (d:Stack→List Bool) : List (Stack×List Bool) :=roles.map (fun k=>(k,d k))
/-- The new store constructor receives only eager data and an eager return list. -/
@[noinline] def cells (values:List (Stack×List Bool)) (frames:List Label) :
    (k:machine.K)→List (machine.Γ k)
  | none=>frames
  | some k=>(values.lookup k).getD []
/-- Kernel identity for every actual19 Boolean field in the materialized store. -/
theorem materialize_eq (d:Stack→List Bool) (k:Stack) :
    ((materialize d).lookup k).getD []=d k :=by
  rw [materialize,List.lookup_graph d (roles_complete k)]
  rfl
/-- Eager actual flags, all physical words and actual return cells only. -/
@[noinline] def rebuild (pc:Option Label) (flags:Option Bool×Option Label)
    (values:List (Stack×List Bool)) (frames:List Label) : machine.Cfg :=⟨pc,flags,cells values frames⟩
/-- Exact host-only representation change, with the machine/step completely unchanged. -/
def snapshot (cfg:machine.Cfg) : machine.Cfg :=
  rebuild cfg.l cfg.var (materialize (fun k=>cfg.stk (some k))) (cfg.stk none)
/-- Kernel identity includes pc, both flags, all19 roles and the real return stack. -/
theorem snapshot_eq (cfg:machine.Cfg) : snapshot cfg=cfg :=by
  cases cfg with
  | mk pc flags data=>
    apply congrArg (Turing.TM2.Cfg.mk pc flags)
    funext k
    cases k with
    | none=>rfl
    | some k=>exact materialize_eq (fun k=>data (some k)) k
/-- Representation identity commutes with the SAME actual compiled step. -/
theorem step_snapshot (cfg:machine.Cfg) : machine.step (snapshot cfg)=machine.step cfg :=by rw [snapshot_eq]
/-- Same actual compiled transitions with an imperative host loop and exact snapshots. -/
def walk (stop:machine.Cfg→Bool) (start:machine.Cfg) : IO (Nat×machine.Cfg) :=do
  let mut cfg:=start
  let mut time:=0
  while !cfg.l.isNone && !stop cfg do
    let some next:=machine.step cfg | throw (IO.userError "actual step unexpectedly returned none")
    time:=time+1
    cfg:=if time%32=0 then snapshot next else next
  return (time,cfg)
/-- Exact whole47-field comparison includes the retained actual width and real binary powers. -/
def allData (cfg:machine.Cfg) (expected:Stack→List Bool) : Bool :=
  roles.all (fun k=>(show List Bool from cfg.stk (some k))==expected k)
/-- Two genuine outer returns remain untouched by the whole caller fragment. -/
def outer :List Label :=[.local .reject,.local .done]
/-- Compare actual return cells without deriving equality on all included labels. -/
def outerEq :List Label→Bool | [.local .reject,.local .done]=>true | _=>false
/-- Exact old native orientation is used only by the observer, never the literal source. -/
def expected (left right index:List Bool) (out:SemiprimeD1OrientationBits.Packet) (good:Bool):Stack→List Bool:=
  let base:=Function.update (input left right index) answer [good]
  if good then Function.update (Function.update (Function.update base (aux .keyOutput) out.key)
    (aux .slotOutput) out.slots) (aux .highOutput) out.high else base
/-- Complete compiled source observation includes all19 actual roles and genuine outer returns. -/
def check (name:String) (left right:List (List Bool)) (index:List Bool):IO Unit:=do
  let l:=SemiprimeD1TensorTapeCodec.vectorBits left
  let r:=SemiprimeD1TensorTapeCodec.vectorBits right
  let out:=SemiprimeD1OrientationBits.acquire left right index
  let before:=initial l r index
  let start:C.State Stack Label:=⟨before.pc,some true,some (.local .reject),before.data,outer⟩
  let (steps,cfg)←walk (fun _=>false) (SemiprimeD1StackCalls.configuration start)
  unless allData cfg (expected l r index out out.valid) && cfg.var.1.isNone && cfg.var.2.isNone &&
    outerEq (show List Label from cfg.stk none) do
    throw (IO.userError s!"orientation source/oldbytes/high/slots/all19/returns mismatch {name}")
  IO.println s!"PACKET_ORIENTATION_PASS case={name} actual_steps={steps} success={out.valid} all19=true three_inputs_only=true numeric_not_byte_equality=true cursor_consumed_only_on_ties=true raw_high_preserved=true exact_old_key_slots_high=true allwork_clear=true flags_clear=true exact_two_outer_returns=true"
end PacketOrientationControls
#eval show IO Unit from do
  PacketOrientationControls.check "empty_rows_keep_padded_high" [] [] [false,false,true,false]
  PacketOrientationControls.check "empty_colour_equal_EOF_zero" [[]] [[]] []
  PacketOrientationControls.check "less_no_index_consumption" [[]] [[true]] [true,false,false]
  PacketOrientationControls.check "greater_no_index_consumption" [[true,true]] [[true]] [true,false,true]
  PacketOrientationControls.check "numeric_tie_unequal_padding" [[true]] [[true,false,false]] [true,false,false]
  PacketOrientationControls.check "numeric_zero_unequal_padding" [[]] [[false,false]] [false,true,false]
  PacketOrientationControls.check "allties_missing_bits_are_false" [[],[true],[false,true]] [[],[true],[false,true]] [true]
  PacketOrientationControls.check "mixed_compares_two_ties_exact_high" [[],[true,true],[true],[false,true],[]]
    [[true],[true],[true,false],[false,true],[]] [true,false,true,false,false]
  PacketOrientationControls.check "mismatched_lengths_clear" [[],[true]] [[]] [true,false]
  PacketOrientationControls.check "reverse_mismatched_lengths_clear" [[]] [[],[true]] []
open Lean Elab Command
run_cmd do
  let env←getEnv
  let mut count:Nat:=0
  for (name,ci) in env.constants.toList do
    unless (`PacketOrientationControls).isPrefixOf name do continue
    count:=count+1
    if ci.isAxiom then throwError "unexpected orientation observer axiom {name}"
    for ax in (←Lean.collectAxioms name) do
      unless ax==``propext || ax==``Classical.choice || ax==``Quot.sound do
        throwError "orientation observer {name} unexpected axiom {ax}"
  logInfo m!"PACKET_ORIENTATION_OBSERVER_STD3 constants={count}"
