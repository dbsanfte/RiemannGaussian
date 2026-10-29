import RiemannGaussian
import RiemannGaussian.SemiprimeD1StackPacketRowsEncoding
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Original
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace PacketRowsControls
open RiemannGaussian SemiprimeD1StackPacketRows
open Lean Elab Command Term Meta
/- Materialize the literal finite inventory from its checked quotient constructor.
The new declaration is kernel checked; no choice operation appears in its code. -/
run_cmd liftTermElabM do
  let ty←elabTerm (←`(Stack)) none
  let e←elabTerm (←`((Finset.univ : Finset Stack).val)) none
  let e←Meta.whnf e
  unless e.isAppOfArity ``Quot.mk 3 do throwError "expected literal physical inventory"
  let decl : DefinitionVal := {
    name := `PacketRowsControls.roles
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
/-- All nineteen source/result/work fields after accepted or rejected source execution. -/
def expected (key catalogue:List Bool) (left right:List (List Bool)) (good:Bool) :Stack→List Bool :=
  let base:=Function.update (input key catalogue) success [good]
  if good then Function.update (Function.update base (output false) (SemiprimeD1TensorTapeCodec.vectorBits left))
      (output true) (SemiprimeD1TensorTapeCodec.vectorBits right) else base
/-- Two actual physical input words, complete19-word equality and true halt/return comparison. -/
def check (name:String) (key catalogue:List Bool) (left right:List (List Bool)) (good:Bool) :IO Unit :=do
  let before:=initial key catalogue
  let start:C.State Stack Label:=⟨before.pc,some true,some (.local .reject),before.data,outer⟩
  let (steps,cfg)←walk (fun _=>false) (SemiprimeD1StackCalls.configuration start)
  unless allData cfg (expected key catalogue left right good) && cfg.var.1.isNone && cfg.var.2.isNone &&
      outerEq (show List Label from cfg.stk none) do
    throw (IO.userError s!"packet rows all19/input/EOF/emptyfield/cleanup/flags/outerreturns mismatch {name}")
  IO.println s!"PACKET_ROWS_CONTROL_PASS case={name} actual_steps={steps} success={good} left_fields={left.length} right_fields={right.length} all19=true two_inputs_only=true no_a_operand=true raw_factor_tail=true false_empty_field_not_EOF=true found_empty_payload_distinct_from_missing=true key_catalogue_preserved=true work_clear=true flags_clear=true exact_two_outer_returns=true"
end PacketRowsControls
#eval show IO Unit from do
  let key:=RiemannGaussian.SemiprimeSourceHistogramHeadRefinement.numberKey
  let frame:=RiemannGaussian.SemiprimeSourceHistogramKeyBits.frame
  let records:=RiemannGaussian.SemiprimeD1StackOwnerLookup.records
  let serial:=RiemannGaussian.SemiprimeD1PacketRows.serialize
  let cat0:=records [([],[])] []
  PacketRowsControls.check "a0_found_empty_payload" (frame [] []) cat0 [] [] true
  PacketRowsControls.check "a0_missing_owner" (frame [true] []) cat0 [] [] false
  PacketRowsControls.check "a0_missing_factor_after_found_empty_owner" (frame [] [true]) cat0 [] [] false
  PacketRowsControls.check "empty_catalogue" (frame [] []) (records [] []) [] [] false
  let left:List (List Bool):=[[],[true],[false,true]]
  let right:List (List Bool):=[[true,true],[],[true,false,true]]
  let cat:=records [([],serial left),([true],serial right)] []
  PacketRowsControls.check "paired_fields_including_zero" (frame [] [true]) cat left right true
  PacketRowsControls.check "reversed_IDs_raw_factor_zero" (frame [true] []) cat right left true
  PacketRowsControls.check "numeric_ID_padding_paid" (frame [true,false,false] [false,false]) cat right left true
  PacketRowsControls.check "mismatched_row_EOF" (frame [] [true])
    (records [([],serial [[]]),([true],serial [[],[]])] []) [] [] false
  PacketRowsControls.check "truncated_colour_field" (frame [] [true])
    (records [([],[true]),([true],serial [[]])] []) [] [] false
  PacketRowsControls.check "malformed_joint_field" [true] cat [] [] false
  let a:=1
  let catalogue:=RiemannGaussian.SemiprimeD1StackSourceAlphabet64Encoding.result a
    (RiemannGaussian.SemiprimeD1StackSourceAlphabet64.aux .output)
  PacketRowsControls.check "actual_frozen_Alpha64_a1" (frame [] (key 63)) catalogue [[]] [key 63] true
open Lean Elab Command
run_cmd do
  let env←getEnv
  let mut count:Nat:=0
  for (name,ci) in env.constants.toList do
    unless (`PacketRowsControls).isPrefixOf name do continue
    count:=count+1
    if ci.isAxiom then throwError "unexpected row observer axiom {name}"
    for ax in (←Lean.collectAxioms name) do
      unless ax==``propext || ax==``Classical.choice || ax==``Quot.sound do
        throwError "row observer {name} unexpected axiom {ax}"
  logInfo m!"PACKET_ROWS_OBSERVER_STD3 constants={count}"
