import RiemannGaussian
import RiemannGaussian.SemiprimeD1StackPacketInventoryEncoding
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Original
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace PacketInventoryControls
open RiemannGaussian SemiprimeD1StackPacketInventory
open Lean Elab Command Term Meta
/- Materialize the literal finite inventory from its checked quotient constructor.
The new declaration is kernel checked; no choice operation appears in its code. -/
run_cmd liftTermElabM do
  let ty←elabTerm (←`(Stack)) none
  let e←elabTerm (←`((Finset.univ : Finset Stack).val)) none
  let e←Meta.whnf e
  unless e.isAppOfArity ``Quot.mk 3 do throwError "expected literal physical inventory"
  let decl : DefinitionVal := {
    name := `PacketInventoryControls.roles
    levelParams := []
    type := mkApp (mkConst ``List [Level.zero]) ty
    value := e.getAppArgs[2]!
    hints := .regular 0
    safety := .safe
  }
  addAndCompile (.defnDecl decl)
/-- Every59 physical field appears in the host-only materialization. -/
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
/-- Kernel identity for every actual59 Boolean field in the materialized store. -/
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
/-- Kernel identity includes pc, both flags, all59 roles and the real return stack. -/
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
def outer :List Label :=[.local .abort,.local .done]
/-- Compare actual return cells without deriving equality on all included labels. -/
def outerEq :List Label→Bool | [.local .abort,.local .done]=>true | _=>false
namespace E
export SemiprimeD1StackPacketInventoryEncoding (acquire result alphabet)
end E
/-- Compare EVERY physical map override/history, discovery order, six-field placement and positive edge. -/
def check (name:String) (a:Nat) (keys:List (List Bool)) :IO Unit:=do
  let bits:=SemiprimeD1TensorTapeCodec.vectorBits keys
  let cat:=E.alphabet a
  let before:=initial bits cat
  let start:C.State Stack Label:=⟨before.pc,some true,some (.local .abort),before.data,outer⟩
  let (steps,cfg)←walk (fun _=>false) (SemiprimeD1StackCalls.configuration start)
  let expected:=E.result bits cat (E.acquire a keys)
  unless allData cfg expected && cfg.var.1.isNone && cfg.var.2.isNone &&
    outerEq (show List Label from cfg.stk none) do
    for k in roles do
      unless (show List Bool from cfg.stk (some k))==expected k do
        IO.println s!"INVENTORY_BAD_WORD actualLen={(cfg.stk (some k)).length} expectedLen={(expected k).length}"
    throw (IO.userError s!"inventory oldj/maps/placement/discovery/edge/all59/returns mismatch {name}")
  IO.println s!"PACKET_INVENTORY_PASS case={name} actual_steps={steps} all59=true two_inputs_only=true OLDj_preserved=true sentinel_byte_keys=true all_overrides_retained=true discovery_order_exact=true sixfield_placements_chronological=true positive_edge_order_exact=true work_clear=true flags_clear=true exact_two_outer_returns=true"
/-- Actual malformed/absent-ID source abort clears all57 noninputs, retaining only the two source words and falseflag. -/
def reject (name:String) (bits cat:List Bool):IO Unit:=do
  let before:=initial bits cat
  let start:C.State Stack Label:=⟨before.pc,some true,some (.local .abort),before.data,outer⟩
  let (steps,cfg)←walk (fun _=>false) (SemiprimeD1StackCalls.configuration start)
  let expected:=Function.update (input bits cat) success [false]
  unless allData cfg expected && cfg.var.1.isNone && cfg.var.2.isNone &&
    outerEq (show List Label from cfg.stk none) do
    throw (IO.userError s!"inventory physical abort/all59/returns mismatch {name}")
  IO.println s!"PACKET_INVENTORY_REJECT case={name} actual_steps={steps} all59=true two_inputs_retained=true all57_noninputs_clear_except_falseflag=true exact_two_outer_returns=true"
end PacketInventoryControls
#eval show IO Unit from do
  let key:=RiemannGaussian.SemiprimeSourceHistogramHeadRefinement.numberKey
  let frame:=RiemannGaussian.SemiprimeSourceHistogramKeyBits.frame
  let k00:=frame [] []
  let k01:=frame [] [true]
  let k10:=frame [true] []
  PacketInventoryControls.check "empty_real_occurrence_stream" 0 []
  PacketInventoryControls.check "a0_one_empty_row_index_zero" 0 [k00]
  PacketInventoryControls.check "a0_three_OLDj_and_edges" 0 [k00,k00,k00]
  PacketInventoryControls.check "a1_five_repeats_samepacket_ties" 1 [k00,k00,k00,k00,k00]
  PacketInventoryControls.check "a1_opposite_classes_shared_packet" 1 [k01,k10,k01,k10,k00]
  PacketInventoryControls.check "a0_raw_highzero_classkeys_distinct" 0 [frame [] [false,false],k00]
  PacketInventoryControls.check "a1_endpoints63andzero" 1 [frame (key 63) [],frame [] (key 63)]
  let cat:=PacketInventoryControls.E.alphabet 0
  PacketInventoryControls.reject "malformed_vector_no_terminator" [] cat
  PacketInventoryControls.reject "missing_owner_a0_presence" (RiemannGaussian.SemiprimeD1TensorTapeCodec.vectorBits [frame [true] []]) cat
open Lean Elab Command
run_cmd do
  let env←getEnv
  let mut count:Nat:=0
  for (name,ci) in env.constants.toList do
    unless (`PacketInventoryControls).isPrefixOf name do continue
    count:=count+1
    if ci.isAxiom then throwError "unexpected inventory observer axiom {name}"
    for ax in (←Lean.collectAxioms name) do
      unless ax==``propext || ax==``Classical.choice || ax==``Quot.sound do
        throwError "inventory observer {name} unexpected axiom {ax}"
  logInfo m!"PACKET_INVENTORY_OBSERVER_STD3 constants={count}"
