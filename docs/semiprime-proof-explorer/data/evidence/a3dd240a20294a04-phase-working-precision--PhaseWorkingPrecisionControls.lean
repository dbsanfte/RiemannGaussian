import RiemannGaussian
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionOriginal
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
namespace PhaseWorkingPrecisionControl
open RiemannGaussian SemiprimeD1StackPhaseWorkingPrecision
attribute [local instance] Fintype.decidableForallFintype
/-- All48 physical data words are eagerly materialized before a new store closure. -/
@[noinline] def values (cfg : machine.Cfg) : Array (List Bool) :=
  #[cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.geometryStack (SemiprimeD1StackPhaseGeometry.subStack .left))))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.geometryStack (SemiprimeD1StackPhaseGeometry.subStack .right))))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.geometryStack (SemiprimeD1StackPhaseGeometry.subStack .scratch))))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.geometryStack (SemiprimeD1StackPhaseGeometry.subStack .output))))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.geometryStack (SemiprimeD1StackPhaseGeometry.aux .exponent))))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.geometryStack (SemiprimeD1StackPhaseGeometry.aux .index))))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.geometryStack (SemiprimeD1StackPhaseGeometry.aux .counter))))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.geometryStack (SemiprimeD1StackPhaseGeometry.aux .center))))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.geometryStack (SemiprimeD1StackPhaseGeometry.aux .alpha))))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.geometryStack (SemiprimeD1StackPhaseGeometry.aux .sign))))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.geometryStack (SemiprimeD1StackPhaseGeometry.aux .zero))))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.geometryStack (SemiprimeD1StackPhaseGeometry.aux .order))))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.geometryStack (SemiprimeD1StackPhaseGeometry.aux .scan))))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.geometryStack (SemiprimeD1StackPhaseGeometry.aux .scratch))))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.aux .levels)))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.aux .left)))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.aux .right)))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.aux .limit)))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.aux .valid)))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.aux .scratch)))),
    cfg.stk (some (metadataStack (M.guardStack (SemiprimeD1StackPhaseGeometryGuard.aux .output)))),
    cfg.stk (some (metadataStack (M.divStack .input))),
    cfg.stk (some (metadataStack (M.divStack .divisor))),
    cfg.stk (some (metadataStack (M.divStack .copied))),
    cfg.stk (some (metadataStack (M.divStack .scratch))),
    cfg.stk (some (metadataStack (M.divStack .quotient))),
    cfg.stk (some (metadataStack (M.divStack .remainder))),
    cfg.stk (some (metadataStack (M.aux .edges))),
    cfg.stk (some (metadataStack (M.aux .precision))),
    cfg.stk (some (metadataStack (M.aux .multiplier))),
    cfg.stk (some (metadataStack (M.aux .multiplicand))),
    cfg.stk (some (metadataStack (M.aux .productScratch))),
    cfg.stk (some (metadataStack (M.aux .q))),
    cfg.stk (some (metadataStack (M.aux .r))),
    cfg.stk (some (metadataStack (M.aux .delta))),
    cfg.stk (some (metadataStack (M.aux .subtractWork))),
    cfg.stk (some (metadataStack (M.aux .copyScratch))),
    cfg.stk (some (aux .left)),
    cfg.stk (some (aux .right)),
    cfg.stk (some (aux .scratch)),
    cfg.stk (some (aux .output)),
    cfg.stk (some (aux .counter)),
    cfg.stk (some (aux .next)),
    cfg.stk (some (aux .todo)),
    cfg.stk (some (aux .zeroTodo)),
    cfg.stk (some (aux .shiftTodo)),
    cfg.stk (some (aux .copyScratch)),
    cfg.stk (some (aux .power))]
/-- Host dispatch captures only already evaluated all48 field values. -/
def data (a : Array (List Bool)) : Stack→List Bool
  | Sum.inl (Sum.inl (Sum.inl (Sum.inl .left)))=>a[0]!
  | Sum.inl (Sum.inl (Sum.inl (Sum.inl .right)))=>a[1]!
  | Sum.inl (Sum.inl (Sum.inl (Sum.inl .scratch)))=>a[2]!
  | Sum.inl (Sum.inl (Sum.inl (Sum.inl .output)))=>a[3]!
  | Sum.inl (Sum.inl (Sum.inl (Sum.inr .exponent)))=>a[4]!
  | Sum.inl (Sum.inl (Sum.inl (Sum.inr .index)))=>a[5]!
  | Sum.inl (Sum.inl (Sum.inl (Sum.inr .counter)))=>a[6]!
  | Sum.inl (Sum.inl (Sum.inl (Sum.inr .center)))=>a[7]!
  | Sum.inl (Sum.inl (Sum.inl (Sum.inr .alpha)))=>a[8]!
  | Sum.inl (Sum.inl (Sum.inl (Sum.inr .sign)))=>a[9]!
  | Sum.inl (Sum.inl (Sum.inl (Sum.inr .zero)))=>a[10]!
  | Sum.inl (Sum.inl (Sum.inl (Sum.inr .order)))=>a[11]!
  | Sum.inl (Sum.inl (Sum.inl (Sum.inr .scan)))=>a[12]!
  | Sum.inl (Sum.inl (Sum.inl (Sum.inr .scratch)))=>a[13]!
  | Sum.inl (Sum.inl (Sum.inr .levels))=>a[14]!
  | Sum.inl (Sum.inl (Sum.inr .left))=>a[15]!
  | Sum.inl (Sum.inl (Sum.inr .right))=>a[16]!
  | Sum.inl (Sum.inl (Sum.inr .limit))=>a[17]!
  | Sum.inl (Sum.inl (Sum.inr .valid))=>a[18]!
  | Sum.inl (Sum.inl (Sum.inr .scratch))=>a[19]!
  | Sum.inl (Sum.inl (Sum.inr .output))=>a[20]!
  | Sum.inl (Sum.inr (Sum.inl .input))=>a[21]!
  | Sum.inl (Sum.inr (Sum.inl .divisor))=>a[22]!
  | Sum.inl (Sum.inr (Sum.inl .copied))=>a[23]!
  | Sum.inl (Sum.inr (Sum.inl .scratch))=>a[24]!
  | Sum.inl (Sum.inr (Sum.inl .quotient))=>a[25]!
  | Sum.inl (Sum.inr (Sum.inl .remainder))=>a[26]!
  | Sum.inl (Sum.inr (Sum.inr .edges))=>a[27]!
  | Sum.inl (Sum.inr (Sum.inr .precision))=>a[28]!
  | Sum.inl (Sum.inr (Sum.inr .multiplier))=>a[29]!
  | Sum.inl (Sum.inr (Sum.inr .multiplicand))=>a[30]!
  | Sum.inl (Sum.inr (Sum.inr .productScratch))=>a[31]!
  | Sum.inl (Sum.inr (Sum.inr .q))=>a[32]!
  | Sum.inl (Sum.inr (Sum.inr .r))=>a[33]!
  | Sum.inl (Sum.inr (Sum.inr .delta))=>a[34]!
  | Sum.inl (Sum.inr (Sum.inr .subtractWork))=>a[35]!
  | Sum.inl (Sum.inr (Sum.inr .copyScratch))=>a[36]!
  | Sum.inr .left=>a[37]!
  | Sum.inr .right=>a[38]!
  | Sum.inr .scratch=>a[39]!
  | Sum.inr .output=>a[40]!
  | Sum.inr .counter=>a[41]!
  | Sum.inr .next=>a[42]!
  | Sum.inr .todo=>a[43]!
  | Sum.inr .zeroTodo=>a[44]!
  | Sum.inr .shiftTodo=>a[45]!
  | Sum.inr .copyScratch=>a[46]!
  | Sum.inr .power=>a[47]!
/-- Kernel exact identity covers all48 roles, not a projected output-only model. -/
theorem data_eq (cfg : machine.Cfg) :data (values cfg)=fun k=>cfg.stk (some k) :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- The old configuration is absent from this completed-array/return store. -/
@[noinline] def rebuild (pc : Option Label) (flags : Option Bool×Option Label)
    (a : Array (List Bool)) (frames : List Label) :machine.Cfg :=
  ⟨pc,flags,fun k=>match k with | none=>frames | some k=>data a k⟩
/-- BOTH payload words and actual none-labelled return cells are eager. -/
def snapshot (cfg : machine.Cfg) :machine.Cfg :=rebuild cfg.l cfg.var (values cfg) (cfg.stk none)
/-- Exact observer identity on pc, flags, all fields and EVERY real return label. -/
theorem snapshot_eq (cfg : machine.Cfg) :snapshot cfg=cfg :=by
  cases cfg with
  | mk pc flags fields=>
    apply congrArg (Turing.TM2.Cfg.mk pc flags)
    funext k
    cases k with
    | none=>rfl
    | some k=>exact congrFun (data_eq _) k
/-- The exact same actual compiled primitive transition is preserved. -/
theorem step_snapshot (cfg : machine.Cfg) :machine.step (snapshot cfg)=machine.step cfg :=by rw [snapshot_eq]
/-- Imperative actual primitive-step counter, with no retained IO continuation chain. -/
def walk (start : machine.Cfg) :IO (Nat×machine.Cfg) :=do
  let mut cfg:=start
  let mut time:=0
  while !cfg.l.isNone do
    if time≥10000000 then throw (IO.userError "phase working precision observer limit")
    let some next:=machine.step cfg | throw (IO.userError "unexpected step none")
    time:=time+1
    cfg:=if time%32=0 then snapshot next else next
  return (time,cfg)
/-- Every old/new physical word, both flags and the exact real caller return are checked. -/
def check (cfg : machine.Cfg) (expected : Stack→List Bool) :IO Unit :=do
  let ok:=decide (∀j:Stack,(show List Bool from cfg.stk (some j))=expected j)
  let frames:=match cfg.stk none with | [.done]=>true | _=>false
  unless cfg.l.isNone && cfg.var.1.isNone && cfg.var.2.isNone && frames && ok do
    throw (IO.userError "all48/cache/originals/binaryD/P/work/flags/exact-return mismatch")
/-- Complete actual source starts ONLY with original a/u/M and binary t/p.
The program physically acquires its guard/i/h/q/r/delta and then BINARY D/P. -/
def full_case (a u edges : Nat) (t p : List Bool) :IO Unit :=do
  let start:SemiprimeD1StackCalls.State Stack Label:=
    ⟨some .start,some true,some .done,input a u edges t p,[.done]⟩
  let (time,cfg)←walk (SemiprimeD1StackCalls.configuration start)
  check cfg (SemiprimeD1StackPhaseWorkingPrecisionComponents.result a u edges t p)
  let D:List Bool:=cfg.stk (some (aux .power))
  let P:List Bool:=cfg.stk (some (aux .output))
  let h:List Bool:=cfg.stk (some (metadataStack (M.divStack .quotient)))
  let q:List Bool:=cfg.stk (some (metadataStack (M.aux .q)))
  IO.println s!"FULL_PHASE_WORKING_PRECISION_PASS a={a} u={u} M={edges} t={SemiprimeBitArithmetic.bitValue t} p_bytes={p.length} actual_transitions={time} h={h.length} q={q.length} D_bytes={D.length} D={SemiprimeBitArithmetic.bitValue D} P_bytes={P.length} P={SemiprimeBitArithmetic.bitValue P} all48roles=true all37cache_retained=true original_binaryp_retained=true no_supplied_derived_words=true work_clear=true flags_clear=true exact_outer_return=true"
/-- Full original-only controls cover all guarded branches, actual div/product/
increment/shift/adder composition, zero h/r, padding, and huge BINARY p/D. -/
def suite :IO Unit :=do
  full_case 0 1 20 [] []
  full_case 3 0 5 [true] [true]
  full_case 3 2 5 [false,false,false,true] [true]
  full_case 3 2 5 [] [true]
  full_case 3 2 5 [false,false,true] [true]
  full_case 2 1 3 [true] [true,false,true]
  full_case 3 2 5 [false,true] [false,false,true]
  full_case 4 3 7 [false,false,true] [true,true,true]
  full_case 2 1 0 [true] [true]
  full_case 64 1 1 [true] (List.replicate 100 true)
end PhaseWorkingPrecisionControl
open PhaseWorkingPrecisionControl
#eval suite
open Lean Elab Command
run_cmd do
  let env←getEnv
  let mut count:Nat:=0
  for (name,ci) in env.constants.toList do
    unless (`PhaseWorkingPrecisionControl).isPrefixOf name do continue
    count:=count+1
    if ci.isAxiom then throwError "unexpected axiom {name}"
    for ax in (←Lean.collectAxioms name) do
      unless ax==``propext || ax==``Classical.choice || ax==``Quot.sound do
        throwError "unexpected transitive axiom {ax} in {name}"
  logInfo m!"PHASE_WORKING_PRECISION_CONTROL_AXIOMS constants={count} standard3_only=true all48fields_and_actual_returns=true snapshot_identity_kernel_checked=true"
