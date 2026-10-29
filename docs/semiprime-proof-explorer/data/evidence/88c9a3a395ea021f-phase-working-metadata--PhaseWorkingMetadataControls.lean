import RiemannGaussian
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataOriginal
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
namespace PhaseWorkingMetadataControl
open RiemannGaussian SemiprimeD1StackPhaseWorkingPrecisionMetadata
attribute [local instance] Fintype.decidableForallFintype
/-- All37 physical data words are eagerly materialized before a new store closure. -/
@[noinline] def values (cfg : machine.Cfg) : Array (List Bool) :=
  #[cfg.stk (some (guardStack (G.geometryStack (SemiprimeD1StackPhaseGeometry.subStack .left)))),
    cfg.stk (some (guardStack (G.geometryStack (SemiprimeD1StackPhaseGeometry.subStack .right)))),
    cfg.stk (some (guardStack (G.geometryStack (SemiprimeD1StackPhaseGeometry.subStack .scratch)))),
    cfg.stk (some (guardStack (G.geometryStack (SemiprimeD1StackPhaseGeometry.subStack .output)))),
    cfg.stk (some (guardStack (G.geometryStack (SemiprimeD1StackPhaseGeometry.aux .exponent)))),
    cfg.stk (some (guardStack (G.geometryStack (SemiprimeD1StackPhaseGeometry.aux .index)))),
    cfg.stk (some (guardStack (G.geometryStack (SemiprimeD1StackPhaseGeometry.aux .counter)))),
    cfg.stk (some (guardStack (G.geometryStack (SemiprimeD1StackPhaseGeometry.aux .center)))),
    cfg.stk (some (guardStack (G.geometryStack (SemiprimeD1StackPhaseGeometry.aux .alpha)))),
    cfg.stk (some (guardStack (G.geometryStack (SemiprimeD1StackPhaseGeometry.aux .sign)))),
    cfg.stk (some (guardStack (G.geometryStack (SemiprimeD1StackPhaseGeometry.aux .zero)))),
    cfg.stk (some (guardStack (G.geometryStack (SemiprimeD1StackPhaseGeometry.aux .order)))),
    cfg.stk (some (guardStack (G.geometryStack (SemiprimeD1StackPhaseGeometry.aux .scan)))),
    cfg.stk (some (guardStack (G.geometryStack (SemiprimeD1StackPhaseGeometry.aux .scratch)))),
    cfg.stk (some (guardStack (G.aux .levels))),
    cfg.stk (some (guardStack (G.aux .left))),
    cfg.stk (some (guardStack (G.aux .right))),
    cfg.stk (some (guardStack (G.aux .limit))),
    cfg.stk (some (guardStack (G.aux .valid))),
    cfg.stk (some (guardStack (G.aux .scratch))),
    cfg.stk (some (guardStack (G.aux .output))),
    cfg.stk (some (divStack .input)),
    cfg.stk (some (divStack .divisor)),
    cfg.stk (some (divStack .copied)),
    cfg.stk (some (divStack .scratch)),
    cfg.stk (some (divStack .quotient)),
    cfg.stk (some (divStack .remainder)),
    cfg.stk (some (aux .edges)),
    cfg.stk (some (aux .precision)),
    cfg.stk (some (aux .multiplier)),
    cfg.stk (some (aux .multiplicand)),
    cfg.stk (some (aux .productScratch)),
    cfg.stk (some (aux .q)),
    cfg.stk (some (aux .r)),
    cfg.stk (some (aux .delta)),
    cfg.stk (some (aux .subtractWork)),
    cfg.stk (some (aux .copyScratch))]
/-- Host bank closure captures only its completed array. -/
def data (a : Array (List Bool)) : Stack→List Bool
  | Sum.inl (Sum.inl (Sum.inl .left))=>a[0]!
  | Sum.inl (Sum.inl (Sum.inl .right))=>a[1]!
  | Sum.inl (Sum.inl (Sum.inl .scratch))=>a[2]!
  | Sum.inl (Sum.inl (Sum.inl .output))=>a[3]!
  | Sum.inl (Sum.inl (Sum.inr .exponent))=>a[4]!
  | Sum.inl (Sum.inl (Sum.inr .index))=>a[5]!
  | Sum.inl (Sum.inl (Sum.inr .counter))=>a[6]!
  | Sum.inl (Sum.inl (Sum.inr .center))=>a[7]!
  | Sum.inl (Sum.inl (Sum.inr .alpha))=>a[8]!
  | Sum.inl (Sum.inl (Sum.inr .sign))=>a[9]!
  | Sum.inl (Sum.inl (Sum.inr .zero))=>a[10]!
  | Sum.inl (Sum.inl (Sum.inr .order))=>a[11]!
  | Sum.inl (Sum.inl (Sum.inr .scan))=>a[12]!
  | Sum.inl (Sum.inl (Sum.inr .scratch))=>a[13]!
  | Sum.inl (Sum.inr .levels)=>a[14]!
  | Sum.inl (Sum.inr .left)=>a[15]!
  | Sum.inl (Sum.inr .right)=>a[16]!
  | Sum.inl (Sum.inr .limit)=>a[17]!
  | Sum.inl (Sum.inr .valid)=>a[18]!
  | Sum.inl (Sum.inr .scratch)=>a[19]!
  | Sum.inl (Sum.inr .output)=>a[20]!
  | Sum.inr (Sum.inl .input)=>a[21]!
  | Sum.inr (Sum.inl .divisor)=>a[22]!
  | Sum.inr (Sum.inl .copied)=>a[23]!
  | Sum.inr (Sum.inl .scratch)=>a[24]!
  | Sum.inr (Sum.inl .quotient)=>a[25]!
  | Sum.inr (Sum.inl .remainder)=>a[26]!
  | Sum.inr (Sum.inr .edges)=>a[27]!
  | Sum.inr (Sum.inr .precision)=>a[28]!
  | Sum.inr (Sum.inr .multiplier)=>a[29]!
  | Sum.inr (Sum.inr .multiplicand)=>a[30]!
  | Sum.inr (Sum.inr .productScratch)=>a[31]!
  | Sum.inr (Sum.inr .q)=>a[32]!
  | Sum.inr (Sum.inr .r)=>a[33]!
  | Sum.inr (Sum.inr .delta)=>a[34]!
  | Sum.inr (Sum.inr .subtractWork)=>a[35]!
  | Sum.inr (Sum.inr .copyScratch)=>a[36]!
/-- Exact kernel identity covers all37 actual physical fields. -/
theorem data_eq (cfg : machine.Cfg) :data (values cfg)=fun k=>cfg.stk (some k) :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> cases k <;> rfl
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
    if time≥10000000 then throw (IO.userError "phase working metadata observer limit")
    let some next:=machine.step cfg | throw (IO.userError "unexpected step none")
    time:=time+1
    cfg:=if time%32=0 then snapshot next else next
  return (time,cfg)
/-- Check all originals/acquiredmetadata/work fields, flags and actual outer returns. -/
def check (cfg : machine.Cfg) (expected : Stack→List Bool) :IO Unit :=do
  let ok:=decide (∀j:Stack,(show List Bool from cfg.stk (some j))=expected j)
  let frames:=match cfg.stk none with | [.done]=>true | _=>false
  unless cfg.l.isNone && cfg.var.1.isNone && cfg.var.2.isNone && frames && ok do
    throw (IO.userError "all37/cache/originals/metadata/work/flags/return mismatch")
/-- WHOLE real source starts with ONLY original a/u/M/binaryt/binaryp. No i,
verdict, height, quotient, product, delta or work answer is supplied. -/
def full_case (a u M : Nat) (t p : List Bool) :IO Unit :=do
  let start:SemiprimeD1StackCalls.State Stack Label:=
    ⟨some .start,some true,some .done,input a u M t p,[.done]⟩
  let (time,cfg)←walk (SemiprimeD1StackCalls.configuration start)
  check cfg (SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution.result a u M t p)
  let h:List Bool:=cfg.stk (some (divStack .quotient))
  let q:List Bool:=cfg.stk (some (aux .q))
  let r:List Bool:=cfg.stk (some (aux .r))
  let d:List Bool:=cfg.stk (some (aux .delta))
  IO.println s!"FULL_PHASE_WORKING_METADATA_PASS a={a} u={u} M={M} t={SemiprimeBitArithmetic.bitValue t} p_bytes={p.length} actual_transitions={time} h={h.length} q={q.length} r={r.length} delta={d.length} all37roles=true all21cache_retained=true binaryp_retained=true no_supplied_derived_metadata=true work_clear=true flags_clear=true exact_outer_return=true"
/-- Actual accepted and rejected paths, zero numerator, exact/inexact division,
order boundaries, paid padding and huge BINARY p all run to the real halt. -/
def suite :IO Unit :=do
  full_case 0 1 100 [] []
  full_case 3 0 5 [true] [true]
  full_case 3 2 5 [false,false,false,true] [true]
  full_case 3 2 5 [] [true]
  full_case 3 2 5 [false,false,true] [true]
  full_case 2 1 3 [true] [true,false,true]
  full_case 3 2 5 [false,true] [false,false,true]
  full_case 4 3 7 [false,false,true] [true,true,true]
  full_case 3 3 7 [false,false,true] []
  full_case 2 1 0 [true] [true]
  full_case 64 1 3 [true] (List.replicate 100 true)
  full_case 2 2 3 [false,true,false,false,false,false] [true,false,false,false]
end PhaseWorkingMetadataControl
open PhaseWorkingMetadataControl
#eval suite
open Lean Elab Command
run_cmd do
  let env←getEnv
  let mut count:Nat:=0
  for (name,ci) in env.constants.toList do
    unless (`PhaseWorkingMetadataControl).isPrefixOf name do continue
    count:=count+1
    if ci.isAxiom then throwError "unexpected axiom {name}"
    for ax in (←Lean.collectAxioms name) do
      unless ax==``propext || ax==``Classical.choice || ax==``Quot.sound do
        throwError "unexpected transitive axiom {ax} in {name}"
  logInfo m!"PHASE_WORKING_METADATA_CONTROL_AXIOMS constants={count} standard3_only=true all37fields_and_actual_returns=true snapshot_identity_kernel_checked=true"
