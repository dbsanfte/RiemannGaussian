import RiemannGaussian
import RiemannGaussian.SemiprimeD1StackJetBlocksEncoding
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace JetBlocksControls
open RiemannGaussian SemiprimeD1StackJetBlocks
open SemiprimeD1StackJetBlocksEncoding
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Whole prepared physical sources, including oldprecision0 with longer raw NEWprecision coefficient words. -/
def cases :List (List Nat×List Bool×Nat×List (List Bool)) :=
  [([],[false,true],0,[[true,false,false],[false,true]]),
   ([],[],1,[[],[true]]),
   ([2],[],2,[[true,false,false],[false,true,false],[true]]),
   ([2,3],[true],2,[[true],[false,true,false],[],[true,true,false],[false]]),
   ([2],[false,true],3,[[true,false,false,false],[false,true],[],[true],[true,true,false],[false,false,true],[true]])]
def outer :List Label :=[.local .start,.local .ready]
def outerEq :List Label→Bool
  | [.local .start,.local .ready]=>true
  | _=>false
def walk :Nat→Nat→machine.Cfg→Option (Nat×machine.Cfg)
  | 0,_,_=>none
  | fuel+1,time,cfg=>if cfg.l.isNone then some (time,cfg)
    else (machine.step cfg).bind (walk fuel (time+1))
def check :IO Unit :=do
  let mut total:=0
  for (axes,precision,q,words) in cases do
    let header:=vectorBits (axes.map (fun n=>List.replicate n true))
    let qbits:=List.replicate q true
    let coeff:=vectorBits words
    let before:C.State Stack Label:=⟨some (.local .start),some true,some (.local .ready),input header precision qbits coeff,outer⟩
    let some (time,cfg):=walk 300000 0 (SemiprimeD1StackCalls.configuration before)
      | throw (IO.userError "jet blocks whole prepared source did not halt")
    let expected:Stack→List Bool:=Sum.elim (SemiprimeD1StackJetContextCorrectness.finalData axes precision)
      (Function.update (privateInput qbits coeff) .output (tape axes.prod q words))
    unless cfg.var.1.isNone && cfg.var.2.isNone && outerEq (show List Label from cfg.stk none) &&
        decide (∀k:Stack,(show List Bool from cfg.stk (some k))=expected k) do
      throw (IO.userError "jet blocks rawcoeff/defaultpad/nativeblocks/all31/contextcache/realreturns mismatch")
    total:=total+time
    IO.println s!"JET_BLOCKS_WHOLE axes={axes} oldprecision={SemiprimeBitArithmetic.bitValue precision} q={q} R={axes.prod} input_fields={words.length} actual_transitions={time} all31=true"
  IO.println s!"JET_BLOCKS_WHOLE cases={cases.length} actual_transitions={total} all31=true actual_context_source=true oldrank_acquired=true no_offset_evaluator=true exact_native_blocks=true raw_padded_coefs_preserved=true default_empty_padding=true extra_fields_drained=true source_inputs_and_context_retained=true two_real_outer_returns=true halt_flags_clear=true"
#eval check
end JetBlocksControls
open Lean Elab Command
run_cmd do
  let env←getEnv
  let mut checked:Nat:=0
  for (name,_) in env.constants.toList do
    unless (`JetBlocksControls).isPrefixOf name do continue
    for ax in (←Lean.collectAxioms name) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "unexpected observer axiom {name}: {ax}"
    checked:=checked+1
  logInfo m!"JET_BLOCKS_OBSERVER declarations={checked} standard3_only=true"
