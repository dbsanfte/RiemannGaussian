/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootOwnerIndex
/-! # Actual original root/index calls with both shared physical inputs acquired
Only static role aliases connect the sources. Exact record/count words are
proved from the real root acquisition and the real original-network interface;
no graph, count or owner getter is a runtime argument.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootOwnerIndexComponents
open SemiprimeD1StackRootOwnerIndex SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
namespace E
export SemiprimeD1StackNetworkOwnerIndexExecution (source done timeBound inputTape original_retained count_retained)
end E
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel)
end Link
local notation "ctl" => (Sum.inl :Control→Label)
/-- Mathematical original acquired root network; it never appears in program/control inputs. -/
def net (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :SemiprimeD1TensorNetwork.Network :=
  SemiprimeD1RootStateResources.root (bitValue bits) hN fixed
/-- Actual original owner records already supplied by the real root source. -/
def rootowners (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :List SemiprimeD1LeafCounter.Vertex :=
  (net bits hN fixed).left.toList
/-- Original factor-record suffix remains intact through the physical index source. -/
def rootSuffix (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :List Bool :=
  SemiprimeD1StackVertexProduct.records (net bits hN fixed).right.toList
/-- Exact actual source input described from the already acquired two physical operands. -/
def indexSource (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :C.State I.Stack I.Label :=
  E.source (rootowners bits hN fixed) (rootSuffix bits hN fixed)
/-- Exact actual halted owner-index bank; specifications do not supply its bytes to runtime. -/
def indexDone (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :C.State I.Stack I.Label :=
  E.done (rootowners bits hN fixed) (rootSuffix bits hN fixed)
/-- Whole completed physical store retains all1804 root source words and all actual index work/shadows. -/
def result (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :Stack→List Bool :=
  data (R.done bits hN fixed tail).data (indexDone bits hN fixed).data
/-- Both actual shared inputs and all private words have their exact used-index projections. -/
theorem data_index (r:R.Stack→List Bool) (i:I.Stack→List Bool)
    (hv:r R.output=i .vertices) (hc:r A.leftCount=i .leftCount) (k:I.Stack) :
    data r i (indexStack k)=i k :=by
  cases k
  · exact hv
  · exact hc
  all_goals rfl
/-- Source record projection is its actual whole physical record input word. -/
theorem indexSource_vertices (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :
    (indexSource bits hN fixed).data .vertices=E.inputTape (rootowners bits hN fixed) (rootSuffix bits hN fixed) :=rfl
/-- Source left-count projection is its actual bounded unary count word. -/
theorem indexSource_leftCount (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :
    (indexSource bits hN fixed).data .leftCount=List.replicate (rootowners bits hN fixed).length true :=rfl
/-- The real root output supplies the whole actual original-network source tape. -/
theorem root_output (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (R.done bits hN fixed tail).data R.output=(indexSource bits hN fixed).data .vertices :=by
  change _=(E.source (net bits hN fixed).left.toList
    (SemiprimeD1StackVertexProduct.records (net bits hN fixed).right.toList)).data .vertices
  rw [SemiprimeD1StackNetworkOwnerIndexOriginal.initial_original (net bits hN fixed)]
  exact SemiprimeD1StackRootNetworkRecordsOriginal.output_original bits hc hN fixed tail
/-- The already acquired E cache supplies the actual source count; M=2E is never substituted. -/
theorem root_left (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (R.done bits hN fixed tail).data A.leftCount=(indexSource bits hN fixed).data .leftCount :=by
  change _=(E.source (net bits hN fixed).left.toList
    (SemiprimeD1StackVertexProduct.records (net bits hN fixed).right.toList)).data .leftCount
  rw [SemiprimeD1StackNetworkOwnerIndexOriginal.initial_original (net bits hN fixed)]
  exact SemiprimeD1StackRootOwnerIndexCoordinates.left_word bits hN fixed tail
/-- Either actual root entry executes inside this caller, retaining all index words EMPTY. -/
theorem root_lift (entry:R.Label) (pc:Control)
    (hc:program (ctl pc)=.call (rootLabel entry) (ctl .index))
    (before after:C.State R.Stack R.Label) (q:Nat)
    (he:before.pc=some entry) (hs:after.pc=none) (hb:before.frames=[]) (ha:after.frames=[])
    (hr:SemiprimeD1StackCalls.run R.program q before=some after) :
    Runs program (q+1) (ctl pc) (data before.data (fun _=>[])) (ctl .index) (data after.data (fun _=>[])) :=by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program rootStack rootLabel Sum.inl_injective
    R.program entry (fun _=>rfl) (ctl pc) (ctl .index) hc q before after _ _ he hb hs ha hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- Actual physical index call is justified by two acquired words, with no graph/count answer operand. -/
theorem index_lift (r:R.Stack→List Bool) (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool)
    (hv:r R.output=E.inputTape owners suffix) (hc:r A.leftCount=List.replicate owners.length true) :
    ∃q ≤ E.timeBound owners suffix,Runs program (q+1) (ctl .index) (data r (fun _=>[])) (ctl .done)
      (data r (E.done owners suffix).data) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackNetworkOwnerIndexExecution.source_run owners suffix
  refine ⟨q,hq,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program indexStack indexLabel index_injective
    I.program (.local .start) (fun _=>rfl) (ctl .index) (ctl .done) rfl q
    (E.source owners suffix) (E.done owners suffix) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;cases k
      · exact hv
      · exact hc
      all_goals rfl
    · intro k _;rfl
  · constructor
    · intro k
      exact data_index r (E.done owners suffix).data
        (hv.trans (E.original_retained owners suffix).symm) (hc.trans (E.count_retained owners suffix).symm) k
    · intro k hk
      rcases k with k|k
      · rfl
      · cases k
        · rfl
        · rfl
        · exact (hk .reader rfl).elim
        · exact (hk .todo rfl).elim
        · exact (hk .ports rfl).elim
        · exact (hk .table rfl).elim
        · exact (hk .valid rfl).elim
        · exact (hk .key rfl).elim
        · exact (hk .owner rfl).elim
        · exact (hk .ownerNext rfl).elim
        · exact (hk .incrementScratch rfl).elim
        · exact (hk .scratch rfl).elim
        · exact (hk .fieldScratch rfl).elim
        · exact (hk .frameBuffer rfl).elim
        · exact (hk .frameScratch rfl).elim
        · exact (hk .history rfl).elim
        · exact (hk .output rfl).elim
/-- Actual original-prefix root result enters the real owner-index source by its two static aliases. -/
theorem index_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ∃q ≤ E.timeBound (rootowners bits hN fixed) (rootSuffix bits hN fixed),
      Runs program (q+1) (ctl .index) (data (R.done bits hN fixed tail).data (fun _=>[])) (ctl .done)
        (result bits hN fixed tail) :=by
  apply index_lift
  · exact (root_output bits hc hN fixed tail).trans (indexSource_vertices bits hN fixed)
  · exact (root_left bits hN fixed tail).trans (indexSource_leftCount bits hN fixed)
end RiemannGaussian.SemiprimeD1StackRootOwnerIndexComponents
