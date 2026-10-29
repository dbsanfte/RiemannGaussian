/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootNetworkRows
/-! # Acquired-index alias and actual original-row ready call
Every original-network lookup contract is proved from the real compiled root.
No graph, routing, count or catalogue getter occurs in the program operands.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootNetworkRowsComponents
open SemiprimeD1StackRootNetworkRows SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
namespace E
export SemiprimeD1StackNetworkRowsExecution (ready done timeBound indexResult dictionaryRows)
end E
namespace O
export SemiprimeD1StackNetworkRowsEncoding (ownerAt)
export SemiprimeD1StackNetworkRowsOriginal (original_contract)
end O
namespace A
export SemiprimeD1StackRootOwnerIndexComponents (net rootowners)
end A
local notation "ctl" => (Sum.inl :Control→Label)
/-- The physically retained original factor suffix, as a mathematical list specification only. -/
def rootfactors (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :List SemiprimeD1LeafCounter.Vertex :=
  (A.net bits hN fixed).right.toList
/-- The actual acquired seventeen-role cache, before any factor suffix/lookup/row work. -/
def rowsSource (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :C.State Q.Stack Q.Label :=
  E.ready (A.rootowners bits hN fixed) (rootfactors bits hN fixed)
/-- The actual final row/tally/cache bank; expected routing is proof notation only. -/
def rowsDone (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :C.State Q.Stack Q.Label :=
  E.done (A.rootowners bits hN fixed) (rootfactors bits hN fixed) (O.ownerAt (A.net bits hN fixed))
/-- Whole physical store keeps every original source word and every new private row/tally word. -/
def result (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :Stack→List Bool :=
  data (R.done bits hN fixed tail).data (rowsDone bits hN fixed).data
/-- Generic exact projection through every shared or new actual row role. -/
theorem data_rows (root:R.Stack→List Bool) (rows:Q.Stack→List Bool)
    (hi:∀k,root (R.indexStack k)=rows (.inl k)) (k:Q.Stack) :
    data root rows (rowsStack k)=rows k :=by
  rcases k with k|k
  · exact hi k
  · rfl
/-- The actual index bank already acquired from N supplies every row-ready index operand without a copy or rerun. -/
theorem acquired_index (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool)
    (k:SemiprimeD1StackNetworkOwnerIndex.Stack) :
    (R.done bits hN fixed tail).data (R.indexStack k)=(rowsSource bits hN fixed).data (.inl k) :=
  SemiprimeD1StackRootOwnerIndexOriginal.index_preserved bits hc hN fixed tail k
/-- Either genuine original-input source runs inside this caller while every new row work word stays empty. -/
theorem root_lift (entry:R.Label) (pc:Control)
    (hc:program (ctl pc)=.call (rootLabel entry) (ctl .rows))
    (before after:C.State R.Stack R.Label) (q:Nat)
    (he:before.pc=some entry) (hs:after.pc=none) (hb:before.frames=[]) (ha:after.frames=[])
    (hr:SemiprimeD1StackCalls.run R.program q before=some after) :
    Runs program (q+1) (ctl pc) (data before.data (fun _=>[])) (ctl .rows) (data after.data (fun _=>[])) :=by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program rootStack rootLabel Sum.inl_injective
    R.program entry (fun _=>rfl) (ctl pc) (ctl .rows) hc q before after _ _ he hb hs ha hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- A literal row-ready call reuses its actual acquired index and preserves the caller's complete source bank. -/
theorem rows_lift (root:R.Stack→List Bool) (owners factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool)
    (hp:∀v∈factors,∀p∈v.ports,SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) (E.dictionaryRows owners)=[route p] ∧
      (route p).length≤owners.length+1)
    (hi:∀k,root (R.indexStack k)=E.indexResult owners factors k) :
    ∃q≤E.timeBound owners factors,Runs program (q+1) (ctl .rows) (data root (fun _=>[])) (ctl .done)
      (data root (E.done owners factors route).data) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackNetworkRowsExecution.ready_run owners factors route hp
  refine ⟨q,hq,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program rowsStack rowsLabel rows_injective
    Q.program (.local .copyFactors) (fun _=>rfl) (ctl .rows) (ctl .done) rfl q
    (E.ready owners factors) (E.done owners factors route) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k
      rcases k with k|k
      · exact hi k
      · rcases k with k|k
        · rfl
        · cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k
      apply data_rows
      intro j
      exact hi j
    · intro k hk
      rcases k with k|k
      · rfl
      · exact (hk (.inr k) rfl).elim
/-- The original acquired root discharges all singleton/routing/owner-width contracts and starts the SAMEready program. -/
theorem rows_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ∃q≤E.timeBound (A.rootowners bits hN fixed) (rootfactors bits hN fixed),
      Runs program (q+1) (ctl .rows) (data (R.done bits hN fixed tail).data (fun _=>[])) (ctl .done)
        (result bits hN fixed tail) :=by
  apply rows_lift
  · exact O.original_contract (A.net bits hN fixed)
      (SemiprimeD1StackRootOwnerIndexOriginal.original_wellFormed bits hN fixed)
  · intro k
    exact acquired_index bits hc hN fixed tail k
end RiemannGaussian.SemiprimeD1StackRootNetworkRowsComponents
