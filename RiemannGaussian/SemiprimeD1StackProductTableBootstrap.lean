/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductTableBootstrapParts
/-! # Entire N-only product-table bootstrap and its OWN physical clock
Original N is actually copied, public constants are acquired ONCE, three actual
word scans acquire arity, and every public/checker role is physically cleared.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackProductTableBootstrap
open SemiprimeD1StackProductTable SemiprimeD1StackProductTableState
open SemiprimeD1StackProductTableBootstrapParts SemiprimeD1StackProcedureTrace SemiprimeD1StackProcedureReturns
namespace A
export SemiprimeD1BinaryPublicAcquisition (Stack Label program initial)
end A
/-- The closed start has only original N, not a width/table/cache answer. -/
theorem initial_data (bits : List Bool) : (initial bits).data=data bits 0 [] [] := by
  funext k
  cases k with
  | inl k=>rfl
  | inr k=>cases k <;> rfl
/-- Actual retained-N copy into the public source's real input register. -/
theorem source_copy (bits : List Bool) :
    Runs program (5*bits.length+4) .start (initial bits).data .bootstrap (checkerReady bits [] []) := by
  rw [initial_data]
  have h:=SemiprimeD1StackProductTablePrimitives.copy_call .source .start .bootstrap rfl (data bits 0 [] []) rfl rfl
  have hr:rawReady bits [] []=data bits 0 [] [] := by
    rw [rawReady,List.reverse_nil]
    exact Function.update_eq_self _ _
  rw [checkerReady,hr]
  exact h
/-- The literal public acquirer executes INSIDE this one fixed larger program.
Its own balanced trace justifies the real call/return, never an evaluator. -/
theorem public_call (bits : List Bool) (hb : bits≠[]) :
    ∃t≤SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits,
      Runs program (t+1) .bootstrap (checkerReady bits [] []) (.arityCopy 0) (bootData bits 0 []) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1BinaryPublicAcquisitionExecution.source_run bits hb
  refine ⟨t,ht,?_⟩
  rw [checkerReady_input]
  apply SemiprimeD1StackProcedureCallsTrace.included_call program (fun k : A.Stack=>.inl (.inl k))
    Label.acquisition (by intro a b h;exact Sum.inl.inj (Sum.inl.inj h))
    A.program (SemiprimeD1BinaryPublicAcquisition.mainLabel .start) (fun _=>rfl)
    .bootstrap (.arityCopy 0) rfl t (A.initial bits)
    (⟨none,none,none,SemiprimeD1BinaryPublicAcquisitionComponents.result bits,[]⟩:C.State A.Stack A.Label)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;rfl
    · intro k hk;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      cases k with
      | inl k=>
        cases k with
        | inl k=>exact (hk k rfl).elim
        | inr k=>
          change []=SemiprimeD1StackProductCheck.input [] [] k
          unfold SemiprimeD1StackProductCheck.input
          split
          · rfl
          · split <;> rfl
      | inr k=>cases k <;> rfl
/-- The actual source prefix budget before clearing public/checker caches. -/
def preparationBound (bits : List Bool) : ℕ :=
  SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits+5*bits.length+
    21*(SemiprimeD1StackPublicProductExecution.cached bits).length+20
/-- Closed acquired-arity source prefix from original binary N ONLY. -/
theorem preparation_run (bits : List Bool) (hb : bits≠[]) :
    ∃t≤preparationBound bits,Runs program t .start (initial bits).data .bootstrapClear
      (bootData bits (SemiprimeD1StackProductTableSpec.arity bits) []) := by
  have h0:=source_copy bits
  obtain ⟨a,ha,h1⟩:=public_call bits hb
  have h2:=arity_run bits
  have h:=chain h0 (chain h1 h2)
  refine ⟨_,?_,h⟩
  unfold preparationBound
  omega
/-- Preparation is genuinely quadratic in ORIGINAL physical binary input width. -/
theorem preparationBound_le (bits : List Bool) : preparationBound bits≤10000000*(bits.length+1)^2 := by
  have hc:=SemiprimeD1StackPublicProductBounds.cached_length_le bits
  have hp:=Nat.pow_le_pow_right (by omega : 1≤bits.length+1) (by decide : 1≤2)
  simp only [pow_one] at hp
  unfold preparationBound SemiprimeD1BinaryPublicAcquisitionExecution.timeBound
  omega
/-- Every initial physical role fits the actual supplied N length. -/
theorem initial_length (bits : List Bool) (k : Stack) : ((initial bits).data k).length≤bits.length := by
  rw [initial_data]
  cases k with
  | inl k=>exact Nat.zero_le _
  | inr k=>cases k <;> first | exact le_rfl | exact Nat.zero_le _
/-- Actual completed preparation trace bounds ALL76 checker cells before
clearing, rather than estimating an unexecuted report or supplied cache. -/
theorem boot_inventory_le (bits : List Bool) (hb : bits≠[]) :
    SemiprimeD1StackProductTableCleanup.inventory
      (bootData bits (SemiprimeD1StackProductTableSpec.arity bits) [])≤76*(bits.length+preparationBound bits) := by
  obtain ⟨t,ht,hpre⟩:=preparation_run bits hb
  obtain ⟨finish,hr,hout⟩:=hpre [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program t bits.length _ finish (initial_length bits) hr
  rw [hout.2.1] at hd
  unfold SemiprimeD1StackProductTableCleanup.inventory
  calc
    _ ≤ ∑_k : P.Stack,(bits.length+preparationBound bits) :=
      Finset.sum_le_sum (fun k _=>(hd (.inl k)).trans (by omega))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,SemiprimeD1StackPublicProduct.stack_card,smul_eq_mul]
/-- Own complete bootstrap bound, fixed before every original binary N. -/
def bootstrapBound (bits : List Bool) : ℕ :=100000000000000*(bits.length+1)^2
/-- COMPLETE N-only bootstrap: real original-input source, acquired arity,
physical ALL76-role cleanup and real return to the recursive tree builder. -/
theorem bootstrap_run (bits : List Bool) (hb : bits≠[]) :
    ∃t≤bootstrapBound bits,Runs program t .start (initial bits).data .build
      (data bits (SemiprimeD1StackProductTableSpec.arity bits) [] []) := by
  obtain ⟨a,ha,h0⟩:=preparation_run bits hb
  let bs:=bootData bits (SemiprimeD1StackProductTableSpec.arity bits) []
  obtain ⟨m,hm,hclear⟩:=SemiprimeD1StackProductTableCleanup.clear_returns bs
  have h1:=SemiprimeD1StackProcedureReturns.call program m .bootstrapClear (.clear 0) .build
    bs (SemiprimeD1StackProductTableCleanup.clean bs) rfl hclear
  have he:SemiprimeD1StackProductTableCleanup.clean bs=data bits (SemiprimeD1StackProductTableSpec.arity bits) [] []:=
    clean_bootData bits _
  rw [he] at h1
  have h:=chain h0 h1
  refine ⟨a+(1+m),?_,h⟩
  have hi:=boot_inventory_le bits hb
  change SemiprimeD1StackProductTableCleanup.inventory bs≤76*(bits.length+preparationBound bits) at hi
  have hp:=preparationBound_le bits
  have hq:=Nat.pow_le_pow_right (by omega : 1≤bits.length+1) (by decide : 1≤2)
  simp only [pow_one] at hq
  unfold bootstrapBound
  omega
/-- Every physical data role is part of one fixed83-role inventory. -/
theorem stack_card : Fintype.card Stack=83 := by decide
end RiemannGaussian.SemiprimeD1StackProductTableBootstrap
