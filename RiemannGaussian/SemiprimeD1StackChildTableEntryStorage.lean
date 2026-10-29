/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntryClock
/-! # All61 actual Boolean roles and genuine return cells at every prefix
The actual cached ranks/precision marker VALUES remain explicit resources.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryStorage
open SemiprimeD1StackChildTableEntry SemiprimeD1StackChildTableEntryEncoding
open SemiprimeD1StackChildTableEntryPrepare SemiprimeD1StackChildTableEntryExecution
open SemiprimeD1StackChildTableEntryBounds SemiprimeD1StackChildTableEntryClock
open SemiprimeD1TensorTapeCodec (vectorBits tape)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeBitArithmetic (bitValue)
/-- Every physically acquired context role is one of its actual retained header/precision/rank/width words, or empty. -/
theorem context_length (axes:List Nat) (p:List Bool) (k:J.Stack):
    (Context.finalData axes p k).length    ≤   (vectorBits (axes.map unary)).length+p.length+axes.prod+bitValue p+1:=by
  rcases k with k|k
  · cases k <;> simp_all [Context.finalData,SemiprimeD1StackJetContext.bank,SemiprimeD1StackJetContextExecution.ready,
      SemiprimeD1StackJetSuffix.data,unary]
    omega
  · rcases k with k|k
    · cases k <;> simp_all [Context.finalData,SemiprimeD1StackJetContext.bank,SemiprimeD1StackAdder.store,
        SemiprimeD1StackUnaryCounterExecution.markers]
      omega
    · fin_cases k <;> simp_all [Context.finalData,SemiprimeD1StackJetContext.bank,SemiprimeD1StackJetContext.cached] <;> omega
/-- The whole front door has only actual axis headers/binary precision in its context allocations. -/
theorem context_initial_length (axes p:List Bool) (k:J.Stack):
    ((J.initial axes p).data k).length    ≤   axes.length+p.length+1:=by
  rcases k with k|k
  · exact Nat.zero_le _
  · rcases k with k|k
    · exact Nat.zero_le _
    · fin_cases k <;> simp_all [SemiprimeD1StackJetContext.initial,SemiprimeD1StackJetContext.bank,
        SemiprimeD1StackJetContext.cached] <;> omega
/-- All seven actual source operands, no rank/cache answers, are counted before whole acquisition. -/
theorem initial_length {d:Nat} (oldAxes newAxes:List Nat) (oldp newp:List Bool)
    (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool) (k:Stack):
    ((initial (tape table) (orderTape order) assignment (vectorBits (oldAxes.map unary)) oldp
      (vectorBits (newAxes.map unary)) newp).data k).length    ≤   resource oldAxes newAxes oldp newp table order assignment:=by
  let S:=resource oldAxes newAxes oldp newp table order assignment
  change _    ≤   S
  rcases k with k|k|k|k|k|k
  · exact (context_initial_length _ _ k).trans (by dsimp [S,resource];omega)
  · exact (context_initial_length _ _ k).trans (by dsimp [S,resource];omega)
  · cases k <;> first | exact Nat.zero_le _ | change assignment.length    ≤   S;dsimp [S,resource];omega
  · cases k <;> exact Nat.zero_le _
  · cases k <;> exact Nat.zero_le _
  · cases k <;> first | exact Nat.zero_le _ | change (tape table).length    ≤   S;dsimp [S,resource];omega | change (orderTape order).length    ≤   S;dsimp [S,resource];omega
/-- The exact ready bank counts all30 already acquired context fields, including their VALUE-materialized rank and precision words. -/
theorem ready_length {d:Nat} (oldAxes newAxes:List Nat) (oldp newp:List Bool)
    (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool) (k:Stack):
    ((ready oldAxes newAxes oldp newp (tape table) (orderTape order) assignment).data k).length    ≤
      resource oldAxes newAxes oldp newp table order assignment:=by
  let S:=resource oldAxes newAxes oldp newp table order assignment
  change _    ≤   S
  rcases k with k|k|k|k|k|k
  · exact (context_length _ _ k).trans (by dsimp [S,resource];omega)
  · exact (context_length _ _ k).trans (by dsimp [S,resource];omega)
  · cases k <;> first | exact Nat.zero_le _ | change assignment.length    ≤   S;dsimp [S,resource];omega
  · cases k <;> exact Nat.zero_le _
  · cases k <;> exact Nat.zero_le _
  · cases k <;> first | exact Nat.zero_le _ | change (tape table).length    ≤   S;dsimp [S,resource];omega | change (orderTape order).length    ≤   S;dsimp [S,resource];omega
/-- Deterministic final halt bounds every reached prefix of the same whole source. -/
theorem source_prefix_fuel {d:Nat} (oldAxes newAxes:List Nat) (ho:∀q∈oldAxes,0<q) (hn:∀q∈newAxes,0<q)
    (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool)
    (hs:(selected table assignment order).length=oldAxes.prod) (hr:oldAxes.prod   ≤   newAxes.prod)
    (fuel:Nat) (out:C.State Stack Label)
    (hp:SemiprimeD1StackCalls.run program fuel (initial (tape table) (orderTape order) assignment
      (vectorBits (oldAxes.map unary)) oldp (vectorBits (newAxes.map unary)) newp)=some out):
    fuel    ≤   wholePolynomial oldAxes newAxes oldp newp table order assignment:=by
  obtain ⟨t,ht,hstop⟩:=source_run_bounded oldAxes newAxes ho hn oldp newp table order assignment hs hr
  have hf:fuel    ≤   t:=by
    by_contra h
    have he:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hp
    have hz:SemiprimeD1StackCalls.run program 1 (done oldAxes newAxes oldp newp (tape table) (orderTape order) assignment (selected table assignment order))=none:=rfl
    rw [hz,Option.bind_none] at hp
    cases hp
  exact hf.trans ht
/-- Deterministic same-program ready halt bounds every reached ready prefix, without any acquisition replay. -/
theorem ready_prefix_fuel {d:Nat} (oldAxes newAxes:List Nat) (ho:0<oldAxes.prod) (hn:0<newAxes.prod)
    (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool)
    (hs:(selected table assignment order).length=oldAxes.prod) (hr:oldAxes.prod   ≤   newAxes.prod)
    (fuel:Nat) (out:C.State Stack Label)
    (hp:SemiprimeD1StackCalls.run program fuel (ready oldAxes newAxes oldp newp (tape table) (orderTape order) assignment)=some out):
    fuel    ≤   readyPolynomial oldAxes newAxes oldp newp table order assignment:=by
  obtain ⟨t,ht,hstop⟩:=ready_run_bounded oldAxes newAxes ho hn oldp newp table order assignment hs hr
  have hf:fuel    ≤   t:=by
    by_contra h
    have he:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hp
    have hz:SemiprimeD1StackCalls.run program 1 (done oldAxes newAxes oldp newp (tape table) (orderTape order) assignment (selected table assignment order))=none:=rfl
    rw [hz,Option.bind_none] at hp
    cases hp
  exact hf.trans ht
/-- Sum ALL61 physical roles before instantiating any large concrete original state. -/
theorem word_sum (words:Stack→List Bool) (cap:Nat) (h:∀k,(words k).length   ≤  cap):
    (∑k:Stack,(words k).length)   ≤  61*cap:=by
  calc
    _   ≤  ∑_k:Stack,cap:=Finset.sum_le_sum (fun k _=>h k)
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
/-- Generic SAME-program physical prefix lemma abstracts source arguments before all-state elaboration. -/
theorem prefix_cells_at (S fuel:Nat) (before out:C.State Stack Label)
    (hd:∀k,(before.data k).length   ≤  S) (hf:before.frames=[])
    (ht:fuel   ≤  100000000*S^2) (hp:SemiprimeD1StackCalls.run program fuel before=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length   ≤  100000000000*S^2:=by
  have hdata:=SemiprimeD1StackReturnLink.run_data_bound program fuel S before out hd hp
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel before out hp
  rw [hf,List.length_nil] at hframes
  have hs:=word_sum out.data (S+fuel) hdata
  have h2:S  ≤  S^2:=Nat.le_pow (by decide:0<(2:Nat))
  omega
/-- Every whole-source prefix counts all61 data roles INCLUDING the unused shadow and all genuine saved return labels. -/
theorem prefix_cells {d:Nat} (oldAxes newAxes:List Nat) (ho:∀q∈oldAxes,0<q) (hn:∀q∈newAxes,0<q)
    (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool)
    (hs:(selected table assignment order).length=oldAxes.prod) (hr:oldAxes.prod  ≤  newAxes.prod)
    (fuel:Nat) (out:C.State Stack Label)
    (hp:SemiprimeD1StackCalls.run program fuel (initial (tape table) (orderTape order) assignment
      (vectorBits (oldAxes.map unary)) oldp (vectorBits (newAxes.map unary)) newp)=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length   ≤  100000000000*(resource oldAxes newAxes oldp newp table order assignment)^2:=by
  exact prefix_cells_at _ fuel _ out (initial_length oldAxes newAxes oldp newp table order assignment) rfl
    (source_prefix_fuel oldAxes newAxes ho hn oldp newp table order assignment hs hr fuel out hp) hp
/-- Same ready-prefix bound includes all acquired caches, every private/shadow word and every real return cell. -/
theorem ready_prefix_cells {d:Nat} (oldAxes newAxes:List Nat) (ho:0<oldAxes.prod) (hn:0<newAxes.prod)
    (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool)
    (hs:(selected table assignment order).length=oldAxes.prod) (hr:oldAxes.prod  ≤  newAxes.prod)
    (fuel:Nat) (out:C.State Stack Label)
    (hp:SemiprimeD1StackCalls.run program fuel (ready oldAxes newAxes oldp newp (tape table) (orderTape order) assignment)=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length   ≤  100000000000*(resource oldAxes newAxes oldp newp table order assignment)^2:=by
  have ht:=ready_prefix_fuel oldAxes newAxes ho hn oldp newp table order assignment hs hr fuel out hp
  have ht':fuel  ≤  100000000*(resource oldAxes newAxes oldp newp table order assignment)^2:=by
    unfold readyPolynomial at ht
    omega
  exact prefix_cells_at _ fuel _ out (ready_length oldAxes newAxes oldp newp table order assignment) rfl ht' hp
/-- Generic exact compiler projection is proved before instantiating original context/table arguments. -/
theorem machine_cells_at (bound fuel:Nat) (before:C.State Stack Label) (cfg:machine.Cfg)
    (hp:(fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration before))=some cfg)
    (hc:∀out,SemiprimeD1StackCalls.run program fuel before=some out→
      (∑k:Stack,(out.data k).length)+out.frames.length  ≤ bound):
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length  ≤ bound:=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .parentTable) (aux .output) (Label.local .start) program fuel before
  have hh:=he.trans hp
  cases hout:SemiprimeD1StackCalls.run program fuel before with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact hc out hout
/-- Every genuine compiled whole-source prefix counts all61 roles and the actual none-labelled return stack. -/
theorem machine_prefix_cells {d:Nat} (oldAxes newAxes:List Nat) (ho:∀q∈oldAxes,0<q) (hn:∀q∈newAxes,0<q)
    (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool)
    (hs:(selected table assignment order).length=oldAxes.prod) (hr:oldAxes.prod ≤ newAxes.prod)
    (fuel:Nat) (cfg:machine.Cfg)
    (hp:(fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration
      (initial (tape table) (orderTape order) assignment (vectorBits (oldAxes.map unary)) oldp (vectorBits (newAxes.map unary)) newp)))=some cfg):
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length  ≤ 100000000000*(resource oldAxes newAxes oldp newp table order assignment)^2:=by
  apply machine_cells_at _ fuel _ cfg hp
  intro out hr'
  exact prefix_cells oldAxes newAxes ho hn oldp newp table order assignment hs hr fuel out hr'
/-- SAME-program compiled ready prefixes retain/count both actual context banks, every private/shadow word and every real return. -/
theorem machine_ready_prefix_cells {d:Nat} (oldAxes newAxes:List Nat) (ho:0<oldAxes.prod) (hn:0<newAxes.prod)
    (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool)
    (hs:(selected table assignment order).length=oldAxes.prod) (hr:oldAxes.prod ≤ newAxes.prod)
    (fuel:Nat) (cfg:machine.Cfg)
    (hp:(fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration
      (ready oldAxes newAxes oldp newp (tape table) (orderTape order) assignment)))=some cfg):
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length  ≤ 100000000000*(resource oldAxes newAxes oldp newp table order assignment)^2:=by
  apply machine_cells_at _ fuel _ cfg hp
  intro out hr'
  exact ready_prefix_cells oldAxes newAxes ho hn oldp newp table order assignment hs hr fuel out hr'
end RiemannGaussian.SemiprimeD1StackChildTableEntryStorage
