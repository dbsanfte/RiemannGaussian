/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryRecordsSeedBounds

/-! # Literal local-table serialization inventory -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryRecordsTableBounds
open SemiprimeD1BoundaryRecords
open SemiprimeD1BoundaryRecordsReduction
open SemiprimeD1BoundaryRecordsGroupBounds
open SemiprimeD1JetAxes (Context)
open SemiprimeD1TensorTables (Table Good storage)

theorem table_properties (ctx : Context) {n : Nat} (t : Table n) (hg : Good ctx t) :
    GoodEntries ctx (tableEntries t).value ∧ Keys n (tableEntries t).value ∧
      (tableEntries t).value.length≤ storage t := by
  induction t with
  | leaf ws =>
    simp only [tableEntries,SemiprimeD1JetAxes.copyVector_value]
    refine ⟨?_,?_,?_⟩
    · intro e he
      have heq:=List.mem_singleton.mp he
      subst e
      exact hg
    · intro e he; simp only [List.mem_singleton] at he; subst e; simp
    · simp only [List.length_cons,List.length_nil,storage]; omega
  | @fork n l r ihl ihr =>
    obtain ⟨hlg,hlk,hln⟩:=ihl hg.1
    obtain ⟨hrg,hrk,hrn⟩:=ihr hg.2
    simp only [tableEntries]
    refine ⟨?_,?_,?_⟩
    · intro e he
      rcases List.mem_append.mp he with he | he
      · obtain ⟨x,hx,rfl⟩:=List.mem_map.mp he; exact hlg x hx
      · obtain ⟨x,hx,rfl⟩:=List.mem_map.mp he; exact hrg x hx
    · intro e he
      rcases List.mem_append.mp he with he | he
      · obtain ⟨x,hx,rfl⟩:=List.mem_map.mp he
        exact Nat.add_le_add_right (hlk x hx) 1
      · obtain ⟨x,hx,rfl⟩:=List.mem_map.mp he
        exact Nat.add_le_add_right (hrk x hx) 1
    · simp only [List.length_append,List.length_map,storage]; omega

theorem sum_copy (es : List Entry) (B : Nat) (h : ∀e∈es,size e≤B) :
    (es.map (fun e => 3*size e+5)).sum≤(3*B+5)*es.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have hx:=h e List.mem_cons_self
    have ht:=ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- Serialization is polynomial in local depth and literal stored input bytes. -/
def tableBudget (ctx : Context) (n : Nat) : Nat := (n+1)*(3*recordBudget ctx n+10)

theorem table_clock (ctx : Context) {n : Nat} (t : Table n) (hg : Good ctx t) :
    (tableEntries t).clock≤tableBudget ctx n*(storage t+1) := by
  induction t with
  | leaf ws =>
    simp only [tableEntries,storage]
    unfold tableBudget recordBudget
    have hc : 0≤(SemiprimeD1JetAxes.copyVector ws).2 := Nat.zero_le _
    have hm : 0≤ctx.rank*(ctx.precision+1) := Nat.zero_le _
    nlinarith
  | @fork n l r ihl ihr =>
    have hl:=ihl hg.1
    have hr:=ihr hg.2
    obtain ⟨hlg,hlk,hln⟩:=table_properties ctx l hg.1
    obtain ⟨hrg,hrk,hrn⟩:=table_properties ctx r hg.2
    have hsl:=sum_copy (tableEntries l).value (recordBudget ctx n)
      (fun e he => size_le ctx n e (hlg e he) (hlk e he))
    have hsr:=sum_copy (tableEntries r).value (recordBudget ctx n)
      (fun e he => size_le ctx n e (hrg e he) (hrk e he))
    have hsl':=hsl.trans (Nat.mul_le_mul_left _ hln)
    have hsr':=hsr.trans (Nat.mul_le_mul_left _ hrn)
    simp only [tableEntries,storage]
    unfold tableBudget recordBudget at hl hr ⊢
    unfold recordBudget at hsl' hsr'
    nlinarith only [hl,hr,hsl',hsr',hln,Nat.zero_le (ctx.rank*(ctx.precision+1))]

end RiemannGaussian.SemiprimeD1BoundaryRecordsTableBounds
