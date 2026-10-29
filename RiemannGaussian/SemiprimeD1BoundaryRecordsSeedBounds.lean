/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryRecordsAttachBounds

/-! # Actual assignment seed report -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryRecordsSeedBounds
open SemiprimeD1BoundaryRecords
open SemiprimeD1BoundaryRecordsBounds
open SemiprimeD1BoundaryRecordsCanonical
open SemiprimeD1BoundaryRecordsGroupBounds
open SemiprimeD1JetAxes (Context)

theorem assignments_keys (n : Nat) : ∀bits∈(assignments n).value,bits.length=n := by
  induction n with
  | zero => simp [assignments]
  | succ n ih =>
    intro bits hb
    simp only [assignments,List.mem_append,List.mem_map] at hb
    rcases hb with ⟨bs,hbs,rfl⟩ | ⟨bs,hbs,rfl⟩ <;> simp only [List.length_cons,ih bs hbs]

theorem seed_length (ctx : Context) (n : Nat) : (seed ctx n).value.length=2^n := by
  simp only [seed,List.length_map,assignments_length]

theorem seed_keys (ctx : Context) (n : Nat) : Keys n (seed ctx n).value := by
  intro e he
  obtain ⟨bits,hb,rfl⟩:=List.mem_map.mp he
  exact (assignments_keys n bits hb).le

/-- Unit creation uses scalar precision and every current coefficient slot. -/
theorem one_clock (ctx : Context) :
    (SemiprimeD1JetAffineCoefficient.one ctx).clock≤SemiprimeD1LeafCounterBounds.oneBudget ctx := by
  have h:=SemiprimeD1JetScalarBits.reduce_clock ctx.precision [true]
  change (SemiprimeD1JetScalarBits.reduce ctx.precision [true]).clock+3*ctx.rank+3≤_
  unfold SemiprimeD1LeafCounterBounds.oneBudget
  omega

/-- Full assignment generation, unit acquisition and complete record-copy factor. -/
def seedBudget (ctx : Context) (n : Nat) : Nat :=
  20*(n+1)+SemiprimeD1LeafCounterBounds.oneBudget ctx+3*recordBudget ctx n+6

theorem seed_clock (ctx : Context) (n : Nat) :
    (seed ctx n).clock≤ seedBudget ctx n*(2^n+1) := by
  have ha:=assignments_clock n
  have hu:=one_clock ctx
  have hs : ((seed ctx n).value.map (fun e => 3*size e+3)).sum≤
      (3*recordBudget ctx n+3)*(seed ctx n).value.length := by
    have hgood:=seed_good ctx n
    have hkeys:=seed_keys ctx n
    have aux : ∀ (es : List Entry), (∀e∈es,size e≤recordBudget ctx n) →
        (es.map (fun e => 3*size e+3)).sum≤(3*recordBudget ctx n+3)*es.length := by
      intro es hh
      induction es with
      | nil => simp
      | cons e es ih =>
        have hx:=hh e List.mem_cons_self
        have ht:=ih (fun x hx => hh x (List.mem_cons_of_mem _ hx))
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        nlinarith
    exact aux _ (fun e he => size_le ctx n e (hgood e he) (hkeys e he))
  rw [seed_length] at hs
  change (assignments n).clock+(SemiprimeD1JetAffineCoefficient.one ctx).clock+
    ((seed ctx n).value.map (fun e => 3*size e+3)).sum+3≤_
  unfold seedBudget
  nlinarith

end RiemannGaussian.SemiprimeD1BoundaryRecordsSeedBounds
