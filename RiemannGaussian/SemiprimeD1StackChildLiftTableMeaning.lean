/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildLiftTable
/-! # Exact complete original child table in the physical false-first traversal order
These trees describe the actually written payload. No table builder, entry
function or old/native runtime report is an operand of the finite program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildLiftTableMeaning
open SemiprimeD1TensorTables (Table build)
namespace V
export SemiprimeD1StackVectorTableSpec (tree leafWords)
end V
/-- Complete physical traversal and native table build agree in EVERY original assignment position. -/
theorem tree_build (n : ℕ) (f : List Bool→SemiprimeD1JetRingBits.Run) (front : List Bool) :
    V.tree (fun raw => (f raw).words) front n=(build n (fun bits => f (front++bits))).table := by
  induction n generalizing front with
  | zero => simp only [V.tree,V.leafWords,build,List.append_nil]
  | succ n ih =>
    change Table.fork (V.tree (fun raw => (f raw).words) (front++[false]) n)
      (V.tree (fun raw => (f raw).words) (front++[true]) n)=
      Table.fork (build n (fun bits => f (front++false::bits))).table
        (build n (fun bits => f (front++true::bits))).table
    congr 1
    · simpa only [List.append_assoc,List.singleton_append] using ih (front++[false])
    · simpa only [List.append_assoc,List.singleton_append] using ih (front++[true])
/-- Full literal eager table produced by the concrete individual tape lookup and integer lift. -/
def table {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (p n : ℕ)
    (parent : Table d) (order : List ℕ) : Table n :=
  (SemiprimeD1ChildTableCopyTape.acquire old extra p n ⟨parent,0⟩ order).table
/-- No alignment, assignment permutation or per-entry integer lift is lost by the physical writer. -/
theorem tree_original {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (p n : ℕ)
    (parent : Table d) (order : List ℕ) :
    V.tree (fun raw => (SemiprimeD1ChildTableCopyTape.entry old extra p parent order raw).words) [] n=
      table old extra p n parent order := by
  simpa only [List.nil_append,table,SemiprimeD1ChildTableCopyTape.acquire] using
    tree_build n (SemiprimeD1ChildTableCopyTape.entry old extra p parent order) []
/-- Original parent Good and positive appended axes internally discharge every new coefficient shape/width. -/
theorem table_good {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (p n : ℕ)
    (parent : Table d) (order : List ℕ) (hg : SemiprimeD1TensorTables.Good old parent)
    (he : 0<extra.prod) : SemiprimeD1TensorTables.Good ⟨extra++old.axes,p⟩ (table old extra p n parent order) :=
  SemiprimeD1ChildTableCopyTape.acquire_good old extra p n ⟨parent,0⟩ order hg he
end RiemannGaussian.SemiprimeD1StackChildLiftTableMeaning
