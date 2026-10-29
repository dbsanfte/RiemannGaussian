/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsRows
/-! # Actual per-row physical-source cost and produced-byte caps
Output length below is paid by the SAME actual144 source execution, never by
an old native table report or an advised output-size clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsRowCost
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsEncoding
open SemiprimeD1StackMarkedRootRecordsRows SemiprimeD1StackMarkedRootRecordsBody
open SemiprimeD1StackMarkedRootRecordsParse (mass)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Paid original bytes for this row; no binary numerical value is expanded. -/
def radius (bits : List Bool) (row : Row) : Nat :=
  bits.length+(vectorBits row.scope).length+row.oldTable.length+mass row.fields+2
/-- A descriptor's physically parsed input-index length is part of its byte mass. -/
theorem index_le_mass (row : Row) : (row.fields 2).length ≤ mass row.fields := by
  rw [mass_eq]
  omega
/-- Actual144 source clock is bounded uniformly in every physical scope payload. -/
theorem table_budget (bits : List Bool) (row : Row) (sideBit : Bool) :
    SemiprimeD1StackMarkedPublicInputTableExecution.runBound bits (row.fields 2) sideBit row.scope ≤
      10^24*(radius bits row)^2*2^row.scope.length := by
  apply (SemiprimeD1StackMarkedPublicInputTableBounds.runBound_le bits (row.fields 2) sideBit row.scope).trans
  unfold SemiprimeD1StackMarkedPublicInputTableBounds.polynomial
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have hi := index_le_mass row
  unfold SemiprimeD1StackMarkedPublicInputTableBounds.resource radius
  omega
/-- Every real initial144 word fits its physically supplied input bytes. -/
theorem table_initial_length (bits : List Bool) (row : Row) (sideBit : Bool) (k : T.Stack) :
    ((SemiprimeD1StackMarkedPublicInputTable.initial bits (row.fields 2) sideBit (vectorBits row.scope)).data k).length ≤
      radius bits row := by
  rw [SemiprimeD1StackMarkedRootRecordsTableView.initial_table]
  have hi := index_le_mass row
  unfold SemiprimeD1StackMarkedRootRecordsTableView.tableWords radius
  split_ifs
  all_goals first | (simp only [List.length_cons,List.length_nil];omega) | omega
/-- Actual emitted table bytes are bounded by the actual run's paid tape growth. -/
theorem newTable_length (bits : List Bool) (row : Row) (hb : bits≠[]) :
    (newTable bits row).length ≤ radius bits row+10^24*(radius bits row)^2*2^row.scope.length := by
  cases hside : row.inputSide with
  | none => simp only [newTable,hside];unfold radius;omega
  | some b =>
    obtain ⟨t,ht,hr⟩ := SemiprimeD1StackMarkedPublicInputTableExecution.source_run bits (row.fields 2) b row.scope hb
    have hd := SemiprimeD1StackReturnLink.run_data_bound T.program t (radius bits row) _ _
      (table_initial_length bits row b) hr
    have ho := hd (G.aux .output)
    rw [SemiprimeD1StackMarkedPublicInputTableExecution.output_bytes] at ho
    have hc := table_budget bits row b
    simp only [newTable,hside]
    omega
/-- Both real tag branches fit one paid table cap, including full old-table erasure. -/
theorem bodyBudget_le (bits : List Bool) (row : Row) :
    bodyBudget bits row ≤ radius bits row+10^24*(radius bits row)^2*2^row.scope.length+6 := by
  cases hside : row.inputSide with
  | none => simp only [bodyBudget,hside];omega
  | some b =>
    have ht := table_budget bits row b
    have hh : row.oldTable.length ≤ radius bits row := by unfold radius;omega
    simp only [bodyBudget,hside]
    omega
/-- Own source/parser/logger/cleanup row bound, with actual arity exponent. -/
theorem rowBudget_le (bits : List Bool) (row : Row) (hb : bits≠[]) :
    rowBudget bits row ≤ 10^26*(radius bits row)^2*2^row.scope.length := by
  let R := radius bits row
  let P := 10^24*R^2*2^row.scope.length
  have hR : 2 ≤ R := by dsimp [R,radius];omega
  have he : 1 ≤ (2:Nat)^row.scope.length := Nat.one_le_pow _ _ (by decide)
  have hsq : R ≤ R^2 := Nat.le_pow (by decide : 0 < (2:Nat))
  have hP0 : 10^24*R^2 ≤ P := Nat.le_mul_of_pos_right _ (by positivity)
  have hP : R ≤ P := by dsimp only [P] at *;nlinarith
  have hn := SemiprimeD1StackStaticWordTableBounds.scope_count_le row.scope
  have hb0 := bodyBudget_le bits row
  have ho := newTable_length bits row hb
  have hparts : (vectorBits row.scope).length+row.oldTable.length+mass row.fields ≤ R := by dsimp [R,radius];omega
  change bodyBudget bits row ≤ R+P+6 at hb0
  change (newTable bits row).length ≤ R+P at ho
  unfold rowBudget
  rw [show 10^26*(radius bits row)^2*2^row.scope.length=100*P by dsimp [P,R];ring]
  nlinarith only [hR,hsq,hP0,hP,hn,hb0,ho,hparts]
/-- Every newly emitted row byte is covered by its SAME actual row cap. -/
theorem newRow_length_le (bits : List Bool) (row : Row) :
    (newRow bits row).length ≤ rowBudget bits row := by
  unfold newRow SemiprimeD1StackVertexRecordStream.row
  simp only [List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
  unfold rowBudget
  omega
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsRowCost
