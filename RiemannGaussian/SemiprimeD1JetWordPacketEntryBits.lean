/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketEntryBits
import RiemannGaussian.SemiprimeD1JetWordModeBounds
import RiemannGaussian.SemiprimeD1PacketModeMask
import RiemannGaussian.SemiprimeD1PacketEntryInputs
import RiemannGaussian.SemiprimeD1JetKernelBits
import RiemannGaussian.SemiprimeD1JetModeBits
import RiemannGaussian.SemiprimeD1TensorTables

/-! # Word-supplied concrete packet row recipes and entries
The actual child bucket supplies every row/column bit and orientation slot.
Global beta is restricted to this packet's target modes before coefficient
extraction. Source factors use the original beta. No old tensor evaluator,
mode-coefficient callback, or semantic ring value appears on the runtime path.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1JetWordPacketEntryBits
open SemiprimeD1JetAxes SemiprimeD1PacketEntryInputs
open SemiprimeD1JetAffineCoefficient (JetRun Row)

open SemiprimeD1PacketEntryBits (borrow multiply sameBit sourceProduct)

/-- Literal sign application; negative uses the actual acquired modular minus one. -/
def signed (ctx : Context) (negative : Bool) (value : JetRun) : JetRun :=
  if negative then multiply ctx (SemiprimeD1JetWordSourceBits.constant ctx ⟨true,[true]⟩) value
  else
    let out := copyVector value.words
    ⟨out.1,value.clock+out.2+3⟩

/-- One actual local-column contribution to a real row. -/
def baseTerm (ctx : Context) (z : JetRun) (a : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row column : Wire a) : JetRun :=
  if column.bit then SemiprimeD1JetWordKernelBits.acquireOriginal ctx (borrow z) a t row.slot column.slot
  else SemiprimeD1JetAffineCoefficient.zero ctx

/-- Actual local constant term, including `1-base` for a false row bit. -/
def rowBase (ctx : Context) (z : JetRun) (a : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a) (columns : List (Wire a)) : JetRun :=
  let base := SemiprimeD1JetAffineCoefficient.sumRuns ctx (columns.map (baseTerm ctx z a t row))
  if row.bit then base else
    let one := SemiprimeD1JetAffineCoefficient.one ctx
    let negative := signed ctx true base
    let out := SemiprimeD1JetRingBits.add ctx one.words negative.words
    ⟨out.words,one.clock+negative.clock+out.clock+5⟩

/-- Actual signed crossing mode. A physical same-bit test also guards the original
odd-unit mode supplier, rather than assuming that bit relation as advice. -/
def coefficient (ctx : Context) (z : JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a)
    (item : SemiprimeD1PacketModeMask.Item) : JetRun :=
  let tile : Fin (2^a) := ⟨item.tile%2^a,Nat.mod_lt _ (by positivity)⟩
  let test := sameBit row.slot.val tile.val i.val
  if item.inPacket && item.targetHere && !item.sourceHere && test.value then
    let mode := SemiprimeD1JetWordModeBits.acquireOriginal ctx (borrow z) a i.val item.mode.order t row.slot tile
    let out := signed ctx (!row.bit) mode
    ⟨out.words,out.clock+test.work+item.tile+row.slot.val+2^a+10⟩
  else
    let out := SemiprimeD1JetAffineCoefficient.zero ctx
    ⟨out.words,out.clock+test.work+item.tile+row.slot.val+2^a+10⟩

/-- Actual coefficient vector acquisition in the unchanged global catalogue order. -/
def coefficients (ctx : Context) (z : JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a) :
    List SemiprimeD1PacketModeMask.Item→SemiprimeMaterializedWords.Run (List (List (List Bool)))
  | [] => ⟨[],1⟩
  | item::items =>
    let value := coefficient ctx z a i t row item
    let tail := coefficients ctx z a i t row items
    ⟨value.words::tail.value,value.clock+tail.work+4⟩

/-- Concrete row recipe and its retained base/mode data acquisition. -/
def recipe (ctx : Context) (z : JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a) (columns : List (Wire a))
    (items : List SemiprimeD1PacketModeMask.Item) : SemiprimeMaterializedWords.Run Row :=
  let base := rowBase ctx z a t row columns
  let modes := coefficients ctx z a i t row items
  ⟨⟨base.words,modes.value⟩,base.clock+modes.work+5⟩

/-- Acquire every actual real-row recipe once and preserve the original row order. -/
def recipes (ctx : Context) (z : JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (columns : List (Wire a))
    (items : List SemiprimeD1PacketModeMask.Item) : List (Wire a)→SemiprimeMaterializedWords.Run (List Row)
  | [] => ⟨[],1⟩
  | row::rows =>
    let value := recipe ctx z a i t row columns items
    let tail := recipes ctx z a i t columns items rows
    ⟨value.value::tail.value,value.work+tail.work+4⟩

/-- Actual single-entry execution. Header/source producers are retained by the
outer table acquisition once; this function retains all per-assignment work. -/
def evaluate {V : ℕ} (ctx : Context) (z : JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (items : SemiprimeD1PacketModeMask.Cache)
    (endpoints : List (SemiprimeD1ChildGraph.Endpoint V)) (beta : List ℕ) (bits : List Bool) : JetRun :=
  let input := gather a endpoints bits
  let restricted := SemiprimeD1PacketModeMask.restrict items beta
  let rows := recipes ctx (borrow z) a i t input.columns items.items input.rows
  let target := SemiprimeD1JetAffineCoefficient.evaluate ctx items.items.length rows.value restricted.value
  let source := sourceProduct ctx a i input.columns beta items.items 0
  let out := multiply ctx target source
  ⟨out.words,input.clock+restricted.work+rows.work+out.clock+beta.length+10⟩

/-- Physical signed application has the original literal result bytes. -/
theorem signed_words (ctx : Context) (negative : Bool) (value : JetRun) :
    (signed ctx negative value).words=(SemiprimeD1PacketEntryBits.signed ctx negative value).words := by
  dsimp only [signed,SemiprimeD1PacketEntryBits.signed]
  split
  · dsimp only [multiply]
    rw [SemiprimeD1JetWordSourceBits.constant_words_eq_integerVector ctx ⟨true,[true]⟩ (-1) rfl]
  · rfl

/-- Signed output depends only on the literal input vector. -/
theorem signed_words_congr (ctx : Context) (negative : Bool) (left right : JetRun)
    (h:left.words=right.words) : (signed ctx negative left).words=(signed ctx negative right).words := by
  dsimp only [signed,multiply]
  split <;> rw [h]

/-- Actual sum payloads depend only on the original ordered payload list. -/
theorem sum_words_congr (ctx : Context) (xs ys : List JetRun)
    (h:xs.map (fun r=>r.words)=ys.map (fun r=>r.words)) :
    (SemiprimeD1JetAffineCoefficient.sumRuns ctx xs).words=
      (SemiprimeD1JetAffineCoefficient.sumRuns ctx ys).words := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => cases h
  | cons x xs ih => cases ys with
    | nil => cases h
    | cons y ys =>
      have he:=List.cons.inj h
      change (SemiprimeD1JetRingBits.add ctx x.words
        (SemiprimeD1JetAffineCoefficient.sumRuns ctx xs).words).words=_
      have hx:x.words=y.words:=he.1
      rw [hx,ih ys he.2]
      rfl

/-- Actual base contribution uses the acquired original word entry. -/
theorem baseTerm_words (ctx : Context) (hpos:ctx.Positive) (z : JetRun) (a : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row column : Wire a) :
    (baseTerm ctx z a t row column).words=
      (SemiprimeD1PacketEntryBits.baseTerm ctx z a t row column).words := by
  dsimp only [baseTerm,SemiprimeD1PacketEntryBits.baseTerm]
  split
  · exact SemiprimeD1JetWordKernelBits.acquireOriginal_words ctx hpos _ _ _ _ _
  · rfl

/-- Real-row base bytes retain all original column order and Boolean conventions. -/
theorem rowBase_words (ctx : Context) (hpos:ctx.Positive) (z : JetRun) (a : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a) (columns : List (Wire a)) :
    (rowBase ctx z a t row columns).words=
      (SemiprimeD1PacketEntryBits.rowBase ctx z a t row columns).words := by
  have hb:(SemiprimeD1JetAffineCoefficient.sumRuns ctx
      (columns.map (baseTerm ctx z a t row))).words=
      (SemiprimeD1JetAffineCoefficient.sumRuns ctx
        (columns.map (SemiprimeD1PacketEntryBits.baseTerm ctx z a t row))).words:=by
    apply sum_words_congr
    simp only [List.map_map]
    apply List.map_congr_left
    intro column _
    exact baseTerm_words ctx hpos z a t row column
  dsimp only [rowBase,SemiprimeD1PacketEntryBits.rowBase]
  split
  · exact hb
  · rw [signed_words,show
      (SemiprimeD1PacketEntryBits.signed ctx true
        (SemiprimeD1JetAffineCoefficient.sumRuns ctx (columns.map (baseTerm ctx z a t row)))).words=
      (SemiprimeD1PacketEntryBits.signed ctx true
        (SemiprimeD1JetAffineCoefficient.sumRuns ctx
          (columns.map (SemiprimeD1PacketEntryBits.baseTerm ctx z a t row)))).words from by
        dsimp only [SemiprimeD1PacketEntryBits.signed,multiply]
        simp only [ite_true]
        rw [hb]]

/-- Original gated coefficient bytes now come from the actual word-only mode. -/
theorem coefficient_words (ctx : Context) (hpos:ctx.Positive) (z : JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a)
    (item : SemiprimeD1PacketModeMask.Item) :
    (coefficient ctx z a i t row item).words=
      (SemiprimeD1PacketEntryBits.coefficient ctx z a i t row item).words := by
  dsimp only [coefficient,SemiprimeD1PacketEntryBits.coefficient]
  split
  · rw [signed_words]
    dsimp only [SemiprimeD1PacketEntryBits.signed,multiply]
    split <;> rw [SemiprimeD1JetWordModeBits.acquireOriginal_words ctx hpos]
  · rfl

/-- Acquired coefficient arrays preserve every original catalogue slot. -/
theorem coefficients_value (ctx : Context) (hpos:ctx.Positive) (z : JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a)
    (items : List SemiprimeD1PacketModeMask.Item) :
    (coefficients ctx z a i t row items).value=
      (SemiprimeD1PacketEntryBits.coefficients ctx z a i t row items).value := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    change (coefficient ctx z a i t row item).words::(coefficients ctx z a i t row items).value=_
    rw [coefficient_words ctx hpos,ih]
    rfl

/-- Each actual affine recipe is exactly the original requested-coefficient input. -/
theorem recipe_value (ctx : Context) (hpos:ctx.Positive) (z : JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a) (columns : List (Wire a))
    (items : List SemiprimeD1PacketModeMask.Item) :
    (recipe ctx z a i t row columns items).value=
      (SemiprimeD1PacketEntryBits.recipe ctx z a i t row columns items).value := by
  dsimp only [recipe,SemiprimeD1PacketEntryBits.recipe]
  rw [rowBase_words ctx hpos,coefficients_value ctx hpos]

/-- Real-row lists preserve original row order, multiplicity and exact recipe data. -/
theorem recipes_value (ctx : Context) (hpos:ctx.Positive) (z : JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (columns : List (Wire a))
    (items : List SemiprimeD1PacketModeMask.Item) (rows : List (Wire a)) :
    (recipes ctx z a i t columns items rows).value=
      (SemiprimeD1PacketEntryBits.recipes ctx z a i t columns items rows).value := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    change (recipe ctx z a i t row columns items).value::(recipes ctx z a i t columns items rows).value=_
    rw [recipe_value ctx hpos,ih]
    rfl

/-- The whole actual packet entry has original bytes, with its own retained report. -/
theorem evaluate_words {V : ℕ} (ctx : Context) (hpos:ctx.Positive) (z : JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (items : SemiprimeD1PacketModeMask.Cache)
    (endpoints : List (SemiprimeD1ChildGraph.Endpoint V)) (beta : List ℕ) (bits : List Bool) :
    (evaluate ctx z a i t items endpoints beta bits).words=
      (SemiprimeD1PacketEntryBits.evaluate ctx z a i t items endpoints beta bits).words := by
  dsimp only [evaluate,SemiprimeD1PacketEntryBits.evaluate,multiply]
  rw [recipes_value ctx hpos]

/-- Completed actual entry shape/width follows the final physical product. -/
theorem evaluate_good {V : ℕ} (ctx : Context) (z : JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (items : SemiprimeD1PacketModeMask.Cache)
    (endpoints : List (SemiprimeD1ChildGraph.Endpoint V)) (beta : List ℕ) (bits : List Bool) :
    SemiprimeD1JetAffineCoefficientBounds.Good ctx (evaluate ctx z a i t items endpoints beta bits).words :=
  SemiprimeD1JetAffineCoefficientBounds.mul_good _ _ _
/-- Every completed literal packet output is canonical in its current context. -/
theorem evaluate_canonical {V : ℕ} (ctx : Context) (z : JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (items : SemiprimeD1PacketModeMask.Cache)
    (endpoints : List (SemiprimeD1ChildGraph.Endpoint V)) (beta : List ℕ) (bits : List Bool) :
    SemiprimeD1TensorTables.GoodWords ctx (evaluate ctx z a i t items endpoints beta bits).words := by
  refine ⟨SemiprimeD1JetRingBits.mul_shape _ _ _,?_⟩
  intro w hw
  exact ⟨SemiprimeD1JetRingBits.mul_compact _ _ _ w hw,
    SemiprimeD1JetRingBits.mul_bounded _ _ _ w hw⟩
end RiemannGaussian.SemiprimeD1JetWordPacketEntryBits
