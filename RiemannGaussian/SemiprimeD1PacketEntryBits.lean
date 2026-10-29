/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketModeMask
import RiemannGaussian.SemiprimeD1PacketEntryInputs
import RiemannGaussian.SemiprimeD1JetKernelBits
import RiemannGaussian.SemiprimeD1JetModeBits
import RiemannGaussian.SemiprimeD1TensorTables

/-! # Concrete packet row recipes and eager packet tables
The actual child bucket supplies every row/column bit and orientation slot.
Global beta is restricted to this packet's target modes before coefficient
extraction. Source factors use the original beta. No old tensor evaluator,
mode-coefficient callback, or semantic ring value appears on the runtime path.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1PacketEntryBits
open SemiprimeD1JetAxes SemiprimeD1PacketEntryInputs
open SemiprimeD1JetAffineCoefficient (JetRun Row)

/-- Borrow an already cached physical jet without recounting its producer. -/
def borrow (value : JetRun) : JetRun := ⟨value.words,0⟩

/-- Concrete product retaining both actual producer reports exactly once. -/
def multiply (ctx : Context) (left right : JetRun) : JetRun :=
  let out := SemiprimeD1JetRingBits.mul ctx left.words right.words
  ⟨out.words,left.clock+right.clock+out.clock+3⟩

/-- Literal sign application; negative uses the actual acquired modular minus one. -/
def signed (ctx : Context) (negative : Bool) (value : JetRun) : JetRun :=
  if negative then multiply ctx (SemiprimeD1JetKernelBits.integerVector ctx (-1)) value
  else
    let out := copyVector value.words
    ⟨out.1,value.clock+out.2+3⟩

/-- One actual local-column contribution to a real row. -/
def baseTerm (ctx : Context) (z : JetRun) (a : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row column : Wire a) : JetRun :=
  if column.bit then SemiprimeD1JetKernelBits.acquireOriginal ctx (borrow z) a t row.slot column.slot
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

/-- Acquire the two original finite indices and compare their actual ith Boolean bits. -/
def sameBit (x y i : ℕ) : SemiprimeMaterializedWords.Run Bool :=
  let xb := SemiprimeSourceHistogramPortKeys.encodeKey x
  let yb := SemiprimeSourceHistogramPortKeys.encodeKey y
  let left := SemiprimeD1ModeRoutingBits.readBit xb.bits i
  let right := SemiprimeD1ModeRoutingBits.readBit yb.bits i
  ⟨left.value==right.value,xb.clock+yb.clock+left.work+right.work+5⟩

/-- The bit test is executed from acquired index bytes, not a supplied branch answer. -/
theorem sameBit_value (x y i : ℕ) : (sameBit x y i).value=(x.testBit i == y.testBit i) := by
  simp only [sameBit,SemiprimeD1ModeRoutingTile.readBit_testBit,
    SemiprimeSourceHistogramPortKeys.encodeKey_value]

/-- Actual signed crossing mode. A physical same-bit test also guards the original
odd-unit mode supplier, rather than assuming that bit relation as advice. -/
def coefficient (ctx : Context) (z : JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a)
    (item : SemiprimeD1PacketModeMask.Item) : JetRun :=
  let tile : Fin (2^a) := ⟨item.tile%2^a,Nat.mod_lt _ (by positivity)⟩
  let test := sameBit row.slot.val tile.val i.val
  if item.inPacket && item.targetHere && !item.sourceHere && test.value then
    let mode := SemiprimeD1JetModeBits.acquireOriginal ctx (borrow z) a i.val item.mode.order t row.slot tile
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

/-- Actual source-tile column contribution `j^order * X`, with j acquired from
this literal slot; no native power or supplied ring coefficient is used. -/
def sourceTerm (ctx : Context) (a : ℕ) (i : Fin a)
    (item : SemiprimeD1PacketModeMask.Item) (column : Wire a) : JetRun :=
  let tiles := 2^(i.val+1)
  if column.bit && (column.slot.val%tiles == item.tile) then
    let index := SemiprimeD1JetPolynomialBits.magnitude ctx.precision (column.slot.val/tiles)
    let scalar := SemiprimeD1JetPolynomialBits.scalar ctx index.bits
    let out := SemiprimeD1JetPolynomialBits.power ctx scalar.words item.mode.order
    ⟨out.words,index.clock+scalar.clock+out.clock+column.slot.val+tiles+8⟩
  else
    let out := SemiprimeD1JetAffineCoefficient.zero ctx
    ⟨out.words,out.clock+column.slot.val+tiles+5⟩

/-- One source mode factor uses the ORIGINAL global exponent, including 0^0=1. -/
def sourceFactor (ctx : Context) (a : ℕ) (i : Fin a) (columns : List (Wire a))
    (beta : List ℕ) (index : ℕ) (item : SemiprimeD1PacketModeMask.Item) : JetRun :=
  if item.inPacket && item.sourceHere then
    let exponent := SemiprimeD1AffineCoefficient.read 0 beta index
    let base := SemiprimeD1JetAffineCoefficient.sumRuns ctx (columns.map (sourceTerm ctx a i item))
    let out := SemiprimeD1JetPolynomialBits.power ctx base.words exponent.1
    ⟨out.words,exponent.2+base.clock+out.clock+6⟩
  else
    let out := SemiprimeD1JetAffineCoefficient.one ctx
    ⟨out.words,out.clock+4⟩

/-- Concrete ordered source-mode product, with all actual factors retained. -/
def sourceProduct (ctx : Context) (a : ℕ) (i : Fin a) (columns : List (Wire a))
    (beta : List ℕ) : List SemiprimeD1PacketModeMask.Item→ℕ→JetRun
  | [],_ => SemiprimeD1JetAffineCoefficient.one ctx
  | item::items,index =>
    let head := sourceFactor ctx a i columns beta index item
    let tail := sourceProduct ctx a i columns beta items (index+1)
    multiply ctx head tail

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

end RiemannGaussian.SemiprimeD1PacketEntryBits
