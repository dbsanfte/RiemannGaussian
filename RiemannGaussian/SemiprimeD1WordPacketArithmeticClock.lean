/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetWordPacketEntryBits
import RiemannGaussian.SemiprimeD1JetWordKernelBounds
import RiemannGaussian.SemiprimeD1PacketEntryValue
import RiemannGaussian.SemiprimeD1JetModeBitsBounds

/-! # Retained physical arithmetic in actual packet row construction
Canonical input shape is an original acquired-vector condition. All outputs
and arithmetic prefixes derive their own current width; no intermediate Fits
or entry-clock answer is a premise. Original word acquisition and every physical report are included; the native
small-index/digit and whole-address lowering boundaries remain explicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 140000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1WordPacketArithmeticClock
open SemiprimeD1JetAxes SemiprimeD1JetAffineCoefficient SemiprimeD1JetAffineCoefficientBounds
open SemiprimeD1JetWordPacketEntryBits SemiprimeD1PacketEntryInputs
open SemiprimeD1PacketEntryBits (borrow multiply)

/-- Actual fixed-width multijet multiplication budget. -/
def mulClock (ctx : Context) : ℕ :=
  SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank ctx.precision ctx.precision

/-- Actual fixed-width multijet addition budget. -/
def addClock (ctx : Context) : ℕ := addBudget ctx ctx.precision

/-- Actual literal unit acquisition budget. -/
def oneClock (ctx : Context) : ℕ := 9*ctx.precision+3*ctx.rank+8

/-- Both actual producer reports are retained by packet multiplication. -/
theorem multiply_clock (ctx : Context) (left right : JetRun)
    (hl : Good ctx left.words) (hr : Good ctx right.words) :
    (multiply ctx left right).clock ≤ left.clock+right.clock+mulClock ctx+3 := by
  have h := SemiprimeD1JetRingBounds.mul_clock ctx left.words right.words ctx.precision
    hl.1.le hr.1.le hl.2 hr.2
  exact Nat.add_le_add_right (Nat.add_le_add_left h (left.clock+right.clock)) 3

/-- Actual packet multiplication always produces canonical target shape/width. -/
theorem multiply_good (ctx : Context) (left right : JetRun) : Good ctx (multiply ctx left right).words :=
  mul_good ctx left.words right.words

/-- Sign cost includes the actual modular minus-one producer and copied positive case. -/
def signClock (ctx : Context) : ℕ := (12*ctx.precision*(ctx.precision+3)+13*ctx.precision+3*ctx.rank+27)+
  mulClock ctx+ctx.rank*(3*ctx.precision+4)+10

/-- Both physical sign branches preserve the actual acquired input shape. -/
theorem signed_good (ctx : Context) (negative : Bool) (value : JetRun) (hv : Good ctx value.words) :
    Good ctx (signed ctx negative value).words := by
  cases negative with
  | false => simpa only [signed,Bool.false_eq_true,ite_false,copyVector_value] using hv
  | true => exact multiply_good ctx _ _

/-- Every sign application pays its actual source report exactly as executed. -/
theorem signed_clock (ctx : Context) (negative : Bool) (value : JetRun) (hv : Good ctx value.words) :
    (signed ctx negative value).clock ≤ value.clock+signClock ctx := by
  have hi := SemiprimeD1JetWordSourceBits.constant_clock ctx ⟨true,[true]⟩
  simp only [List.length_cons,List.length_nil] at hi
  change (SemiprimeD1JetWordSourceBits.constant ctx ⟨true,[true]⟩).clock ≤
    12*ctx.precision*(ctx.precision+3)+13*ctx.precision+3*ctx.rank+27 at hi
  have hc := copyVector_clock_le value.words ctx.precision hv.2
  rw [hv.1] at hc
  have hm := multiply_clock ctx (SemiprimeD1JetWordSourceBits.constant ctx ⟨true,[true]⟩) value
    (SemiprimeD1JetWordSourceBits.constant_good _ _) hv
  cases negative with
  | false =>
    change value.clock+(copyVector value.words).2+3 ≤ _
    unfold signClock
    omega
  | true =>
    change (multiply ctx (SemiprimeD1JetWordSourceBits.constant ctx ⟨true,[true]⟩) value).clock ≤ _
    unfold signClock
    omega

/-- Original finite-grid base-entry bound at actual target precision. -/
def baseClock (ctx : Context) (a : ℕ) : ℕ :=
  SemiprimeD1JetWordKernelBounds.budget ctx ctx.precision a+ctx.rank+1

/-- Every actual real-row column contribution has intrinsic target shape. -/
theorem baseTerm_good (ctx : Context) (z : JetRun) (a : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row column : Wire a) :
    Good ctx (baseTerm ctx z a t row column).words := by
  dsimp only [baseTerm]
  split
  · exact SemiprimeD1JetWordModeBounds.base_good ctx _ a t row.slot column.slot
  · exact zero_good ctx

/-- Borrowed fresh input is actually canonical; no repeated producer cost is
invented for borrowing, while the outer table retains the producer separately. -/
theorem baseTerm_clock (ctx : Context) (z : JetRun) (hz : Good ctx z.words) (a : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row column : Wire a) :
    (baseTerm ctx z a t row column).clock ≤ baseClock ctx a := by
  have h := SemiprimeD1JetWordKernelBounds.acquireOriginal_clock ctx (borrow z) a t row.slot column.slot
    ctx.precision le_rfl hz.1.le hz.2
  dsimp only [baseTerm]
  split
  · change (SemiprimeD1JetWordKernelBits.acquireOriginal ctx (borrow z) a t row.slot column.slot).clock ≤ _
    dsimp only [borrow] at h
    simp only [Nat.zero_add] at h
    exact h.trans (by
      unfold baseClock
      omega)
  · change ctx.rank+1 ≤ _
    unfold baseClock
    omega

/-- Full real-row constant acquisition, including false-bit one-minus-base. -/
def rowBaseClock (ctx : Context) (a columns : ℕ) : ℕ :=
  columns*(baseClock ctx a+addClock ctx+3)+ctx.rank+1+
    oneClock ctx+signClock ctx+addClock ctx+5

/-- Row constants derive all intermediate shape/widths. -/
theorem rowBase_good (ctx : Context) (z : JetRun) (a : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a) (columns : List (Wire a)) :
    Good ctx (rowBase ctx z a t row columns).words := by
  dsimp only [rowBase]
  split
  · exact sumRuns_good ctx _
  · exact add_good ctx _ _

/-- Every actual column callback, sum prefix, literal unit and physical sign is retained. -/
theorem rowBase_clock (ctx : Context) (z : JetRun) (hz : Good ctx z.words) (a : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a) (columns : List (Wire a)) :
    (rowBase ctx z a t row columns).clock ≤ rowBaseClock ctx a columns.length := by
  let base := sumRuns ctx (columns.map (baseTerm ctx z a t row))
  have hbase := sumRuns_clock ctx (columns.map (baseTerm ctx z a t row)) (by
    intro x hx
    obtain ⟨column,_,rfl⟩ := List.mem_map.mp hx
    exact baseTerm_good ctx z a t row column)
  have hcallbacks : ((columns.map (baseTerm ctx z a t row)).map (fun x => x.clock)).sum ≤
      columns.length*baseClock ctx a := by
    clear hbase base
    induction columns with
    | nil => simp
    | cons c cs ih =>
      have hh := baseTerm_clock ctx z hz a t row c
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  simp only [List.length_map] at hbase
  have hb : base.clock ≤ columns.length*(baseClock ctx a+addClock ctx+3)+ctx.rank+1 := by
    have hsum := Nat.add_le_add_right (Nat.add_le_add_right hcallbacks
      (columns.length*(addBudget ctx ctx.precision+3))) (ctx.rank+1)
    exact hbase.trans (by dsimp only [addClock];nlinarith)
  have hu := SemiprimeD1JetPolynomialBitsBounds.one_clock ctx
  have hs := signed_clock ctx true base (sumRuns_good ctx _)
  have ha := SemiprimeD1JetRingBounds.add_clock ctx (one ctx).words (signed ctx true base).words
    ctx.precision (one_good ctx).1.le (signed_good ctx true base (sumRuns_good ctx _)).1.le
      (one_good ctx).2 (signed_good ctx true base (sumRuns_good ctx _)).2
  have hu' : (one ctx).clock ≤ oneClock ctx := hu
  have ha' : (SemiprimeD1JetRingBits.add ctx (one ctx).words (signed ctx true base).words).clock ≤ addClock ctx := ha
  dsimp only [rowBase]
  split
  · change base.clock ≤ _
    exact hb.trans (by unfold rowBaseClock;omega)
  · change (one ctx).clock+(signed ctx true base).clock+
      (SemiprimeD1JetRingBits.add ctx (one ctx).words (signed ctx true base).words).clock+5 ≤ _
    calc
      _ ≤ oneClock ctx+(base.clock+signClock ctx)+addClock ctx+5 :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hu' hs) ha') (le_refl 5)
      _ ≤ oneClock ctx+((columns.length*(baseClock ctx a+addClock ctx+3)+ctx.rank+1)+signClock ctx)+addClock ctx+5 := by
        exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left
          (Nat.add_le_add_right hb (signClock ctx)) (oneClock ctx)) (addClock ctx)) 5
      _ = _ := by unfold rowBaseClock;ring

end RiemannGaussian.SemiprimeD1WordPacketArithmeticClock
