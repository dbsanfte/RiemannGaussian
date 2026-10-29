/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketArithmeticClock

/-! # Actual packet source-mode powers and ordered product clocks
The unchanged global beta is read by the executed finite scans. Its acquired
numeric cap bounds the actual power loops; no requested source value is given.
-/
set_option autoImplicit false
set_option maxHeartbeats 140000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1PacketSourceClock
open SemiprimeD1JetAxes SemiprimeD1JetAffineCoefficient SemiprimeD1JetAffineCoefficientBounds
open SemiprimeD1PacketEntryBits SemiprimeD1PacketEntryInputs SemiprimeD1PacketArithmeticClock

/-- A finite read of an acquired bounded exponent list is bounded, including default0. -/
theorem read_le (beta : List ℕ) (index B : ℕ) (hb : ∀b∈beta,b ≤ B) :
    (SemiprimeD1AffineCoefficient.read 0 beta index).1 ≤ B := by
  induction beta generalizing index with
  | nil => exact Nat.zero_le _
  | cons b beta ih =>
    cases index with
    | zero => exact hb _ List.mem_cons_self
    | succ index => exact ih _ (fun x hx => hb _ (List.mem_cons_of_mem _ hx))

/-- Whole actual finite multijet power loop. -/
def powerClock (ctx : Context) (B : ℕ) : ℕ := B*(mulClock ctx+3)+oneClock ctx

/-- Actual power cost is monotone in its acquired exponent. -/
theorem power_clock (ctx : Context) (words : List (List Bool)) (hg : Good ctx words)
    (b B : ℕ) (hb : b ≤ B) :
    (SemiprimeD1JetPolynomialBits.power ctx words b).clock ≤ powerClock ctx B := by
  have h := SemiprimeD1JetPolynomialBitsBounds.power_clock ctx words b ctx.precision le_rfl hg.1.le hg.2
  have hm := Nat.mul_le_mul_right (mulClock ctx+3) hb
  unfold powerClock
  calc
    _ ≤ b*(mulClock ctx+3)+9*ctx.precision+3*ctx.rank+8 := h
    _ ≤ B*(mulClock ctx+3)+9*ctx.precision+3*ctx.rank+8 :=
      Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hm (9*ctx.precision)) (3*ctx.rank)) 8
    _ = _ := by unfold oneClock;ring

/-- Original index digits, literal scalar vector and actual finite power acquisition. -/
def sourceTermClock (ctx : Context) (a P : ℕ) : ℕ :=
  10*ctx.precision+5+(3*ctx.precision+3*ctx.rank+4)+powerClock ctx P+
    2^a+2^(a+1)+8+ctx.rank+1

/-- Every source-column contribution derives current target shape and width. -/
theorem sourceTerm_good (ctx : Context) (a : ℕ) (i : Fin a)
    (item : SemiprimeD1PacketModeMask.Item) (column : Wire a) :
    Good ctx (sourceTerm ctx a i item column).words := by
  dsimp only [sourceTerm]
  split
  · exact SemiprimeD1JetPolynomialBitsBounds.power_good _ _ _
  · exact zero_good _

/-- Every actually acquired source integer/power and literal zero branch is paid. -/
theorem sourceTerm_clock (ctx : Context) (a : ℕ) (i : Fin a)
    (item : SemiprimeD1PacketModeMask.Item) (column : Wire a) (P : ℕ) (hp : item.mode.order ≤ P) :
    (sourceTerm ctx a i item column).clock ≤ sourceTermClock ctx a P := by
  let index := SemiprimeD1JetPolynomialBits.magnitude ctx.precision (column.slot.val/2^(i.val+1))
  let scalar := SemiprimeD1JetPolynomialBits.scalar ctx index.bits
  have hm := SemiprimeD1JetPolynomialBitsBounds.magnitude_clock ctx.precision (column.slot.val/2^(i.val+1))
  have hw := SemiprimeD1JetPolynomialBitsBounds.magnitude_length ctx.precision (column.slot.val/2^(i.val+1))
  have hs := SemiprimeD1JetPolynomialBitsBounds.scalar_clock ctx index.bits
  have hg : Good ctx scalar.words :=
    ⟨SemiprimeD1JetPolynomialBitsBounds.scalar_shape _ _,
      SemiprimeD1JetPolynomialBitsBounds.scalar_bounded _ _ _ hw⟩
  have hpower := power_clock ctx scalar.words hg _ P hp
  have hslot : column.slot.val ≤ 2^a := column.slot.isLt.le
  have htiles : 2^(i.val+1) ≤ (2:ℕ)^(a+1) := Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right i.isLt.le 1)
  have hw' : index.bits.length ≤ ctx.precision := hw
  have hscalar : scalar.clock ≤ 3*ctx.precision+3*ctx.rank+4 := by
    rw [SemiprimeD1JetPolynomialBitsBounds.scalar_clock]
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hw') (3*ctx.rank)) 4
  dsimp only [sourceTerm]
  split
  · change index.clock+scalar.clock+(SemiprimeD1JetPolynomialBits.power ctx scalar.words item.mode.order).clock+
      column.slot.val+2^(i.val+1)+8 ≤ _
    have hi : index.clock=10*ctx.precision+5 := hm
    unfold sourceTermClock
    omega
  · change ctx.rank+1+column.slot.val+2^(i.val+1)+5 ≤ _
    unfold sourceTermClock
    omega

/-- Actual source-column sum and unchanged global-beta finite power. -/
def sourceFactorClock (ctx : Context) (a C P B T : ℕ) : ℕ :=
  3*T+1+C*(sourceTermClock ctx a P+addClock ctx+3)+ctx.rank+1+
    powerClock ctx B+6+oneClock ctx+4

/-- Both actual source-factor branches have derived current shape/width. -/
theorem sourceFactor_good (ctx : Context) (a : ℕ) (i : Fin a) (columns : List (Wire a))
    (beta : List ℕ) (index : ℕ) (item : SemiprimeD1PacketModeMask.Item) :
    Good ctx (sourceFactor ctx a i columns beta index item).words := by
  dsimp only [sourceFactor]
  split
  · exact SemiprimeD1JetPolynomialBitsBounds.power_good _ _ _
  · exact one_good _

/-- Physical source-factor acquisition reads the ORIGINAL global exponent and
retains every actual contributing column. -/
theorem sourceFactor_clock (ctx : Context) (a : ℕ) (i : Fin a) (columns : List (Wire a))
    (beta : List ℕ) (index : ℕ) (item : SemiprimeD1PacketModeMask.Item) (P B : ℕ)
    (hp : item.mode.order ≤ P) (hb : ∀b∈beta,b ≤ B) :
    (sourceFactor ctx a i columns beta index item).clock ≤
      sourceFactorClock ctx a columns.length P B beta.length := by
  let base := sumRuns ctx (columns.map (sourceTerm ctx a i item))
  have hread := SemiprimeD1AffineCoefficientBounds.read_work 0 beta index
  have hexponent := read_le beta index B hb
  have hsum := sumRuns_clock ctx (columns.map (sourceTerm ctx a i item)) (by
    intro x hx
    obtain ⟨column,_,rfl⟩ := List.mem_map.mp hx
    exact sourceTerm_good ctx a i item column)
  have hcallbacks : ((columns.map (sourceTerm ctx a i item)).map (fun x => x.clock)).sum ≤
      columns.length*sourceTermClock ctx a P := by
    clear hsum base
    induction columns with
    | nil => simp
    | cons c cs ih =>
      have hh := sourceTerm_clock ctx a i item c P hp
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  simp only [List.length_map] at hsum
  have hbase : base.clock ≤ columns.length*(sourceTermClock ctx a P+addClock ctx+3)+ctx.rank+1 := by
    have hh := Nat.add_le_add_right (Nat.add_le_add_right hcallbacks
      (columns.length*(addBudget ctx ctx.precision+3))) (ctx.rank+1)
    exact hsum.trans (by dsimp only [addClock];nlinarith)
  have hpower := power_clock ctx base.words (sumRuns_good ctx _)
    (SemiprimeD1AffineCoefficient.read 0 beta index).1 B hexponent
  have hu := SemiprimeD1JetPolynomialBitsBounds.one_clock ctx
  dsimp only [sourceFactor]
  split
  · change (SemiprimeD1AffineCoefficient.read 0 beta index).2+base.clock+
      (SemiprimeD1JetPolynomialBits.power ctx base.words (SemiprimeD1AffineCoefficient.read 0 beta index).1).clock+6 ≤ _
    unfold sourceFactorClock
    omega
  · change (one ctx).clock+4 ≤ _
    unfold sourceFactorClock oneClock
    omega

/-- Every actual ordered source-product prefix has intrinsic target shape/width. -/
theorem sourceProduct_good (ctx : Context) (a : ℕ) (i : Fin a) (columns : List (Wire a))
    (beta : List ℕ) (items : List SemiprimeD1PacketModeMask.Item) (index : ℕ) :
    Good ctx (sourceProduct ctx a i columns beta items index).words := by
  cases items with
  | nil => exact one_good _
  | cons item items => exact multiply_good _ _ _

/-- All physical source factors and multiplication prefixes are retained. -/
theorem sourceProduct_clock (ctx : Context) (a : ℕ) (i : Fin a) (columns : List (Wire a))
    (beta : List ℕ) (items : List SemiprimeD1PacketModeMask.Item) (index P B : ℕ)
    (hp : ∀item∈items,item.mode.order ≤ P) (hb : ∀b∈beta,b ≤ B) :
    (sourceProduct ctx a i columns beta items index).clock ≤
      items.length*(sourceFactorClock ctx a columns.length P B beta.length+mulClock ctx+3)+oneClock ctx := by
  induction items generalizing index with
  | nil =>
    simp only [sourceProduct,List.length_nil,Nat.zero_mul,Nat.zero_add]
    exact SemiprimeD1JetPolynomialBitsBounds.one_clock ctx
  | cons item items ih =>
    have hh := sourceFactor_clock ctx a i columns beta index item P B (hp _ List.mem_cons_self) hb
    have ht := ih (index+1) (fun x hx => hp x (List.mem_cons_of_mem _ hx))
    have hm := multiply_clock ctx (sourceFactor ctx a i columns beta index item)
      (sourceProduct ctx a i columns beta items (index+1))
      (sourceFactor_good _ _ _ _ _ _ _) (sourceProduct_good _ _ _ _ _ _ _)
    change (multiply ctx (sourceFactor ctx a i columns beta index item)
      (sourceProduct ctx a i columns beta items (index+1))).clock ≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

end RiemannGaussian.SemiprimeD1PacketSourceClock
