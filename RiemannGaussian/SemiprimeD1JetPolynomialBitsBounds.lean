/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetPolynomialBits
import RiemannGaussian.SemiprimeD1JetAffineCoefficientBounds

/-! # Actual polynomial-loop widths and retained concrete arithmetic clocks -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1JetPolynomialBitsBounds
open SemiprimeD1JetAxes SemiprimeD1JetPolynomialBits SemiprimeD1JetAffineCoefficientBounds

/-- Original magnitude acquisition pays every requested digit and trim cell. -/
theorem magnitude_clock (p n : ℕ) : (magnitude p n).clock=10*p+5 := by
  simp only [magnitude,SemiprimeEncodedRowSelection.digits_work,
    SemiprimeSourceCompactBits.trim_clock,SemiprimeEncodedRowSelection.digits_length]
  omega

/-- Acquired magnitude residues have intrinsic target precision width. -/
theorem magnitude_length (p n : ℕ) : (magnitude p n).bits.length≤p := by
  have h:=SemiprimeSourceCompactBits.trim_length (SemiprimeEncodedRowSelection.digits p n).bits
  simpa only [magnitude,SemiprimeEncodedRowSelection.digits_length] using h

/-- A literal scalar vector retains all physical source bits and actual rank. -/
theorem scalar_shape (ctx : Context) (bits : List Bool) : (scalar ctx bits).words.length=ctx.rank := by
  simp [scalar]

/-- Every allocated scalar coefficient is either its actual copied word or zero. -/
theorem scalar_bounded (ctx : Context) (bits : List Bool) (W : ℕ) (h : bits.length≤W) :
    ∀w∈(scalar ctx bits).words,w.length≤W := by
  intro w hw
  rcases List.mem_map.mp hw with ⟨i,_,rfl⟩
  split_ifs
  · simpa only [SemiprimeSourceCompactBits.copy_bits] using h
  · exact Nat.zero_le _

/-- Scalar allocation pays the actual source copy and dense zero-cell table. -/
theorem scalar_clock (ctx : Context) (bits : List Bool) :
    (scalar ctx bits).clock=3*bits.length+3*ctx.rank+4 := by
  simp only [scalar,SemiprimeSourceCompactBits.copy_clock]
  omega

/-- Every finite-power result has original physical target shape/width. -/
theorem power_good (ctx : Context) (z : List (List Bool)) (n : ℕ) :
    Good ctx (power ctx z n).words := by
  cases n with
  | zero => exact one_good ctx
  | succ n => exact mul_good _ _ _

/-- Every finite acquired product result has target shape/width. -/
theorem product_good (ctx : Context) (xs : List SemiprimeD1JetAffineCoefficient.JetRun) :
    Good ctx (product ctx xs).words := by
  cases xs with
  | nil => exact one_good ctx
  | cons x xs => exact mul_good _ _ _

/-- Every actual Horner prefix has derived target shape/width. -/
theorem horner_good (ctx : Context) (z : List (List Bool)) (cs : List (List Bool)) :
    Good ctx (horner ctx z cs).words := by
  cases cs with
  | nil => exact zero_good ctx
  | cons c cs => exact add_good _ _ _

/-- Unit allocation requires only the actual reduction and dense cell table. -/
theorem one_clock (ctx : Context) :
    (SemiprimeD1JetAffineCoefficient.one ctx).clock≤9*ctx.precision+3*ctx.rank+8 := by
  have h:=SemiprimeD1JetScalarBits.reduce_clock ctx.precision [true]
  change (SemiprimeD1JetScalarBits.reduce ctx.precision [true]).clock+3*ctx.rank+3≤_
  omega

/-- All actual finite-power arithmetic is bounded from original source shape/width. -/
theorem power_clock (ctx : Context) (z : List (List Bool)) (n W : ℕ)
    (hp : ctx.precision≤W) (hz : z.length≤ctx.rank) (hw : ∀w∈z,w.length≤W) :
    (power ctx z n).clock≤n*(SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+3)+
      9*ctx.precision+3*ctx.rank+8 := by
  induction n with
  | zero => simpa only [power,Nat.zero_mul,Nat.zero_add] using one_clock ctx
  | succ n ih =>
    have hg:=power_good ctx z n
    have hm:=SemiprimeD1JetRingBounds.mul_clock ctx z (power ctx z n).words W hz hg.1.le hw
      (fun w h=>(hg.2 w h).trans hp)
    change (power ctx z n).clock+(SemiprimeD1JetRingBits.mul ctx z (power ctx z n).words).clock+3≤_
    nlinarith

/-- Acquired-product accumulation retains every actual factor producer report once. -/
theorem product_clock (ctx : Context) (xs : List SemiprimeD1JetAffineCoefficient.JetRun) (W : ℕ)
    (hp : ctx.precision≤W)
    (hs : ∀x∈xs,x.words.length≤ctx.rank ∧ ∀w∈x.words,w.length≤W) :
    (product ctx xs).clock≤(xs.map (fun x=>x.clock)).sum+
      xs.length*(SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+3)+
      9*ctx.precision+3*ctx.rank+8 := by
  induction xs with
  | nil => simpa only [product,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.zero_add] using one_clock ctx
  | cons x xs ih =>
    have hh:=hs x List.mem_cons_self
    have ht:=product_good ctx xs
    have hi:=ih (fun y hy=>hs y (List.mem_cons_of_mem x hy))
    have hm:=SemiprimeD1JetRingBounds.mul_clock ctx x.words (product ctx xs).words W hh.1 ht.1.le hh.2
      (fun w h=>(ht.2 w h).trans hp)
    change x.clock+(product ctx xs).clock+
      (SemiprimeD1JetRingBits.mul ctx x.words (product ctx xs).words).clock+3≤_
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- Actual finite Horner acquisition has a fixed polynomial report per original coefficient. -/
theorem horner_clock (ctx : Context) (z : List (List Bool)) (cs : List (List Bool)) (W : ℕ)
    (hp : ctx.precision≤W) (hz : z.length≤ctx.rank) (hw : ∀w∈z,w.length≤W)
    (hc : ∀c∈cs,c.length≤W) :
    (horner ctx z cs).clock≤cs.length*(3*W+3*ctx.rank+
      SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+
      addBudget ctx W+12)+ctx.rank+1 := by
  induction cs with
  | nil => simp [horner,SemiprimeD1JetAffineCoefficient.zero]
  | cons c cs ih =>
    have hcc:=hc c List.mem_cons_self
    have hi:=ih (fun x hx=>hc x (List.mem_cons_of_mem c hx))
    have ht:=horner_good ctx z cs
    have hm:=SemiprimeD1JetRingBounds.mul_clock ctx z (horner ctx z cs).words W hz ht.1.le hw
      (fun w h=>(ht.2 w h).trans hp)
    have hg:=mul_good ctx z (horner ctx z cs).words
    have ha:=SemiprimeD1JetRingBounds.add_clock ctx (scalar ctx c).words
      (SemiprimeD1JetRingBits.mul ctx z (horner ctx z cs).words).words W
      (scalar_shape ctx c).le hg.1.le (scalar_bounded ctx c W hcc)
      (fun w h=>(hg.2 w h).trans hp)
    have hsc:=scalar_clock ctx c
    change (horner ctx z cs).clock+(scalar ctx c).clock+
      (SemiprimeD1JetRingBits.mul ctx z (horner ctx z cs).words).clock+
      (SemiprimeD1JetRingBits.add ctx (scalar ctx c).words
        (SemiprimeD1JetRingBits.mul ctx z (horner ctx z cs).words).words).clock+5≤_
    simp only [List.length_cons]
    unfold addBudget at hi ⊢
    nlinarith

end RiemannGaussian.SemiprimeD1JetPolynomialBitsBounds
