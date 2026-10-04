/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitGeometricEvaluation

/-!
# Linear Boolean arithmetic for an exact Fermat-ring transform

Canonical addition and subtraction use actual carry and borrow circuits,
with no quotient/remainder routine. A physical template constructs the
modulus `2^K+1`; splitting at its K cells reduces a bounded word by the
identity `2^K = -1`. Structural shifts and Boolean halving supply the
cheap arithmetic needed by an exact transform over this composite ring.
These are transform primitives, not an FFT or a fast multiplication
recurrence, and do not close the original varying-seed acquisition gap.
-/

namespace RiemannGaussian.SemiprimeBitFermatArithmetic

open SemiprimeBitArithmetic SemiprimeBitDivision
open scoped BigOperators

/-- Retains both carry addition and the actual comparison/subtraction,
including the copied canonical output and every primitive charge. -/
structure ResidueAddReport where
  /-- Full Boolean sum, including a possible terminal carry. -/
  sum : BitReport
  /-- Actual comparison with, and subtraction of, the modulus. -/
  reduction : SubReport
  /-- Chosen residue copied to the modulus physical width. -/
  output : BitReport
  /-- Sum of every executed primitive clock and selection tests. -/
  clock : ℕ

/-- Canonical residues sum to less than twice the modulus, so one actual
borrow comparison chooses the unreduced sum or a single subtraction.
Both reports are retained; no decoded value controls the branch. -/
def residueAddBits (modulus xs ys : List Bool) : ResidueAddReport :=
  let sum := addBits xs ys false
  let reduction := subBits sum.bits modulus false
  let output := fitBits
    (if reduction.borrow=true then sum.bits else reduction.result.bits) modulus
  ⟨sum,reduction,output,bitCost sum+bitCost reduction.result+bitCost output+6⟩

/-- The copied output has precisely the literal modulus width, also
when input words contain high zero padding. -/
theorem residueAddBits_width (modulus xs ys : List Bool) :
    (residueAddBits modulus xs ys).output.bits.length=modulus.length := by
  exact (fitBits_counts _ _).1

/-- One paid carry/borrow correction gives the exact canonical sum for
every positive modulus, including composite ones. -/
theorem residueAddBits_exact {modulus xs ys : List Bool}
    (hx : bitValue xs<bitValue modulus)
    (hy : bitValue ys<bitValue modulus) :
    bitValue (residueAddBits modulus xs ys).output.bits=
      (bitValue xs+bitValue ys)%bitValue modulus ∧
    bitValue (residueAddBits modulus xs ys).output.bits<bitValue modulus := by
  have hs := addBits_correct xs ys false
  simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] at hs
  have hwidth := bitValue_lt_width modulus
  unfold residueAddBits
  dsimp only
  split
  · rename_i hb
    have hsum := (subBits_borrow_iff (addBits xs ys false).bits modulus false).mp hb
    simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] at hsum
    rw [fitBits_value (hsum.trans hwidth),hs,Nat.mod_eq_of_lt (by omega)]
    exact ⟨rfl,by omega⟩
  · rename_i hb
    have hborrow : (subBits (addBits xs ys false).bits modulus false).borrow=false := by
      cases h : (subBits (addBits xs ys false).bits modulus false).borrow with
      | false => rfl
      | true => exact False.elim (hb h)
    have hd := subBits_difference hborrow
    have hsum : bitValue modulus≤bitValue (addBits xs ys false).bits := by
      have hn := (subBits_borrow_iff (addBits xs ys false).bits modulus false).not.mp hb
      simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] at hn
      omega
    have hsmall : bitValue (subBits (addBits xs ys false).bits modulus false).result.bits<
        bitValue modulus := by omega
    have he : bitValue xs+bitValue ys=
        bitValue (subBits (addBits xs ys false).bits modulus false).result.bits+
          bitValue modulus := by omega
    rw [fitBits_value (hsmall.trans hwidth),he,Nat.add_mod,Nat.mod_self,Nat.add_zero,
      Nat.mod_mod,Nat.mod_eq_of_lt hsmall]
    exact ⟨rfl,hsmall⟩

/-- The exact natural canonical sum is also the literal ring sum; no
primality, unit or separation premise is needed. -/
theorem residueAddBits_cast {modulus xs ys : List Bool}
    (hx : bitValue xs<bitValue modulus)
    (hy : bitValue ys<bitValue modulus) :
    (bitValue (residueAddBits modulus xs ys).output.bits : ZMod (bitValue modulus))=
      (bitValue xs : ZMod (bitValue modulus))+(bitValue ys : ZMod (bitValue modulus)) := by
  rw [(residueAddBits_exact hx hy).1,ZMod.natCast_mod,Nat.cast_add]

/-- Every physical carry, comparison, correction and output copy is
linear in W. The sum's possible extra bit is charged at W+1. -/
theorem residueAddBits_cost {modulus xs ys : List Bool} {W : ℕ}
    (hm : modulus.length≤W) (hx : xs.length≤W) (hy : ys.length≤W) :
    (residueAddBits modulus xs ys).clock≤27*W+25 := by
  have ha := addBits_cost xs ys false
  have hl := (addBits_counts xs ys false).2.2.2.2
  have hs := subBits_cost (addBits xs ys false).bits modulus false
  have hf := fitBits_cost
    (if (subBits (addBits xs ys false).bits modulus false).borrow=true
      then (addBits xs ys false).bits
      else (subBits (addBits xs ys false).bits modulus false).result.bits) modulus
  dsimp only [residueAddBits]
  omega

/-- Keeps both directed differences and the modulus correction, so the
underflow branch is fully computed and fully charged. -/
structure ResidueSubReport where
  /-- Original directed subtraction and its actual final borrow. -/
  direct : SubReport
  /-- Reverse subtraction, used to express a positive deficit. -/
  reverse : SubReport
  /-- Modulus minus the computed deficit. -/
  correction : SubReport
  /-- Chosen canonical output, copied to the modulus width. -/
  output : BitReport
  /-- All three subtractors, output copy and selection tests. -/
  clock : ℕ

/-- Correct canonical subtraction without division: on underflow use
`M-(y-x)`. The selector reads the computed original borrow bit. -/
def residueSubBits (modulus xs ys : List Bool) : ResidueSubReport :=
  let direct := subBits xs ys false
  let reverse := subBits ys xs false
  let correction := subBits modulus reverse.result.bits false
  let output := fitBits
    (if direct.borrow=true then correction.result.bits else direct.result.bits) modulus
  ⟨direct,reverse,correction,output,
    bitCost direct.result+bitCost reverse.result+bitCost correction.result+
      bitCost output+8⟩

/-- Subtraction always returns the literal modulus physical width. -/
theorem residueSubBits_width (modulus xs ys : List Bool) :
    (residueSubBits modulus xs ys).output.bits.length=modulus.length := by
  exact (fitBits_counts _ _).1

/-- Canonical subtraction keeps its exact unsigned equation with the
computed borrow, including equal residues and zero inputs. -/
theorem residueSubBits_exact {modulus xs ys : List Bool}
    (hx : bitValue xs<bitValue modulus)
    (hy : bitValue ys<bitValue modulus) :
    bitValue (residueSubBits modulus xs ys).output.bits<bitValue modulus ∧
    bitValue (residueSubBits modulus xs ys).output.bits+bitValue ys=
      bitValue xs+bitValue modulus*bitNat (subBits xs ys false).borrow := by
  have hwidth := bitValue_lt_width modulus
  unfold residueSubBits
  dsimp only
  split
  · rename_i hb
    have hlt := (subBits_borrow_iff xs ys false).mp hb
    simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] at hlt
    have hrb : (subBits ys xs false).borrow=false := by
      have hn : ¬(subBits ys xs false).borrow=true := by
        rw [subBits_borrow_iff]
        simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero]
        omega
      cases h : (subBits ys xs false).borrow with
      | false => rfl
      | true => exact False.elim (hn h)
    have hr := subBits_difference hrb
    have hcb : (subBits modulus (subBits ys xs false).result.bits false).borrow=false := by
      have hn : ¬(subBits modulus (subBits ys xs false).result.bits false).borrow=true := by
        rw [subBits_borrow_iff]
        simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero]
        omega
      cases h : (subBits modulus (subBits ys xs false).result.bits false).borrow with
      | false => rfl
      | true => exact False.elim (hn h)
    have hc := subBits_difference hcb
    have hcsmall : bitValue (subBits modulus (subBits ys xs false).result.bits false).result.bits<
        bitValue modulus := by omega
    rw [fitBits_value (hcsmall.trans hwidth)]
    simp only [hb,bitNat,if_true,Nat.mul_one]
    exact ⟨hcsmall,by omega⟩
  · rename_i hb
    have hdb : (subBits xs ys false).borrow=false := by
      cases h : (subBits xs ys false).borrow with
      | false => rfl
      | true => exact False.elim (hb h)
    have hd := subBits_difference hdb
    have hge : bitValue ys≤bitValue xs := by
      have hn := (subBits_borrow_iff xs ys false).not.mp hb
      simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] at hn
      omega
    have hdsmall : bitValue (subBits xs ys false).result.bits<bitValue modulus := by omega
    rw [fitBits_value (hdsmall.trans hwidth)]
    simp only [hdb,bitNat,Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero]
    exact ⟨hdsmall,by omega⟩

/-- The unsigned borrow equation yields the original ring difference
over any positive modulus, without an inverse or primality assumption. -/
theorem residueSubBits_cast {modulus xs ys : List Bool}
    (hx : bitValue xs<bitValue modulus)
    (hy : bitValue ys<bitValue modulus) :
    (bitValue (residueSubBits modulus xs ys).output.bits : ZMod (bitValue modulus))=
      (bitValue xs : ZMod (bitValue modulus))-(bitValue ys : ZMod (bitValue modulus)) := by
  have hc := congrArg (fun a : ℕ => (a : ZMod (bitValue modulus)))
    (residueSubBits_exact hx hy).2
  simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,add_zero] at hc
  exact eq_sub_iff_add_eq.mpr hc

/-- All three actually executed subtractors and the canonical copy
have a linear clock, including unused reverse/correction computations. -/
theorem residueSubBits_cost {modulus xs ys : List Bool} {W : ℕ}
    (hm : modulus.length≤W) (hx : xs.length≤W) (hy : ys.length≤W) :
    (residueSubBits modulus xs ys).clock≤40*W+15 := by
  have hd := subBits_cost xs ys false
  have hr := subBits_cost ys xs false
  have hl := (subBits_counts ys xs false).2.2.2.2
  have hc := subBits_cost modulus (subBits ys xs false).result.bits false
  have hf := fitBits_cost
    (if (subBits xs ys false).borrow=true
      then (subBits modulus (subBits ys xs false).result.bits false).result.bits
      else (subBits xs ys false).result.bits) modulus
  dsimp only [residueSubBits]
  omega

/-- Constructs a high true cell above one low false cell per physical
template cell, without a decoded exponent or a native power. -/
def powerTemplateBits : List Bool→BitReport
  | [] => ⟨[true],0,0,1,1⟩
  | _::tail =>
    let child := powerTemplateBits tail
    ⟨false::child.bits,child.gates,child.reads+1,child.writes+1,child.tests+1⟩

/-- The physical one-hot word represents the exact template power. -/
theorem powerTemplateBits_exact (template : List Bool) :
    bitValue (powerTemplateBits template).bits=2^template.length ∧
    (powerTemplateBits template).bits.length=template.length+1 ∧
    bitCost (powerTemplateBits template)=3*template.length+2 := by
  induction template with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons b tail ih =>
    simp only [powerTemplateBits,bitValue,bitNat,Bool.false_eq_true,if_false,
      Nat.zero_add,List.length_cons,pow_succ,bitCost] at ih ⊢
    constructor
    · rw [ih.1]; ring
    · exact ⟨by omega,by omega⟩

/-- Builds `2^K+1` from the K-cell template. Empty templates have the
actual exceptional word for two; transform statements require K>=1. -/
def fermatModulusBits (template : List Bool) : BitReport :=
  match template with
  | [] => ⟨[false,true],0,0,2,1⟩
  | _::tail =>
    let high := powerTemplateBits tail
    ⟨true::high.bits,high.gates,high.reads+1,high.writes+1,high.tests+1⟩

/-- Every constructed modulus has the stated exact Fermat value. -/
theorem fermatModulusBits_value (template : List Bool) :
    bitValue (fermatModulusBits template).bits=2^template.length+1 := by
  cases template with
  | nil => rfl
  | cons b tail =>
    simp only [fermatModulusBits,bitValue,bitNat,if_true,List.length_cons,
      (powerTemplateBits_exact tail).1,pow_succ]
    ring

/-- For nonempty templates the modulus needs K+1 actual cells; its
construction and every template visit have a linear primitive clock. -/
theorem fermatModulusBits_width_cost {template : List Bool}
    (hK : 0<template.length) :
    (fermatModulusBits template).bits.length=template.length+1 ∧
    bitCost (fermatModulusBits template)=3*template.length+2 := by
  cases template with
  | nil => simp only [List.length_nil] at hK; omega
  | cons b tail =>
    have hp := powerTemplateBits_exact tail
    dsimp only [fermatModulusBits,List.length_cons,bitCost] at hp ⊢
    exact ⟨by omega,by omega⟩

/-- Actual copied/padded low cells and the untouched high suffix. The
suffix is a real input-list reference, not a decoded quotient. -/
structure TemplateSplitReport where
  /-- Precisely one output cell per physical split-template cell. -/
  low : List Bool
  /-- Literal high input suffix after the visited cells. -/
  high : List Bool
  /-- All input/template tests, bit reads and new low cells. -/
  clock : ℕ

/-- Splits at a physical template, copying/padding the low word and
retaining the high suffix. No integer length controls the data path. -/
def splitTemplateBits : List Bool→List Bool→TemplateSplitReport
  | xs,[] => ⟨[],xs,1⟩
  | [],_::tail =>
    let child := splitTemplateBits [] tail
    ⟨false::child.low,child.high,child.clock+4⟩
  | x::xs,_::tail =>
    let child := splitTemplateBits xs tail
    ⟨x::child.low,child.high,child.clock+5⟩

/-- The literal split satisfies the exact radix decomposition, with
zero padding and arbitrary high input cells retained. -/
theorem splitTemplateBits_exact (xs template : List Bool) :
    bitValue xs=bitValue (splitTemplateBits xs template).low+
      2^template.length*bitValue (splitTemplateBits xs template).high ∧
    (splitTemplateBits xs template).low.length=template.length ∧
    (splitTemplateBits xs template).high.length=xs.length-template.length ∧
    (splitTemplateBits xs template).clock≤5*template.length+1 := by
  induction template generalizing xs with
  | nil => simp only [splitTemplateBits,bitValue,List.length_nil,pow_zero,Nat.one_mul,
      Nat.zero_add,Nat.sub_zero,Nat.mul_zero,le_refl,and_self]
  | cons b tail ih =>
    cases xs with
    | nil =>
      have hc := ih []
      simp only [splitTemplateBits,bitValue,bitNat,Bool.false_eq_true,if_false,
        List.length_cons,List.length_nil,pow_succ] at hc ⊢
      exact ⟨by nlinarith,by omega,by omega,by omega⟩
    | cons x xs =>
      have hc := ih xs
      simp only [splitTemplateBits,bitValue,List.length_cons,pow_succ] at hc ⊢
      exact ⟨by nlinarith,by omega,by omega,by omega⟩

/-- The Fermat ring's high radix is exactly minus one. This does not
assume that `2^K+1` is prime. -/
theorem fermat_radix (K : ℕ) :
    ((2^K : ℕ) : ZMod (2^K+1))= -1 := by
  have hz := ZMod.natCast_self (2^K+1)
  rw [Nat.cast_add,Nat.cast_one] at hz
  exact eq_neg_of_add_eq_zero_left hz

/-- Actual constructed modulus, literal split, both fitted operands and
the full canonical subtraction used for bounded Fermat reduction. -/
structure FermatReductionReport where
  /-- Modulus constructed from the original physical template. -/
  modulus : BitReport
  /-- Actual low-word copy and retained high suffix. -/
  split : TemplateSplitReport
  /-- Low operand fitted to the constructed modulus width. -/
  low : BitReport
  /-- High operand fitted to the constructed modulus width. -/
  high : BitReport
  /-- Executed canonical difference, retaining all borrow work. -/
  difference : ResidueSubReport
  /-- Every construction, split, fitting and correction primitive. -/
  clock : ℕ

/-- Reduces a word bounded by `(2^K)^2` via the actual low minus high
words. The bound is a correctness premise, never executable advice.
No native division or generic Boolean division is called. -/
def fermatReduceBits (template xs : List Bool) : FermatReductionReport :=
  let modulus := fermatModulusBits template
  let split := splitTemplateBits xs template
  let low := fitBits split.low modulus.bits
  let high := fitBits split.high modulus.bits
  let difference := residueSubBits modulus.bits low.bits high.bits
  ⟨modulus,split,low,high,difference,
    bitCost modulus+split.clock+bitCost low+bitCost high+difference.clock+12⟩

/-- Bounded reduction returns the exact canonical remainder. The high
word's value is proved small before paid fitting, so no significant
high cell is silently discarded. -/
theorem fermatReduceBits_exact {template xs : List Bool}
    (hK : 0<template.length) (hx : bitValue xs≤(2^template.length)^2) :
    bitValue (fermatReduceBits template xs).difference.output.bits=
      bitValue xs%(2^template.length+1) ∧
    bitValue (fermatReduceBits template xs).difference.output.bits<2^template.length+1 := by
  have hs := splitTemplateBits_exact xs template
  have hp : 0<2^template.length := by positivity
  have hlo := bitValue_lt_width (splitTemplateBits xs template).low
  rw [hs.2.1] at hlo
  have hhi : bitValue (splitTemplateBits xs template).high≤2^template.length := by
    nlinarith [Nat.zero_le (bitValue (splitTemplateBits xs template).low)]
  have hm := fermatModulusBits_value template
  have hw := (fermatModulusBits_width_cost hK).1
  have hmw := bitValue_lt_width (fermatModulusBits template).bits
  rw [hm,hw] at hmw
  have hlfit : bitValue
      (fitBits (splitTemplateBits xs template).low (fermatModulusBits template).bits).bits=
        bitValue (splitTemplateBits xs template).low :=
    fitBits_value (by rw [hw]; omega)
  have hhfit : bitValue
      (fitBits (splitTemplateBits xs template).high (fermatModulusBits template).bits).bits=
        bitValue (splitTemplateBits xs template).high :=
    fitBits_value (by rw [hw]; omega)
  have hlcanon : bitValue
      (fitBits (splitTemplateBits xs template).low (fermatModulusBits template).bits).bits<
        bitValue (fermatModulusBits template).bits := by rw [hlfit,hm]; omega
  have hhcanon : bitValue
      (fitBits (splitTemplateBits xs template).high (fermatModulusBits template).bits).bits<
        bitValue (fermatModulusBits template).bits := by rw [hhfit,hm]; omega
  have hsmall := (residueSubBits_exact hlcanon hhcanon).1
  have hcast := residueSubBits_cast hlcanon hhcanon
  rw [hm,hlfit,hhfit] at hcast
  have hsplit := congrArg (fun a : ℕ => (a : ZMod (2^template.length+1))) hs.1
  simp only [Nat.cast_add,Nat.cast_mul,fermat_radix,neg_one_mul,←sub_eq_add_neg] at hsplit
  have hout : (bitValue (fermatReduceBits template xs).difference.output.bits :
      ZMod (2^template.length+1))=(bitValue xs : ZMod (2^template.length+1)) := by
    exact hcast.trans hsplit.symm
  change bitValue (fermatReduceBits template xs).difference.output.bits<
    bitValue (fermatModulusBits template).bits at hsmall
  rw [hm] at hsmall
  have hval := congrArg ZMod.val hout
  rw [ZMod.val_natCast_of_lt hsmall,ZMod.val_natCast] at hval
  exact ⟨hval,hsmall⟩

/-- The reduction's ring value is exactly its raw input, including raw
products equal to `(2^K)^2`. -/
theorem fermatReduceBits_cast {template xs : List Bool}
    (hK : 0<template.length) (hx : bitValue xs≤(2^template.length)^2) :
    (bitValue (fermatReduceBits template xs).difference.output.bits : ZMod (2^template.length+1))=
      (bitValue xs : ZMod (2^template.length+1)) := by
  rw [(fermatReduceBits_exact hK hx).1,ZMod.natCast_mod]

/-- The full constructed reduction has a linear primitive clock and
fixed output width. Arbitrarily padded high inputs do not require a
scan of unvisited suffix cells; fitting is explicitly paid. -/
theorem fermatReduceBits_width_cost {template xs : List Bool}
    (hK : 0<template.length) :
    (fermatReduceBits template xs).difference.output.bits.length=template.length+1 ∧
    (fermatReduceBits template xs).clock≤56*template.length+80 := by
  have hm := fermatModulusBits_width_cost hK
  have hs := (splitTemplateBits_exact xs template).2.2.2
  have hl := fitBits_counts (splitTemplateBits xs template).low (fermatModulusBits template).bits
  have hh := fitBits_counts (splitTemplateBits xs template).high (fermatModulusBits template).bits
  have hlf := fitBits_cost (splitTemplateBits xs template).low (fermatModulusBits template).bits
  have hhf := fitBits_cost (splitTemplateBits xs template).high (fermatModulusBits template).bits
  have hd := residueSubBits_cost (W:=template.length+1)
    (modulus:=(fermatModulusBits template).bits)
    (xs:=(fitBits (splitTemplateBits xs template).low (fermatModulusBits template).bits).bits)
    (ys:=(fitBits (splitTemplateBits xs template).high (fermatModulusBits template).bits).bits)
    (by omega) (by omega) (by omega)
  constructor
  · exact (residueSubBits_width _ _ _).trans hm.1
  · dsimp only [fermatReduceBits]
    omega

/-- Physically prepends one false bit per offset-template cell. The
unshifted input is shared at the end, and every new bit is charged. -/
def shiftTemplateBits : List Bool→List Bool→BitReport
  | [],xs => ⟨xs,0,0,0,1⟩
  | _::tail,xs =>
    let child := shiftTemplateBits tail xs
    ⟨false::child.bits,child.gates,child.reads+1,child.writes+1,child.tests+1⟩

/-- The literal shifted word has its exact power-of-two value, width
and complete physical-template traversal clock. -/
theorem shiftTemplateBits_exact (offset xs : List Bool) :
    bitValue (shiftTemplateBits offset xs).bits=2^offset.length*bitValue xs ∧
    (shiftTemplateBits offset xs).bits.length=offset.length+xs.length ∧
    bitCost (shiftTemplateBits offset xs)=3*offset.length+1 := by
  induction offset with
  | nil => simp only [shiftTemplateBits,List.length_nil,pow_zero,Nat.one_mul,
      Nat.zero_add,bitCost,Nat.add_zero,Nat.mul_zero,and_self]
  | cons b tail ih =>
    simp only [shiftTemplateBits,bitValue,bitNat,Bool.false_eq_true,if_false,
      Nat.zero_add,List.length_cons,pow_succ,bitCost] at ih ⊢
    exact ⟨by rw [ih.1]; ring,by omega,by omega⟩

/-- Retained actual shift and actual Fermat reduction of the shifted
word, with their complete composed primitive clock. -/
structure FermatShiftReport where
  /-- Actual prepended Boolean cells, rather than a native exponent. -/
  shifted : BitReport
  /-- Actual bounded reduction of that computed word. -/
  reduction : FermatReductionReport
  /-- Every shift and reduction primitive and wrapper test. -/
  clock : ℕ

/-- Cheap multiplication by a power of two, controlled by a physical
offset template. Correctness uses offset width at most K. -/
def fermatShiftBits (template offset xs : List Bool) : FermatShiftReport :=
  let shifted := shiftTemplateBits offset xs
  let reduction := fermatReduceBits template shifted.bits
  ⟨shifted,reduction,bitCost shifted+reduction.clock+4⟩

/-- The shifted canonical output is exactly multiplication by `2^t`
in the composite Fermat ring, including the negating boundary t=K. -/
theorem fermatShiftBits_exact {template offset xs : List Bool}
    (hK : 0<template.length) (ht : offset.length≤template.length)
    (hx : bitValue xs<2^template.length+1) :
    (bitValue (fermatShiftBits template offset xs).reduction.difference.output.bits :
      ZMod (2^template.length+1))=
        ((2^offset.length : ℕ) : ZMod (2^template.length+1))*
          (bitValue xs : ZMod (2^template.length+1)) ∧
    bitValue (fermatShiftBits template offset xs).reduction.difference.output.bits<
      2^template.length+1 := by
  have hs := (shiftTemplateBits_exact offset xs).1
  have hpow : 2^offset.length≤2^template.length := Nat.pow_le_pow_right (by decide) ht
  have hb : bitValue (shiftTemplateBits offset xs).bits≤(2^template.length)^2 := by
    rw [hs,pow_two]
    exact Nat.mul_le_mul hpow (by omega)
  have hc := fermatReduceBits_cast hK hb
  rw [hs,Nat.cast_mul] at hc
  exact ⟨hc,(fermatReduceBits_exact hK hb).2⟩

/-- Every actual shifted/reduced output has K+1 physical cells, and its
whole primitive clock is linear in K rather than quadratic division. -/
theorem fermatShiftBits_width_cost {template offset xs : List Bool}
    (hK : 0<template.length) (ht : offset.length≤template.length) :
    (fermatShiftBits template offset xs).reduction.difference.output.bits.length=
      template.length+1 ∧
    (fermatShiftBits template offset xs).clock≤59*template.length+85 := by
  have hs := (shiftTemplateBits_exact offset xs).2.2
  have hr := fermatReduceBits_width_cost (xs:=(shiftTemplateBits offset xs).bits) hK
  exact ⟨hr.1,by dsimp only [fermatShiftBits]; omega⟩

/-- Literal low digit and shared remaining cells, with the actual
constructor inspection and bit/reference access charged. -/
structure LowBitReport where
  /-- Actual low Boolean digit, or false for an empty word. -/
  digit : Bool
  /-- Literal tail, rather than a decoded quotient by two. -/
  tail : List Bool
  /-- Primitive charge for this one-cell view. -/
  clock : ℕ

/-- Reads one physical digit and keeps the real tail reference. -/
def lowBitViewBits : List Bool→LowBitReport
  | [] => ⟨false,[],1⟩
  | bit::tail => ⟨bit,tail,3⟩

/-- The actual low digit and tail satisfy their exact radix-two
equation, and no high-word scan is hidden in this view. -/
theorem lowBitViewBits_exact (xs : List Bool) :
    bitValue xs=bitNat (lowBitViewBits xs).digit+2*bitValue (lowBitViewBits xs).tail ∧
    (lowBitViewBits xs).tail.length≤xs.length ∧
    (lowBitViewBits xs).clock≤3 := by
  cases xs with
  | nil => exact ⟨rfl,by change 0≤0; omega,by change 1≤3; omega⟩
  | cons bit tail =>
    exact ⟨rfl,by simp only [lowBitViewBits,List.length_cons]; omega,by change 3≤3; omega⟩

/-- A nonempty physical Fermat template always gives an odd modulus;
the proof-side exponent is not used in the actual halving routine. -/
theorem fermat_modulus_odd {K : ℕ} (hK : 0<K) :
    2^K+1=1+2*2^(K-1) := by
  have hk : K=(K-1)+1 := by omega
  conv_lhs => rw [hk,pow_succ]
  ring

/-- Keeps the actual modulus, original low digit, full carry sum, its
low-digit view and the paid copy of the chosen canonical half. -/
structure FermatHalfReport where
  /-- Constructed odd Fermat modulus. -/
  modulus : BitReport
  /-- Original input parity and literal input tail. -/
  input : LowBitReport
  /-- Full carry computation of input plus modulus. -/
  sum : BitReport
  /-- Actual carry-sum low digit and literal tail. -/
  added : LowBitReport
  /-- Chosen input or carry-sum tail copied to the modulus width. -/
  output : BitReport
  /-- Every construction, view, addition, copy and selection primitive. -/
  clock : ℕ

/-- Canonical division by two in the odd Fermat ring: an even input
uses its actual tail; an odd input uses the tail of its computed sum
with the modulus. Every prospective computation is retained and paid. -/
def fermatHalfBits (template xs : List Bool) : FermatHalfReport :=
  let modulus := fermatModulusBits template
  let input := lowBitViewBits xs
  let sum := addBits xs modulus.bits false
  let added := lowBitViewBits sum.bits
  let output := fitBits (if input.digit=true then added.tail else input.tail) modulus.bits
  ⟨modulus,input,sum,added,output,
    bitCost modulus+input.clock+bitCost sum+added.clock+bitCost output+8⟩

/-- Boolean halving has its exact unsigned equation and canonical
value. The odd branch's computed carry sum is proved even before its
low digit is dropped, and no modular inverse is supplied. -/
theorem fermatHalfBits_exact {template xs : List Bool}
    (hK : 0<template.length) (hx : bitValue xs<2^template.length+1) :
    bitValue (fermatHalfBits template xs).output.bits<2^template.length+1 ∧
    2*bitValue (fermatHalfBits template xs).output.bits=
      bitValue xs+(2^template.length+1)*bitNat (lowBitViewBits xs).digit := by
  have hm := fermatModulusBits_value template
  have hmw := bitValue_lt_width (fermatModulusBits template).bits
  rw [hm] at hmw
  have hi := (lowBitViewBits_exact xs).1
  have hs := addBits_correct xs (fermatModulusBits template).bits false
  simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero,hm] at hs
  have ha := (lowBitViewBits_exact (addBits xs (fermatModulusBits template).bits false).bits).1
  have hodd := fermat_modulus_odd hK
  unfold fermatHalfBits
  dsimp only
  split
  · rename_i hb
    have he : (lowBitViewBits (addBits xs (fermatModulusBits template).bits false).bits).digit=false := by
      cases h : (lowBitViewBits (addBits xs (fermatModulusBits template).bits false).bits).digit with
      | false => rfl
      | true =>
        simp only [hb,h,bitNat,if_true] at hi ha
        omega
    have htail : 2*bitValue
        (lowBitViewBits (addBits xs (fermatModulusBits template).bits false).bits).tail=
          bitValue xs+(2^template.length+1) := by
      simp only [he,bitNat,Bool.false_eq_true,if_false,Nat.zero_add] at ha
      omega
    have hsmall : bitValue
        (lowBitViewBits (addBits xs (fermatModulusBits template).bits false).bits).tail<
          2^template.length+1 := by omega
    rw [fitBits_value (hsmall.trans hmw)]
    simp only [hb,bitNat,if_true,Nat.mul_one]
    exact ⟨hsmall,htail⟩
  · rename_i hb
    have he : (lowBitViewBits xs).digit=false := by
      cases h : (lowBitViewBits xs).digit with
      | false => rfl
      | true => exact False.elim (hb h)
    simp only [he,bitNat,Bool.false_eq_true,if_false,Nat.zero_add] at hi
    have hsmall : bitValue (lowBitViewBits xs).tail<2^template.length+1 := by omega
    rw [fitBits_value (hsmall.trans hmw)]
    simp only [he,bitNat,Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero]
    exact ⟨hsmall,hi.symm⟩

/-- The actual canonical half solves multiplication by two in the
composite ring. This uses no extended-Euclid or generic inversion call. -/
theorem fermatHalfBits_cast {template xs : List Bool}
    (hK : 0<template.length) (hx : bitValue xs<2^template.length+1) :
    (2 : ZMod (2^template.length+1))*
        (bitValue (fermatHalfBits template xs).output.bits : ZMod (2^template.length+1))=
      (bitValue xs : ZMod (2^template.length+1)) := by
  have hc := congrArg (fun a : ℕ => (a : ZMod (2^template.length+1)))
    (fermatHalfBits_exact hK hx).2
  rw [Nat.cast_mul,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,add_zero] at hc
  simpa only [Nat.cast_ofNat] using hc

/-- A physical input of at most K+1 cells is canonically halved with
a linear complete primitive clock and exactly K+1 output cells. -/
theorem fermatHalfBits_width_cost {template xs : List Bool}
    (hK : 0<template.length) (hx : xs.length≤template.length+1) :
    (fermatHalfBits template xs).output.bits.length=template.length+1 ∧
    (fermatHalfBits template xs).clock≤18*template.length+36 := by
  have hm := fermatModulusBits_width_cost hK
  have hi := (lowBitViewBits_exact xs).2.2
  have ha := addBits_cost xs (fermatModulusBits template).bits false
  have hs := (lowBitViewBits_exact (addBits xs (fermatModulusBits template).bits false).bits).2.2
  have hf := fitBits_cost
    (if (lowBitViewBits xs).digit=true
      then (lowBitViewBits (addBits xs (fermatModulusBits template).bits false).bits).tail
      else (lowBitViewBits xs).tail) (fermatModulusBits template).bits
  exact ⟨(fitBits_counts _ _).1.trans hm.1,by dsimp only [fermatHalfBits]; omega⟩

/-- The cheap half of literal one constructs an actual inverse of
two, proving the transform normalization unit without assuming a
prime Fermat modulus or invoking the generic inverse backend. -/
theorem fermat_actual_inverse_two {template : List Bool} (hK : 0<template.length) :
    ∃ u : (ZMod (2^template.length+1))ˣ,
      (u : ZMod (2^template.length+1))=2 ∧
      ((u⁻¹ : (ZMod (2^template.length+1))ˣ) : ZMod (2^template.length+1))=
        (bitValue (fermatHalfBits template [true]).output.bits : ZMod (2^template.length+1)) := by
  have hp : 0<2^template.length := by positivity
  have hi : bitValue [true]<2^template.length+1 := by change 1<2^template.length+1; omega
  have hc := fermatHalfBits_cast hK hi
  change (2 : ZMod (2^template.length+1))*
    (bitValue (fermatHalfBits template [true]).output.bits : ZMod (2^template.length+1))=1 at hc
  exact ⟨⟨2,_,hc,by simpa only [mul_comm] using hc⟩,rfl,rfl⟩

/-- Actual power-of-two twiddle and the two canonical butterfly
outputs, with every intermediate shift/carry/borrow word retained. -/
structure FermatButterflyReport where
  /-- Computed canonical power-of-two multiple of the right input. -/
  twiddle : FermatShiftReport
  /-- Canonical sum of the left input and the computed twiddle. -/
  upper : ResidueAddReport
  /-- Canonical difference of those same actual operands. -/
  lower : ResidueSubReport
  /-- Complete shift, reduction, sum, difference and wrapper charges. -/
  clock : ℕ

/-- An actual exact-transform butterfly calls only structural shifts,
carry/borrow circuits and paid copying. There is no scalar product,
division, inverse or root-of-unity oracle in this data path. -/
def fermatButterflyBits (template offset left right : List Bool) : FermatButterflyReport :=
  let twiddle := fermatShiftBits template offset right
  let modulus := twiddle.reduction.modulus.bits
  let upper := residueAddBits modulus left twiddle.reduction.difference.output.bits
  let lower := residueSubBits modulus left twiddle.reduction.difference.output.bits
  ⟨twiddle,upper,lower,twiddle.clock+upper.clock+lower.clock+8⟩

/-- Both actual butterfly outputs preserve their original ring
values and are canonical, including zero and nonunit operands. -/
theorem fermatButterflyBits_exact {template offset left right : List Bool}
    (hK : 0<template.length) (ht : offset.length≤template.length)
    (hl : bitValue left<2^template.length+1) (hr : bitValue right<2^template.length+1) :
    (bitValue (fermatButterflyBits template offset left right).upper.output.bits :
      ZMod (2^template.length+1))=
        (bitValue left : ZMod (2^template.length+1))+
          ((2^offset.length : ℕ) : ZMod (2^template.length+1))*
            (bitValue right : ZMod (2^template.length+1)) ∧
    (bitValue (fermatButterflyBits template offset left right).lower.output.bits :
      ZMod (2^template.length+1))=
        (bitValue left : ZMod (2^template.length+1))-
          ((2^offset.length : ℕ) : ZMod (2^template.length+1))*
            (bitValue right : ZMod (2^template.length+1)) ∧
    bitValue (fermatButterflyBits template offset left right).upper.output.bits<
      2^template.length+1 ∧
    bitValue (fermatButterflyBits template offset left right).lower.output.bits<
      2^template.length+1 := by
  have hs := fermatShiftBits_exact hK ht hr
  have hm : bitValue (fermatShiftBits template offset right).reduction.modulus.bits=
      2^template.length+1 := fermatModulusBits_value template
  have hlm : bitValue left<
      bitValue (fermatShiftBits template offset right).reduction.modulus.bits := by rw [hm]; exact hl
  have htm : bitValue (fermatShiftBits template offset right).reduction.difference.output.bits<
      bitValue (fermatShiftBits template offset right).reduction.modulus.bits := by rw [hm]; exact hs.2
  have ha := residueAddBits_cast hlm htm
  have hd := residueSubBits_cast hlm htm
  have hac := (residueAddBits_exact hlm htm).2
  have hdc := (residueSubBits_exact hlm htm).1
  rw [hm,hs.1] at ha hd
  rw [hm] at hac hdc
  exact ⟨ha,hd,hac,hdc⟩

/-- With physical left width at most K+1, both actual butterfly outputs
have exactly K+1 cells and all work costs at most 126K+200. The bounded
shift/reduction visits only its explicitly paid right-input cells. -/
theorem fermatButterflyBits_width_cost {template offset left right : List Bool}
    (hK : 0<template.length) (ht : offset.length≤template.length)
    (hl : left.length≤template.length+1) :
    (fermatButterflyBits template offset left right).upper.output.bits.length=
      template.length+1 ∧
    (fermatButterflyBits template offset left right).lower.output.bits.length=
      template.length+1 ∧
    (fermatButterflyBits template offset left right).clock≤126*template.length+200 := by
  have hs := fermatShiftBits_width_cost (xs:=right) hK ht
  have hm : (fermatShiftBits template offset right).reduction.modulus.bits.length=
      template.length+1 := (fermatModulusBits_width_cost hK).1
  have ha := residueAddBits_cost (W:=template.length+1)
    (modulus:=(fermatShiftBits template offset right).reduction.modulus.bits)
    (xs:=left) (ys:=(fermatShiftBits template offset right).reduction.difference.output.bits)
    hm.le hl hs.1.le
  have hd := residueSubBits_cost (W:=template.length+1)
    (modulus:=(fermatShiftBits template offset right).reduction.modulus.bits)
    (xs:=left) (ys:=(fermatShiftBits template offset right).reduction.difference.output.bits)
    hm.le hl hs.1.le
  exact ⟨(residueAddBits_width _ _ _).trans hm,(residueSubBits_width _ _ _).trans hm,
    by dsimp only [fermatButterflyBits]; omega⟩

/-- Splitting a character sum into two literal halves exposes the
exact cancellation multiplier. This is an algebraic proof, not a
constructed matrix or an executable summation backend. -/
theorem power_character_double {R : Type*} [CommRing R] (w : R) (n k : ℕ) :
    (∑ j∈Finset.range (n+n),w^(j*k))=
      (1+w^(n*k))*(∑ j∈Finset.range n,w^(j*k)) := by
  rw [Finset.sum_range_add]
  have hs : (∑ j∈Finset.range n,w^((n+j)*k))=
      w^(n*k)*(∑ j∈Finset.range n,w^(j*k)) := by
    simp only [Nat.add_mul,pow_add,Finset.mul_sum]
  rw [hs]
  ring

/-- A negative half-period forces EVERY nonconstant dyadic character
to cancel, even over a composite ring. Even frequencies descend to
the squared root; odd frequencies cancel between the two halves. -/
theorem dyadic_character_cancel {R : Type*} [CommRing R] (w : R) (d : ℕ)
    (hw : w^(2^d)= -1) {k : ℕ} (hk : 0<k ∧ k<2^(d+1)) :
    (∑ j∈Finset.range (2^(d+1)),w^(j*k))=0 := by
  induction d generalizing w k with
  | zero =>
    have hk1 : k=1 := by norm_num at hk; omega
    have hw1 : w= -1 := by simpa only [pow_zero,pow_one] using hw
    simp only [hk1,Nat.mul_one,hw1]
    norm_num [Finset.sum_range_succ]
  | succ d ih =>
    have hcount : 2^(d+1+1)=2^(d+1)+2^(d+1) := by rw [pow_succ]; omega
    rw [hcount,power_character_double]
    rcases Nat.even_or_odd k with he|ho
    · obtain ⟨l,hkl⟩ := even_iff_exists_two_mul.mp he
      have hwl : (w^2)^(2^d)= -1 := by
        calc
          (w^2)^(2^d)=w^(2^(d+1)) := by rw [←pow_mul]; congr 1; rw [pow_succ]; omega
          _ = -1 := hw
      have hll : 0<l ∧ l<2^(d+1) := by rw [hcount] at hk; omega
      have hc := ih (w^2) hwl hll
      have hs : (∑ j∈Finset.range (2^(d+1)),w^(j*k))=
          ∑ j∈Finset.range (2^(d+1)),(w^2)^(j*l) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [←pow_mul,hkl]
        congr 1
        ring
      rw [hs,hc,mul_zero]
    · have hp : w^(2^(d+1)*k)= -1 := by rw [pow_mul,hw,ho.neg_one_pow]
      rw [hp,add_neg_cancel,zero_mul]

/-- In the dyadic Fermat ring, the actual cheap radix two supplies all
nonconstant Fourier cancellations. No primality or field assumption
appears in the proof. -/
theorem fermat_fourier_cancellation (d : ℕ) {k : ℕ}
    (hk : 0<k ∧ k<2^(d+1)) :
    (∑ j∈Finset.range (2^(d+1)),
      (2 : ZMod (2^(2^d)+1))^(j*k))=0 := by
  apply dyadic_character_cancel _ d _ hk
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using fermat_radix (2^d)

/-- The same cheap radix has the complete dyadic transform period.
Cancellation and period are universal algebra, not finite controls. -/
theorem fermat_fourier_period (d : ℕ) :
    (2 : ZMod (2^(2^d)+1))^(2^(d+1))=1 := by
  have hh : (2 : ZMod (2^(2^d)+1))^(2^d)= -1 := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using fermat_radix (2^d)
  rw [pow_succ,pow_mul,hh]
  norm_num

/-- The dyadic transform length is a unit in the actual constructed
Fermat ring. Its unit proof comes from the computed Boolean half of
one, rather than a prime-modulus assumption or supplied inverse. -/
theorem fermat_transform_length_unit {template : List Bool} (hK : 0<template.length)
    (d : ℕ) :
    ∃ u : (ZMod (2^template.length+1))ˣ,
      (u : ZMod (2^template.length+1))=((2^(d+1) : ℕ) : ZMod (2^template.length+1)) := by
  obtain ⟨v,hv,_⟩ := fermat_actual_inverse_two hK
  refine ⟨v^(d+1),?_⟩
  simp only [Units.val_pow_eq_pow_val,hv,Nat.cast_pow,Nat.cast_ofNat]

/-- Actual retained suffix of one physical template after another
physical template has controlled a constructor-by-constructor traversal. -/
structure TemplateSuffixReport where
  /-- Literal remaining template cells, shared rather than regenerated. -/
  remaining : List Bool
  /-- Every visited pair of constructors and tail references. -/
  clock : ℕ

/-- Computes the complementary physical shift template by actual
tail traversal. A decoded offset is never an executable input. -/
def suffixTemplateBits : List Bool→List Bool→TemplateSuffixReport
  | template,[] => ⟨template,2⟩
  | [],_::_ => ⟨[],2⟩
  | _::tail,_::offset =>
    let child := suffixTemplateBits tail offset
    ⟨child.remaining,child.clock+5⟩

/-- The actually retained suffix has exactly K-t physical cells,
and all visits cost at most five primitives per offset cell. -/
theorem suffixTemplateBits_exact (template offset : List Bool) :
    (suffixTemplateBits template offset).remaining.length=template.length-offset.length ∧
    (suffixTemplateBits template offset).clock≤5*offset.length+2 := by
  induction offset generalizing template with
  | nil => simp only [suffixTemplateBits,List.length_nil,Nat.sub_zero,Nat.mul_zero,
      Nat.zero_add,le_refl,and_self]
  | cons bit offset ih =>
    cases template with
    | nil =>
      constructor
      · simp only [suffixTemplateBits,List.length_nil,List.length_cons,Nat.zero_sub]
      · dsimp only [suffixTemplateBits,List.length_cons]; omega
    | cons cell tail =>
      have hc := ih tail
      simp only [suffixTemplateBits,List.length_cons] at hc ⊢
      exact ⟨by omega,by omega⟩

/-- Complementary powers give an exact inverse twiddle in the Fermat
ring, including t=0 and t=K. No field is used. -/
theorem fermat_power_inverse {K t : ℕ} (ht : t≤K) :
    ((2^t : ℕ) : ZMod (2^K+1))*(-((2^(K-t) : ℕ) : ZMod (2^K+1)))=1 := by
  calc
    _ = -(((2^t : ℕ) : ZMod (2^K+1))*((2^(K-t) : ℕ) : ZMod (2^K+1))) := by ring
    _ = -((2^K : ℕ) : ZMod (2^K+1)) := by
      rw [←Nat.cast_mul,←pow_add,show t+(K-t)=K by omega]
    _ = 1 := by rw [fermat_radix]; ring

/-- Actual complementary template, shifted word, constructed zero and
executed canonical negation for an inverse power-of-two twiddle. -/
structure FermatInverseShiftReport where
  /-- Actual suffix computation producing the complementary offset. -/
  complement : TemplateSuffixReport
  /-- Actual positive shift/reduction using that computed suffix. -/
  positive : FermatShiftReport
  /-- Actual zero copied to the constructed modulus width. -/
  zero : BitReport
  /-- Actual canonical subtraction of the shifted word from zero. -/
  negative : ResidueSubReport
  /-- Every complement, shift, zero copy, negation and wrapper primitive. -/
  clock : ℕ

/-- Multiplication by the inverse twiddle uses the computed K-t
template, one positive shift/reduction, then an actual canonical
negation. It does not call inverseBits or a native power. -/
def fermatInverseShiftBits (template offset xs : List Bool) : FermatInverseShiftReport :=
  let complement := suffixTemplateBits template offset
  let positive := fermatShiftBits template complement.remaining xs
  let zero := fitBits [] positive.reduction.modulus.bits
  let negative := residueSubBits positive.reduction.modulus.bits zero.bits
    positive.reduction.difference.output.bits
  ⟨complement,positive,zero,negative,
    complement.clock+positive.clock+bitCost zero+negative.clock+8⟩

/-- The actual inverse shift has the exact complementary negative
power and a canonical value; no inverse is supplied as advice. -/
theorem fermatInverseShiftBits_exact {template offset xs : List Bool}
    (hK : 0<template.length) (ht : offset.length≤template.length)
    (hx : bitValue xs<2^template.length+1) :
    (bitValue (fermatInverseShiftBits template offset xs).negative.output.bits :
      ZMod (2^template.length+1))=
        -((2^(template.length-offset.length) : ℕ) : ZMod (2^template.length+1))*
          (bitValue xs : ZMod (2^template.length+1)) ∧
    bitValue (fermatInverseShiftBits template offset xs).negative.output.bits<
      2^template.length+1 := by
  have hc := suffixTemplateBits_exact template offset
  have hs := fermatShiftBits_exact hK (by rw [hc.1]; omega) hx
  have hm : bitValue
      (fermatShiftBits template (suffixTemplateBits template offset).remaining xs).reduction.modulus.bits=
        2^template.length+1 := fermatModulusBits_value template
  have hz := fitBits_zero_value
    (fermatShiftBits template (suffixTemplateBits template offset).remaining xs).reduction.modulus.bits
  have hp : 0<2^template.length := by positivity
  have hzc : bitValue (fitBits []
      (fermatShiftBits template (suffixTemplateBits template offset).remaining xs).reduction.modulus.bits).bits<
        bitValue (fermatShiftBits template (suffixTemplateBits template offset).remaining xs).reduction.modulus.bits := by
    rw [hz,hm]; omega
  have hsc : bitValue
      (fermatShiftBits template (suffixTemplateBits template offset).remaining xs).reduction.difference.output.bits<
        bitValue (fermatShiftBits template (suffixTemplateBits template offset).remaining xs).reduction.modulus.bits := by
    rw [hm]; exact hs.2
  have hd := residueSubBits_cast hzc hsc
  have hsmall := (residueSubBits_exact hzc hsc).1
  rw [hm,hz,hs.1,hc.1] at hd
  rw [hm] at hsmall
  constructor
  · dsimp only [fermatInverseShiftBits]
    simpa only [Nat.cast_zero,zero_sub,neg_mul] using hd
  · exact hsmall

/-- Multiplying the actual inverse-shift output by its original
twiddle recovers its original input exactly in the composite ring. -/
theorem fermatInverseShiftBits_inverse {template offset xs : List Bool}
    (hK : 0<template.length) (ht : offset.length≤template.length)
    (hx : bitValue xs<2^template.length+1) :
    ((2^offset.length : ℕ) : ZMod (2^template.length+1))*
        (bitValue (fermatInverseShiftBits template offset xs).negative.output.bits :
          ZMod (2^template.length+1))=
      (bitValue xs : ZMod (2^template.length+1)) := by
  rw [(fermatInverseShiftBits_exact hK ht hx).1,←mul_assoc,fermat_power_inverse ht,one_mul]

/-- The inverse twiddle has K+1 output cells and a complete linear
primitive clock, including zero construction and full borrow work. -/
theorem fermatInverseShiftBits_width_cost {template offset xs : List Bool}
    (hK : 0<template.length) (ht : offset.length≤template.length) :
    (fermatInverseShiftBits template offset xs).negative.output.bits.length=
      template.length+1 ∧
    (fermatInverseShiftBits template offset xs).clock≤108*template.length+155 := by
  have hc := suffixTemplateBits_exact template offset
  have hs := fermatShiftBits_width_cost (xs:=xs) hK (by rw [hc.1]; omega)
  have hm : (fermatShiftBits template (suffixTemplateBits template offset).remaining xs).reduction.modulus.bits.length=
      template.length+1 := (fermatModulusBits_width_cost hK).1
  have hz := fitBits_counts []
    (fermatShiftBits template (suffixTemplateBits template offset).remaining xs).reduction.modulus.bits
  have hf := fitBits_cost []
    (fermatShiftBits template (suffixTemplateBits template offset).remaining xs).reduction.modulus.bits
  have hn := residueSubBits_cost (W:=template.length+1)
    (modulus:=(fermatShiftBits template (suffixTemplateBits template offset).remaining xs).reduction.modulus.bits)
    (xs:=(fitBits []
      (fermatShiftBits template (suffixTemplateBits template offset).remaining xs).reduction.modulus.bits).bits)
    (ys:=(fermatShiftBits template (suffixTemplateBits template offset).remaining xs).reduction.difference.output.bits)
    hm.le (by omega) hs.1.le
  exact ⟨(residueSubBits_width _ _ _).trans hm,
    by dsimp only [fermatInverseShiftBits]; omega⟩

/-- Actual sum/difference, both normalized halves and the untwisted
right output, with all intermediate words and clocks retained. -/
structure FermatInverseButterflyReport where
  /-- Actual constructed Fermat modulus. -/
  modulus : BitReport
  /-- Executed canonical sum of the two supplied transform words. -/
  sum : ResidueAddReport
  /-- Executed canonical difference of those words. -/
  difference : ResidueSubReport
  /-- Actual canonical half of the computed sum. -/
  left : FermatHalfReport
  /-- Actual canonical half of the computed difference. -/
  contrast : FermatHalfReport
  /-- Actual inverse twiddle applied to that computed contrast. -/
  right : FermatInverseShiftReport
  /-- Complete construction, mixing, halving and untwisting primitives. -/
  clock : ℕ

/-- An actual normalized inverse butterfly. Every operand for halving
and untwisting comes from the preceding Boolean computation. -/
def fermatInverseButterflyBits (template offset upper lower : List Bool) :
    FermatInverseButterflyReport :=
  let modulus := fermatModulusBits template
  let sum := residueAddBits modulus.bits upper lower
  let difference := residueSubBits modulus.bits upper lower
  let left := fermatHalfBits template sum.output.bits
  let contrast := fermatHalfBits template difference.output.bits
  let right := fermatInverseShiftBits template offset contrast.output.bits
  ⟨modulus,sum,difference,left,contrast,right,
    bitCost modulus+sum.clock+difference.clock+left.clock+contrast.clock+right.clock+12⟩

/-- Both inverse-butterfly equations and canonical outputs hold for
all original residue words; no nonzero or field premise is needed. -/
theorem fermatInverseButterflyBits_exact {template offset upper lower : List Bool}
    (hK : 0<template.length) (ht : offset.length≤template.length)
    (hu : bitValue upper<2^template.length+1) (hl : bitValue lower<2^template.length+1) :
    (2 : ZMod (2^template.length+1))*
        (bitValue (fermatInverseButterflyBits template offset upper lower).left.output.bits :
          ZMod (2^template.length+1))=
      (bitValue upper : ZMod (2^template.length+1))+(bitValue lower : ZMod (2^template.length+1)) ∧
    (2 : ZMod (2^template.length+1))*((2^offset.length : ℕ) : ZMod (2^template.length+1))*
        (bitValue (fermatInverseButterflyBits template offset upper lower).right.negative.output.bits :
          ZMod (2^template.length+1))=
      (bitValue upper : ZMod (2^template.length+1))-(bitValue lower : ZMod (2^template.length+1)) ∧
    bitValue (fermatInverseButterflyBits template offset upper lower).left.output.bits<
      2^template.length+1 ∧
    bitValue (fermatInverseButterflyBits template offset upper lower).right.negative.output.bits<
      2^template.length+1 := by
  have hm := fermatModulusBits_value template
  have hum : bitValue upper<bitValue (fermatModulusBits template).bits := by rw [hm]; exact hu
  have hlm : bitValue lower<bitValue (fermatModulusBits template).bits := by rw [hm]; exact hl
  have hs := residueAddBits_cast hum hlm
  have hd := residueSubBits_cast hum hlm
  have hsc := (residueAddBits_exact hum hlm).2
  have hdc := (residueSubBits_exact hum hlm).1
  rw [hm] at hs hd hsc hdc
  have hleft := fermatHalfBits_cast hK hsc
  have hcontrast := fermatHalfBits_cast hK hdc
  have hcc := (fermatHalfBits_exact hK hdc).1
  have hinv := fermatInverseShiftBits_inverse hK ht hcc
  have hright := (fermatInverseShiftBits_exact hK ht hcc).2
  refine ⟨hleft.trans hs,?_,(fermatHalfBits_exact hK hsc).1,hright⟩
  dsimp only [fermatInverseButterflyBits]
  rw [mul_assoc,hinv]
  exact hcontrast.trans hd

/-- Both actually recovered outputs have K+1 cells. The entire inverse
butterfly is linear in K, with all prospective corrections and repeated
modulus/zero constructions included rather than treated as free advice. -/
theorem fermatInverseButterflyBits_width_cost {template offset upper lower : List Bool}
    (hK : 0<template.length) (ht : offset.length≤template.length)
    (hu : upper.length≤template.length+1) (hl : lower.length≤template.length+1) :
    (fermatInverseButterflyBits template offset upper lower).left.output.bits.length=
      template.length+1 ∧
    (fermatInverseButterflyBits template offset upper lower).right.negative.output.bits.length=
      template.length+1 ∧
    (fermatInverseButterflyBits template offset upper lower).clock≤214*template.length+348 := by
  have hm := fermatModulusBits_width_cost hK
  have hs := residueAddBits_cost hm.1.le hu hl
  have hd := residueSubBits_cost hm.1.le hu hl
  have hsw := (residueAddBits_width (fermatModulusBits template).bits upper lower).trans hm.1
  have hdw := (residueSubBits_width (fermatModulusBits template).bits upper lower).trans hm.1
  have hleft := fermatHalfBits_width_cost hK hsw.le
  have hcontrast := fermatHalfBits_width_cost hK hdw.le
  have hright := fermatInverseShiftBits_width_cost
    (xs:=(fermatHalfBits template (residueSubBits (fermatModulusBits template).bits upper lower).output.bits).output.bits)
    hK ht
  exact ⟨hleft.1,hright.1,by dsimp only [fermatInverseButterflyBits]; omega⟩

/-- Executing the actual inverse butterfly on the actual forward
outputs recovers BOTH original canonical values. The unit cancellation
is justified by the computed half of one, also over composite moduli. -/
theorem fermatButterfly_roundtrip {template offset left right : List Bool}
    (hK : 0<template.length) (ht : offset.length≤template.length)
    (hl : bitValue left<2^template.length+1) (hr : bitValue right<2^template.length+1) :
    let forward := fermatButterflyBits template offset left right
    let back := fermatInverseButterflyBits template offset
      forward.upper.output.bits forward.lower.output.bits
    bitValue back.left.output.bits=bitValue left ∧
    bitValue back.right.negative.output.bits=bitValue right := by
  dsimp only
  have hf := fermatButterflyBits_exact hK ht hl hr
  have hi := fermatInverseButterflyBits_exact hK ht hf.2.2.1 hf.2.2.2
  have hal : (2 : ZMod (2^template.length+1))*
      (bitValue (fermatInverseButterflyBits template offset
        (fermatButterflyBits template offset left right).upper.output.bits
        (fermatButterflyBits template offset left right).lower.output.bits).left.output.bits :
          ZMod (2^template.length+1))=
        (2 : ZMod (2^template.length+1))*(bitValue left : ZMod (2^template.length+1)) := by
    rw [hi.1,hf.1,hf.2.1]
    ring
  have har : (2 : ZMod (2^template.length+1))*((2^offset.length : ℕ) : ZMod (2^template.length+1))*
      (bitValue (fermatInverseButterflyBits template offset
        (fermatButterflyBits template offset left right).upper.output.bits
        (fermatButterflyBits template offset left right).lower.output.bits).right.negative.output.bits :
          ZMod (2^template.length+1))=
        ((2 : ZMod (2^template.length+1))*((2^offset.length : ℕ) : ZMod (2^template.length+1)))*
          (bitValue right : ZMod (2^template.length+1)) := by
    rw [hi.2.1,hf.1,hf.2.1]
    ring
  obtain ⟨u,hu,_⟩ := fermat_actual_inverse_two hK
  have htwo : IsUnit (2 : ZMod (2^template.length+1)) := by rw [←hu]; exact u.isUnit
  have htwiddle : IsUnit (((2^offset.length : ℕ) : ZMod (2^template.length+1))) := by
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    exact htwo.pow offset.length
  have hlcast := htwo.mul_left_cancel hal
  have hrcast := (htwo.mul htwiddle).mul_left_cancel har
  have hleft := congrArg ZMod.val hlcast
  have hright := congrArg ZMod.val hrcast
  rw [ZMod.val_natCast_of_lt hi.2.2.1,ZMod.val_natCast_of_lt hl] at hleft
  rw [ZMod.val_natCast_of_lt hi.2.2.2,ZMod.val_natCast_of_lt hr] at hright
  exact ⟨hleft,hright⟩

/-- The whole actual forward/inverse composition has a linear complete
primitive clock; the inverse reads the forward's computed fixed-width
words, rather than separately supplied transform outputs. -/
theorem fermatButterfly_roundtrip_clock {template offset left right : List Bool}
    (hK : 0<template.length) (ht : offset.length≤template.length)
    (hl : left.length≤template.length+1) :
    let forward := fermatButterflyBits template offset left right
    let back := fermatInverseButterflyBits template offset
      forward.upper.output.bits forward.lower.output.bits
    forward.clock+back.clock+4≤340*template.length+552 := by
  have hf := fermatButterflyBits_width_cost (right:=right) hK ht hl
  have hb := fermatInverseButterflyBits_width_cost hK ht hf.1.le hf.2.1.le
  dsimp only
  omega

end RiemannGaussian.SemiprimeBitFermatArithmetic
