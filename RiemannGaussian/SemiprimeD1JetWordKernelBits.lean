/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetWordSourceBits
import RiemannGaussian.SemiprimeD1KernelEntryBounds

/-! # Actual jet kernel evaluation from acquired original WORD factors
The entry consumer reads physical signed factors, odd denominator and power
factor; all source constants are reduced from bytes. No native factorial,
valuation, large integer quotient, exponent answer or integer-to-digit encoder
produces these data. The original-input wrapper acquires its own factor record.
Native small-index/control and whole heap/tape lowering remain separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1JetWordKernelBits
open scoped BigOperators
open SemiprimeBitArithmetic SemiprimeBitIndexClipping SemiprimeD1JetAxes
open SemiprimeD1JetInterpretation SemiprimeD1JetPolynomialBits
open SemiprimeD1JetAffineCoefficient (JetRun)
open SemiprimeD1RecoveryIntegerBits (positive positive_value)
attribute [local irreducible] SemiprimeD1KernelEntryBits.acquireOriginal
  SemiprimeD1WireKernelOriginal.acquireOriginal SemiprimeD1WireKernelEntry.acquire

/-- Literal product payloads depend only on the literal input vectors. -/
theorem product_words_congr (ctx : Context) (xs ys : List JetRun)
    (h : xs.map (fun r => r.words)=ys.map (fun r => r.words)) :
    (product ctx xs).words=(product ctx ys).words := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => cases h
  | cons x xs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      have he := List.cons.inj h
      have hxy : x.words=y.words := he.1
      change (SemiprimeD1JetRingBits.mul ctx x.words (product ctx xs).words).words=
        (SemiprimeD1JetRingBits.mul ctx y.words (product ctx ys).words).words
      exact congrArg₂ (fun a b => (SemiprimeD1JetRingBits.mul ctx a b).words) hxy (ih ys he.2)

/-- Every dense constant word is canonical after actual source-word reduction. -/
theorem constant_compact (ctx : Context) (word : SignedWord) :
    ∀ w∈(SemiprimeD1JetWordSourceBits.constant ctx word).words,SemiprimeSourceCompactBits.Compact w := by
  intro w hw
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
  split_ifs
  · simpa only [SemiprimeSourceCompactBits.copy_bits] using
      (SemiprimeD1RecoveryStripBits.signed_good ctx.precision word).2
  · trivial

/-- Every existing physical power returns compact coefficient words, including
its literal unit base case. This does not give any native exponent to runtime. -/
theorem power_compact (ctx : Context) (z : List (List Bool)) (n : ℕ) :
    ∀ w∈(power ctx z n).words,SemiprimeSourceCompactBits.Compact w := by
  cases n with
  | zero =>
    intro w hw
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
    split_ifs
    · exact SemiprimeD1JetScalarBits.reduce_compact _ _
    · trivial
  | succ n => exact SemiprimeD1JetRingBits.mul_compact _ _ _

/-- An ACTUAL acquired power-factor word can replace the original repeated
power circuit literally. Only the proof names the old exponent. -/
theorem power_words_eq_constant (ctx : Context) (hpos : ctx.Positive)
    (bits : List Bool) (n : ℕ) (hb : bitValue bits=2^n) :
    (power ctx (SemiprimeD1JetKernelBits.integerVector ctx 2).words n).words=
      (SemiprimeD1JetWordSourceBits.constant ctx (positive bits)).words := by
  have hp := SemiprimeD1JetPolynomialBitsBounds.power_good ctx
    (SemiprimeD1JetKernelBits.integerVector ctx 2).words n
  have hc := SemiprimeD1JetWordSourceBits.constant_good ctx (positive bits)
  apply interpret_injective ctx _ _ hpos hp.1 hc.1
    (power_compact ctx _ n) (constant_compact ctx _)
    hp.2 hc.2
  rw [power_value ctx _ n hpos,SemiprimeD1JetKernelBits.integerVector_value ctx 2 hpos,
    SemiprimeD1JetWordSourceBits.constant_value ctx (positive bits) hpos,positive_value,hb]
  simp only [Nat.cast_pow,Nat.cast_ofNat,Int.cast_pow,Int.cast_ofNat,map_pow]

/-- Actual affine-factor evaluation from physical normalized constant/slope. -/
def linear (ctx : Context) (z : List (List Bool)) (f : SemiprimeD1NormalizedLinearBits.Run) : JetRun :=
  let constant := SemiprimeD1JetWordSourceBits.constant ctx f.constant
  let slope := SemiprimeD1JetWordSourceBits.constant ctx (positive f.slope)
  let term := SemiprimeD1JetRingBits.mul ctx slope.words z
  let out := SemiprimeD1JetRingBits.add ctx constant.words term.words
  ⟨out.words,constant.clock+slope.clock+term.clock+out.clock+5⟩

/-- Exact word compatibility of one acquired physical normalized factor.
Original linear interpretation is a proof projection, never evaluated by runtime. -/
theorem linear_words (ctx : Context) (z : List (List Bool))
    (f : SemiprimeD1NormalizedLinearBits.Run) :
    (linear ctx z f).words=(SemiprimeD1JetKernelBits.linear ctx z (SemiprimeD1KernelEntryBits.linear f)).words := by
  dsimp only [linear,SemiprimeD1JetKernelBits.linear,SemiprimeD1KernelEntryBits.linear]
  rw [SemiprimeD1JetWordSourceBits.constant_words_eq_integerVector ctx f.constant _ rfl,
    SemiprimeD1JetWordSourceBits.constant_words_eq_integerVector ctx (positive f.slope) _ rfl]
  rw [positive_value]

/-- Evaluate one actual acquired WORD entry using only byte sources and physical
modular inverse/vector operations. Factory clocks are retained by the wrapper. -/
def entry (ctx : Context) (z : JetRun) (e : SemiprimeD1KernelEntryBits.Run) : JetRun :=
  let denominator := SemiprimeD1RecoveryStripBits.signed ctx.precision e.denominator
  let inverse := SemiprimeD1OddInverseBits.inverse ctx.precision denominator.bits
  let normalizer := scalar ctx inverse.bits
  let powerFactor := SemiprimeD1JetWordSourceBits.constant ctx (positive e.powerFactor)
  let factors := product ctx (e.factors.map (linear ctx z.words))
  let left := SemiprimeD1JetRingBits.mul ctx normalizer.words powerFactor.words
  let out := SemiprimeD1JetRingBits.mul ctx left.words factors.words
  ⟨out.words,z.clock+denominator.clock+inverse.clock+normalizer.clock+powerFactor.clock+
    factors.clock+left.clock+out.clock+20⟩

/-- Literal output equality discharges every original source-data relation.
No source relation or old entry is an executed argument of the public wrapper. -/
theorem entry_words (ctx : Context) (hpos : ctx.Positive) (z : JetRun)
    (words : SemiprimeD1KernelEntryBits.Run) (original : SemiprimeD1WireKernelEntry.Entry)
    (hf : words.factors.map SemiprimeD1KernelEntryBits.linear=original.factors)
    (hd : words.denominator.value=original.denominator)
    (hp : bitValue words.powerFactor=2^original.power) :
    (entry ctx z words).words=(SemiprimeD1JetKernelBits.entry ctx z original).words := by
  have hlinear : words.factors.map (fun f => (linear ctx z.words f).words)=
      original.factors.map (fun f => (SemiprimeD1JetKernelBits.linear ctx z.words f).words) := by
    rw [←hf,List.map_map]
    apply List.map_congr_left
    intro f _
    exact linear_words ctx z.words f
  have hproducts : (product ctx (words.factors.map (linear ctx z.words))).words=
      (product ctx (original.factors.map (SemiprimeD1JetKernelBits.linear ctx z.words))).words := by
    apply product_words_congr
    simpa only [List.map_map,Function.comp_def] using hlinear
  dsimp only [entry,SemiprimeD1JetKernelBits.entry]
  rw [SemiprimeD1JetWordSourceBits.signed_words_eq_integer ctx.precision words.denominator _ hd,
    ←power_words_eq_constant ctx hpos words.powerFactor original.power hp,hproducts]

/-- Closed original-input wrapper; every actual word-factory stage is retained. -/
def acquireOriginal (ctx : Context) (z : JetRun) (a : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (x y : Fin (2^a)) : JetRun :=
  let data := SemiprimeD1KernelEntryBits.acquireOriginal a t x y
  let out := entry ctx z data
  ⟨out.words,data.clock+out.clock+3⟩

/-- The NEW physically acquired original jet kernel has exactly the frozen
kernel's actual coefficient bytes, with its own distinct complete source report. -/
theorem acquireOriginal_words (ctx : Context) (hpos : ctx.Positive) (z : JetRun) (a : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (x y : Fin (2^a)) :
    (acquireOriginal ctx z a t x y).words=(SemiprimeD1JetKernelBits.acquireOriginal ctx z a t x y).words := by
  exact entry_words ctx hpos z (SemiprimeD1KernelEntryBits.acquireOriginal a t x y)
    (SemiprimeD1WireKernelOriginal.acquireOriginal a t x y) (SemiprimeD1KernelEntryBits.acquire_factors a t x y)
    (SemiprimeD1KernelEntryBits.acquire_denominator a t x y)
    (SemiprimeD1KernelEntryBits.acquire_powerFactor a t x y)

end RiemannGaussian.SemiprimeD1JetWordKernelBits
