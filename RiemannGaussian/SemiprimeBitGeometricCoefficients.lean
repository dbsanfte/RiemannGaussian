/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitIndexTraversal

/-!
# Boolean construction of geometric polynomial coefficients

The original neighboring-coefficient identity gives a linear number of
scalar updates when the short power gaps are units. All powers, constants,
differences, checked inverses and coefficient words below are constructed
by the existing Boolean circuits. No expanded product polynomial is an input.
This addresses the coefficient construction for a short evaluation block;
marked base coefficients, multipoint evaluation and the varying-target
detector batch remain separate.
-/

namespace RiemannGaussian.SemiprimeBitGeometricCoefficients

open Polynomial SemiprimeGeometricRows SemiprimeSeedGeometricRecurrence
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitInverse
open SemiprimeBitIndexFactors SemiprimeBitIndexTraversal

/-- The Boolean modular product, interpreted only in a proof statement. -/
theorem modular_product_value (modulus x y : List Bool) :
    (bitValue (modMulBits x y modulus).division.remainder : ZMod (bitValue modulus))=
      (bitValue x : ZMod (bitValue modulus))*(bitValue y : ZMod (bitValue modulus)) := by
  rw [modMulBits_correct,ZMod.natCast_mod,Nat.cast_mul]

/-- The initial unit is reduced and physically copied by division. -/
theorem reduced_one_value (modulus : List Bool) :
    (bitValue (divideBits [true] modulus).remainder : ZMod (bitValue modulus))=1 := by
  rw [(divideBits_correct _ _).2,ZMod.natCast_mod]
  simp only [bitValue,bitNat,if_true,Nat.mul_zero,Nat.add_zero,Nat.cast_one]

/-- One scalar constant-coefficient extension of the original product. -/
theorem geometric_constant_succ {R : Type*} [CommRing R] (alpha : R) (i : ℕ) :
    (rowPolynomial alpha (i+1)).coeff 0=(rowPolynomial alpha i).coeff 0*(-alpha^i) := by
  simp only [rowPolynomial,SemiprimeCartesianCompletion.rootPolynomial,
    Finset.prod_range_succ,mul_coeff_zero,coeff_sub,coeff_X_zero,coeff_C_zero,zero_sub]

/-- Actual primitives for one bit-counter-controlled initialization visit. -/
structure GeometricInitFrame where
  /-- Full scan of the remaining count. -/
  scan : NonzeroReport
  /-- Full decrement of the computed positive count. -/
  decrement : SubReport
  /-- Actual additive inverse of the current canonical base power. -/
  negative : NegationBitsReport
  /-- Extension of the original constant coefficient. -/
  constant : ModularProduct
  /-- Computation of the next base power. -/
  power : ModularProduct

/-- Computed powers in order, final power, original constant and diagnostics. -/
structure GeometricInitReport where
  /-- Original powers alpha^1 through alpha^s, one word per visit. -/
  powers : List (List Bool)
  /-- The actual final base-power word. -/
  power : List Bool
  /-- The actual constant-coefficient word. -/
  constant : List Bool
  /-- Every executed initialization frame. -/
  frames : List GeometricInitFrame
  /-- Actual final zero-counter scan. -/
  finalScan : NonzeroReport
  /-- All primitive clocks and retained traversal cells. -/
  clock : ℕ

/-- Produce short powers and the original constant coefficient without
expanding the target polynomial. Counter values occur only in erased proofs. -/
def geometricInitLoop (modulus alpha power constant remaining : List Bool) : GeometricInitReport :=
  let scan := nonzeroBits remaining
  if hs : scan.nonzero=true then
    let decrement := subBits remaining [true] false
    let negative := negateResidueBits modulus power
    let nextConstant := modMulBits constant negative.reduction.remainder modulus
    let nextPower := modMulBits power alpha modulus
    let child := geometricInitLoop modulus alpha nextPower.division.remainder
      nextConstant.division.remainder decrement.result.bits
    ⟨nextPower.division.remainder::child.powers,child.power,child.constant,
      ⟨scan,decrement,negative,nextConstant,nextPower⟩::child.frames,child.finalScan,
      scan.clock+bitCost decrement.result+negative.clock+nextConstant.clock+
        nextPower.clock+child.clock+12⟩
  else ⟨[],power,constant,[],scan,scan.clock+5⟩
termination_by bitValue remaining
decreasing_by
  have hp := (nonzeroBits_correct remaining).mp hs
  rw [(decrementBits_value hp).2]
  omega

/-- Initialization computes the original polynomial's constant and its
successive powers for every encoded positive modulus and canonical state. -/
theorem geometricInitLoop_exact {modulus : List Bool} (hN : 0<bitValue modulus)
    (alpha power constant remaining : List Bool) (i : ℕ)
    (hp : bitValue power<bitValue modulus)
    (hpower : (bitValue power : ZMod (bitValue modulus))=(bitValue alpha : ZMod (bitValue modulus))^i)
    (hc : (bitValue constant : ZMod (bitValue modulus))=
      (rowPolynomial (bitValue alpha : ZMod (bitValue modulus)) i).coeff 0) :
    (bitValue (geometricInitLoop modulus alpha power constant remaining).power :
      ZMod (bitValue modulus))=(bitValue alpha : ZMod (bitValue modulus))^(i+bitValue remaining) ∧
    (bitValue (geometricInitLoop modulus alpha power constant remaining).constant :
      ZMod (bitValue modulus))=
      (rowPolynomial (bitValue alpha : ZMod (bitValue modulus)) (i+bitValue remaining)).coeff 0 ∧
    (geometricInitLoop modulus alpha power constant remaining).powers.map
      (fun word => (bitValue word : ZMod (bitValue modulus)))=
      (List.range (bitValue remaining)).map (fun k => (bitValue alpha : ZMod (bitValue modulus))^(i+k+1)) := by
  generalize he : bitValue remaining=n at *
  induction n using Nat.strong_induction_on generalizing power constant remaining i with
  | h n ih =>
    by_cases hs : (nonzeroBits remaining).nonzero=true
    · have hn := (nonzeroBits_correct remaining).mp hs
      let decrement := subBits remaining [true] false
      let negative := negateResidueBits modulus power
      let nextConstant := modMulBits constant negative.reduction.remainder modulus
      let nextPower := modMulBits power alpha modulus
      have hd : bitValue decrement.result.bits=n-1 := by
        exact (decrementBits_value hn).2.trans (by rw [he])
      have hn' : bitValue decrement.result.bits<n := by omega
      have hnext : (bitValue nextPower.division.remainder : ZMod (bitValue modulus))=
          (bitValue alpha : ZMod (bitValue modulus))^(i+1) := by
        rw [modular_product_value,hpower,pow_succ]
      have hconstant : (bitValue nextConstant.division.remainder : ZMod (bitValue modulus))=
          (rowPolynomial (bitValue alpha : ZMod (bitValue modulus)) (i+1)).coeff 0 := by
        rw [modular_product_value,negateResidueBits_correct hp,hpower,hc,geometric_constant_succ]
      have hp' : bitValue nextPower.division.remainder<bitValue modulus := by
        rw [modMulBits_correct]
        exact Nat.mod_lt _ hN
      have ht := ih _ hn' nextPower.division.remainder nextConstant.division.remainder
        decrement.result.bits (i+1) hp' hnext hconstant rfl
      have hi : i+1+bitValue decrement.result.bits=i+n := by omega
      rw [hi] at ht
      rw [geometricInitLoop]
      dsimp only
      simp only [dif_pos hs]
      refine ⟨ht.1,ht.2.1,?_⟩
      change _::(geometricInitLoop modulus alpha nextPower.division.remainder
        nextConstant.division.remainder decrement.result.bits).powers.map _=_
      rw [ht.2.2]
      change (bitValue nextPower.division.remainder : ZMod (bitValue modulus)) ::
        (List.range (bitValue decrement.result.bits)).map
          (fun k => (bitValue alpha : ZMod (bitValue modulus))^(i+1+k+1))=_
      rw [hnext,hd]
      have hlen : n=(n-1)+1 := by omega
      conv_rhs => rw [hlen,List.range_succ_eq_map,List.map_cons,List.map_map]
      congr 1
      apply List.map_congr_left
      intro k _
      congr 1
      omega
    · have hn : n=0 := by
        have hz := nonzeroBits_correct remaining
        cases hb : (nonzeroBits remaining).nonzero with
        | false => have hh : ¬0<bitValue remaining := by rw [←hz]; simp only [hb,Bool.false_eq_true,not_false_eq_true]
                   omega
        | true => exact False.elim (hs hb)
      rw [geometricInitLoop]
      dsimp only
      simp only [dif_neg hs,hn,List.range_zero,List.map_nil,Nat.add_zero]
      exact ⟨hpower,hc,trivial⟩

/-- A failed full counter scan means zero, including padded zero words. -/
theorem counter_zero_of_clear {word : List Bool} (hs : (nonzeroBits word).nonzero≠true) :
    bitValue word=0 := by
  have hn : ¬0<bitValue word := by
    intro hp
    exact hs ((nonzeroBits_correct word).mpr hp)
  omega

/-- Initialization has linear-in-count quadratic primitive work, exact
power/frame counts, and fixed physical output widths. -/
theorem geometricInitLoop_cost_width {W : ℕ} {modulus : List Bool}
    (hN : 0<bitValue modulus) (hW : 1≤W) (alpha power constant remaining : List Bool)
    (hm : modulus.length≤W) (ha : alpha.length≤W) (hp : power.length≤W)
    (hc : constant.length≤W) (hr : remaining.length≤W) :
    (geometricInitLoop modulus alpha power constant remaining).clock≤
      (bitValue remaining+1)*(500*(W+1)^2) ∧
    (geometricInitLoop modulus alpha power constant remaining).power.length≤W ∧
    (geometricInitLoop modulus alpha power constant remaining).constant.length≤W ∧
    (geometricInitLoop modulus alpha power constant remaining).powers.length=bitValue remaining ∧
    (geometricInitLoop modulus alpha power constant remaining).frames.length=bitValue remaining ∧
    ∀ word∈(geometricInitLoop modulus alpha power constant remaining).powers, word.length≤W := by
  generalize he : bitValue remaining=n at *
  induction n using Nat.strong_induction_on generalizing power constant remaining with
  | h n ih =>
    have hscan := nonzeroBits_cost remaining
    by_cases hs : (nonzeroBits remaining).nonzero=true
    · have hn := (nonzeroBits_correct remaining).mp hs
      let decrement := subBits remaining [true] false
      let negative := negateResidueBits modulus power
      let nextConstant := modMulBits constant negative.reduction.remainder modulus
      let nextPower := modMulBits power alpha modulus
      have hd : bitValue decrement.result.bits=n-1 := by
        exact (decrementBits_value hn).2.trans (by rw [he])
      have hdec : decrement.result.bits.length≤W := by
        rw [(subBits_counts remaining [true] false).2.2.2.2]
        exact max_le hr (by simpa only [List.length_cons,List.length_nil] using hW)
      have hnp : nextPower.division.remainder.length≤W := by rw [modMulBits_width hN]; exact hm
      have hnc : nextConstant.division.remainder.length≤W := by rw [modMulBits_width hN]; exact hm
      have hneg : negative.reduction.remainder.length≤W := by rw [negateResidueBits_width hN]; exact hm
      have ht := ih _ (by omega : bitValue decrement.result.bits<n)
        nextPower.division.remainder nextConstant.division.remainder decrement.result.bits hnp hnc hdec rfl
      have hsub := subBits_cost remaining [true] false
      have hmax : max remaining.length ([true] : List Bool).length≤W :=
        max_le hr (by simpa only [List.length_cons,List.length_nil] using hW)
      have hnegCost := negateResidueBits_cost hm hp
      have hconstCost := bounded_modMulBits hc hneg hm
      have hpowerCost := bounded_modMulBits hp ha hm
      have hframe : (nonzeroBits remaining).clock+bitCost decrement.result+negative.clock+
          nextConstant.clock+nextPower.clock+12≤500*(W+1)^2 := by
        dsimp only [decrement,negative,nextConstant,nextPower] at *
        nlinarith only [hscan,hr,hsub,hmax,hnegCost,hconstCost,hpowerCost,hW]
      rw [geometricInitLoop]
      dsimp only
      simp only [dif_pos hs,List.length_cons]
      refine ⟨?_,ht.2.1,ht.2.2.1,?_,?_,?_⟩
      · change (nonzeroBits remaining).clock+bitCost decrement.result+negative.clock+
          nextConstant.clock+nextPower.clock+
          (geometricInitLoop modulus alpha nextPower.division.remainder
            nextConstant.division.remainder decrement.result.bits).clock+12≤_
        have hclock := ht.1
        have hcount : bitValue decrement.result.bits+1=n := by omega
        rw [hcount] at hclock
        calc
          _ ≤ 500*(W+1)^2+n*(500*(W+1)^2) := by omega
          _ = (n+1)*(500*(W+1)^2) := by ring
      · rw [ht.2.2.2.1]
        omega
      · rw [ht.2.2.2.2.1]
        omega
      · intro word hw
        rcases List.mem_cons.mp hw with hsame|htail
        · subst word
          exact hnp
        · exact ht.2.2.2.2.2 word htail
    · have hn : n=0 := by have hz := counter_zero_of_clear hs; omega
      rw [geometricInitLoop]
      dsimp only
      simp only [dif_neg hs,hn,List.length_nil]
      refine ⟨?_,hp,hc,trivial,trivial,?_⟩
      · simp only [Nat.zero_add,Nat.one_mul]
        nlinarith only [hscan,hr,hW]
      · intro word hw
        cases hw

/-- Actual difference and full reduction back to the modulus's width. -/
structure CoefficientDifferenceReport where
  /-- Original full Boolean wrapped subtraction. -/
  difference : DifferenceWordReport
  /-- Paid reduction/copy of the resulting word. -/
  reduction : DivisionReport
  /-- Every subtraction, optional wrap, division and retained cell. -/
  clock : ℕ

/-- Produce a canonical physical modular difference by Boolean circuits. -/
def coefficientDifferenceBits (modulus x y : List Bool) : CoefficientDifferenceReport :=
  let difference := differenceBits modulus x y
  let reduction := divideBits difference.bits modulus
  ⟨difference,reduction,difference.clock+reduction.clock+3⟩

/-- Canonical input words give the actual ring difference. -/
theorem coefficientDifferenceBits_value {modulus x y : List Bool}
    (hN : 0<bitValue modulus) (hx : bitValue x<bitValue modulus)
    (hy : bitValue y<bitValue modulus) :
    (bitValue (coefficientDifferenceBits modulus x y).reduction.remainder : ZMod (bitValue modulus))=
      (bitValue x : ZMod (bitValue modulus))-(bitValue y : ZMod (bitValue modulus)) := by
  let : NeZero (bitValue modulus) := ⟨hN.ne'⟩
  change (bitValue (divideBits (differenceBits modulus x y).bits modulus).remainder :
    ZMod (bitValue modulus))=_
  rw [(divideBits_correct _ _).2,differenceBits_exact hx hy,
    SemiprimeIndexReader.modularDifference_eq_val hN,ZMod.natCast_mod,ZMod.natCast_zmod_val]

/-- Canonical output width and quadratic full primitive clock. -/
theorem coefficientDifferenceBits_cost_width {W : ℕ} {modulus x y : List Bool}
    (hN : 0<bitValue modulus) (hm : modulus.length≤W) (hx : x.length≤W)
    (hy : y.length≤W) :
    (coefficientDifferenceBits modulus x y).clock≤400*(W+1)^2 ∧
      (coefficientDifferenceBits modulus x y).reduction.remainder.length=modulus.length := by
  have hc := differenceBits_cost hm hx hy
  have hw := differenceBits_width hm hx hy
  have hd := bounded_divideBits (by omega : (differenceBits modulus x y).bits.length≤3*(W+1))
    (by omega : modulus.length≤W+1)
  refine ⟨?_,(divideBits_widths (xs:=(differenceBits modulus x y).bits) hN).1⟩
  dsimp only [coefficientDifferenceBits]
  nlinarith

/-- Every primitive of one neighboring-coefficient update, including failure. -/
structure CoefficientWordFrame where
  /-- The actual short base-power gap. -/
  gap : CoefficientDifferenceReport
  /-- The actual recurrence numerator. -/
  numerator : CoefficientDifferenceReport
  /-- The actual recurrence denominator. -/
  denominator : ModularProduct
  /-- Full Euclid report, retaining nonunit GCDs. -/
  inverse : InverseBitsReport
  /-- Actual GCD-one test, never a supplied unit witness. -/
  unit : OneBitsReport
  /-- Numerator times the previous coefficient. -/
  product : ModularProduct
  /-- Computed next coefficient, accepted only by the caller's unit gate. -/
  coefficient : ModularProduct
  /-- All scalar circuits and retained report cells. -/
  clock : ℕ

/-- Use the original cleared recurrence and check its computed denominator. -/
def coefficientFrameBits (modulus one top terminal power previous : List Bool) : CoefficientWordFrame :=
  let gap := coefficientDifferenceBits modulus power one
  let numerator := coefficientDifferenceBits modulus power terminal
  let denominator := modMulBits top gap.reduction.remainder modulus
  let inverse := inverseBits modulus denominator.division.remainder
  let unit := isOneBits inverse.gcd
  let product := modMulBits numerator.reduction.remainder previous modulus
  let coefficient := modMulBits product.division.remainder inverse.coefficient modulus
  ⟨gap,numerator,denominator,inverse,unit,product,coefficient,
    gap.clock+numerator.clock+denominator.clock+inverse.clock+unit.clock+
      product.clock+coefficient.clock+9⟩

/-- A proved mathematical unit makes the actual gate accept and the
actual computed inverse recover the unique original recurrence value. -/
theorem coefficientFrameBits_exact {modulus one top terminal power previous : List Bool}
    (hN : 0<bitValue modulus) (hone : bitValue one<bitValue modulus)
    (ht : bitValue terminal<bitValue modulus) (hp : bitValue power<bitValue modulus)
    (hunit : IsUnit ((bitValue top : ZMod (bitValue modulus))*
      ((bitValue power : ZMod (bitValue modulus))-(bitValue one : ZMod (bitValue modulus)))))
    (expected : ZMod (bitValue modulus))
    (hrec : (bitValue top : ZMod (bitValue modulus))*
      ((bitValue power : ZMod (bitValue modulus))-(bitValue one : ZMod (bitValue modulus)))*expected=
      ((bitValue power : ZMod (bitValue modulus))-(bitValue terminal : ZMod (bitValue modulus)))*
        (bitValue previous : ZMod (bitValue modulus))) :
    (coefficientFrameBits modulus one top terminal power previous).unit.value=true ∧
    (bitValue (coefficientFrameBits modulus one top terminal power previous).coefficient.division.remainder :
      ZMod (bitValue modulus))=expected := by
  let frame := coefficientFrameBits modulus one top terminal power previous
  have hg : (bitValue frame.gap.reduction.remainder : ZMod (bitValue modulus))=
      (bitValue power : ZMod (bitValue modulus))-(bitValue one : ZMod (bitValue modulus)) :=
    coefficientDifferenceBits_value hN hp hone
  have hn : (bitValue frame.numerator.reduction.remainder : ZMod (bitValue modulus))=
      (bitValue power : ZMod (bitValue modulus))-(bitValue terminal : ZMod (bitValue modulus)) :=
    coefficientDifferenceBits_value hN hp ht
  have hd : (bitValue frame.denominator.division.remainder : ZMod (bitValue modulus))=
      (bitValue top : ZMod (bitValue modulus))*
        ((bitValue power : ZMod (bitValue modulus))-(bitValue one : ZMod (bitValue modulus))) := by
    change (bitValue (modMulBits top frame.gap.reduction.remainder modulus).division.remainder :
      ZMod (bitValue modulus))=_
    rw [modular_product_value,hg]
  have hu : IsUnit (bitValue frame.denominator.division.remainder : ZMod (bitValue modulus)) := by
    rw [hd]
    exact hunit
  have hcop := (ZMod.isUnit_iff_coprime (bitValue frame.denominator.division.remainder)
    (bitValue modulus)).mp hu
  have hgcd : bitValue frame.inverse.gcd=1 := by
    change bitValue (inverseBits modulus frame.denominator.division.remainder).gcd=1
    rw [inverseBits_gcd hN]
    exact hcop.symm
  have hgate : frame.unit.value=true := (isOneBits_correct _).mpr hgcd
  have hinverse : (bitValue frame.inverse.coefficient : ZMod (bitValue modulus))*
      (bitValue frame.denominator.division.remainder : ZMod (bitValue modulus))=1 := by
    change (bitValue (inverseBits modulus frame.denominator.division.remainder).coefficient :
      ZMod (bitValue modulus))*(bitValue frame.denominator.division.remainder : ZMod (bitValue modulus))=1
    rw [inverseBits_correct hN,hcop.symm,Nat.cast_one]
  have hrec' : (bitValue frame.denominator.division.remainder : ZMod (bitValue modulus))*expected=
      (bitValue frame.numerator.reduction.remainder : ZMod (bitValue modulus))*
        (bitValue previous : ZMod (bitValue modulus)) := by rw [hd,hn]; exact hrec
  refine ⟨hgate,?_⟩
  change (bitValue (modMulBits frame.product.division.remainder frame.inverse.coefficient
    modulus).division.remainder : ZMod (bitValue modulus))=expected
  rw [modular_product_value]
  change (bitValue (modMulBits frame.numerator.reduction.remainder previous modulus).division.remainder :
    ZMod (bitValue modulus))*(bitValue frame.inverse.coefficient : ZMod (bitValue modulus))=expected
  rw [modular_product_value,←hrec']
  calc
    _ = ((bitValue frame.inverse.coefficient : ZMod (bitValue modulus))*
      (bitValue frame.denominator.division.remainder : ZMod (bitValue modulus)))*expected := by ring
    _ = expected := by rw [hinverse,one_mul]

/-- The actual coefficient gate certifies precisely a unit denominator,
even outside the long route or on malformed original coefficient words. -/
theorem coefficientFrameBits_gate_iff {modulus : List Bool} (hN : 0<bitValue modulus)
    (one top terminal power previous : List Bool) :
    (coefficientFrameBits modulus one top terminal power previous).unit.value=true ↔
      IsUnit (bitValue (coefficientFrameBits modulus one top terminal power previous).denominator.division.remainder :
        ZMod (bitValue modulus)) := by
  let frame := coefficientFrameBits modulus one top terminal power previous
  change (isOneBits (inverseBits modulus frame.denominator.division.remainder).gcd).value=true ↔ _
  rw [isOneBits_correct,inverseBits_gcd hN,ZMod.isUnit_iff_coprime,Nat.coprime_comm]

/-- One executed coefficient update has cubic physical-width primitive work. -/
theorem coefficientFrameBits_cost_width {W : ℕ} {modulus one top terminal power previous : List Bool}
    (hN : 0<bitValue modulus) (hm : modulus.length≤W) (ho : one.length≤W)
    (hs : top.length≤W) (ht : terminal.length≤W) (hp : power.length≤W)
    (hc : previous.length≤W) :
    (coefficientFrameBits modulus one top terminal power previous).clock≤6000*(W+1)^3 ∧
      (coefficientFrameBits modulus one top terminal power previous).coefficient.division.remainder.length=
        modulus.length := by
  have hgap := coefficientDifferenceBits_cost_width hN hm hp ho
  have hnum := coefficientDifferenceBits_cost_width hN hm hp ht
  have hgw : (coefficientDifferenceBits modulus power one).reduction.remainder.length≤W := by
    rw [hgap.2]; exact hm
  have hnw : (coefficientDifferenceBits modulus power terminal).reduction.remainder.length≤W := by
    rw [hnum.2]; exact hm
  have hdw : (modMulBits top (coefficientDifferenceBits modulus power one).reduction.remainder
      modulus).division.remainder.length≤W := by rw [modMulBits_width hN]; exact hm
  have hiw := inverseBits_width hN (modMulBits top
    (coefficientDifferenceBits modulus power one).reduction.remainder modulus).division.remainder
  have hpcw : (modMulBits (coefficientDifferenceBits modulus power terminal).reduction.remainder
      previous modulus).division.remainder.length≤W := by rw [modMulBits_width hN]; exact hm
  have hden := bounded_modMulBits hs hgw hm
  have hinv := inverseBits_cost hN hm hdw
  have hgate := isOneBits_cost (hiw.1.trans hm)
  have hprod := bounded_modMulBits hnw hc hm
  have hnext := bounded_modMulBits hpcw (hiw.2.trans hm) hm
  refine ⟨?_,modMulBits_width hN⟩
  dsimp only [coefficientFrameBits]
  nlinarith only [hgap.1,hnum.1,hden,hinv,hgate,hprod,hnext]

/-- Computed accepted coefficients, exact visited frames and scalar work. -/
structure CoefficientRunReport where
  /-- Values after the initial constant, or none at the first failed inverse. -/
  coefficients : Option (List (List Bool))
  /-- Every visited update, including a rejected denominator. -/
  frames : List CoefficientWordFrame
  /-- All executed primitive work and list/option decisions. -/
  clock : ℕ

/-- Walk only the actually computed powers and stop at a failed unit gate. -/
def coefficientRunBits (modulus one top terminal previous : List Bool) : List (List Bool)→CoefficientRunReport
  | [] => ⟨some [],[],3⟩
  | power::powers =>
    let frame := coefficientFrameBits modulus one top terminal power previous
    if frame.unit.value=true then
      let child := coefficientRunBits modulus one top terminal frame.coefficient.division.remainder powers
      let coefficients := child.coefficients.map (fun words => frame.coefficient.division.remainder::words)
      ⟨coefficients,frame::child.frames,frame.clock+child.clock+8⟩
    else ⟨none,[frame],frame.clock+5⟩

/-- The checked scalar walk constructs the exact original coefficient
sequence from its computed power words and initial constant. -/
theorem coefficientRunBits_exact {modulus one top terminal alpha : List Bool}
    (hN : 0<bitValue modulus) (hone : bitValue one<bitValue modulus)
    (ht : bitValue terminal<bitValue modulus)
    (honeval : (bitValue one : ZMod (bitValue modulus))=1)
    (s : ℕ) (htop : (bitValue top : ZMod (bitValue modulus))=
      (bitValue alpha : ZMod (bitValue modulus))^s)
    (hterminal : (bitValue terminal : ZMod (bitValue modulus))=
      (bitValue alpha : ZMod (bitValue modulus))^(s+1))
    (hunit : IsUnit (bitValue alpha : ZMod (bitValue modulus)))
    (hgaps : ∀ j, 0<j→j≤s→IsUnit ((bitValue alpha : ZMod (bitValue modulus))^j-1))
    (powers : List (List Bool)) (previous : List Bool) (i : ℕ)
    (hcount : i+powers.length≤s)
    (hcur : (bitValue previous : ZMod (bitValue modulus))=
      (rowPolynomial (bitValue alpha : ZMod (bitValue modulus)) s).coeff i)
    (hcanonical : ∀ word∈powers, bitValue word<bitValue modulus)
    (hvalues : powers.map (fun word => (bitValue word : ZMod (bitValue modulus)))=
      (List.range powers.length).map (fun k => (bitValue alpha : ZMod (bitValue modulus))^(i+k+1))) :
    ∃ coefficients, (coefficientRunBits modulus one top terminal previous powers).coefficients=some coefficients ∧
      coefficients.map (fun word => (bitValue word : ZMod (bitValue modulus)))=
        (List.range powers.length).map
          (fun k => (rowPolynomial (bitValue alpha : ZMod (bitValue modulus)) s).coeff (i+k+1)) := by
  induction powers generalizing previous i with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons power powers ih =>
    have hbound : i+1≤s := by simp only [List.length_cons] at hcount; omega
    have hp := hcanonical power (List.mem_cons_self)
    have hvt := hvalues
    rw [List.map_cons,List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map] at hvt
    have hpval : (bitValue power : ZMod (bitValue modulus))=
        (bitValue alpha : ZMod (bitValue modulus))^(i+1) := by
      simpa only [Nat.add_zero] using (List.cons.inj hvt).1
    have htail : powers.map (fun word => (bitValue word : ZMod (bitValue modulus)))=
        (List.range powers.length).map (fun k => (bitValue alpha : ZMod (bitValue modulus))^(i+1+k+1)) := by
      simpa only [Function.comp_def,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (List.cons.inj hvt).2
    have hdenUnit : IsUnit ((bitValue top : ZMod (bitValue modulus))*
        ((bitValue power : ZMod (bitValue modulus))-(bitValue one : ZMod (bitValue modulus)))) := by
      rw [htop,hpval,honeval]
      exact (hunit.pow s).mul (hgaps (i+1) (by omega) hbound)
    have hrec : (bitValue top : ZMod (bitValue modulus))*
        ((bitValue power : ZMod (bitValue modulus))-(bitValue one : ZMod (bitValue modulus)))*
          (rowPolynomial (bitValue alpha : ZMod (bitValue modulus)) s).coeff (i+1)=
        ((bitValue power : ZMod (bitValue modulus))-(bitValue terminal : ZMod (bitValue modulus)))*
          (bitValue previous : ZMod (bitValue modulus)) := by
      rw [htop,hpval,honeval,hterminal,hcur]
      exact geometric_coefficient_recurrence _ s i
    have hframe := coefficientFrameBits_exact hN hone ht hp hdenUnit _ hrec
    have htcount : i+1+powers.length≤s := by simp only [List.length_cons] at hcount; omega
    obtain ⟨coefficients,hout,he⟩ := ih
      (coefficientFrameBits modulus one top terminal power previous).coefficient.division.remainder
      (i+1) htcount hframe.2 (fun word hw => hcanonical word (List.mem_cons_of_mem power hw)) htail
    refine ⟨(coefficientFrameBits modulus one top terminal power previous).coefficient.division.remainder::coefficients,?_,?_⟩
    · rw [coefficientRunBits]
      dsimp only
      rw [if_pos hframe.1]
      simp only [hout,Option.map_some]
    · rw [List.map_cons,hframe.2,he,List.length_cons,List.range_succ_eq_map,
        List.map_cons,List.map_map]
      simp only [Nat.add_zero]
      congr 1
      apply List.map_congr_left
      intro k _
      congr 1
      omega

/-- Every visited scalar update is priced, including a rejected inverse;
accepted output words and the visit list have linear length. -/
theorem coefficientRunBits_cost_width {W : ℕ} {modulus : List Bool}
    (hN : 0<bitValue modulus) (one top terminal previous : List Bool) (powers : List (List Bool))
    (hm : modulus.length≤W) (ho : one.length≤W) (hs : top.length≤W)
    (ht : terminal.length≤W) (hc : previous.length≤W)
    (hp : ∀ word∈powers, word.length≤W) :
    (coefficientRunBits modulus one top terminal previous powers).clock≤
      (powers.length+1)*(6100*(W+1)^3) ∧
    (coefficientRunBits modulus one top terminal previous powers).frames.length≤powers.length ∧
    ∀ coefficients, (coefficientRunBits modulus one top terminal previous powers).coefficients=some coefficients→
      coefficients.length=powers.length ∧ ∀ word∈coefficients, word.length=modulus.length := by
  induction powers generalizing previous with
  | nil =>
    refine ⟨?_,by simp only [coefficientRunBits,List.length_nil,le_refl],?_⟩
    · simp only [coefficientRunBits,List.length_nil,Nat.zero_add,Nat.one_mul]
      have hpow : 1≤(W+1)^3 := by
        have hh : 0<(W+1)^3 := by positivity
        omega
      omega
    · intro coefficients he
      simp only [coefficientRunBits,Option.some.injEq] at he
      subst coefficients
      exact ⟨rfl,by intro word hw; cases hw⟩
  | cons power powers ih =>
    let frame := coefficientFrameBits modulus one top terminal power previous
    have hf := coefficientFrameBits_cost_width hN hm ho hs ht (hp power List.mem_cons_self) hc
    have hw : frame.coefficient.division.remainder.length≤W := by rw [hf.2]; exact hm
    have ht := ih frame.coefficient.division.remainder hw
      (fun word hword => hp word (List.mem_cons_of_mem power hword))
    rw [coefficientRunBits]
    dsimp only
    by_cases hgate : frame.unit.value=true
    · rw [if_pos hgate]
      dsimp only
      refine ⟨?_,?_,?_⟩
      · change frame.clock+(coefficientRunBits modulus one top terminal frame.coefficient.division.remainder powers).clock+8≤_
        have hframeCost : frame.clock≤6000*(W+1)^3 := hf.1
        simp only [List.length_cons]
        have hpow : 1≤(W+1)^3 := by
          have hh : 0<(W+1)^3 := by positivity
          omega
        have htclock := ht.1
        calc
          _ ≤ 6100*(W+1)^3+(powers.length+1)*(6100*(W+1)^3) := by omega
          _ = (powers.length+1+1)*(6100*(W+1)^3) := by ring
      · change (coefficientRunBits modulus one top terminal frame.coefficient.division.remainder powers).frames.length+1≤powers.length+1
        omega
      · intro coefficients he
        change (coefficientRunBits modulus one top terminal frame.coefficient.division.remainder powers).coefficients.map
          (fun words => frame.coefficient.division.remainder::words)=some coefficients at he
        cases hcOut : (coefficientRunBits modulus one top terminal frame.coefficient.division.remainder powers).coefficients with
        | none => simp only [hcOut,Option.map_none,reduceCtorEq] at he
        | some tail =>
          simp only [hcOut,Option.map_some,Option.some.injEq] at he
          subst coefficients
          have hh := ht.2.2 tail hcOut
          refine ⟨by simp only [List.length_cons,hh.1],?_⟩
          intro word hword
          rcases List.mem_cons.mp hword with hsame|htail
          · subst word
            exact hf.2
          · exact hh.2 word htail
    · rw [if_neg hgate]
      dsimp only
      refine ⟨?_,by simp only [List.length_cons,List.length_nil]; omega,?_⟩
      · have hframeCost : frame.clock≤6000*(W+1)^3 := hf.1
        have hpow : 1≤(W+1)^3 := by
          have hh : 0<(W+1)^3 := by positivity
          omega
        have hbudget : 1≤(power::powers).length+1 := by simp only [List.length_cons]; omega
        have hh := Nat.mul_le_mul_right (6100*(W+1)^3) hbudget
        omega
      · intro coefficients he
        cases he

/-- Every produced power is an actually reduced residue. The final states
also stay canonical when the original two starting states are canonical. -/
theorem geometricInitLoop_canonical {modulus : List Bool} (hN : 0<bitValue modulus)
    (alpha power constant remaining : List Bool)
    (hp : bitValue power<bitValue modulus) (hc : bitValue constant<bitValue modulus) :
    bitValue (geometricInitLoop modulus alpha power constant remaining).power<bitValue modulus ∧
    bitValue (geometricInitLoop modulus alpha power constant remaining).constant<bitValue modulus ∧
    ∀ word∈(geometricInitLoop modulus alpha power constant remaining).powers,
      bitValue word<bitValue modulus := by
  generalize he : bitValue remaining=n at *
  induction n using Nat.strong_induction_on generalizing power constant remaining with
  | h n ih =>
    by_cases hs : (nonzeroBits remaining).nonzero=true
    · have hn := (nonzeroBits_correct remaining).mp hs
      let decrement := subBits remaining [true] false
      let nextConstant := modMulBits constant (negateResidueBits modulus power).reduction.remainder modulus
      let nextPower := modMulBits power alpha modulus
      have hd : bitValue decrement.result.bits<n := by
        have hh := (decrementBits_value hn).2
        dsimp only [decrement]
        omega
      have hnextPower : bitValue nextPower.division.remainder<bitValue modulus := by
        rw [modMulBits_correct]; exact Nat.mod_lt _ hN
      have hnextConstant : bitValue nextConstant.division.remainder<bitValue modulus := by
        rw [modMulBits_correct]; exact Nat.mod_lt _ hN
      have ht := ih _ hd nextPower.division.remainder nextConstant.division.remainder
        decrement.result.bits hnextPower hnextConstant rfl
      rw [geometricInitLoop]
      dsimp only
      simp only [dif_pos hs]
      refine ⟨ht.1,ht.2.1,?_⟩
      intro word hw
      rcases List.mem_cons.mp hw with hsame|htail
      · subst word
        exact hnextPower
      · exact ht.2.2 word htail
    · rw [geometricInitLoop]
      dsimp only
      simp only [dif_neg hs]
      exact ⟨hp,hc,by intro word hw; cases hw⟩

/-- Full paid modular updates preserve exact physical state widths. -/
theorem geometricInitLoop_width_exact {modulus : List Bool} (hN : 0<bitValue modulus)
    (alpha power constant remaining : List Bool)
    (hp : power.length=modulus.length) (hc : constant.length=modulus.length) :
    (geometricInitLoop modulus alpha power constant remaining).power.length=modulus.length ∧
    (geometricInitLoop modulus alpha power constant remaining).constant.length=modulus.length := by
  generalize he : bitValue remaining=n at *
  induction n using Nat.strong_induction_on generalizing power constant remaining with
  | h n ih =>
    by_cases hs : (nonzeroBits remaining).nonzero=true
    · have hn := (nonzeroBits_correct remaining).mp hs
      let decrement := subBits remaining [true] false
      let nextConstant := modMulBits constant (negateResidueBits modulus power).reduction.remainder modulus
      let nextPower := modMulBits power alpha modulus
      have hd : bitValue decrement.result.bits<n := by
        have hh := (decrementBits_value hn).2
        dsimp only [decrement]
        omega
      have ht := ih _ hd nextPower.division.remainder nextConstant.division.remainder
        decrement.result.bits (modMulBits_width hN) (modMulBits_width hN) rfl
      rw [geometricInitLoop]
      dsimp only
      simp only [dif_pos hs]
      exact ht
    · rw [geometricInitLoop]
      dsimp only
      simp only [dif_neg hs]
      exact ⟨hp,hc⟩

/-- Entire actual coefficient source, with one initial normalization. -/
structure GeometricCoefficientWordReport where
  /-- Computed canonical one, including its paid width copy. -/
  one : DivisionReport
  /-- Computed original constant and ordered short power words. -/
  initialization : GeometricInitReport
  /-- Computed recurrence terminal alpha^(s+1). -/
  terminal : ModularProduct
  /-- Checked coefficient sequence and failed-denominator diagnostics. -/
  recurrence : CoefficientRunReport
  /-- The original constant followed by every accepted coefficient. -/
  coefficients : Option (List (List Bool))
  /-- All scalar work, initialization, unit gates and source decisions. -/
  clock : ℕ

/-- Construct the original short geometric polynomial's coefficient words
from alpha and a Boolean count. No powers, inverse or coefficients are advice. -/
def geometricCoefficientBits (modulus alpha count : List Bool) : GeometricCoefficientWordReport :=
  let one := divideBits [true] modulus
  let initialization := geometricInitLoop modulus alpha one.remainder one.remainder count
  let terminal := modMulBits initialization.power alpha modulus
  let recurrence := coefficientRunBits modulus one.remainder initialization.power
    terminal.division.remainder initialization.constant initialization.powers
  let coefficients := recurrence.coefficients.map (fun words => initialization.constant::words)
  ⟨one,initialization,terminal,recurrence,coefficients,
    one.clock+initialization.clock+terminal.clock+recurrence.clock+7⟩

/-- Every original coefficient is actually acquired, in order, whenever
the base and its short power gaps are mathematical units. Those unit facts
are proof hypotheses; the algorithm computes and checks its own inverses. -/
theorem geometricCoefficientBits_exact {modulus : List Bool} (hN : 0<bitValue modulus)
    (alpha count : List Bool)
    (ha : IsUnit (bitValue alpha : ZMod (bitValue modulus)))
    (hgaps : ∀ j, 0<j→j≤bitValue count→IsUnit ((bitValue alpha : ZMod (bitValue modulus))^j-1)) :
    ∃ coefficients, (geometricCoefficientBits modulus alpha count).coefficients=some coefficients ∧
      coefficients.map (fun word => (bitValue word : ZMod (bitValue modulus)))=
        (List.range (bitValue count+1)).map
          (fun k => (rowPolynomial (bitValue alpha : ZMod (bitValue modulus)) (bitValue count)).coeff k) := by
  let one := divideBits [true] modulus
  let initialization := geometricInitLoop modulus alpha one.remainder one.remainder count
  let terminal := modMulBits initialization.power alpha modulus
  have hone : bitValue one.remainder<bitValue modulus := by
    rw [(divideBits_correct _ _).2]; exact Nat.mod_lt _ hN
  have honeval : (bitValue one.remainder : ZMod (bitValue modulus))=1 := reduced_one_value modulus
  have hstartPower : (bitValue one.remainder : ZMod (bitValue modulus))=
      (bitValue alpha : ZMod (bitValue modulus))^0 := by rw [honeval,pow_zero]
  have hstartConstant : (bitValue one.remainder : ZMod (bitValue modulus))=
      (rowPolynomial (bitValue alpha : ZMod (bitValue modulus)) 0).coeff 0 := by
    simpa only [rowPolynomial,SemiprimeCartesianCompletion.rootPolynomial,
      Finset.range_zero,Finset.prod_empty,coeff_one_zero] using honeval
  have hi := geometricInitLoop_exact hN alpha one.remainder one.remainder count 0
    hone hstartPower hstartConstant
  simp only [Nat.zero_add] at hi
  have hcan := geometricInitLoop_canonical hN alpha one.remainder one.remainder count hone hone
  have hlen : initialization.powers.length=bitValue count := by
    have he := congrArg List.length hi.2.2
    simpa only [List.length_map,List.length_range] using he
  have hterminal : (bitValue terminal.division.remainder : ZMod (bitValue modulus))=
      (bitValue alpha : ZMod (bitValue modulus))^(bitValue count+1) := by
    rw [modular_product_value,hi.1,pow_succ]
  have ht : bitValue terminal.division.remainder<bitValue modulus := by
    rw [modMulBits_correct]; exact Nat.mod_lt _ hN
  obtain ⟨coefficients,hout,he⟩ := coefficientRunBits_exact hN hone ht honeval
    (bitValue count) hi.1 hterminal ha hgaps initialization.powers initialization.constant 0
    (by rw [hlen,Nat.zero_add]) hi.2.1 hcan.2.2
    (by rw [hlen]; simpa only [Nat.zero_add] using hi.2.2)
  refine ⟨initialization.constant::coefficients,?_,?_⟩
  · change (coefficientRunBits modulus one.remainder initialization.power terminal.division.remainder
      initialization.constant initialization.powers).coefficients.map
        (fun words => initialization.constant::words)=_
    rw [hout]
    rfl
  · rw [List.map_cons,hi.2.1,he,hlen,List.range_succ_eq_map,List.map_cons,List.map_map]
    simp only [Nat.zero_add]
    rfl

/-- Complete actual coefficient construction has linear-in-degree cubic
primitive bit work, exact coefficient count and fixed modulus word widths. -/
theorem geometricCoefficientBits_cost_width {W : ℕ} {modulus : List Bool}
    (hN : 0<bitValue modulus) (hW : 1≤W) (alpha count : List Bool)
    (hm : modulus.length≤W) (ha : alpha.length≤W) (hc : count.length≤W) :
    (geometricCoefficientBits modulus alpha count).clock≤
      (bitValue count+1)*(7000*(W+1)^3) ∧
    (geometricCoefficientBits modulus alpha count).initialization.powers.length=bitValue count ∧
    (geometricCoefficientBits modulus alpha count).initialization.frames.length=bitValue count ∧
    ∀ coefficients, (geometricCoefficientBits modulus alpha count).coefficients=some coefficients→
      coefficients.length=bitValue count+1 ∧ ∀ word∈coefficients, word.length=modulus.length := by
  let one := divideBits [true] modulus
  let initialization := geometricInitLoop modulus alpha one.remainder one.remainder count
  let terminal := modMulBits initialization.power alpha modulus
  let recurrence := coefficientRunBits modulus one.remainder initialization.power
    terminal.division.remainder initialization.constant initialization.powers
  have how : one.remainder.length≤W := by rw [(divideBits_widths (xs:=[true]) hN).1]; exact hm
  have hi := geometricInitLoop_cost_width hN hW alpha one.remainder one.remainder count hm ha how how hc
  have htw : terminal.division.remainder.length≤W := by rw [modMulBits_width hN]; exact hm
  have hr := coefficientRunBits_cost_width hN one.remainder initialization.power
    terminal.division.remainder initialization.constant initialization.powers hm how hi.2.1 htw
    hi.2.2.1 hi.2.2.2.2.2
  have honeCost := bounded_divideBits (by simp only [List.length_cons,List.length_nil]; omega :
    ([true] : List Bool).length≤3*W) hm
  have htCost := bounded_modMulBits hi.2.1 ha hm
  have honeBound : one.clock≤72*(W+1)^2 := honeCost
  have hterminalBound : terminal.clock≤96*(W+1)^2+2 := htCost
  have hp : initialization.powers.length=bitValue count := hi.2.2.2.1
  have hf : initialization.frames.length=bitValue count := hi.2.2.2.2.1
  refine ⟨?_,hp,hf,?_⟩
  · change one.clock+initialization.clock+terminal.clock+recurrence.clock+7≤_
    have hinitCost : initialization.clock≤(bitValue count+1)*(500*(W+1)^2) := hi.1
    have hrecCost : recurrence.clock≤(bitValue count+1)*(6100*(W+1)^3) := by
      have hh := hr.1
      rw [hp] at hh
      exact hh
    have hbase : (W+1)^2≤(W+1)^3 := by
      rw [pow_succ]
      exact Nat.le_mul_of_pos_right _ (by omega)
    have hslack : (bitValue count+1)*(500*(W+1)^2)+72*(W+1)^2+
        (96*(W+1)^2+2)+7≤(bitValue count+1)*(900*(W+1)^3) := by
      have hh := Nat.mul_le_mul_right (500*(W+1)^2) (show 1≤bitValue count+1 by omega)
      nlinarith only [hbase,hh,hW]
    calc
      _ ≤ (bitValue count+1)*(900*(W+1)^3)+(bitValue count+1)*(6100*(W+1)^3) := by
        omega
      _ = _ := by ring
  · intro coefficients he
    change recurrence.coefficients.map (fun words => initialization.constant::words)=some coefficients at he
    cases hout : recurrence.coefficients with
    | none => simp only [hout,Option.map_none,reduceCtorEq] at he
    | some tail =>
      simp only [hout,Option.map_some,Option.some.injEq] at he
      subst coefficients
      have hh := hr.2.2 tail hout
      refine ⟨by simp only [List.length_cons,hh.1,hp],?_⟩
      intro word hw
      rcases List.mem_cons.mp hw with hsame|htail
      · subst word
        exact (geometricInitLoop_width_exact hN alpha one.remainder one.remainder count
          (divideBits_widths (xs:=[true]) hN).1 (divideBits_widths (xs:=[true]) hN).1).2
      · exact hh.2 word htail

/-- The retained original long-route power gaps certify the actual
construction for every short block up to the original half length. -/
theorem long_original_geometric_coefficients {p q m W : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : SemiprimeLocalOrderRouting.LongData g m)
    (modulus alpha count : List Bool) (hmod : bitValue modulus=p*q)
    (halpha : (bitValue alpha : ZMod (p*q))=
      ((SemiprimeSeedSumAcquisition.seedBase (SemiprimeCentreFreeCover.projectedUnit g m) m :
        (ZMod (p*q))ˣ) : ZMod (p*q)))
    (hcount : bitValue count≤seedHalfLength m) (hW : 1≤W)
    (hmodWidth : modulus.length≤W) (halphaWidth : alpha.length≤W) (hcountWidth : count.length≤W) :
    ∃ coefficients, (geometricCoefficientBits modulus alpha count).coefficients=some coefficients ∧
      coefficients.map (fun word => (bitValue word : ZMod (p*q)))=
        (List.range (bitValue count+1)).map
          (fun k => (rowPolynomial
            ((SemiprimeSeedSumAcquisition.seedBase (SemiprimeCentreFreeCover.projectedUnit g m) m :
              (ZMod (p*q))ˣ) : ZMod (p*q)) (bitValue count)).coeff k) ∧
      coefficients.length=bitValue count+1 ∧
      (∀ word∈coefficients, word.length=modulus.length) ∧
      (geometricCoefficientBits modulus alpha count).clock≤
        (bitValue count+1)*(7000*(W+1)^3) := by
  have hN : 0<bitValue modulus := by rw [hmod]; exact Nat.mul_pos hp.pos hq.pos
  have hunit : IsUnit (bitValue alpha : ZMod (bitValue modulus)) := by
    rw [hmod,halpha]
    exact (SemiprimeSeedSumAcquisition.seedBase (SemiprimeCentreFreeCover.projectedUnit g m) m).isUnit
  have hgaps : ∀ j, 0<j→j≤bitValue count→IsUnit ((bitValue alpha : ZMod (bitValue modulus))^j-1) := by
    intro j hj hjmax
    rw [hmod,halpha]
    exact long_seedHalf_power_gaps_unit hp hq hm g hlong j hj (hjmax.trans hcount)
  obtain ⟨coefficients,hout,he⟩ := geometricCoefficientBits_exact hN alpha count hunit hgaps
  rw [hmod,halpha] at he
  have hc := geometricCoefficientBits_cost_width hN hW alpha count hmodWidth halphaWidth hcountWidth
  have hw := hc.2.2.2 coefficients hout
  exact ⟨coefficients,hout,he,hw.1,hw.2,hc.1⟩

/-- A two-modulus short block fits the proved power-gap range. -/
theorem two_modulus_block_le_half {m : ℕ} (hm : 4≤m) : 2*m≤seedHalfLength m := by
  have hh := (seedHalfLength_bounds hm).1
  nlinarith only [hh,hm]

/-- At the actual matched public row modulus, the original two-modulus
block coefficient source has a near-linear primitive bit clock. This
prices this source alone, not marked jets or detector multipoint evaluation. -/
theorem public_short_block_coefficient_cost {p q W : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (g : (ZMod (p*q))ˣ)
    (hlong : SemiprimeLocalOrderRouting.LongData g (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
    (modulus alpha count : List Bool) (hmod : bitValue modulus=p*q)
    (halpha : (bitValue alpha : ZMod (p*q))=
      ((SemiprimeSeedSumAcquisition.seedBase
        (SemiprimeCentreFreeCover.projectedUnit g (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
        (SemiprimeEuclidRowBudget.publicRowModulus (p*q)) : (ZMod (p*q))ˣ) : ZMod (p*q)))
    (hcount : bitValue count=2*SemiprimeEuclidRowBudget.publicRowModulus (p*q)) (hW : 1≤W)
    (hmodWidth : modulus.length≤W) (halphaWidth : alpha.length≤W) (hcountWidth : count.length≤W) :
    ∃ coefficients, (geometricCoefficientBits modulus alpha count).coefficients=some coefficients ∧
      coefficients.length=2*SemiprimeEuclidRowBudget.publicRowModulus (p*q)+1 ∧
      (∀ word∈coefficients, word.length=modulus.length) ∧
      (geometricCoefficientBits modulus alpha count).clock≤
        (4*SemiprimeLehmanCoverage.sixthWidth (p*q)+1)*(7000*(W+1)^3) := by
  have hN := Nat.mul_pos hp.pos hq.pos
  have hb := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 4≤SemiprimeEuclidRowBudget.publicRowModulus (p*q) := hB.trans hb.1
  obtain ⟨coefficients,hout,_,hlen,hw,hc⟩ := long_original_geometric_coefficients hp hq hm g hlong
    modulus alpha count hmod halpha (by rw [hcount]; exact two_modulus_block_le_half hm)
    hW hmodWidth halphaWidth hcountWidth
  refine ⟨coefficients,hout,by rw [hcount] at hlen; exact hlen,hw,?_⟩
  apply hc.trans
  apply Nat.mul_le_mul_right
  rw [hcount]
  omega

end RiemannGaussian.SemiprimeBitGeometricCoefficients
