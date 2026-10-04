/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitIndexFactors

/-!
# Charged Boolean construction of the original short index basis

The early Euclidean basis uses actual restoring division, Boolean
coefficient products/additions and a paid public-width copy. Its determinant
invariant bounds every new coefficient by the original modulus, proving
that the copy preserves its value. Signed clipping/enumeration, original
jet acquisition and the whole machine/memory certificate remain separate.
-/

namespace RiemannGaussian.SemiprimeBitIndexBasis

open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitGcd
open SemiprimeBitIndexRoots SemiprimeIndexLattice

/-- Actual Euclidean quotient/remainder and complete coefficient update. -/
structure BasisStepWordReport where
  /-- One executed restoring division of the original remainders. -/
  division : DivisionReport
  /-- Actual quotient times the current alternating coefficient. -/
  product : BitReport
  /-- Actual addition of the previous alternating coefficient. -/
  addition : BitReport
  /-- Paid public-width copy of the computed coefficient. -/
  coefficient : BitReport
  /-- All four executed primitive clocks and retained report decisions. -/
  clock : ℕ

/-- Compute the exact alternating unsigned update. The public template
caps physical padding; no native coefficient value computes this data path. -/
def basisStepBits (template r0 r1 c0 c1 : List Bool) : BasisStepWordReport :=
  let division := divideBits r0 r1
  let product := mulBits division.quotient c1
  let addition := addBits c0 product.bits false
  let coefficient := fitBits addition.bits template
  ⟨division,product,addition,coefficient,
    division.clock+bitCost product+bitCost addition+bitCost coefficient+3⟩

/-- Conserved determinant bounds a new coefficient by the original N,
including a zero new remainder. No unknown prime or factor is used. -/
theorem coefficient_update_bound {N r0 r1 c0 c1 : ℕ}
    (hdet : r0*c1+r1*c0=N) (hr1 : 0<r1) :
    c0+(r0/r1)*c1≤N := by
  have he := shortRelation_step_determinant r0 r1 c0 c1
  rw [hdet] at he
  have hm := Nat.mul_le_mul_right (c0+(r0/r1)*c1) (Nat.succ_le_of_lt hr1)
  simp only [Nat.one_mul] at hm
  omega

/-- The public-width copy preserves the original untruncated coefficient
because the exact Euclidean determinant proves that it fits. -/
theorem basisStepBits_value {template r0 r1 c0 c1 : List Bool}
    (hdet : bitValue r0*bitValue c1+bitValue r1*bitValue c0=bitValue template)
    (hr1 : 0<bitValue r1) :
    bitValue (basisStepBits template r0 r1 c0 c1).coefficient.bits=
      bitValue c0+(bitValue r0/bitValue r1)*bitValue c1 := by
  have ha : bitValue (addBits c0 (mulBits (divideBits r0 r1).quotient c1).bits false).bits=
      bitValue c0+(bitValue r0/bitValue r1)*bitValue c1 := by
    rw [addBits_correct,mulBits_correct,(divideBits_correct r0 r1).1]
    simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero]
  have hb := coefficient_update_bound hdet hr1
  have hw : bitValue (addBits c0 (mulBits (divideBits r0 r1).quotient c1).bits false).bits<
      2^template.length := by
    rw [ha]
    exact hb.trans_lt (bitValue_lt_width template)
  dsimp only [basisStepBits]
  rw [fitBits_value hw,ha]

/-- The actual next encoded state preserves the original determinant. -/
theorem basisStepBits_determinant {template r0 r1 c0 c1 : List Bool}
    (hdet : bitValue r0*bitValue c1+bitValue r1*bitValue c0=bitValue template)
    (hr1 : 0<bitValue r1) :
    bitValue r1*bitValue (basisStepBits template r0 r1 c0 c1).coefficient.bits+
      bitValue (basisStepBits template r0 r1 c0 c1).division.remainder*bitValue c1=
      bitValue template := by
  rw [basisStepBits_value hdet hr1]
  change bitValue r1*(bitValue c0+(bitValue r0/bitValue r1)*bitValue c1)+
    bitValue (divideBits r0 r1).remainder*bitValue c1=bitValue template
  rw [(divideBits_correct r0 r1).2]
  exact (shortRelation_step_determinant _ _ _ _).trans hdet

/-- Step outputs retain bounded physical words, independently of values
or arithmetic validity of the coefficient inputs. -/
theorem basisStepBits_width {W : ℕ} {template r0 r1 c0 c1 : List Bool}
    (hr1 : 0<bitValue r1) (ht : template.length≤W) (h0 : r0.length≤W) (h1 : r1.length≤W) :
    (basisStepBits template r0 r1 c0 c1).division.quotient.length≤W ∧
      (basisStepBits template r0 r1 c0 c1).division.remainder.length≤W ∧
      (basisStepBits template r0 r1 c0 c1).coefficient.bits.length≤W := by
  dsimp only [basisStepBits]
  exact ⟨(divideBits_widths hr1).2.le.trans h0,
    (divideBits_widths hr1).1.le.trans h1,(fitBits_counts _ _).1.le.trans ht⟩

/-- A full step, including discarded high padding, costs quadratically
in physical width; coefficient multiplication is never a unit-cost call. -/
theorem basisStepBits_cost {W : ℕ} {template r0 r1 c0 c1 : List Bool}
    (hr1 : 0<bitValue r1) (ht : template.length≤W)
    (h0 : r0.length≤W) (h1 : r1.length≤W) (hc0 : c0.length≤W) (hc1 : c1.length≤W) :
    (basisStepBits template r0 r1 c0 c1).clock≤150*(W+1)^2 := by
  have hq : (divideBits r0 r1).quotient.length≤W := (divideBits_widths hr1).2.le.trans h0
  have hd := bounded_divideBits (by omega : r0.length≤3*W) h1
  obtain ⟨hp,hpw⟩ := bounded_mulBits hq hc1
  have ha := (bounded_addBits (by omega : c0.length≤3*W) hpw false).1
  have hf := fitBits_cost
    (addBits c0 (mulBits (divideBits r0 r1).quotient c1).bits false).bits template
  dsimp only [basisStepBits]
  nlinarith

/-- Retained threshold comparison and one actually executed Euclidean step. -/
structure BasisFrame where
  /-- Full comparison difference and borrow, paid even on continuation. -/
  comparison : SubReport
  /-- Division, coefficient arithmetic and paid fixed-width copy. -/
  update : BasisStepWordReport

/-- Actual early-Euclid output words, retained sign, diagnostics and clock. -/
structure BasisLoopWordReport where
  /-- Current alternating unsigned coefficient. -/
  coefficient : List Bool
  /-- Current remainder, at the threshold when the run stops normally. -/
  remainder : List Bool
  /-- Actual preceding alternating unsigned coefficient. -/
  previousCoefficient : List Bool
  /-- Actual preceding remainder, retaining the original basis companion. -/
  previousRemainder : List Bool
  /-- The original alternating sign, never inferred from private factors. -/
  negative : Bool
  /-- All executed arithmetic, fuel/list decisions and retained frames. -/
  clock : ℕ
  /-- Actually executed Euclidean divisions, separate from bit work. -/
  steps : ℕ
  /-- Explicit exhaustion diagnostic for arbitrary insufficient fuel. -/
  exhausted : Bool
  /-- Every executed coefficient update, in original order. -/
  frames : List BasisFrame
  /-- The actual final threshold comparison, absent only on exhaustion. -/
  stoppingComparison : Option SubReport

/-- Fuelled original early Euclid. The stopping branch reads the actual
borrow flag; both remainders and both coefficients are computed as words. -/
def basisLoopBits (template threshold r0 r1 c0 c1 : List Bool) (negative : Bool) :
    List Unit→BasisLoopWordReport
  | [] => ⟨c1,r1,c0,r0,negative,1,0,true,[],none⟩
  | _::fuel =>
    let comparison := subBits threshold r1 false
    if comparison.borrow=false then
      ⟨c1,r1,c0,r0,negative,bitCost comparison.result+3,0,false,[],some comparison⟩
    else
      let update := basisStepBits template r0 r1 c0 c1
      let child := basisLoopBits template threshold r1 update.division.remainder
        c1 update.coefficient.bits (!negative) fuel
      ⟨child.coefficient,child.remainder,child.previousCoefficient,child.previousRemainder,
        child.negative,bitCost comparison.result+update.clock+child.clock+7,
        child.steps+1,child.exhausted,⟨comparison,update⟩::child.frames,child.stoppingComparison⟩

/-- Mathematical interpretation of the retained words and original sign.
No executable word operation invokes this specification. -/
abbrev BasisLoopWordReport.interpret (report : BasisLoopWordReport) : ShortRelationReport :=
  ⟨bitValue report.coefficient,bitValue report.remainder,
    bitValue report.previousCoefficient,bitValue report.previousRemainder,
    report.negative,report.steps⟩

/-- Early stopping cannot exhaust fuel that suffices for the actual full
Boolean GCD run on the same remainders. Coefficients do not supply advice. -/
theorem basisLoopBits_stops_of_gcd (template threshold r0 r1 c0 c1 : List Bool)
    (negative : Bool) (fuel : List Unit)
    (hstop : (gcdLoop r0 r1 fuel).exhausted=false) :
    (basisLoopBits template threshold r0 r1 c0 c1 negative fuel).exhausted=false ∧
      (basisLoopBits template threshold r0 r1 c0 c1 negative fuel).steps≤
        (gcdLoop r0 r1 fuel).divisions := by
  induction fuel generalizing r0 r1 c0 c1 negative with
  | nil => cases hstop
  | cons cell fuel ih =>
    by_cases hb : (subBits threshold r1 false).borrow=false
    · simp only [basisLoopBits,if_pos hb]
      exact ⟨trivial,Nat.zero_le _⟩
    · have hr1 : 0<bitValue r1 := by
        have hh := subBits_borrow_false threshold r1
        have hn : ¬bitValue r1≤bitValue threshold := fun h => hb (hh.mpr h)
        omega
      have hg := (nonzeroBits_correct r1).mpr hr1
      have hcstop : (gcdLoop r1 (divideBits r0 r1).remainder fuel).exhausted=false := by
        simpa only [gcdLoop,if_pos hg] using hstop
      have hc := ih r1 (divideBits r0 r1).remainder c1
        (basisStepBits template r0 r1 c0 c1).coefficient.bits (!negative) hcstop
      simp only [basisLoopBits,if_neg hb,gcdLoop,if_pos hg,basisStepBits]
      exact ⟨hc.1,Nat.add_le_add_right hc.2 1⟩

/-- The same proved two-remainder halving pays sufficient literal fuel
for early Euclid and bounds its actual divisions, including zero inputs. -/
theorem basisLoopBits_stops_pow (k : ℕ) (template threshold r0 r1 c0 c1 : List Bool)
    (negative : Bool) (fuel : List Unit)
    (hr1 : bitValue r1<2^k) (hf : 2*k+1≤fuel.length) :
    (basisLoopBits template threshold r0 r1 c0 c1 negative fuel).exhausted=false ∧
      (basisLoopBits template threshold r0 r1 c0 c1 negative fuel).steps≤2*k := by
  have hg := gcdLoop_stops_pow k r0 r1 fuel hr1 hf
  have he := basisLoopBits_stops_of_gcd template threshold r0 r1 c0 c1 negative fuel hg.1
  exact ⟨he.1,he.2.trans hg.2⟩

/-- Every normally stopped word run is the exact original native early
Euclid, with both predecessor words, the alternating sign and actual
division count. The determinant proves every copy value-preserving. -/
theorem basisLoopBits_exact (template threshold r0 r1 c0 c1 : List Bool)
    (negative : Bool) (fuel : List Unit)
    (hdet : bitValue r0*bitValue c1+bitValue r1*bitValue c0=bitValue template)
    (hstop : (basisLoopBits template threshold r0 r1 c0 c1 negative fuel).exhausted=false) :
    (basisLoopBits template threshold r0 r1 c0 c1 negative fuel).interpret=
      shortRelationLoop (bitValue threshold) (bitValue r0) (bitValue r1)
        (bitValue c0) (bitValue c1) negative := by
  induction fuel generalizing r0 r1 c0 c1 negative with
  | nil => cases hstop
  | cons cell fuel ih =>
    by_cases hb : (subBits threshold r1 false).borrow=false
    · have hs := (subBits_borrow_false threshold r1).mp hb
      rw [basisLoopBits,if_pos hb,shortRelationLoop,dif_pos hs]
    · have hs : ¬bitValue r1≤bitValue threshold :=
        fun h => hb ((subBits_borrow_false threshold r1).mpr h)
      have hr1 : 0<bitValue r1 := by omega
      have hcstop : (basisLoopBits template threshold r1
          (basisStepBits template r0 r1 c0 c1).division.remainder
          c1 (basisStepBits template r0 r1 c0 c1).coefficient.bits (!negative) fuel).exhausted=false := by
        simpa only [basisLoopBits,if_neg hb] using hstop
      have hc := ih r1 (basisStepBits template r0 r1 c0 c1).division.remainder
        c1 (basisStepBits template r0 r1 c0 c1).coefficient.bits (!negative)
        (basisStepBits_determinant hdet hr1) hcstop
      have hrem : bitValue (basisStepBits template r0 r1 c0 c1).division.remainder=
          bitValue r0%bitValue r1 := (divideBits_correct r0 r1).2
      rw [basisStepBits_value hdet hr1,hrem] at hc
      rw [basisLoopBits,if_neg hb,shortRelationLoop,dif_neg hs]
      exact congrArg (fun report : ShortRelationReport => {report with steps := report.steps+1}) hc

/-- Every actual division has one retained frame; exhausted supplied
fuel also retains all its executed work rather than fabricating a stop. -/
theorem basisLoopBits_counts (template threshold r0 r1 c0 c1 : List Bool)
    (negative : Bool) (fuel : List Unit) :
    (basisLoopBits template threshold r0 r1 c0 c1 negative fuel).frames.length=
        (basisLoopBits template threshold r0 r1 c0 c1 negative fuel).steps ∧
      (basisLoopBits template threshold r0 r1 c0 c1 negative fuel).steps≤fuel.length := by
  induction fuel generalizing r0 r1 c0 c1 negative with
  | nil => exact ⟨rfl,Nat.le_refl _⟩
  | cons cell fuel ih =>
    have hc := ih r1 (basisStepBits template r0 r1 c0 c1).division.remainder
      c1 (basisStepBits template r0 r1 c0 c1).coefficient.bits (!negative)
    unfold basisLoopBits
    dsimp only
    split <;> dsimp only [List.length_nil,List.length_cons] <;> omega

/-- No visited step grows a retained coefficient or remainder beyond
the actual public physical template/input width. Padding remains charged. -/
theorem basisLoopBits_width {W : ℕ} {template threshold r0 r1 c0 c1 : List Bool}
    (negative : Bool) (fuel : List Unit)
    (ht : template.length≤W) (h0 : r0.length≤W) (h1 : r1.length≤W)
    (hc0 : c0.length≤W) (hc1 : c1.length≤W) :
    (basisLoopBits template threshold r0 r1 c0 c1 negative fuel).coefficient.length≤W ∧
      (basisLoopBits template threshold r0 r1 c0 c1 negative fuel).remainder.length≤W ∧
      (basisLoopBits template threshold r0 r1 c0 c1 negative fuel).previousCoefficient.length≤W ∧
      (basisLoopBits template threshold r0 r1 c0 c1 negative fuel).previousRemainder.length≤W := by
  induction fuel generalizing r0 r1 c0 c1 negative with
  | nil => exact ⟨hc1,h1,hc0,h0⟩
  | cons cell fuel ih =>
    by_cases hb : (subBits threshold r1 false).borrow=false
    · simpa only [basisLoopBits,if_pos hb] using And.intro hc1 (And.intro h1 (And.intro hc0 h0))
    · have hr1 : 0<bitValue r1 := by
        have hs : ¬bitValue r1≤bitValue threshold :=
          fun h => hb ((subBits_borrow_false threshold r1).mpr h)
        omega
      have hw := basisStepBits_width (c0:=c0) (c1:=c1) hr1 ht h0 h1
      have hc := ih (r0:=r1) (r1:=(basisStepBits template r0 r1 c0 c1).division.remainder)
        (c0:=c1) (c1:=(basisStepBits template r0 r1 c0 c1).coefficient.bits)
        (!negative) h1 hw.2.1 hc1 hw.2.2
      simpa only [basisLoopBits,if_neg hb] using hc

/-- All threshold comparisons, coefficient products/additions, copied
cells, failed first work and frame decisions are paid on every fuel path. -/
theorem basisLoopBits_cost {W : ℕ} {template threshold r0 r1 c0 c1 : List Bool}
    (negative : Bool) (fuel : List Unit)
    (ht : template.length≤W) (hthreshold : threshold.length≤W)
    (h0 : r0.length≤W) (h1 : r1.length≤W) (hc0 : c0.length≤W) (hc1 : c1.length≤W) :
    (basisLoopBits template threshold r0 r1 c0 c1 negative fuel).clock≤
      fuel.length*(200*(W+1)^2)+1 := by
  induction fuel generalizing r0 r1 c0 c1 negative with
  | nil => simp only [basisLoopBits,List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.le_refl]
  | cons cell fuel ih =>
    have hcompare : bitCost (subBits threshold r1 false).result≤12*W+2 := by
      have hc := subBits_cost threshold r1 false
      omega
    by_cases hb : (subBits threshold r1 false).borrow=false
    · simp only [basisLoopBits,if_pos hb,List.length_cons]
      nlinarith
    · have hr1 : 0<bitValue r1 := by
        have hs : ¬bitValue r1≤bitValue threshold :=
          fun h => hb ((subBits_borrow_false threshold r1).mpr h)
        omega
      have hw := basisStepBits_width (c0:=c0) (c1:=c1) hr1 ht h0 h1
      have hu := basisStepBits_cost hr1 ht h0 h1 hc0 hc1
      have hc := ih (r0:=r1) (r1:=(basisStepBits template r0 r1 c0 c1).division.remainder)
        (c0:=c1) (c1:=(basisStepBits template r0 r1 c0 c1).coefficient.bits)
        (!negative) h1 hw.2.1 hc1 hw.2.2
      simp only [basisLoopBits,if_neg hb,List.length_cons]
      nlinarith

/-- Actual public threshold construction, input reduction, fuel and basis. -/
structure BasisWordReport where
  /-- The actual encoded A+1 divisor used to construct the threshold. -/
  widthIncrement : BitReport
  /-- Actual N/(A+1) quotient/remainder report. -/
  thresholdDivision : DivisionReport
  /-- Actual reduction of the supplied decoded residue modulo N. -/
  initialReduction : DivisionReport
  /-- Literally constructed sufficient fuel cells and their clock. -/
  fuel : GcdFuel
  /-- Both original basis vectors, sign and every executed loop frame. -/
  basis : BasisLoopWordReport
  /-- Complete construction, reduction, fuel and early-Euclid clock. -/
  clock : ℕ

/-- Construct the original basis from only the original public words.
The sufficient budget is built from physical words; no native threshold,
modular reduction, quotient, coefficient or private root is supplied. -/
def shortRelationBits (modulus decoded width : List Bool) : BasisWordReport :=
  let increment := addBits width [true] false
  let threshold := divideBits modulus increment.bits
  let initial := divideBits decoded modulus
  let fuel := buildGcdFuel modulus initial.remainder
  let basis := basisLoopBits modulus threshold.quotient modulus initial.remainder
    [] [true] false fuel.cells
  ⟨increment,threshold,initial,fuel,basis,
    bitCost increment+threshold.clock+initial.clock+fuel.clock+basis.clock+6⟩

/-- The actual increment has value A+1, including padded input words. -/
theorem widthIncrement_value (width : List Bool) :
    bitValue (addBits width [true] false).bits=bitValue width+1 := by
  rw [addBits_correct]
  simp only [bitValue,bitNat,if_true,Bool.false_eq_true,if_false,
    Nat.mul_zero,Nat.add_zero]

/-- The physically constructed public fuel always suffices, even on
zero modulus words; its exhausted flag is not assumed away. -/
theorem shortRelationBits_stops (modulus decoded width : List Bool) :
    (shortRelationBits modulus decoded width).basis.exhausted=false := by
  have hf := (buildGcdFuel_counts modulus (divideBits decoded modulus).remainder).1
  have hb := basisLoopBits_stops_pow (divideBits decoded modulus).remainder.length
    modulus (divideBits modulus (addBits width [true] false).bits).quotient
    modulus (divideBits decoded modulus).remainder [] [true] false
    (buildGcdFuel modulus (divideBits decoded modulus).remainder).cells
    (bitValue_lt_width _) (by omega)
  exact hb.1

/-- For every modulus, the executed Boolean constructor equals
the original complete native basis report, not merely its first vector. -/
theorem shortRelationBits_exact (modulus decoded width : List Bool) :
    (shortRelationBits modulus decoded width).basis.interpret=
      shortRelation (bitValue modulus) (bitValue decoded) (bitValue width) := by
  have hdet : bitValue modulus*bitValue [true]+
      bitValue (divideBits decoded modulus).remainder*bitValue []=bitValue modulus := by
    simp only [bitValue,bitNat,if_true,Nat.mul_zero,Nat.add_zero,Nat.mul_one]
  have hs := shortRelationBits_stops modulus decoded width
  have hc := basisLoopBits_exact modulus
    (divideBits modulus (addBits width [true] false).bits).quotient modulus
    (divideBits decoded modulus).remainder [] [true] false
    (buildGcdFuel modulus (divideBits decoded modulus).remainder).cells hdet hs
  change (basisLoopBits _ _ _ _ _ _ _ _).interpret=_
  rw [hc,(divideBits_correct modulus (addBits width [true] false).bits).1,
    widthIncrement_value,(divideBits_correct decoded modulus).2]
  simp only [shortRelation,bitValue,bitNat,if_true,Nat.mul_zero,Nat.add_zero]

/-- The actual basis division count respects the original value-based
bound, independently of supplied high-zero padding. -/
theorem shortRelationBits_steps (modulus decoded width : List Bool) :
    (shortRelationBits modulus decoded width).basis.steps≤
      2*Nat.clog 2 (bitValue decoded%bitValue modulus+1) := by
  have he := congrArg ShortRelationReport.steps (shortRelationBits_exact modulus decoded width)
  change (shortRelationBits modulus decoded width).basis.steps=
    (shortRelation (bitValue modulus) (bitValue decoded) (bitValue width)).steps at he
  rw [he]
  exact shortRelation_steps _ _ _

/-- Positive modulus words have a cell for the literal initial coefficient.
This is derived from the actual input, not a separate representation premise. -/
theorem positive_word_length {bits : List Bool} (hvalue : 0<bitValue bits) :
    0<bits.length := by
  have hw := bitValue_lt_width bits
  by_contra! hn
  have hz : bits.length=0 := by omega
  rw [hz,pow_zero] at hw
  omega

/-- All four original basis words retain at most the supplied public
physical width. Actual quotient and coefficient construction are included. -/
theorem shortRelationBits_width {W : ℕ} {modulus decoded width : List Bool}
    (hN : 0<bitValue modulus) (hm : modulus.length≤W) :
    (shortRelationBits modulus decoded width).basis.coefficient.length≤W ∧
      (shortRelationBits modulus decoded width).basis.remainder.length≤W ∧
      (shortRelationBits modulus decoded width).basis.previousCoefficient.length≤W ∧
      (shortRelationBits modulus decoded width).basis.previousRemainder.length≤W := by
  have hi : (divideBits decoded modulus).remainder.length≤W :=
    (divideBits_widths hN).1.le.trans hm
  exact basisLoopBits_width false _ hm hm hi (Nat.zero_le _)
    (by have hp := positive_word_length hN; simp only [List.length_cons,List.length_nil]; omega)

/-- Full public basis construction has cubic physical bit-primitive cost:
the threshold and input reduction, literal fuel, every full coefficient
product/addition and paid width copy are included. -/
theorem shortRelationBits_cost {W : ℕ} {modulus decoded width : List Bool}
    (hN : 0<bitValue modulus) (hm : modulus.length≤W)
    (hs : decoded.length≤W) (hwidth : width.length≤W) :
    (shortRelationBits modulus decoded width).clock≤3000*(W+1)^3 := by
  have hp := positive_word_length hN
  have hone : ([true] : List Bool).length≤W := by
    simp only [List.length_cons,List.length_nil]
    omega
  obtain ⟨hadd,haddWidth⟩ := bounded_addBits hwidth hone false
  have hthreshold := bounded_divideBits (by omega : modulus.length≤3*(W+1)) haddWidth
  have hinitial := bounded_divideBits (by omega : decoded.length≤3*W) hm
  have htw : (divideBits modulus (addBits width [true] false).bits).quotient.length≤W := by
    have hinc : 0<bitValue (addBits width [true] false).bits := by
      rw [widthIncrement_value]
      omega
    exact (divideBits_widths hinc).2.le.trans hm
  have hiw : (divideBits decoded modulus).remainder.length≤W :=
    (divideBits_widths hN).1.le.trans hm
  obtain ⟨hf,hbuild⟩ := buildGcdFuel_counts modulus (divideBits decoded modulus).remainder
  have hsize : (buildGcdFuel modulus (divideBits decoded modulus).remainder).cells.length≤4*W+1 := by
    omega
  have hloop := basisLoopBits_cost (c0:=[]) (c1:=[true]) false
    (buildGcdFuel modulus (divideBits decoded modulus).remainder).cells
    hm htw hm hiw (Nat.zero_le _) hone
  have hloopBound := Nat.mul_le_mul_right (200*(W+1)^2) hsize
  dsimp only [shortRelationBits]
  nlinarith

/-- Both original signed basis relations, the exact determinant and the
short-vector bounds now hold for the actually constructed Boolean report. -/
theorem shortRelationBits_basis {modulus width : List Bool}
    (hN : 0<bitValue modulus) (hA : 0<bitValue width) (decoded : List Bool) :
    let out := (shortRelationBits modulus decoded width).basis.interpret
    indexRelation (bitValue decoded : ZMod (bitValue modulus)) out.coefficient out.second ∧
      indexRelation (bitValue decoded : ZMod (bitValue modulus))
        out.previousCoefficient out.companionSecond ∧
      0<out.coefficient ∧ out.coefficient≤bitValue width ∧
      |out.second|≤(bitValue modulus/(bitValue width+1) : ℕ) ∧
      (out.coefficient*out.companionSecond-out.second*out.previousCoefficient=bitValue modulus ∨
        out.coefficient*out.companionSecond-out.second*out.previousCoefficient= -(bitValue modulus : ℤ)) := by
  rw [shortRelationBits_exact modulus]
  exact shortRelation_basis hN hA _

/-- Construct exactly the basis used by the original coefficient
enumerator. Doubling the actual bound creates one paid false cell. -/
def indexBasisBits (modulus decoded bound : List Bool) : BasisWordReport :=
  let child := shortRelationBits modulus decoded (false::bound)
  {child with clock := child.clock+1}

/-- Both original source vectors, sign and division count match the
executed original enumerator's basis on every input word encoding. -/
theorem indexBasisBits_exact (modulus decoded bound : List Bool) :
    (indexBasisBits modulus decoded bound).basis.interpret=
      (SemiprimeIndexEnumeration.enumerateCoefficients
        (bitValue modulus) (bitValue decoded) (bitValue bound)).basis := by
  have he := shortRelationBits_exact modulus decoded (false::bound)
  simp only [bitValue,bitNat,Bool.false_eq_true,if_false,Nat.zero_add] at he
  exact he

/-- The four original basis words fit the actual modulus word even
when the supplied bound has a different physical width or high zeros. -/
theorem indexBasisBits_width {modulus : List Bool} (hN : 0<bitValue modulus)
    (decoded bound : List Bool) :
    (indexBasisBits modulus decoded bound).basis.coefficient.length≤modulus.length ∧
      (indexBasisBits modulus decoded bound).basis.remainder.length≤modulus.length ∧
      (indexBasisBits modulus decoded bound).basis.previousCoefficient.length≤modulus.length ∧
      (indexBasisBits modulus decoded bound).basis.previousRemainder.length≤modulus.length :=
  shortRelationBits_width (decoded:=decoded) (width:=false::bound) hN (Nat.le_refl _)

/-- The complete original enumeration basis is acquired in cubic
physical bit cost, including public doubling, threshold, reduction,
coefficient arithmetic, all comparisons and literal sufficient fuel. -/
theorem indexBasisBits_cost {W : ℕ} {modulus decoded bound : List Bool}
    (hN : 0<bitValue modulus) (hm : modulus.length≤W)
    (hs : decoded.length≤W) (hbound : bound.length≤W) :
    (indexBasisBits modulus decoded bound).clock≤25000*(W+1)^3 := by
  have hc := shortRelationBits_cost hN (by omega : modulus.length≤W+1)
    (by omega : decoded.length≤W+1)
    (by simp only [List.length_cons]; omega : (false::bound).length≤W+1)
  have hp := Nat.pow_le_pow_left (by omega : W+1+1≤2*(W+1)) 3
  rw [mul_pow] at hp
  norm_num only at hp
  dsimp only [indexBasisBits]
  nlinarith

/-- An actually accepted marked word feeds the priced original basis
constructor with no residue re-encoding. The original jet acquisition,
signed line enumeration and complete factor controller remain separate. -/
theorem marked_basis_cost {W : ℕ} {modulus target targetD baseD bound word : List Bool}
    (hN : 0<bitValue modulus)
    (hword : (SemiprimeBitInverse.decodeMarkedBits modulus target targetD baseD).index=some word)
    (hm : modulus.length≤W) (hx : target.length≤W)
    (hD : targetD.length≤W) (hE : baseD.length≤W) (hbound : bound.length≤W) :
    (SemiprimeBitInverse.decodeMarkedBits modulus target targetD baseD).clock+
      (indexBasisBits modulus word bound).clock≤30000*(W+1)^3 := by
  have hw : word.length≤W :=
    (SemiprimeBitIndexFactors.marked_word_width hN hword).le.trans hm
  have hd := SemiprimeBitInverse.decodeMarkedBits_cost hN hm hx hD hE
  have hb := indexBasisBits_cost hN hm hw hbound
  omega

end RiemannGaussian.SemiprimeBitIndexBasis
