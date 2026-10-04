/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitGeometricCoefficients
import Mathlib.Algebra.DualNumber

/-!
# Original marked geometric coefficients by Boolean arithmetic

First-order coefficient state keeps the original value and logarithmic base
derivative together. Its inverse uses the same checked scalar denominator.
Only short base-power gaps are inverted; original target collision factors
are retained. Fast multipoint evaluation and the varying-target detector
batch remain separate from this coefficient source.
-/

namespace RiemannGaussian.SemiprimeBitGeometricMarks

open scoped DualNumber
open Polynomial TrivSqZeroExt SemiprimeGeometricRows SemiprimeIntervalJet
open SemiprimeSharedIntervalJet SemiprimeSeedLazyJets SemiprimeSeedGeometricRecurrence
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitInverse
open SemiprimeBitIndexTraversal SemiprimeBitGeometricCoefficients

/-- Proof-side first-order base, with its logarithmic variation. -/
noncomputable def markedBase {R : Type*} (alpha : R) : R[ε] := ⟨alpha,alpha⟩

/-- The first-order base power carries its literal original exponent. -/
theorem markedBase_power {R : Type*} [CommRing R] (alpha : R) (i : ℕ) :
    fst (markedBase alpha^i)=alpha^i ∧ snd (markedBase alpha^i)=(i : R)*alpha^i := by
  induction i with
  | zero => simp only [pow_zero,fst_one,snd_one,Nat.cast_zero,zero_mul,and_self]
  | succ i ih =>
    have hf : fst (markedBase alpha)=alpha := rfl
    have hs : snd (markedBase alpha)=alpha := rfl
    simp only [pow_succ,fst_mul,DualNumber.snd_mul,ih.1,ih.2,hf,hs,Nat.cast_add,Nat.cast_one]
    constructor
    · trivial
    · ring

/-- The first projection of the original first-order polynomial is the
original value polynomial, coefficient by coefficient. -/
theorem marked_coeff_value {R : Type*} [CommRing R] (alpha : R) (s k : ℕ) :
    fst ((rowPolynomial (markedBase alpha) s).coeff k)=(rowPolynomial alpha s).coeff k := by
  have he := congrArg (fun P : R[X] => P.coeff k)
    (rowPolynomial_map (fstHom R R R).toRingHom (markedBase alpha) s)
  rw [coeff_map] at he
  change fst ((rowPolynomial (markedBase alpha) s).coeff k)=
    (rowPolynomial (fst (markedBase alpha)) s).coeff k at he
  simpa only [markedBase,fst_mk] using he

/-- Extend the original geometric target polynomial by one original factor. -/
theorem rowPolynomial_succ {R : Type*} [CommRing R] (alpha : R) (s : ℕ) :
    rowPolynomial alpha (s+1)=X*rowPolynomial alpha s-C (alpha^s)*rowPolynomial alpha s := by
  simp only [rowPolynomial,SemiprimeCartesianCompletion.rootPolynomial,Finset.prod_range_succ]
  ring

/-- Extend the original logarithmic base polynomial by its literal last
factor, retaining the original absolute exponent s. -/
theorem babyBasePolynomial_succ {R : Type*} [CommRing R] (alpha : R) (s : ℕ) :
    babyBasePolynomial alpha (s+1)=X*babyBasePolynomial alpha s-
      C (alpha^s)*babyBasePolynomial alpha s-C ((s : R)*alpha^s)*rowPolynomial alpha s := by
  have hh := baseDerivative_split (C alpha) X s 1
  have hs := singleton_block_jet (C alpha) X s
  rw [hs.1,hs.2.2] at hh
  have hp : intervalProduct (C alpha) X s=rowPolynomial alpha s := by
    simp only [intervalProduct,rowPolynomial,SemiprimeCartesianCompletion.rootPolynomial,map_pow]
  rw [hp] at hh
  simp only [←map_pow] at hh
  change baseDerivative (C alpha) X (s+1)=_
  rw [hh]
  rw [←C_eq_natCast,neg_mul,←C_mul]
  change babyBasePolynomial alpha s*(X-C (alpha^s))+
    rowPolynomial alpha s*(-C ((s : R)*alpha^s))=_
  ring

/-- The second projection is exactly the original marked BASE
derivative polynomial, not the derivative of a rephased detector. -/
theorem marked_coeff_base {R : Type*} [CommRing R] (alpha : R) (s k : ℕ) :
    snd ((rowPolynomial (markedBase alpha) s).coeff k)=(babyBasePolynomial alpha s).coeff k := by
  induction s generalizing k with
  | zero =>
    simp only [rowPolynomial,SemiprimeCartesianCompletion.rootPolynomial,Finset.range_zero,
      Finset.prod_empty,babyBasePolynomial,baseDerivative,Finset.sum_empty,neg_zero]
    by_cases hk : k=0
    · subst k
      simp only [coeff_one_zero,snd_one,coeff_zero]
    · simp only [coeff_one,if_neg hk,coeff_zero,snd_zero]
  | succ s ih =>
    rw [rowPolynomial_succ,babyBasePolynomial_succ]
    cases k with
    | zero =>
      simp only [coeff_sub,coeff_X_mul_zero,coeff_C_mul,snd_sub,snd_zero,
        DualNumber.snd_mul,marked_coeff_value,(markedBase_power alpha s).1,
        (markedBase_power alpha s).2,ih]
      ring
    | succ k =>
      simp only [coeff_sub,coeff_X_mul,coeff_C_mul,snd_sub,DualNumber.snd_mul,
        marked_coeff_value,(markedBase_power alpha s).1,(markedBase_power alpha s).2,ih]
      ring

/-- The same cleared recurrence retains both original coefficient
channels. A unit scalar denominator is also a unit first-order denominator. -/
theorem marked_coefficient_recurrence {R : Type*} [CommRing R] (alpha : R) (s k : ℕ) :
    markedBase alpha^s*(markedBase alpha^(k+1)-1)*(rowPolynomial (markedBase alpha) s).coeff (k+1)=
      (markedBase alpha^(k+1)-markedBase alpha^(s+1))*(rowPolynomial (markedBase alpha) s).coeff k := by
  exact geometric_coefficient_recurrence _ s k

/-- The original base has no new first-order unit condition. -/
theorem markedBase_unit_iff {R : Type*} [CommRing R] (alpha : R) :
    IsUnit (markedBase alpha) ↔ IsUnit alpha := by
  rw [isUnit_iff_isUnit_fst]
  rfl

/-- Every short first-order power gap is invertible precisely when
its original scalar power gap is invertible. -/
theorem markedBase_gap_unit_iff {R : Type*} [CommRing R] (alpha : R) (i : ℕ) :
    IsUnit (markedBase alpha^i-1) ↔ IsUnit (alpha^i-1) := by
  rw [isUnit_iff_isUnit_fst,fst_sub,fst_one,(markedBase_power alpha i).1]

/-- Two actual coefficient words; no interpreted ring element is data. -/
structure MarkedWord where
  /-- Original coefficient residue word. -/
  scalar : List Bool
  /-- Original logarithmic base-derivative residue word. -/
  marked : List Bool

/-- Proof-side interpretation of the two physical words. -/
noncomputable def MarkedWord.interpret (modulus : List Bool) (word : MarkedWord) :
    (ZMod (bitValue modulus))[ε] :=
  ⟨(bitValue word.scalar : ZMod (bitValue modulus)),(bitValue word.marked : ZMod (bitValue modulus))⟩

/-- Physical width predicate, used in proofs and never to encode values. -/
abbrev MarkedWord.Bounded (word : MarkedWord) (W : ℕ) : Prop :=
  word.scalar.length≤W ∧ word.marked.length≤W

/-- Canonical residue predicate, used only to prove subtraction correct. -/
abbrev MarkedWord.Canonical (word : MarkedWord) (modulus : List Bool) : Prop :=
  bitValue word.scalar<bitValue modulus ∧ bitValue word.marked<bitValue modulus

/-- Full scalar addition and paid modular reduction. -/
structure CoefficientSumReport where
  /-- Actual carry circuit. -/
  addition : BitReport
  /-- Actual normalization of the computed sum. -/
  reduction : DivisionReport
  /-- Complete scalar work and retained primitive references. -/
  clock : ℕ

/-- Compute a canonical modular sum without a native residue oracle. -/
def coefficientSumBits (modulus x y : List Bool) : CoefficientSumReport :=
  let addition := addBits x y false
  let reduction := divideBits addition.bits modulus
  ⟨addition,reduction,bitCost addition+reduction.clock+3⟩

/-- The actual full modular sum refines ring addition on every input. -/
theorem coefficientSumBits_value (modulus x y : List Bool) :
    (bitValue (coefficientSumBits modulus x y).reduction.remainder : ZMod (bitValue modulus))=
      (bitValue x : ZMod (bitValue modulus))+(bitValue y : ZMod (bitValue modulus)) := by
  have ha := addBits_correct x y false
  simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] at ha
  change (bitValue (divideBits (addBits x y false).bits modulus).remainder : ZMod (bitValue modulus))=_
  rw [(divideBits_correct _ _).2,ZMod.natCast_mod,ha,Nat.cast_add]

/-- Every sum output has the actual modulus width, is canonical, and
costs quadratic physical-word work including its paid normalization. -/
theorem coefficientSumBits_cost_width {modulus : List Bool} (hN : 0<bitValue modulus)
    (x y : List Bool) (W : ℕ) (hm : modulus.length≤W) (hx : x.length≤W) (hy : y.length≤W) :
    (coefficientSumBits modulus x y).clock≤400*(W+1)^2 ∧
    (coefficientSumBits modulus x y).reduction.remainder.length=modulus.length ∧
    bitValue (coefficientSumBits modulus x y).reduction.remainder<bitValue modulus := by
  have ha := bounded_addBits hx hy false
  have hr := bounded_divideBits (by omega : (addBits x y false).bits.length≤3*(W+1))
    (by omega : modulus.length≤W+1)
  refine ⟨?_,(divideBits_widths (xs:=(addBits x y false).bits) hN).1,?_⟩
  · dsimp only [coefficientSumBits]
    nlinarith
  · change bitValue (divideBits (addBits x y false).bits modulus).remainder<bitValue modulus
    rw [(divideBits_correct _ _).2]
    exact Nat.mod_lt _ hN

/-- Every scalar primitive of a first-order coefficient product. -/
structure MarkedProductReport where
  /-- Original scalar product. -/
  scalar : ModularProduct
  /-- First original product-rule term. -/
  left : ModularProduct
  /-- Second original product-rule term. -/
  right : ModularProduct
  /-- Full sum of the two computed marked terms. -/
  addition : CoefficientSumReport
  /-- Actual first-order output pair. -/
  word : MarkedWord
  /-- All four scalar clocks and retained product/output references. -/
  clock : ℕ

/-- Apply the original product rule to two actual residue-word pairs. -/
def markedMulBits (modulus : List Bool) (x y : MarkedWord) : MarkedProductReport :=
  let scalar := modMulBits x.scalar y.scalar modulus
  let left := modMulBits x.scalar y.marked modulus
  let right := modMulBits x.marked y.scalar modulus
  let addition := coefficientSumBits modulus left.division.remainder right.division.remainder
  ⟨scalar,left,right,addition,⟨scalar.division.remainder,addition.reduction.remainder⟩,
    scalar.clock+left.clock+right.clock+addition.clock+7⟩

/-- Boolean product-rule multiplication is exactly first-order ring
multiplication, including zeros and nonunit original coefficients. -/
theorem markedMulBits_value (modulus : List Bool) (x y : MarkedWord) :
    (markedMulBits modulus x y).word.interpret modulus=x.interpret modulus*y.interpret modulus := by
  apply TrivSqZeroExt.ext
  · change (bitValue (modMulBits x.scalar y.scalar modulus).division.remainder : ZMod (bitValue modulus))=_
    rw [modular_product_value]
    rfl
  · change (bitValue (coefficientSumBits modulus (modMulBits x.scalar y.marked modulus).division.remainder
      (modMulBits x.marked y.scalar modulus).division.remainder).reduction.remainder : ZMod (bitValue modulus))=_
    rw [coefficientSumBits_value,modular_product_value,modular_product_value]
    rfl

/-- Actual first-order products have fixed widths, canonical residues and
quadratic primitive work; no input unit or zero-product assumption is used. -/
theorem markedMulBits_cost_width {modulus : List Bool} (hN : 0<bitValue modulus)
    (x y : MarkedWord) (W : ℕ) (hm : modulus.length≤W) (hx : x.Bounded W) (hy : y.Bounded W) :
    (markedMulBits modulus x y).clock≤1000*(W+1)^2 ∧
    (markedMulBits modulus x y).word.scalar.length=modulus.length ∧
    (markedMulBits modulus x y).word.marked.length=modulus.length ∧
    (markedMulBits modulus x y).word.Canonical modulus := by
  have hs := bounded_modMulBits hx.1 hy.1 hm
  have hl := bounded_modMulBits hx.1 hy.2 hm
  have hr := bounded_modMulBits hx.2 hy.1 hm
  have hlw : (modMulBits x.scalar y.marked modulus).division.remainder.length≤W := by
    rw [modMulBits_width hN]; exact hm
  have hrw : (modMulBits x.marked y.scalar modulus).division.remainder.length≤W := by
    rw [modMulBits_width hN]; exact hm
  have ha := coefficientSumBits_cost_width hN _ _ W hm hlw hrw
  refine ⟨?_,modMulBits_width hN,ha.2.1,?_,ha.2.2⟩
  · dsimp only [markedMulBits]
    nlinarith only [hs,hl,hr,ha.1,Nat.zero_le W]
  · change bitValue (modMulBits x.scalar y.scalar modulus).division.remainder<bitValue modulus
    rw [modMulBits_correct]
    exact Nat.mod_lt _ hN

/-- Paid first-order multiplication always returns canonical residues,
independently of any supplied width bound or input canonicality. -/
theorem markedMulBits_canonical {modulus : List Bool} (hN : 0<bitValue modulus) (x y : MarkedWord) :
    (markedMulBits modulus x y).word.Canonical modulus := by
  constructor
  · change bitValue (modMulBits x.scalar y.scalar modulus).division.remainder<bitValue modulus
    rw [modMulBits_correct]; exact Nat.mod_lt _ hN
  · change bitValue (divideBits (addBits
      (modMulBits x.scalar y.marked modulus).division.remainder
      (modMulBits x.marked y.scalar modulus).division.remainder false).bits modulus).remainder<bitValue modulus
    rw [(divideBits_correct _ _).2]; exact Nat.mod_lt _ hN

/-- Full scalar negations of both original coefficient channels. -/
structure MarkedNegationReport where
  /-- Actual value negation. -/
  scalar : NegationBitsReport
  /-- Actual logarithmic derivative negation. -/
  marked : NegationBitsReport
  /-- Actual resulting residue pair. -/
  word : MarkedWord
  /-- Complete two-scalar clock and retained sign/output cells. -/
  clock : ℕ

/-- Negate both original residue channels by paid Boolean subtraction. -/
def markedNegateBits (modulus : List Bool) (x : MarkedWord) : MarkedNegationReport :=
  let scalar := negateResidueBits modulus x.scalar
  let marked := negateResidueBits modulus x.marked
  ⟨scalar,marked,⟨scalar.reduction.remainder,marked.reduction.remainder⟩,scalar.clock+marked.clock+5⟩

/-- Canonical input values make both actual negations exact. -/
theorem markedNegateBits_value (modulus : List Bool) (x : MarkedWord) (hx : x.Canonical modulus) :
    (markedNegateBits modulus x).word.interpret modulus= -x.interpret modulus := by
  apply TrivSqZeroExt.ext
  · change (bitValue (negateResidueBits modulus x.scalar).reduction.remainder : ZMod (bitValue modulus))=_
    rw [negateResidueBits_correct hx.1]
    rfl
  · change (bitValue (negateResidueBits modulus x.marked).reduction.remainder : ZMod (bitValue modulus))=_
    rw [negateResidueBits_correct hx.2]
    rfl

/-- Full first-order negation has fixed canonical widths and quadratic
primitive work for every physical input, including failed canonicality. -/
theorem markedNegateBits_cost_width {modulus : List Bool} (hN : 0<bitValue modulus)
    (x : MarkedWord) (W : ℕ) (hm : modulus.length≤W) (hx : x.Bounded W) :
    (markedNegateBits modulus x).clock≤300*(W+1)^2 ∧
    (markedNegateBits modulus x).word.scalar.length=modulus.length ∧
    (markedNegateBits modulus x).word.marked.length=modulus.length ∧
    (markedNegateBits modulus x).word.Canonical modulus := by
  have hs := negateResidueBits_cost hm hx.1
  have he := negateResidueBits_cost hm hx.2
  refine ⟨?_,negateResidueBits_width hN _,negateResidueBits_width hN _,?_,?_⟩
  · dsimp only [markedNegateBits]
    nlinarith only [hs,he,Nat.zero_le W]
  · change bitValue (divideBits (subBits modulus x.scalar false).result.bits modulus).remainder<bitValue modulus
    rw [(divideBits_correct _ _).2]; exact Nat.mod_lt _ hN
  · change bitValue (divideBits (subBits modulus x.marked false).result.bits modulus).remainder<bitValue modulus
    rw [(divideBits_correct _ _).2]; exact Nat.mod_lt _ hN

/-- Two full canonical differences retain both original first-order channels. -/
structure MarkedDifferenceReport where
  /-- Actual scalar difference. -/
  scalar : CoefficientDifferenceReport
  /-- Actual marked difference. -/
  marked : CoefficientDifferenceReport
  /-- Actual normalized first-order word pair. -/
  word : MarkedWord
  /-- Every executed subtraction, wrap, reduction and output reference. -/
  clock : ℕ

/-- Compute both original first-order differences by Boolean circuits. -/
def markedDifferenceBits (modulus : List Bool) (x y : MarkedWord) : MarkedDifferenceReport :=
  let scalar := coefficientDifferenceBits modulus x.scalar y.scalar
  let marked := coefficientDifferenceBits modulus x.marked y.marked
  ⟨scalar,marked,⟨scalar.reduction.remainder,marked.reduction.remainder⟩,scalar.clock+marked.clock+5⟩

/-- Canonical original pairs give their exact first-order difference. -/
theorem markedDifferenceBits_value {modulus : List Bool} (hN : 0<bitValue modulus)
    (x y : MarkedWord) (hx : x.Canonical modulus) (hy : y.Canonical modulus) :
    (markedDifferenceBits modulus x y).word.interpret modulus=x.interpret modulus-y.interpret modulus := by
  apply TrivSqZeroExt.ext
  · change (bitValue (coefficientDifferenceBits modulus x.scalar y.scalar).reduction.remainder : ZMod (bitValue modulus))=_
    rw [coefficientDifferenceBits_value hN hx.1 hy.1]
    rfl
  · change (bitValue (coefficientDifferenceBits modulus x.marked y.marked).reduction.remainder : ZMod (bitValue modulus))=_
    rw [coefficientDifferenceBits_value hN hx.2 hy.2]
    rfl

/-- Each first-order difference pays both scalar normalizations and
keeps fixed canonical output widths on arbitrary physical words. -/
theorem markedDifferenceBits_cost_width {modulus : List Bool} (hN : 0<bitValue modulus)
    (x y : MarkedWord) (W : ℕ) (hm : modulus.length≤W) (hx : x.Bounded W) (hy : y.Bounded W) :
    (markedDifferenceBits modulus x y).clock≤900*(W+1)^2 ∧
    (markedDifferenceBits modulus x y).word.scalar.length=modulus.length ∧
    (markedDifferenceBits modulus x y).word.marked.length=modulus.length ∧
    (markedDifferenceBits modulus x y).word.Canonical modulus := by
  have hs := coefficientDifferenceBits_cost_width hN hm hx.1 hy.1
  have he := coefficientDifferenceBits_cost_width hN hm hx.2 hy.2
  refine ⟨?_,hs.2,he.2,?_,?_⟩
  · dsimp only [markedDifferenceBits]
    nlinarith only [hs.1,he.1,Nat.zero_le W]
  · change bitValue (divideBits (SemiprimeBitIndexFactors.differenceBits modulus x.scalar y.scalar).bits modulus).remainder<bitValue modulus
    rw [(divideBits_correct _ _).2]; exact Nat.mod_lt _ hN
  · change bitValue (divideBits (SemiprimeBitIndexFactors.differenceBits modulus x.marked y.marked).bits modulus).remainder<bitValue modulus
    rw [(divideBits_correct _ _).2]; exact Nat.mod_lt _ hN

/-- Every primitive of a computed first-order inverse and its unit gate. -/
structure MarkedInverseWordReport where
  /-- Actual scalar extended-Euclid report, including nonunit GCDs. -/
  inverse : InverseBitsReport
  /-- Actual computed GCD-one test. -/
  unit : OneBitsReport
  /-- Square of the actual inverse coefficient. -/
  square : ModularProduct
  /-- Computed marked correction before its original negative sign. -/
  product : ModularProduct
  /-- Full negation/reduction of the correction. -/
  negative : NegationBitsReport
  /-- Actual pair (a^-1,-a^-2*e), accepted only by the caller's gate. -/
  word : MarkedWord
  /-- Complete scalar inverse, products, negation, gate and references. -/
  clock : ℕ

/-- The first-order inverse uses exactly one checked scalar inversion.
No derivative inverse, local prime or private collision index is supplied. -/
def markedInverseBits (modulus : List Bool) (x : MarkedWord) : MarkedInverseWordReport :=
  let inverse := inverseBits modulus x.scalar
  let unit := isOneBits inverse.gcd
  let square := modMulBits inverse.coefficient inverse.coefficient modulus
  let product := modMulBits square.division.remainder x.marked modulus
  let negative := negateResidueBits modulus product.division.remainder
  ⟨inverse,unit,square,product,negative,⟨inverse.coefficient,negative.reduction.remainder⟩,
    inverse.clock+unit.clock+square.clock+product.clock+negative.clock+8⟩

/-- First-order invertibility imposes exactly the original scalar
unit condition, including over the composite semiprime ring. -/
theorem markedInverseBits_gate_iff {modulus : List Bool} (hN : 0<bitValue modulus) (x : MarkedWord) :
    (markedInverseBits modulus x).unit.value=true ↔ IsUnit (x.interpret modulus) := by
  change (isOneBits (inverseBits modulus x.scalar).gcd).value=true ↔ IsUnit (x.interpret modulus)
  rw [isOneBits_correct,inverseBits_gcd hN,isUnit_iff_isUnit_fst]
  change (bitValue modulus).gcd (bitValue x.scalar)=1 ↔
    IsUnit (bitValue x.scalar : ZMod (bitValue modulus))
  rw [ZMod.isUnit_iff_coprime,Nat.coprime_comm]

/-- Whenever the actual gate accepts, both original inverse equations
hold in the first-order ring. No additional unit denominator appears. -/
theorem markedInverseBits_value {modulus : List Bool} (hN : 0<bitValue modulus) (x : MarkedWord)
    (hgate : (markedInverseBits modulus x).unit.value=true) :
    (markedInverseBits modulus x).word.interpret modulus*x.interpret modulus=1 := by
  let report := markedInverseBits modulus x
  have hgcd : bitValue report.inverse.gcd=1 := (isOneBits_correct _).mp hgate
  have hcop : (bitValue modulus).gcd (bitValue x.scalar)=1 := by
    change bitValue (inverseBits modulus x.scalar).gcd=1 at hgcd
    rw [inverseBits_gcd hN] at hgcd
    exact hgcd
  have hinverse : (bitValue report.inverse.coefficient : ZMod (bitValue modulus))*
      (bitValue x.scalar : ZMod (bitValue modulus))=1 := by
    change (bitValue (inverseBits modulus x.scalar).coefficient : ZMod (bitValue modulus))*
      (bitValue x.scalar : ZMod (bitValue modulus))=1
    rw [inverseBits_correct hN,hcop,Nat.cast_one]
  have hp : bitValue report.product.division.remainder<bitValue modulus := by
    change bitValue (modMulBits report.square.division.remainder x.marked modulus).division.remainder<bitValue modulus
    rw [modMulBits_correct]; exact Nat.mod_lt _ hN
  have hmark : (bitValue report.word.marked : ZMod (bitValue modulus))=
      -((bitValue report.inverse.coefficient : ZMod (bitValue modulus))^2*
        (bitValue x.marked : ZMod (bitValue modulus))) := by
    change (bitValue (negateResidueBits modulus report.product.division.remainder).reduction.remainder :
      ZMod (bitValue modulus))=_
    rw [negateResidueBits_correct hp]
    change -(bitValue (modMulBits report.square.division.remainder x.marked modulus).division.remainder :
      ZMod (bitValue modulus))=_
    rw [modular_product_value]
    change -((bitValue (modMulBits report.inverse.coefficient report.inverse.coefficient modulus).division.remainder :
      ZMod (bitValue modulus))*(bitValue x.marked : ZMod (bitValue modulus)))=_
    rw [modular_product_value,pow_two]
  apply TrivSqZeroExt.ext
  · exact hinverse
  · change (bitValue report.inverse.coefficient : ZMod (bitValue modulus))*
      (bitValue x.marked : ZMod (bitValue modulus))+
      (bitValue report.word.marked : ZMod (bitValue modulus))*(bitValue x.scalar : ZMod (bitValue modulus))=0
    rw [hmark]
    linear_combination -(bitValue report.inverse.coefficient : ZMod (bitValue modulus))*
      (bitValue x.marked : ZMod (bitValue modulus))*hinverse

/-- The full computed inverse/correction/gate clock is cubic in physical
width. Both output residues are canonical even on a rejected unit gate. -/
theorem markedInverseBits_cost_width {modulus : List Bool} (hN : 0<bitValue modulus)
    (x : MarkedWord) (W : ℕ) (hm : modulus.length≤W) (hx : x.Bounded W) :
    (markedInverseBits modulus x).clock≤6000*(W+1)^3 ∧
    (markedInverseBits modulus x).word.Bounded W ∧
    (markedInverseBits modulus x).word.Canonical modulus := by
  have hi := inverseBits_cost hN hm hx.1
  have hiw := inverseBits_width hN x.scalar
  have hgate := isOneBits_cost (hiw.1.trans hm)
  have hs := bounded_modMulBits (hiw.2.trans hm) (hiw.2.trans hm) hm
  have hsw : (modMulBits (inverseBits modulus x.scalar).coefficient
      (inverseBits modulus x.scalar).coefficient modulus).division.remainder.length≤W := by
    rw [modMulBits_width hN]; exact hm
  have hp := bounded_modMulBits hsw hx.2 hm
  have hpw : (modMulBits (modMulBits (inverseBits modulus x.scalar).coefficient
      (inverseBits modulus x.scalar).coefficient modulus).division.remainder x.marked
      modulus).division.remainder.length≤W := by rw [modMulBits_width hN]; exact hm
  have hn := negateResidueBits_cost hm hpw
  refine ⟨?_,⟨hiw.2.trans hm,?_⟩,⟨inverseBits_coefficient_lt hN _,?_⟩⟩
  · dsimp only [markedInverseBits]
    nlinarith only [hi,hgate,hs,hp,hn,Nat.zero_le W]
  · change (negateResidueBits modulus (modMulBits (modMulBits
      (inverseBits modulus x.scalar).coefficient (inverseBits modulus x.scalar).coefficient
      modulus).division.remainder x.marked modulus).division.remainder).reduction.remainder.length≤W
    rw [negateResidueBits_width hN]
    exact hm
  · change bitValue (divideBits
      (subBits modulus (modMulBits (modMulBits (inverseBits modulus x.scalar).coefficient
        (inverseBits modulus x.scalar).coefficient modulus).division.remainder x.marked
        modulus).division.remainder false).result.bits modulus).remainder<bitValue modulus
    rw [(divideBits_correct _ _).2]; exact Nat.mod_lt _ hN

/-- Actual counter scan/update and the original marked initial products. -/
structure MarkedInitFrame where
  /-- Complete scan of the current physical count. -/
  scan : NonzeroReport
  /-- Actual Boolean decrement controlling the child call. -/
  decrement : SubReport
  /-- Both negated original power channels. -/
  negative : MarkedNegationReport
  /-- Original constant and its marked variation. -/
  constant : MarkedProductReport
  /-- Next original power and its literal exponent mark. -/
  power : MarkedProductReport

/-- Actual marked powers, constant, visited frames and primitive work. -/
structure MarkedInitReport where
  /-- Ordered original first-order powers. -/
  powers : List MarkedWord
  /-- Actual final power and its original logarithmic variation. -/
  power : MarkedWord
  /-- Actual original constant coefficient and base-derivative coefficient. -/
  constant : MarkedWord
  /-- Every actual counter-controlled visit. -/
  frames : List MarkedInitFrame
  /-- Complete final zero-counter scan. -/
  finalScan : NonzeroReport
  /-- All scalar circuits, counter work and retained references. -/
  clock : ℕ

/-- Construct marked powers and the original marked constant coefficient.
Only computed Boolean scans and decrements control the count. -/
def markedInitLoop (modulus : List Bool) (alpha power constant : MarkedWord)
    (remaining : List Bool) : MarkedInitReport :=
  let scan := nonzeroBits remaining
  if hs : scan.nonzero=true then
    let decrement := subBits remaining [true] false
    let negative := markedNegateBits modulus power
    let nextConstant := markedMulBits modulus constant negative.word
    let nextPower := markedMulBits modulus power alpha
    let child := markedInitLoop modulus alpha nextPower.word nextConstant.word decrement.result.bits
    ⟨nextPower.word::child.powers,child.power,child.constant,
      ⟨scan,decrement,negative,nextConstant,nextPower⟩::child.frames,child.finalScan,
      scan.clock+bitCost decrement.result+negative.clock+nextConstant.clock+nextPower.clock+child.clock+14⟩
  else ⟨[],power,constant,[],scan,scan.clock+5⟩
termination_by bitValue remaining
decreasing_by
  have hp := (nonzeroBits_correct remaining).mp hs
  rw [(decrementBits_value hp).2]
  omega

/-- Both original constant channels and the ordered first-order powers
are computed by the actual initializer, including zero count and padding. -/
theorem markedInitLoop_exact {modulus : List Bool} (hN : 0<bitValue modulus)
    (alpha power constant : MarkedWord) (remaining : List Bool) (i : ℕ)
    (hp : power.Canonical modulus)
    (hpower : power.interpret modulus=alpha.interpret modulus^i)
    (hc : constant.interpret modulus=(rowPolynomial (alpha.interpret modulus) i).coeff 0) :
    (markedInitLoop modulus alpha power constant remaining).power.interpret modulus=
      alpha.interpret modulus^(i+bitValue remaining) ∧
    (markedInitLoop modulus alpha power constant remaining).constant.interpret modulus=
      (rowPolynomial (alpha.interpret modulus) (i+bitValue remaining)).coeff 0 ∧
    (markedInitLoop modulus alpha power constant remaining).powers.map (fun word => word.interpret modulus)=
      (List.range (bitValue remaining)).map (fun k => alpha.interpret modulus^(i+k+1)) := by
  generalize he : bitValue remaining=n at *
  induction n using Nat.strong_induction_on generalizing power constant remaining i with
  | h n ih =>
    by_cases hs : (nonzeroBits remaining).nonzero=true
    · have hn := (nonzeroBits_correct remaining).mp hs
      let decrement := subBits remaining [true] false
      let negative := markedNegateBits modulus power
      let nextConstant := markedMulBits modulus constant negative.word
      let nextPower := markedMulBits modulus power alpha
      have hd : bitValue decrement.result.bits=n-1 := by
        exact (decrementBits_value hn).2.trans (by rw [he])
      have hn' : bitValue decrement.result.bits<n := by omega
      have hnext : nextPower.word.interpret modulus=alpha.interpret modulus^(i+1) := by
        change (markedMulBits modulus power alpha).word.interpret modulus=_
        rw [markedMulBits_value,hpower,pow_succ]
      have hconstant : nextConstant.word.interpret modulus=
          (rowPolynomial (alpha.interpret modulus) (i+1)).coeff 0 := by
        change (markedMulBits modulus constant negative.word).word.interpret modulus=_
        rw [markedMulBits_value,markedNegateBits_value _ _ hp,hpower,hc,geometric_constant_succ]
      have hnp : nextPower.word.Canonical modulus := markedMulBits_canonical hN power alpha
      have ht := ih _ hn' nextPower.word nextConstant.word decrement.result.bits (i+1) hnp hnext hconstant rfl
      have hi : i+1+bitValue decrement.result.bits=i+n := by omega
      rw [hi] at ht
      rw [markedInitLoop]
      dsimp only
      simp only [dif_pos hs]
      refine ⟨ht.1,ht.2.1,?_⟩
      change nextPower.word.interpret modulus::
        (markedInitLoop modulus alpha nextPower.word nextConstant.word decrement.result.bits).powers.map _=_
      rw [ht.2.2,hnext,hd]
      have hlen : n=(n-1)+1 := by omega
      conv_rhs => rw [hlen,List.range_succ_eq_map,List.map_cons,List.map_map]
      congr 1
      apply List.map_congr_left
      intro k _
      congr 1
      omega
    · have hn : n=0 := by have hz := counter_zero_of_clear hs; omega
      rw [markedInitLoop]
      dsimp only
      simp only [dif_neg hs,hn,List.range_zero,List.map_nil,Nat.add_zero]
      exact ⟨hpower,hc,trivial⟩

/-- The entire marked initializer has linear-in-count quadratic work,
exact visit/power counts and bounded physical output words. -/
theorem markedInitLoop_cost_width {W : ℕ} {modulus : List Bool}
    (hN : 0<bitValue modulus) (hW : 1≤W) (alpha power constant : MarkedWord)
    (remaining : List Bool) (hm : modulus.length≤W) (ha : alpha.Bounded W)
    (hp : power.Bounded W) (hc : constant.Bounded W) (hr : remaining.length≤W) :
    (markedInitLoop modulus alpha power constant remaining).clock≤
      (bitValue remaining+1)*(4000*(W+1)^2) ∧
    (markedInitLoop modulus alpha power constant remaining).power.Bounded W ∧
    (markedInitLoop modulus alpha power constant remaining).constant.Bounded W ∧
    (markedInitLoop modulus alpha power constant remaining).powers.length=bitValue remaining ∧
    (markedInitLoop modulus alpha power constant remaining).frames.length=bitValue remaining ∧
    ∀ word∈(markedInitLoop modulus alpha power constant remaining).powers, word.Bounded W := by
  generalize he : bitValue remaining=n at *
  induction n using Nat.strong_induction_on generalizing power constant remaining with
  | h n ih =>
    have hscan := nonzeroBits_cost remaining
    by_cases hs : (nonzeroBits remaining).nonzero=true
    · have hn := (nonzeroBits_correct remaining).mp hs
      let decrement := subBits remaining [true] false
      let negative := markedNegateBits modulus power
      let nextConstant := markedMulBits modulus constant negative.word
      let nextPower := markedMulBits modulus power alpha
      have hd : bitValue decrement.result.bits=n-1 := by
        exact (decrementBits_value hn).2.trans (by rw [he])
      have hdec : decrement.result.bits.length≤W := by
        rw [(subBits_counts remaining [true] false).2.2.2.2]
        exact max_le hr (by simpa only [List.length_cons,List.length_nil] using hW)
      have hneg := markedNegateBits_cost_width hN power W hm hp
      have hnegWidth : negative.word.Bounded W :=
        ⟨by rw [hneg.2.1]; exact hm,by rw [hneg.2.2.1]; exact hm⟩
      have hnextPower := markedMulBits_cost_width hN power alpha W hm hp ha
      have hnextConstant := markedMulBits_cost_width hN constant negative.word W hm hc hnegWidth
      have hnp : nextPower.word.Bounded W :=
        ⟨by rw [hnextPower.2.1]; exact hm,by rw [hnextPower.2.2.1]; exact hm⟩
      have hnc : nextConstant.word.Bounded W :=
        ⟨by rw [hnextConstant.2.1]; exact hm,by rw [hnextConstant.2.2.1]; exact hm⟩
      have ht := ih _ (by omega : bitValue decrement.result.bits<n) nextPower.word
        nextConstant.word decrement.result.bits hnp hnc hdec rfl
      have hsub := subBits_cost remaining [true] false
      have hmax : max remaining.length ([true] : List Bool).length≤W :=
        max_le hr (by simpa only [List.length_cons,List.length_nil] using hW)
      have hframe : (nonzeroBits remaining).clock+bitCost decrement.result+negative.clock+
          nextConstant.clock+nextPower.clock+14≤4000*(W+1)^2 := by
        dsimp only [decrement,negative,nextConstant,nextPower] at *
        nlinarith only [hscan,hr,hsub,hmax,hneg.1,hnextPower.1,hnextConstant.1,hW]
      rw [markedInitLoop]
      dsimp only
      simp only [dif_pos hs,List.length_cons]
      refine ⟨?_,ht.2.1,ht.2.2.1,?_,?_,?_⟩
      · change (nonzeroBits remaining).clock+bitCost decrement.result+negative.clock+
          nextConstant.clock+nextPower.clock+
          (markedInitLoop modulus alpha nextPower.word nextConstant.word decrement.result.bits).clock+14≤_
        have hclock := ht.1
        have hcount : bitValue decrement.result.bits+1=n := by omega
        rw [hcount] at hclock
        calc
          _ ≤ 4000*(W+1)^2+n*(4000*(W+1)^2) := by omega
          _ = (n+1)*(4000*(W+1)^2) := by ring
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
      rw [markedInitLoop]
      dsimp only
      simp only [dif_neg hs,hn,List.length_nil]
      refine ⟨?_,hp,hc,trivial,trivial,?_⟩
      · simp only [Nat.zero_add,Nat.one_mul]
        nlinarith only [hscan,hr,hW]
      · intro word hw
        cases hw

/-- Every marked power and final state is a canonical actual residue,
including all intermediate powers emitted by the initializer. -/
theorem markedInitLoop_canonical {modulus : List Bool} (hN : 0<bitValue modulus)
    (alpha power constant : MarkedWord) (remaining : List Bool)
    (hp : power.Canonical modulus) (hc : constant.Canonical modulus) :
    (markedInitLoop modulus alpha power constant remaining).power.Canonical modulus ∧
    (markedInitLoop modulus alpha power constant remaining).constant.Canonical modulus ∧
    ∀ word∈(markedInitLoop modulus alpha power constant remaining).powers, word.Canonical modulus := by
  generalize he : bitValue remaining=n at *
  induction n using Nat.strong_induction_on generalizing power constant remaining with
  | h n ih =>
    by_cases hs : (nonzeroBits remaining).nonzero=true
    · have hn := (nonzeroBits_correct remaining).mp hs
      let decrement := subBits remaining [true] false
      let negative := markedNegateBits modulus power
      let nextConstant := markedMulBits modulus constant negative.word
      let nextPower := markedMulBits modulus power alpha
      have hd : bitValue decrement.result.bits<n := by
        have hh := (decrementBits_value hn).2
        dsimp only [decrement]
        omega
      have hnextPower := markedMulBits_canonical hN power alpha
      have hnextConstant := markedMulBits_canonical hN constant negative.word
      have ht := ih _ hd nextPower.word nextConstant.word decrement.result.bits
        hnextPower hnextConstant rfl
      rw [markedInitLoop]
      dsimp only
      simp only [dif_pos hs]
      refine ⟨ht.1,ht.2.1,?_⟩
      intro word hw
      rcases List.mem_cons.mp hw with hsame|htail
      · subst word
        exact hnextPower
      · exact ht.2.2 word htail
    · rw [markedInitLoop]
      dsimp only
      simp only [dif_neg hs]
      exact ⟨hp,hc,by intro word hw; cases hw⟩

/-- Every actual scalar circuit in one marked coefficient recurrence. -/
structure MarkedCoefficientFrame where
  /-- Both channels of the original short power gap. -/
  gap : MarkedDifferenceReport
  /-- Both channels of the original recurrence numerator. -/
  numerator : MarkedDifferenceReport
  /-- Both channels of the constructed recurrence denominator. -/
  denominator : MarkedProductReport
  /-- Computed scalar inverse and first-order correction, with unit gate. -/
  inverse : MarkedInverseWordReport
  /-- Original numerator times the previous marked coefficient. -/
  product : MarkedProductReport
  /-- Original next coefficient and its logarithmic base variation. -/
  coefficient : MarkedProductReport
  /-- Every scalar circuit and retained recurrence/report reference. -/
  clock : ℕ

/-- Execute the original recurrence in computed first-order word pairs. -/
def markedCoefficientFrameBits (modulus : List Bool) (one top terminal power previous : MarkedWord) :
    MarkedCoefficientFrame :=
  let gap := markedDifferenceBits modulus power one
  let numerator := markedDifferenceBits modulus power terminal
  let denominator := markedMulBits modulus top gap.word
  let inverse := markedInverseBits modulus denominator.word
  let product := markedMulBits modulus numerator.word previous
  let coefficient := markedMulBits modulus product.word inverse.word
  ⟨gap,numerator,denominator,inverse,product,coefficient,
    gap.clock+numerator.clock+denominator.clock+inverse.clock+product.clock+coefficient.clock+11⟩

/-- The actual computed unit gate and inverse recover the exact original
first-order recurrence value, using no extra marked denominator inverse. -/
theorem markedCoefficientFrameBits_exact {modulus : List Bool} (hN : 0<bitValue modulus)
    (one top terminal power previous : MarkedWord) (ho : one.Canonical modulus)
    (ht : terminal.Canonical modulus) (hp : power.Canonical modulus)
    (hunit : IsUnit (top.interpret modulus*(power.interpret modulus-one.interpret modulus)))
    (expected : (ZMod (bitValue modulus))[ε])
    (hrec : top.interpret modulus*(power.interpret modulus-one.interpret modulus)*expected=
      (power.interpret modulus-terminal.interpret modulus)*previous.interpret modulus) :
    (markedCoefficientFrameBits modulus one top terminal power previous).inverse.unit.value=true ∧
    (markedCoefficientFrameBits modulus one top terminal power previous).coefficient.word.interpret modulus=expected := by
  let frame := markedCoefficientFrameBits modulus one top terminal power previous
  have hg : frame.gap.word.interpret modulus=power.interpret modulus-one.interpret modulus :=
    markedDifferenceBits_value hN power one hp ho
  have hn : frame.numerator.word.interpret modulus=power.interpret modulus-terminal.interpret modulus :=
    markedDifferenceBits_value hN power terminal hp ht
  have hd : frame.denominator.word.interpret modulus=
      top.interpret modulus*(power.interpret modulus-one.interpret modulus) := by
    change (markedMulBits modulus top frame.gap.word).word.interpret modulus=_
    rw [markedMulBits_value,hg]
  have hu : IsUnit (frame.denominator.word.interpret modulus) := by rw [hd]; exact hunit
  have hgate : frame.inverse.unit.value=true := (markedInverseBits_gate_iff hN _).mpr hu
  have hi : frame.inverse.word.interpret modulus*frame.denominator.word.interpret modulus=1 :=
    markedInverseBits_value hN _ hgate
  have hrec' : frame.denominator.word.interpret modulus*expected=
      frame.numerator.word.interpret modulus*previous.interpret modulus := by rw [hd,hn]; exact hrec
  refine ⟨hgate,?_⟩
  change (markedMulBits modulus frame.product.word frame.inverse.word).word.interpret modulus=expected
  rw [markedMulBits_value]
  change (markedMulBits modulus frame.numerator.word previous).word.interpret modulus*
    frame.inverse.word.interpret modulus=expected
  rw [markedMulBits_value,←hrec']
  calc
    _ = (frame.inverse.word.interpret modulus*frame.denominator.word.interpret modulus)*expected := by ring
    _ = expected := by rw [hi,one_mul]

/-- Every actual marked recurrence frame has cubic physical work,
fixed canonical coefficient widths and at most one scalar inverse. -/
theorem markedCoefficientFrameBits_cost_width {modulus : List Bool} (hN : 0<bitValue modulus)
    (one top terminal power previous : MarkedWord) (W : ℕ) (hm : modulus.length≤W)
    (ho : one.Bounded W) (hs : top.Bounded W) (ht : terminal.Bounded W)
    (hp : power.Bounded W) (hc : previous.Bounded W) :
    (markedCoefficientFrameBits modulus one top terminal power previous).clock≤12000*(W+1)^3 ∧
    (markedCoefficientFrameBits modulus one top terminal power previous).coefficient.word.scalar.length=modulus.length ∧
    (markedCoefficientFrameBits modulus one top terminal power previous).coefficient.word.marked.length=modulus.length ∧
    (markedCoefficientFrameBits modulus one top terminal power previous).coefficient.word.Canonical modulus := by
  let frame := markedCoefficientFrameBits modulus one top terminal power previous
  have hgap := markedDifferenceBits_cost_width hN power one W hm hp ho
  have hnum := markedDifferenceBits_cost_width hN power terminal W hm hp ht
  have hgw : frame.gap.word.Bounded W := ⟨hgap.2.1.le.trans hm,hgap.2.2.1.le.trans hm⟩
  have hnw : frame.numerator.word.Bounded W := ⟨hnum.2.1.le.trans hm,hnum.2.2.1.le.trans hm⟩
  have hden := markedMulBits_cost_width hN top frame.gap.word W hm hs hgw
  have hdw : frame.denominator.word.Bounded W := ⟨hden.2.1.le.trans hm,hden.2.2.1.le.trans hm⟩
  have hinv := markedInverseBits_cost_width hN frame.denominator.word W hm hdw
  have hprod := markedMulBits_cost_width hN frame.numerator.word previous W hm hnw hc
  have hpcw : frame.product.word.Bounded W := ⟨hprod.2.1.le.trans hm,hprod.2.2.1.le.trans hm⟩
  have hnext := markedMulBits_cost_width hN frame.product.word frame.inverse.word W hm hpcw hinv.2.1
  refine ⟨?_,hnext.2.1,hnext.2.2.1,hnext.2.2.2⟩
  change frame.gap.clock+frame.numerator.clock+frame.denominator.clock+frame.inverse.clock+
    frame.product.clock+frame.coefficient.clock+11≤_
  have hgapCost : frame.gap.clock≤900*(W+1)^2 := hgap.1
  have hnumCost : frame.numerator.clock≤900*(W+1)^2 := hnum.1
  have hdenCost : frame.denominator.clock≤1000*(W+1)^2 := hden.1
  have hinvCost : frame.inverse.clock≤6000*(W+1)^3 := hinv.1
  have hprodCost : frame.product.clock≤1000*(W+1)^2 := hprod.1
  have hnextCost : frame.coefficient.clock≤1000*(W+1)^2 := hnext.1
  nlinarith only [hgapCost,hnumCost,hdenCost,hinvCost,hprodCost,hnextCost,Nat.zero_le W]

/-- Accepted marked coefficient words, actual visit reports and full work. -/
structure MarkedCoefficientRunReport where
  /-- Original next coefficients, or none at the first rejected inverse. -/
  coefficients : Option (List MarkedWord)
  /-- Every visited update, including a failed scalar unit gate. -/
  frames : List MarkedCoefficientFrame
  /-- All actual scalar circuits and list/option decisions. -/
  clock : ℕ

/-- Walk only the actually computed original marked power source. -/
def markedCoefficientRunBits (modulus : List Bool) (one top terminal previous : MarkedWord) :
    List MarkedWord→MarkedCoefficientRunReport
  | [] => ⟨some [],[],3⟩
  | power::powers =>
    let frame := markedCoefficientFrameBits modulus one top terminal power previous
    if frame.inverse.unit.value=true then
      let child := markedCoefficientRunBits modulus one top terminal frame.coefficient.word powers
      let coefficients := child.coefficients.map (fun words => frame.coefficient.word::words)
      ⟨coefficients,frame::child.frames,frame.clock+child.clock+8⟩
    else ⟨none,[frame],frame.clock+5⟩

/-- The checked word-pair walk computes every original first-order
coefficient, including the marked base channel, without additional advice. -/
theorem markedCoefficientRunBits_exact {modulus : List Bool} (hN : 0<bitValue modulus)
    (one top terminal alpha : MarkedWord) (ho : one.Canonical modulus) (ht : terminal.Canonical modulus)
    (hone : one.interpret modulus=1) (s : ℕ) (htop : top.interpret modulus=alpha.interpret modulus^s)
    (hterminal : terminal.interpret modulus=alpha.interpret modulus^(s+1))
    (hunit : IsUnit (alpha.interpret modulus))
    (hgaps : ∀ j, 0<j→j≤s→IsUnit (alpha.interpret modulus^j-1))
    (powers : List MarkedWord) (previous : MarkedWord) (i : ℕ) (hcount : i+powers.length≤s)
    (hcur : previous.interpret modulus=(rowPolynomial (alpha.interpret modulus) s).coeff i)
    (hcanonical : ∀ word∈powers, word.Canonical modulus)
    (hvalues : powers.map (fun word => word.interpret modulus)=
      (List.range powers.length).map (fun k => alpha.interpret modulus^(i+k+1))) :
    ∃ coefficients, (markedCoefficientRunBits modulus one top terminal previous powers).coefficients=some coefficients ∧
      coefficients.map (fun word => word.interpret modulus)=
        (List.range powers.length).map (fun k => (rowPolynomial (alpha.interpret modulus) s).coeff (i+k+1)) := by
  induction powers generalizing previous i with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons power powers ih =>
    have hbound : i+1≤s := by simp only [List.length_cons] at hcount; omega
    have hp := hcanonical power List.mem_cons_self
    have hvt := hvalues
    rw [List.map_cons,List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map] at hvt
    have hpval : power.interpret modulus=alpha.interpret modulus^(i+1) := by
      simpa only [Nat.add_zero] using (List.cons.inj hvt).1
    have htail : powers.map (fun word => word.interpret modulus)=
        (List.range powers.length).map (fun k => alpha.interpret modulus^(i+1+k+1)) := by
      simpa only [Function.comp_def,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        using (List.cons.inj hvt).2
    have hdenUnit : IsUnit (top.interpret modulus*(power.interpret modulus-one.interpret modulus)) := by
      rw [htop,hpval,hone]
      exact (hunit.pow s).mul (hgaps (i+1) (by omega) hbound)
    have hrec : top.interpret modulus*(power.interpret modulus-one.interpret modulus)*
        (rowPolynomial (alpha.interpret modulus) s).coeff (i+1)=
        (power.interpret modulus-terminal.interpret modulus)*previous.interpret modulus := by
      rw [htop,hpval,hone,hterminal,hcur]
      exact geometric_coefficient_recurrence _ s i
    have hframe := markedCoefficientFrameBits_exact hN one top terminal power previous ho ht hp hdenUnit _ hrec
    have htcount : i+1+powers.length≤s := by simp only [List.length_cons] at hcount; omega
    obtain ⟨coefficients,hout,he⟩ := ih
      (markedCoefficientFrameBits modulus one top terminal power previous).coefficient.word (i+1) htcount
      hframe.2 (fun word hw => hcanonical word (List.mem_cons_of_mem power hw)) htail
    refine ⟨(markedCoefficientFrameBits modulus one top terminal power previous).coefficient.word::coefficients,?_,?_⟩
    · rw [markedCoefficientRunBits]
      dsimp only
      rw [if_pos hframe.1]
      simp only [hout,Option.map_some]
    · rw [List.map_cons,hframe.2,he,List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map]
      simp only [Nat.add_zero]
      congr 1
      apply List.map_congr_left
      intro k _
      congr 1
      omega

/-- The complete marked coefficient walk pays all successful or rejected
updates, and emits exactly one fixed-width word pair per accepted power. -/
theorem markedCoefficientRunBits_cost_width {modulus : List Bool} (hN : 0<bitValue modulus)
    (one top terminal previous : MarkedWord) (powers : List MarkedWord) (W : ℕ)
    (hm : modulus.length≤W) (ho : one.Bounded W) (hs : top.Bounded W) (ht : terminal.Bounded W)
    (hc : previous.Bounded W) (hp : ∀ word∈powers, word.Bounded W) :
    (markedCoefficientRunBits modulus one top terminal previous powers).clock≤
      (powers.length+1)*(13000*(W+1)^3) ∧
    (markedCoefficientRunBits modulus one top terminal previous powers).frames.length≤powers.length ∧
    ∀ coefficients, (markedCoefficientRunBits modulus one top terminal previous powers).coefficients=some coefficients→
      coefficients.length=powers.length ∧
      ∀ word∈coefficients, word.scalar.length=modulus.length ∧ word.marked.length=modulus.length := by
  induction powers generalizing previous with
  | nil =>
    refine ⟨?_,by simp only [markedCoefficientRunBits,List.length_nil,le_refl],?_⟩
    · simp only [markedCoefficientRunBits,List.length_nil,Nat.zero_add,Nat.one_mul]
      have hpow : 1≤(W+1)^3 := by
        have hh : 0<(W+1)^3 := by positivity
        omega
      omega
    · intro coefficients he
      simp only [markedCoefficientRunBits,Option.some.injEq] at he
      subst coefficients
      exact ⟨rfl,by intro word hw; cases hw⟩
  | cons power powers ih =>
    let frame := markedCoefficientFrameBits modulus one top terminal power previous
    have hf := markedCoefficientFrameBits_cost_width hN one top terminal power previous W hm ho hs ht
      (hp power List.mem_cons_self) hc
    have hw : frame.coefficient.word.Bounded W := ⟨hf.2.1.le.trans hm,hf.2.2.1.le.trans hm⟩
    have hr := ih frame.coefficient.word hw (fun word hword => hp word (List.mem_cons_of_mem power hword))
    rw [markedCoefficientRunBits]
    dsimp only
    by_cases hgate : frame.inverse.unit.value=true
    · rw [if_pos hgate]
      dsimp only
      refine ⟨?_,?_,?_⟩
      · change frame.clock+(markedCoefficientRunBits modulus one top terminal frame.coefficient.word powers).clock+8≤_
        have hframeCost : frame.clock≤12000*(W+1)^3 := hf.1
        simp only [List.length_cons]
        have hpow : 1≤(W+1)^3 := by
          have hh : 0<(W+1)^3 := by positivity
          omega
        have hrclock := hr.1
        calc
          _ ≤ 13000*(W+1)^3+(powers.length+1)*(13000*(W+1)^3) := by omega
          _ = (powers.length+1+1)*(13000*(W+1)^3) := by ring
      · change (markedCoefficientRunBits modulus one top terminal frame.coefficient.word powers).frames.length+1≤powers.length+1
        omega
      · intro coefficients he
        change (markedCoefficientRunBits modulus one top terminal frame.coefficient.word powers).coefficients.map
          (fun words => frame.coefficient.word::words)=some coefficients at he
        cases hout : (markedCoefficientRunBits modulus one top terminal frame.coefficient.word powers).coefficients with
        | none => simp only [hout,Option.map_none,reduceCtorEq] at he
        | some tail =>
          simp only [hout,Option.map_some,Option.some.injEq] at he
          subst coefficients
          have hh := hr.2.2 tail hout
          refine ⟨by simp only [List.length_cons,hh.1],?_⟩
          intro word hword
          rcases List.mem_cons.mp hword with hsame|htail
          · subst word
            exact ⟨hf.2.1,hf.2.2.1⟩
          · exact hh.2 word htail
    · rw [if_neg hgate]
      dsimp only
      refine ⟨?_,by simp only [List.length_cons,List.length_nil]; omega,?_⟩
      · have hframeCost : frame.clock≤12000*(W+1)^3 := hf.1
        have hpow : 1≤(W+1)^3 := by
          have hh : 0<(W+1)^3 := by positivity
          omega
        have hbudget : 1≤(power::powers).length+1 := by simp only [List.length_cons]; omega
        have hh := Nat.mul_le_mul_right (13000*(W+1)^3) hbudget
        omega
      · intro coefficients he
        cases he

/-- A paid marked product normalizes both physical components exactly. -/
theorem markedMulBits_width {modulus : List Bool} (hN : 0<bitValue modulus) (x y : MarkedWord) :
    (markedMulBits modulus x y).word.scalar.length=modulus.length ∧
    (markedMulBits modulus x y).word.marked.length=modulus.length := by
  exact ⟨modMulBits_width hN,
    (divideBits_widths (xs:=(addBits (modMulBits x.scalar y.marked modulus).division.remainder
      (modMulBits x.marked y.scalar modulus).division.remainder false).bits) hN).1⟩

/-- Exact normalization of both initial states is preserved through
every actual counter-controlled marked initializer update. -/
theorem markedInitLoop_width_exact {modulus : List Bool} (hN : 0<bitValue modulus)
    (alpha power constant : MarkedWord) (remaining : List Bool)
    (hp : power.scalar.length=modulus.length ∧ power.marked.length=modulus.length)
    (hc : constant.scalar.length=modulus.length ∧ constant.marked.length=modulus.length) :
    ((markedInitLoop modulus alpha power constant remaining).power.scalar.length=modulus.length ∧
      (markedInitLoop modulus alpha power constant remaining).power.marked.length=modulus.length) ∧
    ((markedInitLoop modulus alpha power constant remaining).constant.scalar.length=modulus.length ∧
      (markedInitLoop modulus alpha power constant remaining).constant.marked.length=modulus.length) := by
  generalize he : bitValue remaining=n at *
  induction n using Nat.strong_induction_on generalizing power constant remaining with
  | h n ih =>
    by_cases hs : (nonzeroBits remaining).nonzero=true
    · have hn := (nonzeroBits_correct remaining).mp hs
      let decrement := subBits remaining [true] false
      let negative := markedNegateBits modulus power
      let nextConstant := markedMulBits modulus constant negative.word
      let nextPower := markedMulBits modulus power alpha
      have hd : bitValue decrement.result.bits<n := by
        have hh := (decrementBits_value hn).2
        dsimp only [decrement]
        omega
      have ht := ih _ hd nextPower.word nextConstant.word decrement.result.bits
        (markedMulBits_width hN _ _) (markedMulBits_width hN _ _) rfl
      rw [markedInitLoop]
      dsimp only
      simp only [dif_pos hs]
      exact ht
    · rw [markedInitLoop]
      dsimp only
      simp only [dif_neg hs]
      exact ⟨hp,hc⟩

/-- Complete actual original value/base coefficient source and diagnostics. -/
structure MarkedGeometricCoefficientReport where
  /-- Full computation of the physically normalized scalar one. -/
  one : DivisionReport
  /-- Full computation of the physically normalized marked zero. -/
  zero : DivisionReport
  /-- Computed original marked powers and constant coefficient. -/
  initialization : MarkedInitReport
  /-- Computed terminal power in both original channels. -/
  terminal : MarkedProductReport
  /-- Full checked marked coefficient recurrence. -/
  recurrence : MarkedCoefficientRunReport
  /-- Actual original value/base coefficient pairs, including the constant. -/
  coefficients : Option (List MarkedWord)
  /-- Every scalar circuit, initialization, inverse gate and source decision. -/
  clock : ℕ

/-- Construct both original short-block coefficient channels from actual
Boolean modulus/base/count words. No marked coefficient or inverse is advice. -/
def markedGeometricCoefficientBits (modulus alpha count : List Bool) : MarkedGeometricCoefficientReport :=
  let one := divideBits [true] modulus
  let zero := divideBits [] modulus
  let initial : MarkedWord := ⟨one.remainder,zero.remainder⟩
  let base : MarkedWord := ⟨alpha,alpha⟩
  let initialization := markedInitLoop modulus base initial initial count
  let terminal := markedMulBits modulus initialization.power base
  let recurrence := markedCoefficientRunBits modulus initial initialization.power terminal.word
    initialization.constant initialization.powers
  let coefficients := recurrence.coefficients.map (fun words => initialization.constant::words)
  ⟨one,zero,initialization,terminal,recurrence,coefficients,
    one.clock+zero.clock+initialization.clock+terminal.clock+recurrence.clock+10⟩

/-- The actual normalized one/zero pair is the first-order unit. -/
theorem initialMarkedWord_value (modulus : List Bool) :
    (MarkedWord.mk (divideBits [true] modulus).remainder (divideBits [] modulus).remainder).interpret modulus=1 := by
  apply TrivSqZeroExt.ext
  · exact reduced_one_value modulus
  · change (bitValue (divideBits [] modulus).remainder : ZMod (bitValue modulus))=0
    rw [(divideBits_correct _ _).2,ZMod.natCast_mod]
    simp only [bitValue,Nat.cast_zero]

/-- Both initial components are computed canonical residue words. -/
theorem initialMarkedWord_canonical {modulus : List Bool} (hN : 0<bitValue modulus) :
    (MarkedWord.mk (divideBits [true] modulus).remainder (divideBits [] modulus).remainder).Canonical modulus := by
  constructor
  · rw [(divideBits_correct _ _).2]; exact Nat.mod_lt _ hN
  · rw [(divideBits_correct _ _).2]; exact Nat.mod_lt _ hN

/-- The complete actual source computes every original first-order
coefficient in order under the original scalar unit/power-gap conditions. -/
theorem markedGeometricCoefficientBits_dual_exact {modulus : List Bool} (hN : 0<bitValue modulus)
    (alpha count : List Bool) (ha : IsUnit (bitValue alpha : ZMod (bitValue modulus)))
    (hgaps : ∀ j, 0<j→j≤bitValue count→IsUnit ((bitValue alpha : ZMod (bitValue modulus))^j-1)) :
    ∃ coefficients, (markedGeometricCoefficientBits modulus alpha count).coefficients=some coefficients ∧
      coefficients.map (fun word => word.interpret modulus)=
        (List.range (bitValue count+1)).map
          (fun k => (rowPolynomial (markedBase (bitValue alpha : ZMod (bitValue modulus))) (bitValue count)).coeff k) := by
  let one := divideBits [true] modulus
  let zero := divideBits [] modulus
  let initial : MarkedWord := ⟨one.remainder,zero.remainder⟩
  let base : MarkedWord := ⟨alpha,alpha⟩
  let initialization := markedInitLoop modulus base initial initial count
  let terminal := markedMulBits modulus initialization.power base
  have hone : initial.interpret modulus=1 := initialMarkedWord_value modulus
  have hcan : initial.Canonical modulus := initialMarkedWord_canonical hN
  have hbase : base.interpret modulus=markedBase (bitValue alpha : ZMod (bitValue modulus)) := rfl
  have hstartPower : initial.interpret modulus=base.interpret modulus^0 := by rw [hone,pow_zero]
  have hstartConstant : initial.interpret modulus=(rowPolynomial (base.interpret modulus) 0).coeff 0 := by
    simpa only [rowPolynomial,SemiprimeCartesianCompletion.rootPolynomial,
      Finset.range_zero,Finset.prod_empty,coeff_one_zero] using hone
  have hi := markedInitLoop_exact hN base initial initial count 0 hcan hstartPower hstartConstant
  simp only [Nat.zero_add] at hi
  have hic := markedInitLoop_canonical hN base initial initial count hcan hcan
  have hlen : initialization.powers.length=bitValue count := by
    have he := congrArg List.length hi.2.2
    simpa only [List.length_map,List.length_range] using he
  have ht : terminal.word.interpret modulus=base.interpret modulus^(bitValue count+1) := by
    change (markedMulBits modulus initialization.power base).word.interpret modulus=_
    rw [markedMulBits_value,hi.1,pow_succ]
  have htc : terminal.word.Canonical modulus := markedMulBits_canonical hN _ _
  have hunit : IsUnit (base.interpret modulus) := by rw [hbase,markedBase_unit_iff]; exact ha
  have hgap : ∀ j, 0<j→j≤bitValue count→IsUnit (base.interpret modulus^j-1) := by
    intro j hj hjmax
    rw [hbase,markedBase_gap_unit_iff]
    exact hgaps j hj hjmax
  obtain ⟨coefficients,hout,he⟩ := markedCoefficientRunBits_exact hN initial initialization.power
    terminal.word base hcan htc hone (bitValue count) hi.1 ht hunit hgap
    initialization.powers initialization.constant 0 (by rw [hlen,Nat.zero_add]) hi.2.1 hic.2.2
    (by rw [hlen]; simpa only [Nat.zero_add] using hi.2.2)
  refine ⟨initialization.constant::coefficients,?_,?_⟩
  · change (markedCoefficientRunBits modulus initial initialization.power terminal.word
      initialization.constant initialization.powers).coefficients.map
        (fun words => initialization.constant::words)=_
    rw [hout]
    rfl
  · rw [List.map_cons,hi.2.1,he,hlen,List.range_succ_eq_map,List.map_cons,List.map_map]
    simp only [Nat.zero_add,hbase]
    rfl

/-- Every actual value/mark pair is exactly the coefficient of the
original value polynomial and ORIGINAL logarithmic BASE derivative. -/
theorem markedGeometricCoefficientBits_exact {modulus : List Bool} (hN : 0<bitValue modulus)
    (alpha count : List Bool) (ha : IsUnit (bitValue alpha : ZMod (bitValue modulus)))
    (hgaps : ∀ j, 0<j→j≤bitValue count→IsUnit ((bitValue alpha : ZMod (bitValue modulus))^j-1)) :
    ∃ coefficients, (markedGeometricCoefficientBits modulus alpha count).coefficients=some coefficients ∧
      coefficients.map (fun word =>
        ((bitValue word.scalar : ZMod (bitValue modulus)),(bitValue word.marked : ZMod (bitValue modulus))))=
        (List.range (bitValue count+1)).map
          (fun k => ((rowPolynomial (bitValue alpha : ZMod (bitValue modulus)) (bitValue count)).coeff k,
            (babyBasePolynomial (bitValue alpha : ZMod (bitValue modulus)) (bitValue count)).coeff k)) := by
  obtain ⟨coefficients,hout,he⟩ := markedGeometricCoefficientBits_dual_exact hN alpha count ha hgaps
  refine ⟨coefficients,hout,?_⟩
  have hp := congrArg (List.map (fun z : (ZMod (bitValue modulus))[ε] => (fst z,snd z))) he
  have hconvert : List.map (fun z : (ZMod (bitValue modulus))[ε] => (fst z,snd z))
      (coefficients.map (fun word => word.interpret modulus))=
      coefficients.map (fun word =>
        ((bitValue word.scalar : ZMod (bitValue modulus)),(bitValue word.marked : ZMod (bitValue modulus)))) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro word _
    rfl
  rw [hconvert] at hp
  simpa only [List.map_map,Function.comp_def,marked_coeff_value,marked_coeff_base] using hp

/-- The complete actual marked coefficient source has linear-in-degree
cubic primitive work, exact source counts and fixed physical pair widths. -/
theorem markedGeometricCoefficientBits_cost_width {modulus : List Bool} (hN : 0<bitValue modulus)
    (alpha count : List Bool) (W : ℕ) (hW : 1≤W) (hm : modulus.length≤W)
    (ha : alpha.length≤W) (hc : count.length≤W) :
    (markedGeometricCoefficientBits modulus alpha count).clock≤
      (bitValue count+1)*(20000*(W+1)^3) ∧
    (markedGeometricCoefficientBits modulus alpha count).initialization.powers.length=bitValue count ∧
    (markedGeometricCoefficientBits modulus alpha count).initialization.frames.length=bitValue count ∧
    ∀ coefficients, (markedGeometricCoefficientBits modulus alpha count).coefficients=some coefficients→
      coefficients.length=bitValue count+1 ∧
      ∀ word∈coefficients, word.scalar.length=modulus.length ∧ word.marked.length=modulus.length := by
  let one := divideBits [true] modulus
  let zero := divideBits [] modulus
  let initial : MarkedWord := ⟨one.remainder,zero.remainder⟩
  let base : MarkedWord := ⟨alpha,alpha⟩
  let initialization := markedInitLoop modulus base initial initial count
  let terminal := markedMulBits modulus initialization.power base
  let recurrence := markedCoefficientRunBits modulus initial initialization.power terminal.word
    initialization.constant initialization.powers
  have hiw : initial.scalar.length=modulus.length ∧ initial.marked.length=modulus.length :=
    ⟨(divideBits_widths (xs:=[true]) hN).1,(divideBits_widths (xs:=[]) hN).1⟩
  have hw : initial.Bounded W := ⟨hiw.1.le.trans hm,hiw.2.le.trans hm⟩
  have hbw : base.Bounded W := ⟨ha,ha⟩
  have hi := markedInitLoop_cost_width hN hW base initial initial count hm hbw hw hw hc
  have hterminal := markedMulBits_cost_width hN initialization.power base W hm hi.2.1 hbw
  have htw : terminal.word.Bounded W := ⟨hterminal.2.1.le.trans hm,hterminal.2.2.1.le.trans hm⟩
  have hr := markedCoefficientRunBits_cost_width hN initial initialization.power terminal.word
    initialization.constant initialization.powers W hm hw hi.2.1 htw hi.2.2.1 hi.2.2.2.2.2
  have honeCost := bounded_divideBits (by simp only [List.length_cons,List.length_nil]; omega :
    ([true] : List Bool).length≤3*W) hm
  have hzeroCost := bounded_divideBits (xs:=[]) (by simp only [List.length_nil]; omega) hm
  have honeBound : one.clock≤72*(W+1)^2 := honeCost
  have hzeroBound : zero.clock≤72*(W+1)^2 := hzeroCost
  have htBound : terminal.clock≤1000*(W+1)^2 := hterminal.1
  have hp : initialization.powers.length=bitValue count := hi.2.2.2.1
  have hf : initialization.frames.length=bitValue count := hi.2.2.2.2.1
  refine ⟨?_,hp,hf,?_⟩
  · change one.clock+zero.clock+initialization.clock+terminal.clock+recurrence.clock+10≤_
    have hinitCost : initialization.clock≤(bitValue count+1)*(4000*(W+1)^2) := hi.1
    have hrecCost : recurrence.clock≤(bitValue count+1)*(13000*(W+1)^3) := by
      have hh := hr.1
      rw [hp] at hh
      exact hh
    have hbaseBudget : (W+1)^2≤(W+1)^3 := by
      rw [pow_succ]
      exact Nat.le_mul_of_pos_right _ (by omega)
    have hslack : (bitValue count+1)*(4000*(W+1)^2)+144*(W+1)^2+
        1000*(W+1)^2+10≤(bitValue count+1)*(7000*(W+1)^3) := by
      have hh := Nat.mul_le_mul_right (4000*(W+1)^2) (show 1≤bitValue count+1 by omega)
      nlinarith only [hbaseBudget,hh,hW]
    calc
      _ ≤ (bitValue count+1)*(7000*(W+1)^3)+(bitValue count+1)*(13000*(W+1)^3) := by omega
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
      intro word hword
      rcases List.mem_cons.mp hword with hsame|htail
      · subst word
        exact (markedInitLoop_width_exact hN base initial initial count hiw hiw).2
      · exact hh.2 word htail

/-- Actual coefficient weighting and computed successor index. -/
structure TargetCoefficientFrame where
  /-- Original scalar coefficient times the computed index residue. -/
  product : ModularProduct
  /-- Paid modular increment of the actual index word. -/
  successor : CoefficientSumReport

/-- Constructed original target-derivative coefficient words and work. -/
structure TargetCoefficientRunReport where
  /-- Actual target-derivative words in original coefficient order. -/
  words : List (List Bool)
  /-- Every coefficient weighting and computed index increment. -/
  frames : List TargetCoefficientFrame
  /-- All scalar clocks and traversal/report references. -/
  clock : ℕ

/-- Weight actual original coefficients by a computed modular counter.
Both the index update and the unused final successor are paid. -/
def targetCoefficientRunBits (modulus one index : List Bool) : List MarkedWord→TargetCoefficientRunReport
  | [] => ⟨[],[],3⟩
  | coefficient::coefficients =>
    let product := modMulBits coefficient.scalar index modulus
    let successor := coefficientSumBits modulus index one
    let child := targetCoefficientRunBits modulus one successor.reduction.remainder coefficients
    ⟨product.division.remainder::child.words,⟨product,successor⟩::child.frames,
      product.clock+successor.clock+child.clock+8⟩

/-- Actual coefficient weighting is the original polynomial's target
derivative coefficient, including modular counter wrap and all padding. -/
theorem targetCoefficientRunBits_exact (modulus one index : List Bool)
    (hone : (bitValue one : ZMod (bitValue modulus))=1)
    (P : (ZMod (bitValue modulus))[X]) (coefficients : List MarkedWord) (i : ℕ)
    (hindex : (bitValue index : ZMod (bitValue modulus))=((i+1 : ℕ) : ZMod (bitValue modulus)))
    (hvalues : coefficients.map (fun word => (bitValue word.scalar : ZMod (bitValue modulus)))=
      (List.range coefficients.length).map (fun k => P.coeff (i+k+1))) :
    (targetCoefficientRunBits modulus one index coefficients).words.map
      (fun word => (bitValue word : ZMod (bitValue modulus)))=
      (List.range coefficients.length).map (fun k => P.derivative.coeff (i+k)) := by
  induction coefficients generalizing index i with
  | nil => rfl
  | cons coefficient coefficients ih =>
    have hv := hvalues
    rw [List.map_cons,List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map] at hv
    have hc : (bitValue coefficient.scalar : ZMod (bitValue modulus))=P.coeff (i+1) := by
      simpa only [Nat.add_zero] using (List.cons.inj hv).1
    have ht : coefficients.map (fun word => (bitValue word.scalar : ZMod (bitValue modulus)))=
        (List.range coefficients.length).map (fun k => P.coeff (i+1+k+1)) := by
      simpa only [Function.comp_def,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        using (List.cons.inj hv).2
    have hs : (bitValue (coefficientSumBits modulus index one).reduction.remainder : ZMod (bitValue modulus))=
        ((i+1+1 : ℕ) : ZMod (bitValue modulus)) := by
      rw [coefficientSumBits_value,hindex,hone]
      simp only [Nat.cast_add,Nat.cast_one]
    have hp : (bitValue (modMulBits coefficient.scalar index modulus).division.remainder : ZMod (bitValue modulus))=
        P.derivative.coeff i := by
      rw [modular_product_value,hc,hindex,coeff_derivative]
      simp only [Nat.cast_add,Nat.cast_one]
    rw [targetCoefficientRunBits]
    dsimp only
    rw [List.map_cons,hp,ih _ (i+1) hs ht,List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map]
    simp only [Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro k _
    congr 1
    omega

/-- The entire actual target-derivative coefficient walk has linear
quadratic primitive work, exact counts and fixed output word widths. -/
theorem targetCoefficientRunBits_cost_width {modulus : List Bool} (hN : 0<bitValue modulus)
    (one index : List Bool) (coefficients : List MarkedWord) (W : ℕ)
    (hm : modulus.length≤W) (ho : one.length≤W) (hi : index.length≤W)
    (hc : ∀ word∈coefficients, word.scalar.length≤W) :
    (targetCoefficientRunBits modulus one index coefficients).clock≤
      (coefficients.length+1)*(600*(W+1)^2) ∧
    (targetCoefficientRunBits modulus one index coefficients).words.length=coefficients.length ∧
    (targetCoefficientRunBits modulus one index coefficients).frames.length=coefficients.length ∧
    ∀ word∈(targetCoefficientRunBits modulus one index coefficients).words, word.length=modulus.length := by
  induction coefficients generalizing index with
  | nil =>
    refine ⟨?_,rfl,rfl,?_⟩
    · simp only [targetCoefficientRunBits,List.length_nil,Nat.zero_add,Nat.one_mul]
      nlinarith only [Nat.zero_le W]
    · intro word hw
      cases hw
  | cons coefficient coefficients ih =>
    let product := modMulBits coefficient.scalar index modulus
    let successor := coefficientSumBits modulus index one
    have hp := bounded_modMulBits (hc coefficient List.mem_cons_self) hi hm
    have hs := coefficientSumBits_cost_width hN index one W hm hi ho
    have hsw : successor.reduction.remainder.length≤W := hs.2.1.le.trans hm
    have ht := ih successor.reduction.remainder hsw
      (fun word hw => hc word (List.mem_cons_of_mem coefficient hw))
    have hframe : product.clock+successor.clock+8≤600*(W+1)^2 := by
      dsimp only [product,successor]
      nlinarith only [hp,hs.1,Nat.zero_le W]
    rw [targetCoefficientRunBits]
    dsimp only
    refine ⟨?_,?_,?_,?_⟩
    · change product.clock+successor.clock+
        (targetCoefficientRunBits modulus one successor.reduction.remainder coefficients).clock+8≤_
      have hclock := ht.1
      simp only [List.length_cons]
      calc
        _ ≤ 600*(W+1)^2+(coefficients.length+1)*(600*(W+1)^2) := by omega
        _ = (coefficients.length+1+1)*(600*(W+1)^2) := by ring
    · change (targetCoefficientRunBits modulus one successor.reduction.remainder coefficients).words.length+1=
        coefficients.length+1
      rw [ht.2.1]
    · change (targetCoefficientRunBits modulus one successor.reduction.remainder coefficients).frames.length+1=
        coefficients.length+1
      rw [ht.2.2.1]
    · intro word hw
      rcases List.mem_cons.mp hw with hsame|htail
      · subst word
        exact modMulBits_width hN
      · exact ht.2.2.2 word htail

/-- Actual three-channel coefficient preparation, including rejected source. -/
structure ThreeChannelCoefficientReport where
  /-- Full original value/base marked coefficient construction. -/
  source : MarkedGeometricCoefficientReport
  /-- Computed target-derivative coefficient report when the source accepts. -/
  target : Option TargetCoefficientRunReport
  /-- Original value/base pairs and actual target-derivative words. -/
  coefficients : Option (List MarkedWord×List (List Bool))
  /-- Full coefficient construction, weighting and source decisions. -/
  clock : ℕ

/-- Prepare all three original short-block polynomials from Boolean
modulus/base/count words. A failed scalar inverse retains its diagnostics. -/
def threeChannelCoefficientBits (modulus alpha count : List Bool) : ThreeChannelCoefficientReport :=
  let source := markedGeometricCoefficientBits modulus alpha count
  match source.coefficients with
  | none => ⟨source,none,none,source.clock+4⟩
  | some coefficients =>
    let target := targetCoefficientRunBits modulus source.one.remainder source.one.remainder coefficients.tail
    ⟨source,some target,some (coefficients,target.words),source.clock+target.clock+8⟩

/-- The actual complete source retains the value and marked base
polynomials and computes every target-derivative coefficient in order. -/
theorem threeChannelCoefficientBits_exact {modulus : List Bool} (hN : 0<bitValue modulus)
    (alpha count : List Bool) (ha : IsUnit (bitValue alpha : ZMod (bitValue modulus)))
    (hgaps : ∀ j, 0<j→j≤bitValue count→IsUnit ((bitValue alpha : ZMod (bitValue modulus))^j-1)) :
    ∃ coefficients target, (threeChannelCoefficientBits modulus alpha count).coefficients=some (coefficients,target) ∧
      coefficients.map (fun word =>
        ((bitValue word.scalar : ZMod (bitValue modulus)),(bitValue word.marked : ZMod (bitValue modulus))))=
        (List.range (bitValue count+1)).map
          (fun k => ((rowPolynomial (bitValue alpha : ZMod (bitValue modulus)) (bitValue count)).coeff k,
            (babyBasePolynomial (bitValue alpha : ZMod (bitValue modulus)) (bitValue count)).coeff k)) ∧
      target.map (fun word => (bitValue word : ZMod (bitValue modulus)))=
        (List.range (bitValue count)).map
          (fun k => (rowPolynomial (bitValue alpha : ZMod (bitValue modulus)) (bitValue count)).derivative.coeff k) := by
  let source := markedGeometricCoefficientBits modulus alpha count
  obtain ⟨coefficients,hout,he⟩ := markedGeometricCoefficientBits_exact hN alpha count ha hgaps
  have hlen : coefficients.length=bitValue count+1 := by
    have hh := congrArg List.length he
    simpa only [List.length_map,List.length_range] using hh
  have hscalar : coefficients.map (fun word => (bitValue word.scalar : ZMod (bitValue modulus)))=
      (List.range (bitValue count+1)).map
        (fun k => (rowPolynomial (bitValue alpha : ZMod (bitValue modulus)) (bitValue count)).coeff k) := by
    have hh := congrArg (List.map Prod.fst) he
    simpa only [List.map_map,Function.comp_def] using hh
  have hone : (bitValue source.one.remainder : ZMod (bitValue modulus))=1 := reduced_one_value modulus
  have htailLength : coefficients.tail.length=bitValue count := by rw [List.length_tail,hlen]; omega
  have htail : coefficients.tail.map (fun word => (bitValue word.scalar : ZMod (bitValue modulus)))=
      (List.range coefficients.tail.length).map
        (fun k => (rowPolynomial (bitValue alpha : ZMod (bitValue modulus)) (bitValue count)).coeff (0+k+1)) := by
    cases coefficients with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons head tail =>
      rw [List.map_cons,List.range_succ_eq_map,List.map_cons,List.map_map] at hscalar
      have hh := (List.cons.inj hscalar).2
      rw [htailLength]
      simpa only [List.tail_cons,Function.comp_def,Nat.succ_eq_add_one,Nat.zero_add] using hh
  have ht := targetCoefficientRunBits_exact modulus source.one.remainder source.one.remainder hone
    (rowPolynomial (bitValue alpha : ZMod (bitValue modulus)) (bitValue count)) coefficients.tail 0
    (by simpa only [Nat.zero_add,Nat.cast_one] using hone) htail
  refine ⟨coefficients,(targetCoefficientRunBits modulus source.one.remainder source.one.remainder coefficients.tail).words,
    ?_,he,?_⟩
  · have hout' : (markedGeometricCoefficientBits modulus alpha count).coefficients=some coefficients := hout
    rw [threeChannelCoefficientBits]
    dsimp only
    rw [hout']
  · simpa only [htailLength,Nat.zero_add] using ht

/-- All three actual coefficient channels have a complete linear-in-degree
primitive bit clock and exact counts/physical widths on accepted sources. -/
theorem threeChannelCoefficientBits_cost_width {modulus : List Bool} (hN : 0<bitValue modulus)
    (alpha count : List Bool) (W : ℕ) (hW : 1≤W) (hm : modulus.length≤W)
    (ha : alpha.length≤W) (hc : count.length≤W) :
    (threeChannelCoefficientBits modulus alpha count).clock≤
      (bitValue count+1)*(22000*(W+1)^3) ∧
    ∀ coefficients target, (threeChannelCoefficientBits modulus alpha count).coefficients=some (coefficients,target)→
      coefficients.length=bitValue count+1 ∧ target.length=bitValue count ∧
      (∀ word∈coefficients, word.scalar.length=modulus.length ∧ word.marked.length=modulus.length) ∧
      (∀ word∈target, word.length=modulus.length) := by
  let source := markedGeometricCoefficientBits modulus alpha count
  have hs := markedGeometricCoefficientBits_cost_width hN alpha count W hW hm ha hc
  have hsourceClock : source.clock≤(bitValue count+1)*(20000*(W+1)^3) := hs.1
  have honeWidth : source.one.remainder.length≤W := (divideBits_widths (xs:=[true]) hN).1.le.trans hm
  have hpositive : 1≤(W+1)^3 := by
    have hh : 0<(W+1)^3 := by positivity
    omega
  cases hout : source.coefficients with
  | none =>
    have hout' : (markedGeometricCoefficientBits modulus alpha count).coefficients=none := hout
    have hclock : (threeChannelCoefficientBits modulus alpha count).clock=source.clock+4 := by
      rw [threeChannelCoefficientBits]
      dsimp only
      rw [hout']
    rw [hclock]
    refine ⟨?_,?_⟩
    · have hcount : 1≤bitValue count+1 := by omega
      nlinarith only [hsourceClock,hpositive,hcount]
    · intro coefficients target he
      rw [threeChannelCoefficientBits] at he
      dsimp only at he
      rw [hout'] at he
      cases he
  | some coefficients =>
    have hout' : (markedGeometricCoefficientBits modulus alpha count).coefficients=some coefficients := hout
    have hw := hs.2.2.2 coefficients hout
    have hlen : coefficients.tail.length=bitValue count := by rw [List.length_tail,hw.1]; omega
    have hcTail : ∀ word∈coefficients.tail, word.scalar.length≤W := by
      intro word hword
      exact (hw.2 word (List.mem_of_mem_tail hword)).1.le.trans hm
    have ht := targetCoefficientRunBits_cost_width hN source.one.remainder source.one.remainder
      coefficients.tail W hm honeWidth honeWidth hcTail
    have hclock : (threeChannelCoefficientBits modulus alpha count).clock=source.clock+
        (targetCoefficientRunBits modulus source.one.remainder source.one.remainder coefficients.tail).clock+8 := by
      rw [threeChannelCoefficientBits]
      dsimp only
      rw [hout']
    rw [hclock]
    refine ⟨?_,?_⟩
    · have htClock : (targetCoefficientRunBits modulus source.one.remainder source.one.remainder coefficients.tail).clock≤
          (bitValue count+1)*(600*(W+1)^2) := by rw [←hlen]; exact ht.1
      have hbase : (W+1)^2≤(W+1)^3 := by
        rw [pow_succ]; exact Nat.le_mul_of_pos_right _ (by omega)
      have hslack : (bitValue count+1)*(600*(W+1)^2)+8≤(bitValue count+1)*(2000*(W+1)^3) := by
        have hh := Nat.mul_le_mul_right (600*(W+1)^2) (show 1≤bitValue count+1 by omega)
        nlinarith only [hbase,hh,hW]
      calc
        _ ≤ (bitValue count+1)*(20000*(W+1)^3)+(bitValue count+1)*(2000*(W+1)^3) := by omega
        _ = _ := by ring
    · intro output target he
      rw [threeChannelCoefficientBits] at he
      dsimp only at he
      rw [hout'] at he
      cases he
      exact ⟨hw.1,ht.2.1.trans hlen,hw.2,ht.2.2.2⟩

/-- The original long-route gap theorem certifies all three actual
short-block coefficient channels without any marked inverse advice. -/
theorem long_original_three_channel_coefficients {p q m W : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : SemiprimeLocalOrderRouting.LongData g m)
    (modulus alpha count : List Bool) (hmod : bitValue modulus=p*q)
    (halpha : (bitValue alpha : ZMod (p*q))=
      ((SemiprimeSeedSumAcquisition.seedBase (SemiprimeCentreFreeCover.projectedUnit g m) m :
        (ZMod (p*q))ˣ) : ZMod (p*q)))
    (hcount : bitValue count≤seedHalfLength m) (hW : 1≤W)
    (hmodWidth : modulus.length≤W) (halphaWidth : alpha.length≤W) (hcountWidth : count.length≤W) :
    ∃ coefficients target, (threeChannelCoefficientBits modulus alpha count).coefficients=some (coefficients,target) ∧
      coefficients.map (fun word =>
        ((bitValue word.scalar : ZMod (p*q)),(bitValue word.marked : ZMod (p*q))))=
        (List.range (bitValue count+1)).map
          (fun k => ((rowPolynomial
            ((SemiprimeSeedSumAcquisition.seedBase (SemiprimeCentreFreeCover.projectedUnit g m) m :
              (ZMod (p*q))ˣ) : ZMod (p*q)) (bitValue count)).coeff k,
            (babyBasePolynomial
              ((SemiprimeSeedSumAcquisition.seedBase (SemiprimeCentreFreeCover.projectedUnit g m) m :
                (ZMod (p*q))ˣ) : ZMod (p*q)) (bitValue count)).coeff k)) ∧
      target.map (fun word => (bitValue word : ZMod (p*q)))=
        (List.range (bitValue count)).map
          (fun k => (rowPolynomial
            ((SemiprimeSeedSumAcquisition.seedBase (SemiprimeCentreFreeCover.projectedUnit g m) m :
              (ZMod (p*q))ˣ) : ZMod (p*q)) (bitValue count)).derivative.coeff k) ∧
      coefficients.length=bitValue count+1 ∧ target.length=bitValue count ∧
      (∀ word∈coefficients, word.scalar.length=modulus.length ∧ word.marked.length=modulus.length) ∧
      (∀ word∈target, word.length=modulus.length) ∧
      (threeChannelCoefficientBits modulus alpha count).clock≤
        (bitValue count+1)*(22000*(W+1)^3) := by
  have hN : 0<bitValue modulus := by rw [hmod]; exact Nat.mul_pos hp.pos hq.pos
  have hunit : IsUnit (bitValue alpha : ZMod (bitValue modulus)) := by
    rw [hmod,halpha]
    exact (SemiprimeSeedSumAcquisition.seedBase (SemiprimeCentreFreeCover.projectedUnit g m) m).isUnit
  have hgaps : ∀ j, 0<j→j≤bitValue count→IsUnit ((bitValue alpha : ZMod (bitValue modulus))^j-1) := by
    intro j hj hjmax
    rw [hmod,halpha]
    exact long_seedHalf_power_gaps_unit hp hq hm g hlong j hj (hjmax.trans hcount)
  obtain ⟨coefficients,target,hout,he,ht⟩ := threeChannelCoefficientBits_exact hN alpha count hunit hgaps
  rw [hmod,halpha] at he ht
  have hc := threeChannelCoefficientBits_cost_width hN alpha count W hW hmodWidth halphaWidth hcountWidth
  have hw := hc.2 coefficients target hout
  exact ⟨coefficients,target,hout,he,ht,hw.1,hw.2.1,hw.2.2.1,hw.2.2.2,hc.1⟩

/-- At the actual public row modulus, all three original two-modulus
block coefficient channels have a near-linear primitive bit clock.
Public word generation, fast evaluation and the complete detector remain
separate obligations. -/
theorem public_short_block_three_channel_cost {p q W : ℕ} (hp : p.Prime) (hq : q.Prime)
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
    ∃ coefficients target, (threeChannelCoefficientBits modulus alpha count).coefficients=some (coefficients,target) ∧
      coefficients.length=2*SemiprimeEuclidRowBudget.publicRowModulus (p*q)+1 ∧
      target.length=2*SemiprimeEuclidRowBudget.publicRowModulus (p*q) ∧
      (∀ word∈coefficients, word.scalar.length=modulus.length ∧ word.marked.length=modulus.length) ∧
      (∀ word∈target, word.length=modulus.length) ∧
      (threeChannelCoefficientBits modulus alpha count).clock≤
        (4*SemiprimeLehmanCoverage.sixthWidth (p*q)+1)*(22000*(W+1)^3) := by
  have hN := Nat.mul_pos hp.pos hq.pos
  have hb := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 4≤SemiprimeEuclidRowBudget.publicRowModulus (p*q) := hB.trans hb.1
  obtain ⟨coefficients,target,hout,_,_,hlen,htlen,hw,htw,hc⟩ :=
    long_original_three_channel_coefficients hp hq hm g hlong modulus alpha count hmod halpha
      (by rw [hcount]; exact two_modulus_block_le_half hm) hW hmodWidth halphaWidth hcountWidth
  refine ⟨coefficients,target,hout,by rw [hcount] at hlen; exact hlen,
    by rw [hcount] at htlen; exact htlen,hw,htw,?_⟩
  apply hc.trans
  apply Nat.mul_le_mul_right
  rw [hcount]
  omega

end RiemannGaussian.SemiprimeBitGeometricMarks
