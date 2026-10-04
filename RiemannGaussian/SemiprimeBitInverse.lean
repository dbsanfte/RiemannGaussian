/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSeedFiniteTransfer
import RiemannGaussian.SemiprimeBitGcd
import RiemannGaussian.SemiprimeWindowInverse

/-!
# Boolean extended Euclid for marked derivative recovery

The data path computes its quotient, coefficient product, padded subtraction
and coefficient reduction with the frozen Boolean circuits. Natural arithmetic
occurs in specifications and clock instrumentation. The returned GCD is retained
for nonunits; only a GCD of one certifies an inverse. The public loop constructs
its own sufficient physical fuel. This scalar backend does not acquire the
original geometric interval jets or price the complete factorizer.
-/

namespace RiemannGaussian.SemiprimeBitInverse

open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitGcd
open SemiprimeWindowInverse

/-- The actual circuits and intermediate words of one coefficient update. -/
structure InverseFrame where
  /-- Euclidean quotient and remainder computed from the current remainder words. -/
  division : DivisionReport
  /-- Quotient times the second coefficient, reduced by the public modulus. -/
  product : ModularProduct
  /-- The first coefficient plus the modulus, computed by Boolean addition. -/
  padded : BitReport
  /-- Subtraction of the reduced product from that padded word. -/
  difference : SubReport
  /-- Reduction of the new coefficient to the modulus's physical width. -/
  reduction : DivisionReport
  /-- All circuit clocks and six retained call/frame cells. -/
  clock : ℕ

/-- Extended Euclid's coefficient update contains no native quotient,
remainder, multiplication or subtraction in its data path. -/
def makeInverseFrame (modulus r₀ r₁ c₀ c₁ : List Bool) : InverseFrame :=
  let division := divideBits r₀ r₁
  let product := modMulBits division.quotient c₁ modulus
  let padded := addBits c₀ modulus false
  let difference := subBits padded.bits product.division.remainder false
  let reduction := divideBits difference.result.bits modulus
  ⟨division,product,padded,difference,reduction,
    division.clock+product.clock+bitCost padded+bitCost difference.result+reduction.clock+6⟩

/-- The reduced coefficient product is the exact natural specification. -/
theorem makeInverseFrame_product (modulus r₀ r₁ c₀ c₁ : List Bool) :
    bitValue (makeInverseFrame modulus r₀ r₁ c₀ c₁).product.division.remainder=
      (bitValue r₀/bitValue r₁*bitValue c₁)%bitValue modulus := by
  simp only [makeInverseFrame,modMulBits_correct,(divideBits_correct r₀ r₁).1]

/-- Padding really prevents underflow for every positive modulus, even
when the original coefficient or product carries arbitrary zero padding. -/
theorem makeInverseFrame_no_borrow {modulus : List Bool}
    (hN : 0<bitValue modulus) (r₀ r₁ c₀ c₁ : List Bool) :
    (makeInverseFrame modulus r₀ r₁ c₀ c₁).difference.borrow=false := by
  have hp := makeInverseFrame_product modulus r₀ r₁ c₀ c₁
  have ha : bitValue (addBits c₀ modulus false).bits=bitValue c₀+bitValue modulus := by
    simpa only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] using
      addBits_correct c₀ modulus false
  have hm := Nat.mod_lt (bitValue r₀/bitValue r₁*bitValue c₁) hN
  cases hb : (makeInverseFrame modulus r₀ r₁ c₀ c₁).difference.borrow with
  | false => rfl
  | true =>
    have hl := (subBits_borrow_iff (addBits c₀ modulus false).bits
      (modMulBits (divideBits r₀ r₁).quotient c₁ modulus).division.remainder false).mp hb
    simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero,ha] at hl
    change bitValue c₀+bitValue modulus<
      bitValue (makeInverseFrame modulus r₀ r₁ c₀ c₁).product.division.remainder at hl
    rw [hp] at hl
    omega

/-- All three output values refine the frozen verified arithmetic frame.
That frame is a proof specification, never an executable inverse oracle. -/
theorem makeInverseFrame_exact {modulus : List Bool} (hN : 0<bitValue modulus)
    (r₀ r₁ c₀ c₁ : List Bool) :
    bitValue (makeInverseFrame modulus r₀ r₁ c₀ c₁).division.quotient=bitValue r₀/bitValue r₁ ∧
    bitValue (makeInverseFrame modulus r₀ r₁ c₀ c₁).division.remainder=bitValue r₀%bitValue r₁ ∧
    bitValue (makeInverseFrame modulus r₀ r₁ c₀ c₁).reduction.remainder=
      (makeFrame (bitValue modulus) (bitValue r₀) (bitValue r₁) (bitValue c₀) (bitValue c₁)).nextCoefficient := by
  refine ⟨(divideBits_correct r₀ r₁).1,(divideBits_correct r₀ r₁).2,?_⟩
  have hb := makeInverseFrame_no_borrow hN r₀ r₁ c₀ c₁
  have hs := subBits_difference hb
  change bitValue (makeInverseFrame modulus r₀ r₁ c₀ c₁).difference.result.bits=
    bitValue (addBits c₀ modulus false).bits-
      bitValue (makeInverseFrame modulus r₀ r₁ c₀ c₁).product.division.remainder at hs
  have ha : bitValue (addBits c₀ modulus false).bits=bitValue c₀+bitValue modulus := by
    simpa only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] using
      addBits_correct c₀ modulus false
  have hp := makeInverseFrame_product modulus r₀ r₁ c₀ c₁
  change bitValue (divideBits
    (makeInverseFrame modulus r₀ r₁ c₀ c₁).difference.result.bits modulus).remainder=_
  rw [(divideBits_correct _ modulus).2,hs,ha,hp]
  rfl

/-- Two actual output words, the composed clock and an explicit exhaustion flag. -/
structure InverseBitsReport where
  /-- The Euclidean GCD word, retained also when the input is a nonunit. -/
  gcd : List Bool
  /-- The coefficient multiplying the original input to give that GCD modulo N. -/
  coefficient : List Bool
  /-- Boolean/cell/test work, including every modular coefficient update. -/
  clock : ℕ
  /-- The number of positive Euclidean remainder steps. -/
  steps : ℕ
  /-- Insufficient arbitrary supplied fuel is never silently called an inverse. -/
  exhausted : Bool

/-- Fuelled extended Euclid on Boolean words. Only its Euclidean remainder
pair controls branching; coefficient updates use the actual charged circuits. -/
def inverseLoop (modulus r₀ r₁ c₀ c₁ : List Bool) : List Unit→InverseBitsReport
  | [] => ⟨r₀,c₀,1,0,true⟩
  | _::fuel =>
    let check := nonzeroBits r₁
    if check.nonzero=true then
      let frame := makeInverseFrame modulus r₀ r₁ c₀ c₁
      let child := inverseLoop modulus r₁ frame.division.remainder c₁ frame.reduction.remainder fuel
      ⟨child.gcd,child.coefficient,check.clock+frame.clock+child.clock+3,
        child.steps+1,child.exhausted⟩
    else
      ⟨r₀,c₀,check.clock+3,0,false⟩

/-- Coefficient arithmetic does not alter the literal GCD loop's stopping
condition. Its existing sufficient-fuel theorem therefore applies. -/
theorem inverseLoop_exhausted (modulus r₀ r₁ c₀ c₁ : List Bool) (fuel : List Unit) :
    (inverseLoop modulus r₀ r₁ c₀ c₁ fuel).exhausted=(gcdLoop r₀ r₁ fuel).exhausted := by
  induction fuel generalizing r₀ r₁ c₀ c₁ with
  | nil => rfl
  | cons cell fuel ih =>
    by_cases hb : (nonzeroBits r₁).nonzero=true
    · simp only [inverseLoop,gcdLoop,if_pos hb,makeInverseFrame]
      exact ih _ _ _ _
    · simp only [inverseLoop,gcdLoop,if_neg hb]

/-- A stopped bit loop returns exactly the GCD and coefficient of the
verified arithmetic loop. No coefficient advice is supplied as input. -/
theorem inverseLoop_refines {modulus : List Bool} (hN : 0<bitValue modulus)
    (r₀ r₁ c₀ c₁ : List Bool) (fuel : List Unit)
    (hstop : (inverseLoop modulus r₀ r₁ c₀ c₁ fuel).exhausted=false) :
    bitValue (inverseLoop modulus r₀ r₁ c₀ c₁ fuel).gcd=
      (euclidLoop (bitValue modulus) (bitValue r₀) (bitValue r₁) (bitValue c₀) (bitValue c₁)).gcd ∧
    bitValue (inverseLoop modulus r₀ r₁ c₀ c₁ fuel).coefficient=
      (euclidLoop (bitValue modulus) (bitValue r₀) (bitValue r₁) (bitValue c₀) (bitValue c₁)).coefficient := by
  induction fuel generalizing r₀ r₁ c₀ c₁ with
  | nil => simp only [inverseLoop,Bool.true_eq_false] at hstop
  | cons cell fuel ih =>
    by_cases hb : (nonzeroBits r₁).nonzero=true
    · have hpos := (nonzeroBits_correct r₁).mp hb
      have hc : (inverseLoop modulus r₁
          (makeInverseFrame modulus r₀ r₁ c₀ c₁).division.remainder c₁
          (makeInverseFrame modulus r₀ r₁ c₀ c₁).reduction.remainder fuel).exhausted=false := by
        simpa only [inverseLoop,if_pos hb] using hstop
      have ht := ih _ _ _ _ hc
      obtain ⟨_,hr,he⟩ := makeInverseFrame_exact hN r₀ r₁ c₀ c₁
      rw [hr,he] at ht
      rw [inverseLoop,if_pos hb,euclidLoop,dif_neg (by omega : bitValue r₁≠0)]
      exact ht
    · have hz : bitValue r₁=0 := by
        have hn : ¬0<bitValue r₁ := by
          intro hp
          exact hb ((nonzeroBits_correct r₁).mpr hp)
        omega
      simp only [inverseLoop,if_neg hb]
      rw [euclidLoop,dif_pos hz]
      exact ⟨rfl,rfl⟩

/-- Public inversion normalizes its input and literal one with charged
division, constructs physical fuel, and retains a GCD for every nonunit. -/
def inverseBits (modulus input : List Bool) : InverseBitsReport :=
  let normal := divideBits input modulus
  let one := divideBits [true] modulus
  let fuel := buildGcdFuel modulus normal.remainder
  let child := inverseLoop modulus modulus normal.remainder [] one.remainder fuel.cells
  {child with clock := child.clock+normal.clock+one.clock+fuel.clock+7}

/-- Its self-constructed fuel always suffices, even on a zero modulus or input. -/
theorem inverseBits_stops (modulus input : List Bool) :
    (inverseBits modulus input).exhausted=false := by
  have hf := (buildGcdFuel_counts modulus (divideBits input modulus).remainder).1
  have hs := (gcdLoop_stops_pow (divideBits input modulus).remainder.length modulus
    (divideBits input modulus).remainder (buildGcdFuel modulus (divideBits input modulus).remainder).cells
    (bitValue_lt_width _) (by omega)).1
  simpa only [inverseBits,inverseLoop_exhausted] using hs

/-- The actual coefficient and GCD refine countedInverse over a positive
modulus. The natural routine appears only on the specification side. -/
theorem inverseBits_refines {modulus : List Bool} (hN : 0<bitValue modulus) (input : List Bool) :
    bitValue (inverseBits modulus input).gcd=(countedInverse (bitValue modulus) (bitValue input)).gcd ∧
    bitValue (inverseBits modulus input).coefficient=
      (countedInverse (bitValue modulus) (bitValue input)).coefficient := by
  have hstop : (inverseLoop modulus modulus (divideBits input modulus).remainder []
      (divideBits [true] modulus).remainder
      (buildGcdFuel modulus (divideBits input modulus).remainder).cells).exhausted=false :=
    inverseBits_stops modulus input
  have he := inverseLoop_refines hN _ _ _ _ _ hstop
  rw [(divideBits_correct input modulus).2,(divideBits_correct [true] modulus).2] at he
  simpa only [inverseBits,countedInverse,bitValue,bitNat,if_true,Nat.mul_zero,Nat.add_zero] using he

/-- The returned Boolean GCD is the original input's GCD, including nonunits. -/
theorem inverseBits_gcd {modulus : List Bool} (hN : 0<bitValue modulus) (input : List Bool) :
    bitValue (inverseBits modulus input).gcd=(bitValue modulus).gcd (bitValue input) := by
  rw [(inverseBits_refines hN input).1,countedInverse_gcd]

/-- The computed coefficient satisfies the full modular GCD equation;
it is an inverse exactly on the GCD-one branch. -/
theorem inverseBits_correct {modulus : List Bool} (hN : 0<bitValue modulus) (input : List Bool) :
    ((bitValue (inverseBits modulus input).coefficient : ℕ) : ZMod (bitValue modulus))*
      (bitValue input : ZMod (bitValue modulus))=
      ((bitValue modulus).gcd (bitValue input) : ZMod (bitValue modulus)) := by
  rw [(inverseBits_refines hN input).2]
  exact countedInverse_correct hN (bitValue input)

/-- The returned coefficient is canonical for every positive modulus. -/
theorem inverseBits_coefficient_lt {modulus : List Bool} (hN : 0<bitValue modulus)
    (input : List Bool) : bitValue (inverseBits modulus input).coefficient<bitValue modulus := by
  rw [(inverseBits_refines hN input).2]
  exact countedInverse_coefficient_lt hN (bitValue input)

/-- Positive divisors retain the old remainder width and reduce the new
coefficient to the public modulus's width, with no free trimming. -/
theorem makeInverseFrame_widths {modulus r₁ : List Bool}
    (hN : 0<bitValue modulus) (hr : 0<bitValue r₁) (r₀ c₀ c₁ : List Bool) :
    (makeInverseFrame modulus r₀ r₁ c₀ c₁).division.remainder.length=r₁.length ∧
    (makeInverseFrame modulus r₀ r₁ c₀ c₁).reduction.remainder.length=modulus.length := by
  exact ⟨(divideBits_widths (xs:=r₀) hr).1,(divideBits_widths (xs:=
    (makeInverseFrame modulus r₀ r₁ c₀ c₁).difference.result.bits) hN).1⟩

/-- One coefficient update has a quadratic Boolean/cell/test cost,
including every quotient, product, padding, subtraction and reduction. -/
theorem makeInverseFrame_cost {L : ℕ} {modulus r₀ r₁ c₀ c₁ : List Bool}
    (hN : 0<bitValue modulus) (hr : 0<bitValue r₁)
    (hm : modulus.length≤L) (h₀ : r₀.length≤L) (h₁ : r₁.length≤L)
    (hc₀ : c₀.length≤L) (hc₁ : c₁.length≤L) :
    (makeInverseFrame modulus r₀ r₁ c₀ c₁).clock≤600*(L+1)^2 := by
  have hq : (divideBits r₀ r₁).quotient.length≤L := by
    rw [(divideBits_widths (xs:=r₀) hr).2]
    exact h₀
  have hd := bounded_divideBits (by omega : r₀.length≤3*L) h₁
  have hp := bounded_modMulBits hq hc₁ hm
  obtain ⟨ha,hap⟩ := bounded_addBits hc₀ hm false
  have hpr : (modMulBits (divideBits r₀ r₁).quotient c₁ modulus).division.remainder.length≤L := by
    rw [modMulBits_width hN]
    exact hm
  have hmax : max (addBits c₀ modulus false).bits.length
      (modMulBits (divideBits r₀ r₁).quotient c₁ modulus).division.remainder.length≤L+1 :=
    max_le hap (by omega)
  have hs := subBits_cost (addBits c₀ modulus false).bits
    (modMulBits (divideBits r₀ r₁).quotient c₁ modulus).division.remainder false
  have hsw : (subBits (addBits c₀ modulus false).bits
      (modMulBits (divideBits r₀ r₁).quotient c₁ modulus).division.remainder false).result.bits.length≤L+1 := by
    rw [(subBits_counts _ _ false).2.2.2.2]
    exact hmax
  have hred := bounded_divideBits (by omega :
    (subBits (addBits c₀ modulus false).bits
      (modMulBits (divideBits r₀ r₁).quotient c₁ modulus).division.remainder false).result.bits.length≤3*(L+1))
    (by omega : modulus.length≤L+1)
  dsimp only [makeInverseFrame]
  nlinarith

/-- Every recursive state keeps both output words within the supplied
physical width, including an exhausted arbitrary supplied loop. -/
theorem inverseLoop_width {L : ℕ} {modulus : List Bool} (hN : 0<bitValue modulus)
    (r₀ r₁ c₀ c₁ : List Bool) (fuel : List Unit)
    (hm : modulus.length≤L) (h₀ : r₀.length≤L) (h₁ : r₁.length≤L)
    (hc₀ : c₀.length≤L) (hc₁ : c₁.length≤L) :
    (inverseLoop modulus r₀ r₁ c₀ c₁ fuel).gcd.length≤L ∧
      (inverseLoop modulus r₀ r₁ c₀ c₁ fuel).coefficient.length≤L := by
  induction fuel generalizing r₀ r₁ c₀ c₁ with
  | nil => exact ⟨h₀,hc₀⟩
  | cons cell fuel ih =>
    by_cases hb : (nonzeroBits r₁).nonzero=true
    · have hw := makeInverseFrame_widths hN ((nonzeroBits_correct r₁).mp hb) r₀ c₀ c₁
      have ht := ih r₁ (makeInverseFrame modulus r₀ r₁ c₀ c₁).division.remainder c₁
        (makeInverseFrame modulus r₀ r₁ c₀ c₁).reduction.remainder
        h₁ (by omega) hc₁ (by omega)
      simpa only [inverseLoop,if_pos hb] using ht
    · simpa only [inverseLoop,if_neg hb] using And.intro h₀ hc₀

/-- Every visited frame pays its Boolean test and coefficient update.
Arbitrary insufficient fuel also satisfies this physical-work bound. -/
theorem inverseLoop_cost {L : ℕ} {modulus : List Bool} (hN : 0<bitValue modulus)
    (r₀ r₁ c₀ c₁ : List Bool) (fuel : List Unit)
    (hm : modulus.length≤L) (h₀ : r₀.length≤L) (h₁ : r₁.length≤L)
    (hc₀ : c₀.length≤L) (hc₁ : c₁.length≤L) :
    (inverseLoop modulus r₀ r₁ c₀ c₁ fuel).clock≤fuel.length*(620*(L+1)^2)+1 := by
  induction fuel generalizing r₀ r₁ c₀ c₁ with
  | nil => simp only [inverseLoop,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons cell fuel ih =>
    have hs := nonzeroBits_cost r₁
    by_cases hb : (nonzeroBits r₁).nonzero=true
    · have hpos := (nonzeroBits_correct r₁).mp hb
      have hw := makeInverseFrame_widths hN hpos r₀ c₀ c₁
      have ht := ih r₁ (makeInverseFrame modulus r₀ r₁ c₀ c₁).division.remainder c₁
        (makeInverseFrame modulus r₀ r₁ c₀ c₁).reduction.remainder
        h₁ (by omega) hc₁ (by omega)
      have hf := makeInverseFrame_cost hN hpos hm h₀ h₁ hc₀ hc₁
      simp only [inverseLoop,if_pos hb,List.length_cons]
      nlinarith
    · simp only [inverseLoop,if_neg hb,List.length_cons]
      nlinarith

/-- Public outputs occupy at most the actual modulus width, independently
of how much padding was present in the input before its paid normalization. -/
theorem inverseBits_width {modulus : List Bool} (hN : 0<bitValue modulus) (input : List Bool) :
    (inverseBits modulus input).gcd.length≤modulus.length ∧
      (inverseBits modulus input).coefficient.length≤modulus.length := by
  apply inverseLoop_width hN _ _ _ _ _ le_rfl le_rfl
  · rw [(divideBits_widths (xs:=input) hN).1]
  · exact Nat.zero_le _
  · rw [(divideBits_widths (xs:=[true]) hN).1]

/-- Inversion has a complete cubic scalar bit-primitive bound, including
both input normalizations, physical fuel allocation and coefficient updates. -/
theorem inverseBits_cost {L : ℕ} {modulus input : List Bool} (hN : 0<bitValue modulus)
    (hm : modulus.length≤L) (hi : input.length≤L) :
    (inverseBits modulus input).clock≤4000*(L+1)^3 := by
  have hmpos : 0<modulus.length := by
    cases modulus with
    | nil => simp only [bitValue,lt_self_iff_false] at hN
    | cons bit tail => simp only [List.length_cons]; omega
  have hn : (divideBits input modulus).remainder.length≤L := by
    rw [(divideBits_widths (xs:=input) hN).1]
    exact hm
  have ho : (divideBits [true] modulus).remainder.length≤L := by
    rw [(divideBits_widths (xs:=[true]) hN).1]
    exact hm
  have hf := buildGcdFuel_counts modulus (divideBits input modulus).remainder
  have hs : (buildGcdFuel modulus (divideBits input modulus).remainder).cells.length≤4*L+1 := by omega
  have hb : (buildGcdFuel modulus (divideBits input modulus).remainder).clock≤10*L+3 := by omega
  have hc := inverseLoop_cost hN modulus (divideBits input modulus).remainder []
    (divideBits [true] modulus).remainder
    (buildGcdFuel modulus (divideBits input modulus).remainder).cells hm hm hn (Nat.zero_le L) ho
  have hnormal := bounded_divideBits (by omega : input.length≤3*L) hm
  have hone := bounded_divideBits (by simp only [List.length_cons,List.length_nil]; omega :
    ([true] : List Bool).length≤3*L) hm
  have hsize := Nat.mul_le_mul_right (620*(L+1)^2) hs
  have hclock : (inverseBits modulus input).clock≤
      (4*L+1)*(620*(L+1)^2)+144*(L+1)^2+10*L+11 := by
    dsimp only [inverseBits]
    omega
  have hlast : (4*L+1)*(620*(L+1)^2)+144*(L+1)^2+10*L+11≤4000*(L+1)^3 := by
    nlinarith
  exact hclock.trans hlast

/-- A mathematical unit certifies the computed inverse value; it is not
an input to the Boolean algorithm. -/
theorem inverseBits_unit {modulus : List Bool} (hN : 0<bitValue modulus) (input : List Bool)
    (u : (ZMod (bitValue modulus))ˣ) (hu : bitValue input=(u : ZMod (bitValue modulus)).val) :
    bitValue (inverseBits modulus input).coefficient=
      ((u⁻¹ : (ZMod (bitValue modulus))ˣ) : ZMod (bitValue modulus)).val := by
  let : NeZero (bitValue modulus) := ⟨hN.ne'⟩
  rw [(inverseBits_refines hN input).2,hu]
  exact countedInverse_unit u

/-- A Boolean one test and its complete primitive clock. -/
structure OneBitsReport where
  /-- True precisely when the physical word represents one. -/
  value : Bool
  /-- Both subtraction circuits, two negations, the AND and literal/call cells. -/
  clock : ℕ

/-- Compare against one with two Boolean borrow circuits. Padding is scanned. -/
def isOneBits (bits : List Bool) : OneBitsReport :=
  let lower := subBits [true] bits false
  let upper := subBits bits [true] false
  ⟨Bool.and (Bool.not lower.borrow) (Bool.not upper.borrow),
    bitCost lower.result+bitCost upper.result+9⟩

/-- The actual Boolean test is equivalent to the word's mathematical value. -/
theorem isOneBits_correct (bits : List Bool) :
    (isOneBits bits).value=true ↔ bitValue bits=1 := by
  have hlo := subBits_borrow_iff [true] bits false
  have hhi := subBits_borrow_iff bits [true] false
  simp only [bitValue,bitNat,if_true,Bool.false_eq_true,if_false,Nat.mul_zero,
    Nat.add_zero] at hlo hhi
  simp only [isOneBits,Bool.and_eq_true,Bool.not_eq_true_eq_eq_false]
  have hlf : (subBits [true] bits false).borrow=false ↔ ¬1<bitValue bits := by
    rw [←hlo]
    exact Bool.eq_false_iff
  have hhf : (subBits bits [true] false).borrow=false ↔ ¬bitValue bits<1 := by
    rw [←hhi]
    exact Bool.eq_false_iff
  rw [hlf,hhf]
  omega

/-- The GCD-one decision costs linear work in its physical word width. -/
theorem isOneBits_cost {L : ℕ} {bits : List Bool} (hw : bits.length≤L) :
    (isOneBits bits).clock≤24*(L+1)+13 := by
  have hl := subBits_cost [true] bits false
  have hh := subBits_cost bits [true] false
  have hmax₀ : max ([true] : List Bool).length bits.length≤L+1 := max_le (by simp) (by omega)
  have hmax₁ : max bits.length ([true] : List Bool).length≤L+1 := max_le (by omega) (by simp)
  dsimp only [isOneBits]
  omega

/-- Exact subtraction and reduction of an already canonical residue. -/
structure NegationBitsReport where
  /-- The actual subtraction from the positive modulus. -/
  subtraction : SubReport
  /-- Final normalization also handles a zero input residue. -/
  reduction : DivisionReport
  /-- Both primitive clocks and two retained call cells. -/
  clock : ℕ

/-- Compute the additive inverse of a reduced residue by Boolean circuits. -/
def negateResidueBits (modulus residue : List Bool) : NegationBitsReport :=
  let subtraction := subBits modulus residue false
  let reduction := divideBits subtraction.result.bits modulus
  ⟨subtraction,reduction,bitCost subtraction.result+reduction.clock+2⟩

/-- No underflow is assumed: canonicality proves that the actual borrow is false. -/
theorem negateResidueBits_no_borrow {modulus residue : List Bool}
    (hr : bitValue residue<bitValue modulus) :
    (negateResidueBits modulus residue).subtraction.borrow=false := by
  apply Bool.eq_false_iff.mpr
  intro hb
  have hl := (subBits_borrow_iff modulus residue false).mp hb
  simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] at hl
  omega

/-- The actual bit residue is the additive inverse in the composite ring. -/
theorem negateResidueBits_correct {modulus residue : List Bool}
    (hr : bitValue residue<bitValue modulus) :
    (bitValue (negateResidueBits modulus residue).reduction.remainder : ZMod (bitValue modulus))=
      -(bitValue residue : ZMod (bitValue modulus)) := by
  have hs := subBits_difference (negateResidueBits_no_borrow hr)
  change bitValue (subBits modulus residue false).result.bits=bitValue modulus-bitValue residue at hs
  change (bitValue (divideBits (subBits modulus residue false).result.bits modulus).remainder :
    ZMod (bitValue modulus))=_
  rw [(divideBits_correct _ modulus).2,hs,ZMod.natCast_mod,Nat.cast_sub hr.le,
    ZMod.natCast_self,zero_sub]

/-- Canonical modular negation preserves the modulus's physical output width. -/
theorem negateResidueBits_width {modulus : List Bool} (hN : 0<bitValue modulus)
    (residue : List Bool) :
    (negateResidueBits modulus residue).reduction.remainder.length=modulus.length :=
  (divideBits_widths (xs:=(subBits modulus residue false).result.bits) hN).1

/-- Both negation circuits have a composed quadratic physical-width cost. -/
theorem negateResidueBits_cost {L : ℕ} {modulus residue : List Bool}
    (hm : modulus.length≤L) (hr : residue.length≤L) :
    (negateResidueBits modulus residue).clock≤100*(L+1)^2 := by
  have hs := subBits_cost modulus residue false
  have hmax : max modulus.length residue.length≤L := max_le hm hr
  have hwidth : (subBits modulus residue false).result.bits.length≤3*L := by
    rw [(subBits_counts _ _ false).2.2.2.2]
    omega
  have hd := bounded_divideBits hwidth hm
  dsimp only [negateResidueBits]
  nlinarith

/-- Actual marked-index circuits, including a checked inverse-acceptance bit. -/
structure MarkedBitsReport where
  /-- The target times target derivative, reduced by the public modulus. -/
  denominator : ModularProduct
  /-- Extended Euclid retains its GCD and computed coefficient. -/
  inverse : InverseBitsReport
  /-- Inverse coefficient times the original marked base derivative. -/
  product : ModularProduct
  /-- The original decoder's negative sign, computed and normalized. -/
  negative : NegationBitsReport
  /-- The Boolean GCD-one test; a nonunit never accepts an inverse. -/
  unit : OneBitsReport
  /-- A candidate word is retained only when the inverse is certified. -/
  index : Option (List Bool)
  /-- Every scalar circuit, inverse, unit gate and retained call/branch cell. -/
  clock : ℕ

/-- Decode the marked derivative ratio from actual acquired words.
No unit inverse, GCD result, natural residue or local index is supplied as advice. -/
def decodeMarkedBits (modulus target targetD baseD : List Bool) : MarkedBitsReport :=
  let denominator := modMulBits target targetD modulus
  let inverse := inverseBits modulus denominator.division.remainder
  let product := modMulBits inverse.coefficient baseD modulus
  let negative := negateResidueBits modulus product.division.remainder
  let unit := isOneBits inverse.gcd
  let index := if unit.value=true then some negative.reduction.remainder else none
  ⟨denominator,inverse,product,negative,unit,index,
    denominator.clock+inverse.clock+product.clock+negative.clock+unit.clock+7⟩

/-- The retained Boolean GCD is exactly the denominator's arithmetic GCD. -/
theorem decodeMarkedBits_gcd {modulus : List Bool} (hN : 0<bitValue modulus)
    (target targetD baseD : List Bool) :
    bitValue (decodeMarkedBits modulus target targetD baseD).inverse.gcd=
      (bitValue modulus).gcd (bitValue target*bitValue targetD) := by
  change bitValue (inverseBits modulus (modMulBits target targetD modulus).division.remainder).gcd=_
  rw [inverseBits_gcd hN,modMulBits_correct]
  exact (Nat.gcd_comm _ _).trans (Nat.gcd_rec _ _).symm

/-- The inverse-acceptance gate checks exactly GCD one, using actual bits. -/
theorem decodeMarkedBits_unit_iff {modulus : List Bool} (hN : 0<bitValue modulus)
    (target targetD baseD : List Bool) :
    (decodeMarkedBits modulus target targetD baseD).unit.value=true ↔
      (bitValue modulus).gcd (bitValue target*bitValue targetD)=1 := by
  change (isOneBits (decodeMarkedBits modulus target targetD baseD).inverse.gcd).value=true ↔ _
  rw [isOneBits_correct,decodeMarkedBits_gcd hN]

/-- A nonunit denominator returns no index candidate while retaining
its exact GCD in the report for checked factor or saturation handling. -/
theorem decodeMarkedBits_nonunit {modulus : List Bool} (hN : 0<bitValue modulus)
    (target targetD baseD : List Bool)
    (hg : (bitValue modulus).gcd (bitValue target*bitValue targetD)≠1) :
    (decodeMarkedBits modulus target targetD baseD).index=none := by
  have hb : ¬(decodeMarkedBits modulus target targetD baseD).unit.value=true := by
    intro he
    exact hg ((decodeMarkedBits_unit_iff hN target targetD baseD).mp he)
  change (if (decodeMarkedBits modulus target targetD baseD).unit.value=true then
    some (decodeMarkedBits modulus target targetD baseD).negative.reduction.remainder else none)=none
  rw [if_neg hb]

/-- A unit denominator certifies the actual decoded residue, including
the original negative sign and the complete marked derivative channel. -/
theorem decodeMarkedBits_unit_exact {modulus : List Bool} (hN : 0<bitValue modulus)
    (target targetD baseD : List Bool) (denom : (ZMod (bitValue modulus))ˣ)
    (hdenom : (denom : ZMod (bitValue modulus))=
      (bitValue target : ZMod (bitValue modulus))*(bitValue targetD : ZMod (bitValue modulus))) :
    (decodeMarkedBits modulus target targetD baseD).unit.value=true ∧
    (bitValue (decodeMarkedBits modulus target targetD baseD).negative.reduction.remainder :
      ZMod (bitValue modulus))=
      -((denom⁻¹ : (ZMod (bitValue modulus))ˣ) : ZMod (bitValue modulus))*
        (bitValue baseD : ZMod (bitValue modulus)) := by
  let : NeZero (bitValue modulus) := ⟨hN.ne'⟩
  let d := (modMulBits target targetD modulus).division.remainder
  have hdcast : (bitValue d : ZMod (bitValue modulus))=(denom : ZMod (bitValue modulus)) := by
    rw [modMulBits_correct,ZMod.natCast_mod,Nat.cast_mul]
    exact hdenom.symm
  have hdlt : bitValue d<bitValue modulus := by
    rw [modMulBits_correct]
    exact Nat.mod_lt _ hN
  have hdval : bitValue d=(denom : ZMod (bitValue modulus)).val := by
    have hh := congrArg ZMod.val hdcast
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hdlt] using hh
  have hg : bitValue (inverseBits modulus d).gcd=1 := by
    rw [(inverseBits_refines hN d).1,hdval,countedInverse_unit_gcd]
  have hi : (bitValue (inverseBits modulus d).coefficient : ZMod (bitValue modulus))=
      ((denom⁻¹ : (ZMod (bitValue modulus))ˣ) : ZMod (bitValue modulus)) := by
    rw [inverseBits_unit hN d denom hdval,ZMod.natCast_zmod_val]
  constructor
  · exact (isOneBits_correct _).mpr hg
  · have hr : bitValue (modMulBits (inverseBits modulus d).coefficient baseD modulus).division.remainder<
        bitValue modulus := by
      rw [modMulBits_correct]
      exact Nat.mod_lt _ hN
    have hn := negateResidueBits_correct hr
    rw [modMulBits_correct,ZMod.natCast_mod,Nat.cast_mul,hi] at hn
    simpa only [decodeMarkedBits,d,neg_mul] using hn

/-- The Boolean decoder refines the original rich interval reader's
marked index when supplied its exact target and derivative words. -/
theorem decodeMarkedBits_eq_decodedIndex {modulus : List Bool} (hN : 0<bitValue modulus)
    (target targetD baseD : List Bool) (alpha x : (ZMod (bitValue modulus))ˣ) (L : ℕ)
    (hx : (bitValue target : ZMod (bitValue modulus))=(x : ZMod (bitValue modulus)))
    (hD : (bitValue targetD : ZMod (bitValue modulus))=
      SemiprimeIntervalJet.targetDerivative (alpha : ZMod (bitValue modulus)) (x : ZMod (bitValue modulus)) L)
    (hE : (bitValue baseD : ZMod (bitValue modulus))=
      SemiprimeIntervalJet.baseDerivative (alpha : ZMod (bitValue modulus)) (x : ZMod (bitValue modulus)) L)
    (denom : (ZMod (bitValue modulus))ˣ)
    (hdenom : (denom : ZMod (bitValue modulus))=(x : ZMod (bitValue modulus))*
      SemiprimeIntervalJet.targetDerivative (alpha : ZMod (bitValue modulus)) (x : ZMod (bitValue modulus)) L) :
    (decodeMarkedBits modulus target targetD baseD).unit.value=true ∧
    (bitValue (decodeMarkedBits modulus target targetD baseD).negative.reduction.remainder :
      ZMod (bitValue modulus))=
      SemiprimeIntervalJet.decodedIndex (alpha : ZMod (bitValue modulus)) (x : ZMod (bitValue modulus)) L denom := by
  have hh := decodeMarkedBits_unit_exact hN target targetD baseD denom (by rwa [hx,hD])
  refine ⟨hh.1,?_⟩
  rw [hh.2,hE]
  rfl

/-- The accepted Boolean word preserves the original simple local root
index through every retained coefficient reduction. No local index is
an input to the executable decoder. -/
theorem decodeMarkedBits_at_local_root {modulus : List Bool} (hN : 0<bitValue modulus)
    {R : Type*} [CommRing R] (f : ZMod (bitValue modulus)→+*R)
    (target targetD baseD : List Bool) (alpha x : (ZMod (bitValue modulus))ˣ) (L : ℕ)
    (hx : (bitValue target : ZMod (bitValue modulus))=(x : ZMod (bitValue modulus)))
    (hD : (bitValue targetD : ZMod (bitValue modulus))=
      SemiprimeIntervalJet.targetDerivative (alpha : ZMod (bitValue modulus)) (x : ZMod (bitValue modulus)) L)
    (hE : (bitValue baseD : ZMod (bitValue modulus))=
      SemiprimeIntervalJet.baseDerivative (alpha : ZMod (bitValue modulus)) (x : ZMod (bitValue modulus)) L)
    (denom : (ZMod (bitValue modulus))ˣ)
    (hdenom : (denom : ZMod (bitValue modulus))=(x : ZMod (bitValue modulus))*
      SemiprimeIntervalJet.targetDerivative (alpha : ZMod (bitValue modulus)) (x : ZMod (bitValue modulus)) L)
    {k : ℕ} (hk : k<L) (hroot : f (x : ZMod (bitValue modulus))=(f (alpha : ZMod (bitValue modulus)))^k) :
    ∃ word, (decodeMarkedBits modulus target targetD baseD).index=some word ∧
      f (bitValue word : ZMod (bitValue modulus))=(k : R) := by
  have hh := decodeMarkedBits_eq_decodedIndex hN target targetD baseD alpha x L hx hD hE denom hdenom
  refine ⟨(decodeMarkedBits modulus target targetD baseD).negative.reduction.remainder,?_,?_⟩
  · change (if (decodeMarkedBits modulus target targetD baseD).unit.value=true then
      some (decodeMarkedBits modulus target targetD baseD).negative.reduction.remainder else none)=_
    rw [if_pos hh.1]
  · rw [hh.2]
    exact SemiprimeIntervalJet.decodedIndex_map_root f _ _ L denom hdenom hk hroot

/-- Marked index computation preserves a bounded physical residue word. -/
theorem decodeMarkedBits_width {modulus : List Bool} (hN : 0<bitValue modulus)
    (target targetD baseD : List Bool) :
    (decodeMarkedBits modulus target targetD baseD).negative.reduction.remainder.length=modulus.length :=
  negateResidueBits_width hN _

/-- The complete scalar marked decoder is cubic in physical word width.
The input jet acquisition and mixed-index factor batch are separate stages. -/
theorem decodeMarkedBits_cost {L : ℕ} {modulus target targetD baseD : List Bool}
    (hN : 0<bitValue modulus) (hm : modulus.length≤L) (hx : target.length≤L)
    (hD : targetD.length≤L) (hE : baseD.length≤L) :
    (decodeMarkedBits modulus target targetD baseD).clock≤5000*(L+1)^3 := by
  have hd := bounded_modMulBits hx hD hm
  have hdw : (modMulBits target targetD modulus).division.remainder.length≤L := by
    rw [modMulBits_width hN]
    exact hm
  have hi := inverseBits_cost hN hm hdw
  have hiw := inverseBits_width hN (modMulBits target targetD modulus).division.remainder
  have hp := bounded_modMulBits (hiw.2.trans hm) hE hm
  have hpw : (modMulBits (inverseBits modulus
      (modMulBits target targetD modulus).division.remainder).coefficient baseD modulus).division.remainder.length≤L := by
    rw [modMulBits_width hN]
    exact hm
  have hn := negateResidueBits_cost hm hpw
  have hu := isOneBits_cost (hiw.1.trans hm)
  dsimp only [decodeMarkedBits]
  nlinarith

/-- A saturated actual long seed reader cannot return none. This covers
both equal and different local root indices, without supplying those indices. -/
theorem long_readSeed_saturated {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hm : 4≤m) (g : (ZMod (p*q))ˣ) (hlong : SemiprimeLocalOrderRouting.LongData g m)
    (s : SemiprimeDenseRowCarries.ProgressionSeed ((ZMod (p*q))ˣ))
    (hzero : SemiprimeIntervalJet.intervalProduct
      ((SemiprimeSeedSumAcquisition.seedBase (SemiprimeCentreFreeCover.projectedUnit g m) m :
        (ZMod (p*q))ˣ) : ZMod (p*q)) (s.step : ZMod (p*q))
        (SemiprimeSeedSumAcquisition.seedLength m)=0) :
    SemiprimeSeedSumAcquisition.readSeed (SemiprimeCentreFreeCover.projectedUnit g m) m s≠none := by
  let : Fact p.Prime := ⟨hp⟩
  have hz := congrArg (ZMod.castHom (dvd_mul_right p q) (ZMod p)) hzero
  rw [SemiprimeIntervalJet.intervalProduct_map,map_zero,SemiprimeIntervalJet.intervalProduct_zero_iff] at hz
  obtain ⟨k,hk,hroot⟩ := hz
  have hpds := SemiprimeSeedSumAcquisition.long_seed_interval_periods hm g hlong
  have hcover : SemiprimeSeedSumAcquisition.seedLength m≤(2*m)^2 := by
    nlinarith only [(SemiprimeSeedSumAcquisition.seedLength_bounds hm).2]
  have hreader := SemiprimeWrapIndexRecovery.recoverTaggedInterval_preserves_root hp hq hpq
    (SemiprimeSeedSumAcquisition.seedBase (SemiprimeCentreFreeCover.projectedUnit g m) m)
    s.step hk hcover hpds.1 hpds.2 hroot
  intro hnone
  rcases hreader with ⟨d,hd⟩|hd
  · change SemiprimeSeedSumAcquisition.readSeed (SemiprimeCentreFreeCover.projectedUnit g m) m s=
      some (Sum.inl d) at hd
    rw [hnone] at hd
    cases hd
  · change SemiprimeSeedSumAcquisition.readSeed (SemiprimeCentreFreeCover.projectedUnit g m) m s=
      some (Sum.inr k) at hd
    rw [hnone] at hd
    cases hd

/-- Count saturation-stage entries along the established seed scan's
actually visited prefix. This is a specification-side count, not jet acquisition. -/
noncomputable def seedMarkedAttemptBudget {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    List (SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ))→ℕ
  | [] => 0
  | s::tail =>
    let visit := if SemiprimeIntervalJet.intervalProduct
      ((SemiprimeSeedSumAcquisition.seedBase g m : (ZMod N)ˣ) : ZMod N) (s.step : ZMod N)
        (SemiprimeSeedSumAcquisition.seedLength m)=0 then 1 else 0
    match SemiprimeSeedSumAcquisition.readSeed g m s with
    | none => visit+seedMarkedAttemptBudget g m tail
    | some _ => visit

/-- On the actual long branch the whole original seed scan enters
marked-index recovery at most once, independently of the supplied list length. -/
theorem long_seedMarkedAttemptBudget_le_one {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : SemiprimeLocalOrderRouting.LongData g m)
    (xs : List (SemiprimeDenseRowCarries.ProgressionSeed ((ZMod (p*q))ˣ))) :
    seedMarkedAttemptBudget (SemiprimeCentreFreeCover.projectedUnit g m) m xs≤1 := by
  induction xs with
  | nil => change 0≤1; omega
  | cons s tail ih =>
    cases he : SemiprimeSeedSumAcquisition.readSeed (SemiprimeCentreFreeCover.projectedUnit g m) m s with
    | none =>
      have hz : SemiprimeIntervalJet.intervalProduct
          ((SemiprimeSeedSumAcquisition.seedBase (SemiprimeCentreFreeCover.projectedUnit g m) m :
            (ZMod (p*q))ˣ) : ZMod (p*q)) (s.step : ZMod (p*q))
            (SemiprimeSeedSumAcquisition.seedLength m)≠0 := by
        intro hzero
        exact long_readSeed_saturated hp hq hpq hm g hlong s hzero he
      simpa only [seedMarkedAttemptBudget,he,if_neg hz,Nat.zero_add] using ih
    | some outcome =>
      simp only [seedMarkedAttemptBudget,he]
      split <;> omega

/-- The actual public long route certifies the at-most-once marked stage
at its matched row modulus. Prefix construction and scalar jet acquisition
remain separate costs from this proved control-flow fact. -/
theorem actual_public_route_marked_attempt_le_one {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hroute : SemiprimeWrapIndexRecovery.routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := SemiprimeCentreFreeCover.projectedUnit (ZMod.unitOfCoprime a hc) m
      ∀ xs : List (SemiprimeDenseRowCarries.ProgressionSeed ((ZMod (p*q))ˣ)),
        seedMarkedAttemptBudget h m xs≤1 := by
  have hdata := SemiprimeWrapIndexRecovery.routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hdata
  obtain ⟨hc,hlong⟩ := hdata
  have hN := Nat.mul_pos hp.pos hq.pos
  have hm : 4≤SemiprimeEuclidRowBudget.publicRowModulus (p*q) :=
    hB.trans (SemiprimeEuclidRowBudget.publicRowModulus_bounds hN).1
  refine ⟨hc,?_⟩
  dsimp only
  intro xs
  exact long_seedMarkedAttemptBudget_le_one hp hq hpq hm _ hlong xs

end RiemannGaussian.SemiprimeBitInverse
