/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitArithmetic

/-!
# Boolean subtraction and restoring quotient/remainder

The data path uses full-borrow Boolean circuits and fixed-width bit words.
All gates, bit-cell traffic and branch tests are charged in the existing
primitive model. No natural value evaluation computes an output. These
local backend proofs do not yet establish universal one-sixth recovery or
the full public factorizer's machine and bit-cost certificate.
-/

namespace RiemannGaussian.SemiprimeBitDivision

open SemiprimeBitArithmetic

/-- Seven-gate full subtraction returns the low difference bit and borrow:
two XORs, one NOT, two ANDs and two ORs. -/
def fullSubtractor (x y borrow : Bool) : Bool×Bool :=
  (Bool.xor (Bool.xor x y) borrow,
    Bool.or (Bool.and (Bool.not x) (Bool.or y borrow)) (Bool.and y borrow))

/-- The full-borrow circuit preserves its exact natural digit equation. -/
theorem fullSubtractor_correct (x y borrow : Bool) :
    bitNat x+2*bitNat (fullSubtractor x y borrow).2=
      bitNat y+bitNat borrow+bitNat (fullSubtractor x y borrow).1 := by
  cases x <;> cases y <;> cases borrow <;> rfl

/-- Actual low difference word, final borrow and the complete primitive clocks. -/
structure SubReport where
  /-- Every output cell and charged subtraction primitive. -/
  result : BitReport
  /-- The borrow beyond the full physical input width. -/
  borrow : Bool

/-- Ripple subtraction reads both words once and uses literal false past
the shorter input. The final borrow is retained instead of assumed absent. -/
def subBits : List Bool → List Bool → Bool → SubReport
  | [],[],borrow => ⟨⟨[],0,0,0,2⟩,borrow⟩
  | x::xs,[],borrow =>
    let digit := fullSubtractor x false borrow
    let tail := subBits xs [] digit.2
    ⟨⟨digit.1::tail.result.bits,tail.result.gates+7,tail.result.reads+1,
      tail.result.writes+1,tail.result.tests+2⟩,tail.borrow⟩
  | [],y::ys,borrow =>
    let digit := fullSubtractor false y borrow
    let tail := subBits [] ys digit.2
    ⟨⟨digit.1::tail.result.bits,tail.result.gates+7,tail.result.reads+1,
      tail.result.writes+1,tail.result.tests+2⟩,tail.borrow⟩
  | x::xs,y::ys,borrow =>
    let digit := fullSubtractor x y borrow
    let tail := subBits xs ys digit.2
    ⟨⟨digit.1::tail.result.bits,tail.result.gates+7,tail.result.reads+2,
      tail.result.writes+1,tail.result.tests+2⟩,tail.borrow⟩
termination_by xs ys _ => xs.length+ys.length
decreasing_by all_goals simp_wf <;> omega

/-- Full physical width, every gate and every actual input/output bit cell
are charged, including underflow and high-zero-padded inputs. -/
theorem subBits_counts (xs ys : List Bool) (borrow : Bool) :
    (subBits xs ys borrow).result.gates=7*max xs.length ys.length ∧
    (subBits xs ys borrow).result.reads=xs.length+ys.length ∧
    (subBits xs ys borrow).result.writes=max xs.length ys.length ∧
    (subBits xs ys borrow).result.tests=2*max xs.length ys.length+2 ∧
    (subBits xs ys borrow).result.bits.length=max xs.length ys.length := by
  induction xs generalizing ys borrow with
  | nil =>
    induction ys generalizing borrow with
    | nil => simp [subBits]
    | cons y ys ih =>
      have hc := ih (fullSubtractor false y borrow).2
      rw [subBits]
      dsimp only [List.length_cons,List.length_nil] at hc ⊢
      omega
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hc := ih [] (fullSubtractor x false borrow).2
      rw [subBits]
      dsimp only [List.length_cons,List.length_nil] at hc ⊢
      omega
    | cons y ys =>
      have hc := ih ys (fullSubtractor x y borrow).2
      rw [subBits]
      dsimp only [List.length_cons] at hc ⊢
      omega

/-- Subtraction's final borrow and low word satisfy the exact unsigned
equation at the actual physical width, without a native subtraction call. -/
theorem subBits_equation (xs ys : List Bool) (borrow : Bool) :
    bitValue xs+2^(max xs.length ys.length)*bitNat (subBits xs ys borrow).borrow=
      bitValue ys+bitNat borrow+bitValue (subBits xs ys borrow).result.bits := by
  induction xs generalizing ys borrow with
  | nil =>
    induction ys generalizing borrow with
    | nil => simp only [subBits,bitValue,List.length_nil,Nat.max_self,pow_zero,
        Nat.one_mul,Nat.zero_add,Nat.add_zero]
    | cons y ys ih =>
      have hc := fullSubtractor_correct false y borrow
      have ht := ih (fullSubtractor false y borrow).2
      rw [subBits]
      dsimp only
      simp only [bitValue,List.length_nil,List.length_cons,Nat.zero_max,pow_succ,
        bitNat,Bool.false_eq_true,if_false] at hc ht ⊢
      nlinarith
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hc := fullSubtractor_correct x false borrow
      have ht := ih [] (fullSubtractor x false borrow).2
      rw [subBits]
      dsimp only
      simp only [bitValue,List.length_nil,List.length_cons,Nat.max_zero,pow_succ,
        bitNat,Bool.false_eq_true,if_false] at hc ht ⊢
      nlinarith
    | cons y ys =>
      have hc := fullSubtractor_correct x y borrow
      have ht := ih ys (fullSubtractor x y borrow).2
      have hm : max (xs.length+1) (ys.length+1)=max xs.length ys.length+1 := by omega
      rw [subBits]
      dsimp only
      simp only [bitValue,List.length_cons,hm,pow_succ]
      nlinarith

/-- Final borrow gives the exact comparison, rather than a supplied integer
ordering oracle. The low word itself also remains available. -/
theorem subBits_borrow_iff (xs ys : List Bool) (borrow : Bool) :
    (subBits xs ys borrow).borrow=true ↔ bitValue xs<bitValue ys+bitNat borrow := by
  have he := subBits_equation xs ys borrow
  have hl := (subBits_counts xs ys borrow).2.2.2.2
  have hv := bitValue_lt_width (subBits xs ys borrow).result.bits
  rw [hl] at hv
  constructor
  · intro hb
    rw [hb] at he
    simp only [bitNat,if_true,Nat.mul_one] at he ⊢
    omega
  · intro hless
    by_contra hn
    have hb : (subBits xs ys borrow).borrow=false := by
      cases h : (subBits xs ys borrow).borrow with
      | false => rfl
      | true => exact False.elim (hn h)
    rw [hb] at he
    simp only [bitNat,Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero] at he hless
    omega

/-- A subtraction with no final borrow returns the literal natural difference. -/
theorem subBits_difference {xs ys : List Bool}
    (hb : (subBits xs ys false).borrow=false) :
    bitValue (subBits xs ys false).result.bits=bitValue xs-bitValue ys := by
  have he := subBits_equation xs ys false
  simp only [hb,bitNat,Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero] at he
  omega

/-- The complete gate/cell/test clock of subtraction is linear in the
longer physical input, whether or not the operation underflows. -/
theorem subBits_cost (xs ys : List Bool) (borrow : Bool) :
    bitCost (subBits xs ys borrow).result≤12*max xs.length ys.length+2 := by
  obtain ⟨hg,hr,hw,ht,_⟩ := subBits_counts xs ys borrow
  dsimp only [bitCost]
  omega

/-- Copy or zero-pad only the width of a literal template word. This
operation is actually implemented and charged, rather than free trimming. -/
def fitBits : List Bool → List Bool → BitReport
  | _,[] => ⟨[],0,0,0,1⟩
  | [],_::ys =>
    let tail := fitBits [] ys
    ⟨false::tail.bits,tail.gates,tail.reads,tail.writes+1,tail.tests+2⟩
  | x::xs,_::ys =>
    let tail := fitBits xs ys
    ⟨x::tail.bits,tail.gates,tail.reads+1,tail.writes+1,tail.tests+2⟩

/-- Fitting produces exactly the requested physical width and includes
every visited input bit and new output bit in its linear clock. -/
theorem fitBits_counts (xs ys : List Bool) :
    (fitBits xs ys).bits.length=ys.length ∧ (fitBits xs ys).gates=0 ∧
    (fitBits xs ys).reads≤ys.length ∧ (fitBits xs ys).writes=ys.length ∧
    (fitBits xs ys).tests=2*ys.length+1 := by
  induction ys generalizing xs with
  | nil => simp only [fitBits,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl,and_self]
  | cons y ys ih =>
    cases xs with
    | nil =>
      have hc := ih []
      simp only [fitBits,List.length_cons]
      omega
    | cons x xs =>
      have hc := ih xs
      simp only [fitBits,List.length_cons]
      omega

/-- Width fitting's gate/cell/test clock includes zero padding and copying. -/
theorem fitBits_cost (xs ys : List Bool) : bitCost (fitBits xs ys)≤4*ys.length+1 := by
  obtain ⟨_,hg,hr,hw,ht⟩ := fitBits_counts xs ys
  dsimp only [bitCost]
  omega

/-- The actual zero-filled template word has natural value zero. -/
theorem fitBits_zero_value (ys : List Bool) : bitValue (fitBits [] ys).bits=0 := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp only [fitBits,bitValue,bitNat,Bool.false_eq_true,if_false,ih,
      Nat.mul_zero,Nat.zero_add]

/-- Fitting preserves every value that actually fits the template width.
The data path performs only bit copying and literal zero padding. -/
theorem fitBits_value {xs ys : List Bool} (hwidth : bitValue xs<2^ys.length) :
    bitValue (fitBits xs ys).bits=bitValue xs := by
  induction ys generalizing xs with
  | nil =>
    simp only [fitBits,bitValue]
    simp only [List.length_nil,pow_zero] at hwidth
    omega
  | cons y ys ih =>
    cases xs with
    | nil => exact fitBits_zero_value _
    | cons x xs =>
      have hs : bitValue xs<2^ys.length := by
        simp only [bitValue,List.length_cons,pow_succ] at hwidth
        omega
      simp only [fitBits,bitValue,ih hs]

/-- One-bit nonzero decision and its charged complete scan. -/
structure NonzeroReport where
  /-- The OR of every actual input bit. -/
  nonzero : Bool
  /-- All Boolean gates, input reads and list tests. -/
  clock : ℕ

/-- Test a divisor without evaluating its natural value. The complete
word is scanned even if an earlier bit already equals true. -/
def nonzeroBits : List Bool → NonzeroReport
  | [] => ⟨false,1⟩
  | bit::tail =>
    let child := nonzeroBits tail
    ⟨Bool.or bit child.nonzero,child.clock+3⟩

/-- The actual Boolean divisor test is equivalent to positive value. -/
theorem nonzeroBits_correct (bits : List Bool) :
    (nonzeroBits bits).nonzero=true ↔ 0<bitValue bits := by
  induction bits with
  | nil => simp only [nonzeroBits,bitValue,Bool.false_eq_true,Nat.lt_irrefl]
  | cons bit bits ih =>
    cases bit <;> cases hb : (nonzeroBits bits).nonzero <;>
      simp only [hb] at ih <;>
      simp [nonzeroBits,bitValue,bitNat,hb] at ih ⊢ <;> omega

/-- Every divisor bit is explicitly read and ORed, with linear scan cost. -/
theorem nonzeroBits_cost (bits : List Bool) : (nonzeroBits bits).clock=3*bits.length+1 := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp only [nonzeroBits,List.length_cons,ih]; omega

/-- Actual quotient/remainder bit words and the composed restoring clock. -/
structure DivisionReport where
  /-- Actual quotient word, with high zero padding allowed. -/
  quotient : List Bool
  /-- Actual remainder, fitted to the divisor word in the positive case. -/
  remainder : List Bool
  /-- All recursively composed Boolean/cell/test charges. -/
  clock : ℕ
  /-- Number of restored input digits. -/
  rounds : ℕ

/-- Restore one input bit at a time. Full subtraction supplies the decision;
the next remainder is physically fitted at every step, with every copy paid.
Each step also charges its input read, list test, expanded and quotient cells,
and the one-bit borrow branch. -/
def divideLoop : List Bool → List Bool → DivisionReport
  | [],divisor =>
    let zero := fitBits [] divisor
    ⟨[],zero.bits,bitCost zero+1,0⟩
  | bit::tail,divisor =>
    let child := divideLoop tail divisor
    let expanded := bit::child.remainder
    let difference := subBits expanded divisor false
    if difference.borrow=true then
      let fitted := fitBits expanded divisor
      ⟨false::child.quotient,fitted.bits,
        child.clock+bitCost difference.result+bitCost fitted+5,child.rounds+1⟩
    else
      let fitted := fitBits difference.result.bits divisor
      ⟨true::child.quotient,fitted.bits,
        child.clock+bitCost difference.result+bitCost fitted+5,child.rounds+1⟩

/-- The literal output widths and positive recursion depth are bounded
without assumptions on input values, including an all-zero divisor word. -/
theorem divideLoop_widths (xs ys : List Bool) :
    (divideLoop xs ys).remainder.length=ys.length ∧
    (divideLoop xs ys).quotient.length=xs.length ∧
    (divideLoop xs ys).rounds=xs.length := by
  induction xs with
  | nil => exact ⟨(fitBits_counts [] ys).1,rfl,rfl⟩
  | cons bit xs ih =>
    have hkeep := (fitBits_counts (bit::(divideLoop xs ys).remainder) ys).1
    have hsub := (fitBits_counts
      (subBits (bit::(divideLoop xs ys).remainder) ys false).result.bits ys).1
    rw [divideLoop]
    dsimp only
    split <;> dsimp only [List.length_cons] <;> omega

/-- Restoring division preserves the exact Euclidean equation and a
proper remainder at every actual recursive state for a positive divisor. -/
theorem divideLoop_invariant (xs ys : List Bool) (hD : 0<bitValue ys) :
    bitValue ys*bitValue (divideLoop xs ys).quotient+
      bitValue (divideLoop xs ys).remainder=bitValue xs ∧
      bitValue (divideLoop xs ys).remainder<bitValue ys := by
  induction xs with
  | nil =>
    simp only [divideLoop,bitValue,fitBits_zero_value,Nat.mul_zero,Nat.zero_add]
    exact ⟨True.intro,hD⟩
  | cons bit xs ih =>
    let child := divideLoop xs ys
    let expanded := bit::child.remainder
    let difference := subBits expanded ys false
    have he : bitValue ys*bitValue child.quotient+bitValue child.remainder=bitValue xs := ih.1
    have hr : bitValue child.remainder<bitValue ys := ih.2
    have hdigit : bitNat bit≤1 := by cases bit <;> decide
    have hexp : bitValue expanded<2*bitValue ys := by
      change bitNat bit+2*bitValue child.remainder<2*bitValue ys
      omega
    have hword := bitValue_lt_width ys
    by_cases hb : difference.borrow=true
    · have hsmall : bitValue expanded<bitValue ys := by
        have h := (subBits_borrow_iff expanded ys false).mp hb
        simpa only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] using h
      have hf := fitBits_value (lt_trans hsmall hword)
      rw [divideLoop]
      dsimp only
      rw [if_pos hb]
      dsimp only
      rw [hf]
      constructor
      · simp only [bitValue,bitNat,Bool.false_eq_true,if_false,Nat.zero_add]
        change bitValue ys*(2*bitValue child.quotient)+bitValue expanded=
          bitNat bit+2*bitValue xs
        have hvalue : bitValue expanded=bitNat bit+2*bitValue child.remainder := rfl
        nlinarith
      · exact hsmall
    · have hfalse : difference.borrow=false := Bool.eq_false_of_not_eq_true hb
      have hs := subBits_equation expanded ys false
      change bitValue expanded+2^(max expanded.length ys.length)*bitNat difference.borrow=
        bitValue ys+bitNat false+bitValue difference.result.bits at hs
      simp only [hfalse,bitNat,Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero] at hs
      have hsmall : bitValue difference.result.bits<bitValue ys := by omega
      have hf := fitBits_value (lt_trans hsmall hword)
      rw [divideLoop]
      dsimp only
      rw [if_neg hb]
      dsimp only
      rw [hf]
      constructor
      · simp only [bitValue,bitNat,if_true]
        dsimp only [expanded] at hs
        simp only [bitValue] at hs
        change bitValue ys*(1+2*bitValue child.quotient)+bitValue difference.result.bits=
          bitNat bit+2*bitValue xs
        nlinarith
      · exact hsmall

/-- Every restoring frame pays a linear divisor-width subtraction and fit.
The base case also pays construction of the literal zero remainder word. -/
theorem divideLoop_cost (xs ys : List Bool) :
    (divideLoop xs ys).clock≤xs.length*(16*ys.length+20)+4*ys.length+2 := by
  induction xs with
  | nil =>
    have hc := fitBits_cost [] ys
    dsimp only [divideLoop,List.length_nil]
    omega
  | cons bit xs ih =>
    have hwidth := (divideLoop_widths xs ys).1
    have hc := subBits_cost (bit::(divideLoop xs ys).remainder) ys false
    have hk := fitBits_cost (bit::(divideLoop xs ys).remainder) ys
    have hs := fitBits_cost
      (subBits (bit::(divideLoop xs ys).remainder) ys false).result.bits ys
    have hm : max (bit::(divideLoop xs ys).remainder).length ys.length=ys.length+1 := by
      simp only [List.length_cons,hwidth]
      omega
    rw [hm] at hc
    rw [divideLoop]
    dsimp only [List.length_cons]
    split <;> dsimp only <;> nlinarith

/-- Total quotient/remainder handles an all-zero divisor by returning zero
quotient and the original input as remainder, with the divisor scan paid. -/
def divideBits (xs ys : List Bool) : DivisionReport :=
  let check := nonzeroBits ys
  if check.nonzero=true then
    let report := divideLoop xs ys
    {report with clock := report.clock+check.clock+1}
  else
    ⟨[],xs,check.clock+1,0⟩

/-- The actual Boolean outputs equal both natural quotient and natural
remainder, including zero divisors and high-zero-padded physical words. -/
theorem divideBits_correct (xs ys : List Bool) :
    bitValue (divideBits xs ys).quotient=bitValue xs/bitValue ys ∧
      bitValue (divideBits xs ys).remainder=bitValue xs%bitValue ys := by
  by_cases hb : (nonzeroBits ys).nonzero=true
  · have hD := (nonzeroBits_correct ys).mp hb
    obtain ⟨he,hr⟩ := divideLoop_invariant xs ys hD
    have hn : bitValue xs=bitValue (divideLoop xs ys).remainder+
        bitValue ys*bitValue (divideLoop xs ys).quotient := by nlinarith
    have hq : bitValue xs/bitValue ys=bitValue (divideLoop xs ys).quotient := by
      rw [hn,Nat.add_mul_div_left _ _ hD,Nat.div_eq_of_lt hr,Nat.zero_add]
    have hm : bitValue xs%bitValue ys=bitValue (divideLoop xs ys).remainder := by
      rw [hn,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr]
    simp only [divideBits,if_pos hb]
    exact ⟨hq.symm,hm.symm⟩
  · have hz : bitValue ys=0 := by
      have hn : ¬0<bitValue ys := by intro hp; exact hb ((nonzeroBits_correct ys).mpr hp)
      omega
    simp only [divideBits,if_neg hb,hz,Nat.div_zero,Nat.mod_zero,bitValue,and_self]

/-- Positive division returns a fixed divisor-width remainder and at most
the literal input width of quotient, without free canonicalization. -/
theorem divideBits_widths {xs ys : List Bool} (hD : 0<bitValue ys) :
    (divideBits xs ys).remainder.length=ys.length ∧
      (divideBits xs ys).quotient.length=xs.length := by
  have hb := (nonzeroBits_correct ys).mpr hD
  simp only [divideBits,if_pos hb]
  exact ⟨(divideLoop_widths xs ys).1,(divideLoop_widths xs ys).2.1⟩

/-- Total division's composed clock includes the actual zero-divisor scan
and every restoring step; no native quotient/remainder is called. -/
theorem divideBits_cost (xs ys : List Bool) :
    (divideBits xs ys).clock≤xs.length*(16*ys.length+20)+7*ys.length+4 := by
  have hs := nonzeroBits_cost ys
  have hc := divideLoop_cost xs ys
  dsimp only [divideBits]
  split <;> dsimp only <;> omega

/-- A dividend up to three input widths, as produced by the scalar bit
multiplier, still has quadratic restoring division work. -/
theorem bounded_divideBits {L : ℕ} {xs ys : List Bool}
    (hx : xs.length≤3*L) (hy : ys.length≤L) :
    (divideBits xs ys).clock≤72*(L+1)^2 := by
  have hc := divideBits_cost xs ys
  have hm := Nat.mul_le_mul hx (by omega : 16*ys.length+20≤16*L+20)
  nlinarith

/-- Actual scalar modular product, with both backend reports and clock. -/
structure ModularProduct where
  /-- Actual Boolean multiplication, including every intermediate bit cell. -/
  product : BitReport
  /-- Actual quotient/remainder computation of the product by the modulus. -/
  division : DivisionReport
  /-- Both clocks and the retained modular report cell. -/
  clock : ℕ

/-- Modular multiplication computes its own Boolean product and restoring
remainder. No supplied integer product or native modulo computes its value. -/
def modMulBits (xs ys modulus : List Bool) : ModularProduct :=
  let product := mulBits xs ys
  let division := divideBits product.bits modulus
  ⟨product,division,bitCost product+division.clock+1⟩

/-- The actual modular output is the literal product residue, for every
modulus value including zero. All natural arithmetic here is specification. -/
theorem modMulBits_correct (xs ys modulus : List Bool) :
    bitValue (modMulBits xs ys modulus).division.remainder=
      (bitValue xs*bitValue ys)%bitValue modulus := by
  have hr := (divideBits_correct (mulBits xs ys).bits modulus).2
  simpa only [modMulBits,mulBits_correct] using hr

/-- Bounded scalar modular multiplication has an explicit quadratic
primitive clock, paying both the product and general remainder backend. -/
theorem bounded_modMulBits {L : ℕ} {xs ys modulus : List Bool}
    (hx : xs.length≤L) (hy : ys.length≤L) (hm : modulus.length≤L) :
    (modMulBits xs ys modulus).clock≤96*(L+1)^2+2 := by
  obtain ⟨hp,hwidth⟩ := bounded_mulBits hx hy
  have hd := bounded_divideBits hwidth hm
  dsimp only [modMulBits]
  omega

/-- Positive scalar moduli keep the actual modular output at their fixed
physical width, so repeated residue products do not grow their input words. -/
theorem modMulBits_width {xs ys modulus : List Bool} (hD : 0<bitValue modulus) :
    (modMulBits xs ys modulus).division.remainder.length=modulus.length :=
  (divideBits_widths (xs:=(mulBits xs ys).bits) hD).1

/-- Every actual modular product and its composed retained-batch clock. -/
structure ModularBatch where
  /-- Computed products, divisions and modular outputs in original order. -/
  products : List ModularProduct
  /-- All modular clocks, traversal tests and retained report cells. -/
  clock : ℕ

/-- Construct every requested modular product and charge its complete
Boolean backend, instead of receiving products or remainder advice. -/
def modMulBatch (modulus : List Bool) : List (List Bool×List Bool) → ModularBatch
  | [] => ⟨[],1⟩
  | pair::tail =>
    let product := modMulBits pair.1 pair.2 modulus
    let rest := modMulBatch modulus tail
    ⟨product::rest.products,product.clock+rest.clock+2⟩

/-- The batch retains one computed report per literal input pair. -/
theorem modMulBatch_length (modulus : List Bool) (pairs : List (List Bool×List Bool)) :
    (modMulBatch modulus pairs).products.length=pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair tail ih => simp only [modMulBatch,List.length_cons,ih]

/-- Every computed batch residue is the literal corresponding product mod
the actual common modulus, including the zero-modulus case. -/
theorem modMulBatch_correct (modulus : List Bool) (pairs : List (List Bool×List Bool)) :
    (modMulBatch modulus pairs).products.map (fun report => bitValue report.division.remainder)=
      pairs.map (fun pair => (bitValue pair.1*bitValue pair.2)%bitValue modulus) := by
  induction pairs with
  | nil => rfl
  | cons pair tail ih => simp only [modMulBatch,List.map_cons,modMulBits_correct,ih]

/-- The composed actual modular batch has linear count and quadratic
physical-width primitive work, with every division and retained cell paid. -/
theorem modMulBatch_cost {L : ℕ} (modulus : List Bool) (pairs : List (List Bool×List Bool))
    (hm : modulus.length≤L) (hw : ∀ pair∈pairs,pair.1.length≤L ∧ pair.2.length≤L) :
    (modMulBatch modulus pairs).clock≤pairs.length*(96*(L+1)^2+4)+1 := by
  induction pairs with
  | nil => simp only [modMulBatch,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons pair tail ih =>
    have hp := hw pair (List.mem_cons_self)
    have hc := bounded_modMulBits hp.1 hp.2 hm
    have ht := ih (fun p h => hw p (List.mem_cons_of_mem _ h))
    simp only [modMulBatch,List.length_cons]
    nlinarith

end RiemannGaussian.SemiprimeBitDivision
