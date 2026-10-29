/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMacroFermatNetwork
import Mathlib.Data.BitVec

/-!
# Concrete finite Boolean multiplication relation

All words are literal finite bit vectors with their standard little-endian
binary decoding. The relation explicitly checks normalized Fourier inversion,
canonical coefficients, INTEGER carries and nontrivial input flags. Its accepted
extensions will be counted by an explicit equivalence, not an assumed semantic
correctness premise. This finite relation does not yet assert the Python
compiler's exact two-stage port layout or its small-arity/wire cost.
-/
namespace RiemannGaussian.SemiprimeBooleanNetwork
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open SemiprimeMacroFermatNetwork

/-- Literal finite-width binary encoding. -/
def encode (width value : ℕ) : BitVec width := BitVec.ofNat width value

/-- Literal little-endian binary decoding. -/
def decode {width : ℕ} (word : BitVec width) : ℕ := word.toNat

/-- Encoding a value within width loses no information. -/
theorem decode_encode {width value : ℕ} (h : value<2^width) :
    decode (encode width value)=value := by
  simp [decode,encode,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h]

/-- Every bit word is the encoding of its decoded value. -/
theorem encode_decode {width : ℕ} (word : BitVec width) :
    encode width (decode word)=word := by
  apply BitVec.eq_of_toNat_eq
  simp [decode,encode]

/-- Binary words and their exact bounded integer values are in bijection. -/
def wordEquiv (width : ℕ) : BitVec width ≃ Fin (2^width) where
  toFun word := ⟨decode word,word.isLt⟩
  invFun value := encode width value.val
  left_inv := encode_decode
  right_inv value := Fin.ext (decode_encode value.isLt)

/-- Enumerate exactly the actual finite binary words through their canonical values. -/
instance bitWordFintype (width : ℕ) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2^width)) (wordEquiv width).symm

/-- Finite digit/word arrays have zero outside their declared ports. -/
def values {size width : ℕ} (words : Fin size→BitVec width) (i : ℕ) : ℕ :=
  if h : i<size then decode (words ⟨i,h⟩) else 0

/-- Decoding at a declared port is exact. -/
theorem values_at {size width : ℕ} (words : Fin size→BitVec width) (i : Fin size) :
    values words i.val=decode (words i) := by simp [values]

/-- Every decoded finite port fits its physical width. -/
theorem values_bound {size width : ℕ} (words : Fin size→BitVec width)
    (i : ℕ) (hi : i<size) : values words i<2^width := by
  simpa [values,hi,decode] using (words ⟨i,hi⟩).isLt

/-- Literal integer value of the input digit ports. -/
def operand {digits bits : ℕ} (words : Fin digits→BitVec bits) : ℕ :=
  ∑ i∈Finset.range digits,values words i*(2^bits)^i


/-- Input digit arithmetic agrees with the literal least-significant-first split. -/
theorem operand_succ {digits bits : ℕ} (words : Fin (digits+1)→BitVec bits) :
    operand words=decode (words 0)+2^bits*operand (fun i : Fin digits => words i.succ) := by
  unfold operand
  rw [radix_sum_succ]
  rw [show values words 0=decode (words 0) by simp [values]]
  congr 1
  apply congrArg (fun x : ℕ => 2^bits*x)
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  simp only [values,show k+1<digits+1 by omega,show k<digits by omega,dite_eq_left]
  rfl

/-- Exact finite digit words always represent an integer within their total width. -/
theorem operand_bound {digits bits : ℕ} (words : Fin digits→BitVec bits) :
    operand words<(2^bits)^digits := by
  induction digits with
  | zero => simp [operand]
  | succ digits ih =>
    rw [operand_succ,pow_succ]
    have ht := ih (fun i => words i.succ)
    have hh := (words 0).isLt
    change decode (words 0)<2^bits at hh
    nlinarith

/-- The positional value is injective on literal fixed-length digit words. -/
theorem operand_injective (digits bits : ℕ) :
    Function.Injective (operand : (Fin digits→BitVec bits)→ℕ) := by
  induction digits with
  | zero => intro x y h; funext i; exact Fin.elim0 i
  | succ digits ih =>
    intro x y he
    rw [operand_succ,operand_succ] at he
    have hx := (x 0).isLt
    have hy := (y 0).isLt
    have hhead : decode (x 0)=decode (y 0) := by
      have hm := congrArg (fun v : ℕ => v%2^bits) he
      simpa [Nat.add_mod,Nat.mul_mod,decode,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] using hm
    have htail : operand (fun i : Fin digits => x i.succ)=
        operand (fun i : Fin digits => y i.succ) := by
      have hp : 0<(2 : ℕ)^bits := by positivity
      nlinarith
    have ht := ih htail
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact BitVec.eq_of_toNat_eq hhead
    · exact congrFun ht j

/-- Input digits are in bijection with the actual bounded integers, not
merely an unspecified finite set of the same size. -/
noncomputable def operandEquiv (digits bits : ℕ) :
    (Fin digits→BitVec bits) ≃ Fin ((2^bits)^digits) :=
  Equiv.ofBijective (fun words => ⟨operand words,operand_bound words⟩) (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    constructor
    · intro x y h
      exact operand_injective digits bits (congrArg Fin.val h)
    · have hc : Fintype.card (BitVec bits)=2^bits :=
        (Fintype.card_congr (wordEquiv bits)).trans (Fintype.card_fin _)
      simp only [Fintype.card_fun,Fintype.card_fin,hc])

/-- The nontriviality flag checks the actual input value, not an oracle. -/
def nontrivialFlag {digits bits : ℕ} (words : Fin digits→BitVec bits) : Bool :=
  decide (2≤operand words)

/-- All actual internal finite Boolean words and two input flags. -/
structure Extension (d : ℕ) where
  /-- Canonical inverse-output coefficient words. -/
  coefficient : Fin (macroLength d)→BitVec (macroLength d+1)
  /-- Physical n-bit carries, including both boundary positions. -/
  carry : Fin (macroLength d+1)→BitVec (macroLength d)
  /-- Nontrivial left-input flag. -/
  leftFlag : Bool
  /-- Nontrivial right-input flag. -/
  rightFlag : Bool
  deriving Fintype

/-- Explicit local-predicate conjunction for the constructed finite relation.
The Fourier inverse formula is computed from the actual inputs, not supplied
as a convolution-correctness hypothesis. -/
def Valid {digits bits : ℕ} (d : ℕ) (left right : Fin digits→BitVec bits)
    (target : ℕ→ℕ) (extension : Extension d) : Prop :=
  ArithmeticNetworkValid d (values left) (values right) target
    (values extension.coefficient) (values extension.carry) digits (2^bits) ∧
  extension.leftFlag=nontrivialFlag left ∧ extension.leftFlag=true ∧
  extension.rightFlag=nontrivialFlag right ∧ extension.rightFlag=true

/-- Explicit finite input-pair predicate corresponding to nontrivial factors. -/
def FactorPair {digits bits : ℕ} (left right : Fin digits→BitVec bits) (N : ℕ) : Prop :=
  2≤operand left ∧ 2≤operand right ∧ operand left*operand right=N

/-- The relation's literal nontriviality flags force both factors to exceed one. -/
theorem valid_nontrivial {digits bits d : ℕ} {left right : Fin digits→BitVec bits}
    {target : ℕ→ℕ} {extension : Extension d} (h : Valid d left right target extension) :
    2≤operand left ∧ 2≤operand right := by
  have hl : nontrivialFlag left=true := h.2.1.symm.trans h.2.2.1
  have hr : nontrivialFlag right=true := h.2.2.2.1.symm.trans h.2.2.2.2
  exact ⟨of_decide_eq_true hl,of_decide_eq_true hr⟩

/-- Accepted bit-word extensions imply the actual nontrivial digit product. -/
theorem valid_sound {digits bits d : ℕ} (left right : Fin digits→BitVec bits)
    (target : ℕ→ℕ) (extension : Extension d)
    (hsize : 2*digits≤macroLength d)
    (hbound : digits*(2^bits)^2<2^(macroLength d)+1)
    (htarget : ∀ i, i<macroLength d → target i<2^bits)
    (h : Valid d left right target extension) :
    FactorPair left right (∑ k∈Finset.range (macroLength d),target k*(2^bits)^k) := by
  have hp := (arithmetic_network_iff d (values left) (values right) target digits (2^bits)
    (by positivity) hsize (values_bound left) (values_bound right) htarget hbound).mp
    ⟨values extension.coefficient,values extension.carry,h.1⟩
  exact ⟨(valid_nontrivial h).1,(valid_nontrivial h).2,hp⟩

/-- The constructed finite Boolean relation has at most one internal
extension for each input pair, including every physical carry bit. -/
theorem valid_unique {digits bits d : ℕ} (left right : Fin digits→BitVec bits)
    (target : ℕ→ℕ) (first second : Extension d)
    (hsize : 2*digits≤macroLength d)
    (hbound : digits*(2^bits)^2<2^(macroLength d)+1)
    (hfirst : Valid d left right target first)
    (hsecond : Valid d left right target second) : first=second := by
  have hu := arithmetic_network_unique d (values left) (values right) target
    (values first.coefficient) (values second.coefficient)
    (values first.carry) (values second.carry) digits (2^bits) (by positivity)
    hsize (values_bound left) (values_bound right) hbound hfirst.1 hsecond.1
  have hc : first.coefficient=second.coefficient := by
    funext j
    apply BitVec.eq_of_toNat_eq
    simpa only [values_at,decode] using hu.1 j.val j.isLt
  have hk : first.carry=second.carry := by
    funext j
    apply BitVec.eq_of_toNat_eq
    simpa only [values_at,decode] using hu.2 j.val (by have := j.isLt; omega)
  have hl : first.leftFlag=second.leftFlag := hfirst.2.1.trans hsecond.2.1.symm
  have hr : first.rightFlag=second.rightFlag := hfirst.2.2.2.1.trans hsecond.2.2.2.1.symm
  cases first
  cases second
  simp_all

/-- Every true nontrivial input product has a valid finite bit extension.
The strict physical carry capacity is derived, not assumed as a witness. -/
theorem valid_complete {digits bits d : ℕ} (left right : Fin digits→BitVec bits)
    (target : ℕ→ℕ) (hbits : 0<bits) (hquarter : macroLength d=4*bits)
    (hdigits : digits≤bits) (htarget : ∀ i, i<macroLength d → target i<2^bits)
    (hpair : FactorPair left right
      (∑ k∈Finset.range (macroLength d),target k*(2^bits)^k)) :
    ∃ extension,Valid d left right target extension := by
  let n := macroLength d
  have hn : 0<n := by dsimp [n,macroLength]; positivity
  have hsize : 2*digits≤n := by dsimp [n]; omega
  have hstrict := compiler_quarter_strict_bound digits bits n hdigits hbits hquarter
  have hbound : digits*(2^bits)^2<2^n+1 := by omega
  obtain ⟨output,carry,harith⟩ :=
    (arithmetic_network_iff d (values left) (values right) target digits (2^bits)
      (by positivity) hsize (values_bound left) (values_bound right) htarget hbound).mpr hpair.2.2
  have heq := canonical_inverse_convolution d (values left) (values right) output
    digits (2^bits) hsize (values_bound left) (values_bound right) hbound harith.1 harith.2.1
  have hc : ∀ k, k<n → output k≤digits*(2^bits)^2 := by
    intro k hk
    rw [heq k hk]
    exact convolution_bound _ _ digits (2^bits) k (values_bound left) (values_bound right)
  have hcap := compiler_carry_capacity output target carry digits bits n hdigits hbits
    hquarter harith.2.2.1 hc harith.2.2.2.2
  have hout : ∀ k, k<n → output k<2^(n+1) := by
    intro k hk
    have hp : 0<(2 : ℕ)^n := by positivity
    have hh := harith.1 k hk
    change output k<2^n+1 at hh
    rw [pow_succ]
    omega
  let extension : Extension d :=
    ⟨fun i => encode (n+1) (output i.val),fun i => encode n (carry i.val),
      nontrivialFlag left,nontrivialFlag right⟩
  have ho : ∀ k, k<n → values extension.coefficient k=output k := by
    intro k hk
    exact (values_at extension.coefficient ⟨k,hk⟩).trans (decode_encode (hout k hk))
  have hh : ∀ k, k≤n → values extension.carry k=carry k := by
    intro k hk
    exact (values_at extension.carry ⟨k,by omega⟩).trans (decode_encode (hcap k hk))
  refine ⟨extension,?_,rfl,?_,rfl,?_⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · intro k hk
      rw [ho k hk]
      exact harith.1 k hk
    · intro k hk
      rw [ho k hk]
      exact harith.2.1 k hk
    · rw [hh 0 (by omega)]
      exact harith.2.2.1
    · rw [hh n (by omega)]
      exact harith.2.2.2.1
    · intro k hk
      rw [ho k hk,hh k (by omega),hh (k+1) (by omega)]
      exact harith.2.2.2.2 k hk
  · exact decide_eq_true hpair.1
  · exact decide_eq_true hpair.2.1

/-- One accepted input pair contributes exactly one Boolean extension;
a false pair contributes none. No extension-count oracle is assumed. -/
theorem extension_count {digits bits d : ℕ} (left right : Fin digits→BitVec bits)
    (target : ℕ→ℕ) (hbits : 0<bits) (hquarter : macroLength d=4*bits)
    (hdigits : digits≤bits) (htarget : ∀ i, i<macroLength d → target i<2^bits) :
    (∑ extension : Extension d,if Valid d left right target extension then (1 : ℕ) else 0)=
      if FactorPair left right
        (∑ k∈Finset.range (macroLength d),target k*(2^bits)^k) then 1 else 0 := by
  classical
  have hsize : 2*digits≤macroLength d := by omega
  have hstrict := compiler_quarter_strict_bound digits bits (macroLength d) hdigits hbits hquarter
  have hbound : digits*(2^bits)^2<2^(macroLength d)+1 := by omega
  by_cases hp : FactorPair left right
      (∑ k∈Finset.range (macroLength d),target k*(2^bits)^k)
  · rw [ite_eq_left hp]
    obtain ⟨extension,he⟩ := valid_complete left right target hbits hquarter hdigits htarget hp
    rw [Finset.sum_eq_single extension]
    · exact ite_eq_left he
    · intro other ho hne
      apply ite_eq_right
      intro hother
      exact hne (valid_unique left right target other extension hsize hbound hother he)
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ extension))
  · rw [ite_eq_right hp]
    apply Finset.sum_eq_zero
    intro extension he
    apply ite_eq_right
    intro hv
    exact hp (valid_sound left right target extension hsize hbound htarget hv)

/-- The literal 0/1 Boolean-relation contraction over all input and internal
bit words. This is a definition by finite sums, not an execution-time claim. -/
noncomputable def contraction (d digits bits : ℕ) (target : ℕ→ℕ) : ℕ := by
  classical
  exact ∑ left : Fin digits→BitVec bits,∑ right : Fin digits→BitVec bits,
    ∑ extension : Extension d,if Valid d left right target extension then 1 else 0

/-- The constructed Boolean relation counts precisely the ordered nontrivial
INTEGER factor pairs within its input width. The only numerical premises are
public radix, coefficient-capacity and target-digit bounds. -/
theorem contraction_counts_factor_pairs (d digits bits : ℕ) (target : ℕ→ℕ)
    (hbits : 0<bits) (hquarter : macroLength d=4*bits) (hdigits : digits≤bits)
    (htarget : ∀ i, i<macroLength d → target i<2^bits) :
    contraction d digits bits target=
      ∑ P : Fin ((2^bits)^digits),∑ Q : Fin ((2^bits)^digits),
        if 2≤P.val ∧ 2≤Q.val ∧ P.val*Q.val=
          (∑ k∈Finset.range (macroLength d),target k*(2^bits)^k) then 1 else 0 := by
  classical
  unfold contraction
  simp_rw [extension_count _ _ target hbits hquarter hdigits htarget]
  apply Fintype.sum_equiv (operandEquiv digits bits)
  intro left
  apply Fintype.sum_equiv (operandEquiv digits bits)
  intro right
  simp only [FactorPair,operandEquiv,Equiv.ofBijective_apply]
  split_ifs with h <;> simp [h]

/-- The bit vector is precisely its ordered list of Boolean least-significant
ports; thus the relation really is a finite Boolean assignment relation. -/
theorem bit_ports_bijective (width : ℕ) :
    Function.Bijective (fun word : BitVec width => word.getLsb) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro x y he
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact congrFun he ⟨i,hi⟩
  · have hc : Fintype.card (BitVec width)=2^width :=
      (Fintype.card_congr (wordEquiv width)).trans (Fintype.card_fin _)
    simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool] using hc

/-- Literal Boolean port conversion, with no unspecified enumeration. -/
noncomputable def bitPortsEquiv (width : ℕ) : BitVec width ≃ (Fin width→Bool) :=
  Equiv.ofBijective (fun word => word.getLsb) (bit_ports_bijective width)

/-- Subdividing every Boolean edge inserts one actual equality predicate;
every original accepted assignment has exactly one copy assignment. -/
theorem equality_subdivision_count {I : Type*} [Fintype I] (accepted : (I→Bool)→Prop) :
    (∑ original : I→Bool,∑ copy : I→Bool,
      if (∀ i,copy i=original i) ∧ accepted original then (1 : ℕ) else 0)=
      ∑ original : I→Bool,if accepted original then 1 else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro original ho
  have he : (∑ copy : I→Bool,
      if (∀ i,copy i=original i) ∧ accepted original then (1 : ℕ) else 0)=
      ∑ copy : I→Bool,if copy=original then (if accepted original then 1 else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro copy hc
    by_cases hp : copy=original
    · subst copy
      simp
    · have hn : ¬∀ i,copy i=original i := fun h => hp (funext h)
      simp [hp,hn]
  rw [he]
  simp

/-- Explicit vertices of the constructed finite relational network. -/
inductive Check (d : ℕ)
  | canonical : Fin (macroLength d)→Check d
  | inverse : Fin (macroLength d)→Check d
  | carry : Fin (macroLength d)→Check d
  | initial : Check d
  | terminal : Check d
  | leftValue : Check d
  | leftTrue : Check d
  | rightValue : Check d
  | rightTrue : Check d
  deriving DecidableEq,Fintype

/-- Literal local arithmetic/flag predicates; the inverse vertex reads all
input digits but only its single output coefficient. Its scope is therefore
larger than the Python compiler's two-stage macro implementation. -/
def localCheck {digits bits : ℕ} (d : ℕ) (left right : Fin digits→BitVec bits)
    (target : ℕ→ℕ) (extension : Extension d) : Check d→Prop
  | .canonical j => values extension.coefficient j.val<2^(macroLength d)+1
  | .inverse j =>
      (macroLength d : MacroRing d)*(values extension.coefficient j.val : MacroRing d)=
        fourier 4 (macroLength d)
          (fun k => fourier 4 digits (fun i => (values left i : MacroRing d)) k*
            fourier 4 digits (fun i => (values right i : MacroRing d)) k)
          (if j.val=0 then 0 else macroLength d-j.val)
  | .carry j => values extension.coefficient j.val+values extension.carry j.val=
      target j.val+2^bits*values extension.carry (j.val+1)
  | .initial => values extension.carry 0=0
  | .terminal => values extension.carry (macroLength d)=0
  | .leftValue => extension.leftFlag=nontrivialFlag left
  | .leftTrue => extension.leftFlag=true
  | .rightValue => extension.rightFlag=nontrivialFlag right
  | .rightTrue => extension.rightFlag=true

/-- Validity is DERIVED equivalent to all literal local checks. -/
theorem valid_iff_local {digits bits d : ℕ} (left right : Fin digits→BitVec bits)
    (target : ℕ→ℕ) (extension : Extension d) :
    Valid d left right target extension ↔ ∀ check,localCheck d left right target extension check := by
  constructor
  · intro h check
    cases check with
    | canonical j => exact h.1.1 j.val j.isLt
    | inverse j => exact h.1.2.1 j.val j.isLt
    | carry j => exact h.1.2.2.2.2 j.val j.isLt
    | initial => exact h.1.2.2.1
    | terminal => exact h.1.2.2.2.1
    | leftValue => exact h.2.1
    | leftTrue => exact h.2.2.1
    | rightValue => exact h.2.2.2.1
    | rightTrue => exact h.2.2.2.2
  · intro h
    refine ⟨⟨?_,?_,h .initial,h .terminal,?_⟩,
      h .leftValue,h .leftTrue,h .rightValue,h .rightTrue⟩
    · intro j hj
      exact h (.canonical ⟨j,hj⟩)
    · intro j hj
      exact h (.inverse ⟨j,hj⟩)
    · intro j hj
      exact h (.carry ⟨j,hj⟩)

/-- Every local tensor is an actual computed zero/one predicate. -/
noncomputable def localEntry {digits bits : ℕ} (d : ℕ) (left right : Fin digits→BitVec bits)
    (target : ℕ→ℕ) (extension : Extension d) (check : Check d) : ℕ :=
  if localCheck d left right target extension check then 1 else 0

/-- The local tensor product agrees with validity; no graph-semantic
correctness assumption is used. -/
theorem local_product {digits bits d : ℕ} (left right : Fin digits→BitVec bits)
    (target : ℕ→ℕ) (extension : Extension d) :
    (∏ check : Check d,localEntry d left right target extension check)=
      if Valid d left right target extension then 1 else 0 := by
  classical
  by_cases hp : Valid d left right target extension
  · rw [ite_eq_left hp]
    apply Finset.prod_eq_one
    intro check hc
    exact ite_eq_left ((valid_iff_local left right target extension).mp hp check)
  · rw [ite_eq_right hp]
    have hn : ¬∀ check,localCheck d left right target extension check :=
      fun h => hp ((valid_iff_local left right target extension).mpr h)
    obtain ⟨check,hcheck⟩ := not_forall.mp hn
    apply Finset.prod_eq_zero (Finset.mem_univ check)
    exact ite_eq_right hcheck

/-- Summing the literal local 0/1 tensor product counts nontrivial factor
pairs. The displayed larger inverse scopes are not a free small-port compiler. -/
theorem local_contraction_counts_factor_pairs (d digits bits : ℕ) (target : ℕ→ℕ)
    (hbits : 0<bits) (hquarter : macroLength d=4*bits) (hdigits : digits≤bits)
    (htarget : ∀ i, i<macroLength d → target i<2^bits) :
    (∑ left : Fin digits→BitVec bits,∑ right : Fin digits→BitVec bits,
      ∑ extension : Extension d,∏ check : Check d,localEntry d left right target extension check)=
      ∑ P : Fin ((2^bits)^digits),∑ Q : Fin ((2^bits)^digits),
        if 2≤P.val ∧ 2≤Q.val ∧ P.val*Q.val=
          (∑ k∈Finset.range (macroLength d),target k*(2^bits)^k) then 1 else 0 := by
  simp_rw [local_product]
  exact contraction_counts_factor_pairs d digits bits target hbits hquarter hdigits htarget

end RiemannGaussian.SemiprimeBooleanNetwork
