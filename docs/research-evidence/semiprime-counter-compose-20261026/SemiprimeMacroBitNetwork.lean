/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBooleanNetwork

/-!
# Actual canonical macro-transform arrays

The first DFT, twiddle and second DFT arrays use the compiler's literal two-axis
indices. Their equations have unique canonical bit extensions, and their output
is derived equal to the flat transform. This module separately counts the
compiler's tagged word/flag signal family; no graph wiring or time bound is
assumed from that cardinality.
-/
noncomputable section

namespace RiemannGaussian.SemiprimeMacroBitNetwork
open scoped BigOperators
open SemiprimeMacroFermatNetwork SemiprimeBooleanNetwork
attribute [local instance] Classical.propDecidable

/-- Canonical physical `(n+1)`-bit residue word. -/
abbrev ResidueWord (d : ℕ) :=
  {word : BitVec (macroLength d+1) // decode word<2^(macroLength d)+1}

/-- Finite enumeration of all canonical physical words. -/
noncomputable instance residueWordFintype (d : ℕ) : Fintype (ResidueWord d) := Fintype.ofFinite _

/-- A canonical physical word's actual ring value. -/
def residueValue {d : ℕ} (word : ResidueWord d) : MacroRing d := (decode word.val : MacroRing d)

/-- Encode the actual canonical representative of a ring value. -/
def residueWord (d : ℕ) (value : MacroRing d) : ResidueWord d := by
  have : NeZero (2^(macroLength d)+1) := ⟨by positivity⟩
  have hv := ZMod.val_lt value
  have hp : 0<(2 : ℕ)^(macroLength d) := by positivity
  have hw : value.val<2^(macroLength d+1) := by rw [pow_succ]; omega
  exact ⟨encode (macroLength d+1) value.val,by rw [decode_encode hw];exact hv⟩

/-- Canonical binary encoding does not alter the ring value. -/
theorem residueValue_word (d : ℕ) (value : MacroRing d) :
    residueValue (residueWord d value)=value := by
  have : NeZero (2^(macroLength d)+1) := ⟨by positivity⟩
  unfold residueValue residueWord
  have hv := ZMod.val_lt value
  have hp : 0<(2 : ℕ)^(macroLength d) := by positivity
  have hw : value.val<2^(macroLength d+1) := by rw [pow_succ]; omega
  rw [decode_encode hw]
  exact ZMod.natCast_zmod_val value

/-- Canonical physical words are determined by their ring value. -/
theorem residueValue_injective (d : ℕ) : Function.Injective (@residueValue d) := by
  intro x y h
  apply Subtype.ext
  apply BitVec.eq_of_toNat_eq
  exact canonical_nat_unique _ _ _ x.property y.property h

/-- Three actual intermediate arrays for the compiler's transform stages. -/
structure MacroArrays (d r t : ℕ) where
  /-- First-stage output at `(j1,k2)`. -/
  first : Fin r→Fin t→ResidueWord d
  /-- Explicit twiddle output at `(j1,k2)`. -/
  twiddle : Fin r→Fin t→ResidueWord d
  /-- Final output at `(k2,k1)`, flat slot `k2+t*k1`. -/
  second : Fin t→Fin r→ResidueWord d
  deriving Fintype

/-- Literal small-port stage predicates, including the second-stage
normalizer (one forward, inverse length for inverse transforms). -/
def MacroValid (d r t : ℕ) (w normalizer : MacroRing d) (input : ℕ→MacroRing d)
    (a : MacroArrays d r t) : Prop :=
  (∀ j₁ k₂, residueValue (a.first j₁ k₂)=
    ∑ j₂∈Finset.range t,input (j₁.val+r*j₂)*(w^r)^(j₂*k₂.val)) ∧
  (∀ j₁ k₂,residueValue (a.twiddle j₁ k₂)=residueValue (a.first j₁ k₂)*w^(j₁.val*k₂.val)) ∧
  (∀ k₂ k₁,residueValue (a.second k₂ k₁)=normalizer*
    ∑ j₁ : Fin r,residueValue (a.twiddle j₁ k₂)*(w^t)^(j₁.val*k₁.val))

/-- Construct every canonical word through the same three arithmetic stages. -/
def buildMacro (d r t : ℕ) (w normalizer : MacroRing d) (input : ℕ→MacroRing d) :
    MacroArrays d r t :=
  let first := fun (j₁ : Fin r) (k₂ : Fin t) => residueWord d
    (∑ j₂∈Finset.range t,input (j₁.val+r*j₂)*(w^r)^(j₂*k₂.val))
  let twiddle := fun j₁ k₂ => residueWord d (residueValue (first j₁ k₂)*w^(j₁.val*k₂.val))
  let second := fun k₂ k₁ => residueWord d (normalizer*
    ∑ j₁ : Fin r,residueValue (twiddle j₁ k₂)*(w^t)^(j₁.val*k₁.val))
  ⟨first,twiddle,second⟩

/-- All constructed stage predicates hold, without an assumed macro identity. -/
theorem buildMacro_valid (d r t : ℕ) (w normalizer : MacroRing d) (input : ℕ→MacroRing d) :
    MacroValid d r t w normalizer input (buildMacro d r t w normalizer input) := by
  refine ⟨?_,?_,?_⟩ <;> intros <;> exact residueValue_word d _

/-- Every first-stage, twiddle and second-stage bit is uniquely determined. -/
theorem macro_valid_unique (d r t : ℕ) (w normalizer : MacroRing d) (input : ℕ→MacroRing d)
    (a b : MacroArrays d r t) (ha : MacroValid d r t w normalizer input a)
    (hb : MacroValid d r t w normalizer input b) : a=b := by
  have hf : a.first=b.first := by
    funext j₁ k₂
    apply residueValue_injective d
    rw [ha.1,hb.1]
  have ht : a.twiddle=b.twiddle := by
    funext j₁ k₂
    apply residueValue_injective d
    rw [ha.2.1,hb.2.1,hf]
  have hs : a.second=b.second := by
    funext k₂ k₁
    apply residueValue_injective d
    rw [ha.2.2,hb.2.2,ht]
  cases a
  cases b
  simp_all

/-- Small-port stage equations imply the actual flat normalized DFT, with
the compiler's exact output index and twiddle convention. -/
theorem macro_valid_output (d r t : ℕ) (w normalizer : MacroRing d) (input : ℕ→MacroRing d)
    (a : MacroArrays d r t) (ha : MacroValid d r t w normalizer input a)
    (hw : w^(r*t)=1) (k₂ : Fin t) (k₁ : Fin r) :
    residueValue (a.second k₂ k₁)=normalizer*fourier w (r*t) input (k₂.val+t*k₁.val) := by
  rw [ha.2.2,←macroFourier_eq_fourier w r t input k₁.val k₂.val hw]
  unfold macroFourier
  apply congrArg (fun x => normalizer*x)
  simp_rw [ha.2.1,ha.1]
  rw [Fin.sum_univ_eq_sum_range (fun j₁ : ℕ =>
    (∑ j₂∈Finset.range t,input (j₁+r*j₂)*(w^r)^(j₂*k₂.val))*
      w^(j₁*k₂.val)*(w^t)^(j₁*k₁.val)) r]
  apply Finset.sum_congr rfl
  intro j₁ hj₁
  ring

/-- Adding all actual macro intermediates preserves any downstream output
predicate's zero/one contribution; there is no free transform oracle. -/
theorem macro_extension_count (d r t : ℕ) (w normalizer : MacroRing d) (input : ℕ→MacroRing d)
    (accepted : (Fin t→Fin r→ResidueWord d)→Prop) :
    (∑ a : MacroArrays d r t,if MacroValid d r t w normalizer input a ∧ accepted a.second
      then (1 : ℕ) else 0)=
    if accepted (buildMacro d r t w normalizer input).second then 1 else 0 := by
  classical
  let built := buildMacro d r t w normalizer input
  have hv : MacroValid d r t w normalizer input built := buildMacro_valid d r t w normalizer input
  rw [Finset.sum_eq_single built]
  · simp only [hv,true_and]
    split_ifs with h <;> simp_all [built]
  · intro a ha hne
    apply ite_eq_right
    intro h
    exact hne (macro_valid_unique d r t w normalizer input a built h.1 hv)
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ built))


/-- The literal inverse root is a public power, requiring no modular inverse
oracle or prime-modulus hypothesis. -/
def inverseRoot (d : ℕ) : MacroRing d := (4 : MacroRing d)^(macroLength d-1)

/-- This public power is exactly a multiplicative inverse of the compiler root. -/
theorem inverseRoot_mul (d : ℕ) : inverseRoot d*(4 : MacroRing d)=1 := by
  have hp : 0<macroLength d := by unfold macroLength; positivity
  have hn : 1≤macroLength d := by omega
  unfold inverseRoot
  rw [←pow_succ,Nat.sub_add_cancel hn,root_four_period]

/-- The inverse-root transform has the same complete period. -/
theorem inverseRoot_period (d : ℕ) : (inverseRoot d)^(macroLength d)=1 := by
  unfold inverseRoot
  rw [←pow_mul,Nat.mul_comm, pow_mul,root_four_period,one_pow]

/-- Inverse-root phases equal the exact zero-plus-reflected frequency phases. -/
theorem inverseRoot_power (d : ℕ) (k : ℕ) (hk : k<macroLength d) :
    (inverseRoot d)^k=(4 : MacroRing d)^(if k=0 then 0 else macroLength d-k) := by
  by_cases hk0 : k=0
  · subst k
    simp
  · rw [ite_eq_right hk0]
    have hw : (4 : MacroRing d)^k*4^(macroLength d-k)=1 := by
      rw [←pow_add,Nat.add_sub_of_le (le_of_lt hk),root_four_period]
    have hi : (inverseRoot d)^k*(4 : MacroRing d)^k=1 := by
      rw [←mul_pow,inverseRoot_mul,one_pow]
    calc
      (inverseRoot d)^k=(inverseRoot d)^k*((4 : MacroRing d)^k*4^(macroLength d-k)) := by rw [hw,mul_one]
      _ = ((inverseRoot d)^k*(4 : MacroRing d)^k)*4^(macroLength d-k) := by ring
      _ = _ := by rw [hi,one_mul]

/-- The small-port inverse transform satisfies the EXACT normalized reflected
Fourier equation used by the arithmetic multiplication bridge. -/
theorem macro_valid_inverse (d r t : ℕ) (normalizer : MacroRing d)
    (input : ℕ→MacroRing d) (a : MacroArrays d r t)
    (ha : MacroValid d r t (inverseRoot d) normalizer input a)
    (hshape : r*t=macroLength d)
    (hnormalizer : (macroLength d : MacroRing d)*normalizer=1)
    (k₂ : Fin t) (k₁ : Fin r) :
    (macroLength d : MacroRing d)*residueValue (a.second k₂ k₁)=
      fourier 4 (macroLength d) input
        (if k₂.val+t*k₁.val=0 then 0 else macroLength d-(k₂.val+t*k₁.val)) := by
  have hp : (inverseRoot d)^(r*t)=1 := by rw [hshape,inverseRoot_period]
  rw [macro_valid_output d r t (inverseRoot d) normalizer input a ha hp k₂ k₁,
    ←mul_assoc,hnormalizer,one_mul,hshape]
  have hk : k₂.val+t*k₁.val<macroLength d := by
    have h₁ := k₁.isLt
    have h₂ := k₂.isLt
    nlinarith
  unfold fourier
  apply Finset.sum_congr rfl
  intro j hj
  rw [show j*(k₂.val+t*k₁.val)=(k₂.val+t*k₁.val)*j by ring,pow_mul,
    inverseRoot_power d _ hk,←pow_mul]
  congr 2
  ring


/-- The compiler's actual final flattening uses `k=k2+t*k1`. -/
def flatOutput {d r t : ℕ} (a : MacroArrays d r t) (k : Fin (r*t)) : ResidueWord d :=
  let axes := (finProdFinEquiv : Fin r×Fin t ≃ Fin (r*t)).symm k
  a.second axes.2 axes.1

/-- The flat second-stage array equals the literal normalized full DFT. -/
theorem flatOutput_value (d r t : ℕ) (w normalizer : MacroRing d) (input : ℕ→MacroRing d)
    (a : MacroArrays d r t) (ha : MacroValid d r t w normalizer input a)
    (hw : w^(r*t)=1) (k : Fin (r*t)) :
    residueValue (flatOutput a k)=normalizer*fourier w (r*t) input k.val := by
  let axes := (finProdFinEquiv : Fin r×Fin t ≃ Fin (r*t)).symm k
  have he := congrArg Fin.val
    ((finProdFinEquiv : Fin r×Fin t ≃ Fin (r*t)).apply_symm_apply k)
  change axes.2.val+t*axes.1.val=k.val at he
  change residueValue (a.second axes.2 axes.1)=_
  rw [macro_valid_output d r t w normalizer input a ha hw axes.2 axes.1,he]

/-- The flat actual inverse array satisfies the previous arithmetic network's
normalized inverse equation at every output slot. -/
theorem flatOutput_inverse (d r t : ℕ) (normalizer : MacroRing d) (input : ℕ→MacroRing d)
    (a : MacroArrays d r t) (ha : MacroValid d r t (inverseRoot d) normalizer input a)
    (hshape : r*t=macroLength d)
    (hnormalizer : (macroLength d : MacroRing d)*normalizer=1) (k : Fin (r*t)) :
    (macroLength d : MacroRing d)*residueValue (flatOutput a k)=
      fourier 4 (macroLength d) input (if k.val=0 then 0 else macroLength d-k.val) := by
  let axes := (finProdFinEquiv : Fin r×Fin t ≃ Fin (r*t)).symm k
  have he := congrArg Fin.val
    ((finProdFinEquiv : Fin r×Fin t ≃ Fin (r*t)).apply_symm_apply k)
  change axes.2.val+t*axes.1.val=k.val at he
  change (macroLength d : MacroRing d)*residueValue (a.second axes.2 axes.1)=_
  rw [macro_valid_inverse d r t normalizer input a ha hshape hnormalizer axes.2 axes.1,he]

/-- The second-stage normalizer exists inside the actual ring by the proved
unit-length theorem; it is not an assumption of a field inversion oracle. -/
theorem length_normalizer_exists (d : ℕ) :
    ∃ normalizer : MacroRing d,(macroLength d : MacroRing d)*normalizer=1 := by
  obtain ⟨u,hu⟩ := macro_length_unit d
  refine ⟨(↑(u⁻¹) : MacroRing d),?_⟩
  rw [←hu]
  exact Units.mul_inv u


/-- Actual successive one-bit OR outputs, starting from the first digit flag. -/
def orOutputs (previous : Bool) : List Bool→List Bool
  | [] => []
  | flag::tail => (previous || flag)::orOutputs (previous || flag) tail

/-- Literal local OR-vertex equations, including the exact output-list shape. -/
def OrValid (previous : Bool) : List Bool→List Bool→Prop
  | [],output => output=[]
  | _::_,[] => False
  | flag::tail,next::rest => next=(previous || flag) ∧ OrValid next tail rest

/-- The OR chain's local equations have exactly the constructed output bits. -/
theorem or_valid_iff (previous : Bool) (input output : List Bool) :
    OrValid previous input output ↔ output=orOutputs previous input := by
  induction input generalizing previous output with
  | nil => simp [OrValid,orOutputs]
  | cons flag tail ih =>
    cases output with
    | nil => simp [OrValid,orOutputs]
    | cons next rest =>
      simp only [OrValid,orOutputs,List.cons.injEq,ih]
      constructor
      · rintro ⟨rfl,h⟩
        exact ⟨rfl,h⟩
      · rintro ⟨rfl,h⟩
        exact ⟨rfl,h⟩

/-- No hidden flag extension multiplicity is introduced by an OR chain. -/
theorem or_unique_extension (previous : Bool) (input : List Bool) :
    ∃! output,OrValid previous input output := by
  refine ⟨orOutputs previous input,(or_valid_iff previous input _).mpr rfl,?_⟩
  intro output ho
  exact (or_valid_iff previous input output).mp ho

/-- Exactly one output bit is generated per non-initial digit flag. -/
theorem or_output_length (previous : Bool) (input : List Bool) :
    (orOutputs previous input).length=input.length := by
  induction input generalizing previous with
  | nil => rfl
  | cons flag tail ih => simp only [orOutputs,List.length_cons,ih]

/-- Read the final wire of the actual sequential OR chain. -/
def lastFlag (previous : Bool) : List Bool→Bool
  | [] => previous
  | flag::tail => lastFlag flag tail

/-- The final check is exactly OR of the initial flag and remaining digits. -/
theorem or_terminal (previous : Bool) (input : List Bool) :
    lastFlag previous (orOutputs previous input)=(previous || input.any id) := by
  induction input generalizing previous with
  | nil => simp [lastFlag,orOutputs]
  | cons flag tail ih => simp [lastFlag,orOutputs,ih,Bool.or_assoc]


/-- Ordinary high-digit flags detect positivity of the actual radix tail. -/
theorem digit_tail_positive (base : ℕ) (hbase : 0<base) (input : List ℕ) :
    (input.map (fun digit => decide (digit≠0))).any id=true ↔
      0<Nat.ofDigits base input := by
  induction input with
  | nil => simp
  | cons digit tail ih =>
    simp only [List.map_cons,List.any_cons,id_eq,Bool.or_eq_true,decide_eq_true_eq,
      ih,Nat.ofDigits_cons]
    constructor
    · intro h
      rcases h with hd | ht
      · omega
      · have hp := Nat.mul_pos hbase ht
        omega
    · intro h
      by_cases hd : digit=0
      · right
        have ht : Nat.ofDigits base tail≠0 := by intro hz;rw [hd,hz] at h;simp at h
        omega
      · exact Or.inl hd

/-- The actual initial-digit flag and sequential OR outputs implement
nontriviality, not an assumed decoded-value flag oracle. -/
theorem digit_or_nontrivial (base head : ℕ) (tail : List ℕ) (hbase : 2≤base) :
    lastFlag (decide (2≤head))
      (orOutputs (decide (2≤head)) (tail.map (fun digit => decide (digit≠0))))=true ↔
        2≤Nat.ofDigits base (head::tail) := by
  rw [or_terminal]
  simp only [Bool.or_eq_true,decide_eq_true_eq,digit_tail_positive base (by omega),Nat.ofDigits_cons]
  constructor
  · intro h
    rcases h with hh | ht
    · omega
    · have hp := Nat.mul_le_mul hbase (show 1≤Nat.ofDigits base tail by omega)
      omega
  · intro h
    by_cases ht : 0<Nat.ofDigits base tail
    · exact Or.inr ht
    · left
      have hz : Nat.ofDigits base tail=0 := by omega
      rw [hz] at h
      simpa using h

/-- The actual finite input array and its literal digit list have identical
integer meaning, including leading zero padding. -/
theorem input_digit_evaluation {digits bits : ℕ} (words : Fin digits→BitVec bits) :
    Nat.ofDigits (2^bits) (List.ofFn (fun i => decode (words i)))=operand words := by
  induction digits with
  | zero => simp [operand]
  | succ digits ih => rw [List.ofFn_succ,Nat.ofDigits_cons,operand_succ,ih]

/-- The compiler's digit flags and actual `digits-1` OR chain replace the
previous whole-operand flag exactly. No extra global flag vertex is required. -/
theorem actual_input_flag {digits bits : ℕ} (words : Fin (digits+1)→BitVec bits)
    (hbits : 0<bits) :
    lastFlag (decide (2≤decode (words 0)))
      (orOutputs (decide (2≤decode (words 0)))
        ((List.ofFn (fun i : Fin digits => decode (words i.succ))).map
          (fun digit => decide (digit≠0))))=true ↔ nontrivialFlag words=true := by
  have hb : 2≤(2 : ℕ)^bits := by
    calc
      2=(2 : ℕ)^1 := by norm_num
      _ ≤ 2^bits := Nat.pow_le_pow_right (by omega) hbits
  rw [digit_or_nontrivial (2^bits) (decode (words 0)) _ hb]
  have he := input_digit_evaluation words
  rw [List.ofFn_succ,Nat.ofDigits_cons] at he
  change 2≤decode (words 0)+2^bits*Nat.ofDigits (2^bits)
    (List.ofFn (fun i : Fin digits => decode (words i.succ))) ↔ decide (2≤operand words)=true
  rw [he]
  exact decide_eq_true_iff.symm

/-- The compiler's actual word-producing signal families: two input arrays,
three stages in each of three transforms, products, and all carry words. -/
abbrev WordSignal (n : ℕ) :=
  (Fin 2×Fin n) ⊕ (Fin 3×Fin 3×Fin n) ⊕ Fin n ⊕ Fin (n+1)

/-- Literal digit-flag and non-initial OR-output signal families. -/
abbrev FlagSignal (digits : ℕ) :=
  (Fin 2×Fin digits) ⊕ (Fin 2×Fin (digits-1))

/-- Each word signal has n+1 physical Boolean ports, each flag one. -/
abbrev SignalBit (n digits : ℕ) :=
  (WordSignal n×Fin (n+1)) ⊕ FlagSignal digits

/-- Every original signal bit is split into its two equality-host edges. -/
abbrev SubdividedBit (n digits : ℕ) := SignalBit n digits×Bool

/-- The thirteen full word arrays and the initial carry are counted exactly. -/
theorem word_signal_count (n : ℕ) : Fintype.card (WordSignal n)=13*n+1 := by
  simp only [WordSignal,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  ring

/-- Every generated digit flag and every actual OR output is counted. -/
theorem flag_signal_count (digits : ℕ) (hdigits : 0<digits) :
    Fintype.card (FlagSignal digits)=4*digits-2 := by
  simp only [FlagSignal,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

/-- Exact count of the compiler's generated pre-subdivision bit signals.
This counts concrete tagged signals, not a claimed graph-incidence theorem. -/
theorem signal_bit_count (n digits : ℕ) (hdigits : 0<digits) :
    Fintype.card (SignalBit n digits)=(13*n+1)*(n+1)+4*digits-2 := by
  change Fintype.card ((WordSignal n×Fin (n+1)) ⊕ FlagSignal digits)=_
  rw [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
    word_signal_count,flag_signal_count digits hdigits]
  omega

/-- Equality subdivision doubles the generated bit-edge signal count exactly. -/
theorem subdivided_bit_count (n digits : ℕ) (hdigits : 0<digits) :
    Fintype.card (SubdividedBit n digits)=2*((13*n+1)*(n+1)+4*digits-2) := by
  simp only [SubdividedBit,Fintype.card_prod,Fintype.card_bool,signal_bit_count n digits hdigits]
  omega

/-- Actual arithmetic macro vertex port counts: first DFT, explicit scale,
second DFT, point product and INTEGER carry. Flags are separate one-bit ports. -/
def arithmeticArities (n r t : ℕ) : Fin 5→ℕ :=
  ![2*t*(n+1),2*(n+1),2*r*(n+1),3*(n+1),3*(n+1)]

/-- The concrete macro vertex scopes depend on r/t, not on the full dense n.
Balancing those public axes remains a separate numerical parameter bridge. -/
theorem arithmetic_arity_bound (n r t : ℕ) (i : Fin 5) :
    arithmeticArities n r t i≤(2*(r+t)+3)*(n+1) := by
  fin_cases i <;> simp [arithmeticArities] <;> nlinarith

end RiemannGaussian.SemiprimeMacroBitNetwork
