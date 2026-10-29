/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMacroGraph

/-!
# Literal local arithmetic tables for the actual ordered macro graph

Tables read actual finite Boolean port words. No global graph correctness or
counting premise is included in the public numerical configuration.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace RiemannGaussian.SemiprimeMacroGraphSemantics
open scoped BigOperators
open SemiprimeMacroFermatNetwork SemiprimeBooleanNetwork SemiprimeMacroBitNetwork
open SemiprimeMacroGraph
attribute [local instance] Classical.propDecidable

/-- Public arithmetic parameters, source widths and target digits only. -/
structure Config where
  /-- Dyadic root-four depth. -/
  depth : ℕ
  /-- First macro axis. -/
  r : ℕ
  /-- Second macro axis. -/
  t : ℕ
  /-- Number of active source digits. -/
  digits : ℕ
  /-- Radix logarithm. -/
  bits : ℕ
  /-- Actual transform shape. -/
  shape : r*t=macroLength depth
  /-- The physical quarter-radix rule. -/
  quarter : r*t=4*bits
  /-- Positive radix logarithm. -/
  bits_pos : 0<bits
  /-- At least one source digit and flag. -/
  digits_pos : 0<digits
  /-- Public digit capacity. -/
  digits_le : digits≤bits
  /-- Each active source's actual top-width cap. -/
  width : Fin digits→ℕ
  /-- Widths never exceed the radix logarithm. -/
  width_le : ∀ i,width i≤bits
  /-- Literal target digit data. -/
  target : ℕ→ℕ
  /-- Target digits are actual radix digits. -/
  target_lt : ∀ i,i<r*t → target i<2^bits
  /-- Actual inverse-DFT second-stage normalizer. -/
  normalizer : MacroRing depth
  /-- Its public unit equation. -/
  normalizer_spec : (macroLength depth : MacroRing depth)*normalizer=1

/-- Public capacity licenses source flags' actual input vertex indices. -/
theorem Config.cap (p : Config) : p.digits≤p.r*p.t := by
  have hq := p.quarter
  have hd := p.digits_le
  omega

/-- Decode the literal ordered little-endian Boolean word. -/
def readWord (width : ℕ) (bits : Fin width→Bool) : ℕ :=
  decode ((bitPortsEquiv width).symm bits)

/-- Word decoding agrees exactly with the original physical word. -/
theorem readWord_bits {width : ℕ} (word : BitVec width) :
    readWord width word.getLsb=decode word := by
  unfold readWord
  rw [show word.getLsb=(bitPortsEquiv width) word by rfl,Equiv.symm_apply_apply]

/-- Every physical word has its literal width bound before gate checks. -/
theorem readWord_bound (width : ℕ) (bits : Fin width→Bool) : readWord width bits<2^width :=
  ((bitPortsEquiv width).symm bits).isLt

/-- Exact source digit flag convention used by make_input. -/
def digitFlag (index value : ℕ) : Bool := if index=0 then decide (2≤value) else decide (value≠0)

/-- Root parameter at each actual forward/inverse transform. -/
def root (p : Config) : Transform→MacroRing p.depth
  | .inl _ => 4
  | .inr _ => inverseRoot p.depth

/-- The inverse normalizer is folded only into the second DFT stage. -/
def normalization (p : Config) : Transform→MacroRing p.depth
  | .inl _ => 1
  | .inr _ => p.normalizer

/-- Literal arithmetic/flag checks on the actual input-before-output port blocks. -/
def localTable (p : Config) : (v : Vertex p.r p.t p.digits)→(LocalSlot v→Bool)→Prop
  | .input _ i,x =>
      let word := readWord (p.r*p.t+1) (fun bit => x (.inl bit))
      if hi : i.val<p.digits then
        word<2^(p.width ⟨i.val,hi⟩) ∧
          ∀ j : {j : Fin p.digits // j.val=i.val},x (.inr j)=digitFlag i.val word
      else word=0
  | .first tr _,x =>
      let input := fun j : Fin p.t => readWord (p.r*p.t+1) (fun bit => x (.inl (j,bit)))
      let output := fun k : Fin p.t => readWord (p.r*p.t+1) (fun bit => x (.inr (k,bit)))
      (∀ j,input j<2^(p.r*p.t)+1) ∧ (∀ k,output k<2^(p.r*p.t)+1) ∧
        ∀ k,(output k : MacroRing p.depth)=
          ∑ j : Fin p.t,(input j : MacroRing p.depth)*(root p tr^p.r)^(j.val*k.val)
  | .scale tr j k,x =>
      let input := readWord (p.r*p.t+1) (fun bit => x (.inl bit))
      let output := readWord (p.r*p.t+1) (fun bit => x (.inr bit))
      input<2^(p.r*p.t)+1 ∧ output<2^(p.r*p.t)+1 ∧
        (output : MacroRing p.depth)=(input : MacroRing p.depth)*root p tr^(j.val*k.val)
  | .second tr _,x =>
      let input := fun j : Fin p.r => readWord (p.r*p.t+1) (fun bit => x (.inl (j,bit)))
      let output := fun k : Fin p.r => readWord (p.r*p.t+1) (fun bit => x (.inr (k,bit)))
      (∀ j,input j<2^(p.r*p.t)+1) ∧ (∀ k,output k<2^(p.r*p.t)+1) ∧
        ∀ k,(output k : MacroRing p.depth)=normalization p tr*
          ∑ j : Fin p.r,(input j : MacroRing p.depth)*(root p tr^p.t)^(j.val*k.val)
  | .product _,x =>
      let input := fun side : Fin 2 => readWord (p.r*p.t+1) (fun bit => x (.inl (side,bit)))
      let output := readWord (p.r*p.t+1) (fun bit => x (.inr bit))
      (∀ side,input side<2^(p.r*p.t)+1) ∧ output<2^(p.r*p.t)+1 ∧
        (output : MacroRing p.depth)=(input 0 : MacroRing p.depth)*(input 1 : MacroRing p.depth)
  | .carryInitial,x => readWord (p.r*p.t+1) x=0
  | .carry k,x =>
      let coefficient := readWord (p.r*p.t+1) (fun bit => x (.inl (0,bit)))
      let previous := readWord (p.r*p.t+1) (fun bit => x (.inl (1,bit)))
      let next := readWord (p.r*p.t+1) (fun bit => x (.inr bit))
      coefficient<2^(p.r*p.t)+1 ∧ previous<2^(p.r*p.t) ∧ next<2^(p.r*p.t) ∧
        coefficient+previous=p.target k.val+2^p.bits*next
  | .carryTerminal,x => readWord (p.r*p.t+1) x=0
  | .orGate _ _,x => x 2=(x 0 || x 1)
  | .inputCheck _,x => x 0=true

/-- Actual zero/one tensor table on the proved ordered Fin arity ports. -/
def table (p : Config) (v : Vertex p.r p.t p.digits) (input : Fin (arity v)→Bool) : Bool :=
  decide (localTable p v (fun slot => input ((localSlotFinEquiv v) slot)))

/-- Actual raw original signal assignment, read through its ordered local roles. -/
def originalLocal (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (v : Vertex p.r p.t p.digits) (slot : LocalSlot v) : Bool :=
  originalAssignment p.digits_pos assignment (unstructuredPort ⟨v,slot⟩)

/-- Conjunction of the literal original vertex predicates. -/
def OriginalAccepted (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool) : Prop :=
  ∀ v,localTable p v (originalLocal p assignment v)

/-- Every actual word signal decoded directly from its physical bit wires. -/
def wordNat (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (signal : WordSignal p.r p.t) : ℕ :=
  readWord (p.r*p.t+1) (fun bit => assignment (.inl (signal,bit)))

/-- Every actual flag signal is its single physical bit. -/
def flagValue (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (signal : SemiprimeMacroGraph.FlagSignal p.digits) : Bool := assignment (.inr signal)

/-- Shared original word-role decoding reads the actual signal identified
by the proved concrete graph, not a semantic equivalence premise. -/
theorem original_word_role (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (port : WordPort p.r p.t) :
    readWord (p.r*p.t+1) (fun bit => originalAssignment p.digits_pos assignment (.inl (port,bit)))=
      wordNat p assignment (portSignal port).1 := rfl

/-- Shared original flag-role decoding reads its actual wire. -/
theorem original_flag_role (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (port : FlagPort p.digits) :
    originalAssignment p.digits_pos assignment (.inr port)=
      flagValue p assignment (flagPortSignal p.digits_pos port).1 := rfl

/-- Exact ordered block pullback, with the same owner and local ordering. -/
theorem ordered_unstructured (p : Config) (v : Vertex p.r p.t p.digits) (slot : LocalSlot v) :
    (orderedPortEquiv p.r p.t p.digits p.cap).symm ⟨v,(localSlotFinEquiv v) slot⟩=
      unstructuredPort ⟨v,slot⟩ := by
  apply (orderedPortEquiv p.r p.t p.digits p.cap).injective
  rw [Equiv.apply_symm_apply]
  have h := (structuredPortEquiv p.r p.t p.digits p.cap).apply_symm_apply ⟨v,slot⟩
  exact (congrArg (fun q : (u : Vertex p.r p.t p.digits)×LocalSlot u =>
    (⟨q.1,(localSlotFinEquiv q.1) q.2⟩ : (u : Vertex p.r p.t p.digits)×Fin (arity u))) h).symm

/-- The literal ordered Boolean tables are exactly the original local checks. -/
theorem ordered_tables_iff (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool) :
    (∀ v,table p v (fun slot => originalAssignment p.digits_pos assignment
      ((orderedPortEquiv p.r p.t p.digits p.cap).symm ⟨v,slot⟩))=true) ↔
      OriginalAccepted p assignment := by
  simp only [table,decide_eq_true_eq,ordered_unstructured,OriginalAccepted]
  rfl

/-- Actual shared input word of each forward/inverse transform. -/
def inputSignal (p : Config) : Transform→Fin (p.r*p.t)→WordSignal p.r p.t
  | .inl side,k => .input side k
  | .inr _,k => .product k

/-- Actual flat final word of any transform. -/
def finalSignal (p : Config) (tr : Transform) (k : Fin (p.r*p.t)) : WordSignal p.r p.t :=
  let axes := (outputIndex p.r p.t).symm k
  .second tr axes.2 axes.1

/-- Literal source checks extracted from the actual local source vertex. -/
theorem source_checks (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (side : Fin 2) (i : Fin (p.r*p.t)) :
    if hi : i.val<p.digits then
      wordNat p assignment (.input side i)<2^(p.width ⟨i.val,hi⟩) ∧
        ∀ j : {j : Fin p.digits // j.val=i.val},
          flagValue p assignment (.digit side j.val)=digitFlag i.val (wordNat p assignment (.input side i))
    else wordNat p assignment (.input side i)=0 := h (.input side i)

/-- Both the canonical outputs and the actual first-DFT equation are obtained
from the literal table; no transform correctness premise is supplied. -/
theorem first_checks (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (tr : Transform) (j₁ : Fin p.r) :
    (∀ j₂ : Fin p.t,wordNat p assignment (inputSignal p tr (inputIndex p.r p.t (j₁,j₂)))<2^(p.r*p.t)+1) ∧
    (∀ k₂ : Fin p.t,wordNat p assignment (.first tr j₁ k₂)<2^(p.r*p.t)+1) ∧
    ∀ k₂ : Fin p.t,(wordNat p assignment (.first tr j₁ k₂) : MacroRing p.depth)=
      ∑ j₂ : Fin p.t,(wordNat p assignment (inputSignal p tr (inputIndex p.r p.t (j₁,j₂))) : MacroRing p.depth)*
        (root p tr^p.r)^(j₂.val*k₂.val) := by
  have hh := h (.first tr j₁)
  cases tr with
  | inl side => exact hh
  | inr u => cases u;exact hh

/-- Literal twiddle checks, including actual canonical output words. -/
theorem scale_checks (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (tr : Transform) (j : Fin p.r) (k : Fin p.t) :
    wordNat p assignment (.first tr j k)<2^(p.r*p.t)+1 ∧
    wordNat p assignment (.twiddle tr j k)<2^(p.r*p.t)+1 ∧
    (wordNat p assignment (.twiddle tr j k) : MacroRing p.depth)=
      (wordNat p assignment (.first tr j k) : MacroRing p.depth)*root p tr^(j.val*k.val) :=
  h (.scale tr j k)

/-- Literal second-stage equations retain the actual inverse normalization. -/
theorem second_checks (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (tr : Transform) (k₂ : Fin p.t) :
    (∀ j : Fin p.r,wordNat p assignment (.twiddle tr j k₂)<2^(p.r*p.t)+1) ∧
    (∀ k₁ : Fin p.r,wordNat p assignment (.second tr k₂ k₁)<2^(p.r*p.t)+1) ∧
    ∀ k₁ : Fin p.r,(wordNat p assignment (.second tr k₂ k₁) : MacroRing p.depth)=
      normalization p tr*∑ j : Fin p.r,(wordNat p assignment (.twiddle tr j k₂) : MacroRing p.depth)*
        (root p tr^p.t)^(j.val*k₁.val) := h (.second tr k₂)

/-- The actual point-product vertex connects the two forward final words. -/
theorem product_checks (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (k : Fin (p.r*p.t)) :
    (∀ side : Fin 2,wordNat p assignment (finalSignal p (.inl side) k)<2^(p.r*p.t)+1) ∧
    wordNat p assignment (.product k)<2^(p.r*p.t)+1 ∧
    (wordNat p assignment (.product k) : MacroRing p.depth)=
      (wordNat p assignment (finalSignal p (.inl 0) k) : MacroRing p.depth)*
      (wordNat p assignment (finalSignal p (.inl 1) k) : MacroRing p.depth) := h (.product k)

/-- Actual INTEGER carry table, including both strict n-bit value checks. -/
theorem carry_checks (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (k : Fin (p.r*p.t)) :
    wordNat p assignment (finalSignal p (.inr ()) k)<2^(p.r*p.t)+1 ∧
    wordNat p assignment (.carry ⟨k.val,by have := k.isLt;omega⟩)<2^(p.r*p.t) ∧
    wordNat p assignment (.carry ⟨k.val+1,by have := k.isLt;omega⟩)<2^(p.r*p.t) ∧
    wordNat p assignment (finalSignal p (.inr ()) k)+
      wordNat p assignment (.carry ⟨k.val,by have := k.isLt;omega⟩)=
      p.target k.val+2^p.bits*wordNat p assignment (.carry ⟨k.val+1,by have := k.isLt;omega⟩) := h (.carry k)

/-- Initial/terminal physical carry checks are exactly zero. -/
theorem carry_endpoints (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) :
    wordNat p assignment (.carry ⟨0,by omega⟩)=0 ∧
      wordNat p assignment (.carry ⟨p.r*p.t,by omega⟩)=0 := ⟨h .carryInitial,h .carryTerminal⟩

/-- Actual previous flag wire of an OR gate. -/
def previousFlag (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (side : Fin 2) (i : Fin (p.digits-1)) : Bool :=
  if hi : i.val=0 then flagValue p assignment (.digit side ⟨0,p.digits_pos⟩)
  else flagValue p assignment (.orOut side ⟨i.val-1,by have := i.isLt;omega⟩)

/-- The terminal one-check reads the sole digit or the last actual OR output. -/
def terminalFlag (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool) (side : Fin 2) : Bool :=
  if hd : p.digits=1 then flagValue p assignment (.digit side ⟨0,p.digits_pos⟩)
  else flagValue p assignment (.orOut side ⟨p.digits-2,by have := p.digits_pos;omega⟩)

/-- Actual OR gate checks extracted through the complete graph flag wiring. -/
theorem or_checks (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (side : Fin 2) (i : Fin (p.digits-1)) :
    flagValue p assignment (.orOut side i)=
      (previousFlag p assignment side i || flagValue p assignment (.digit side ⟨i.val+1,by have := i.isLt;omega⟩)) := by
  have hh := h (.orGate side i)
  by_cases hi : i.val=0 <;>
    simpa [localTable,originalLocal,unstructuredPort,originalAssignment,bitPortSignal,
      flagPortSignal,flagValue,previousFlag,hi] using hh

/-- Actual terminal flag checks extracted, including the d=1 boundary. -/
theorem terminal_checks (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (side : Fin 2) : terminalFlag p assignment side=true := by
  have hh := h (.inputCheck side)
  by_cases hd : p.digits=1 <;>
    simpa [localTable,originalLocal,unstructuredPort,originalAssignment,bitPortSignal,
      flagPortSignal,flagValue,terminalFlag,hd] using hh

/-- Every physical output in the complete accepted graph is canonical; this
is proved by its actual producing table, not assumed as an array invariant. -/
theorem all_words_canonical (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (signal : WordSignal p.r p.t) :
    wordNat p assignment signal<2^(p.r*p.t)+1 := by
  cases signal with
  | input side i =>
    have hs := source_checks p assignment h side i
    split_ifs at hs with hi
    · have he := p.width_le ⟨i.val,hi⟩
      have hb : p.bits≤p.r*p.t := by have := p.quarter;omega
      have hp := Nat.pow_le_pow_right (show (0 : ℕ)<2 by omega) (he.trans hb)
      exact lt_trans (lt_of_lt_of_le hs.1 hp) (by omega)
    · rw [hs];positivity
  | first tr j k => exact (first_checks p assignment h tr j).2.1 k
  | twiddle tr j k => exact (scale_checks p assignment h tr j k).2.1
  | second tr k j => exact (second_checks p assignment h tr k).2.1 j
  | product k => exact (product_checks p assignment h k).2.1
  | carry k =>
    by_cases hk : k.val=0
    · have he : k=⟨0,by omega⟩ := Fin.ext hk
      rw [he,(carry_endpoints p assignment h).1]
      positivity
    · let previous : Fin (p.r*p.t) := ⟨k.val-1,by have := k.isLt;omega⟩
      have hc := (carry_checks p assignment h previous).2.2.1
      have he : (⟨previous.val+1,by have := previous.isLt;omega⟩ : Fin (p.r*p.t+1))=k := by
        apply Fin.ext
        dsimp [previous]
        omega
      rw [he] at hc
      omega

/-- Exact value of the actual first-stage source axis permutation. -/
theorem inputIndex_value (r t : ℕ) (j₁ : Fin r) (j₂ : Fin t) :
    (inputIndex r t (j₁,j₂)).val=j₁.val+r*j₂.val := rfl

/-- The actual shared transform input array, zero outside its physical length. -/
def inputFunction (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (tr : Transform) (i : ℕ) : MacroRing p.depth :=
  if hi : i<p.r*p.t then (wordNat p assignment (inputSignal p tr ⟨i,hi⟩) : MacroRing p.depth) else 0

/-- Actual finite input slots are decoded without alteration. -/
theorem inputFunction_at (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (tr : Transform) (i : Fin (p.r*p.t)) :
    inputFunction p assignment tr i.val=(wordNat p assignment (inputSignal p tr i) : MacroRing p.depth) := by
  simp [inputFunction,i.isLt]

/-- Extract the actual three canonical arrays from shared physical wires.
The physical word values are used literally; the following theorem derives
all local stage equations from tables. -/
def extractedArrays (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (tr : Transform) : MacroArrays p.depth p.r p.t where
  first j k := residueWord p.depth (wordNat p assignment (.first tr j k))
  twiddle j k := residueWord p.depth (wordNat p assignment (.twiddle tr j k))
  second k j := residueWord p.depth (wordNat p assignment (.second tr k j))

/-- The extracted canonical words retain the actual physical values in the ring. -/
theorem extracted_final_value (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (tr : Transform) (k : Fin (p.r*p.t)) :
    residueValue (flatOutput (extractedArrays p assignment tr) k)=
      (wordNat p assignment (finalSignal p tr k) : MacroRing p.depth) := by
  exact residueValue_word p.depth _

/-- Actual accepted physical vertex tables imply all three canonical macro
stage relations. This instantiates MacroValid rather than postulating it. -/
theorem extracted_macro_valid (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (tr : Transform) :
    MacroValid p.depth p.r p.t (root p tr) (normalization p tr)
      (inputFunction p assignment tr) (extractedArrays p assignment tr) := by
  refine ⟨?_,?_,?_⟩
  · intro j₁ k₂
    change residueValue (residueWord p.depth (wordNat p assignment (.first tr j₁ k₂)))=_
    rw [residueValue_word,(first_checks p assignment h tr j₁).2.2 k₂]
    rw [←Fin.sum_univ_eq_sum_range (fun j₂ : ℕ =>
      inputFunction p assignment tr (j₁.val+p.r*j₂)*(root p tr^p.r)^(j₂*k₂.val)) p.t]
    apply Finset.sum_congr rfl
    intro j₂ hj₂
    rw [←inputIndex_value p.r p.t j₁ j₂,inputFunction_at]
  · intro j k
    change residueValue (residueWord p.depth (wordNat p assignment (.twiddle tr j k)))=
      residueValue (residueWord p.depth (wordNat p assignment (.first tr j k)))*_
    simp only [residueValue_word]
    exact (scale_checks p assignment h tr j k).2.2
  · intro k j
    change residueValue (residueWord p.depth (wordNat p assignment (.second tr k j)))=
      normalization p tr*∑ i : Fin p.r,
        residueValue (residueWord p.depth (wordNat p assignment (.twiddle tr i k)))*(root p tr^p.t)^(i.val*j.val)
    simp only [residueValue_word]
    exact (second_checks p assignment h tr k).2.2 j

/-- The actual root at every physical transform has the required full period. -/
theorem root_period (p : Config) (tr : Transform) : root p tr^(p.r*p.t)=1 := by
  rw [p.shape]
  cases tr with
  | inl side => exact root_four_period p.depth
  | inr u => exact inverseRoot_period p.depth

/-- Every actual final transform word is its literal normalized full Fourier value. -/
theorem actual_final_fourier (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (tr : Transform) (k : Fin (p.r*p.t)) :
    (wordNat p assignment (finalSignal p tr k) : MacroRing p.depth)=
      normalization p tr*fourier (root p tr) (p.r*p.t) (inputFunction p assignment tr) k.val := by
  rw [←extracted_final_value]
  exact flatOutput_value p.depth p.r p.t _ _ _ _
    (extracted_macro_valid p assignment h tr) (root_period p tr) k

/-- Actual physical inverse tables satisfy the normalized reflected equation
of the multiplication proof, with their actual point-product input wires. -/
theorem actual_inverse_fourier (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (k : Fin (p.r*p.t)) :
    (macroLength p.depth : MacroRing p.depth)*
      (wordNat p assignment (finalSignal p (.inr ()) k) : MacroRing p.depth)=
      fourier 4 (macroLength p.depth) (inputFunction p assignment (.inr ()))
        (if k.val=0 then 0 else macroLength p.depth-k.val) := by
  rw [←extracted_final_value]
  exact flatOutput_inverse p.depth p.r p.t p.normalizer _ _
    (extracted_macro_valid p assignment h (.inr ())) p.shape p.normalizer_spec k

/-- Actual source digit values, with zero padding beyond the physical array. -/
def sourceFunction (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (side : Fin 2) (i : ℕ) : ℕ :=
  if hi : i<p.r*p.t then wordNat p assignment (.input side ⟨i,hi⟩) else 0

/-- Source zero-padding is proved from the actual zero-source predicates. -/
theorem sourceFunction_zero (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (side : Fin 2) (i : ℕ) (hi : p.digits ≤ i) :
    sourceFunction p assignment side i=0 := by
  by_cases hn : i<p.r*p.t
  · have hs := source_checks p assignment h side ⟨i,hn⟩
    rw [dite_eq_right (by change ¬i<p.digits;omega)] at hs
    simpa [sourceFunction,hn] using hs
  · simp [sourceFunction,hn]

/-- Source tables supply the literal active radix bounds even at a shorter top digit. -/
theorem sourceFunction_bound (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (side : Fin 2) (i : ℕ) (hi : i<p.digits) :
    sourceFunction p assignment side i<2^p.bits := by
  have hn : i<p.r*p.t := lt_of_lt_of_le hi p.cap
  have hs := source_checks p assignment h side ⟨i,hn⟩
  rw [dite_eq_left hi] at hs
  have hb := Nat.pow_le_pow_right (show (0 : ℕ)<2 by omega) (p.width_le ⟨i,hi⟩)
  simpa [sourceFunction,hn] using lt_of_lt_of_le hs.1 hb

/-- Congruent actual input values on the finite clock give equal Fourier values. -/
theorem fourier_congr_range {R : Type*} [CommSemiring R] (w : R) (n k : ℕ)
    (a b : ℕ→R) (hab : ∀ i,i<n → a i=b i) : fourier w n a k=fourier w n b k := by
  unfold fourier
  apply Finset.sum_congr rfl
  intro i hi
  rw [hab i (Finset.mem_range.mp hi)]

/-- Literal zero source padding can be removed from the full finite Fourier sum. -/
theorem fourier_zero_padding {R : Type*} [CommSemiring R] (w : R) (n digits k : ℕ)
    (a : ℕ→R) (hsize : digits≤n) (hz : ∀ i, digits ≤ i → a i = 0) :
    fourier w n a k=fourier w digits a k := by
  unfold fourier
  have hn : n=digits+(n-digits) := by omega
  conv_lhs => rw [hn,Finset.sum_range_add]
  have he : (∑ i∈Finset.range (n-digits),a (digits+i)*w^((digits+i)*k))=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hz _ (by omega),zero_mul]
  rw [he,add_zero]

/-- The actual padded forward input is exactly the original source digit family. -/
theorem forward_input_eq (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (side : Fin 2) (i : ℕ) : inputFunction p assignment (.inl side) i=
      (sourceFunction p assignment side i : MacroRing p.depth) := by
  unfold inputFunction sourceFunction
  split_ifs <;> rfl

/-- Actual complete forward transforms evaluate precisely the unpadded source
polynomials, not a newly supplied or changed coefficient family. -/
theorem actual_forward_fourier (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (side : Fin 2) (k : Fin (p.r*p.t)) :
    (wordNat p assignment (finalSignal p (.inl side) k) : MacroRing p.depth)=
      fourier 4 p.digits (fun i => (sourceFunction p assignment side i : MacroRing p.depth)) k.val := by
  rw [actual_final_fourier p assignment h (.inl side) k]
  change 1*fourier 4 (p.r*p.t) (inputFunction p assignment (.inl side)) k.val=_
  rw [one_mul]
  have hf : inputFunction p assignment (.inl side)=fun i => (sourceFunction p assignment side i : MacroRing p.depth) :=
    funext (forward_input_eq p assignment side)
  rw [hf]
  exact fourier_zero_padding 4 _ _ _ _ p.cap (fun i hi => by rw [sourceFunction_zero p assignment h side i hi];rfl)

/-- Literal point-product gates therefore supply the actual Fourier product. -/
theorem actual_product_fourier (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (k : Fin (p.r*p.t)) :
    (wordNat p assignment (.product k) : MacroRing p.depth)=
      fourier 4 p.digits (fun i => (sourceFunction p assignment 0 i : MacroRing p.depth)) k.val*
      fourier 4 p.digits (fun i => (sourceFunction p assignment 1 i : MacroRing p.depth)) k.val := by
  rw [(product_checks p assignment h k).2.2,
    actual_forward_fourier p assignment h 0 k,actual_forward_fourier p assignment h 1 k]

/-- Literal final inverse coefficient array, extended by zero outside its ports. -/
def coefficientFunction (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool) (i : ℕ) : ℕ :=
  if hi : i<p.r*p.t then wordNat p assignment (finalSignal p (.inr ()) ⟨i,hi⟩) else 0

/-- Literal physical carry array, including both endpoints. -/
def carryFunction (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool) (i : ℕ) : ℕ :=
  if hi : i≤p.r*p.t then wordNat p assignment (.carry ⟨i,by omega⟩) else 0

/-- The entire actual ordered vertex conjunction instantiates the complete
arithmetic multiplication relation. No convolution, inverse or carry witness
correctness is a premise: every witness is the decoded actual wire array. -/
theorem actual_arithmetic_valid (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) :
    ArithmeticNetworkValid p.depth (sourceFunction p assignment 0) (sourceFunction p assignment 1)
      p.target (coefficientFunction p assignment) (carryFunction p assignment) p.digits (2^p.bits) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi
    have hn : i<p.r*p.t := by rw [p.shape];exact hi
    have hc := all_words_canonical p assignment h (finalSignal p (.inr ()) ⟨i,hn⟩)
    rw [show coefficientFunction p assignment i=wordNat p assignment (finalSignal p (.inr ()) ⟨i,hn⟩) by
      simp [coefficientFunction,hn]]
    simpa only [p.shape] using hc
  · intro i hi
    have hn : i<p.r*p.t := by rw [p.shape];exact hi
    have hx := actual_inverse_fourier p assignment h ⟨i,hn⟩
    rw [show coefficientFunction p assignment i=wordNat p assignment (finalSignal p (.inr ()) ⟨i,hn⟩) by
      simp [coefficientFunction,hn]]
    rw [hx]
    apply fourier_congr_range
    intro k hk
    have hkn : k<p.r*p.t := by rw [p.shape];exact hk
    rw [show inputFunction p assignment (.inr ()) k=
      (wordNat p assignment (.product ⟨k,hkn⟩) : MacroRing p.depth) by
        simpa only [inputSignal] using inputFunction_at p assignment (.inr ()) ⟨k,hkn⟩]
    exact actual_product_fourier p assignment h ⟨k,hkn⟩
  · simpa [carryFunction] using (carry_endpoints p assignment h).1
  · rw [←p.shape]
    simpa [carryFunction] using (carry_endpoints p assignment h).2
  · intro i hi
    have hn : i<p.r*p.t := by rw [p.shape];exact hi
    have hc := (carry_checks p assignment h ⟨i,hn⟩).2.2.2
    simpa [coefficientFunction,carryFunction,hn,show i≤p.r*p.t by omega,
      show i+1≤p.r*p.t by omega] using hc

/-- Literal source operands of the accepted graph, in actual integer arithmetic. -/
def sourceOperand (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool) (side : Fin 2) : ℕ :=
  ∑ i∈Finset.range p.digits,sourceFunction p assignment side i*(2^p.bits)^i

/-- The target integer is its public supplied digit evaluation. -/
def targetValue (p : Config) : ℕ :=
  ∑ i∈Finset.range (p.r*p.t),p.target i*(2^p.bits)^i

/-- Whole-graph multiplication soundness, derived from literal source, both
forward transforms, point products, actual inverse stages and INTEGER carries. -/
theorem accepted_integer_product (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) :
    sourceOperand p assignment 0*sourceOperand p assignment 1=targetValue p := by
  have hsize : 2*p.digits≤macroLength p.depth := by
    rw [←p.shape]
    have hd := p.digits_le
    have hq := p.quarter
    omega
  have hbound : p.digits*(2^p.bits)^2<2^(macroLength p.depth)+1 := by
    have hb := compiler_quarter_strict_bound p.digits p.bits (p.r*p.t) p.digits_le p.bits_pos p.quarter
    rw [p.shape] at hb
    omega
  have he := (arithmetic_network_iff p.depth (sourceFunction p assignment 0) (sourceFunction p assignment 1)
    p.target p.digits (2^p.bits) (by positivity) hsize
    (sourceFunction_bound p assignment h 0) (sourceFunction_bound p assignment h 1)
    (fun i hi => p.target_lt i (by rw [p.shape];exact hi)) hbound).mp
      ⟨coefficientFunction p assignment,carryFunction p assignment,actual_arithmetic_valid p assignment h⟩
  simpa only [sourceOperand,targetValue,p.shape] using he

/-- A true actual OR output traces back to an actual true digit flag. -/
theorem or_true_has_digit (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (side : Fin 2) (i : Fin (p.digits-1))
    (hi : flagValue p assignment (.orOut side i)=true) :
    ∃ j : Fin p.digits,flagValue p assignment (.digit side j)=true := by
  have hh : ∀ n : ℕ,∀ k : Fin (p.digits-1),k.val=n →
      flagValue p assignment (.orOut side k)=true →
        ∃ j : Fin p.digits,flagValue p assignment (.digit side j)=true := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k hk htrue
      rw [or_checks p assignment h side k] at htrue
      simp only [Bool.or_eq_true] at htrue
      rcases htrue with previous | current
      · by_cases hzero : k.val=0
        · exact ⟨⟨0,p.digits_pos⟩,by simpa [previousFlag,hzero] using previous⟩
        · have hlt : k.val-1<p.digits-1 := by have := k.isLt;omega
          have hp : flagValue p assignment (.orOut side ⟨k.val-1,hlt⟩)=true := by
            simpa [previousFlag,hzero] using previous
          exact ih (k.val-1) (by omega) ⟨k.val-1,hlt⟩ rfl hp
      · exact ⟨⟨k.val+1,by have := k.isLt;omega⟩,current⟩
  exact hh i.val i rfl hi

/-- Terminal one-checks and the literal OR chain guarantee a true source flag. -/
theorem true_digit_flag (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (side : Fin 2) :
    ∃ j : Fin p.digits,flagValue p assignment (.digit side j)=true := by
  have ht := terminal_checks p assignment h side
  unfold terminalFlag at ht
  split_ifs at ht with hd
  · exact ⟨⟨0,p.digits_pos⟩,ht⟩
  · exact or_true_has_digit p assignment h side ⟨p.digits-2,by have := p.digits_pos;omega⟩ ht

/-- Actual local source flags and OR checks force the original integer operand
at least two. No whole-operand flag oracle or guessed semantic equivalence. -/
theorem accepted_operand_nontrivial (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (side : Fin 2) : 2≤sourceOperand p assignment side := by
  obtain ⟨j,hflag⟩ := true_digit_flag p assignment h side
  have hj : j.val<p.r*p.t := lt_of_lt_of_le j.isLt p.cap
  have hs := source_checks p assignment h side ⟨j.val,hj⟩
  rw [dite_eq_left j.isLt] at hs
  have hf := hs.2 ⟨j,rfl⟩
  rw [hf] at hflag
  have hsource : sourceFunction p assignment side j.val=wordNat p assignment (.input side ⟨j.val,hj⟩) := by
    simp [sourceFunction,hj]
  have hterm : sourceFunction p assignment side j.val*(2^p.bits)^j.val≤sourceOperand p assignment side := by
    unfold sourceOperand
    exact Finset.single_le_sum (f:=fun i => sourceFunction p assignment side i*(2^p.bits)^i)
      (fun i hi => Nat.zero_le _) (Finset.mem_range.mpr j.isLt)
  rw [hsource] at hterm
  by_cases hj0 : j.val=0
  · have hv : 2≤wordNat p assignment (.input side ⟨j.val,hj⟩) := by
      simpa [digitFlag,hj0] using hflag
    have hpw : (2^p.bits)^j.val=1 := by rw [hj0,pow_zero]
    rw [hpw,Nat.mul_one] at hterm
    omega
  · have hv : wordNat p assignment (.input side ⟨j.val,hj⟩)≠0 := by
      simpa [digitFlag,hj0] using hflag
    have hb : 2≤(2 : ℕ)^p.bits := by
      calc
        2=(2 : ℕ)^1 := by norm_num
        _ ≤ 2^p.bits := Nat.pow_le_pow_right (by omega) p.bits_pos
    have hp : 2≤(2^p.bits)^j.val := by
      have he := Nat.pow_le_pow_right (show 0<(2 : ℕ)^p.bits by positivity) (show 1≤j.val by omega)
      have he' : 2^p.bits≤(2^p.bits)^j.val := by simpa only [pow_one] using he
      exact le_trans hb he'
    have hm := Nat.mul_le_mul (show 1≤wordNat p assignment (.input side ⟨j.val,hj⟩) by omega) hp
    omega

/-- Complete original-graph factor soundness from the literal local tables. -/
theorem accepted_factor_pair (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) :
    2≤sourceOperand p assignment 0 ∧ 2≤sourceOperand p assignment 1 ∧
      sourceOperand p assignment 0*sourceOperand p assignment 1=targetValue p :=
  ⟨accepted_operand_nontrivial p assignment h 0,accepted_operand_nontrivial p assignment h 1,
    accepted_integer_product p assignment h⟩

/-- Literal zero/one tables for every actual subdivided vertex, including the
two ordered equality ports rather than a supplied wire-equivalence premise. -/
def subdividedTable (p : Config) : (v : SubdividedVertex p.r p.t p.digits)→
    (Fin (subdividedArity v)→Bool)→Bool
  | .inl v,input => table p v input
  | .inr _,input => decide (input (0 : Fin 2)=input (1 : Fin 2))

/-- Actual complete ordered tensor acceptance after equality subdivision. -/
def SubdividedAccepted (p : Config) (assignment : Edge p.r p.t p.digits→Bool) : Prop :=
  ∀ v,subdividedTable p v (fun slot => assignment (orderedEdgeAt p.digits_pos p.cap ⟨v,slot⟩))=true

/-- The original ordered vertex reads the actual original host's half-edge. -/
theorem ordered_original_edge (p : Config) (v : Vertex p.r p.t p.digits) (slot : Fin (arity v)) :
    orderedEdgeAt p.digits_pos p.cap ⟨.inl v,slot⟩=
      bitPortSignal p.digits_pos ((orderedPortEquiv p.r p.t p.digits p.cap).symm ⟨v,slot⟩) := rfl

/-- Equality's zero port is exactly the producer-side half-edge. -/
theorem ordered_equality_zero (p : Config) (signal : BitSignal p.r p.t p.digits) :
    orderedEdgeAt p.digits_pos p.cap ⟨.inr signal,(0 : Fin 2)⟩=(signal,false) := rfl

/-- Equality's one port is exactly the consumer-side half-edge. -/
theorem ordered_equality_one (p : Config) (signal : BitSignal p.r p.t p.digits) :
    orderedEdgeAt p.digits_pos p.cap ⟨.inr signal,(1 : Fin 2)⟩=(signal,true) := rfl

/-- Actual equality tables glue all original local bits, with the exact
original vertex checks rather than an assumed global graph semantics. -/
theorem subdivided_tables_iff (p : Config) (assignment : Edge p.r p.t p.digits→Bool) :
    SubdividedAccepted p assignment ↔ equalitiesHold assignment ∧
      (∀ v,localTable p v (fun slot => subdividedAssignment p.digits_pos assignment
        (unstructuredPort ⟨v,slot⟩))) := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro signal
      have hh := h (.inr signal)
      change decide (assignment (orderedEdgeAt p.digits_pos p.cap ⟨.inr signal,(0 : Fin 2)⟩)=
        assignment (orderedEdgeAt p.digits_pos p.cap ⟨.inr signal,(1 : Fin 2)⟩))=true at hh
      rw [ordered_equality_zero,ordered_equality_one] at hh
      exact of_decide_eq_true hh
    · intro v
      have hh := h (.inl v)
      change table p v (fun slot => assignment (orderedEdgeAt p.digits_pos p.cap ⟨.inl v,slot⟩))=true at hh
      simp only [table,decide_eq_true_eq,ordered_original_edge,ordered_unstructured] at hh
      exact hh
  · rintro ⟨heq,h⟩ v
    cases v with
    | inl v =>
      change table p v (fun slot => assignment (orderedEdgeAt p.digits_pos p.cap ⟨.inl v,slot⟩))=true
      simp only [table,decide_eq_true_eq,ordered_original_edge,ordered_unstructured]
      exact h v
    | inr signal =>
      change decide (assignment (orderedEdgeAt p.digits_pos p.cap ⟨.inr signal,(0 : Fin 2)⟩)=
        assignment (orderedEdgeAt p.digits_pos p.cap ⟨.inr signal,(1 : Fin 2)⟩))=true
      rw [ordered_equality_zero,ordered_equality_one]
      exact decide_eq_true (heq signal)

/-- Equality-table acceptance recovers the original shared signal assignment. -/
theorem subdivided_original (p : Config) (assignment : Edge p.r p.t p.digits→Bool)
    (h : SubdividedAccepted p assignment) :
    OriginalAccepted p (fun signal => assignment (signal,false)) := by
  obtain ⟨heq,horiginal⟩ := (subdivided_tables_iff p assignment).mp h
  have ha (edge : Edge p.r p.t p.digits) : assignment edge=assignment (edge.1,false) := by
    rcases edge with ⟨signal,side⟩
    cases side
    · rfl
    · exact (heq signal).symm
  have hf : subdividedAssignment p.digits_pos assignment=
      originalAssignment p.digits_pos (fun signal => assignment (signal,false)) := by
    funext port
    exact ha (bitPortSignal p.digits_pos port)
  intro v
  change localTable p v (fun slot => originalAssignment p.digits_pos
    (fun signal => assignment (signal,false)) (unstructuredPort ⟨v,slot⟩))
  rw [←hf]
  exact horiginal v

/-- The complete actual subdivided ordered graph yields genuine nontrivial
integer factors, not just ring congruences or a projected normalization. -/
theorem subdivided_factor_pair (p : Config) (assignment : Edge p.r p.t p.digits→Bool)
    (h : SubdividedAccepted p assignment) :
    2≤sourceOperand p (fun signal => assignment (signal,false)) 0 ∧
    2≤sourceOperand p (fun signal => assignment (signal,false)) 1 ∧
      sourceOperand p (fun signal => assignment (signal,false)) 0*
        sourceOperand p (fun signal => assignment (signal,false)) 1=targetValue p :=
  accepted_factor_pair p _ (subdivided_original p assignment h)

/-- The actual equality tables preserve the count of the entire instantiated
original arithmetic graph. There is no arbitrary accepted-predicate premise. -/
theorem actual_subdivision_count (p : Config) :
    (∑ assignment : Edge p.r p.t p.digits→Bool,if SubdividedAccepted p assignment then (1 : ℕ) else 0)=
      ∑ assignment : BitSignal p.r p.t p.digits→Bool,if OriginalAccepted p assignment then 1 else 0 := by
  have hc := graph_subdivision_count p.digits_pos
    (fun input => ∀ v,localTable p v (fun slot => input (unstructuredPort ⟨v,slot⟩)))
  refine Eq.trans ?_ (Eq.trans hc ?_)
  · apply Finset.sum_congr rfl
    intro assignment ha
    by_cases h : SubdividedAccepted p assignment
    · have hh := (subdivided_tables_iff p assignment).mp h
      simp only [ite_eq_left h,ite_eq_left hh]
    · have hh : ¬(equalitiesHold assignment ∧ ∀ v,localTable p v
          (fun slot => subdividedAssignment p.digits_pos assignment (unstructuredPort ⟨v,slot⟩))) :=
        fun hh => h ((subdivided_tables_iff p assignment).mpr hh)
      simp only [ite_eq_right h,ite_eq_right hh]
  · apply Finset.sum_congr rfl
    intro assignment ha
    by_cases h : OriginalAccepted p assignment
    · have hh : ∀ v,localTable p v (fun slot => originalAssignment p.digits_pos assignment
          (unstructuredPort ⟨v,slot⟩)) := h
      simp only [ite_eq_left h,ite_eq_left hh]
    · have hh : ¬∀ v,localTable p v (fun slot => originalAssignment p.digits_pos assignment
          (unstructuredPort ⟨v,slot⟩)) := h
      simp only [ite_eq_right h,ite_eq_right hh]

end RiemannGaussian.SemiprimeMacroGraphSemantics
