/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMacroGraphSemantics
import RiemannGaussian.SemiprimeMacroFlagExtension
import RiemannGaussian.SemiprimeMacroGraphUnique

/-!
# Constructing the complete accepted macro-graph transcript

The forward, product and inverse arrays are evaluated through the actual
canonical macro stages. Integer carries are then derived from the supplied
true integer product, rather than assumed as graph witnesses.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace RiemannGaussian.SemiprimeMacroGraphExtension
open scoped BigOperators
open SemiprimeMacroFermatNetwork SemiprimeBooleanNetwork SemiprimeMacroBitNetwork
open SemiprimeMacroGraph SemiprimeMacroGraphSemantics SemiprimeMacroFlagExtension
attribute [local instance] Classical.propDecidable

/-- Actual active input digit arrays for both operands. -/
abbrev Inputs (p : Config) := Fin 2→Fin p.digits→BitVec p.bits

/-- Compute both actual forward transforms from original zero-padded digits. -/
def forwardArrays (p : Config) (input : Inputs p) (side : Fin 2) : MacroArrays p.depth p.r p.t :=
  buildMacro p.depth p.r p.t 4 1 (fun i => (values (input side) i : MacroRing p.depth))

/-- Literal canonical point-product word at each physical clock slot. -/
def productWord (p : Config) (input : Inputs p) (k : Fin (p.r*p.t)) : ResidueWord p.depth :=
  residueWord p.depth (residueValue (flatOutput (forwardArrays p input 0) k)*
    residueValue (flatOutput (forwardArrays p input 1) k))

/-- Actual point-product input function of the inverse transform. -/
def inverseInput (p : Config) (input : Inputs p) (i : ℕ) : MacroRing p.depth :=
  if hi : i<p.r*p.t then residueValue (productWord p input ⟨i,hi⟩) else 0

/-- Compute the actual normalized inverse transform from point-product words. -/
def inverseArrays (p : Config) (input : Inputs p) : MacroArrays p.depth p.r p.t :=
  buildMacro p.depth p.r p.t (inverseRoot p.depth) p.normalizer (inverseInput p input)

/-- All three explicitly computed macro transcripts. -/
def transcriptArrays (p : Config) (input : Inputs p) : Transform→MacroArrays p.depth p.r p.t
  | .inl side => forwardArrays p input side
  | .inr _ => inverseArrays p input

/-- Actual natural inverse coefficient values, zero beyond the physical array. -/
def coefficient (p : Config) (input : Inputs p) (i : ℕ) : ℕ :=
  if hi : i<p.r*p.t then decode (flatOutput (inverseArrays p input) ⟨i,hi⟩).val else 0

/-- Every computed forward word is the original unpadded digit polynomial value. -/
theorem forward_value (p : Config) (input : Inputs p) (side : Fin 2) (k : Fin (p.r*p.t)) :
    residueValue (flatOutput (forwardArrays p input side) k)=
      fourier 4 p.digits (fun i => (values (input side) i : MacroRing p.depth)) k.val := by
  unfold forwardArrays
  have hp : (4 : MacroRing p.depth)^(p.r*p.t)=1 := by rw [p.shape,root_four_period]
  rw [flatOutput_value p.depth p.r p.t 4 1 _ _ (buildMacro_valid _ _ _ _ _ _) hp k,one_mul]
  exact fourier_zero_padding 4 _ _ _ _ p.cap (fun i hi => by simp [values,Nat.not_lt.mpr hi])

/-- The literal product word is exactly the original Fourier point product. -/
theorem product_value (p : Config) (input : Inputs p) (k : Fin (p.r*p.t)) :
    residueValue (productWord p input k)=
      fourier 4 p.digits (fun i => (values (input 0) i : MacroRing p.depth)) k.val*
      fourier 4 p.digits (fun i => (values (input 1) i : MacroRing p.depth)) k.val := by
  rw [productWord,residueValue_word,forward_value,forward_value]

/-- The computed physical inverse words obey the exact normalized equation
for the original digit polynomial product. -/
theorem inverse_normalized (p : Config) (input : Inputs p) (k : Fin (p.r*p.t)) :
    (macroLength p.depth : MacroRing p.depth)*residueValue (flatOutput (inverseArrays p input) k)=
      fourier 4 (macroLength p.depth)
        (fun i => fourier 4 p.digits (fun j => (values (input 0) j : MacroRing p.depth)) i*
          fourier 4 p.digits (fun j => (values (input 1) j : MacroRing p.depth)) i)
        (if k.val=0 then 0 else macroLength p.depth-k.val) := by
  unfold inverseArrays
  rw [flatOutput_inverse p.depth p.r p.t p.normalizer _ _ (buildMacro_valid _ _ _ _ _ _)
    p.shape p.normalizer_spec k]
  apply fourier_congr_range
  intro i hi
  have hn : i<p.r*p.t := by rw [p.shape];exact hi
  simpa only [inverseInput,hn,dite_eq_left] using product_value p input ⟨i,hn⟩

/-- Canonical computed inverse coefficients are exactly the ordinary integer
convolution, proved through actual stages and no-wrap rather than assumed. -/
theorem coefficient_convolution (p : Config) (input : Inputs p) :
    ∀ i,i<p.r*p.t → coefficient p input i=convolution (values (input 0)) (values (input 1)) p.digits i := by
  have hsize : 2*p.digits≤macroLength p.depth := by
    rw [←p.shape]
    have := p.digits_le
    have := p.quarter
    omega
  have hbound : p.digits*(2^p.bits)^2<2^(macroLength p.depth)+1 := by
    have hb := compiler_quarter_strict_bound p.digits p.bits (p.r*p.t) p.digits_le p.bits_pos p.quarter
    rw [p.shape] at hb
    omega
  have hc : ∀ i,i<macroLength p.depth → coefficient p input i<2^(macroLength p.depth)+1 := by
    intro i hi
    have hn : i<p.r*p.t := by rw [p.shape];exact hi
    simpa only [coefficient,hn,dite_eq_left] using (flatOutput (inverseArrays p input) ⟨i,hn⟩).property
  have hinverse : ∀ i,i<macroLength p.depth →
      (macroLength p.depth : MacroRing p.depth)*(coefficient p input i : MacroRing p.depth)=
        fourier 4 (macroLength p.depth)
          (fun k => fourier 4 p.digits (fun j => (values (input 0) j : MacroRing p.depth)) k*
            fourier 4 p.digits (fun j => (values (input 1) j : MacroRing p.depth)) k)
          (if i=0 then 0 else macroLength p.depth-i) := by
    intro i hi
    have hn : i<p.r*p.t := by rw [p.shape];exact hi
    simpa only [coefficient,hn,dite_eq_left,residueValue] using inverse_normalized p input ⟨i,hn⟩
  intro i hi
  exact canonical_inverse_convolution p.depth (values (input 0)) (values (input 1))
    (coefficient p input) p.digits (2^p.bits) hsize (values_bound _) (values_bound _)
    hbound hc hinverse i (by rw [←p.shape];exact hi)

/-- A true original integer product supplies actual bounded INTEGER carries
for the explicitly computed inverse words. -/
theorem computed_carries_exist (p : Config) (input : Inputs p)
    (hproduct : operand (input 0)*operand (input 1)=targetValue p) :
    ∃ carry : ℕ→ℕ,carry 0=0 ∧ carry (p.r*p.t)=0 ∧
      (∀ i,i<p.r*p.t → coefficient p input i+carry i=p.target i+2^p.bits*carry (i+1)) ∧
      (∀ i,i≤p.r*p.t → carry i<2^(p.r*p.t)) := by
  have hsize : 2*p.digits≤p.r*p.t := by have := p.digits_le;have := p.quarter;omega
  have heval : (∑ i∈Finset.range (p.r*p.t),coefficient p input i*(2^p.bits)^i)+0=
      ∑ i∈Finset.range (p.r*p.t),p.target i*(2^p.bits)^i := by
    rw [Nat.add_zero]
    calc
      _ = ∑ i∈Finset.range (p.r*p.t),convolution (values (input 0)) (values (input 1)) p.digits i*(2^p.bits)^i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [coefficient_convolution p input i (Finset.mem_range.mp hi)]
      _ = operand (input 0)*operand (input 1) := convolution_evaluation _ _ _ _ hsize _
      _ = _ := hproduct
  obtain ⟨carry,hzero,hend,hcarry⟩ := integer_carries_exist (coefficient p input) p.target (2^p.bits)
    (p.r*p.t) 0 (by positivity) p.target_lt heval
  refine ⟨carry,hzero,hend,hcarry,?_⟩
  exact compiler_carry_capacity (coefficient p input) p.target carry p.digits p.bits (p.r*p.t)
    p.digits_le p.bits_pos p.quarter hzero
    (fun i hi => by rw [coefficient_convolution p input i hi];exact convolution_bound _ _ _ _ _ (values_bound _) (values_bound _))
    hcarry

/-- Actual shared input function for the evaluated transcript. -/
def transcriptInput (p : Config) (input : Inputs p) : Transform→ℕ→MacroRing p.depth
  | .inl side => fun i => (values (input side) i : MacroRing p.depth)
  | .inr _ => inverseInput p input

/-- All evaluated transcript arrays satisfy their literal macro equations. -/
theorem transcript_valid (p : Config) (input : Inputs p) (tr : Transform) :
    MacroValid p.depth p.r p.t (root p tr) (normalization p tr)
      (transcriptInput p input tr) (transcriptArrays p input tr) := by
  cases tr with
  | inl side => exact buildMacro_valid _ _ _ _ _ _
  | inr u => exact buildMacro_valid _ _ _ _ _ _

/-- All actual natural word signals, with derived integer carries as data. -/
def wordValue (p : Config) (input : Inputs p) (carry : ℕ→ℕ) : WordSignal p.r p.t→ℕ
  | .input side i => values (input side) i.val
  | .first tr j k => decode ((transcriptArrays p input tr).first j k).val
  | .twiddle tr j k => decode ((transcriptArrays p input tr).twiddle j k).val
  | .second tr k j => decode ((transcriptArrays p input tr).second k j).val
  | .product k => decode (productWord p input k).val
  | .carry k => carry k.val

/-- The final flat word is the same word in the actual tagged transcript. -/
theorem wordValue_final (p : Config) (input : Inputs p) (carry : ℕ→ℕ)
    (tr : Transform) (k : Fin (p.r*p.t)) :
    wordValue p input carry (finalSignal p tr k)=decode (flatOutput (transcriptArrays p input tr) k).val := rfl

/-- Canonicality of every evaluated physical word, including source padding
and the strictly bounded physical carries, follows from actual construction. -/
theorem wordValue_canonical (p : Config) (input : Inputs p) (carry : ℕ→ℕ)
    (hcarry : ∀ i,i≤p.r*p.t → carry i<2^(p.r*p.t)) (signal : WordSignal p.r p.t) :
    wordValue p input carry signal<2^(p.r*p.t)+1 := by
  cases signal with
  | input side i =>
    have hb : values (input side) i.val<2^p.bits := by
      by_cases hi : i.val<p.digits
      · exact values_bound _ _ hi
      · simp [values,hi]
    have hs : p.bits≤p.r*p.t := by have := p.quarter;omega
    have hp := Nat.pow_le_pow_right (show (0 : ℕ)<2 by omega) hs
    exact lt_trans (lt_of_lt_of_le hb hp) (by omega)
  | first tr j k => simpa only [wordValue,p.shape] using ((transcriptArrays p input tr).first j k).property
  | twiddle tr j k => simpa only [wordValue,p.shape] using ((transcriptArrays p input tr).twiddle j k).property
  | second tr k j => simpa only [wordValue,p.shape] using ((transcriptArrays p input tr).second k j).property
  | product k => simpa only [wordValue,p.shape] using (productWord p input k).property
  | carry k =>
    have hc := hcarry k.val (by have := k.isLt;omega)
    exact lt_trans hc (by omega)

/-- Every evaluated physical value fits its actual `(n+1)`-bit wire word. -/
theorem wordValue_width (p : Config) (input : Inputs p) (carry : ℕ→ℕ)
    (hcarry : ∀ i,i≤p.r*p.t → carry i<2^(p.r*p.t)) (signal : WordSignal p.r p.t) :
    wordValue p input carry signal<2^(p.r*p.t+1) := by
  have hc := wordValue_canonical p input carry hcarry signal
  have hp : 0<(2 : ℕ)^(p.r*p.t) := by positivity
  rw [pow_succ]
  omega

/-- Construct all actual word bits and the unique canonical digit/OR flag bits. -/
def buildAssignment (p : Config) (input : Inputs p) (carry : ℕ→ℕ) : BitSignal p.r p.t p.digits→Bool
  | .inl (signal,bit) => (encode (p.r*p.t+1) (wordValue p input carry signal)).getLsb bit
  | .inr signal => buildFlags p.digits_pos (fun side => inputFlag (input side)) signal

/-- Every constructed physical word decodes to its actual evaluated value. -/
theorem built_word (p : Config) (input : Inputs p) (carry : ℕ→ℕ)
    (hcarry : ∀ i,i≤p.r*p.t → carry i<2^(p.r*p.t)) (signal : WordSignal p.r p.t) :
    wordNat p (buildAssignment p input carry) signal=wordValue p input carry signal := by
  change readWord (p.r*p.t+1) (encode (p.r*p.t+1) (wordValue p input carry signal)).getLsb=_
  rw [readWord_bits,decode_encode (wordValue_width p input carry hcarry signal)]

/-- Every constructed flag is the actual canonical OR-prefix construction. -/
theorem built_flag (p : Config) (input : Inputs p) (carry : ℕ→ℕ)
    (signal : SemiprimeMacroGraph.FlagSignal p.digits) :
    flagValue p (buildAssignment p input carry) signal=
      buildFlags p.digits_pos (fun side => inputFlag (input side)) signal := rfl

/-- Actual first-stage input word values agree with the evaluated shared input. -/
theorem wordValue_input (p : Config) (input : Inputs p) (carry : ℕ→ℕ)
    (tr : Transform) (k : Fin (p.r*p.t)) :
    (wordValue p input carry (inputSignal p tr k) : MacroRing p.depth)=transcriptInput p input tr k.val := by
  cases tr with
  | inl side => rfl
  | inr u => cases u;simp [inputSignal,wordValue,transcriptInput,inverseInput,k.isLt,residueValue]

/-- Actual evaluated first-stage equations, including the source permutation. -/
theorem wordValue_first (p : Config) (input : Inputs p) (carry : ℕ→ℕ)
    (tr : Transform) (j₁ : Fin p.r) (k₂ : Fin p.t) :
    (wordValue p input carry (.first tr j₁ k₂) : MacroRing p.depth)=
      ∑ j₂ : Fin p.t,(wordValue p input carry (inputSignal p tr (inputIndex p.r p.t (j₁,j₂))) : MacroRing p.depth)*
        (root p tr^p.r)^(j₂.val*k₂.val) := by
  change residueValue ((transcriptArrays p input tr).first j₁ k₂)=_
  rw [(transcript_valid p input tr).1 j₁ k₂]
  rw [←Fin.sum_univ_eq_sum_range (fun j₂ : ℕ =>
    transcriptInput p input tr (j₁.val+p.r*j₂)*(root p tr^p.r)^(j₂*k₂.val)) p.t]
  apply Finset.sum_congr rfl
  intro j₂ hj₂
  rw [←inputIndex_value p.r p.t j₁ j₂,←wordValue_input p input carry tr]

/-- Actual evaluated twiddle equations. -/
theorem wordValue_scale (p : Config) (input : Inputs p) (carry : ℕ→ℕ)
    (tr : Transform) (j : Fin p.r) (k : Fin p.t) :
    (wordValue p input carry (.twiddle tr j k) : MacroRing p.depth)=
      (wordValue p input carry (.first tr j k) : MacroRing p.depth)*root p tr^(j.val*k.val) :=
  (transcript_valid p input tr).2.1 j k

/-- Actual evaluated second-stage equations retain inverse normalization. -/
theorem wordValue_second (p : Config) (input : Inputs p) (carry : ℕ→ℕ)
    (tr : Transform) (k : Fin p.t) (j : Fin p.r) :
    (wordValue p input carry (.second tr k j) : MacroRing p.depth)=
      normalization p tr*∑ i : Fin p.r,(wordValue p input carry (.twiddle tr i k) : MacroRing p.depth)*
        (root p tr^p.t)^(i.val*j.val) := (transcript_valid p input tr).2.2 k j

/-- Actual evaluated canonical product equations. -/
theorem wordValue_product (p : Config) (input : Inputs p) (carry : ℕ→ℕ)
    (k : Fin (p.r*p.t)) :
    (wordValue p input carry (.product k) : MacroRing p.depth)=
      (wordValue p input carry (finalSignal p (.inl 0) k) : MacroRing p.depth)*
      (wordValue p input carry (finalSignal p (.inl 1) k) : MacroRing p.depth) := by
  rw [wordValue_final,wordValue_final]
  exact residueValue_word p.depth _

/-- The computed transcript instantiates every literal original vertex table.
All hypotheses concern original input width/product and derived carry data,
never desired graph acceptance. -/
theorem buildAssignment_accepted (p : Config) (input : Inputs p) (carry : ℕ→ℕ)
    (hwidth : ∀ side i,decode (input side i)<2^(p.width i))
    (hnontrivial : ∀ side,2≤operand (input side))
    (hzero : carry 0=0) (hend : carry (p.r*p.t)=0)
    (hsteps : ∀ i,i<p.r*p.t → coefficient p input i+carry i=p.target i+2^p.bits*carry (i+1))
    (hcarry : ∀ i,i≤p.r*p.t → carry i<2^(p.r*p.t)) :
    OriginalAccepted p (buildAssignment p input carry) := by
  let assignment := buildAssignment p input carry
  have hb : ∀ signal : WordSignal p.r p.t,wordNat p assignment signal=wordValue p input carry signal :=
    built_word p input carry hcarry
  have hc := wordValue_canonical p input carry hcarry
  intro vertex
  cases vertex with
  | input side i =>
    change (if hi : i.val<p.digits then
      wordNat p assignment (.input side i)<2^(p.width ⟨i.val,hi⟩) ∧
        ∀ j : {j : Fin p.digits // j.val=i.val},
          flagValue p assignment (.digit side j.val)=digitFlag i.val (wordNat p assignment (.input side i))
      else wordNat p assignment (.input side i)=0)
    rw [hb]
    split_ifs with hi
    · refine ⟨?_,?_⟩
      · simpa [wordValue,values,hi] using hwidth side ⟨i.val,hi⟩
      · intro j
        rw [built_flag,buildFlags_digit]
        have hj : j.val=⟨i.val,hi⟩ := Fin.ext j.property
        rw [hj]
        simp only [inputFlag,digitFlag,wordValue,values,hi,dite_eq_left]
    · simp [wordValue,values,hi]
  | first tr j₁ =>
    have ht :
        (∀ j₂ : Fin p.t,wordNat p assignment (inputSignal p tr (inputIndex p.r p.t (j₁,j₂)))<2^(p.r*p.t)+1) ∧
        (∀ k₂ : Fin p.t,wordNat p assignment (.first tr j₁ k₂)<2^(p.r*p.t)+1) ∧
        ∀ k₂ : Fin p.t,(wordNat p assignment (.first tr j₁ k₂) : MacroRing p.depth)=
          ∑ j₂ : Fin p.t,(wordNat p assignment (inputSignal p tr (inputIndex p.r p.t (j₁,j₂))) : MacroRing p.depth)*
            (root p tr^p.r)^(j₂.val*k₂.val) := by
      simp_rw [hb]
      exact ⟨fun j₂ => hc _,fun k₂ => hc _,fun k₂ => wordValue_first p input carry tr j₁ k₂⟩
    cases tr with
    | inl side => exact ht
    | inr u => cases u;exact ht
  | scale tr j k =>
    have ht : wordNat p assignment (.first tr j k)<2^(p.r*p.t)+1 ∧
        wordNat p assignment (.twiddle tr j k)<2^(p.r*p.t)+1 ∧
        (wordNat p assignment (.twiddle tr j k) : MacroRing p.depth)=
          (wordNat p assignment (.first tr j k) : MacroRing p.depth)*root p tr^(j.val*k.val) := by
      simp_rw [hb]
      exact ⟨hc _,hc _,wordValue_scale p input carry tr j k⟩
    exact ht
  | second tr k₂ =>
    have ht : (∀ j : Fin p.r,wordNat p assignment (.twiddle tr j k₂)<2^(p.r*p.t)+1) ∧
        (∀ k₁ : Fin p.r,wordNat p assignment (.second tr k₂ k₁)<2^(p.r*p.t)+1) ∧
        ∀ k₁ : Fin p.r,(wordNat p assignment (.second tr k₂ k₁) : MacroRing p.depth)=
          normalization p tr*∑ j : Fin p.r,(wordNat p assignment (.twiddle tr j k₂) : MacroRing p.depth)*
            (root p tr^p.t)^(j.val*k₁.val) := by
      simp_rw [hb]
      exact ⟨fun j => hc _,fun j => hc _,fun j => wordValue_second p input carry tr k₂ j⟩
    exact ht
  | product k =>
    have ht : (∀ side : Fin 2,wordNat p assignment (finalSignal p (.inl side) k)<2^(p.r*p.t)+1) ∧
        wordNat p assignment (.product k)<2^(p.r*p.t)+1 ∧
        (wordNat p assignment (.product k) : MacroRing p.depth)=
          (wordNat p assignment (finalSignal p (.inl 0) k) : MacroRing p.depth)*
          (wordNat p assignment (finalSignal p (.inl 1) k) : MacroRing p.depth) := by
      simp_rw [hb]
      exact ⟨fun side => hc _,hc _,wordValue_product p input carry k⟩
    exact ht
  | carryInitial =>
    change wordNat p assignment (.carry ⟨0,by omega⟩)=0
    rw [hb]
    exact hzero
  | carry k =>
    have ht : wordNat p assignment (finalSignal p (.inr ()) k)<2^(p.r*p.t)+1 ∧
        wordNat p assignment (.carry ⟨k.val,by have := k.isLt;omega⟩)<2^(p.r*p.t) ∧
        wordNat p assignment (.carry ⟨k.val+1,by have := k.isLt;omega⟩)<2^(p.r*p.t) ∧
        wordNat p assignment (finalSignal p (.inr ()) k)+
          wordNat p assignment (.carry ⟨k.val,by have := k.isLt;omega⟩)=
          p.target k.val+2^p.bits*wordNat p assignment (.carry ⟨k.val+1,by have := k.isLt;omega⟩) := by
      simp_rw [hb]
      refine ⟨hc _,hcarry k.val (by have := k.isLt;omega),hcarry (k.val+1) (by have := k.isLt;omega),?_⟩
      rw [wordValue_final]
      have he : coefficient p input k.val=decode (flatOutput (inverseArrays p input) k).val := by
        simp [coefficient,k.isLt]
      simpa only [wordValue,transcriptArrays] using (he ▸ hsteps k.val k.isLt)
    exact ht
  | carryTerminal =>
    change wordNat p assignment (.carry ⟨p.r*p.t,by omega⟩)=0
    rw [hb]
    exact hend
  | orGate side i =>
    have hh := buildFlags_or p.digits_pos (fun side => inputFlag (input side)) side i
    by_cases hi : i.val=0 <;>
      simpa [localTable,originalLocal,unstructuredPort,originalAssignment,bitPortSignal,
        flagPortSignal,buildAssignment,SemiprimeMacroFlagExtension.previous,hi] using hh
  | inputCheck side =>
    have hh := (terminal_inputFlag_iff p.digits_pos input p.bits_pos side).mpr (hnontrivial side)
    by_cases hd : p.digits=1 <;>
      simpa [localTable,originalLocal,unstructuredPort,originalAssignment,bitPortSignal,
        flagPortSignal,buildAssignment,SemiprimeMacroFlagExtension.terminal,hd] using hh

/-- Every true nontrivial pair of original source integers, respecting its
actual active digit widths, has a complete accepted physical bit assignment. -/
theorem accepted_extension_exists (p : Config) (input : Inputs p)
    (hwidth : ∀ side i,decode (input side i)<2^(p.width i))
    (hnontrivial : ∀ side,2≤operand (input side))
    (hproduct : operand (input 0)*operand (input 1)=targetValue p) :
    ∃ assignment : BitSignal p.r p.t p.digits→Bool,
      OriginalAccepted p assignment ∧
      ∀ side (i : Fin p.digits),wordNat p assignment
        (.input side ⟨i.val,lt_of_lt_of_le i.isLt p.cap⟩)=decode (input side i) := by
  obtain ⟨carry,hzero,hend,hsteps,hcarry⟩ := computed_carries_exist p input hproduct
  refine ⟨buildAssignment p input carry,buildAssignment_accepted p input carry hwidth hnontrivial
    hzero hend hsteps hcarry,?_⟩
  intro side i
  rw [built_word p input carry hcarry]
  exact values_at (input side) i

/-- Read the actual original source digits as their exact b-bit input words. -/
def extractedInput (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool) : Inputs p :=
  fun side i => encode p.bits (wordNat p assignment (.input side ⟨i.val,lt_of_lt_of_le i.isLt p.cap⟩))

/-- Accepted source tables prove no truncation occurs during input extraction. -/
theorem extractedInput_value (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (side : Fin 2) (i : Fin p.digits) :
    decode (extractedInput p assignment side i)=
      wordNat p assignment (.input side ⟨i.val,lt_of_lt_of_le i.isLt p.cap⟩) := by
  have hn := lt_of_lt_of_le i.isLt p.cap
  have hb := sourceFunction_bound p assignment h side i.val i.isLt
  have hh : wordNat p assignment (.input side ⟨i.val,hn⟩)<2^p.bits := by
    simpa only [sourceFunction,hn,dite_eq_left] using hb
  exact decode_encode hh

/-- Extracted inputs preserve their actual shorter active top-width cap. -/
theorem extractedInput_width (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (side : Fin 2) (i : Fin p.digits) :
    decode (extractedInput p assignment side i)<2^(p.width i) := by
  rw [extractedInput_value p assignment h side i]
  have hs := source_checks p assignment h side ⟨i.val,lt_of_lt_of_le i.isLt p.cap⟩
  rw [dite_eq_left i.isLt] at hs
  exact hs.1

/-- Input extraction preserves the exact original integer operand. -/
theorem extractedInput_operand (p : Config) (assignment : BitSignal p.r p.t p.digits→Bool)
    (h : OriginalAccepted p assignment) (side : Fin 2) :
    operand (extractedInput p assignment side)=sourceOperand p assignment side := by
  unfold operand sourceOperand
  apply Finset.sum_congr rfl
  intro i hi
  have hd := Finset.mem_range.mp hi
  have hn := lt_of_lt_of_le hd p.cap
  have he : values (extractedInput p assignment side) i=
      wordNat p assignment (.input side ⟨i,hn⟩) := by
    exact (values_at (extractedInput p assignment side) ⟨i,hd⟩).trans
      (extractedInput_value p assignment h side ⟨i,hd⟩)
  rw [he]
  simp only [sourceFunction,hn,dite_eq_left]

/-- Exact original-input predicate: literal digit widths, nontrivial integers,
and their true product. No graph acceptance appears in this predicate. -/
def InputValid (p : Config) (input : Inputs p) : Prop :=
  (∀ side i,decode (input side i)<2^(p.width i)) ∧
  (∀ side,2≤operand (input side)) ∧ operand (input 0)*operand (input 1)=targetValue p

/-- The finite set of actual accepted original signal assignments. -/
abbrev Accepted (p : Config) := {assignment : BitSignal p.r p.t p.digits→Bool // OriginalAccepted p assignment}

/-- The finite set of literal original input pairs with true nontrivial product. -/
abbrev AdmissibleInputs (p : Config) := {input : Inputs p // InputValid p input}

/-- Read accepted actual graph wires into their valid original input pair. -/
def acceptedInput (p : Config) (assignment : Accepted p) : AdmissibleInputs p :=
  ⟨extractedInput p assignment.val,by
    refine ⟨extractedInput_width p assignment.val assignment.property,?_,?_⟩
    · intro side
      rw [extractedInput_operand p assignment.val assignment.property]
      exact accepted_operand_nontrivial p assignment.val assignment.property side
    · rw [extractedInput_operand p assignment.val assignment.property,
        extractedInput_operand p assignment.val assignment.property]
      exact accepted_integer_product p assignment.val assignment.property⟩

/-- The actual input projection is injective by proved canonical-stage,
carry, flag and physical-bit uniqueness; no unique-extension promise is assumed. -/
theorem acceptedInput_injective (p : Config) : Function.Injective (acceptedInput p) := by
  intro a b he
  apply Subtype.ext
  apply SemiprimeMacroGraphUnique.accepted_unique p a.val b.val a.property b.property
  intro side i
  have hv := congrArg (fun input : Inputs p => decode (input side i)) (congrArg Subtype.val he)
  change decode (extractedInput p a.val side i)=decode (extractedInput p b.val side i) at hv
  rw [extractedInput_value p a.val a.property,extractedInput_value p b.val b.property] at hv
  exact hv

/-- Every original input pair satisfying only width/nontrivial/product data
has an actual accepted graph assignment reading back to that pair. -/
theorem acceptedInput_surjective (p : Config) : Function.Surjective (acceptedInput p) := by
  intro input
  obtain ⟨assignment,ha,hpreserve⟩ := accepted_extension_exists p input.val
    input.property.1 input.property.2.1 input.property.2.2
  refine ⟨⟨assignment,ha⟩,Subtype.ext ?_⟩
  change extractedInput p assignment=input.val
  funext side i
  apply BitVec.eq_of_toNat_eq
  change decode (extractedInput p assignment side i)=decode (input.val side i)
  rw [extractedInput_value p assignment ha,hpreserve side i]

/-- Complete actual graph semantics: accepted physical bit assignments are
in bijection with the true original factor inputs, including finite top widths. -/
def acceptedInputEquiv (p : Config) : Accepted p ≃ AdmissibleInputs p :=
  Equiv.ofBijective (acceptedInput p) ⟨acceptedInput_injective p,acceptedInput_surjective p⟩

/-- Exact accepted original graph cardinal equals the original factor-input
cardinal, with no graph-correctness or count premise. -/
theorem accepted_card (p : Config) : Fintype.card (Accepted p)=Fintype.card (AdmissibleInputs p) :=
  Fintype.card_congr (acceptedInputEquiv p)

/-- Literal zero/one summation is the exact accepted finite cardinal. -/
theorem indicator_card {X : Type*} [Fintype X] (P : X→Prop) [Fintype {x // P x}] :
    (∑ x : X,if P x then (1 : ℕ) else 0)=Fintype.card {x // P x} := by
  rw [Fintype.card_subtype]
  exact Finset.sum_boole P Finset.univ

/-- The complete actual original graph count equals its true admissible
nontrivial factor-input count, with every internal bit extension paid by proof. -/
theorem original_count_eq_inputs (p : Config) :
    (∑ assignment : BitSignal p.r p.t p.digits→Bool,if OriginalAccepted p assignment then (1 : ℕ) else 0)=
      ∑ input : Inputs p,if InputValid p input then 1 else 0 := by
  rw [indicator_card (OriginalAccepted p),indicator_card (InputValid p)]
  exact accepted_card p

/-- The complete actual subdivided ordered graph has that same factor-input
count; actual equality tables, not a global equivalence promise, enforce gluing. -/
theorem subdivided_count_eq_inputs (p : Config) :
    (∑ assignment : Edge p.r p.t p.digits→Bool,if SubdividedAccepted p assignment then (1 : ℕ) else 0)=
      ∑ input : Inputs p,if InputValid p input then 1 else 0 := by
  rw [actual_subdivision_count,original_count_eq_inputs]

/-- Products of literal Boolean tensor entries implement their whole local conjunction. -/
theorem boolean_product_indicator {E : Type*} [Fintype E] (entry : E→Bool) :
    (∏ e : E,if entry e then (1 : ℕ) else 0)=if ∀ e,entry e=true then 1 else 0 := by
  classical
  by_cases h : ∀ e,entry e=true
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro e he
    rw [h e]
    rfl
  · rw [ite_eq_right h]
    obtain ⟨e,he⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    have hh : entry e=false := by cases hx : entry e <;> simp_all
    rw [hh]
    rfl

/-- Literal local 0/1 tensor contraction of the full actual ordered graph,
not merely a global accepted-predicate count, equals the original factor inputs. -/
theorem actual_tensor_contraction (p : Config) :
    (∑ assignment : Edge p.r p.t p.digits→Bool,
      ∏ v : SubdividedVertex p.r p.t p.digits,
        if subdividedTable p v (fun slot => assignment (orderedEdgeAt p.digits_pos p.cap ⟨v,slot⟩)) then (1 : ℕ) else 0)=
      ∑ input : Inputs p,if InputValid p input then 1 else 0 := by
  have he (assignment : Edge p.r p.t p.digits→Bool) :
      (∏ v : SubdividedVertex p.r p.t p.digits,
        if subdividedTable p v (fun slot => assignment (orderedEdgeAt p.digits_pos p.cap ⟨v,slot⟩)) then (1 : ℕ) else 0)=
        if SubdividedAccepted p assignment then 1 else 0 := by
    have hh := boolean_product_indicator (fun v : SubdividedVertex p.r p.t p.digits =>
      subdividedTable p v (fun slot => assignment (orderedEdgeAt p.digits_pos p.cap ⟨v,slot⟩)))
    by_cases h : SubdividedAccepted p assignment
    · have hv : ∀ v,subdividedTable p v
          (fun slot => assignment (orderedEdgeAt p.digits_pos p.cap ⟨v,slot⟩))=true := h
      rw [ite_eq_left hv] at hh
      rw [hh,ite_eq_left h]
    · have hv : ¬∀ v,subdividedTable p v
          (fun slot => assignment (orderedEdgeAt p.digits_pos p.cap ⟨v,slot⟩))=true := h
      rw [ite_eq_right hv] at hh
      rw [hh,ite_eq_right h]
  calc
    _ = ∑ assignment : Edge p.r p.t p.digits→Bool,
        if SubdividedAccepted p assignment then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro assignment ha
      exact he assignment
    _ = _ := subdivided_count_eq_inputs p

end RiemannGaussian.SemiprimeMacroGraphExtension
