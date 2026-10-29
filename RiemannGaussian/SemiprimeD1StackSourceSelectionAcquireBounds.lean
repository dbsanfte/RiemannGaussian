/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireExecution
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireProjection
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Storage
/-! # Whole physical three-input acquisition envelope with the actual alphabet paid
The original typed network is a proof interpretation of the acquired row word.
All intermediate word bounds come from the SAME actual21/30/63 source traces;
the final39 source keeps its own actual cubic acquired-byte clock. The factor
64^a is explicitly included in the input envelope and is never made free.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireBounds
open SemiprimeD1StackSourceSelectionAcquire SemiprimeD1StackSourceSelectionAcquireEncoding
open SemiprimeD1StackSourceSelectionAcquireSelectorInput SemiprimeD1StackSourceSelectionAcquireKeyInput
open SemiprimeD1StackSourceSelectionAcquireProjection
attribute [local irreducible] SemiprimeD1IncidenceSearch.run SemiprimeD1IncidenceAcquisition.acquire
/-- Actual original row bytes, unary owner/exponent bytes, genuinely enumerated alphabet cardinality and one unit. -/
def inputSize (net:N.Network) (a:Nat) :Nat:=
  (SemiprimeD1StackSourceOccurrencesEncoding.inputTape (originalRows net)).length+net.leftCount+a+64^a+1
/-- Only SAME actual21/30 source caps augment the actual physical input envelope. -/
def producerEnvelope (net:N.Network) (a:Nat) :Nat:=inputSize net a+
  SemiprimeD1StackSourceOccurrencesBounds.polynomial net.leftCount (originalRows net)+10000*(a+1)*(64^a+1)
/-- Complete stopped selector word envelope follows its own actual input and actual whole trace. -/
def cacheEnvelope (net:N.Network) (a:Nat) :Nat:=producerEnvelope net a+selectorBound net a+1
/-- Basic retained physical input words and the actual alphabet count are all paid before any source call. -/
theorem input_bounds (net:N.Network) (a:Nat) :1≤ inputSize net a ∧
    SemiprimeD1StackSourceOccurrencesBounds.inputSize net.leftCount (originalRows net)≤ inputSize net a ∧
    a+1≤ inputSize net a ∧ 64^a+1≤ inputSize net a :=by
  have hL:0<64^a:=pow_pos (by decide) a
  unfold inputSize SemiprimeD1StackSourceOccurrencesBounds.inputSize
  omega
/-- The producer envelope is positive and retains every actual original input byte. -/
theorem envelope_pos (net:N.Network) (a:Nat) :1≤ producerEnvelope net a :=by
  have h:=(input_bounds net a).1
  unfold producerEnvelope
  omega
/-- ALL21 acquired occurrence/F/M/source/scratch words are bounded using the SAME actual whole occurrence run. -/
theorem occurrence_word_bound (net:N.Network) (a:Nat) (k:Occ.Stack) :
    ((occurrenceDone net).data k).length≤ producerEnvelope net a :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackSourceOccurrencesBounds.source_run_bounded net.leftCount (originalRows net)
  have hi:∀k,((SemiprimeD1StackSourceOccurrencesExecution.source net.leftCount (originalRows net)).data k).length≤ inputSize net a:=by
    intro k
    have h:=SemiprimeD1StackSourceOccurrencesExecution.initial_length net.leftCount (originalRows net) k
    have hb:=(input_bounds net a).2.1
    unfold SemiprimeD1StackSourceOccurrencesBounds.inputSize at hb
    exact h.trans (by omega)
  have hd:=SemiprimeD1StackReturnLink.run_data_bound Occ.program q (inputSize net a) _ _ hi hr k
  change ((occurrenceDone net).data k).length≤ inputSize net a+q at hd
  exact hd.trans (by unfold producerEnvelope;omega)
/-- ALL30 actual acquired alphabet/counter/power/catalogue words are paid by the SAME actual alphabet construction trace. -/
theorem alphabet_word_bound (net:N.Network) (a:Nat) (k:Alpha.Stack) :
    ((alphabetDone a).data k).length≤ producerEnvelope net a :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackSourceAlphabet64Bounds.source_run_bounded a
  have hi:∀k,((Alpha.initial (List.replicate a true)).data k).length≤ inputSize net a:=by
    intro k
    exact (SemiprimeD1StackSourceAlphabet64Storage.initial_role_bound a k).trans
      (by have h:=(input_bounds net a).2.2.1;omega)
  have hd:=SemiprimeD1StackReturnLink.run_data_bound Alpha.program q (inputSize net a) _ _ hi hr k
  change ((alphabetDone a).data k).length≤ inputSize net a+q at hd
  exact hd.trans (by unfold producerEnvelope;omega)
/-- The generic seven-word selector input has no physical word larger than its actually acquired producer envelope. -/
theorem selector_initial_word_bound (net:N.Network) (a:Nat) (k:Select.Stack) :
    ((selectorSource net a).data k).length≤ producerEnvelope net a :=by
  have he:selectorReady (occurrenceDone net).data (alphabetDone a).data=(selectorSource net a).data:=
    selectorReady_original net a
  rw [←he,selectorReady_eq_initial]
  rcases k with k|k
  · rcases k with k|k
    · exact Nat.zero_le _
    · cases k <;> first
      | exact occurrence_word_bound net a .output
      | exact alphabet_word_bound net a (Alpha.aux .square)
      | exact alphabet_word_bound net a (Alpha.aux .cube)
      | exact alphabet_word_bound net a (Alpha.aux .fourth)
      | exact Nat.zero_le _
  · cases k <;> first
    | exact alphabet_word_bound net a (Alpha.aux .output)
    | exact occurrence_word_bound net a .number
    | exact occurrence_word_bound net a .factors
    | exact Nat.zero_le _
/-- The actual seven acquired source words bound the entire original selector input, including unary n/F and catalogue colour bytes. -/
theorem selectorSize_le (net:N.Network) (a:Nat) :
    SemiprimeD1StackSourceIncidenceSelectOriginal.acquiredSize net.leftCount net.rows.length a
      (N.arity net.rows) (N.owner net.rows)+1≤9*producerEnvelope net a :=by
  have ho:=occurrence_word_bound net a .output
  have hN:=occurrence_word_bound net a .number
  have hF:=occurrence_word_bound net a .factors
  have hc:=alphabet_word_bound net a (Alpha.aux .output)
  have hs:=alphabet_word_bound net a (Alpha.aux .square)
  have hu:=alphabet_word_bound net a (Alpha.aux .cube)
  have hf:=alphabet_word_bound net a (Alpha.aux .fourth)
  change (SemiprimeD1StackSourceAlphabet64Encoding.result a (Alpha.aux .output)).length≤ producerEnvelope net a at hc
  change (SemiprimeD1StackSourceAlphabet64Encoding.result a (Alpha.aux .square)).length≤ producerEnvelope net a at hs
  change (SemiprimeD1StackSourceAlphabet64Encoding.result a (Alpha.aux .cube)).length≤ producerEnvelope net a at hu
  change (SemiprimeD1StackSourceAlphabet64Encoding.result a (Alpha.aux .fourth)).length≤ producerEnvelope net a at hf
  have hp:=envelope_pos net a
  have hout:=SemiprimeD1StackSourceOccurrencesOriginal.output_original net
  have hfac:=SemiprimeD1StackSourceOccurrencesOriginal.factor_count net
  unfold SemiprimeD1StackSourceOccurrencesOriginal.originalDone at hout hfac
  change ((occurrenceDone net).data .output)=_ at hout
  change ((occurrenceDone net).data .factors)=_ at hfac
  rw [hout,←SemiprimeD1StackSourceIncidenceSelectOccurrences.network_original_keys net a] at ho
  rw [hfac,List.length_replicate] at hF
  change (List.replicate net.leftCount true).length≤_ at hN
  rw [List.length_replicate] at hN
  unfold SemiprimeD1StackSourceIncidenceSelectOriginal.acquiredSize
  change _≤9*producerEnvelope net a
  omega
/-- Every actual63-word stopped cache bound comes from the SAME closed actual selector run, not a supplied selected-ID width or report clock. -/
theorem selector_word_bound (net:N.Network) (a:Nat) (k:Select.Stack) :
    ((selectorDone net a).data k).length≤ producerEnvelope net a+selectorBound net a :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackSourceIncidenceSelectOriginal.acquired_source_run net.leftCount net.rows.length a
    (N.arity net.rows) (N.owner net.rows)
  have hd:=SemiprimeD1StackReturnLink.run_data_bound Select.program q (producerEnvelope net a) _ _
    (selector_initial_word_bound net a) hr k
  change ((selectorDone net a).data k).length≤ producerEnvelope net a+q at hd
  exact hd.trans (Nat.add_le_add_left hq _)
/-- Actual four-field handoff and the SAME stopped63-word trace bound the entire39-role input cache/tape size. -/
theorem keyInputSize_le (net:N.Network) (a:Nat) :
    SemiprimeD1StackSourceSelectedKeysEncoding.inputSize (keyInput net a)≤5*cacheEnvelope net a :=by
  have he:keyReady (selectorDone net a).data=(SemiprimeD1StackSourceSelectedKeysEncoding.source (keyInput net a)).data:=
    keyReady_original net.leftCount net.rows.length a (N.arity net.rows) (N.owner net.rows)
  have hD:((SemiprimeD1StackSourceSelectedKeysEncoding.source (keyInput net a)).data
      (Keys.environmentStack (Env.aux .dictionary))).length≤ producerEnvelope net a+selectorBound net a:=by
    rw [←he]
    exact selector_word_bound net a Select.dictionary
  have hK:((SemiprimeD1StackSourceSelectedKeysEncoding.source (keyInput net a)).data
      (Keys.environmentStack (Env.aux .nextKey))).length≤ producerEnvelope net a+selectorBound net a:=by
    rw [←he]
    exact selector_word_bound net a Select.nextKey
  have hP:((SemiprimeD1StackSourceSelectedKeysEncoding.source (keyInput net a)).data
      (Keys.environmentStack (Env.aux .prefix))).length≤ producerEnvelope net a+selectorBound net a:=by
    rw [←he]
    exact selector_word_bound net a Select.selected
  have hS:((SemiprimeD1StackSourceSelectedKeysEncoding.source (keyInput net a)).data
      (Keys.aux .source)).length≤ producerEnvelope net a+selectorBound net a:=by
    rw [←he]
    exact selector_word_bound net a (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .source))
  change (SemiprimeD1StackSourceSelectedKeysEncoding.tape (keyInput net a)).length≤_ at hS
  change (SemiprimeD1StackSourceEnvironmentEncoding.dictionary (selectedIDs net a)).length≤_ at hD
  change (SemiprimeD1StackSourceEnvironmentEncoding.variableKey (selectedIDs net a).length).length≤_ at hK
  change (SemiprimeD1TensorTapeCodec.vectorBits (selectedIDs net a)).length≤_ at hP
  unfold SemiprimeD1StackSourceSelectedKeysEncoding.inputSize SemiprimeD1StackSourceEnvironmentBounds.cacheSize
  change (SemiprimeD1StackSourceSelectedKeysEncoding.tape (keyInput net a)).length+
    ((SemiprimeD1StackSourceEnvironmentEncoding.dictionary (selectedIDs net a)).length+
      (SemiprimeD1StackSourceEnvironmentEncoding.variableKey (selectedIDs net a).length).length+
      0+0+(SemiprimeD1TensorTapeCodec.vectorBits (selectedIDs net a)).length+1)≤_
  unfold cacheEnvelope
  omega
/-- Seven real preserving input copies pay precisely the seven acquired input words, with all actual returns included. -/
theorem selectorCopyTime_le (net:N.Network) (a:Nat) :
    selectorCopyTime (occurrenceDone net).data (alphabetDone a).data≤35*producerEnvelope net a+28 :=by
  have h0:=occurrence_word_bound net a .output
  have h1:=alphabet_word_bound net a (Alpha.aux .output)
  have h2:=alphabet_word_bound net a (Alpha.aux .square)
  have h3:=alphabet_word_bound net a (Alpha.aux .cube)
  have h4:=alphabet_word_bound net a (Alpha.aux .fourth)
  have h5:=occurrence_word_bound net a .number
  have h6:=occurrence_word_bound net a .factors
  unfold selectorCopyTime
  omega
/-- Four actual stopped-selector word copies pay every selected cache/key/prefix/occurrence byte. -/
theorem keyCopyTime_le (net:N.Network) (a:Nat) :
    keyCopyTime (selectorDone net a).data≤20*(producerEnvelope net a+selectorBound net a)+16 :=by
  have h0:=selector_word_bound net a Select.dictionary
  have h1:=selector_word_bound net a Select.nextKey
  have h2:=selector_word_bound net a Select.selected
  have h3:=selector_word_bound net a (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .source))
  unfold keyCopyTime
  omega
/-- The actual39 source keeps its own cubic clock on its actually acquired cache/tape bytes. -/
theorem keysClock_le (net:N.Network) (a:Nat) :
    SemiprimeD1StackSourceSelectedKeysBounds.polynomial (keyInput net a)≤1250000000*(cacheEnvelope net a)^3 :=by
  have h:=Nat.pow_le_pow_left (keyInputSize_le net a) 3
  unfold SemiprimeD1StackSourceSelectedKeysBounds.polynomial
  calc
    _≤10000000*(5*cacheEnvelope net a)^3:=Nat.mul_le_mul_left _ h
    _=1250000000*(cacheEnvelope net a)^3:=by ring
/-- All four SAME actual source clocks and eleven paid copies compose within one cubic acquired-cache envelope. -/
theorem timeBound_envelope (net:N.Network) (a:Nat) :timeBound net a≤10^12*(cacheEnvelope net a)^3 :=by
  have ho:=SemiprimeD1StackSourceOccurrencesBounds.timeBound_le net.leftCount (originalRows net)
  have hs:=selectorCopyTime_le net a
  have hk:=keyCopyTime_le net a
  have ht:=keysClock_le net a
  have hp:=envelope_pos net a
  have hC:1≤ cacheEnvelope net a:=by unfold cacheEnvelope;omega
  have hC3:cacheEnvelope net a≤(cacheEnvelope net a)^3:=Nat.le_pow (by decide:0<(3:Nat))
  unfold timeBound cacheEnvelope producerEnvelope at *
  norm_num only [Nat.reducePow] at *
  omega
/-- The actual input and SAME21/30 clocks have one fixed quadratic envelope, with64^a explicitly present. -/
theorem producerEnvelope_le (net:N.Network) (a:Nat) :producerEnvelope net a≤10^7*(inputSize net a)^2 :=by
  let R:=inputSize net a
  have hR:1≤ R:=(input_bounds net a).1
  have ho:=Nat.pow_le_pow_left (input_bounds net a).2.1 2
  have hm:=Nat.mul_le_mul (input_bounds net a).2.2.1 (input_bounds net a).2.2.2
  have hself:R≤ R^2:=Nat.le_pow (by decide:0<(2:Nat))
  unfold producerEnvelope SemiprimeD1StackSourceOccurrencesBounds.polynomial
  change R+1000000*(SemiprimeD1StackSourceOccurrencesBounds.inputSize net.leftCount (originalRows net))^2+
    10000*(a+1)*(64^a+1)≤10^7*R^2
  norm_num only [Nat.reducePow]
  nlinarith only [ho,hm,hself]
/-- The same actual selector input bound yields a fixed degree32 original physical-source cap. -/
theorem selectorBound_le (net:N.Network) (a:Nat) :selectorBound net a≤10^158*(inputSize net a)^32 :=by
  have hs:=selectorSize_le net a
  have hp:=producerEnvelope_le net a
  have h9:9*producerEnvelope net a≤10^8*(inputSize net a)^2:=by norm_num only [Nat.reducePow] at hp ⊢;omega
  have h:=Nat.pow_le_pow_left (hs.trans h9) 16
  unfold selectorBound
  calc
    _≤10^30*(10^8*(inputSize net a)^2)^16:=Nat.mul_le_mul_left _ h
    _=10^158*(inputSize net a)^32:=by ring
/-- All actual stopped cache words are bounded by a fixed degree32 physical-input expression. -/
theorem cacheEnvelope_le (net:N.Network) (a:Nat) :cacheEnvelope net a≤10^159*(inputSize net a)^32 :=by
  have hp:=producerEnvelope_le net a
  have hs:=selectorBound_le net a
  have hR:1≤ inputSize net a:=(input_bounds net a).1
  have hpow:(inputSize net a)^2≤(inputSize net a)^32:=Nat.pow_le_pow_right hR (by decide)
  have h1:1≤(inputSize net a)^32:=Nat.one_le_pow _ _ hR
  have hb:producerEnvelope net a≤10^7*(inputSize net a)^32:=hp.trans (Nat.mul_le_mul_left _ hpow)
  unfold cacheEnvelope
  norm_num only [Nat.reducePow] at hs hb ⊢
  omega
/-- Universal whole-source polynomial with fixed constants before all networks and exponents. -/
def polynomial (net:N.Network) (a:Nat) :Nat:=10^500*(inputSize net a)^100
set_option exponentiation.threshold 512 in
/-- The actual four-source trace retains its own clocks throughout; no old native report clock is transported. -/
theorem timeBound_le (net:N.Network) (a:Nat) :timeBound net a≤ polynomial net a :=by
  have ht:=timeBound_envelope net a
  have hc:=Nat.pow_le_pow_left (cacheEnvelope_le net a) 3
  have hR:1≤ inputSize net a:=(input_bounds net a).1
  have hp:(inputSize net a)^96≤(inputSize net a)^100:=Nat.pow_le_pow_right hR (by decide)
  calc
    timeBound net a≤10^12*(cacheEnvelope net a)^3:=ht
    _≤10^12*(10^159*(inputSize net a)^32)^3:=Nat.mul_le_mul_left _ hc
    _=10^489*(inputSize net a)^96:=by
      calc
        _=(10^12*10^(159*3))*(inputSize net a)^(32*3):=by rw [mul_pow,←pow_mul,←pow_mul,Nat.mul_assoc]
        _=10^(12+159*3)*(inputSize net a)^(32*3):=by rw [pow_add]
        _=10^489*(inputSize net a)^96:=rfl
    _≤10^500*(inputSize net a)^100:=Nat.mul_le_mul (Nat.pow_le_pow_right (n:=10) (i:=489) (j:=500) (by decide) (by decide)) hp
    _=polynomial net a:=rfl
/-- Whole literal three-input source has the same original-row exact stop within the fixed physical-input polynomial. -/
theorem source_run_bounded (net:N.Network) (a:Nat) :∃q≤ polynomial net a,
    SemiprimeD1StackCalls.run program q (source net a)=some (done net a) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackSourceSelectionAcquireExecution.source_run net a
  exact ⟨q,hq.trans (timeBound_le net a),hr⟩
/-- Genuine fixed154-role finite machine executes the same whole source with its own polynomial clock. -/
noncomputable def machineSource (net:N.Network) (a:Nat) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (source net a))
      (some (SemiprimeD1StackCalls.configuration (done net a))) (polynomial net a) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (occurrenceStack .rows) (keyStack (Keys.aux .output)) (Label.local .start) program
  let h:=source_run_bounded net a
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireBounds
