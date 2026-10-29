/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireExecution
/-! # Entire original selected-key acquisition and retained actual source banks
The expected native runs below are mathematical meanings only. Every actual
occurrence, factor counter, alphabet/power, selector/cache and key has already
been constructed by the SAME literal three-input program in source_run.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireOriginal
open SemiprimeD1StackSourceSelectionAcquire SemiprimeD1StackSourceSelectionAcquireEncoding
open SemiprimeD1StackSourceSelectionAcquireExecution
open SemiprimeD1TensorTapeCodec (vectorBits)
attribute [local irreducible] SemiprimeD1IncidenceSearch.run SemiprimeD1IncidenceAcquisition.acquire
/-- The whole acquired output is EXACTthe original incidence acquisition key vector, in its original occurrence order. -/
theorem output_original (net:N.Network) (a:Nat) :
    result net a (keyStack (Keys.aux .output))=
      vectorBits (SemiprimeD1IncidenceAcquisition.acquire net.leftCount net.rows.length 64 a
        (N.arity net.rows) (N.owner net.rows)).keys :=
  SemiprimeD1StackSourceSelectedKeysOriginal.output_original net.leftCount net.rows.length 64 a
    (N.arity net.rows) (N.owner net.rows) [] [] (vectorBits (selectedIDs net a))
/-- Every21-role original row/count/key/helper field remains physically retained. -/
theorem occurrence_retained (net:N.Network) (a:Nat) (k:Occ.Stack) :
    result net a (occurrenceStack k)=(occurrenceDone net).data k :=rfl
/-- Every30-role original alphabet, colour row and binary power field remains physically retained. -/
theorem alphabet_retained (net:N.Network) (a:Nat) (k:Alpha.Stack) :
    result net a (alphabetStack k)=(alphabetDone a).data k :=rfl
/-- Every63-role selected/query/cache field remains retained for subsequent real packet construction. -/
theorem selector_retained (net:N.Network) (a:Nat) (k:Select.Stack) :
    result net a (selectorStack k)=(selectorDone net a).data k :=rfl
/-- Every39-role selected-key source/cache/helper field has its exact whole-source value. -/
theorem key_retained (net:N.Network) (a:Nat) (k:Keys.Stack) :
    result net a (keyStack k)=(keyDone net a).data k :=rfl
/-- The original factor count, including every empty factor, is acquired internally by the actual prescan. -/
theorem factor_count (net:N.Network) (a:Nat) :
    result net a (occurrenceStack .factors)=List.replicate net.rows.length true :=
  SemiprimeD1StackSourceOccurrencesOriginal.factor_count net
/-- Actual original unary n is retained rather than supplied as a decoded runtime counter. -/
theorem number_retained (net:N.Network) (a:Nat) :
    result net a (occurrenceStack .number)=List.replicate net.leftCount true :=rfl
/-- The actual unary alphabet dimension remains available for a paid packet-padding source. -/
theorem dimension_retained (net:N.Network) (a:Nat) :
    result net a (alphabetStack (Alpha.aux .source))=List.replicate a true :=rfl
/-- Complete selected Env25 is exactly the reached original full-selection dictionary/key/prefix state. -/
theorem environment_original (net:N.Network) (a:Nat) (k:Env.Stack) :
    result net a (selectorStack (SemiprimeD1StackSourceIncidenceSelect.environmentStack k))=
      SemiprimeD1StackSourceEnvironmentExecution.result (selectedIDs net a) k :=
  SemiprimeD1StackSourceIncidenceSelectOriginal.acquired_environment net.leftCount net.rows.length a
    (N.arity net.rows) (N.owner net.rows) k
/-- Physical input ABI is the upstream original row output plus actual unary n/a, with no F or derived cache. -/
theorem input_rows (net:N.Network) (a:Nat) :
    (source net a).data (occurrenceStack .rows)=SemiprimeD1StackNetworkRowsEncoding.originalTape net :=
  SemiprimeD1StackSourceOccurrencesEncoding.original_input net
/-- Whole exact original acquisition has its own actual complete-source clock, never an old transported report. -/
theorem source_original (net:N.Network) (a:Nat) :
    ∃t ≤ timeBound net a,SemiprimeD1StackCalls.run program t (source net a)=some (done net a) ∧
      (done net a).data (keyStack (Keys.aux .output))=
        vectorBits (SemiprimeD1IncidenceAcquisition.acquire net.leftCount net.rows.length 64 a
          (N.arity net.rows) (N.owner net.rows)).keys :=by
  obtain ⟨t,ht,he⟩:=source_run net a
  exact ⟨t,ht,he,output_original net a⟩
end RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireOriginal
