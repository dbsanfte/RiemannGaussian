/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireCalls
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireSelectorInput
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireKeyInput
/-! # Original typed-row family of the actual three-input source
Networks, lists, counts and original native runs below are proof descriptions
of the physical input/output banks. None is accepted by the literal program.
The caller must acquire the original row/n/a bytes; this source pays all later
occurrence, factor-count, alphabet, selection and selected-key construction.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireEncoding
open SemiprimeD1StackSourceSelectionAcquire SemiprimeD1StackSourceSelectionAcquireSelectorInput
open SemiprimeD1StackSourceSelectionAcquireKeyInput
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace N
export SemiprimeD1TensorNetwork (Network arity owner)
end N
attribute [local irreducible] SemiprimeD1IncidenceSearch.run SemiprimeD1IncidenceAcquisition.acquire
/-- Exact original physical binary-owner rows, with all original local-slot occurrences preserved. -/
def originalRows (net:N.Network) :List (List (List Bool)) :=SemiprimeD1StackSourceOccurrencesEncoding.originalRows net
/-- Actual complete21-role acquired occurrence/F/M result. -/
def occurrenceDone (net:N.Network) :C.State Occ.Stack Occ.Label :=
  SemiprimeD1StackSourceOccurrencesExecution.done net.leftCount (originalRows net)
/-- Actual acquired30-role original alphabet/power result. -/
def alphabetDone (a:Nat) :C.State Alpha.Stack Alpha.Label :=SemiprimeD1StackSourceAlphabet64Encoding.done a
/-- Actual original63-role selector entry from the original occurrence and acquired alphabet ABIs. -/
def selectorSource (net:N.Network) (a:Nat) :C.State Select.Stack Select.Label :=
  SemiprimeD1StackSourceIncidenceSelectOriginal.acquiredSource net.leftCount net.rows.length a
    (N.arity net.rows) (N.owner net.rows)
/-- Exact actual stopped63-role source, preserving its complete selected cache. -/
def selectorDone (net:N.Network) (a:Nat) :C.State Select.Stack Select.Label :=
  SemiprimeD1StackSourceIncidenceSelectOriginal.acquiredDone net.leftCount net.rows.length a
    (N.arity net.rows) (N.owner net.rows)
/-- Exact original newest-first IDs, used only to specify the reached cache/prefix. -/
def selectedIDs (net:N.Network) (a:Nat) :List (List Bool) :=
  (SemiprimeD1IncidenceSearch.run net.leftCount net.rows.length 64 a (N.arity net.rows) (N.owner net.rows)).value
/-- Proof interpretation of the actual stopped cache and actual original occurrence bytes. -/
def keyInput (net:N.Network) (a:Nat) :SemiprimeD1StackSourceSelectedKeysEncoding.Inputs :=
  SemiprimeD1StackSourceSelectedKeysOriginal.originalInput net.leftCount net.rows.length 64 a
    (N.arity net.rows) (N.owner net.rows) [] [] (vectorBits (selectedIDs net a))
/-- The entire actual39-role selected-key source stop, including every retained cache word. -/
def keyDone (net:N.Network) (a:Nat) :C.State Keys.Stack Keys.Label :=
  SemiprimeD1StackSourceSelectedKeysEncoding.done (keyInput net a)
/-- Actual initial configuration contains ONLYthe original nested row, unary n and unary a words. -/
def source (net:N.Network) (a:Nat) :C.State Stack Label :=
  initial (SemiprimeD1StackSourceOccurrencesEncoding.inputTape (originalRows net))
    (List.replicate net.leftCount true) (List.replicate a true)
/-- All154 actual acquired/cache/selected/output/shadow fields at the complete whole source stop. -/
def result (net:N.Network) (a:Nat) :Stack→List Bool :=
  data (occurrenceDone net).data (alphabetDone a).data (selectorDone net a).data (keyDone net a).data []
/-- Genuine final halt; no source/work/return word is silently reset. -/
def done (net:N.Network) (a:Nat) :C.State Stack Label :=⟨none,none,none,result net a,[]⟩
/-- Own original selector allowance in ONLYits actual acquired physical input bytes. -/
def selectorBound (net:N.Network) (a:Nat) :Nat :=
  10^30*(SemiprimeD1StackSourceIncidenceSelectOriginal.acquiredSize net.leftCount net.rows.length a
    (N.arity net.rows) (N.owner net.rows)+1)^16
/-- Own whole source clock retains every one of the four actual producer/consumer clocks and all eleven copies. -/
def timeBound (net:N.Network) (a:Nat) :Nat :=
  SemiprimeD1StackSourceOccurrencesExecution.timeBound net.leftCount (originalRows net)+
    10000*(a+1)*(64^a+1)+selectorCopyTime (occurrenceDone net).data (alphabetDone a).data+
    selectorBound net a+keyCopyTime (selectorDone net a).data+
    SemiprimeD1StackSourceSelectedKeysBounds.polynomial (keyInput net a)+5
end RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireEncoding
