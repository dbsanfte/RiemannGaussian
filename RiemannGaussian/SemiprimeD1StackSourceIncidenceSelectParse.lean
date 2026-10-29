/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectView
/-! # Complete actual catalogue candidate parsing
Both actual framed fields and both physical valid-byte pops are charged. The
unused colour row is really drained; only the actual compact candidate word is
retained for the shared environment extension and real scorer call.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectParse
open SemiprimeD1StackSourceIncidenceSelect SemiprimeD1StackSourceIncidenceSelectPrimitives
open SemiprimeD1StackSourceIncidenceSelectView SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
/-- Actual tagged candidate record is parsed in order, with no advised ID/colour/count operand. -/
theorem candidate_run (first:Bool) (ids:List (List Bool))
    (pfx stream square cube fourth catalogue owners factors todo savedKey bestID bestScore:List Bool)
    (id colour:List Bool) (rows:List (List Bool×List Bool)) :
    Runs program (8*id.length+9*colour.length+18) (ctl (.header first))
      (clean ids [] pfx stream square cube fourth catalogue owners factors todo
        (SemiprimeD1StackOwnerLookup.records ((id,colour)::rows) []) savedKey bestID bestScore [])
      (ctl (.install first))
      (clean ids id pfx stream square cube fourth catalogue owners factors todo
        (SemiprimeD1StackOwnerLookup.records rows []) savedKey bestID bestScore []) :=by
  let tail:=SemiprimeD1StackOwnerLookup.records rows []
  have h0:=pop_run (.header first) (ctl .abort) (ctl (if first then .abort else .catalogueEOF))
    (ctl (.parseID first)) (aux .reader)
    (clean ids [] pfx stream square cube fourth catalogue owners factors todo
      (SemiprimeD1StackOwnerLookup.records ((id,colour)::rows) []) savedKey bestID bestScore [])
    (true::frame id (frame colour tail)) rfl rfl
  change Runs program 1 _ _ _ (Function.update
    (clean ids [] pfx stream square cube fourth catalogue owners factors todo
      (SemiprimeD1StackOwnerLookup.records ((id,colour)::rows) []) savedKey bestID bestScore [])
    (aux .reader) (frame id (frame colour tail))) at h0
  rw [clean_reader] at h0
  have h1:=field_valid .candidate (.parseID first) (.idValid first) (ctl (.parseColour first)) rfl rfl
    (clean ids [] pfx stream square cube fourth catalogue owners factors todo
      (frame id (frame colour tail)) savedKey bestID bestScore []) id (frame colour tail) rfl rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update
    (clean ids [] pfx stream square cube fourth catalogue owners factors todo
      (frame id (frame colour tail)) savedKey bestID bestScore []) (aux .reader) (frame colour tail)) candidate id) at h1
  rw [clean_reader,clean_chosen] at h1
  have h2:=field_discard .colour (.parseColour first) (.colourValid first) (.drainColour first)
    (ctl (.install first)) rfl rfl rfl
    (clean ids id pfx stream square cube fourth catalogue owners factors todo (frame colour tail) savedKey bestID bestScore [])
    colour tail rfl rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (clean ids id pfx stream square cube fourth catalogue owners factors todo (frame colour tail) savedKey bestID bestScore [])
    (aux .reader) tail) at h2
  rw [clean_reader] at h2
  have h:=join (join h0 h1) h2
  have ht:1+(8*id.length+8)+(9*colour.length+9)=8*id.length+9*colour.length+18:=by omega
  simpa only [ht,tail] using h
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectParse
