/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputCalls
/-! # Actual retained-input and metadata preserving copies -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputCopies
open SemiprimeD1StackMarkedPublicInput SemiprimeD1StackMarkedPublicInputEncoding
open SemiprimeD1StackMarkedPublicInputPrimitives SemiprimeD1StackProcedureTrace
/-- Real raw preserving copy includes its physical caller and return. -/
theorem raw_copy (p : P.Stack → List Bool) (w : Work) :
    Runs program (5*(p P.assignment).length+4) (ctl .raw)
      (data p {w with reader := [], scratch := []}) (ctl .extract)
      (data p {w with reader := p P.assignment, scratch := []}) := by
  have h := copy_call 0 .raw .extract rfl
    (data p {w with reader := [], scratch := []}) (p P.assignment) [] rfl rfl rfl
  rw [show copyStack 0 1=word 0 from rfl] at h
  simpa only [List.append_nil,update_reader] using h
/-- Real index preserving copy includes its physical caller and return. -/
theorem index_copy (p : P.Stack → List Bool) (w : Work) :
    Runs program (5*(p P.index).length+4) (ctl .index)
      (data p {w with multiplier := [], scratch := []}) (ctl .radix)
      (data p {w with multiplier := p P.index, scratch := []}) := by
  have h := copy_call 1 .index .radix rfl
    (data p {w with multiplier := [], scratch := []}) (p P.index) [] rfl rfl rfl
  rw [show copyStack 1 1=product .multiplier from rfl] at h
  simpa only [List.append_nil,update_multiplier] using h
/-- Real radix preserving copy includes its physical caller and return. -/
theorem radix_copy (p : P.Stack → List Bool) (w : Work) :
    Runs program (5*(p (.inl (.inl SemiprimeD1StackPublicInputWidth.radixKey))).length+4) (ctl .radix)
      (data p {w with radix := [], scratch := []}) (ctl .multiply)
      (data p {w with radix := p (.inl (.inl SemiprimeD1StackPublicInputWidth.radixKey)), scratch := []}) := by
  have h := copy_call 2 .radix .multiply rfl
    (data p {w with radix := [], scratch := []}) (p (.inl (.inl SemiprimeD1StackPublicInputWidth.radixKey))) [] rfl rfl rfl
  rw [show copyStack 2 1=product .multiplicand from rfl] at h
  simpa only [List.append_nil,update_radix] using h
/-- Real digit preserving copy includes its physical caller and return. -/
theorem digit_copy (p : P.Stack → List Bool) (w : Work) :
    Runs program (5*(w.digit).length+4) (ctl .digit)
      (data p {w with shifted := [], scratch := []}) (ctl .shift)
      (data p {w with shifted := w.digit, scratch := []}) := by
  have h := copy_call 4 .digit .shift rfl
    (data p {w with shifted := [], scratch := []}) (w.digit) [] rfl rfl rfl
  rw [show copyStack 4 1=aux .shifted from rfl] at h
  simpa only [List.append_nil,update_shifted] using h
/-- The acquired ell markers are physically prepended to the actual offset product. -/
theorem offset_copy (p : P.Stack → List Bool) (w : Work) :
    Runs program (5*(p (.inl (.inl SemiprimeD1StackPublicInputWidth.widthKey))).length+4)
      (ctl .offset) (data p {w with scratch := []}) (ctl .digit)
      (data p {w with offset := p (.inl (.inl SemiprimeD1StackPublicInputWidth.widthKey))++w.offset, scratch := []}) := by
  have h := copy_call 3 .offset .digit rfl (data p {w with scratch := []})
    (p (.inl (.inl SemiprimeD1StackPublicInputWidth.widthKey))) w.offset rfl rfl rfl
  rw [show copyStack 3 1=product .product from rfl] at h
  simpa only [update_offset] using h
/-- Both width-template copies visit the real ell cache, appending to the physical destination. -/
theorem width_copy (p : P.Stack → List Bool) (w : Work) (pc next : Control)
    (hc : program (ctl pc)=.call (copyLabel 5 0) (ctl next)) :
    Runs program (5*(p (.inl (.inl SemiprimeD1StackPublicInputWidth.widthKey))).length+4)
      (ctl pc) (data p {w with scratch := []}) (ctl next)
      (data p {w with template := p (.inl (.inl SemiprimeD1StackPublicInputWidth.widthKey))++w.template, scratch := []}) := by
  have h := copy_call 5 pc next hc (data p {w with scratch := []})
    (p (.inl (.inl SemiprimeD1StackPublicInputWidth.widthKey))) w.template rfl rfl rfl
  rw [show copyStack 5 1=aux .widthTemplate from rfl] at h
  simpa only [update_template] using h
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputCopies

