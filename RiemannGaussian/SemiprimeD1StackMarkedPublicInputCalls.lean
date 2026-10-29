/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputEncoding
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputPrimitives
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Complete actual checker, extraction, product and fit calls
Each included trace has real caller/return instructions and preserves every
physical word outside its explicitly fixed image.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputCalls
open SemiprimeD1StackMarkedPublicInput SemiprimeD1StackMarkedPublicInputEncoding
open SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel)
end Link
/-- The original52-role checker runs completely before any marked arithmetic. -/
theorem checker_call (bits raw indexWord : List Bool) (hb : bits≠[]) (w : Work) :
    ∃ t ≤ SemiprimeD1StackPublicInputBounds.runBound bits raw indexWord+1,
      Runs program t (ctl .start) (data (P.initial bits raw indexWord).data w)
        (ctl .checked) (data (acquired bits raw indexWord) w) := by
  obtain ⟨t,ht,hr⟩ := SemiprimeD1StackPublicInputBounds.source_run_bounded bits raw indexWord hb
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program checker checkerLabel Sum.inl_injective
    P.program .start (fun _ => rfl) (ctl .start) (ctl .checked) rfl
    t (P.initial bits raw indexWord) (SemiprimeD1StackPublicInputState.done bits raw indexWord)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k; rfl
    · intro k _; rfl
  · constructor
    · intro k; rfl
    · intro k hk
      rcases k with k | k
      · exact False.elim (hk k rfl)
      · rfl
/-- Real full-width extraction reacquires the actual digit from a paid raw copy. -/
theorem block_call (p : P.Stack → List Bool) (w : Work) (raw : List Bool) :
    Runs program (SemiprimeD1StackWordBlockExecution.totalTime
      (p (.inl P.modulusKey))+1) (ctl .extract)
      (data p {w with reader := raw, count := [], reverse := [], digit := []})
      (ctl .index) (data p {w with reader := raw.drop (p (.inl P.modulusKey)).length, count := [], reverse := [], digit := SemiprimeD1StackWordBlockExecution.result raw (p (.inl P.modulusKey))}) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program blockStack blockLabel block_injective
    B.program .start (fun _ => rfl) (ctl .extract) (ctl .index) rfl _
    (SemiprimeD1StackWordBlock.initial raw (p (.inl P.modulusKey)))
    (SemiprimeD1StackWordBlockExecution.done raw (p (.inl P.modulusKey)))
    _ _ rfl rfl rfl rfl (SemiprimeD1StackWordBlockExecution.source_run raw (p (.inl P.modulusKey)))
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k _; rfl
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk
      rcases k with k | k
      · rfl
      · rcases k with k | k
        · fin_cases k <;> first | rfl | exact False.elim (hk 0 rfl) | exact False.elim (hk 4 rfl)
        · rfl
/-- Unary offset multiplication is performed by the frozen actual four-role loops. -/
theorem product_call (p : P.Stack → List Bool) (w : Work) (m d : List Bool) :
    ∃ t ≤ 5*(m.length*(2*d.length+3)+1)+1,
      Runs program t (ctl .multiply)
        (data p {w with multiplier := m, radix := d, productScratch := [], offset := []})
        (ctl .offset) (data p {w with multiplier := [], radix := d, productScratch := [], offset := List.replicate (m.length*d.length) true}) := by
  obtain ⟨t,ht,hr⟩ := SemiprimeD1StackUnaryProductRaw.product_run m d
  refine ⟨t+1,by omega,?_⟩
  apply included_call program product productLabel (by intro i j h; exact Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h)))
    U.code U.entry (fun _ => rfl) (ctl .multiply) (ctl .offset) rfl t
    (⟨some U.entry,none,SemiprimeD1StackUnaryProduct.contents m d [] []⟩)
    (⟨none,none,SemiprimeD1StackUnaryProduct.contents [] d [] (List.replicate (m.length*d.length) true)⟩)
    _ _ rfl rfl hr
  · constructor
    · intro k; cases k <;> rfl
    · intro k _; rfl
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk
      rcases k with k | k
      · rfl
      · rcases k with k | k
        · rfl
        · rcases k with k | k
          · exact False.elim (hk k rfl)
          · rfl
/-- All branches execute this SAME physical fit, with the twice-acquired template. -/
theorem fit_call (p : P.Stack → List Bool) (w : Work) :
    Runs program (SemiprimeD1StackWordFitExecution.totalTime w.shifted w.template+1)
      (ctl .fit) (data p {w with count := [], reverse := [], output := []})
      (ctl .clearRaw) (data p {w with count := [], reverse := [], shifted := [], output := SemiprimeD1StackWordFitExecution.result w.shifted w.template}) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program fitStack fitLabel fit_injective
    F.program .start (fun _ => rfl) (ctl .fit) (ctl .clearRaw) rfl _
    (SemiprimeD1StackWordFit.initial w.shifted w.template)
    (SemiprimeD1StackWordFitExecution.done w.shifted w.template)
    _ _ rfl rfl rfl rfl (SemiprimeD1StackWordFitExecution.source_run w.shifted w.template)
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k _; rfl
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk
      rcases k with k | k
      · rfl
      · rcases k with k | k
        · fin_cases k <;> rfl
        · rcases k with k | k
          · rfl
          · cases k <;> first | rfl | exact False.elim (hk 0 rfl) | exact False.elim (hk 4 rfl)
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputCalls

