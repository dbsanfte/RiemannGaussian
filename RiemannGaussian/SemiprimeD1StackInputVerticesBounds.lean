/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackInputVerticesExecution
import RiemannGaussian.SemiprimeD1StackTransformBounds
import RiemannGaussian.SemiprimeMacroFiniteEnumerations
import RiemannGaussian.SemiprimeD1StackGraphIndicesBounds

/-! # Actual tagged input-vertex data and all-prefix machine storage
The original input block, including its precise Fin2×FinR order, is acquired
from binary N. Other vertex/port/checker families remain separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackInputVerticesBounds
open SemiprimeD1StackInputVertices SemiprimeD1StackInputVerticesComponents SemiprimeD1StackInputVerticesExecution
open SemiprimeMacroParameters SemiprimeBitArithmetic
open SemiprimeD1StackInputVerticesLoop
open SemiprimeSourceHistogramKeyBits (frame)

/-- Every actual data stack has at most original width plus executed pushes. -/
theorem prefix_data_bound (bits:List Bool) (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial bits)=some out) :
    ∀k,(out.data k).length≤bits.length+fuel := by
  apply SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ out ?_ hr
  intro k
  cases k with
  | inl k => cases k <;> simp [initial,input,Meta.input]
  | inr bit => cases bit <;> simp [initial,input]

/-- Pure scalar substitution independent of executable projection contexts. -/
theorem numeric_space (n fuel cells frames time:ℕ)
    (hc:cells≤13*(n+fuel)) (hf:frames≤fuel) (ht:fuel≤time)
    (hb:time≤200000*(n+1)^2) : cells+frames≤3000000*(n+1)^2 := by
  nlinarith

/-- All thirteen Boolean stacks and the real return stack are included. -/
theorem machine_space (bits:List Bool) (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun cfg=>cfg.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (cfg.stk (some (.inl .input))).length+(cfg.stk (some (.inl .width))).length+(cfg.stk (some (.inl .nonzero))).length+(cfg.stk (some (.inl .threshold))).length+(cfg.stk (some (.inl .radius))).length+(cfg.stk (some (.inl .square))).length+(cfg.stk (some (.inl .exponent))).length+(cfg.stk (some (.inl .squareWork))).length+(cfg.stk (some (.inl .thresholdWork))).length+(cfg.stk (some (.inl .temporary))).length+(cfg.stk (some (.inl .radix))).length+(cfg.stk (some (.inr false))).length+(cfg.stk (some (.inr true))).length+(cfg.stk none).length≤3000000*(bits.length+1)^2 := by
  rw [initial_eq] at hr
  let state:=initial bits
  change (fun cfg=>cfg.bind machine.step)^[fuel]
    (some (SemiprimeD1StackCalls.configuration state))=some cfg at hr
  have he:=SemiprimeD1StackCalls.run_correct (.inl .input) (.inr false) (.inl .start) program fuel state
  change (C.run program fuel state).map SemiprimeD1StackCalls.configuration=
    (fun cfg=>cfg.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration state)) at he
  cases hc:C.run program fuel state with
  | none => rw [hc,hr] at he;cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj he
    rw [←hcfg]
    have hbound:=prefix_data_bound bits fuel out hc
    have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel state out hc
    have htime:fuel≤totalTime bits.length:=by
      by_contra hn
      have ht:fuel=totalTime bits.length+((fuel-totalTime bits.length-1)+1):=by omega
      rw [ht,SemiprimeD1StackReturnLink.run_add,acquire_run bits,Option.bind_some] at hc
      have hh:C.run program ((fuel-totalTime bits.length-1)+1) (done bits)=none:=by
        unfold C.run
        rw [Function.iterate_succ_apply]
        have hs:C.step program (done bits)=none:=by
          simp [C.step,SemiprimeD1StackCalls.step,done]
        simp only [Option.bind_some,hs]
        exact Function.iterate_fixed rfl _
      rw [hh] at hc;cases hc
    have h0:=hbound (.inl .input)
    have h1:=hbound (.inl .width)
    have h2:=hbound (.inl .nonzero)
    have h3:=hbound (.inl .threshold)
    have h4:=hbound (.inl .radius)
    have h5:=hbound (.inl .square)
    have h6:=hbound (.inl .exponent)
    have h7:=hbound (.inl .squareWork)
    have h8:=hbound (.inl .thresholdWork)
    have h9:=hbound (.inl .temporary)
    have h10:=hbound (.inl .radix)
    have h11:=hbound (.inr false)
    have h12:=hbound (.inr true)
    change out.frames.length≤0+fuel at hf
    have hs:(out.data (.inl .input)).length+(out.data (.inl .width)).length+(out.data (.inl .nonzero)).length+(out.data (.inl .threshold)).length+(out.data (.inl .radius)).length+(out.data (.inl .square)).length+(out.data (.inl .exponent)).length+(out.data (.inl .squareWork)).length+(out.data (.inl .thresholdWork)).length+(out.data (.inl .temporary)).length+(out.data (.inl .radix)).length+(out.data (.inr false)).length+(out.data (.inr true)).length≤13*(bits.length+fuel):=by omega
    change (out.data (.inl .input)).length+(out.data (.inl .width)).length+(out.data (.inl .nonzero)).length+(out.data (.inl .threshold)).length+(out.data (.inl .radius)).length+(out.data (.inl .square)).length+(out.data (.inl .exponent)).length+(out.data (.inl .squareWork)).length+(out.data (.inl .thresholdWork)).length+(out.data (.inl .temporary)).length+(out.data (.inl .radix)).length+(out.data (.inr false)).length+(out.data (.inr true)).length+out.frames.length≤_
    exact numeric_space bits.length fuel _ _ _ hs (by simpa only [Nat.zero_add] using hf) htime (totalTime_le bits.length)

/-- The original binary input and actual nonzero flag remain physically retained. -/
theorem retained (bits:List Bool) :
    result bits (.inl .input)=bits ∧
      result bits (.inl .nonzero)=[SemiprimeD1BinaryBootstrap.seenOne bits] := by
  exact ⟨rfl,rfl⟩

/-- Exact one-side finite index order; every original record and duplicate is retained. -/
theorem catalogue_fin (side:Bool) (n:ℕ) (tail:List Bool) :
    catalogue side n tail=(SemiprimeFiniteEnumerations.fin n).values.foldr
      (fun i rest=>record side (List.replicate i.val true) rest) tail := by
  rw [catalogue_range,←SemiprimeD1StackGraphIndicesBounds.fin_values]
  simp only [List.foldr_map]

/-- The whole emitted family is the actual original Cartesian Fin2×FinR order. -/
theorem catalogue_product (R:ℕ) (tail:List Bool) :
    catalogue false R (catalogue true R tail)=
      (SemiprimeFiniteEnumerations.prod (SemiprimeFiniteEnumerations.fin 2)
        (SemiprimeFiniteEnumerations.fin R)).values.foldr
        (fun v rest=>record (decide (v.1.val=1)) (List.replicate v.2.val true) rest) tail := by
  have ht:(SemiprimeFiniteEnumerations.fin 2).values=[0,1]:=rfl
  change _=((SemiprimeFiniteEnumerations.fin 2).values.product
    (SemiprimeFiniteEnumerations.fin R).values).foldr _ tail
  rw [ht]
  simp only [List.product,List.flatMap_cons,List.flatMap_nil,List.foldr_append,List.foldr_map,List.append_nil]
  change _=(SemiprimeFiniteEnumerations.fin R).values.foldr
    (fun i rest=>record false (List.replicate i.val true) rest)
    ((SemiprimeFiniteEnumerations.fin R).values.foldr (fun i rest=>record true (List.replicate i.val true) rest) tail)
  rw [←catalogue_fin,←catalogue_fin]

/-- The actual typed original input-vertex Cartesian family, not a supplied label list. -/
def inputFamily (r t digits:ℕ) : List (SemiprimeMacroGraph.Vertex r t digits) :=
  (SemiprimeFiniteEnumerations.prod (SemiprimeFiniteEnumerations.fin 2)
    (SemiprimeFiniteEnumerations.fin (r*t))).values.map (fun v=>.input v.1 v.2)
/-- Mathematical descriptor specification for input vertices only; never a runtime callback. -/
def encodeInputVertex {r t digits:ℕ} (v:SemiprimeMacroGraph.Vertex r t digits) (tail:List Bool) : List Bool :=
  match v with
  | .input side i => record (decide (side.val=1)) (List.replicate i.val true) tail
  | _ => tail

/-- Exact original constructor prefix: the new family is the input block of original vertices. -/
theorem input_family_prefix (r t digits:ℕ) :
    ∃rest,(SemiprimeMacroFiniteEnumerations.vertices r t digits).values=inputFamily r t digits++rest := by
  unfold SemiprimeMacroFiniteEnumerations.vertices
  simp only [SemiprimeFiniteEnumerations.transport,SemiprimeFiniteEnumerations.sum,List.map_append,List.map_map]
  have hf:(SemiprimeFiniteEnumerations.prod (SemiprimeFiniteEnumerations.fin 2)
      (SemiprimeFiniteEnumerations.fin (r*t))).values.map
      (SemiprimeMacroFiniteEnumerations.verticesEquiv r t digits ∘ Sum.inl)=inputFamily r t digits:=by
    apply List.map_congr_left
    intro v _
    rcases v with ⟨side,i⟩
    rfl
  rw [hf]
  exact ⟨_,rfl⟩

/-- Exact input-family size is derived from the original constructor list. -/
theorem input_family_length (r t digits:ℕ) : (inputFamily r t digits).length=2*(r*t) := by
  simp [inputFamily]

/-- The same acquired family is the arithmetic-input prefix of the COMPLETE subdivided vertex list. -/
theorem subdivided_input_prefix (r t digits:ℕ) :
    ∃rest,(SemiprimeMacroFiniteEnumerations.subdividedVertices r t digits).values=
      (inputFamily r t digits).map Sum.inl++rest := by
  obtain ⟨rest,hr⟩:=input_family_prefix r t digits
  change ∃tail,(SemiprimeMacroFiniteEnumerations.vertices r t digits).values.map Sum.inl++
    (SemiprimeMacroFiniteEnumerations.bits r t digits).values.map Sum.inr=
    (inputFamily r t digits).map Sum.inl++tail
  rw [hr,List.map_append,List.append_assoc]
  exact ⟨_,rfl⟩

/-- Actual output allocation counts every finite constructor/side field and index byte. -/
theorem output_length (bits:List Bool) :
    (result bits (.inr false)).length=2*(transformLength bits.length)^2+12*transformLength bits.length := by
  change (catalogue false (transformLength bits.length) (catalogue true (transformLength bits.length) [])).length=_
  rw [catalogue_length,catalogue_length]
  simp only [List.length_nil]
  ring

/-- The whole N-only output is exactly the physically encoded ORIGINAL input-vertex block. -/
theorem original_input_vertices (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    let ell:=bitLength (bitValue bits)
    result bits (.inr false)=(inputFamily (firstAxis ell) (secondAxis ell) (digitCount ell)).foldr encodeInputVertex [] := by
  have hw:bits.length=bitLength (bitValue bits):=SemiprimeD1BinaryBootstrap.canonical_width bits hc
  change catalogue false (transformLength bits.length) (catalogue true (transformLength bits.length) [])=_
  rw [hw,←axes_product,catalogue_product]
  simp only [inputFamily,List.foldr_map,encodeInputVertex]

/-- Canonical original input ties physical width to the public bitLength. -/
def originalInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits)))
      (200000*(bitLength (bitValue bits)+1)^2) := by
  have hw:=SemiprimeD1BinaryBootstrap.canonical_width bits hc
  simpa only [hw,bitLength] using acquireInTime bits
end RiemannGaussian.SemiprimeD1StackInputVerticesBounds
