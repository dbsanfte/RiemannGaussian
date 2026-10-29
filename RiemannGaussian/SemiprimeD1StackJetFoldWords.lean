/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFold
import RiemannGaussian.SemiprimeD1RecursiveCounter
/-! # Literal fold bytes and exact native right-fold order
All values in this file are proof notation for physical Boolean tapes. The
source executes only the fixed controller and actual linked arithmetic code.
No canonical-word or associativity premise is needed to identify either fold.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackJetFoldWords
open SemiprimeD1JetAxes (Context)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Coefficient words remain arbitrary binary Boolean words. -/
abbrev Jet:=List (List Bool)
/-- One actual ordered group of child-result vectors. -/
abbrev Group:=List Jet
/-- Actual mode-major ordered groups of child-result vectors. -/
abbrev Modes:=List Group
/-- Physical child-result vector, with every padded coefficient bit retained. -/
def jetTape (jet:Jet):List Bool:=vectorBits jet
/-- Physical vector of actual child-result vectors for one mode. -/
def groupTape (children:Group):List Bool:=vectorBits (children.map jetTape)
/-- Physical mode-major vector of child-result groups. -/
def modeTape (modes:Modes):List Bool:=vectorBits (modes.map groupTape)
/-- Exact native-order product, stated on literal binary words only. -/
def productWords (ctx:Context):Group→Jet
  | []=>(SemiprimeD1JetAffineCoefficient.one ctx).words
  | x::xs=>(SemiprimeD1JetRingBits.mul ctx x (productWords ctx xs)).words
/-- Exact native-order sum of mode products, stated on literal binary words only. -/
def sumWords (ctx:Context):Modes→Jet
  | []=>(SemiprimeD1JetAffineCoefficient.zero ctx).words
  | x::xs=>(SemiprimeD1JetRingBits.add ctx (productWords ctx x) (sumWords ctx xs)).words
/-- Literal native product order agrees even for noncanonical and padded child words. -/
theorem product_native (ctx:Context) (runs:List SemiprimeD1JetAffineCoefficient.JetRun):
    productWords ctx (runs.map (fun r=>r.words))=(SemiprimeD1RecursiveCounter.product ctx runs).words:=by
  induction runs with
  | nil=>rfl
  | cons r rs ih=>simp only [List.map_cons,productWords,SemiprimeD1RecursiveCounter.product,ih]
/-- Literal native mode sum order agrees without rearranging or recoding any input word. -/
theorem sum_native (ctx:Context) (runs:List (List SemiprimeD1JetAffineCoefficient.JetRun)):
    sumWords ctx (runs.map (fun row=>row.map (fun r=>r.words)))=
      (SemiprimeD1JetAffineCoefficient.sumRuns ctx (runs.map (SemiprimeD1RecursiveCounter.product ctx))).words:=by
  induction runs with
  | nil=>rfl
  | cons r rs ih=>simp only [List.map_cons,sumWords,SemiprimeD1JetAffineCoefficient.sumRuns,product_native,ih]
/-- Acquired dense outputs have exact rank and every coefficient fits actual precision. -/
def Dense (ctx:Context) (jet:Jet):Prop:=jet.length=ctx.rank ∧∀word∈jet,word.length ≤ctx.precision
/-- The actual scalar-one producer has bounded binary width even at precision zero. -/
theorem one_dense (ctx:Context):Dense ctx (SemiprimeD1JetAffineCoefficient.one ctx).words:=by
  constructor
  · simp only [SemiprimeD1JetAffineCoefficient.one,List.length_map,List.length_range]
  · intro word hw
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp hw
    split_ifs
    · exact SemiprimeD1JetScalarBits.reduce_length _ _
    · exact Nat.zero_le _
/-- Dense zero cells are allocated by real arithmetic in the source. -/
theorem zero_dense (ctx:Context):Dense ctx (SemiprimeD1JetAffineCoefficient.zero ctx).words:=by
  constructor
  · exact List.length_replicate
  · intro word hw
    have he:word=[]:=List.eq_of_mem_replicate hw
    rw [he,List.length_nil]
    exact Nat.zero_le _
/-- Every actual complete multiplication derives output shape and binary coefficient width internally. -/
theorem mul_dense (ctx:Context) (a b:Jet):Dense ctx (SemiprimeD1JetRingBits.mul ctx a b).words:=by
  constructor
  · exact SemiprimeD1JetRingBits.mul_shape _ _ _
  · intro word hw
    simp only [SemiprimeD1JetRingBits.mul,List.map_map,Function.comp_def] at hw
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp hw
    exact SemiprimeD1JetRingBits.mulAt_length _ _ _ _
/-- Every actual complete addition derives output shape and binary coefficient width internally. -/
theorem add_dense (ctx:Context) (a b:Jet):Dense ctx (SemiprimeD1JetRingBits.add ctx a b).words:=by
  constructor
  · exact SemiprimeD1JetRingBits.add_shape _ _ _
  · intro word hw
    simp only [SemiprimeD1JetRingBits.add,List.map_map,Function.comp_def] at hw
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp hw
    exact SemiprimeD1JetRingBits.addAt_length _ _ _ _
/-- The literal right product has internally bounded output regardless of input padding. -/
theorem product_dense (ctx:Context) (children:Group):Dense ctx (productWords ctx children):=by
  cases children with
  | nil=>exact one_dense ctx
  | cons x xs=>exact mul_dense ctx x (productWords ctx xs)
/-- The literal right mode sum has internally bounded output regardless of input padding. -/
theorem sum_dense (ctx:Context) (modes:Modes):Dense ctx (sumWords ctx modes):=by
  cases modes with
  | nil=>exact zero_dense ctx
  | cons x xs=>exact add_dense ctx (productWords ctx x) (sumWords ctx xs)
/-- Actual framed dense-output byte cap, not a supplied result-size answer. -/
def denseBytes (ctx:Context):Nat:=2*ctx.rank*ctx.precision+2*ctx.rank+1
/-- Every actual coefficient bit is paid by the derived per-coordinate width bound. -/
theorem sum_lengths_le (jet:Jet) (p:Nat) (hbound:∀word∈jet,word.length ≤p):
    (jet.map List.length).sum ≤jet.length*p:=by
  induction jet with
  | nil=>simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons word jet ih=>
    have hw:=hbound word (by simp)
    have ht:=ih (fun w hw=>hbound w (by simp [hw]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [hw,ht]
/-- Every serialized dense arithmetic output fits its derived physical byte cap. -/
theorem dense_tape_length (ctx:Context) (jet:Jet) (h:Dense ctx jet):
    (jetTape jet).length ≤denseBytes ctx:=by
  have hs:=sum_lengths_le jet ctx.precision h.2
  unfold jetTape denseBytes
  rw [SemiprimeD1TensorTapeCodec.vectorBits_length,h.1]
  rw [h.1] at hs
  nlinarith only [hs]
end RiemannGaussian.SemiprimeD1StackJetFoldWords
