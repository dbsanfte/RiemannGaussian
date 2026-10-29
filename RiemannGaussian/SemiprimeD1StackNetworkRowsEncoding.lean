/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkRows
/-! # Exact nested owner-row codec and original incidence-order interpretation
All native lists/owners below specify physically acquired bytes. No getter,
lookup, arity, row, function or enumeration is an executed source operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkRowsEncoding
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace Owner
export SemiprimeD1StackNetworkOwnerIndexEncoding (ownerWord ownerWord_length ownerWord_value)
end Owner
/-- Actual one-vector-field bytes, before the list's single final false terminator. -/
def chunk (word:List Bool) :List Bool :=true::frame word []
/-- Chronological actual field bytes, before the final false vector terminator. -/
def payload (words:List (List Bool)) :List Bool :=words.foldr (fun word tail=>chunk word++tail) []
/-- Literal nested output ABI: one physical vector word per original factor, including empty rows. -/
def rowsTape (rows:List (List (List Bool))) :List Bool :=vectorBits (rows.map vectorBits)
/-- Actual framing preserves an arbitrary following vector/record suffix. -/
theorem chunk_append (word tail:List Bool) :chunk word++tail=true::frame word tail :=by
  unfold chunk
  rw [List.cons_append,SemiprimeD1TensorTapeCodec.frame_append,List.nil_append]
/-- Literal payload concatenation preserves row and local-slot order exactly. -/
theorem payload_append (xs ys:List (List Bool)) :payload (xs++ys)=payload xs++payload ys :=by
  induction xs with
  | nil=>rfl
  | cons word xs ih=>
    change chunk word++payload (xs++ys)=(chunk word++payload xs)++payload ys
    rw [ih,List.append_assoc]
/-- One real terminating false push and reverse completes the existing vector codec. -/
theorem payload_vector (words:List (List Bool)) :payload words++[false]=vectorBits words :=by
  induction words with
  | nil=>rfl
  | cons word words ih=>
    change (chunk word++payload words)++[false]=_
    rw [List.append_assoc,ih,chunk_append]
    rfl
/-- Every actual framed field includes both tag and delimiter. -/
theorem chunk_length (word:List Bool) :(chunk word).length=2*word.length+2 :=by
  simp only [chunk,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
/-- Exact bytes of a variable-width actual binary-owner vector. -/
theorem vector_length (words:List (List Bool)) :
    (vectorBits words).length=2*(words.map List.length).sum+2*words.length+1 :=
  SemiprimeD1StackNetworkOwnerIndexPorts.vector_length words
/-- Exact bytes of the physically logged prefix, including each repeated owner occurrence. -/
theorem payload_length (words:List (List Bool)) :
    (payload words).length=2*(words.map List.length).sum+2*words.length :=by
  have h:=congrArg List.length (payload_vector words)
  rw [List.length_append,vector_length] at h
  simp only [List.length_cons,List.length_nil] at h
  omega
/-- Mathematical original owner word of one globally indexed occurrence; no such getter is executed. -/
def ownerAt (net:SemiprimeD1TensorNetwork.Network) (p:Nat) :List Bool :=
  if h:p<SemiprimeD1TensorNetwork.scope net.rows then
    Owner.ownerWord net.leftCount (SemiprimeD1TensorNetworkLayout.leftGroup net.rows ⟨p,h⟩).val else []
/-- Every actual original global port resolves by the REALindex's exact singleton source semantics. -/
theorem original_singleton (net:SemiprimeD1TensorNetwork.Network) (hw:SemiprimeD1TensorNetwork.WellFormed net)
    (p:Nat) (hp:p<SemiprimeD1TensorNetwork.scope net.rows) :
    SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p)
      (SemiprimeD1StackNetworkOwnerIndexExecution.pairs net.left.toList)=[ownerAt net p] :=by
  have h:=SemiprimeD1StackNetworkOwnerIndexOriginal.original_owner_fibre net hw ⟨p,hp⟩
  simpa only [ownerAt,hp,dite_eq_left] using h
/-- Actual returned binary owners retain their physically allocated n+1-bit width. -/
theorem ownerAt_length (net:SemiprimeD1TensorNetwork.Network) (p:Nat) (hp:p<SemiprimeD1TensorNetwork.scope net.rows) :
    (ownerAt net p).length=net.leftCount+1 :=by
  simp only [ownerAt,hp,dite_eq_left]
  exact Owner.ownerWord_length _ _ (Nat.le_of_lt (SemiprimeD1TensorNetworkLayout.leftGroup net.rows ⟨p,hp⟩).isLt)
/-- Mathematical expected original factor rows, retaining exact original port/local-slot order. -/
def resolvedRows (net:SemiprimeD1TensorNetwork.Network) :List (List (List Bool)) :=
  net.right.toList.map (fun v=>v.ports.map (ownerAt net))
/-- Original expected output ABI uses original literal owner rows, including repeated and zero-port factors. -/
def originalTape (net:SemiprimeD1TensorNetwork.Network) :List Bool :=
  rowsTape (net.rows.map (fun row=>row.map (fun v=>Owner.ownerWord net.leftCount v.val)))
end RiemannGaussian.SemiprimeD1StackNetworkRowsEncoding
