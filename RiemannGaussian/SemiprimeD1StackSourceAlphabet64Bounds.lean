/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Execution
/-! # Whole own clock from actual counter width and actual alphabet cardinality -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64Bounds
open SemiprimeD1StackSourceAlphabet64 SemiprimeD1StackSourceAlphabet64Encoding
open SemiprimeD1StackSourceAlphabet64Rows SemiprimeD1StackSourceAlphabet64Loop
open SemiprimeD1StackSourceAlphabet64Execution
/-- The radix64 cardinality is the honest binary-counter enumeration length. -/
theorem cardinality (a:Nat) :2^(6*a)=64^a :=by
  calc
    2^(6*a)=(2^6)^a:=by rw [pow_mul]
    _=64^a:=by norm_num
/-- Every raw fixed-width counter byte and every actual field/vector tag remains paid. -/
theorem vector_length (a:Nat) (ws:List (List Bool)) (hw:∀w∈ws,w.length=6*a) :
    (SemiprimeD1TensorTapeCodec.vectorBits ws).length=(12*a+2)*ws.length+1 :=by
  induction ws with
  | nil=>simp only [SemiprimeD1TensorTapeCodec.vectorBits,List.length_cons,List.length_nil,Nat.mul_zero,Nat.zero_add]
  | cons w ws ih=>
    have h0:=hw w List.mem_cons_self
    have h1:=ih (fun v hv=>hw v (List.mem_cons_of_mem _ hv))
    change (true::SemiprimeSourceHistogramKeyBits.frame w (SemiprimeD1TensorTapeCodec.vectorBits ws)).length=_
    rw [List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,h0,h1,List.length_cons]
    ring
/-- Every dictionary chunk includes its actual compact ID, complete row, both fields and pair tag. -/
theorem chunk_length (a:Nat) (word:List Bool) (hw:word.length=6*a) :
    (chunk a word).length ≤ 38*a+3 :=by
  have hi:(compact word).length ≤ 6*a:=(SemiprimeSourceCompactBits.trim_length word).trans_eq hw
  have hr:=row_length a word
  change (true::SemiprimeSourceHistogramKeyBits.frame (compact word)
    (SemiprimeSourceHistogramKeyBits.frame (row a word) [])).length ≤ _
  rw [List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
  omega
/-- Full chronological log length is derived internally from all actual framed fields. -/
theorem stream_length (a:Nat) (ws:List (List Bool)) (hw:∀w∈ws,w.length=6*a) :
    (stream a ws).length ≤ (38*a+3)*ws.length :=by
  induction ws with
  | nil=>rfl
  | cons w ws ih=>
    have h0:=chunk_length a w (hw w List.mem_cons_self)
    have h1:=ih (fun v hv=>hw v (List.mem_cons_of_mem _ hv))
    change (chunk a w++stream a ws).length ≤ _
    rw [List.length_append,List.length_cons]
    nlinarith only [h0,h1]
/-- Whole SAME physical acquisition is linear in actual width times alphabet cardinality.
This concerns alphabet construction only; no old near-linear selector-query claim is made. -/
theorem runBound_le (a:Nat) :runBound a ≤ 10000*(a+1)*(64^a+1) :=by
  let L:Nat:=64^a
  let B:Nat:=(a+1)*(L+1)
  have hB:1 ≤ B:=Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos L)
  have ha:a+1 ≤ B:=Nat.le_mul_of_pos_right _ (Nat.succ_pos L)
  have hL:(a+1)*L ≤ B:=Nat.mul_le_mul_left _ (Nat.le_succ L)
  have hv:=vector_length a (words a) (word_width a)
  rw [words_length] at hv
  have hs:=stream_length a (words a) (word_width a)
  rw [words_length] at hs
  have hi:(SemiprimeD1TensorTapeCodec.vectorBits (words a)).length ≤ 14*B+1:=by
    have hm:(12*a+2)*L ≤ (14*(a+1))*L:=Nat.mul_le_mul_right _ (by omega)
    have he:(14*(a+1))*L=14*((a+1)*L):=by ring
    rw [he] at hm
    have hn:=hm.trans (Nat.mul_le_mul_left 14 hL)
    change _=(12*a+2)*L+1 at hv
    omega
  have hstream:(stream a (words a)).length ≤ 41*B:=by
    have hm:(38*a+3)*L ≤ (41*(a+1))*L:=Nat.mul_le_mul_right _ (by omega)
    have he:(41*(a+1))*L=41*((a+1)*L):=by ring
    rw [he] at hm
    exact hs.trans (hm.trans (Nat.mul_le_mul_left 41 hL))
  have henum:100*(6*a+1)*L ≤ 700*B:=by
    have hm:(6*a+1)*L ≤ (7*(a+1))*L:=Nat.mul_le_mul_right _ (by omega)
    have he:(7*(a+1))*L=7*((a+1)*L):=by ring
    rw [he] at hm
    have hh:=Nat.mul_le_mul_left 100 (hm.trans (Nat.mul_le_mul_left 7 hL))
    nlinarith only [hh]
  have hrows:2000*(a+1)*L ≤ 2000*B:=by
    have h:=Nat.mul_le_mul_left 2000 hL
    simpa only [Nat.mul_assoc] using h
  unfold runBound
  rw [cardinality,words_length]
  rw [show 10000*(a+1)*(64^a+1)=10000*B by dsimp only [B,L];ring]
  change 95*a+100*(6*a+1)*L+21+5*(SemiprimeD1TensorTapeCodec.vectorBits (words a)).length+4+
    (2000*(a+1)*L+1)+2*(stream a (words a)).length+4+1 ≤ 10000*B
  change 100*(6*a+1)*L ≤ _ at henum
  change 2000*(a+1)*L ≤ _ at hrows
  omega
/-- Real complete source from unary markers only, with no candidate or power advice. -/
theorem source_run_bounded (a:Nat) :
    ∃q ≤ 10000*(a+1)*(64^a+1),SemiprimeD1StackCalls.run program q
      (initial (List.replicate a true))=some (done a) :=by
  obtain ⟨q,hq,hr⟩:=source_run a
  exact ⟨q,hq.trans (runBound_le a),hr⟩
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64Bounds
