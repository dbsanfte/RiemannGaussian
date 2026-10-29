/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTables
import RiemannGaussian.SemiprimeSourceHistogramKeyBits

/-! # Sequential tensor-table tape codec
Actual coefficient words are framed without numeric decoding. Both tree branches
are serialized. Vector parsing scans tags and copies every encountered word.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1TensorTapeCodec
open SemiprimeD1TensorTables SemiprimeSourceHistogramKeyBits

/-- Literal copied concatenation with its cell traversal report. -/
def appendBits : List Bool → List Bool → SemiprimeSourceCompactBits.Report
  | [],ys => ⟨ys,1⟩
  | b::bs,ys => let out:=appendBits bs ys; ⟨b::out.bits,out.clock+3⟩

/-- Actual concatenation copies exactly its first input. -/
theorem appendBits_bits (xs ys : List Bool) : (appendBits xs ys).bits=xs++ys := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [appendBits,List.cons_append,ih]

/-- Every copied concatenation cell is charged. -/
theorem appendBits_clock (xs ys : List Bool) : (appendBits xs ys).clock=3*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [appendBits,List.length_cons,ih];omega

/-- A complete literal coefficient vector, including an explicit end marker. -/
def vectorBits : List (List Bool) → List Bool
  | [] => [false]
  | w::ws => true::frame w (vectorBits ws)

/-- Execute every coefficient-field framing and vector constructor. -/
def encodeVector : List (List Bool) → SemiprimeSourceCompactBits.Report
  | [] => ⟨[false],2⟩
  | w::ws => let tail:=encodeVector ws; let field:=pair w tail.bits
             ⟨true::field.bits,tail.clock+field.clock+3⟩

/-- The vector serializer preserves all literal words, including padding. -/
theorem encodeVector_bits (ws : List (List Bool)) : (encodeVector ws).bits=vectorBits ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [encodeVector,pair_bits,vectorBits,ih]

/-- Actual serialized vector length. -/
theorem vectorBits_length (ws : List (List Bool)) :
    (vectorBits ws).length=2*(ws.map List.length).sum+2*ws.length+1 := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [vectorBits,List.length_cons,frame_length,List.map_cons,List.sum_cons,ih];omega

/-- Vector setup work is linear in its actual serialized length. -/
theorem encodeVector_clock (ws : List (List Bool)) :
    (encodeVector ws).clock ≤ 4*(vectorBits ws).length := by
  induction ws with
  | nil => decide
  | cons w ws ih =>
    simp only [encodeVector,pair_clock,vectorBits,List.length_cons,frame_length]
    omega

/-- A field parser never advances past the actual input tail. -/
theorem split_rest_length (xs : List Bool) : (split xs).rest.length ≤ xs.length := by
  induction xs using split.induct with
  | case1 => simp [split]
  | case2 ys => simp [split]
  | case3 => simp [split]
  | case4 b bs ih => simp only [split,List.length_cons];omega

/-- Parsed vector, remaining tape and all copied/scanned cell reports. -/
structure Parsed where
  /-- Actual reconstructed coefficient vector. -/
  words : List (List Bool)
  /-- Actual unconsumed tape suffix. -/
  rest : List Bool
  /-- All field tests, copies and recursion controls. -/
  clock : ℕ

/-- Sequential self-delimiting vector parser; malformed EOF yields empty output. -/
def parseVector (xs : List Bool) : Parsed :=
  match xs with
  | [] => ⟨[],[],2⟩
  | false::tail => ⟨[],tail,3⟩
  | true::tail =>
    let field:=split tail
    let out:=parseVector field.rest
    ⟨field.first::out.words,out.rest,field.clock+out.clock+4⟩
termination_by xs.length
decreasing_by
  have h:=split_rest_length tail
  simp_wf
  omega

/-- Framing a first field commutes with attaching a literal tail. -/
theorem frame_append (w xs ys : List Bool) : frame w xs++ys=frame w (xs++ys) := by
  induction w with
  | nil => rfl
  | cons b bs ih => simp only [frame,List.cons_append,ih]

/-- Parsing an encoded vector recovers every bit and the exact following tape. -/
theorem parseVector_correct (ws : List (List Bool)) (tail : List Bool) :
    (parseVector (vectorBits ws++tail)).words=ws ∧
      (parseVector (vectorBits ws++tail)).rest=tail := by
  induction ws with
  | nil => simp [vectorBits,parseVector]
  | cons w ws ih =>
    simp only [vectorBits,List.cons_append,frame_append,parseVector]
    rw [(split_frame w (vectorBits ws++tail)).2.1]
    simp only [(split_frame w (vectorBits ws++tail)).1,ih.1,ih.2,and_self]

/-- Every encountered vector field is scanned and copied at linear tape cost. -/
theorem parseVector_clock (ws : List (List Bool)) (tail : List Bool) :
    (parseVector (vectorBits ws++tail)).clock ≤ 4*(vectorBits ws).length := by
  induction ws with
  | nil => simp [vectorBits,parseVector]
  | cons w ws ih =>
    simp only [vectorBits,List.cons_append,frame_append,parseVector]
    rw [(split_frame w (vectorBits ws++tail)).2.1,split_frame_clock]
    simp only [List.length_cons,frame_length]
    omega

/-- Prefix-free tagged tree layout containing every literal coefficient bit. -/
def tape : {n : ℕ} → Table n → List Bool
  | _,.leaf words => false::vectorBits words
  | _,.fork low high => true::(tape low++tape high)

/-- Execute serialization with all subtree concatenation copies retained. -/
def serialize : {n : ℕ} → Table n → SemiprimeSourceCompactBits.Report
  | _,.leaf words => let out:=encodeVector words; ⟨false::out.bits,out.clock+3⟩
  | _,.fork low high =>
    let lo:=serialize low
    let hi:=serialize high
    let joined:=appendBits lo.bits hi.bits
    ⟨true::joined.bits,lo.clock+hi.clock+joined.clock+4⟩

/-- Executed tree serialization is the exact tagged tape. -/
theorem serialize_bits {n : ℕ} (table : Table n) : (serialize table).bits=tape table := by
  induction table with
  | leaf words => simp only [serialize,tape,encodeVector_bits]
  | fork low high ihl ihh => simp only [serialize,tape,appendBits_bits,ihl,ihh]

/-- Serializer copies are bounded by actual tape length times tree depth. -/
theorem serialize_clock {n : ℕ} (table : Table n) :
    (serialize table).clock ≤ 8*(n+1)*(tape table).length := by
  induction table with
  | leaf words =>
    have h:=encodeVector_clock words
    simp only [serialize,tape,List.length_cons]
    omega
  | @fork n low high ihl ihh =>
    have ha:=appendBits_clock (serialize low).bits (serialize high).bits
    rw [serialize_bits,serialize_bits] at ha
    simp only [serialize,tape,serialize_bits,List.length_cons,List.length_append]
    nlinarith

/-- All literal coefficient-word lengths have the expected finite sum bound. -/
theorem word_lengths_le (words : List (List Bool)) (P : ℕ)
    (hw : ∀w∈words,w.length ≤ P) : (words.map List.length).sum ≤ words.length*P := by
  induction words with
  | nil => simp
  | cons w ws ih =>
    have hh:=hw w (by simp)
    have ht:=ih (fun x hx => hw x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- Actual canonical input shape gives a full serialized-storage bound. -/
theorem tape_length (ctx : SemiprimeD1JetAxes.Context) {n : ℕ} (table : Table n)
    (hg : Good ctx table) :
    (tape table).length+1 ≤ (2*ctx.rank*(ctx.precision+1)+3)*2^n := by
  induction table with
  | leaf words =>
    have h:=word_lengths_le words ctx.precision (fun w hw => (hg.2 w hw).2)
    simp only [tape,List.length_cons,vectorBits_length,pow_zero,Nat.mul_one]
    rw [hg.1] at h ⊢
    nlinarith
  | @fork n low high ihl ihh =>
    have hl:=ihl hg.1
    have hh:=ihh hg.2
    simp only [tape,List.length_cons,List.length_append,pow_succ]
    nlinarith

/-- Serialized bits fit the literal table's existing copied-cell inventory. -/
theorem tape_le_storage {n : ℕ} (table : Table n) :
    (tape table).length ≤ storage table := by
  induction table with
  | leaf words =>
    simp only [tape,List.length_cons,vectorBits_length,storage,SemiprimeD1JetAxes.copyVector_clock]
    omega
  | fork low high ihl ihh =>
    simp only [tape,List.length_cons,List.length_append,storage]
    omega

end RiemannGaussian.SemiprimeD1TensorTapeCodec
