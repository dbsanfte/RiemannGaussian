/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetAdd

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackJetAddExecution
open SemiprimeD1StackJetAdd SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Actual source trace composition. -/
theorem run_append (m n : ℕ) (a b c : C.State Stack Label)
    (hm : C.run program m a=some b) (hn : C.run program n b=some c) : C.run program (m+n) a=some c := by
  rw [SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,hn]

/-- Two literal actual transitions. -/
theorem two_steps (a b c : C.State Stack Label)
    (h₁ : C.step program a=some b) (h₂ : C.step program b=some c) : C.run program 2 a=some c := by
  change (C.step program a).bind (C.step program)=some c
  rw [h₁,Option.bind_some,h₂]

/-- Three literal actual transitions. -/
theorem three_steps (a b c d : C.State Stack Label)
    (h₁ : C.step program a=some b) (h₂ : C.step program b=some c) (h₃ : C.step program c=some d) : C.run program 3 a=some d := by
  change ((C.step program a).bind (C.step program)).bind (C.step program)=some d
  rw [h₁,Option.bind_some,h₂,Option.bind_some,h₃]

/-- Exact literal write to the left stack. -/
theorem store_left (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy bits : List Bool) :
    Function.update (store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy) (.inl (.inl .left)) bits=store bits right scratch scalar precision scalarWork a b rank active rev output valid parser copy := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_left (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) : store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy (.inl (.inl .left))=left := rfl

/-- Exact literal write to the right stack. -/
theorem store_right (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy bits : List Bool) :
    Function.update (store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy) (.inl (.inl .right)) bits=store left bits scratch scalar precision scalarWork a b rank active rev output valid parser copy := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_right (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) : store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy (.inl (.inl .right))=right := rfl

/-- Exact literal write to the scratch stack. -/
theorem store_scratch (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy bits : List Bool) :
    Function.update (store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy) (.inl (.inl .scratch)) bits=store left right bits scalar precision scalarWork a b rank active rev output valid parser copy := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_scratch (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) : store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy (.inl (.inl .scratch))=scratch := rfl

/-- Exact literal write to the scalar stack. -/
theorem store_scalar (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy bits : List Bool) :
    Function.update (store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy) (.inl (.inl .output)) bits=store left right scratch bits precision scalarWork a b rank active rev output valid parser copy := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_scalar (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) : store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy (.inl (.inl .output))=scalar := rfl

/-- Exact literal write to the precision stack. -/
theorem store_precision (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy bits : List Bool) :
    Function.update (store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy) (.inl (.inr false)) bits=store left right scratch scalar bits scalarWork a b rank active rev output valid parser copy := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_precision (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) : store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy (.inl (.inr false))=precision := rfl

/-- Exact literal write to the scalarWork stack. -/
theorem store_scalarWork (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy bits : List Bool) :
    Function.update (store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy) (.inl (.inr true)) bits=store left right scratch scalar precision bits a b rank active rev output valid parser copy := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_scalarWork (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) : store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy (.inl (.inr true))=scalarWork := rfl

/-- Exact literal write to the a stack. -/
theorem store_a (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy bits : List Bool) :
    Function.update (store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy) (.inr .leftTape) bits=store left right scratch scalar precision scalarWork bits b rank active rev output valid parser copy := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_a (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) : store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy (.inr .leftTape)=a := rfl

/-- Exact literal write to the b stack. -/
theorem store_b (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy bits : List Bool) :
    Function.update (store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy) (.inr .rightTape) bits=store left right scratch scalar precision scalarWork a bits rank active rev output valid parser copy := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_b (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) : store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy (.inr .rightTape)=b := rfl

/-- Exact literal write to the rank stack. -/
theorem store_rank (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy bits : List Bool) :
    Function.update (store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy) (.inr .rank) bits=store left right scratch scalar precision scalarWork a b bits active rev output valid parser copy := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_rank (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) : store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy (.inr .rank)=rank := rfl

/-- Exact literal write to the active stack. -/
theorem store_active (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy bits : List Bool) :
    Function.update (store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy) (.inr .active) bits=store left right scratch scalar precision scalarWork a b rank bits rev output valid parser copy := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_active (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) : store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy (.inr .active)=active := rfl

/-- Exact literal write to the rev stack. -/
theorem store_rev (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy bits : List Bool) :
    Function.update (store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy) (.inr .reverseOut) bits=store left right scratch scalar precision scalarWork a b rank active bits output valid parser copy := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_rev (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) : store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy (.inr .reverseOut)=rev := rfl

/-- Exact literal write to the output stack. -/
theorem store_output (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy bits : List Bool) :
    Function.update (store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy) (.inr .output) bits=store left right scratch scalar precision scalarWork a b rank active rev bits valid parser copy := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_output (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) : store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy (.inr .output)=output := rfl

/-- Exact literal write to the valid stack. -/
theorem store_valid (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy bits : List Bool) :
    Function.update (store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy) (.inr .valid) bits=store left right scratch scalar precision scalarWork a b rank active rev output bits parser copy := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_valid (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) : store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy (.inr .valid)=valid := rfl

/-- Exact literal write to the parser stack. -/
theorem store_parser (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy bits : List Bool) :
    Function.update (store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy) (.inr .parser) bits=store left right scratch scalar precision scalarWork a b rank active rev output valid bits copy := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_parser (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) : store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy (.inr .parser)=parser := rfl

/-- Exact literal write to the copy stack. -/
theorem store_copy (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy bits : List Bool) :
    Function.update (store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy) (.inr .copy) bits=store left right scratch scalar precision scalarWork a b rank active rev output valid parser bits := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
    · cases k <;> simp [store,SemiprimeD1StackJetScalarAdd.store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_copy (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) : store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy (.inr .copy)=copy := rfl

/-- Actual bitwise clearing of any unused input vector suffix. -/
theorem clear_left (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run program (a.length+1) (state (some .clearLeft) flag rt left right scratch scalar precision scalarWork a b rank active rev output valid parser copy)=
    some (state (some .clearRight) none rt left right scratch scalar precision scalarWork ([]) b rank active rev output valid parser copy) := by
  induction a generalizing flag with
  | nil => simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,program,store_a]
  | cons bit a ih =>
    have hs : C.run program 1 (state (some .clearLeft) flag rt left right scratch scalar precision scalarWork (bit::a) b rank active rev output valid parser copy)=
        some (state (some .clearLeft) (some bit) rt left right scratch scalar precision scalarWork (a) b rank active rev output valid parser copy) := by
      cases bit <;> simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,program,store_a]
    have hh:=run_append 1 (a.length+1) _ _ _ hs (ih (some bit))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Actual bitwise clearing of any unused input vector suffix. -/
theorem clear_right (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run program (b.length+1) (state (some .clearRight) flag rt left right scratch scalar precision scalarWork a b rank active rev output valid parser copy)=
    some (state (some .reverse) none rt left right scratch scalar precision scalarWork a ([]) rank active rev output valid parser copy) := by
  induction b generalizing flag with
  | nil => simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,program,store_b]
  | cons bit b ih =>
    have hs : C.run program 1 (state (some .clearRight) flag rt left right scratch scalar precision scalarWork a (bit::b) rank active rev output valid parser copy)=
        some (state (some .clearRight) (some bit) rt left right scratch scalar precision scalarWork a (b) rank active rev output valid parser copy) := by
      cases bit <;> simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,program,store_b]
    have hh:=run_append 1 (b.length+1) _ _ _ hs (ih (some bit))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Actual final reversal restores encoded coefficient order. -/
theorem reverse_run (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run program (2*rev.length+1) (state (some .reverse) flag rt left right scratch scalar precision scalarWork a b rank active rev output valid parser copy)=
    some (state (some .done) none rt left right scratch scalar precision scalarWork a b rank active ([]) (rev.reverse++output) valid parser copy) := by
  induction rev generalizing output flag with
  | nil => simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,program,store_rev]
  | cons bit rev ih =>
    have hs : C.run program 2 (state (some .reverse) flag rt left right scratch scalar precision scalarWork a b rank active (bit::rev) output valid parser copy)=
        some (state (some .reverse) (some bit) rt left right scratch scalar precision scalarWork a b rank active (rev) (bit::output) valid parser copy) := by
      apply two_steps (b:=state (some (.pushOutput bit)) (some bit) rt left right scratch scalar precision scalarWork a b rank active (rev) output valid parser copy)
      · cases bit <;> simp [C.step,C.execute,SemiprimeD1StackBytecode.choose,state,program,store_rev]
      · simp [C.step,C.execute,state,program,store_output]
    have hh:=run_append 2 (2*rev.length+1) _ _ _ hs (ih (bit::output) (some bit))
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,List.reverse_cons,List.append_assoc,
      List.singleton_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Clean-workspace boundary payload; vectors and all context remain actual stack data. -/
def P (left right scalar width a b rank active rev : List Bool) : Stack → List Bool :=
  store left right [] scalar width [] a b rank active rev [] [] [] []

/-- One physical writer iteration emits a continuation tag and the actual bit. -/
theorem emit_three (width a b rank active rev scalar : List Bool) (bit : Bool)
    (flag : Option Bool) (rt : Option Label) :
    C.run program 3 (state (some .emitWord) flag rt [] [] [] (bit::scalar) width [] a b rank active rev [] [] [] [])=
    some (state (some .emitWord) (some bit) rt [] [] [] scalar width [] a b rank active (bit::true::rev) [] [] [] []) := by
  apply three_steps
    (b:=state (some (.emitPrefix bit)) (some bit) rt [] [] [] scalar width [] a b rank active rev [] [] [] [])
    (c:=state (some (.emitData bit)) (some bit) rt [] [] [] scalar width [] a b rank active (true::rev) [] [] [] [])
  · cases bit <;> simp [C.step,C.execute,state,program,SemiprimeD1StackBytecode.choose,store_scalar]
  · simp [C.step,C.execute,state,program,store_rev]
  · simp [C.step,C.execute,state,program,store_rev]

/-- Every field bit and the terminating delimiter are actually emitted. -/
theorem emit_word_run (width a b rank active rev scalar : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run program (3*scalar.length+2)
      (state (some .emitWord) flag rt [] [] [] scalar width [] a b rank active rev [] [] [] [])=
    some (state (some .loop) none rt [] [] [] [] width [] a b rank active
      ((frame scalar []).reverse++rev) [] [] [] []) := by
  induction scalar generalizing rev flag with
  | nil =>
    apply two_steps (b:=state (some .endWord) none rt [] [] [] [] width [] a b rank active rev [] [] [] [])
    · simp [C.step,C.execute,state,program,SemiprimeD1StackBytecode.choose,store_scalar]
    · simp [C.step,C.execute,state,program,store_rev,frame]
  | cons bit scalar ih =>
    have h1:=emit_three width a b rank active rev scalar bit flag rt
    have h2:=ih (bit::true::rev) (some bit)
    have hh:=run_append 3 (3*scalar.length+2) _ _ _ h1 h2
    rw [show 3+(3*scalar.length+2)=3*(bit::scalar).length+2 by simp; omega] at hh
    simpa only [frame,List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append] using hh

/-- Exact writer stage including the vector-cons tag; no serializer callback is supplied. -/
theorem emit_run (width a b rank active rev scalar : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run program (3*scalar.length+3)
      (state (some .emitTag) flag rt [] [] [] scalar width [] a b rank active rev [] [] [] [])=
    some (state (some .loop) none rt [] [] [] [] width [] a b rank active
      ((true::frame scalar []).reverse++rev) [] [] [] []) := by
  have h1 : C.run program 1
      (state (some .emitTag) flag rt [] [] [] scalar width [] a b rank active rev [] [] [] [])=
      some (state (some .emitWord) flag rt [] [] [] scalar width [] a b rank active (true::rev) [] [] [] []) := by
    simp [C.run,C.step,C.execute,state,program,store_rev]
  have h2:=emit_word_run width a b rank active (true::rev) scalar flag rt
  have hh:=run_append 1 (3*scalar.length+2) _ _ _ h1 h2
  rw [show 1+(3*scalar.length+2)=3*scalar.length+3 by omega] at hh
  simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh

/-- Literal read cost: a nil sentinel is peeked once; each actual word is physically parsed. -/
def readClock : List (List Bool) → ℕ
  | [] => 1
  | word::_ => 8*word.length+10

/-- Actual left coefficient read, including nil-default behavior and parsed flag acquisition. -/
theorem read_left (width b rank active rev right : List Bool) (as : List (List Bool)) :
    Runs program (readClock as) .readLeft
      (P [] right [] width (vectorBits as) b rank active rev)
      .readRight (P (as.headD []) right [] width (vectorBits as.tail) b rank active rev) := by
  cases as with
  | nil =>
    apply one_base program .readLeft .readRight
      (.peek (.inr .leftTape) .readRight .readRight .leftTag) (P [] right [] width (vectorBits []) b rank active rev) (P [] right [] width (vectorBits []) b rank active rev) rfl
    · rfl
    · rfl
  | cons word as =>
    let d0:=P [] right [] width (vectorBits (word::as)) b rank active rev
    let d1:=P [] right [] width (frame word (vectorBits as)) b rank active rev
    let d2:=store word right [] [] width [] (vectorBits as) b rank active rev [] [true] [] []
    let d3:=P word right [] width (vectorBits as) b rank active rev
    have h0 : Runs program 1 .readLeft d0 .leftTag d0 := by
      apply one_base program .readLeft .leftTag (.peek (.inr .leftTape) .readRight .readRight .leftTag) d0 d0 rfl
      · rfl
      · rfl
    have h1 : Runs program 1 .leftTag d0 .callLeft d1 := by
      apply one_base program .leftTag .callLeft (.pop (.inr .leftTape) .callLeft .callLeft .callLeft) d0 d1 rfl
      · rfl
      · funext k
        rcases k with k|k
        · rcases k with k|k
          · cases k <;> rfl
          · cases k <;> rfl
        · cases k <;> rfl
    have h2 : Runs program (8*word.length+7) .callLeft d1 .leftParsed d2 := by
      apply included_call program (fieldStack false) (Label.field false) (fieldStack_injective false)
        Field.code (Field.active .tagPop (none,false)) (fun _=>rfl) .callLeft .leftParsed rfl
        (8*word.length+6) (Field.initial (frame word (vectorBits as)) [])
        (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents (vectorBits as) [] word)
          (fun _=>[true])⟩:SemiprimeD1StackBytecode.State Field.Stack Field.Label) d1 d2
      · rfl
      · rfl
      · exact Field.framed_run word (vectorBits as) []
      · constructor
        · intro k; rcases k with k|k <;> cases k <;> rfl
        · intro k hk; rfl
      · constructor
        · intro k; rcases k with k|k <;> cases k <;> rfl
        · intro k hk
          rcases k with k|k
          · rcases k with k|k
            · cases k <;> first | rfl | exact False.elim (hk (.inl .output) rfl)
            · cases k <;> rfl
          · cases k <;> first | rfl | exact False.elim (hk (.inl .input) rfl) | exact False.elim (hk (.inr ()) rfl)
    have h3 : Runs program 1 .leftParsed d2 .readRight d3 := by
      apply one_base program .leftParsed .readRight (.pop (.inr .valid) .abort .abort .readRight) d2 d3 rfl
      · rfl
      · funext k
        rcases k with k|k
        · rcases k with k|k
          · cases k <;> rfl
          · cases k <;> rfl
        · cases k <;> rfl
    have hh:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3
    simpa only [readClock,List.headD_cons,List.tail_cons,
      show 1+1+(8*word.length+7)+1=8*word.length+10 by omega] using hh

/-- Actual right coefficient read, including nil-default behavior and parsed flag acquisition. -/
theorem read_right (width a rank active rev left : List Bool) (bs : List (List Bool)) :
    Runs program (readClock bs) .readRight
      (P left [] [] width a (vectorBits bs) rank active rev)
      .callScalar (P left (bs.headD []) [] width a (vectorBits bs.tail) rank active rev) := by
  cases bs with
  | nil =>
    apply one_base program .readRight .callScalar
      (.peek (.inr .rightTape) .callScalar .callScalar .rightTag) (P left [] [] width a (vectorBits []) rank active rev) (P left [] [] width a (vectorBits []) rank active rev) rfl
    · rfl
    · rfl
  | cons word bs =>
    let d0:=P left [] [] width a (vectorBits (word::bs)) rank active rev
    let d1:=P left [] [] width a (frame word (vectorBits bs)) rank active rev
    let d2:=store left word [] [] width [] a (vectorBits bs) rank active rev [] [true] [] []
    let d3:=P left word [] width a (vectorBits bs) rank active rev
    have h0 : Runs program 1 .readRight d0 .rightTag d0 := by
      apply one_base program .readRight .rightTag (.peek (.inr .rightTape) .callScalar .callScalar .rightTag) d0 d0 rfl
      · rfl
      · rfl
    have h1 : Runs program 1 .rightTag d0 .callRight d1 := by
      apply one_base program .rightTag .callRight (.pop (.inr .rightTape) .callRight .callRight .callRight) d0 d1 rfl
      · rfl
      · funext k
        rcases k with k|k
        · rcases k with k|k
          · cases k <;> rfl
          · cases k <;> rfl
        · cases k <;> rfl
    have h2 : Runs program (8*word.length+7) .callRight d1 .rightParsed d2 := by
      apply included_call program (fieldStack true) (Label.field true) (fieldStack_injective true)
        Field.code (Field.active .tagPop (none,false)) (fun _=>rfl) .callRight .rightParsed rfl
        (8*word.length+6) (Field.initial (frame word (vectorBits bs)) [])
        (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents (vectorBits bs) [] word)
          (fun _=>[true])⟩:SemiprimeD1StackBytecode.State Field.Stack Field.Label) d1 d2
      · rfl
      · rfl
      · exact Field.framed_run word (vectorBits bs) []
      · constructor
        · intro k; rcases k with k|k <;> cases k <;> rfl
        · intro k hk; rfl
      · constructor
        · intro k; rcases k with k|k <;> cases k <;> rfl
        · intro k hk
          rcases k with k|k
          · rcases k with k|k
            · cases k <;> first | rfl | exact False.elim (hk (.inl .output) rfl)
            · cases k <;> rfl
          · cases k <;> first | rfl | exact False.elim (hk (.inl .input) rfl) | exact False.elim (hk (.inr ()) rfl)
    have h3 : Runs program 1 .rightParsed d2 .callScalar d3 := by
      apply one_base program .rightParsed .callScalar (.pop (.inr .valid) .abort .abort .callScalar) d2 d3 rfl
      · rfl
      · funext k
        rcases k with k|k
        · rcases k with k|k
          · cases k <;> rfl
          · cases k <;> rfl
        · cases k <;> rfl
    have hh:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3
    simpa only [readClock,List.headD_cons,List.tail_cons,
      show 1+1+(8*word.length+7)+1=8*word.length+10 by omega] using hh

/-- Actual nested scalar-add call; coefficients are the words acquired by the field readers. -/
theorem scalar_call (left right width a b rank active rev : List Bool)
    (flag : Option Bool) (rt : Option Label) :
    ∃ff rr,C.run program (SemiprimeD1StackJetScalarAddExecution.totalTime left right width+1)
      (⟨some .callScalar,flag,rt,P left right [] width a b rank active rev,[]⟩:C.State Stack Label)=
    some (⟨some .emitTag,ff,rr,P [] [] (SemiprimeD1StackJetScalarAddExecution.result left right width)
      width a b rank active rev,[]⟩:C.State Stack Label) := by
  let d0:=P left right [] width a b rank active rev
  let d1:=P [] [] (SemiprimeD1StackJetScalarAddExecution.result left right width) width a b rank active rev
  let entered : C.State Stack Label:=⟨some (.scalar .start),none,none,d0,[.emitTag]⟩
  have hstart : C.run program 1 (⟨some .callScalar,flag,rt,d0,[]⟩:C.State Stack Label)=some entered := rfl
  have hrel : SemiprimeD1StackValidationLink.Rel Sum.inl Label.scalar d0 .emitTag []
      (SemiprimeD1StackJetScalarAdd.state (some .start) none none left right [] [] width []) entered := by
    constructor
    · constructor
      · intro k; rfl
      · intro k hk
        rcases k with k|k
        · exact False.elim (hk k rfl)
        · rfl
    · exact ⟨rfl,rfl⟩
  obtain ⟨finish,hfinish,hr⟩:=SemiprimeD1StackValidationLink.run_rel Sum.inl Label.scalar Sum.inl_injective
    program S.program (fun _=>rfl) d0 .emitTag [] _ _ _ entered hrel
    (SemiprimeD1StackJetScalarAddExecution.source_run left right width) rfl
  have desired : SemiprimeD1StackMultiplierLink.DataRel Sum.inl d0
      (SemiprimeD1StackJetScalarAdd.state none none none [] [] []
        (SemiprimeD1StackJetScalarAddExecution.result left right width) width []).data d1 := by
    constructor
    · intro k; rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · cases k <;> rfl
  have hd:=SemiprimeD1StackMultiplierLink.data_unique Sum.inl d0 _ _ _ hr.1 desired
  have hp : finish.pc=some .emitTag ∧ finish.frames=[] := hr.2
  have heq : finish=(⟨some .emitTag,finish.flag,finish.returned,d1,[]⟩:C.State Stack Label) := by
    cases finish
    simp_all
  refine ⟨finish.flag,finish.returned,?_⟩
  have hh:=run_append 1 _ _ _ _ hstart (hfinish.trans (congrArg some heq))
  simpa only [Nat.add_comm] using hh

/-- Actual reads of both next coefficients, with nil-defaults supplied only by tape sentinels. -/
theorem read_pair (width rank active rev : List Bool) (a b : List (List Bool)) :
    Runs program (readClock a+readClock b) .readLeft
      (P [] [] [] width (vectorBits a) (vectorBits b) rank active rev)
      .callScalar (P (a.headD []) (b.headD []) [] width (vectorBits a.tail) (vectorBits b.tail) rank active rev) :=
  runs_trans program _ _ _ _ _ _ _ _
    (read_left width (vectorBits b) rank active rev [] a)
    (read_right width (vectorBits a.tail) rank active rev (a.headD []) b)

/-- Exact physical round count: rank pop, both field reads, modular scalar call and binary frame writes. -/
def roundTime (width : List Bool) (a b : List (List Bool)) : ℕ :=
  1+(readClock a+readClock b)+(SemiprimeD1StackJetScalarAddExecution.totalTime (a.headD []) (b.headD []) width+1)+
    (3*(SemiprimeD1StackJetScalarAddExecution.result (a.headD []) (b.headD []) width).length+3)

/-- One rank cell drives one actual coefficient pair, modular sum and serialized write. -/
theorem round_run (width rank active rev : List Bool) (a b : List (List Bool)) (marker : Bool)
    (flag : Option Bool) (rt : Option Label) :
    ∃ff rr,C.run program (roundTime width a b)
      (state (some .loop) flag rt [] [] [] [] width [] (vectorBits a) (vectorBits b) rank (marker::active) rev [] [] [] [])=
    some (state (some .loop) ff rr [] [] [] [] width [] (vectorBits a.tail) (vectorBits b.tail) rank active
      ((true::frame (SemiprimeD1StackJetScalarAddExecution.result (a.headD []) (b.headD []) width) []).reverse++rev) [] [] [] []) := by
  have h0 : C.run program 1
      (state (some .loop) flag rt [] [] [] [] width [] (vectorBits a) (vectorBits b) rank (marker::active) rev [] [] [] [])=
      some (state (some .readLeft) (some marker) rt [] [] [] [] width [] (vectorBits a) (vectorBits b) rank active rev [] [] [] []) := by
    cases marker <;> simp [C.run,C.step,C.execute,state,program,SemiprimeD1StackBytecode.choose,store_active]
  obtain ⟨readOut,h1,hAt⟩:=read_pair width rank active rev a b []
    (state (some .readLeft) (some marker) rt [] [] [] [] width [] (vectorBits a) (vectorBits b) rank active rev [] [] [] [])
    ⟨rfl,rfl,rfl⟩
  have heq : readOut=(⟨some .callScalar,readOut.flag,readOut.returned,
      P (a.headD []) (b.headD []) [] width (vectorBits a.tail) (vectorBits b.tail) rank active rev,[]⟩:C.State Stack Label) := by
    cases readOut
    simp_all [At]
  have h1':=h1.trans (congrArg some heq)
  obtain ⟨ff,rr,h2⟩:=scalar_call (a.headD []) (b.headD []) width (vectorBits a.tail) (vectorBits b.tail)
    rank active rev readOut.flag readOut.returned
  have h3:=emit_run width (vectorBits a.tail) (vectorBits b.tail) rank active rev
    (SemiprimeD1StackJetScalarAddExecution.result (a.headD []) (b.headD []) width) ff rr
  refine ⟨none,rr,?_⟩
  exact run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ h0 h1') h2) h3

/-- Proof-side canonical coefficient list obtained from this many physical rank cells. -/
def rows : List Bool → List Bool → List (List Bool) → List (List Bool) → List (List Bool)
  | [],_,_,_ => []
  | _::counter,width,a,b =>
    SemiprimeD1StackJetScalarAddExecution.result (a.headD []) (b.headD []) width::rows counter width a.tail b.tail

/-- Literal forward vector payload, without the final nil-vector marker. -/
def chunks : List (List Bool) → List Bool
  | [] => []
  | word::rest => (true::frame word [])++chunks rest

/-- The physical frame chunks and final false bit are exactly the existing vector codec. -/
theorem vector_eq_prefix (words : List (List Bool)) : vectorBits words=chunks words++[false] := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    simp only [vectorBits,chunks,List.cons_append,
      SemiprimeD1TensorTapeCodec.frame_append,List.nil_append,←ih]

/-- Exact actual loop count, not a count or coefficient answer used by the running program. -/
def loopTime : List Bool → List Bool → List (List Bool) → List (List Bool) → ℕ
  | [],_,_,_ => 1
  | _::counter,width,a,b => roundTime width a b+loopTime counter width a.tail b.tail

/-- All rank-driven coefficient reads and writes execute in their original dense order. -/
theorem loop_run (counter width rank rev : List Bool) (a b : List (List Bool))
    (flag : Option Bool) (rt : Option Label) :
    ∃rr,C.run program (loopTime counter width a b)
      (state (some .loop) flag rt [] [] [] [] width [] (vectorBits a) (vectorBits b) rank counter rev [] [] [] [])=
    some (state (some .endVector) none rr [] [] [] [] width []
      (vectorBits (a.drop counter.length)) (vectorBits (b.drop counter.length)) rank []
      ((chunks (rows counter width a b)).reverse++rev) [] [] [] []) := by
  induction counter generalizing a b rev flag rt with
  | nil =>
    refine ⟨rt,?_⟩
    simp [loopTime,C.run,C.step,C.execute,state,program,SemiprimeD1StackBytecode.choose,store_active,rows,chunks]
  | cons marker counter ih =>
    obtain ⟨ff,rr,h1⟩:=round_run width rank counter rev a b marker flag rt
    obtain ⟨last,h2⟩:=ih ((true::frame (SemiprimeD1StackJetScalarAddExecution.result (a.headD []) (b.headD []) width) []).reverse++rev)
      a.tail b.tail ff rr
    have hh:=run_append _ _ _ _ _ h1 h2
    refine ⟨last,?_⟩
    simpa only [loopTime,rows,chunks,List.reverse_append,List.append_assoc,List.length_cons,List.drop_tail] using hh

/-- Whole physical vector reverse consists of the final marker and reversed emitted chunks. -/
theorem vector_reverse (words : List (List Bool)) : (vectorBits words).reverse=false::(chunks words).reverse := by
  rw [vector_eq_prefix,List.reverse_append]
  rfl

/-- Exact physical output finishing time, including both unused input suffixes. -/
def finishTime (a b words : List (List Bool)) : ℕ :=
  1+((vectorBits a).length+1)+((vectorBits b).length+1)+(2*(vectorBits words).length+1)+1

/-- Finishing executes vector termination, actual input clearing, reversal and halt. -/
theorem finish_run (width rank : List Bool) (a b words : List (List Bool))
    (flag : Option Bool) (rt : Option Label) :
    C.run program (finishTime a b words)
      (state (some .endVector) flag rt [] [] [] [] width [] (vectorBits a) (vectorBits b) rank [] (chunks words).reverse [] [] [] [])=
    some (state none none none [] [] [] [] width [] [] [] rank [] [] (vectorBits words) [] [] []) := by
  have h1 : C.run program 1
      (state (some .endVector) flag rt [] [] [] [] width [] (vectorBits a) (vectorBits b) rank [] (chunks words).reverse [] [] [] [])=
      some (state (some .clearLeft) flag rt [] [] [] [] width [] (vectorBits a) (vectorBits b) rank []
        (vectorBits words).reverse [] [] [] []) := by
    simp [C.run,C.step,C.execute,state,program,store_rev,vector_reverse]
  have h2:=clear_left [] [] [] [] width [] (vectorBits a) (vectorBits b) rank [] (vectorBits words).reverse [] [] [] [] flag rt
  have h3:=clear_right [] [] [] [] width [] [] (vectorBits b) rank [] (vectorBits words).reverse [] [] [] [] none rt
  have h4:=reverse_run [] [] [] [] width [] [] [] rank [] (vectorBits words).reverse [] [] [] [] none rt
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at h4
  have h5 : C.run program 1
      (state (some .done) none rt [] [] [] [] width [] [] [] rank [] [] (vectorBits words) [] [] [])=
      some (state none none none [] [] [] [] width [] [] [] rank [] [] (vectorBits words) [] [] []) := rfl
  exact run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ h1 h2) h3) h4) h5

/-- Exact closed actual vector-addition trace length. -/
def totalTime (width rank : List Bool) (a b : List (List Bool)) : ℕ :=
  (5*rank.length+4)+loopTime rank width a b+
    finishTime (a.drop rank.length) (b.drop rank.length) (rows rank width a b)

/-- Closed actual vector acquisition: no per-coordinate callback, metadata answer or output supplied. -/
theorem source_run (width rank : List Bool) (a b : List (List Bool)) :
    C.run program (totalTime width rank a b)
      (state (some .start) none none [] [] [] [] width [] (vectorBits a) (vectorBits b) rank [] [] [] [] [] [])=
    some (state none none none [] [] [] [] width [] [] [] rank [] [] (vectorBits (rows rank width a b)) [] [] []) := by
  let d0:=P [] [] [] width (vectorBits a) (vectorBits b) rank [] []
  let d1:=P [] [] [] width (vectorBits a) (vectorBits b) rank rank []
  have hcopy : Runs program (5*rank.length+4) .start d0 .loop d1 := by
    apply included_call program copyStack Label.copy copyStack_injective SemiprimeD1StackCopy.code (0:Fin 9)
      (fun _=>rfl) .start .loop rfl (5*rank.length+3)
      (SemiprimeD1StackCopy.state 0 none rank [] []) (SemiprimeD1StackCopy.done rank (rank++[])) d0 d1
    · rfl
    · rfl
    · exact SemiprimeD1StackCopy.copy_words rank [] none
    · constructor
      · intro k; fin_cases k <;> rfl
      · intro k hk; rfl
    · constructor
      · intro k; fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.done,SemiprimeD1StackCopy.payload,d1,P]
      · intro k hk
        rcases k with k|k
        · rfl
        · cases k <;> first | rfl | exact False.elim (hk 1 rfl)
  obtain ⟨copied,h1,hAt⟩:=hcopy []
    (state (some .start) none none [] [] [] [] width [] (vectorBits a) (vectorBits b) rank [] [] [] [] [] []) ⟨rfl,rfl,rfl⟩
  have heq : copied=state (some .loop) copied.flag copied.returned [] [] [] [] width []
      (vectorBits a) (vectorBits b) rank rank [] [] [] [] [] := by
    cases copied
    simp_all [At,state,P,d1]
  have h1':=h1.trans (congrArg some heq)
  obtain ⟨rr,h2⟩:=loop_run rank width rank [] a b copied.flag copied.returned
  simp only [List.append_nil] at h2
  have h3:=finish_run width rank (a.drop rank.length) (b.drop rank.length) (rows rank width a b) none rr
  exact run_append _ _ _ _ _ (run_append _ _ _ _ _ h1' h2) h3

/-- Dense source-coordinate bytes written by the actual rank counter. -/
theorem rows_eq_map (rank width : List Bool) (a b : List (List Bool)) :
    rows rank width a b=(List.range rank.length).map (fun i=>
      (SemiprimeD1JetScalarBits.add width.length ((a[i]?).getD []) ((b[i]?).getD [])).bits) := by
  induction rank generalizing a b with
  | nil => rfl
  | cons marker rank ih =>
    rw [rows,List.length_cons,List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,Function.comp_def]
    rw [ih]
    congr 1
    · cases a <;> cases b <;> rfl
    · apply List.map_congr_left
      intro i hi
      simp only [List.getElem?_tail]

/-- Exact original JetRingBits dense-add bytes from the physical precision/rank representation. -/
theorem rows_eq_original (ctx : SemiprimeD1JetAxes.Context) (width rank : List Bool)
    (a b : List (List Bool)) (hp : width.length=ctx.precision) (hr : rank.length=ctx.rank) :
    rows rank width a b=(SemiprimeD1JetRingBits.add ctx a b).words := by
  rw [rows_eq_map,hp,hr]
  simp only [SemiprimeD1JetRingBits.add,List.map_map,Function.comp_def,SemiprimeD1JetRingBits.addAt,
    SemiprimeD1JetRingBits.read_bits]

/-- Physical head-word length is bounded by its actual tagged tape inventory. -/
theorem head_length_le (a : List (List Bool)) : (a.headD []).length ≤ (vectorBits a).length := by
  cases a with
  | nil => simp [vectorBits]
  | cons word rest => simp only [List.headD_cons,vectorBits,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]; omega

/-- Advancing the actual parsed stream never increases its serialized inventory. -/
theorem tail_length_le (a : List (List Bool)) : (vectorBits a.tail).length ≤ (vectorBits a).length := by
  cases a with
  | nil => rfl
  | cons word rest => simp only [List.tail_cons,vectorBits,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]; omega

/-- Unused suffix inventory is bounded by the original physical input tape. -/
theorem drop_length_le (a : List (List Bool)) (n : ℕ) : (vectorBits (a.drop n)).length ≤ (vectorBits a).length := by
  induction n generalizing a with
  | zero => exact le_refl _
  | succ n ih =>
    rw [←List.drop_tail]
    exact (ih a.tail).trans (tail_length_le a)

/-- Every actual coefficient read has a closed inventory bound, without a read-cost supplier. -/
theorem readClock_le (a : List (List Bool)) : readClock a ≤ 8*(vectorBits a).length+10 := by
  have hh:=head_length_le a
  cases a <;> simp only [readClock,List.headD_nil,List.headD_cons] at * <;> omega

/-- One actual round is linear in current encoded input inventory and physical precision. -/
theorem roundTime_le (width : List Bool) (a b : List (List Bool)) :
    roundTime width a b ≤ 100*((vectorBits a).length+(vectorBits b).length+width.length+2) := by
  have h1:=readClock_le a
  have h2:=readClock_le b
  have h3:=SemiprimeD1StackJetScalarAddExecution.totalTime_le (a.headD []) (b.headD []) width
  have h4:=(SemiprimeD1JetScalarBits.add_length width.length (a.headD []) (b.headD []))
  change (SemiprimeD1StackJetScalarAddExecution.result (a.headD []) (b.headD []) width).length ≤ width.length at h4
  have ha:=head_length_le a
  have hb:=head_length_le b
  unfold roundTime SemiprimeD1StackJetScalarAddExecution.timeBound at *
  omega

/-- Actual rank-loop time with inventory caps derived from actual original tapes. -/
theorem loopTime_le (counter width : List Bool) (a b : List (List Bool)) (A B : ℕ)
    (ha : (vectorBits a).length ≤ A) (hb : (vectorBits b).length ≤ B) :
    loopTime counter width a b ≤ counter.length*100*(A+B+width.length+2)+1 := by
  induction counter generalizing a b with
  | nil => simp [loopTime]
  | cons marker counter ih =>
    have h1:=roundTime_le width a b
    have h2:=ih a.tail b.tail ((tail_length_le a).trans ha) ((tail_length_le b).trans hb)
    simp only [loopTime,List.length_cons]
    nlinarith

/-- The physical counter controls the exact number of canonical output coefficients. -/
theorem rows_length (counter width : List Bool) (a b : List (List Bool)) :
    (rows counter width a b).length=counter.length := by
  induction counter generalizing a b with
  | nil => rfl
  | cons marker counter ih => simp only [rows,List.length_cons,ih]

/-- Serialized output size is derived from actual modular outputs, with no Fits/size oracle. -/
theorem rows_tape_length (counter width : List Bool) (a b : List (List Bool)) :
    (vectorBits (rows counter width a b)).length ≤ 2*counter.length*width.length+2*counter.length+1 := by
  induction counter generalizing a b with
  | nil => simp [rows,vectorBits]
  | cons marker counter ih =>
    have h1:=ih a.tail b.tail
    have h2:=SemiprimeD1JetScalarBits.add_length width.length (a.headD []) (b.headD [])
    change (SemiprimeD1StackJetScalarAddExecution.result (a.headD []) (b.headD []) width).length ≤ width.length at h2
    simp only [rows,vectorBits,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length] at *
    nlinarith

/-- Fixed polynomial in physical rank, precision and encoded operand inventories. -/
def timeBound (R p A B : ℕ) : ℕ := 200*(R+1)*(A+B+p+2)

/-- Complete actual time: rank acquisition, all reads/arithmetic/writes, suffix clearing, reversal and halt. -/
theorem totalTime_le (width rank : List Bool) (a b : List (List Bool)) :
    totalTime width rank a b ≤ timeBound rank.length width.length (vectorBits a).length (vectorBits b).length := by
  have hl:=loopTime_le rank width a b (vectorBits a).length (vectorBits b).length (le_refl _) (le_refl _)
  have ha:=drop_length_le a rank.length
  have hb:=drop_length_le b rank.length
  have ho:=rows_tape_length rank width a b
  unfold totalTime finishTime timeBound
  nlinarith

/-- Genuine source execution certificate from actual encoded vectors and context counters. -/
def sourceAdd (width rank : List Bool) (a b : List (List Bool)) :
    StateTransition.EvalsToInTime (C.step program)
      (state (some .start) none none [] [] [] [] width [] (vectorBits a) (vectorBits b) rank [] [] [] [] [] [])
      (some (state none none none [] [] [] [] width [] [] [] rank [] [] (vectorBits (rows rank width a b)) [] [] []))
      (timeBound rank.length width.length (vectorBits a).length (vectorBits b).length) :=
  ⟨⟨_,source_run width rank a b⟩,totalTime_le width rank a b⟩

/-- Actual fixed dense-vector machine execution, without any coefficient/routing evaluator. -/
def machineAdd (width rank : List Bool) (a b : List (List Bool)) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (state (some .start) none none [] [] [] [] width [] (vectorBits a) (vectorBits b) rank [] [] [] [] [] []))
      (some (SemiprimeD1StackCalls.configuration
        (state none none none [] [] [] [] width [] [] [] rank [] [] (vectorBits (rows rank width a b)) [] [] [])))
      (timeBound rank.length width.length (vectorBits a).length (vectorBits b).length) :=
  SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label) (Sum.inr Aux.leftTape) (Sum.inr Aux.output)
    Label.start program _ _ _ (sourceAdd width rank a b)

/-- Exact old dense jet bytes at the actual caller's physical context representation. -/
def machineAddContext (ctx : SemiprimeD1JetAxes.Context) (width rank : List Bool) (a b : List (List Bool))
    (hp : width.length=ctx.precision) (hr : rank.length=ctx.rank) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (state (some .start) none none [] [] [] [] width [] (vectorBits a) (vectorBits b) rank [] [] [] [] [] []))
      (some (SemiprimeD1StackCalls.configuration
        (state none none none [] [] [] [] width [] [] [] rank [] []
          (vectorBits (SemiprimeD1JetRingBits.add ctx a b).words) [] [] [])))
      (timeBound rank.length width.length (vectorBits a).length (vectorBits b).length) := by
  rw [←rows_eq_original ctx width rank a b hp hr]
  exact machineAdd width rank a b

/-- Every actual source prefix bounds all fifteen Boolean stacks and its real return frames. -/
theorem prefix_cells (width rank : List Bool) (a b : List (List Bool)) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel
      (state (some .start) none none [] [] [] [] width [] (vectorBits a) (vectorBits b) rank [] [] [] [] [] [])=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      16*(width.length+rank.length+(vectorBits a).length+(vectorBits b).length+fuel) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel
    (width.length+rank.length+(vectorBits a).length+(vectorBits b).length) _ out (by
      intro k
      rcases k with k|k
      · rcases k with k|k
        · cases k <;> simp [state,store,SemiprimeD1StackJetScalarAdd.store]
        · cases k <;> simp [state,store,SemiprimeD1StackJetScalarAdd.store]; omega
      · cases k <;> simp [state,store] <;> omega) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k:Stack,(out.data k).length) ≤
      15*(width.length+rank.length+(vectorBits a).length+(vectorBits b).length+fuel) := by
    calc
      _ ≤ ∑_k:Stack,(width.length+rank.length+(vectorBits a).length+(vectorBits b).length+fuel) :=
        Finset.sum_le_sum (fun k _=>hd k)
      _ = 15*(width.length+rank.length+(vectorBits a).length+(vectorBits b).length+fuel) := by
        have h₀ : Fintype.card SemiprimeD1StackAdder.Stack=4 := by decide
        have h₁ : Fintype.card Aux=9 := by decide
        simp [Stack,SemiprimeD1StackJetScalarAdd.Stack,h₀,h₁]
  omega

/-- A successful execution prefix cannot continue beyond the actual dense-vector halt. -/
theorem prefix_fuel_le (width rank : List Bool) (a b : List (List Bool)) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel
      (state (some .start) none none [] [] [] [] width [] (vectorBits a) (vectorBits b) rank [] [] [] [] [] [])=some out) :
    fuel ≤ totalTime width rank a b := by
  by_contra hn
  have he : fuel=totalTime width rank a b+(1+(fuel-(totalTime width rank a b+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hh : C.run program 1
      (state none none none [] [] [] [] width [] [] [] rank [] [] (vectorBits (rows rank width a b)) [] [] [])=none := rfl
  rw [hh,Option.bind_none] at hr
  cases hr

/-- All-prefix physical data/return storage is polynomial in rank, precision and actual encoded inventory. -/
theorem prefix_polynomial_cells (width rank : List Bool) (a b : List (List Bool)) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel
      (state (some .start) none none [] [] [] [] width [] (vectorBits a) (vectorBits b) rank [] [] [] [] [] [])=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      16*(width.length+rank.length+(vectorBits a).length+(vectorBits b).length+
        timeBound rank.length width.length (vectorBits a).length (vectorBits b).length) := by
  have hf:=(prefix_fuel_le width rank a b fuel out hr).trans (totalTime_le width rank a b)
  exact (prefix_cells width rank a b fuel out hr).trans (by omega)

/-- The same unconditional prefix bound holds for the actual compiled fixed machine. -/
theorem machine_prefix_polynomial_cells (width rank : List Bool) (a b : List (List Bool)) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (state (some .start) none none [] [] [] [] width [] (vectorBits a) (vectorBits b) rank [] [] [] [] [] [])))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      16*(width.length+rank.length+(vectorBits a).length+(vectorBits b).length+
        timeBound rank.length width.length (vectorBits a).length (vectorBits b).length) := by
  let start:=state (some .start) none none [] [] [] [] width [] (vectorBits a) (vectorBits b) rank [] [] [] [] [] []
  have he:=SemiprimeD1StackCalls.run_correct (Sum.inr Aux.leftTape) (Sum.inr Aux.output) Label.start program fuel start
  change (C.run program fuel start).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  cases hc:C.run program fuel start with
  | none => rw [hc,hr] at he; cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    rw [←hcfg]
    exact prefix_polynomial_cells width rank a b fuel out hc

/-- A common numerical resource bound yields one fixed quadratic polynomial, without an advised runtime. -/
theorem timeBound_le_square (R p A B S : ℕ) (hR : R ≤ S) (hp : p ≤ S) (hA : A ≤ S) (hB : B ≤ S) :
    timeBound R p A B ≤ 1000*(S+1)^2 := by
  unfold timeBound
  have h : 200*(R+1)*(A+B+p+2) ≤ 200*(S+1)*(3*S+2) := by gcongr; omega
  nlinarith

end RiemannGaussian.SemiprimeD1StackJetAddExecution
