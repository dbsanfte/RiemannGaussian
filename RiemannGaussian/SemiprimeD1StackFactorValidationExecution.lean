/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFactorValidation

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackFactorValidationExecution
open SemiprimeD1StackFactorValidation
namespace C
export SemiprimeD1StackCalls (State execute step run)
end C

/-- Proof-side configuration constructor; all data still occupy actual stacks. -/
def atState (pc : Option Label) (flag : Option Bool) (returned : Option Label)
    (data : Stack → List Bool) : C.State Stack Label := ⟨pc,flag,returned,data,[]⟩

/-- Actual trace composition in the fixed validator. -/
theorem run_append (m n : ℕ) (a b c : C.State Stack Label)
    (hm : C.run code m a=some b) (hn : C.run code n b=some c) :
    C.run code (m+n) a=some c := by
  rw [SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,hn]

/-- Two literal transitions of the real program. -/
theorem two_steps (a b c : C.State Stack Label)
    (h₁ : C.step code a=some b) (h₂ : C.step code b=some c) : C.run code 2 a=some c := by
  change (C.step code a).bind (C.step code)=some c
  rw [h₁,Option.bind_some,h₂]

/-- Exact physical xs stack write. -/
theorem payload_xs (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid) (.inl (.inr .input)) bits=payload bits ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_xs (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid (.inl (.inr .input))=xs := rfl

/-- Exact physical ys stack write. -/
theorem payload_ys (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid) (.inl (.inr .divisor)) bits=payload xs bits ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_ys (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid (.inl (.inr .divisor))=ys := rfl

/-- Exact physical ds stack write. -/
theorem payload_ds (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid) (.inl (.inr .digits)) bits=payload xs ys bits left right scratch diff rem quo cp tmp input candidate guard work lower upper valid := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_ds (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid (.inl (.inr .digits))=ds := rfl

/-- Exact physical left stack write. -/
theorem payload_left (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid) (.inl (.inl .left)) bits=payload xs ys ds bits right scratch diff rem quo cp tmp input candidate guard work lower upper valid := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_left (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid (.inl (.inl .left))=left := rfl

/-- Exact physical right stack write. -/
theorem payload_right (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid) (.inl (.inl .right)) bits=payload xs ys ds left bits scratch diff rem quo cp tmp input candidate guard work lower upper valid := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_right (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid (.inl (.inl .right))=right := rfl

/-- Exact physical scratch stack write. -/
theorem payload_scratch (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid) (.inl (.inl .scratch)) bits=payload xs ys ds left right bits diff rem quo cp tmp input candidate guard work lower upper valid := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_scratch (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid (.inl (.inl .scratch))=scratch := rfl

/-- Exact physical diff stack write. -/
theorem payload_diff (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid) (.inl (.inl .output)) bits=payload xs ys ds left right scratch bits rem quo cp tmp input candidate guard work lower upper valid := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_diff (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid (.inl (.inl .output))=diff := rfl

/-- Exact physical rem stack write. -/
theorem payload_rem (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid) (.inl (.inr .remainder)) bits=payload xs ys ds left right scratch diff bits quo cp tmp input candidate guard work lower upper valid := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_rem (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid (.inl (.inr .remainder))=rem := rfl

/-- Exact physical quo stack write. -/
theorem payload_quo (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid) (.inl (.inr .quotient)) bits=payload xs ys ds left right scratch diff rem bits cp tmp input candidate guard work lower upper valid := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_quo (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid (.inl (.inr .quotient))=quo := rfl

/-- Exact physical cp stack write. -/
theorem payload_cp (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid) (.inl (.inr .copyScratch)) bits=payload xs ys ds left right scratch diff rem quo bits tmp input candidate guard work lower upper valid := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_cp (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid (.inl (.inr .copyScratch))=cp := rfl

/-- Exact physical tmp stack write. -/
theorem payload_tmp (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid) (.inl (.inr .template)) bits=payload xs ys ds left right scratch diff rem quo cp bits input candidate guard work lower upper valid := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_tmp (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid (.inl (.inr .template))=tmp := rfl

/-- Exact physical input stack write. -/
theorem payload_input (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid) (.inr .input) bits=payload xs ys ds left right scratch diff rem quo cp tmp bits candidate guard work lower upper valid := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_input (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid (.inr .input)=input := rfl

/-- Exact physical candidate stack write. -/
theorem payload_candidate (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid) (.inr .candidate) bits=payload xs ys ds left right scratch diff rem quo cp tmp input bits guard work lower upper valid := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_candidate (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid (.inr .candidate)=candidate := rfl

/-- Exact physical guard stack write. -/
theorem payload_guard (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid) (.inr .guard) bits=payload xs ys ds left right scratch diff rem quo cp tmp input candidate bits work lower upper valid := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_guard (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid (.inr .guard)=guard := rfl

/-- Exact physical work stack write. -/
theorem payload_work (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid) (.inr .copyScratch) bits=payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard bits lower upper valid := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_work (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid (.inr .copyScratch)=work := rfl

/-- Exact physical lower stack write. -/
theorem payload_lower (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid) (.inr .lower) bits=payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work bits upper valid := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_lower (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid (.inr .lower)=lower := rfl

/-- Exact physical upper stack write. -/
theorem payload_upper (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid) (.inr .upper) bits=payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower bits valid := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_upper (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid (.inr .upper)=upper := rfl

/-- Exact physical valid stack write. -/
theorem payload_valid (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid bits : List Bool) :
    Function.update (payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid) (.inr .valid) bits=payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper bits := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
    · cases k <;> simp [payload,SemiprimeD1StackDivider.payload,Function.update]
  · cases k <;> simp [payload,Function.update]

@[simp] theorem payload_get_valid (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid (.inr .valid)=valid := rfl

/-- Actual copy execution at any one of this validator's literal call sites. -/
theorem copy_call (kind : CopyKind) (site continuation : Label)
    (hcall : code site=.call (.copy kind 0) continuation)
    (data : Stack → List Bool) (ho : data (copyOutput kind)=[]) (hw : data (.inr .copyScratch)=[])
    (flag : Option Bool) (rt : Option Label) :
    ∃ff rr,C.run code (1+(5*(data (copyInput kind)).length+3))
      (atState (some site) flag rt data)=
    some (atState (some continuation) ff rr
      (Function.update data (copyOutput kind) (data (copyInput kind)))) := by
  let inp:=data (copyInput kind)
  let entered : C.State Stack Label := ⟨some (.copy kind 0),none,none,data,[continuation]⟩
  have hstart : C.run code 1 (atState (some site) flag rt data)=some entered := by
    simp [C.run,C.step,C.execute,atState,entered,hcall]
  have hd : SemiprimeD1StackMultiplierLink.DataRel (copyStack kind) data
      (SemiprimeD1StackCopy.payload inp [] []) data := by
    constructor
    · intro k
      fin_cases k
      · rfl
      · exact ho
      · exact hw
    · intro k hk; rfl
  have hrel : SemiprimeD1StackMultiplierLink.Rel (copyStack kind) (Label.copy kind) data
      continuation [] (SemiprimeD1StackCopy.state 0 none inp [] []) entered := ⟨hd,rfl,rfl⟩
  obtain ⟨finish,hfinish,hr⟩:=SemiprimeD1StackMultiplierLink.run_rel (copyStack kind)
    (Label.copy kind) (copyStack_injective kind) code SemiprimeD1StackCopy.code
    (fun _=>rfl) data continuation [] _ _ _ entered hrel (SemiprimeD1StackCopy.copy_words inp [] none)
  have hu:=SemiprimeD1StackMultiplierLink.data_update (copyStack kind) (copyStack_injective kind)
    data (SemiprimeD1StackCopy.payload inp [] []) data hd (1:Fin 3) inp
  have hs : Function.update (SemiprimeD1StackCopy.payload inp [] []) (1:Fin 3) inp=
      SemiprimeD1StackCopy.payload inp inp [] := by funext k; fin_cases k <;> rfl
  have hm : copyStack kind 1=copyOutput kind := rfl
  rw [hs,hm] at hu
  have desired : SemiprimeD1StackMultiplierLink.DataRel (copyStack kind) data
      (SemiprimeD1StackCopy.done inp (inp++[])).store
      (Function.update data (copyOutput kind) inp) := by simpa only [SemiprimeD1StackCopy.done,List.append_nil] using hu
  have hdata:=SemiprimeD1StackMultiplierLink.data_unique (copyStack kind) data _ _ _ hr.1 desired
  have hpc : finish.pc=some continuation ∧ finish.frames=[] := hr.2
  have heq : finish=atState (some continuation) finish.flag finish.returned
      (Function.update data (copyOutput kind) inp) := by cases finish; simp_all [atState]
  exact ⟨finish.flag,finish.returned,run_append 1 _ _ _ _ hstart (hfinish.trans (congrArg some heq))⟩

/-- Subtractor call time includes its actual return and the caller push. -/
def subClock (left right : List Bool) : ℕ :=
  1+(3*(max left.length right.length+1)+2*(SemiprimeBitDivision.subBits left right false).result.bits.length+3)

/-- Literal data remaining after the included subtractor. -/
def subData (data : Stack → List Bool) : Stack → List Bool :=
  let difference:=SemiprimeBitDivision.subBits (data (subStack .left)) (data (subStack .right)) false
  Function.update (Function.update (Function.update data (subStack .left) []) (subStack .right) [])
    (subStack .output) (difference.borrow::difference.result.bits)

/-- Exact real comparison/subtraction call at either literal validator call site. -/
theorem subtract_call (site continuation : Label)
    (hcall : code site=.call (.subtractor (.start false)) continuation)
    (data : Stack → List Bool) (hs : data (subStack .scratch)=[]) (ho : data (subStack .output)=[])
    (flag : Option Bool) (rt : Option Label) :
    ∃ff rr,C.run code (subClock (data (subStack .left)) (data (subStack .right)))
      (atState (some site) flag rt data)=some (atState (some continuation) ff rr (subData data)) := by
  let left:=data (subStack .left)
  let right:=data (subStack .right)
  let result:=SemiprimeBitDivision.subBits left right false
  let entered : C.State Stack Label := ⟨some (.subtractor (.start false)),none,none,data,[continuation]⟩
  have hi : Function.Injective subStack := by intro a b h; exact Sum.inl.inj (Sum.inl.inj h)
  have hstart : C.run code 1 (atState (some site) flag rt data)=some entered := by
    simp [C.run,C.step,C.execute,atState,entered,hcall]
  have hd : SemiprimeD1StackMultiplierLink.DataRel subStack data
      (SemiprimeD1StackAdder.store left right [] []) data := by
    constructor
    · intro k
      cases k with
      | left => rfl
      | right => rfl
      | scratch => exact hs
      | output => exact ho
    · intro k hk; rfl
  have hrel : SemiprimeD1StackMultiplierLink.Rel subStack Label.subtractor data continuation []
      (SemiprimeD1StackSubtractor.state (some (.start false)) none left right [] []) entered := ⟨hd,rfl,rfl⟩
  obtain ⟨finish,hfinish,hr⟩:=SemiprimeD1StackMultiplierLink.run_rel subStack Label.subtractor hi
    code SemiprimeD1StackSubtractor.code (fun _=>rfl) data continuation [] _ _ _ entered hrel
    (SemiprimeD1StackSubtractorExecution.source_run left right false)
  have h1:=SemiprimeD1StackMultiplierLink.data_update subStack hi data _ _ hd .left []
  rw [SemiprimeD1StackAdder.store_left] at h1
  have h2:=SemiprimeD1StackMultiplierLink.data_update subStack hi data _ _ h1 .right []
  rw [SemiprimeD1StackAdder.store_right] at h2
  have h3:=SemiprimeD1StackMultiplierLink.data_update subStack hi data _ _ h2 .output
    (result.borrow::result.result.bits)
  rw [SemiprimeD1StackAdder.store_output] at h3
  have desired : SemiprimeD1StackMultiplierLink.DataRel subStack data
      (SemiprimeD1StackSubtractor.state none none [] [] [] (result.borrow::result.result.bits)).store
      (subData data) := h3
  have hdata:=SemiprimeD1StackMultiplierLink.data_unique subStack data _ _ _ hr.1 desired
  have hpc : finish.pc=some continuation ∧ finish.frames=[] := hr.2
  have heq : finish=atState (some continuation) finish.flag finish.returned (subData data) := by
    cases finish
    simp_all [atState]
  exact ⟨finish.flag,finish.returned,run_append 1 _ _ _ _ hstart (hfinish.trans (congrArg some heq))⟩

/-- Proof-side splitting of actual divider and persistent auxiliary stacks. -/
def join (div : D.Stack → List Bool) (extra : Aux → List Bool) : Stack → List Bool
  | .inl k => div k
  | .inr k => extra k

/-- Actual persistent auxiliary payload, without any semantic word getter. -/
def extraData (input candidate guard work lower upper valid : List Bool) : Aux → List Bool
  | .input => input
  | .candidate => candidate
  | .guard => guard
  | .copyScratch => work
  | .lower => lower
  | .upper => upper
  | .valid => valid

/-- Exact rewriting between the two literal payload presentations. -/
theorem join_payload (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    join (D.payload xs ys ds left right scratch diff rem quo cp tmp)
      (extraData input candidate guard work lower upper valid)=
    payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid := by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl

/-- Actual nested-call divider inclusion, with no trace or output answer supplied. -/
theorem divider_call (input candidate : List Bool) (extra : Aux → List Bool)
    (flag : Option Bool) (rt : Option Label) :
    ∃ff rr,C.run code (1+SemiprimeD1StackDividerExecution.executionTime input candidate)
      (atState (some (.control .callDivider)) flag rt
        (join (D.payload input candidate [] [] [] [] [] [] [] [] []) extra))=
    some (atState (some (.control .callLower)) ff rr
      (join (D.payload [] [] [] [] [] [] []
        (SemiprimeBitDivision.divideLoop input candidate).remainder
        (SemiprimeBitDivision.divideLoop input candidate).quotient [] []) extra)) := by
  let original:=join (D.payload input candidate [] [] [] [] [] [] [] [] []) extra
  let entered : C.State Stack Label := ⟨some (.divider (.control .start)),none,none,original,[.control .callLower]⟩
  have hstart : C.run code 1 (atState (some (.control .callDivider)) flag rt original)=some entered := rfl
  have hrel : SemiprimeD1StackValidationLink.Rel Sum.inl Label.divider original (.control .callLower) []
      (SemiprimeD1StackDivider.state (some (.control .start)) none none input candidate [] [] [] [] [] [] [] [] []) entered := by
    constructor
    · constructor
      · intro k; rfl
      · intro k hk
        rcases k with k|k
        · exact False.elim (hk k rfl)
        · rfl
    · exact ⟨rfl,rfl⟩
  obtain ⟨finish,hfinish,hr⟩:=SemiprimeD1StackValidationLink.run_rel Sum.inl Label.divider Sum.inl_injective
    code D.code (fun _=>rfl) original (.control .callLower) [] _ _ _ entered hrel
    (SemiprimeD1StackDividerExecution.source_run input candidate) rfl
  have desired : SemiprimeD1StackMultiplierLink.DataRel Sum.inl original
      (SemiprimeD1StackDivider.state none none none [] [] [] [] [] [] []
        (SemiprimeBitDivision.divideLoop input candidate).remainder
        (SemiprimeBitDivision.divideLoop input candidate).quotient [] []).data
      (join (D.payload [] [] [] [] [] [] []
        (SemiprimeBitDivision.divideLoop input candidate).remainder
        (SemiprimeBitDivision.divideLoop input candidate).quotient [] []) extra) := by
    constructor
    · intro k; rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · rfl
  have hdata:=SemiprimeD1StackMultiplierLink.data_unique Sum.inl original _ _ _ hr.1 desired
  have hpc : finish.pc=some (.control .callLower) ∧ finish.frames=[] := hr.2
  have heq : finish=atState (some (.control .callLower)) finish.flag finish.returned
      (join (D.payload [] [] [] [] [] [] []
        (SemiprimeBitDivision.divideLoop input candidate).remainder
        (SemiprimeBitDivision.divideLoop input candidate).quotient [] []) extra) := by
    cases finish
    simp_all [atState]
  exact ⟨finish.flag,finish.returned,run_append 1 _ _ _ _ hstart (hfinish.trans (congrArg some heq))⟩

/-- Actual clearing loop, one literal pop per visited cell. -/
theorem clear_lower (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (diff.length+1) (state (some (.control .clearLower)) flag rt xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid)=
    some (state (some (.control .callUpper)) none rt xs ys ds left right scratch ([]) rem quo cp tmp input candidate guard work lower upper valid) := by
  induction diff generalizing flag with
  | nil => simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,subStack,payload_diff]
  | cons b diff ih =>
    have hs : C.run code 1 (state (some (.control .clearLower)) flag rt xs ys ds left right scratch (b::diff) rem quo cp tmp input candidate guard work lower upper valid)=
        some (state (some (.control .clearLower)) (some b) rt xs ys ds left right scratch (diff) rem quo cp tmp input candidate guard work lower upper valid) := by
      cases b <;> simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,subStack,payload_diff]
    have hh:=run_append 1 (diff.length+1) _ _ _ hs (ih (some b))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Actual clearing loop, one literal pop per visited cell. -/
theorem clear_upper (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (diff.length+1) (state (some (.control .clearUpper)) flag rt xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid)=
    some (state (some (.control (.scanR false))) none rt xs ys ds left right scratch ([]) rem quo cp tmp input candidate guard work lower upper valid) := by
  induction diff generalizing flag with
  | nil => simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,subStack,payload_diff]
  | cons b diff ih =>
    have hs : C.run code 1 (state (some (.control .clearUpper)) flag rt xs ys ds left right scratch (b::diff) rem quo cp tmp input candidate guard work lower upper valid)=
        some (state (some (.control .clearUpper)) (some b) rt xs ys ds left right scratch (diff) rem quo cp tmp input candidate guard work lower upper valid) := by
      cases b <;> simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,subStack,payload_diff]
    have hh:=run_append 1 (diff.length+1) _ _ _ hs (ih (some b))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Actual clearing loop, one literal pop per visited cell. -/
theorem clear_input (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (input.length+1) (state (some (.control .cleanupInput)) flag rt xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid)=
    some (state (some (.control .cleanupCandidate)) none rt xs ys ds left right scratch diff rem quo cp tmp ([]) candidate guard work lower upper valid) := by
  induction input generalizing flag with
  | nil => simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_input]
  | cons b input ih =>
    have hs : C.run code 1 (state (some (.control .cleanupInput)) flag rt xs ys ds left right scratch diff rem quo cp tmp (b::input) candidate guard work lower upper valid)=
        some (state (some (.control .cleanupInput)) (some b) rt xs ys ds left right scratch diff rem quo cp tmp (input) candidate guard work lower upper valid) := by
      cases b <;> simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_input]
    have hh:=run_append 1 (input.length+1) _ _ _ hs (ih (some b))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Actual clearing loop, one literal pop per visited cell. -/
theorem clear_candidate (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (candidate.length+1) (state (some (.control .cleanupCandidate)) flag rt xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid)=
    some (state (some (.control .done)) none rt xs ys ds left right scratch diff rem quo cp tmp input ([]) guard work lower upper valid) := by
  induction candidate generalizing flag with
  | nil => simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_candidate]
  | cons b candidate ih =>
    have hs : C.run code 1 (state (some (.control .cleanupCandidate)) flag rt xs ys ds left right scratch diff rem quo cp tmp input (b::candidate) guard work lower upper valid)=
        some (state (some (.control .cleanupCandidate)) (some b) rt xs ys ds left right scratch diff rem quo cp tmp input (candidate) guard work lower upper valid) := by
      cases b <;> simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_candidate]
    have hh:=run_append 1 (candidate.length+1) _ _ _ hs (ih (some b))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Full physical OR scan; the acquired flag is stored only in finite control. -/
theorem scan_guard (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) (nz : Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (guard.length+1) (state (some (.control (.scanGuard nz))) flag rt xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid)=
    some (state (some (.control (.guardDone (nz || (SemiprimeBitDivision.nonzeroBits guard).nonzero))))
      none rt xs ys ds left right scratch diff rem quo cp tmp input candidate ([]) work lower upper valid) := by
  induction guard generalizing nz flag with
  | nil => simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_guard,SemiprimeBitDivision.nonzeroBits]
  | cons b guard ih =>
    have hs : C.run code 1 (state (some (.control (.scanGuard nz))) flag rt xs ys ds left right scratch diff rem quo cp tmp input candidate (b::guard) work lower upper valid)=
        some (state (some (.control (.scanGuard (nz || b)))) (some b) rt xs ys ds left right scratch diff rem quo cp tmp input candidate (guard) work lower upper valid) := by
      cases b <;> simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_guard]
    have hh:=run_append 1 (guard.length+1) _ _ _ hs (ih (nz || b) (some b))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
      SemiprimeBitDivision.nonzeroBits,Bool.or_assoc] using hh

/-- Full physical OR scan; the acquired flag is stored only in finite control. -/
theorem scan_remainder (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) (nz : Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (rem.length+1) (state (some (.control (.scanR nz))) flag rt xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid)=
    some (state (some (.control (.lowerFlag (nz || (SemiprimeBitDivision.nonzeroBits rem).nonzero))))
      none rt xs ys ds left right scratch diff ([]) quo cp tmp input candidate guard work lower upper valid) := by
  induction rem generalizing nz flag with
  | nil => simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_rem,SemiprimeBitDivision.nonzeroBits]
  | cons b rem ih =>
    have hs : C.run code 1 (state (some (.control (.scanR nz))) flag rt xs ys ds left right scratch diff (b::rem) quo cp tmp input candidate guard work lower upper valid)=
        some (state (some (.control (.scanR (nz || b)))) (some b) rt xs ys ds left right scratch diff (rem) quo cp tmp input candidate guard work lower upper valid) := by
      cases b <;> simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,state,code,payload_rem]
    have hh:=run_append 1 (rem.length+1) _ _ _ hs (ih (nz || b) (some b))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
      SemiprimeBitDivision.nonzeroBits,Bool.or_assoc] using hh

/-- Proof-side name for the actual clean-workspace boundary payload. -/
def P (input candidate rem quo lower upper valid : List Bool) : Stack → List Bool :=
  payload [] [] [] [] [] [] [] rem quo [] [] input candidate [] [] lower upper valid

/-- Exact lower-comparison stage cost, counted from actual calls and pops. -/
def lowerClock (candidate : List Bool) : ℕ :=
  (1+(5*candidate.length+3))+2+subClock candidate [false,true]+2+
    ((SemiprimeBitDivision.subBits candidate [false,true] false).result.bits.length+1)

/-- Actual lower comparison and saved borrow, preserving both result/persistent operands. -/
theorem lower_run (input candidate rem quo : List Bool) (flag : Option Bool) (rt : Option Label) :
    ∃ff rr,C.run code (lowerClock candidate)
      (atState (some (.control .callLower)) flag rt (P input candidate rem quo [] [] []))=
    some (atState (some (.control .callUpper)) ff rr
      (P input candidate rem quo [(SemiprimeBitDivision.subBits candidate [false,true] false).borrow] [] [])) := by
  obtain ⟨f1,r1,h1⟩:=copy_call .left (.control .callLower) (.control .lowerHigh) rfl
    (P input candidate rem quo [] [] []) rfl rfl flag rt
  simp only [copyInput,copyOutput,subStack,P,payload_get_candidate,payload_left] at h1
  have h2 : C.run code 2
      (atState (some (.control .lowerHigh)) f1 r1
        (payload [] [] [] candidate [] [] [] rem quo [] [] input candidate [] [] [] [] []))=
      some (state (some (.control .lowerSub)) f1 r1
        [] [] [] candidate [false,true] [] [] rem quo [] [] input candidate [] [] [] [] []) := by
    apply two_steps (b:=state (some (.control .lowerLow)) f1 r1
      [] [] [] candidate [true] [] [] rem quo [] [] input candidate [] [] [] [] [])
    · simp [C.step,C.execute,state,atState,code,subStack,payload_right]
    · simp [C.step,C.execute,state,code,subStack,payload_right]
  obtain ⟨f3,r3,h3⟩:=subtract_call (.control .lowerSub) (.control .lowerRead) rfl
    (payload [] [] [] candidate [false,true] [] [] rem quo [] [] input candidate [] [] [] [] []) rfl rfl f1 r1
  simp only [subData,subStack,payload_get_left,payload_get_right,payload_left,payload_right,payload_diff] at h3
  let difference:=SemiprimeBitDivision.subBits candidate [false,true] false
  have h4 : C.run code 2
      (atState (some (.control .lowerRead)) f3 r3
        (payload [] [] [] [] [] [] (difference.borrow::difference.result.bits) rem quo [] [] input candidate [] [] [] [] []))=
      some (state (some (.control .clearLower)) (some difference.borrow) r3
        [] [] [] [] [] [] difference.result.bits rem quo [] [] input candidate [] [] [difference.borrow] [] []) := by
    apply two_steps (b:=state (some (.control (.lowerSave difference.borrow))) (some difference.borrow) r3
      [] [] [] [] [] [] difference.result.bits rem quo [] [] input candidate [] [] [] [] [])
    · cases hb:difference.borrow <;> simp [C.step,C.execute,atState,state,code,subStack,
        SemiprimeD1StackBytecode.choose,payload_diff]
    · simp [C.step,C.execute,state,code,payload_lower]
  have h5:=clear_lower [] [] [] [] [] [] difference.result.bits rem quo [] [] input candidate [] []
    [difference.borrow] [] [] (some difference.borrow) r3
  refine ⟨none,r3,?_⟩
  exact run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ h1 h2) h3) h4) h5

/-- Exact upper-comparison stage cost, with both actual operand copies retained. -/
def upperClock (input candidate : List Bool) : ℕ :=
  (1+(5*candidate.length+3))+(1+(5*input.length+3))+subClock candidate input+2+
    ((SemiprimeBitDivision.subBits candidate input false).result.bits.length+1)

/-- Actual strict-upper comparison, acquiring and retaining its actual borrow flag. -/
theorem upper_run (input candidate rem quo lower : List Bool) (flag : Option Bool) (rt : Option Label) :
    ∃ff rr,C.run code (upperClock input candidate)
      (atState (some (.control .callUpper)) flag rt (P input candidate rem quo lower [] []))=
    some (atState (some (.control (.scanR false))) ff rr
      (P input candidate rem quo lower [(SemiprimeBitDivision.subBits candidate input false).borrow] [])) := by
  obtain ⟨f1,r1,h1⟩:=copy_call .left (.control .callUpper) (.control .callUpperRight) rfl
    (P input candidate rem quo lower [] []) rfl rfl flag rt
  simp only [copyInput,copyOutput,subStack,P,payload_get_candidate,payload_left] at h1
  obtain ⟨f2,r2,h2⟩:=copy_call .right (.control .callUpperRight) (.control .upperSub) rfl
    (payload [] [] [] candidate [] [] [] rem quo [] [] input candidate [] [] lower [] []) rfl rfl f1 r1
  simp only [copyInput,copyOutput,subStack,payload_get_input,payload_right] at h2
  obtain ⟨f3,r3,h3⟩:=subtract_call (.control .upperSub) (.control .upperRead) rfl
    (payload [] [] [] candidate input [] [] rem quo [] [] input candidate [] [] lower [] []) rfl rfl f2 r2
  simp only [subData,subStack,payload_get_left,payload_get_right,payload_left,payload_right,payload_diff] at h3
  let difference:=SemiprimeBitDivision.subBits candidate input false
  have h4 : C.run code 2
      (atState (some (.control .upperRead)) f3 r3
        (payload [] [] [] [] [] [] (difference.borrow::difference.result.bits) rem quo [] [] input candidate [] [] lower [] []))=
      some (state (some (.control .clearUpper)) (some difference.borrow) r3
        [] [] [] [] [] [] difference.result.bits rem quo [] [] input candidate [] [] lower [difference.borrow] []) := by
    apply two_steps (b:=state (some (.control (.upperSave difference.borrow))) (some difference.borrow) r3
      [] [] [] [] [] [] difference.result.bits rem quo [] [] input candidate [] [] lower [] [])
    · cases hb:difference.borrow <;> simp [C.step,C.execute,atState,state,code,subStack,
        SemiprimeD1StackBytecode.choose,payload_diff]
    · simp [C.step,C.execute,state,code,payload_upper]
  have h5:=clear_upper [] [] [] [] [] [] difference.result.bits rem quo [] [] input candidate [] []
    lower [difference.borrow] [] (some difference.borrow) r3
  refine ⟨none,r3,?_⟩
  exact run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ h1 h2) h3) h4) h5

/-- Three physical reads/pushes assemble the valid bit from acquired flags. -/
theorem flags_run (input candidate quo : List Bool) (nz lower upper : Bool)
    (flag : Option Bool) (rt : Option Label) :
    C.run code 3
      (atState (some (.control (.lowerFlag nz))) flag rt (P input candidate [] quo [lower] [upper] []))=
    some (atState (some (.control .cleanupInput)) (some upper) rt
      (P input candidate [] quo [] [] [((!lower) && upper) && !nz])) := by
  have h1 : C.run code 1
      (atState (some (.control (.lowerFlag nz))) flag rt (P input candidate [] quo [lower] [upper] []))=
      some (atState (some (.control (.upperFlag nz lower))) (some lower) rt (P input candidate [] quo [] [upper] [])) := by
    cases lower <;> simp [C.run,C.step,C.execute,atState,P,code,SemiprimeD1StackBytecode.choose,payload_lower]
  have h2 : C.run code 1
      (atState (some (.control (.upperFlag nz lower))) (some lower) rt (P input candidate [] quo [] [upper] []))=
      some (atState (some (.control (.finish (((!lower) && upper) && !nz)))) (some upper) rt
        (P input candidate [] quo [] [] [])) := by
    cases lower <;> cases upper <;> cases nz <;>
      simp [C.run,C.step,C.execute,atState,P,code,SemiprimeD1StackBytecode.choose,payload_upper]
  have h3 : C.run code 1
      (atState (some (.control (.finish (((!lower) && upper) && !nz)))) (some upper) rt
        (P input candidate [] quo [] [] []))=
      some (atState (some (.control .cleanupInput)) (some upper) rt
        (P input candidate [] quo [] [] [((!lower) && upper) && !nz])) := by
    simp [C.run,C.step,C.execute,atState,P,code,payload_valid]
  exact run_append 2 1 _ _ _ (run_append 1 1 _ _ _ h1 h2) h3

/-- Exact cleanup time of both persistent operands and the final halt. -/
theorem cleanup_run (input candidate quo : List Bool) (valid : Bool)
    (flag : Option Bool) (rt : Option Label) :
    C.run code (input.length+candidate.length+3)
      (atState (some (.control .cleanupInput)) flag rt (P input candidate [] quo [] [] [valid]))=
    some (atState none none none (P [] [] [] quo [] [] [valid])) := by
  have h1:=clear_input [] [] [] [] [] [] [] [] quo [] [] input candidate [] [] [] [] [valid] flag rt
  have h2:=clear_candidate [] [] [] [] [] [] [] [] quo [] [] [] candidate [] [] [] [] [valid] none rt
  have h3 : C.run code 1 (atState (some (.control .done)) none rt (P [] [] [] quo [] [] [valid]))=
      some (atState none none none (P [] [] [] quo [] [] [valid])) := rfl
  simpa only [atState,state,P,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    run_append _ _ _ _ _ (run_append _ _ _ _ _ h1 h2) h3

/-- Exact physical input/divisor acquisition plus actual nested division. -/
def divideClock (input candidate : List Bool) : ℕ :=
  (1+(5*input.length+3))+(1+(5*candidate.length+3))+
    (1+SemiprimeD1StackDividerExecution.executionTime input candidate)

/-- The zero guard's positive branch invokes the actual closed divider. -/
theorem divide_run (input candidate : List Bool) (flag : Option Bool) (rt : Option Label) :
    ∃ff rr,C.run code (divideClock input candidate)
      (atState (some (.control (.guardDone true))) flag rt (P input candidate [] [] [] [] []))=
    some (atState (some (.control .callLower)) ff rr
      (P input candidate (SemiprimeBitDivision.divideLoop input candidate).remainder
        (SemiprimeBitDivision.divideLoop input candidate).quotient [] [] [])) := by
  obtain ⟨f1,r1,h1⟩:=copy_call .input (.control (.guardDone true)) (.control .callDivisor) rfl
    (P input candidate [] [] [] [] []) rfl rfl flag rt
  simp only [copyInput,copyOutput,P,payload_get_input,payload_xs] at h1
  obtain ⟨f2,r2,h2⟩:=copy_call .divisor (.control .callDivisor) (.control .callDivider) rfl
    (payload input [] [] [] [] [] [] [] [] [] [] input candidate [] [] [] [] []) rfl rfl f1 r1
  simp only [copyInput,copyOutput,payload_get_candidate,payload_ys] at h2
  obtain ⟨ff,rr,h3⟩:=divider_call input candidate (extraData input candidate [] [] [] [] []) f2 r2
  simp only [join_payload] at h3
  refine ⟨ff,rr,?_⟩
  exact run_append _ _ _ _ _ (run_append _ _ _ _ _ h1 h2) h3

/-- Literal valid expression assembled by this physical execution. -/
def positiveFlag (input candidate : List Bool) : Bool :=
  (!(SemiprimeBitDivision.subBits candidate [false,true] false).borrow &&
    (SemiprimeBitDivision.subBits candidate input false).borrow) &&
    !(SemiprimeBitDivision.nonzeroBits (SemiprimeBitDivision.divideLoop input candidate).remainder).nonzero

/-- Exact physical positive-guard branch cost. -/
def positiveClock (input candidate : List Bool) : ℕ :=
  divideClock input candidate+lowerClock candidate+upperClock input candidate+
    ((SemiprimeBitDivision.divideLoop input candidate).remainder.length+1)+3+
    (input.length+candidate.length+3)

/-- Complete positive branch, retaining all producers, scans and operand cleanup. -/
theorem positive_run (input candidate : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (positiveClock input candidate)
      (atState (some (.control (.guardDone true))) flag rt (P input candidate [] [] [] [] []))=
    some (atState none none none
      (P [] [] [] (SemiprimeBitDivision.divideLoop input candidate).quotient [] [] [positiveFlag input candidate])) := by
  let result:=SemiprimeBitDivision.divideLoop input candidate
  let lb:=(SemiprimeBitDivision.subBits candidate [false,true] false).borrow
  let ub:=(SemiprimeBitDivision.subBits candidate input false).borrow
  obtain ⟨f1,r1,h1⟩:=divide_run input candidate flag rt
  obtain ⟨f2,r2,h2⟩:=lower_run input candidate result.remainder result.quotient f1 r1
  obtain ⟨f3,r3,h3⟩:=upper_run input candidate result.remainder result.quotient [lb] f2 r2
  have h4:=scan_remainder [] [] [] [] [] [] [] result.remainder result.quotient [] []
    input candidate [] [] [lb] [ub] [] false f3 r3
  simp only [Bool.false_or] at h4
  have h5:=flags_run input candidate result.quotient (SemiprimeBitDivision.nonzeroBits result.remainder).nonzero lb ub none r3
  have h6:=cleanup_run input candidate result.quotient (positiveFlag input candidate) (some ub) r3
  exact run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _
    (run_append _ _ _ _ _ h1 h2) h3) h4) h5) h6

/-- Actual zero-candidate branch: no divider invocation, empty cofactor, false valid bit. -/
theorem zero_run (input candidate : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run code (1+(input.length+candidate.length+3))
      (atState (some (.control (.guardDone false))) flag rt (P input candidate [] [] [] [] []))=
    some (atState none none none (P [] [] [] [] [] [] [false])) := by
  have h1 : C.run code 1
      (atState (some (.control (.guardDone false))) flag rt (P input candidate [] [] [] [] []))=
      some (atState (some (.control .cleanupInput)) flag rt (P input candidate [] [] [] [] [false])) := by
    simp [C.run,C.step,C.execute,atState,P,code,payload_valid]
  exact run_append _ _ _ _ _ h1 (cleanup_run input candidate [] false flag rt)

/-- Positive guard connects the actual branch bytes to the original validation outputs. -/
theorem positive_outputs (input candidate : List Bool)
    (hc : (SemiprimeBitDivision.nonzeroBits candidate).nonzero=true) :
    positiveFlag input candidate=(SemiprimeD1FactorValidationBits.run input candidate).valid ∧
    (SemiprimeBitDivision.divideLoop input candidate).quotient=
      (SemiprimeD1FactorValidationBits.run input candidate).cofactor := by
  simp [positiveFlag,SemiprimeD1FactorValidationBits.run,SemiprimeBitPrimeScan.orderWords,
    SemiprimeBitDivision.divideBits,hc]

/-- A physically acquired zero guard forces exactly the original false/empty fallback. -/
theorem zero_outputs (input candidate : List Bool)
    (hc : (SemiprimeBitDivision.nonzeroBits candidate).nonzero=false) :
    (SemiprimeD1FactorValidationBits.run input candidate).valid=false ∧
    (SemiprimeD1FactorValidationBits.run input candidate).cofactor=[] := by
  have hz:=(SemiprimeBitPrimeScan.nonzeroBits_false_iff candidate).mp hc
  have hl : (SemiprimeBitPrimeScan.orderWords candidate [false,true]).difference.borrow=true :=
    (SemiprimeBitPrimeScan.orderWords_less candidate [false,true]).mpr (by rw [hz]; decide)
  simp [SemiprimeD1FactorValidationBits.run,hl,SemiprimeBitDivision.divideBits,hc]

/-- Exact trace count of this physical implementation, including its acquired zero branch. -/
def executionTime (input candidate : List Bool) : ℕ :=
  (1+(5*candidate.length+3))+(candidate.length+1)+
    (if (SemiprimeBitDivision.nonzeroBits candidate).nonzero then positiveClock input candidate
      else 1+(input.length+candidate.length+3))

/-- Closed all-input execution computes the original valid flag AND exact cofactor bytes. -/
theorem source_run (input candidate : List Bool) :
    C.run code (executionTime input candidate)
      (atState (some (.control .start)) none none (P input candidate [] [] [] [] []))=
    some (atState none none none
      (P [] [] [] (SemiprimeD1FactorValidationBits.run input candidate).cofactor [] []
        [(SemiprimeD1FactorValidationBits.run input candidate).valid])) := by
  obtain ⟨ff,rr,h1⟩:=copy_call .guard (.control .start) (.control (.scanGuard false)) rfl
    (P input candidate [] [] [] [] []) rfl rfl none none
  simp only [copyInput,copyOutput,P,payload_get_candidate,payload_guard] at h1
  have h2:=scan_guard [] [] [] [] [] [] [] [] [] [] [] input candidate candidate [] [] [] [] false ff rr
  simp only [Bool.false_or] at h2
  have hp:=run_append _ _ _ _ _ h1 h2
  cases hc:(SemiprimeBitDivision.nonzeroBits candidate).nonzero with
  | false =>
    have hf:=zero_run input candidate none rr
    rw [(zero_outputs input candidate hc).1,(zero_outputs input candidate hc).2]
    simp only [hc] at hp
    simpa only [P,executionTime,hc,Bool.false_eq_true,ite_false] using run_append _ _ _ _ _ hp hf
  | true =>
    have hf:=positive_run input candidate none rr
    rw [(positive_outputs input candidate hc).1,(positive_outputs input candidate hc).2] at hf
    simp only [hc] at hp
    simpa only [P,executionTime,hc,ite_true] using run_append _ _ _ _ _ hp hf

/-- Actual comparison stage is linear in its physical operand widths. -/
theorem subClock_le (left right : List Bool) :
    subClock left right ≤ 10*(left.length+right.length+2) := by
  have hh:=(SemiprimeBitDivision.subBits_counts left right false).2.2.2.2
  unfold subClock
  omega

/-- The lower stage has an original-width bound, with no supplied comparison flag. -/
theorem lowerClock_le (candidate : List Bool) : lowerClock candidate ≤ 30*(candidate.length+2) := by
  have hs:=subClock_le candidate [false,true]
  have hd:=(SemiprimeBitDivision.subBits_counts candidate [false,true] false).2.2.2.2
  simp only [List.length_cons,List.length_nil] at *
  unfold lowerClock
  omega

/-- The upper stage has a fixed linear bound in the actual original binary widths. -/
theorem upperClock_le (input candidate : List Bool) :
    upperClock input candidate ≤ 30*(input.length+candidate.length+2) := by
  have hs:=subClock_le candidate input
  have hd:=(SemiprimeBitDivision.subBits_counts candidate input false).2.2.2.2
  unfold upperClock
  omega

/-- Complete explicit bit-length budget; the divider's actual quadratic budget is retained. -/
def timeBound (n m : ℕ) : ℕ := SemiprimeD1StackDividerExecution.timeBound n m+200*(n+m+3)

/-- Every physical branch fits the same original-input quadratic bound. -/
theorem source_time (input candidate : List Bool) : executionTime input candidate ≤ timeBound input.length candidate.length := by
  have hd:=SemiprimeD1StackDividerExecution.source_time input candidate
  have hl:=lowerClock_le candidate
  have hu:=upperClock_le input candidate
  have hr:=(SemiprimeBitDivision.divideLoop_widths input candidate).1
  unfold executionTime timeBound positiveClock divideClock
  split <;> omega

/-- Actual source-transition certificate; all outputs are produced, never supplied. -/
def sourceValidate (input candidate : List Bool) :
    StateTransition.EvalsToInTime (C.step code)
      (atState (some (.control .start)) none none (P input candidate [] [] [] [] []))
      (some (atState none none none
        (P [] [] [] (SemiprimeD1FactorValidationBits.run input candidate).cofactor [] []
          [(SemiprimeD1FactorValidationBits.run input candidate).valid])))
      (timeBound input.length candidate.length) :=
  ⟨⟨_,source_run input candidate⟩,source_time input candidate⟩

/-- Actual fixed FinTM2 validator; its declared result pair is flag and binary cofactor. -/
def machineValidate (input candidate : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (atState (some (.control .start)) none none (P input candidate [] [] [] [] [])))
      (some (SemiprimeD1StackCalls.configuration (atState none none none
        (P [] [] [] (SemiprimeD1FactorValidationBits.run input candidate).cofactor [] []
          [(SemiprimeD1FactorValidationBits.run input candidate).valid]))))
      (timeBound input.length candidate.length) :=
  SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label)
    (Sum.inr Aux.input) (Sum.inr Aux.valid) (Label.control Control.start) code _ _ _
    (sourceValidate input candidate)

/-- Every source prefix counts all eighteen Boolean stacks and the real return stack. -/
theorem prefix_cells (input candidate : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run code fuel (atState (some (.control .start)) none none (P input candidate [] [] [] [] []))=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 19*(input.length+candidate.length+fuel) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound code fuel (input.length+candidate.length)
    _ out (by
      intro k
      rcases k with k|k
      · rcases k with k|k
        · cases k <;> simp [atState,P,payload,SemiprimeD1StackDivider.payload]
        · cases k <;> simp [atState,P,payload,SemiprimeD1StackDivider.payload]
      · cases k <;> simp [atState,P,payload]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound code fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k:Stack,(out.data k).length) ≤ 18*(input.length+candidate.length+fuel) := by
    calc
      _ ≤ ∑_k:Stack,(input.length+candidate.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = 18*(input.length+candidate.length+fuel) := by
        have ha : Fintype.card SemiprimeD1StackAdder.Stack=4 := by decide
        have hb : Fintype.card SemiprimeD1StackDivider.Aux=7 := by decide
        have hc : Fintype.card Aux=7 := by decide
        simp [Stack,SemiprimeD1StackDivider.Stack,ha,hb,hc]
  omega

/-- A successful prefix cannot continue beyond the actual proved halt. -/
theorem prefix_fuel_le (input candidate : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run code fuel (atState (some (.control .start)) none none (P input candidate [] [] [] [] []))=some out) :
    fuel ≤ executionTime input candidate := by
  by_contra hn
  have he : fuel=executionTime input candidate+(1+(fuel-(executionTime input candidate+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hh : C.run code 1 (atState none none none
      (P [] [] [] (SemiprimeD1FactorValidationBits.run input candidate).cofactor [] []
        [(SemiprimeD1FactorValidationBits.run input candidate).valid]))=none := rfl
  rw [hh,Option.bind_none] at hr
  cases hr

/-- Every successful source prefix has a fixed input-polynomial space bound. -/
theorem prefix_polynomial_cells (input candidate : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run code fuel (atState (some (.control .start)) none none (P input candidate [] [] [] [] []))=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      19*(input.length+candidate.length+timeBound input.length candidate.length) := by
  have hf:=(prefix_fuel_le input candidate fuel out hr).trans (source_time input candidate)
  exact (prefix_cells input candidate fuel out hr).trans (by omega)

/-- Actual target-machine prefixes satisfy the same bound without a supplied fuel cap. -/
theorem machine_prefix_polynomial_cells (input candidate : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (atState (some (.control .start)) none none (P input candidate [] [] [] [] []))))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      19*(input.length+candidate.length+timeBound input.length candidate.length) := by
  let start:=atState (some (.control .start)) none none (P input candidate [] [] [] [] [])
  have he:=SemiprimeD1StackCalls.run_correct (Sum.inr Aux.input) (Sum.inr Aux.valid)
    (.control .start) code fuel start
  change (C.run code fuel start).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  cases hc:C.run code fuel start with
  | none => rw [hc,hr] at he; cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    rw [←hcfg]
    exact prefix_polynomial_cells input candidate fuel out hc

/-- The concrete transition bound is one fixed quadratic monomial. -/
theorem timeBound_le_square (n m : ℕ) : timeBound n m ≤ 2000*(n+m+3)^2 := by
  have hd:=SemiprimeD1StackDividerExecution.timeBound_le_square n m
  unfold timeBound
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (m*m),Nat.zero_le (n*m)]

end RiemannGaussian.SemiprimeD1StackFactorValidationExecution
