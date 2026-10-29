/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMacroEntryBitPrimitives
import RiemannGaussian.SemiprimeCountRecovery

/-! # Exact ternary lift of the original Boolean factor network
Symbol2 is rejected on existing local scopes. Coverage of the ORIGINAL variables
forces every globally accepted symbol to be Boolean; no new factors or ports occur.
The exact count below is a natural cardinality, not a count reduced modulo3.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeTernaryFactor
open scoped BigOperators
open SemiprimeMacroEntryBitPrimitives SemiprimeCountRecovery

/-- Literal embedding of the two Boolean symbols into the ternary alphabet. -/
def embed : Bool → Fin 3 | false => 0 | true => 1
/-- Literal Boolean projection; symbol2 projects false but is rejected first. -/
def project (x : Fin 3) : Bool := decide (x.val=1)
/-- Exactly the two original symbols, not a field-valued side condition. -/
def isBoolean (x : Fin 3) : Prop := x.val<2

instance (x : Fin 3) : Decidable (isBoolean x) := inferInstanceAs (Decidable (x.val < 2))

@[simp] theorem project_embed (b : Bool) : project (embed b)=b := by cases b <;> decide
@[simp] theorem embed_isBoolean (b : Bool) : isBoolean (embed b) := by cases b <;> decide

theorem embed_project (x : Fin 3) (h : isBoolean x) : embed (project x)=x := by
  apply Fin.ext
  unfold isBoolean at h
  by_cases hx : x.val=1
  · simp [project,embed,hx]
  · have hz : x.val=0 := by omega
    simp [project,embed,hz]

/-- A complete finite admissibility scan; every symbol test is retained/charged. -/
def scan : (w : ℕ) → (Fin w → Fin 3) → CheckRun
  | 0,_ => ⟨true,1⟩
  | w+1,input =>
      let tail := scan w (fun i => input i.succ)
      ⟨decide (isBoolean (input 0)) && tail.accepted,tail.clock+4⟩

/-- All local occurrences, including repeated ports, are checked for symbol2. -/
theorem scan_correct (w : ℕ) (input : Fin w → Fin 3) :
    (scan w input).accepted=true ↔ ∀ i, isBoolean (input i) := by
  induction w with
  | zero => simp [scan]
  | succ w ih =>
    simp only [scan,Bool.and_eq_true,decide_eq_true_eq,ih]
    exact ⟨fun h i => Fin.cases h.1 h.2 i,fun h => ⟨h 0,fun i => h i.succ⟩⟩

/-- The actual finite scan has linear alphabet-test/control cost. -/
theorem scan_clock (w : ℕ) (input : Fin w → Fin 3) : (scan w input).clock=4*w+1 := by
  induction w with
  | zero => rfl
  | succ w ih => simp only [scan,ih]; omega

/-- Reject2 before calling the original paid Boolean checker on the SAME ports. -/
def liftChecker (w : ℕ) (base : (Fin w → Bool) → CheckRun) (input : Fin w → Fin 3) : CheckRun :=
  let allowed := scan w input
  if allowed.accepted then
    let original := base (fun i => project (input i))
    ⟨original.accepted,allowed.clock+original.clock+1⟩
  else ⟨false,allowed.clock+1⟩

/-- The lifted checker is exactly the zero extension of the Boolean checker. -/
theorem liftChecker_correct (w : ℕ) (base : (Fin w → Bool) → CheckRun) (input : Fin w → Fin 3) :
    (liftChecker w base input).accepted=true ↔
      (∀ i, isBoolean (input i)) ∧ (base (fun i => project (input i))).accepted=true := by
  unfold liftChecker
  dsimp only
  split_ifs with h
  · simp only [scan_correct] at h
    exact ⟨fun hb => ⟨h,hb⟩,fun hb => hb.2⟩
  · have hn : ¬∀ i, isBoolean (input i) := by
      intro ha
      exact h ((scan_correct w input).mpr ha)
    simp [hn]

/-- The original checker is called once only after success of the scan. -/
theorem liftChecker_clock (w : ℕ) (base : (Fin w → Bool) → CheckRun) (input : Fin w → Fin 3) (E : ℕ)
    (h : ∀ bits, (base bits).clock ≤ E) : (liftChecker w base input).clock ≤ 4*w+E+2 := by
  unfold liftChecker
  dsimp only
  split_ifs <;> simp only [scan_clock] <;> have hb := h (fun i => project (input i)) <;> omega

/-- The standard finite-field alphabet identification, with no field-sum count claim. -/
def fieldEquiv : Fin 3 ≃ ZMod 3 := (ZMod.finEquiv 3).toEquiv

/-- Prefix restrictions are checked on existing ports, without adding unary tensors. -/
def prefixChecker {A : Type} [DecidableEq A] (w : ℕ) (coordinate : Fin w → A)
    (base : (Fin w → Bool) → CheckRun) (fixed : List (A × Bool))
    (input : Fin w → Bool) : CheckRun :=
  let original := base input
  let gate := fixed.all (fun pair => (List.finRange w).all
    (fun i => decide (coordinate i=pair.1 → input i=pair.2)))
  ⟨original.accepted && gate,original.clock+fixed.length*(3*w+2)+1⟩

/-- The executed prefix gate is exactly the finite port constraint. -/
theorem prefixChecker_correct {A : Type} [DecidableEq A] (w : ℕ) (coordinate : Fin w → A)
    (base : (Fin w → Bool) → CheckRun) (fixed : List (A × Bool)) (input : Fin w → Bool) :
    (prefixChecker w coordinate base fixed input).accepted=true ↔
      (base input).accepted=true ∧ ∀ pair ∈ fixed, ∀ i, coordinate i=pair.1 → input i=pair.2 := by
  simp only [prefixChecker,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,
    List.mem_finRange,true_implies]

section Network
variable {A E : Type} [Fintype A] [DecidableEq A] [Fintype E]

/-- The original local checker conjunction, on Boolean function assignments. -/
def booleanPredicate (arity : E → ℕ) (base : (e : E) → (Fin (arity e) → Bool) → CheckRun)
    (coordinate : (e : E) → Fin (arity e) → A) (x : A → Bool) : Bool :=
  decide (∀ e, (base e (fun i => x (coordinate e i))).accepted=true)

/-- Literal ternary global predicate; local arities and coordinates are unchanged. -/
def ternaryPredicate (arity : E → ℕ) (base : (e : E) → (Fin (arity e) → Bool) → CheckRun)
    (coordinate : (e : E) → Fin (arity e) → A) (x : A → Fin 3) : Bool :=
  decide (∀ e, (liftChecker (arity e) (base e) (fun i => x (coordinate e i))).accepted=true)

omit [Fintype A] [DecidableEq A] in
/-- ORIGINAL variable coverage turns local rejection into global Boolean support. -/
theorem ternary_accept_iff (arity : E → ℕ)
    (base : (e : E) → (Fin (arity e) → Bool) → CheckRun)
    (coordinate : (e : E) → Fin (arity e) → A) (coverage : ∀ a, ∃ e i, coordinate e i=a)
    (x : A → Fin 3) : ternaryPredicate arity base coordinate x=true ↔
      (∀ a, isBoolean (x a)) ∧ booleanPredicate arity base coordinate (fun a => project (x a))=true := by
  simp only [ternaryPredicate,booleanPredicate,decide_eq_true_eq,liftChecker_correct]
  constructor
  · intro h
    refine ⟨?_,fun e => (h e).2⟩
    intro a
    obtain ⟨e,i,hi⟩ := coverage a
    simpa only [hi] using (h e).1 i
  · rintro ⟨ha,hb⟩ e
    exact ⟨fun i => ha _,hb e⟩

/-- Accepted ternary assignments correspond one-for-one to original Boolean assignments. -/
def acceptedEquiv (arity : E → ℕ) (base : (e : E) → (Fin (arity e) → Bool) → CheckRun)
    (coordinate : (e : E) → Fin (arity e) → A) (coverage : ∀ a, ∃ e i, coordinate e i=a) :
    {x : A → Fin 3 // ternaryPredicate arity base coordinate x=true} ≃
      {x : A → Bool // booleanPredicate arity base coordinate x=true} where
  toFun x := ⟨fun a => project (x.val a),(ternary_accept_iff arity base coordinate coverage x.val).mp x.property |>.2⟩
  invFun x := ⟨fun a => embed (x.val a),(ternary_accept_iff arity base coordinate coverage _).mpr
    ⟨fun a => embed_isBoolean _,by simpa only [project_embed] using x.property⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext a
    exact embed_project _ (((ternary_accept_iff arity base coordinate coverage x.val).mp x.property).1 a)
  right_inv x := by apply Subtype.ext; funext a; exact project_embed _

/-- Cardinality of a literal Boolean predicate equals its accepted subtype. -/
theorem acceptedCount_eq_card {X : Type} [Fintype X] (P : X → Bool) :
    acceptedCount P=Fintype.card {x // P x=true} := by
  classical
  simp [acceptedCount,Fintype.card_subtype]

/-- Exact NATURAL count preservation; no reduction modulo3 is being asserted as a decoder. -/
theorem ternary_count_boolean (arity : E → ℕ)
    (base : (e : E) → (Fin (arity e) → Bool) → CheckRun)
    (coordinate : (e : E) → Fin (arity e) → A) (coverage : ∀ a, ∃ e i, coordinate e i=a) :
    acceptedCount (ternaryPredicate arity base coordinate)=acceptedCount (booleanPredicate arity base coordinate) := by
  classical
  rw [acceptedCount_eq_card,acceptedCount_eq_card]
  exact Fintype.card_congr (acceptedEquiv arity base coordinate coverage)

/-- The old finite-set assignment representation is just the Boolean function representation. -/
def booleanAssignments : Finset A ≃ (A → Bool) where
  toFun x := fun a => decide (a∈x)
  invFun x := Finset.univ.filter (fun a => x a=true)
  left_inv x := by ext a; simp
  right_inv x := by funext a; simp

/-- Coverage proves that the SAME-scope prefix checker enforces the original global prefix. -/
theorem boolean_prefix_iff (arity : E → ℕ)
    (base : (e : E) → (Fin (arity e) → Bool) → CheckRun)
    (coordinate : (e : E) → Fin (arity e) → A) (coverage : ∀ a, ∃ e i, coordinate e i=a)
    (fixed : List (A × Bool)) (x : A → Bool) :
    booleanPredicate arity (fun e => prefixChecker (arity e) (coordinate e) (base e) fixed)
      coordinate x=true ↔
      booleanPredicate arity base coordinate x=true ∧ ∀ pair ∈ fixed, x pair.1=pair.2 := by
  simp only [booleanPredicate,decide_eq_true_eq,prefixChecker_correct]
  constructor
  · intro h
    refine ⟨fun e => (h e).1,?_⟩
    intro pair hp
    obtain ⟨e,i,hi⟩ := coverage pair.1
    simpa only [hi] using (h e).2 pair hp i hi
  · rintro ⟨h,hp⟩ e
    refine ⟨h e,?_⟩
    intro pair hm i hi
    simpa only [hi] using hp pair hm

/-- Prefix counting remains exact with no added scopes or occurrences. -/
theorem ternary_prefix_count (arity : E → ℕ)
    (base : (e : E) → (Fin (arity e) → Bool) → CheckRun)
    (coordinate : (e : E) → Fin (arity e) → A) (coverage : ∀ a, ∃ e i, coordinate e i=a)
    (fixed : List (A × Bool)) :
    acceptedCount (ternaryPredicate arity
      (fun e => prefixChecker (arity e) (coordinate e) (base e) fixed) coordinate)=
    acceptedCount (restricted (fun x a => x a) (booleanPredicate arity base coordinate) fixed) := by
  rw [ternary_count_boolean arity _ coordinate coverage]
  congr 1
  funext x
  apply Bool.eq_iff_iff.mpr
  rw [boolean_prefix_iff arity base coordinate coverage]
  simp [restricted,List.all_eq_true]

/-- Boolean indicator conjunction is exactly the literal tensor product. -/
theorem boolean_count_tensor (arity : E → ℕ)
    (base : (e : E) → (Fin (arity e) → Bool) → CheckRun)
    (coordinate : (e : E) → Fin (arity e) → A) :
    acceptedCount (booleanPredicate arity base coordinate)=
      ∑ x : A → Bool, ∏ e : E,
        if (base e (fun i => x (coordinate e i))).accepted then (1 : ℕ) else 0 := by
  classical
  unfold acceptedCount
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : ∀ e, (base e (fun i => x (coordinate e i))).accepted=true
  · simp [booleanPredicate,h]
  · obtain ⟨e,he⟩ := not_forall.mp h
    have hz : (base e (fun i => x (coordinate e i))).accepted=false := Bool.eq_false_iff.mpr he
    have hp : (∏ e : E, if (base e (fun i => x (coordinate e i))).accepted then (1 : ℕ) else 0)=0 :=
      Finset.prod_eq_zero (Finset.mem_univ e) (by simp [hz])
    simp only [booleanPredicate,decide_eq_false h,Bool.false_eq_true,ite_false,hp]

end Network
end RiemannGaussian.SemiprimeTernaryFactor
