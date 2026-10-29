/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceLayout

/-!
# Computable finite lists for the native source layout

All data definitions use explicit lists, constructors and finite-domain function
recursion. Classical reasoning is confined to erased proof fields/theorems.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeFiniteEnumerations
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes

/-- Literal ascending Fin enumeration. -/
def fin (n : ℕ) : FiniteEnumeration (Fin n) :=
  ⟨List.finRange n, List.nodup_finRange n, List.mem_finRange⟩

/-- Transport through a supplied computable equivalence. -/
def transport {A B : Type*} (e : FiniteEnumeration A) (f : A ≃ B) : FiniteEnumeration B where
  values := e.values.map f
  nodup := e.nodup.map f.injective
  complete b := List.mem_map.mpr ⟨f.symm b,e.complete _,f.apply_symm_apply b⟩

/-- Explicit disjoint sum, with all left entries before all right entries. -/
def sum {A B : Type*} (a : FiniteEnumeration A) (b : FiniteEnumeration B) : FiniteEnumeration (A ⊕ B) where
  values := a.values.map Sum.inl ++ b.values.map Sum.inr
  nodup := by
    apply List.nodup_append.mpr
    refine ⟨a.nodup.map Sum.inl_injective,b.nodup.map Sum.inr_injective,?_⟩
    intro x hx y hy hxy
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hy
    cases hxy
  complete x := by
    cases x with
    | inl x => exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨x,a.complete x,rfl⟩))
    | inr x => exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨x,b.complete x,rfl⟩))

/-- Explicit Cartesian pair list, with its original lexicographic order. -/
def prod {A B : Type*} (a : FiniteEnumeration A) (b : FiniteEnumeration B) : FiniteEnumeration (A × B) where
  values := a.values.product b.values
  nodup := a.nodup.product b.nodup
  complete x := List.mem_product.mpr ⟨a.complete x.1,b.complete x.2⟩

/-- Dependent finite incidence enumeration, without an abstract finite inverse. -/
def sigma {A : Type*} {B : A → Type*} (a : FiniteEnumeration A)
    (b : (i : A) → FiniteEnumeration (B i)) : FiniteEnumeration (Sigma B) where
  values := a.values.flatMap (fun i => (b i).values.map (Sigma.mk i))
  nodup := by
    apply List.nodup_flatMap.mpr
    constructor
    · intro i _
      apply (b i).nodup.map
      intro x y h
      cases h
      rfl
    · apply a.nodup.imp
      intro i j hij
      apply List.disjoint_left.mpr
      intro z hz hz'
      obtain ⟨x,_,hx⟩ := List.mem_map.mp hz
      obtain ⟨y,_,hy⟩ := List.mem_map.mp hz'
      exact hij (congrArg Sigma.fst (hx.trans hy.symm))
  complete x := List.mem_flatMap.mpr ⟨x.1,a.complete _,List.mem_map.mpr ⟨x.2,(b x.1).complete _,rfl⟩⟩

/-- All functions on a finite Fin domain, by finite head/tail recursion. -/
def pi : (n : ℕ) → {B : Fin n → Type*} → ((i : Fin n) → FiniteEnumeration (B i)) →
    FiniteEnumeration ((i : Fin n) → B i)
  | 0, _, _ => ⟨[fun i => Fin.elim0 i],by simp,by
      intro f
      have h : f=(fun i => Fin.elim0 i) := by funext i; exact Fin.elim0 i
      simp [h]⟩
  | n+1, B, es => transport (prod (es 0) (pi n (fun i => es i.succ))) (Fin.consEquiv B)

@[simp] theorem fin_length (n : ℕ) : (fin n).values.length=n := by simp [fin]

@[simp] theorem transport_length {A B : Type*} (e : FiniteEnumeration A) (f : A ≃ B) :
    (transport e f).values.length=e.values.length := by simp only [transport, List.length_map]

@[simp] theorem sum_length {A B : Type*} (a : FiniteEnumeration A) (b : FiniteEnumeration B) :
    (sum a b).values.length=a.values.length+b.values.length := by simp [sum]

@[simp] theorem prod_length {A B : Type*} (a : FiniteEnumeration A) (b : FiniteEnumeration B) :
    (prod a b).values.length=a.values.length*b.values.length := List.length_product _ _

/-- Exact dependent incidence-list size. -/
theorem sigma_length {A : Type*} {B : A → Type*} (a : FiniteEnumeration A)
    (b : (i : A) → FiniteEnumeration (B i)) :
    (sigma a b).values.length=(a.values.map (fun i => (b i).values.length)).sum := by
  simp [sigma, List.length_flatMap]

/-- The function list has the exact finite Cartesian-product size. -/
theorem pi_length (n : ℕ) {B : Fin n → Type*} (es : (i : Fin n) → FiniteEnumeration (B i)) :
    (pi n es).values.length=∏ i, (es i).values.length := by
  induction n with
  | zero => simp [pi]
  | succ n ih => simp only [pi, transport_length, prod_length, ih, Fin.prod_univ_succ]

/-- The actual r^Q source word list. -/
def words (r Q : ℕ) : FiniteEnumeration (Word r Q) := pi Q (fun _ => fin r)

/-- The actual universal incidence alphabet for one slot. -/
def universal (r Q : ℕ) : FiniteEnumeration (UniversalType r Q 1) :=
  transport (prod (words r Q) (pi 1 (fun _ => words r Q))) (equivProd r Q 1).symm

/-- All actual score terms, including repetitions in the original incidences. -/
def scoreTerms {I V : Type} (inc : FiniteEnumeration I) (vars : FiniteEnumeration V) (Q : ℕ) :
    FiniteEnumeration (SqrtLog.Packing.ScoreTerm I V Q) :=
  sum (prod inc inc) (prod (fin Q) (prod vars vars))

/-- Explicit source data from original incidence, variable and factor lists. -/
def sourceEnumerations {I V E : Type}
    (inc : FiniteEnumeration I) (vars : FiniteEnumeration V) (factors : FiniteEnumeration E)
    (r Q : ℕ) [NeZero r] : SemiprimeSourceLayout.Enumerations I V E r Q where
  incidences := inc
  types := universal r Q
  wordFirst := fun _ => 0
  wordTail := (words r Q).values.filter (fun w => decide (w ≠ fun _ => 0))
  words_nodup := by
    apply List.nodup_cons.mpr
    constructor
    · simp
    · exact (words r Q).nodup.filter _
  words_complete w := by
    by_cases hw : w=(fun _ => 0)
    · simp only [List.mem_cons, hw, true_or]
    · exact List.mem_cons.mpr (Or.inr (List.mem_filter.mpr ⟨(words r Q).complete w,by simpa using hw⟩))
  terms := scoreTerms inc vars Q
  indices := sum vars factors

/-- Complete original dependent ports of an explicit indexed network. -/
def indexedIncidences (m : ℕ) (arity : Fin m → ℕ) : FiniteEnumeration ((e : Fin m) × Fin (arity e)) :=
  sigma (fin m) (fun e => fin (arity e))

/-- Fully specified lists for an original Fin-indexed Boolean network. -/
def indexed (n m r Q : ℕ) [NeZero r] (arity : Fin m → ℕ) :
    SemiprimeSourceLayout.Enumerations ((e : Fin m) × Fin (arity e)) (Fin n) (Fin m) r Q :=
  sourceEnumerations (indexedIncidences m arity) (fin n) (fin m) r Q

/-- Exact computed word-alphabet length. -/
theorem words_length (r Q : ℕ) : (words r Q).values.length=r^Q := by
  rw [FiniteEnumeration.length_eq_card]
  exact card_word r Q

/-- Exact computed universal-type alphabet length. -/
theorem universal_length (r Q : ℕ) : (universal r Q).values.length=r^(2*Q) := by
  rw [FiniteEnumeration.length_eq_card, card_universalType]
  congr 1
  omega

/-- Exact original indexed incidence count. -/
theorem indexedIncidences_length (m : ℕ) (arity : Fin m → ℕ) :
    (indexedIncidences m arity).values.length=∑ e, arity e := by
  rw [FiniteEnumeration.length_eq_card]
  simp

section Search
variable {I V E : Type} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E] {r Q : ℕ} [NeZero r]

/-- Compiled conditional-expectation data path. No noncomputable SourceLayout
wrapper is called; finite type dictionaries and all lists are explicit inputs. -/
def searchWords (owner : I → V) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) (ε : ℚ) :
    SqrtLog.Packing.WordAssignment V E r Q :=
  SqrtLog.Packing.computedWords owner factor en.wordFirst en.wordTail en.terms.values en.indices.values
    (ε*(Fintype.card I : ℚ)/(Fintype.card (UniversalType r Q 1) : ℚ))
    ((Fintype.card V : ℚ)/(2*(r : ℚ)))

omit [Fintype E] [DecidableEq I] [NeZero r] in
/-- The compiled word search is literally the one used by the proved layout. -/
theorem searchWords_eq (owner : I → V) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) (ε : ℚ) :
    searchWords owner factor en ε=SemiprimeSourceLayout.searchedWords owner factor en ε := rfl

/-- Compiled complete buckets, minimum scans, lookup and literal leftovers. -/
def searchPacking (owner : I → V) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) (ε : ℚ) :
    PackingData I (UniversalType r Q 1) :=
  SqrtLog.Packing.computedPacking owner factor en.incidences en.types en.wordFirst en.wordTail
    en.terms.values en.indices.values
    (ε*(Fintype.card I : ℚ)/(Fintype.card (UniversalType r Q 1) : ℚ))
    ((Fintype.card V : ℚ)/(2*(r : ℚ)))

omit [Fintype E] [DecidableEq I] [NeZero r] in
/-- The compiled packing is the layout's actual searched packing on these lists. -/
theorem searchPacking_eq (owner : I → V) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) (ε : ℚ) :
    searchPacking owner factor en ε=SemiprimeSourceLayout.searchedPacking owner factor en ε := rfl

/-- The source instrumentation runs the same compiled local word computations. -/
def searchWordsCounted (owner : I → V) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) (ε : ℚ) :
    SqrtLog.Packing.WordAssignment V E r Q × ℕ :=
  SqrtLog.Packing.computedWordsCounted owner factor en.wordFirst en.wordTail en.terms.values en.indices.values
    (ε*(Fintype.card I : ℚ)/(Fintype.card (UniversalType r Q 1) : ℚ))
    ((Fintype.card V : ℚ)/(2*(r : ℚ)))

omit [Fintype E] [DecidableEq I] [NeZero r] in
/-- The operationally counted word result is the actual uncounted result. -/
theorem searchWordsCounted_value (owner : I → V) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) (ε : ℚ) :
    (searchWordsCounted owner factor en ε).1=searchWords owner factor en ε :=
  SqrtLog.Packing.computedWordsCounted_value owner factor _ _ _ _ _ _

omit [Fintype E] [DecidableEq I] [NeZero r] in
/-- Actual local-term evaluation count, not a supplied exponential computation. -/
theorem searchWordsCounted_calls (owner : I → V) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) (ε : ℚ) :
    (searchWordsCounted owner factor en ε).2 ≤
      en.indices.values.length*(2*en.wordTail.length*(en.terms.values.length*(en.wordFirst::en.wordTail).length^4)) :=
  SqrtLog.Packing.computedWordsCounted_calls_le owner factor _ _ _ _ _ _

end Search

/-- A fully compiled original indexed-network word supplier. -/
def indexedWords (n m r Q : ℕ) [NeZero r] (arity : Fin m → ℕ)
    (coordinate : (e : Fin m) → Fin (arity e) → Fin n) (ε : ℚ) :
    SqrtLog.Packing.WordAssignment (Fin n) (Fin m) r Q :=
  searchWords (fun i : (e : Fin m) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst
    (indexed n m r Q arity) ε

/-- A fully compiled original indexed-network complete-bucket supplier. -/
def indexedPacking (n m r Q : ℕ) [NeZero r] (arity : Fin m → ℕ)
    (coordinate : (e : Fin m) → Fin (arity e) → Fin n) (ε : ℚ) :
    PackingData ((e : Fin m) × Fin (arity e)) (UniversalType r Q 1) :=
  searchPacking (fun i : (e : Fin m) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst
    (indexed n m r Q arity) ε

end RiemannGaussian.SemiprimeFiniteEnumerations

#print axioms RiemannGaussian.SemiprimeFiniteEnumerations.searchPacking_eq
#print axioms RiemannGaussian.SemiprimeFiniteEnumerations.searchWordsCounted_calls
