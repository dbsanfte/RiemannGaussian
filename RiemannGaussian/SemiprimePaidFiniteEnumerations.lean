/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePaidFiniteEnumerationLists

/-! # Paid original indexed source enumeration
All incidence, word, universal, score and index lists are literally acquired.
The old enumeration appears only in correctness proofs, never as a value oracle.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimePaidFiniteEnumerations
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes Subexp.ConstructivePacking SqrtLog
open SemiprimeMaterializedSourceUniversal
open SemiprimePaidFiniteEnumerationLists

/-- One factor's actual dependent port list, including its metadata read. -/
def ports {F : ℕ} (arity : Fin F → ℕ) (e : Fin F) : Run (List ((e : Fin F) × Fin (arity e))) :=
  let indices := fin (arity e)
  let out := collect (fun i => (⟨Sigma.mk e i,1⟩ : Run ((e : Fin F) × Fin (arity e)))) indices.value
  ⟨out.value,indices.work+out.work+2⟩

/-- All actual incidences in the exact original factor-major order. -/
def incidences (F : ℕ) (arity : Fin F → ℕ) : Run (List ((e : Fin F) × Fin (arity e))) :=
  let factors := fin F
  let out := flat (ports arity) factors.value
  ⟨out.value,factors.work+out.work+1⟩

theorem ports_value {F : ℕ} (arity : Fin F → ℕ) (e : Fin F) :
    (ports arity e).value=(List.finRange (arity e)).map (Sigma.mk e) := by
  simp only [ports,collect_value,fin_value]

theorem incidences_value (F : ℕ) (arity : Fin F → ℕ) :
    (incidences F arity).value=(SemiprimeFiniteEnumerations.indexedIncidences F arity).values := by
  simp only [incidences,flat_value,fin_value,ports_value]
  rfl

@[simp] theorem incidences_length (F : ℕ) (arity : Fin F → ℕ) :
    (incidences F arity).value.length=∑ e, arity e := by
  rw [incidences_value,SemiprimeFiniteEnumerations.indexedIncidences_length]

/-- Finite dependent acquisition budget in factor count and total original incidence. -/
def incidenceBudget (F M : ℕ) : ℕ := 3*(F+1)^2+F*(3*(M+1)^2+4*M+5)+2

theorem incidences_work (F : ℕ) (arity : Fin F → ℕ) :
    (incidences F arity).work ≤ incidenceBudget F (∑ e, arity e) := by
  let M := ∑ e, arity e
  have hm (e : Fin F) : arity e ≤ M := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
  have hp (e : Fin F) : (ports arity e).work ≤ 3*(M+1)^2+3*M+3 := by
    have hf := fin_work (arity e)
    have hmap := collect_work (fun i => (⟨Sigma.mk e i,1⟩ : Run ((e : Fin F) × Fin (arity e))))
      (fin (arity e)).value 1 (fun _ _ => le_rfl)
    rw [fin_value,List.length_finRange] at hmap
    have hme := hm e
    have hsq : 3*(arity e+1)^2 ≤ 3*(M+1)^2 := by gcongr
    simp only [ports,fin_value]
    omega
  have hl (e : Fin F) : (ports arity e).value.length ≤ M := by
    rw [ports_value,List.length_map,List.length_finRange]
    exact hm e
  have hout := flat_work (ports arity) (fin F).value (3*(M+1)^2+3*M+3) M
    (fun e _ => hp e) (fun e _ => hl e)
  rw [fin_value,List.length_finRange] at hout
  have hf := fin_work F
  change (incidences F arity).work ≤ incidenceBudget F M
  simp only [incidences,fin_value]
  unfold incidenceBudget
  have he : F*(3*(M+1)^2+3*M+3+M+2)=F*(3*(M+1)^2+4*M+5) := by ring
  rw [he] at hout
  omega

variable {r Q : ℕ} [NeZero r]

/-- Full universal incidence alphabet, reusing the acquired word data. -/
def universal (r Q : ℕ) [NeZero r] : Run (List (UniversalType r Q 1)) :=
  let ws := words r Q
  let empty : List (Fin 0 → Word r Q) := [fun i => Fin.elim0 i]
  let slotPairs := product ws.value empty
  let slots := collect (fun p => (⟨Fin.cons p.1 p.2,1⟩ : Run (Fin 1 → Word r Q))) slotPairs.value
  let pairs := product ws.value slots.value
  let out := collect (fun p => (⟨(equivProd r Q 1).symm p,2⟩ : Run (UniversalType r Q 1))) pairs.value
  ⟨out.value,ws.work+slotPairs.work+slots.work+pairs.work+out.work+4⟩

theorem universal_value (r Q : ℕ) [NeZero r] :
    (universal r Q).value=(SemiprimeFiniteEnumerations.universal r Q).values := by
  simp only [universal,collect_value,product_value,words_value]
  rfl

@[simp] theorem universal_length (r Q : ℕ) [NeZero r] :
    (universal r Q).value.length=r^(2*Q) := by
  rw [universal_value,SemiprimeFiniteEnumerations.universal_length]

/-- Universal-alphabet work is polynomial in the acquired word alphabet A. -/
def universalBudget (r Q : ℕ) : ℕ :=
  wordsBudget r Q+(7*r^Q+1)+(3*r^Q+1)+(r^Q*(4*r^Q+3)+1)+(4*(r^Q)^2+1)+4

theorem universal_work (r Q : ℕ) [NeZero r] :
    (universal r Q).work ≤ universalBudget r Q := by
  have hw := words_work r Q
  let empty : List (Fin 0 → Word r Q) := [fun i => Fin.elim0 i]
  have hslot := product_work (words r Q).value empty
  have hs := collect_work (fun p => (⟨Fin.cons p.1 p.2,1⟩ : Run (Fin 1 → Word r Q)))
    (product (words r Q).value empty).value 1 (fun _ _ => le_rfl)
  have hslots : (collect (fun p => (⟨Fin.cons p.1 p.2,1⟩ : Run (Fin 1 → Word r Q)))
      (product (words r Q).value empty).value).value.length=r^Q := by
    simp only [collect_value,List.length_map,product_value]
    exact List.length_product _ _ |>.trans (by simp [empty])
  have hp := product_work (words r Q).value
    (collect (fun p => (⟨Fin.cons p.1 p.2,1⟩ : Run (Fin 1 → Word r Q)))
      (product (words r Q).value empty).value).value
  have ho := collect_work
    (fun p => (⟨(equivProd r Q 1).symm p,2⟩ : Run (UniversalType r Q 1)))
    (product (words r Q).value
      (collect (fun p => (⟨Fin.cons p.1 p.2,1⟩ : Run (Fin 1 → Word r Q)))
        (product (words r Q).value empty).value).value).value 2 (fun _ _ => le_rfl)
  have hlen : (product (words r Q).value empty).value.length=r^Q := by
    rw [product_value]
    exact List.length_product _ _ |>.trans (by simp [empty])
  have hlen2 : (product (words r Q).value
      (collect (fun p => (⟨Fin.cons p.1 p.2,1⟩ : Run (Fin 1 → Word r Q)))
        (product (words r Q).value empty).value).value).value.length=r^Q*r^Q := by
    rw [product_value]
    exact List.length_product _ _ |>.trans (by rw [words_length,hslots])
  rw [words_length] at hslot hp
  rw [hslots] at hp
  rw [hlen] at hs
  rw [hlen2] at ho
  simp only [empty,List.length_singleton] at hslot
  unfold universal universalBudget
  dsimp only
  nlinarith

/-- Actual collision/head score menu, using cached finite lists. -/
def scores {I V : Type} (is : List I) (vs : List V) (qs : List (Fin Q)) :
    Run (List (Packing.ScoreTerm I V Q)) :=
  let collisions := product is is
  let heads := product vs vs
  let taggedHeads := product qs heads.value
  let out := sum collisions.value taggedHeads.value
  ⟨out.value,collisions.work+heads.work+taggedHeads.work+out.work+3⟩

theorem scores_value {I V : Type} (is : List I) (vs : List V) (qs : List (Fin Q)) :
    (scores is vs qs).value=(is.product is).map Sum.inl++(qs.product (vs.product vs)).map Sum.inr := by
  simp only [scores,sum_value,product_value]

/-- Exact polynomial menu-construction envelope, not an enumeration of global assignments. -/
def scoreBudget (M n Q : ℕ) : ℕ :=
  (M*(4*M+3)+1)+(n*(4*n+3)+1)+(Q*(4*n*n+3)+1)+4*(M*M+Q*n*n)+7

theorem scores_work {I V : Type} (is : List I) (vs : List V) (qs : List (Fin Q)) :
    (scores is vs qs).work ≤ scoreBudget is.length vs.length qs.length := by
  have hl := product_work is is
  have hh := product_work vs vs
  have hr := product_work qs (product vs vs).value
  have ho := sum_work (product is is).value (product qs (product vs vs).value).value
  have plen {α β : Type} (xs : List α) (ys : List β) : (product xs ys).value.length=xs.length*ys.length := by
    rw [product_value]
    exact List.length_product _ _
  rw [plen] at hr
  rw [plen,plen,plen] at ho
  unfold scores scoreBudget
  dsimp only
  nlinarith

/-- Full zero-word scan, with every coordinate read rather than a function equality oracle. -/
def zeroTest (w : Word r Q) : List (Fin Q) → Run Bool
  | [] => ⟨true,1⟩
  | i::is => let tail := zeroTest w is; ⟨decide (w i=0) && tail.value,tail.work+3⟩

theorem zeroTest_value (w : Word r Q) (is : List (Fin Q)) :
    (zeroTest w is).value=true ↔ ∀ i∈is, w i=0 := by
  induction is with
  | nil => simp [zeroTest]
  | cons i is ih => simp only [zeroTest,Bool.and_eq_true,decide_eq_true_eq,ih,List.forall_mem_cons]

theorem zeroTest_work (w : Word r Q) (is : List (Fin Q)) :
    (zeroTest w is).work=3*is.length+1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [zeroTest,List.length_cons,ih]; omega

/-- Filter the acquired word table with actual complete zero scans and finite list cells. -/
def nonzeroWords (coordinates : List (Fin Q)) : List (Word r Q) → Run (List (Word r Q))
  | [] => ⟨[],1⟩
  | w::ws =>
      let z := zeroTest w coordinates
      let tail := nonzeroWords coordinates ws
      ⟨if z.value then tail.value else w::tail.value,z.work+tail.work+3⟩

theorem nonzeroWords_value (ws : List (Word r Q)) :
    (nonzeroWords (List.finRange Q) ws).value=ws.filter (fun w => decide (w≠fun _ => 0)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hz : (zeroTest w (List.finRange Q)).value=true ↔ w=(fun _ => 0) := by
      rw [zeroTest_value]
      simp only [List.mem_finRange,true_implies]
      exact ⟨fun h => funext h,fun h i => congrFun h i⟩
    simp only [nonzeroWords,ih,List.filter_cons]
    by_cases h : w=(fun _ => 0)
    · rw [ite_eq_left (hz.mpr h)]
      simp [h]
    · rw [ite_eq_right (by simpa only [hz] using h)]
      simp [h]

theorem nonzeroWords_work (coordinates : List (Fin Q)) (ws : List (Word r Q)) :
    (nonzeroWords coordinates ws).work ≤ ws.length*(3*coordinates.length+4)+1 := by
  induction ws with
  | nil => simp [nonzeroWords]
  | cons w ws ih =>
    simp only [nonzeroWords,zeroTest_work,List.length_cons]
    nlinarith

/-- Finite enumeration records are determined by literal ordered data; proof fields erase. -/
theorem enumeration_ext {α : Type} {a b : FiniteEnumeration α}
    (h : a.values=b.values) : a=b := by
  cases a
  cases b
  cases h
  rfl

/-- A proof-only certificate attached to actual acquired list data. -/
def certify {α : Type} (values : List α) (hn : values.Nodup) (hc : ∀ a, a∈values) : FiniteEnumeration α :=
  ⟨values,hn,hc⟩

/-- Actual indexed enumeration acquisition from original public dimensions and arities. -/
def indexed (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    Run (SemiprimeSourceLayout.Enumerations ((e : Fin F) × Fin (arity e)) (Fin n) (Fin F) r Q) :=
  let vs := fin n
  let fs := fin F
  let is := incidences F arity
  let ws := words r Q
  let us := universal r Q
  let qs := fin Q
  let ts := scores is.value vs.value qs.value
  let ids := sum vs.value fs.value
  let tail := nonzeroWords qs.value ws.value
  let data : SemiprimeSourceLayout.Enumerations ((e : Fin F) × Fin (arity e)) (Fin n) (Fin F) r Q :=
    { incidences := certify is.value (by
        rw [incidences_value]
        exact (SemiprimeFiniteEnumerations.indexedIncidences F arity).nodup) (by
        intro i
        rw [incidences_value]
        exact (SemiprimeFiniteEnumerations.indexedIncidences F arity).complete i)
      types := certify us.value (by rw [universal_value]; exact (SemiprimeFiniteEnumerations.universal r Q).nodup)
        (by intro u; rw [universal_value]; exact (SemiprimeFiniteEnumerations.universal r Q).complete u)
      wordFirst := fun _ => 0
      wordTail := tail.value
      words_nodup := by
        change ((fun _ => (0 : Fin r)) :: (nonzeroWords (fin Q).value (words r Q).value).value).Nodup
        rw [fin_value,nonzeroWords_value,words_value]
        exact (SemiprimeFiniteEnumerations.indexed n F r Q arity).words_nodup
      words_complete := by
        intro w
        change w∈(fun _ => (0 : Fin r)) :: (nonzeroWords (fin Q).value (words r Q).value).value
        rw [fin_value,nonzeroWords_value,words_value]
        exact (SemiprimeFiniteEnumerations.indexed n F r Q arity).words_complete w
      terms := certify ts.value (by
        change (scores (incidences F arity).value (fin n).value (fin Q).value).value.Nodup
        simp only [scores_value,incidences_value,fin_value]
        exact (SemiprimeFiniteEnumerations.scoreTerms
          (SemiprimeFiniteEnumerations.indexedIncidences F arity) (SemiprimeFiniteEnumerations.fin n) Q).nodup)
        (by
          intro t
          change t∈(scores (incidences F arity).value (fin n).value (fin Q).value).value
          simp only [scores_value,incidences_value,fin_value]
          exact (SemiprimeFiniteEnumerations.scoreTerms
            (SemiprimeFiniteEnumerations.indexedIncidences F arity) (SemiprimeFiniteEnumerations.fin n) Q).complete t)
      indices := certify ids.value (by
        rw [sum_value,fin_value,fin_value]
        exact (SemiprimeFiniteEnumerations.sum (SemiprimeFiniteEnumerations.fin n) (SemiprimeFiniteEnumerations.fin F)).nodup)
        (by
          intro i
          rw [sum_value,fin_value,fin_value]
          exact (SemiprimeFiniteEnumerations.sum (SemiprimeFiniteEnumerations.fin n) (SemiprimeFiniteEnumerations.fin F)).complete i) }
  ⟨data,vs.work+fs.work+is.work+ws.work+us.work+qs.work+ts.work+ids.work+tail.work+12⟩

omit [NeZero r] in
/-- Exact source-enumeration data equality; all certificate fields are propositions. -/
theorem data_ext {I V E : Type} {a b : SemiprimeSourceLayout.Enumerations I V E r Q}
    (hi : a.incidences=b.incidences) (ht : a.types=b.types)
    (hf : a.wordFirst=b.wordFirst) (hw : a.wordTail=b.wordTail)
    (hs : a.terms=b.terms) (hx : a.indices=b.indices) : a=b := by
  cases a
  cases b
  cases hi
  cases ht
  cases hf
  cases hw
  cases hs
  cases hx
  rfl

/-- ALL list orderings and actual function values match the previous indexed source enumeration. -/
theorem indexed_value (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    (indexed n F r Q arity).value=SemiprimeFiniteEnumerations.indexed n F r Q arity := by
  apply data_ext
  · apply enumeration_ext
    exact incidences_value F arity
  · apply enumeration_ext
    exact universal_value r Q
  · rfl
  · change (nonzeroWords (fin Q).value (words r Q).value).value=_
    rw [fin_value,nonzeroWords_value,words_value]
    rfl
  · apply enumeration_ext
    change (scores (incidences F arity).value (fin n).value (fin Q).value).value=_
    rw [scores_value,incidences_value,fin_value,fin_value]
    rfl
  · apply enumeration_ext
    change (sum (fin n).value (fin F).value).value=_
    rw [sum_value,fin_value,fin_value]
    rfl

/-- Combined attached clock of the actual original indexed acquisition. -/
def budget (n F r Q M : ℕ) : ℕ :=
  3*(n+1)^2+3*(F+1)^2+incidenceBudget F M+wordsBudget r Q+universalBudget r Q+
    3*(Q+1)^2+scoreBudget M n Q+4*(n+F)+4+r^Q*(3*Q+4)+1+12

/-- No list, coefficient, score-menu or term answer is supplied to this full bound. -/
theorem indexed_work (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    (indexed n F r Q arity).work ≤ budget n F r Q (∑ e,arity e) := by
  have hv := fin_work n
  have hf := fin_work F
  have hi := incidences_work F arity
  have hw := words_work r Q
  have hu := universal_work r Q
  have hq := fin_work Q
  have hs := scores_work (incidences F arity).value (fin n).value (fin Q).value
  rw [incidences_length,fin_value,List.length_finRange,fin_value,List.length_finRange] at hs
  have hx := sum_work (fin n).value (fin F).value
  rw [fin_value,List.length_finRange,fin_value,List.length_finRange] at hx
  have ht := nonzeroWords_work (fin Q).value (words r Q).value
  rw [fin_value,List.length_finRange,words_length] at ht
  unfold indexed budget
  dsimp only
  simp only [fin_value]
  omega

/-- Acquired incidence list length is the actual total port count. -/
theorem indexed_incidence_length (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    (indexed n F r Q arity).value.incidences.values.length=∑ e,arity e := by
  rw [indexed_value]
  exact SemiprimeFiniteEnumerations.indexedIncidences_length F arity

/-- Acquired universal table has exactly the actual D=r^(2Q) entries. -/
theorem indexed_universal_length (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    (indexed n F r Q arity).value.types.values.length=r^(2*Q) := by
  rw [indexed_value]
  exact SemiprimeFiniteEnumerations.universal_length r Q

/-- Acquired source score menu is exactly M²+Q*n², not all assignments. -/
theorem indexed_score_length (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    (indexed n F r Q arity).value.terms.values.length=(∑ e,arity e)^2+Q*n^2 := by
  change (scores (incidences F arity).value (fin n).value (fin Q).value).value.length=_
  rw [scores_value,List.length_append,List.length_map,List.length_map]
  change ((incidences F arity).value ×ˢ (incidences F arity).value).length+
    ((fin Q).value ×ˢ ((fin n).value ×ˢ (fin n).value)).length=_
  rw [List.length_product,List.length_product,List.length_product,incidences_length,fin_value,List.length_finRange,
    fin_value,List.length_finRange]
  ring

/-- Actual source index list contains each variable and factor once. -/
theorem indexed_indices_length (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    (indexed n F r Q arity).value.indices.values.length=n+F := by
  change (sum (fin n).value (fin F).value).value.length=_
  rw [sum_value,List.length_append,List.length_map,List.length_map,fin_value,List.length_finRange,
    fin_value,List.length_finRange]

/-- The complete word producer's bound as a literal polynomial in independent dimensions. -/
def wordPolynomial (color Q A : ℕ) : ℕ :=
  1+Q*(3*(color+1)^2+(color*(4*A+3)+1)+3*(Q+1)^2+(color*A*(5*Q+5)+1)+4)

/-- The universal pair menu's literal polynomial. -/
def universalPolynomial (color Q A : ℕ) : ℕ :=
  wordPolynomial color Q A+(7*A+1)+(3*A+1)+(A*(4*A+3)+1)+(4*A^2+1)+4

/-- Fixed polynomial in the original dimensions, total incidence and acquired alphabet size. -/
def polynomial (n F M Q color A : ℕ) : ℕ :=
  3*(n+1)^2+3*(F+1)^2+incidenceBudget F M+wordPolynomial color Q A+
    universalPolynomial color Q A+3*(Q+1)^2+scoreBudget M n Q+4*(n+F)+4+A*(3*Q+4)+1+12

/-- At positive Q, r<=A=r^Q, so no hidden color dependence escapes the polynomial. -/
theorem indexed_work_polynomial (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) (hQ : 1≤Q) :
    (indexed n F r Q arity).work ≤ polynomial n F (∑ e,arity e) Q (r^Q) (r^Q) := by
  have hr : r≤r^Q := by
    simpa only [pow_one] using Nat.pow_le_pow_right (NeZero.one_le (n:=r)) hQ
  calc
    (indexed n F r Q arity).work ≤ budget n F r Q (∑ e,arity e) := indexed_work n F r Q arity
    _ = polynomial n F (∑ e,arity e) Q r (r^Q) := by
      unfold budget polynomial universalPolynomial wordPolynomial universalBudget wordsBudget wordStage
      rfl
    _ ≤ polynomial n F (∑ e,arity e) Q (r^Q) (r^Q) := by
      unfold polynomial universalPolynomial wordPolynomial
      gcongr

end RiemannGaussian.SemiprimePaidFiniteEnumerations
