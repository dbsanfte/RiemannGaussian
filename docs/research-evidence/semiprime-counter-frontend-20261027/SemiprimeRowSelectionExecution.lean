/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeLayoutSelection

/-! # Executed rational pivoting while retaining original integer row indices -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace RiemannGaussian.SemiprimeRowSelectionExecution
open scoped BigOperators

/-- Rational rows on the actual explicitly enumerated columns. -/
abbrev Row (n : ℕ) := Fin n → ℚ

/-- Materialize the finite row; later reads do not recompute its arithmetic. -/
def cacheRow {n : ℕ} (row : Row n) : Row n :=
  let data := Vector.ofFn row
  fun i => data.get i

/-- Materialized row access is exactly its computed value. -/
theorem cacheRow_apply {n : ℕ} (row : Row n) (i : Fin n) : cacheRow row i=row i := Vector.get_ofFn _ _

/-- Materialize all finite working rows after a pivot update. -/
def cacheMatrix {n : ℕ} (rows : Fin n → Row n) : Fin n → Row n :=
  let data := Vector.ofFn (fun i => Vector.ofFn (rows i))
  fun i j => (data.get i).get j

/-- Each stored matrix entry is the literal computed entry. -/
theorem cacheMatrix_apply {n : ℕ} (rows : Fin n → Row n) (i j : Fin n) :
    cacheMatrix rows i j=rows i j := by simp only [cacheMatrix,Vector.get_ofFn]

/-- Fixed-width reduced working rows and the indices of original selected rows. -/
structure State (m n : ℕ) where
  /-- Whether this column currently owns a pivot. -/
  active : Fin n → Bool
  /-- Materialized rational working rows, indexed by pivot column. -/
  rows : Fin n → Row n
  /-- Original integer-row indices, never rescaled or replaced in the output. -/
  selected : List (Fin m)

/-- The empty, fully explicit initial state. -/
def empty (m n : ℕ) : State m n := ⟨fun _ => false,fun _ _ => 0,[]⟩

/-- Inactive rows are zero and active pivot coordinates form a Kronecker matrix. -/
structure Good {m n : ℕ} (s : State m n) : Prop where
  /-- Unused working slots have no hidden nonzero rows. -/
  inactive : ∀ c,s.active c=false → s.rows c=0
  /-- Every active row is normalized and zero at every other active pivot. -/
  pivot : ∀ c d,s.active c=true → s.active d=true → s.rows c d=if c=d then 1 else 0

/-- The empty state satisfies the exact working-matrix invariant. -/
theorem empty_good (m n : ℕ) : Good (empty m n) := by
  constructor
  · intro c _; rfl
  · intro c d hc; cases hc

/-- One actual residual row, computed by all current pivot eliminations. -/
def residual {m n : ℕ} (s : State m n) (row : Row n) : Row n :=
  cacheRow (fun v => row v-∑ c : Fin n,if s.active c then row c*s.rows c v else 0)

/-- Every old pivot has been eliminated from the actual computed residual. -/
theorem residual_pivot {m n : ℕ} (s : State m n) (hg : Good s) (row : Row n)
    (d : Fin n) (hd : s.active d=true) : residual s row d=0 := by
  rw [residual,cacheRow_apply]
  have he (c : Fin n) : (if s.active c then row c*s.rows c d else 0)=
      if c=d then row d else 0 := by
    by_cases hc : s.active c=true
    · rw [ite_eq_left hc,hg.pivot c d hc hd]
      by_cases hcd : c=d <;> simp [hcd]
    · have hne : c≠d := by intro h; subst c; exact hc hd
      simp only [ite_eq_right hc,ite_eq_right hne]
  simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true,sub_self]

/-- First nonzero residual coordinate, scanned in literal finite-column order. -/
def findPivot {n : ℕ} (row : Row n) : Option (Fin n) :=
  (List.finRange n).find? (fun c => decide (row c≠0))

/-- A reported pivot was actually tested nonzero. -/
theorem findPivot_some {n : ℕ} (row : Row n) (p : Fin n) (h : findPivot row=some p) : row p≠0 := by
  have hh := List.find?_some (p:=fun c : Fin n => decide (row c≠0))
    (l:=List.finRange n) h
  exact of_decide_eq_true hh

/-- A failed finite scan proves the whole residual row is exactly zero. -/
theorem findPivot_none {n : ℕ} (row : Row n) (h : findPivot row=none) : row=0 := by
  funext c
  have hc := (List.find?_eq_none.mp h) c (List.mem_finRange c)
  change row c=0
  simpa only [decide_eq_true_eq,not_not] using hc

/-- Normalize using the computed nonzero pivot entry. -/
def normalized {m n : ℕ} (s : State m n) (row : Row n) (p : Fin n) : Row n :=
  let reduced := residual s row
  let pivot := reduced p
  cacheRow (fun v => reduced v / pivot)

/-- Explicit complete back elimination, retaining the literal original row index. -/
def pivotInsert {m n : ℕ} (s : State m n) (j : Fin m) (row : Row n) (p : Fin n) : State m n :=
  let reduced := normalized s row p
  { active := fun c => if c=p then true else s.active c
    rows := cacheMatrix (fun c v => if c=p then reduced v else
      if s.active c then s.rows c v-s.rows c p*reduced v else 0)
    selected := j::s.selected }

/-- One actual row-selection step: dependent rows are omitted from the output. -/
def insert {m n : ℕ} (s : State m n) (j : Fin m) (row : Row n) : State m n :=
  match findPivot (residual s row) with
  | none => s
  | some p => pivotInsert s j row p

/-- A new pivot cannot be an old active pivot. -/
theorem pivot_fresh {m n : ℕ} (s : State m n) (hg : Good s) (row : Row n)
    (p : Fin n) (hp : residual s row p≠0) : s.active p=false := by
  cases h : s.active p with
  | false => rfl
  | true => exact False.elim (hp (residual_pivot s hg row p h))

/-- The normalized residual is one at its actual new pivot. -/
theorem normalized_self {m n : ℕ} (s : State m n) (row : Row n) (p : Fin n)
    (hp : residual s row p≠0) : normalized s row p p=1 := by
  rw [normalized,cacheRow_apply,div_self hp]

/-- The new normalized row remains zero on every old active pivot. -/
theorem normalized_old {m n : ℕ} (s : State m n) (hg : Good s) (row : Row n)
    (p d : Fin n) (hd : s.active d=true) : normalized s row p d=0 := by
  rw [normalized,cacheRow_apply,residual_pivot s hg row d hd,zero_div]

/-- Every actual pivot update preserves the full reduced-row invariant. -/
theorem pivotInsert_good {m n : ℕ} (s : State m n) (hg : Good s) (j : Fin m)
    (row : Row n) (p : Fin n) (hp : residual s row p≠0) : Good (pivotInsert s j row p) := by
  have hself := normalized_self s row p hp
  constructor
  · intro c hc
    have hcp : c≠p := by intro he; subst c; simp [pivotInsert] at hc
    have hold : s.active c=false := by simpa only [pivotInsert,ite_eq_right hcp] using hc
    funext v
    simp only [pivotInsert,cacheMatrix_apply,ite_eq_right hcp,hold,Bool.false_eq_true,ite_false,Pi.zero_apply]
  · intro c d hc hd
    by_cases hcp : c=p
    · subst c
      by_cases hdp : d=p
      · subst d; simpa only [pivotInsert,cacheMatrix_apply,ite_true] using hself
      · have hold : s.active d=true := by simpa only [pivotInsert,ite_eq_right hdp] using hd
        simp only [pivotInsert,cacheMatrix_apply,ite_true,normalized_old s hg row p d hold,
          ite_eq_right (Ne.symm hdp)]
    · have holdc : s.active c=true := by simpa only [pivotInsert,ite_eq_right hcp] using hc
      by_cases hdp : d=p
      · subst d
        simp only [pivotInsert,cacheMatrix_apply,ite_eq_right hcp,holdc,ite_true,hself,
          mul_one,sub_self]
      · have holdd : s.active d=true := by simpa only [pivotInsert,ite_eq_right hdp] using hd
        simp only [pivotInsert,cacheMatrix_apply,ite_eq_right hcp,holdc,ite_true,
          normalized_old s hg row p d holdd,mul_zero,sub_zero,hg.pivot c d holdc holdd]

/-- The concrete selection step is lawful even when every row is zero. -/
theorem insert_good {m n : ℕ} (s : State m n) (hg : Good s) (j : Fin m) (row : Row n) :
    Good (insert s j row) := by
  unfold insert
  split
  · exact hg
  · rename_i p hp
    exact pivotInsert_good s hg j row p (findPivot_some _ _ hp)


/-- Process the explicit candidate order, retaining actual original integer rows. -/
def run {m n : ℕ} (C : Fin m → Fin n → ℤ) : List (Fin m) → State m n
  | [] => empty m n
  | j::tail => insert (run C tail) j (fun v => (C j v : ℚ))

/-- Every computed full or partial run has lawful reduced pivot coordinates. -/
theorem run_good {m n : ℕ} (C : Fin m → Fin n → ℤ) (candidates : List (Fin m)) :
    Good (run C candidates) := by
  induction candidates with
  | nil => exact empty_good _ _
  | cons j tail ih => exact insert_good _ ih _ _

/-- Rational span of the actual materialized working rows. -/
def workSpan {m n : ℕ} (s : State m n) : Submodule ℚ (Row n) :=
  Submodule.span ℚ (Set.range s.rows)

/-- Every working row is in its literal span. -/
theorem row_mem_workSpan {m n : ℕ} (s : State m n) (c : Fin n) : s.rows c∈workSpan s :=
  Submodule.subset_span ⟨c,rfl⟩

/-- Residual elimination uses only linear combinations of actual working rows. -/
theorem residual_eq {m n : ℕ} (s : State m n) (row : Row n) :
    residual s row=row-∑ c : Fin n,if s.active c then row c • s.rows c else 0 := by
  funext v
  simp only [residual,cacheRow_apply,Pi.sub_apply,Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  cases s.active c <;> rfl

/-- The sum subtracted during elimination belongs to the old working span. -/
theorem eliminated_mem {m n : ℕ} (s : State m n) (row : Row n) :
    (∑ c : Fin n,if s.active c then row c • s.rows c else 0)∈workSpan s := by
  apply Submodule.sum_mem
  intro c _
  split
  · exact Submodule.smul_mem _ _ (row_mem_workSpan s c)
  · exact Submodule.zero_mem _

/-- Normalization is exactly scalar multiplication, not a span oracle. -/
theorem normalized_eq {m n : ℕ} (s : State m n) (row : Row n) (p : Fin n) :
    normalized s row p=(residual s row p)⁻¹ • residual s row := by
  funext v
  simp only [normalized,cacheRow_apply,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv]
  ring

/-- Computed normalization lies in the span enlarged by the new original row. -/
theorem normalized_mem {m n : ℕ} (s : State m n) (row : Row n) (p : Fin n) :
    normalized s row p∈workSpan s ⊔ Submodule.span ℚ {row} := by
  rw [normalized_eq,residual_eq]
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  · exact (le_sup_right : Submodule.span ℚ {row}≤_)
      (Submodule.subset_span (Set.mem_singleton row))
  · exact (le_sup_left : workSpan s≤_) (eliminated_mem s row)

/-- A failed residual scan discards only a row already in the computed old span. -/
theorem rejected_mem {m n : ℕ} (s : State m n) (row : Row n)
    (h : findPivot (residual s row)=none) : row∈workSpan s := by
  have hz := findPivot_none _ h
  have he : row=∑ c : Fin n,if s.active c then row c • s.rows c else 0 := by
    have hh := residual_eq s row
    rw [hz] at hh
    exact sub_eq_zero.mp hh.symm
  rw [he]
  exact eliminated_mem s row

/-- Every old working row is retained in the span after a computed pivot. -/
theorem old_mem_new {m n : ℕ} (s : State m n) (hg : Good s) (j : Fin m)
    (row : Row n) (p : Fin n) (hp : residual s row p≠0) (c : Fin n) :
    s.rows c∈workSpan (pivotInsert s j row p) := by
  have hnewp : (pivotInsert s j row p).rows p=normalized s row p := by
    funext v
    simp only [pivotInsert,cacheMatrix_apply,ite_true]
  by_cases hc : s.active c=true
  · have hcp : c≠p := by
      intro h
      subst c
      rw [pivot_fresh s hg row p hp] at hc
      cases hc
    have he : s.rows c=(pivotInsert s j row p).rows c+s.rows c p • (pivotInsert s j row p).rows p := by
      rw [hnewp]
      funext v
      simp only [pivotInsert,cacheMatrix_apply,ite_eq_right hcp,hc,ite_true,
        Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
    rw [he]
    exact Submodule.add_mem _ (row_mem_workSpan _ c)
      (Submodule.smul_mem _ _ (row_mem_workSpan _ p))
  · have hz : s.active c=false := Bool.eq_false_iff.mpr hc
    rw [hg.inactive c hz]
    exact Submodule.zero_mem _

/-- The new original row is in the updated computed working span. -/
theorem new_mem_new {m n : ℕ} (s : State m n) (hg : Good s) (j : Fin m)
    (row : Row n) (p : Fin n) (hp : residual s row p≠0) :
    row∈workSpan (pivotInsert s j row p) := by
  have hnewp : (pivotInsert s j row p).rows p=normalized s row p := by
    funext v
    simp only [pivotInsert,cacheMatrix_apply,ite_true]
  have hresEq : residual s row=residual s row p • normalized s row p := by
    funext v
    simp only [normalized,cacheRow_apply,Pi.smul_apply,smul_eq_mul]
    exact (mul_div_cancel₀ _ hp).symm
  have hres : residual s row∈workSpan (pivotInsert s j row p) := by
    rw [hresEq,← hnewp]
    exact Submodule.smul_mem _ _ (row_mem_workSpan _ p)
  have hsum : (∑ c : Fin n,if s.active c then row c • s.rows c else 0)∈
      workSpan (pivotInsert s j row p) := by
    apply Submodule.sum_mem
    intro c _
    split
    · exact Submodule.smul_mem _ _ (old_mem_new s hg j row p hp c)
    · exact Submodule.zero_mem _
  have he : row=residual s row+∑ c : Fin n,if s.active c then row c • s.rows c else 0 := by
    rw [residual_eq,sub_add_cancel]
  have hmem := Submodule.add_mem (workSpan (pivotInsert s j row p)) hres hsum
  exact (congrArg (fun v : Row n => v∈workSpan (pivotInsert s j row p)) he).mpr hmem

/-- Exact span update from the executed elimination, with no supplied rank premise. -/
theorem pivotInsert_span {m n : ℕ} (s : State m n) (hg : Good s) (j : Fin m)
    (row : Row n) (p : Fin n) (hp : residual s row p≠0) :
    workSpan (pivotInsert s j row p)=workSpan s ⊔ Submodule.span ℚ {row} := by
  have hnorm := normalized_mem s row p
  have hnewp : (pivotInsert s j row p).rows p=normalized s row p := by
    funext v
    simp only [pivotInsert,cacheMatrix_apply,ite_true]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨c,rfl⟩
    by_cases hc : c=p
    · subst c
      rw [hnewp]
      exact hnorm
    · by_cases hactive : s.active c=true
      · have he : (pivotInsert s j row p).rows c=s.rows c-s.rows c p • normalized s row p := by
          funext v
          simp only [pivotInsert,cacheMatrix_apply,ite_eq_right hc,hactive,ite_true,
            Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
        rw [he]
        exact Submodule.sub_mem _ ((le_sup_left : workSpan s≤_) (row_mem_workSpan s c))
          (Submodule.smul_mem _ _ hnorm)
      · have he : (pivotInsert s j row p).rows c=0 := by
          funext v
          simp only [pivotInsert,cacheMatrix_apply,ite_eq_right hc,ite_eq_right hactive,Pi.zero_apply]
        rw [he]
        exact Submodule.zero_mem _
  · apply sup_le
    · exact Submodule.span_le.mpr (by rintro _ ⟨c,rfl⟩; exact old_mem_new s hg j row p hp c)
    · apply Submodule.span_le.mpr
      intro v hv
      have heq : v=row := Set.mem_singleton_iff.mp hv
      subst v
      exact new_mem_new s hg j row p hp

/-- Every selection step has the exact full-row span update. -/
theorem insert_span {m n : ℕ} (s : State m n) (hg : Good s) (j : Fin m) (row : Row n) :
    workSpan (insert s j row)=workSpan s ⊔ Submodule.span ℚ {row} := by
  unfold insert
  split
  · rename_i h
    apply (sup_eq_left.mpr (Submodule.span_le.mpr (by
      intro v hv
      have he := Set.mem_singleton_iff.mp hv
      subst v
      exact rejected_mem s row h))).symm
  · rename_i p hp
    exact pivotInsert_span s hg j row p (findPivot_some _ _ hp)


/-- Literal rational view of an original integer row. -/
def originalRow {m n : ℕ} (C : Fin m → Fin n → ℤ) (j : Fin m) : Row n := fun v => (C j v : ℚ)

/-- Span of a finite candidate list, defined without a basis choice. -/
def inputSpan {m n : ℕ} (C : Fin m → Fin n → ℤ) : List (Fin m) → Submodule ℚ (Row n)
  | [] => ⊥
  | j::tail => inputSpan C tail ⊔ Submodule.span ℚ {originalRow C j}

/-- The literal empty working matrix has zero span. -/
theorem empty_span (m n : ℕ) : workSpan (empty m n)=⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨c,rfl⟩
    exact Submodule.zero_mem _
  · exact bot_le

/-- The actual run spans every input row, including all computed rejections. -/
theorem run_span {m n : ℕ} (C : Fin m → Fin n → ℤ) (candidates : List (Fin m)) :
    workSpan (run C candidates)=inputSpan C candidates := by
  induction candidates with
  | nil => exact empty_span _ _
  | cons j tail ih =>
    change workSpan (insert (run C tail) j (originalRow C j))=_
    rw [insert_span _ (run_good C tail),ih]
    rfl

/-- The same actual working span equals the span of the ORIGINAL selected rows. -/
theorem run_selected_span {m n : ℕ} (C : Fin m → Fin n → ℤ) (candidates : List (Fin m)) :
    workSpan (run C candidates)=inputSpan C (run C candidates).selected := by
  induction candidates with
  | nil => exact empty_span _ _
  | cons j tail ih =>
    change workSpan (insert (run C tail) j (originalRow C j))=
      inputSpan C (insert (run C tail) j (originalRow C j)).selected
    unfold insert
    split
    · exact ih
    · rename_i p hp
      rw [pivotInsert_span _ (run_good C tail) _ _ _ (findPivot_some _ _ hp),ih]
      rfl

/-- No original index can be invented by the selector. -/
theorem run_selected_subset {m n : ℕ} (C : Fin m → Fin n → ℤ) (candidates : List (Fin m)) :
    ∀ j∈(run C candidates).selected,j∈candidates := by
  induction candidates with
  | nil => simp [run,empty]
  | cons j tail ih =>
    change ∀ k∈(insert (run C tail) j (originalRow C j)).selected,k∈j::tail
    unfold insert
    split
    · intro k hk; exact List.mem_cons_of_mem _ (ih k hk)
    · simp only [pivotInsert,List.mem_cons]
      intro k hk
      rcases hk with hk|hk
      · exact Or.inl hk
      · exact Or.inr (ih k hk)

/-- Distinct input records yield distinct output original-row records. -/
theorem run_selected_nodup {m n : ℕ} (C : Fin m → Fin n → ℤ) (candidates : List (Fin m))
    (h : candidates.Nodup) : (run C candidates).selected.Nodup := by
  induction candidates with
  | nil => simp [run,empty]
  | cons j tail ih =>
    have ht := (List.nodup_cons.mp h).2
    have hj := (List.nodup_cons.mp h).1
    change (insert (run C tail) j (originalRow C j)).selected.Nodup
    unfold insert
    split
    · exact ih ht
    · apply List.nodup_cons.mpr
      exact ⟨fun hmem => hj (run_selected_subset C tail j hmem),ih ht⟩

/-- Actual active pivot columns. -/
def activeSet {m n : ℕ} (s : State m n) : Finset (Fin n) := Finset.univ.filter (fun c => s.active c=true)

/-- The active set gains exactly the fresh computed pivot. -/
theorem pivotInsert_activeSet {m n : ℕ} (s : State m n) (j : Fin m) (row : Row n) (p : Fin n) :
    activeSet (pivotInsert s j row p)=Insert.insert p (activeSet s) := by
  ext c
  by_cases hc : c=p <;> simp [activeSet,pivotInsert,hc]

/-- The number of ORIGINAL selected rows equals the computed pivot cardinality. -/
theorem run_selected_length {m n : ℕ} (C : Fin m → Fin n → ℤ) (candidates : List (Fin m)) :
    (run C candidates).selected.length=(activeSet (run C candidates)).card := by
  induction candidates with
  | nil => simp [run,empty,activeSet]
  | cons j tail ih =>
    change (insert (run C tail) j (originalRow C j)).selected.length=
      (activeSet (insert (run C tail) j (originalRow C j))).card
    unfold insert
    split
    · exact ih
    · rename_i p hp
      have hf := pivot_fresh (run C tail) (run_good C tail) (originalRow C j) p (findPivot_some _ _ hp)
      have hn : p∉activeSet (run C tail) := by simp [activeSet,hf]
      rw [pivotInsert_activeSet,Finset.card_insert_of_notMem hn]
      simpa only [pivotInsert,List.length_cons] using congrArg (·+1) ih


/-- The finite active-column type indexes the independent computed rows. -/
def Active {m n : ℕ} (s : State m n) := {c : Fin n // s.active c=true}

/-- Explicit finite subtype enumeration for active pivot slots. -/
instance activeFintype {m n : ℕ} (s : State m n) : Fintype (Active s) :=
  inferInstanceAs (Fintype {c : Fin n // s.active c=true})

/-- Active pivot equality is literal finite-column equality. -/
instance activeDecidableEq {m n : ℕ} (s : State m n) : DecidableEq (Active s) :=
  inferInstanceAs (DecidableEq {c : Fin n // s.active c=true})

/-- Active pivots have the same explicit cardinal as their finite column set. -/
theorem active_card {m n : ℕ} (s : State m n) : Fintype.card (Active s)=(activeSet s).card := by
  change Fintype.card {c : Fin n // s.active c=true}=
    (Finset.univ.filter (fun c : Fin n => s.active c=true)).card
  exact Fintype.card_subtype _

/-- Pivot coordinates are an explicit left-inverse certificate of independence. -/
theorem active_independent {m n : ℕ} (s : State m n) (hg : Good s) :
    LinearIndependent ℚ (fun c : Active s => s.rows c.val) := by
  apply linearIndependent_iff'.mpr
  intro t coeff hz c hc
  have hv := congrFun hz c.val
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hv
  have hd (i : Active s) : s.rows i.val c.val=if i=c then 1 else 0 := by
    rw [hg.pivot i.val c.val i.property c.property]
    by_cases hi : i=c
    · subst i; simp
    · have hval : i.val≠c.val := by intro h; exact hi (Subtype.ext h)
      simp only [ite_eq_right hi,ite_eq_right hval]
  simp only [hd,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',hc,ite_true] at hv
  exact hv

/-- Inactive zero rows add nothing: active computed rows span the actual workspace. -/
theorem workSpan_active {m n : ℕ} (s : State m n) (hg : Good s) :
    workSpan s=Submodule.span ℚ (Set.range (fun c : Active s => s.rows c.val)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨c,rfl⟩
    by_cases hc : s.active c=true
    · exact Submodule.subset_span ⟨⟨c,hc⟩,rfl⟩
    · rw [hg.inactive c (Bool.eq_false_iff.mpr hc)]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨c,rfl⟩
    exact row_mem_workSpan s c.val

/-- The actual workspace cardinality equals its true rational rank. -/
theorem workSpan_finrank {m n : ℕ} (s : State m n) (hg : Good s) :
    Module.finrank ℚ (workSpan s)=(activeSet s).card := by
  rw [workSpan_active s hg,finrank_span_eq_card (active_independent s hg),active_card]

/-- The actual finite-list span has its universal linear-membership property. -/
theorem inputSpan_le_iff {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (S : Submodule ℚ (Row n)) : inputSpan C ids≤S ↔ ∀ j∈ids,originalRow C j∈S := by
  induction ids with
  | nil => simp [inputSpan]
  | cons j tail ih =>
    simp only [inputSpan,sup_le_iff,ih,Submodule.span_singleton_le_iff_mem,List.mem_cons]
    constructor
    · rintro ⟨ht,hj⟩ k (hk|hk)
      · simpa only [hk] using hj
      · exact ht k hk
    · intro h
      exact ⟨fun k hk => h k (Or.inr hk),h j (Or.inl rfl)⟩

/-- Every candidate's literal original row belongs to its explicit list span. -/
theorem input_mem_span {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (j : Fin m) (hj : j∈ids) : originalRow C j∈inputSpan C ids :=
  (inputSpan_le_iff C ids _).mp le_rfl j hj

/-- The list span equals the span of its actual indexed original rows. -/
theorem inputSpan_get {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m)) :
    inputSpan C ids=Submodule.span ℚ (Set.range (fun i : Fin ids.length => originalRow C (ids.get i))) := by
  apply le_antisymm
  · apply (inputSpan_le_iff C ids _).mpr
    intro j hj
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hj
    exact Submodule.subset_span ⟨i,congrArg (originalRow C) hi⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact input_mem_span C ids _ (List.get_mem _ _)

/-- Enumerating every original input row gives the actual full rational row space. -/
theorem inputSpan_all {m n : ℕ} (C : Fin m → Fin n → ℤ) :
    inputSpan C (List.finRange m)=Submodule.span ℚ (Set.range (originalRow C)) := by
  apply le_antisymm
  · apply (inputSpan_le_iff C _ _).mpr
    intro j _
    exact Submodule.subset_span ⟨j,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact input_mem_span C _ j (List.mem_finRange j)


/-- The literal selected original index list for the complete finite input. -/
def selectedIndices {m n : ℕ} (C : Fin m → Fin n → ℤ) : List (Fin m) :=
  (run C (List.finRange m)).selected

/-- Actual retained original indices are distinct. -/
theorem selectedIndices_nodup {m n : ℕ} (C : Fin m → Fin n → ℤ) :
    (selectedIndices C).Nodup := run_selected_nodup C _ (List.nodup_finRange m)

/-- Explicit selected original-row lookup. -/
def selectedIndex {m n : ℕ} (C : Fin m → Fin n → ℤ) : Fin (selectedIndices C).length → Fin m :=
  (selectedIndices C).get

/-- The selector never repeats an original row index. -/
theorem selectedIndex_injective {m n : ℕ} (C : Fin m → Fin n → ℤ) :
    Function.Injective (selectedIndex C) := (selectedIndices_nodup C).injective_get

/-- Selected ORIGINAL rows, not reduced scratch rows, span exactly the full matrix. -/
theorem selected_span_eq {m n : ℕ} (C : Fin m → Fin n → ℤ) :
    Submodule.span ℚ (Set.range (fun i => originalRow C (selectedIndex C i)))=
      Submodule.span ℚ (Set.range (originalRow C)) := by
  have hs := run_selected_span C (List.finRange m)
  have ha := run_span C (List.finRange m)
  have hi := inputSpan_get C (selectedIndices C)
  exact hi.symm.trans (hs.symm.trans (ha.trans (inputSpan_all C)))

/-- The computed selected cardinality is the true rational constraint rank. -/
theorem selected_card_rank {m n : ℕ} (C : Fin m → Fin n → ℤ) :
    (selectedIndices C).length=OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank.rowRank C := by
  have hc := run_selected_length C (List.finRange m)
  have hr := workSpan_finrank (run C (List.finRange m)) (run_good C _)
  have hs := (run_span C (List.finRange m)).trans (inputSpan_all C)
  change (selectedIndices C).length=Module.finrank ℚ
    (Submodule.span ℚ (Set.range (originalRow C)))
  exact hc.trans (hr.symm.trans (congrArg (fun S : Submodule ℚ (Row n) => Module.finrank ℚ S) hs))

/-- Computable replacement for the old Classical.choice actual-row selector. -/
def selectedRows {m n : ℕ} (C : Fin m → Fin n → ℤ) : SemiprimeLayoutSelection.SelectedRows C where
  Index := Fin (selectedIndices C).length
  finite := inferInstance
  select := selectedIndex C
  injective := selectedIndex_injective C
  span := OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRowSelection.rationalRowSpan_of_span_eq
    C (selectedIndex C) (selected_span_eq C)
  card_eq := by simpa only [Fintype.card_fin] using selected_card_rank C

/-- The computed retained original rows themselves are linearly independent. -/
theorem selected_independent {m n : ℕ} (C : Fin m → Fin n → ℤ) :
    LinearIndependent ℚ (fun i => originalRow C (selectedIndex C i)) := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change Fintype.card (Fin (selectedIndices C).length)=Module.finrank ℚ
    (Submodule.span ℚ (Set.range (fun i => originalRow C (selectedIndex C i))))
  rw [selected_span_eq,Fintype.card_fin]
  exact selected_card_rank C

/-- Larger rational scratch entries never change selected integer measurement heights. -/
theorem selected_integer_height {m n : ℕ} (C : Fin m → Fin n → ℤ) (height : ℕ)
    (h : ∀ j v,|C j v|≤(height : ℤ)) :
    ∀ i v,|C ((selectedRows C).select i) v|≤(height : ℤ) := fun i v => h ((selectedRows C).select i) v


open OAI.Algorithms.SubexponentialSAT.SqrtLog

/-- Explicit column reindexing preserves rational row rank. -/
theorem rank_column_equiv {m n : ℕ} {V : Type}
    (C : Fin m → V → ℤ) (columns : Fin n ≃ V) :
    LayoutRank.rowRank (fun j v => C j (columns v))=LayoutRank.rowRank C := by
  let f := LinearEquiv.funCongrLeft ℚ ℚ columns
  have hmap : (LayoutRank.rowSpace C).map f.toLinearMap=
      LayoutRank.rowSpace (fun j v => C j (columns v)) := by
    unfold LayoutRank.rowSpace
    rw [LinearMap.map_span,← Set.range_comp]
    rfl
  have h := (f.submoduleMap (LayoutRank.rowSpace C)).finrank_eq
  rw [hmap] at h
  exact h.symm

/-- Executed original-row selection for any supplied explicit finite column order. -/
def selectedRowsWithColumns {m n : ℕ} {V : Type} [Fintype V]
    (C : Fin m → V → ℤ) (columns : Fin n ≃ V) : SemiprimeLayoutSelection.SelectedRows C where
  Index := (selectedRows (fun j v => C j (columns v))).Index
  finite := (selectedRows (fun j v => C j (columns v))).finite
  select := (selectedRows (fun j v => C j (columns v))).select
  injective := (selectedRows (fun j v => C j (columns v))).injective
  span := by
    intro j
    obtain ⟨coeff,hcoeff⟩ := (selectedRows (fun j v => C j (columns v))).span j
    refine ⟨coeff,fun v => ?_⟩
    simpa only [Equiv.apply_symm_apply] using hcoeff (columns.symm v)
  card_eq := (selectedRows (fun j v => C j (columns v))).card_eq.trans (rank_column_equiv C columns)


/-- The actually computed residual is a rational linear map. -/
def residualLinear {m n : ℕ} (s : State m n) : Row n →ₗ[ℚ] Row n where
  toFun := residual s
  map_add' a b := by
    funext v
    simp only [residual,cacheRow_apply,Pi.add_apply]
    have he (c : Fin n) : (if s.active c then (a c+b c)*s.rows c v else 0)=
        (if s.active c then a c*s.rows c v else 0)+(if s.active c then b c*s.rows c v else 0) := by
      cases s.active c <;> simp
      ring
    simp only [he,Finset.sum_add_distrib]
    ring
  map_smul' a row := by
    funext v
    simp only [residual,cacheRow_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    have he (c : Fin n) : (if s.active c then (a*row c)*s.rows c v else 0)=
        a*(if s.active c then row c*s.rows c v else 0) := by
      cases s.active c <;> simp
      ring
    simp only [he,← Finset.mul_sum]
    ring

/-- Computed residual elimination kills every existing working basis row. -/
theorem residual_basis {m n : ℕ} (s : State m n) (hg : Good s) (c : Fin n) :
    residual s (s.rows c)=0 := by
  by_cases hc : s.active c=true
  · funext v
    rw [residual,cacheRow_apply]
    have he (d : Fin n) : (if s.active d then s.rows c d*s.rows d v else 0)=
        if d=c then s.rows c v else 0 := by
      by_cases hd : s.active d=true
      · rw [ite_eq_left hd,hg.pivot c d hc hd]
        by_cases hdc : d=c
        · subst d; simp
        · simp only [ite_eq_right hdc,ite_eq_right (Ne.symm hdc),zero_mul]
      · have hdc : d≠c := by intro h; subst d; exact hd hc
        simp only [ite_eq_right hd,ite_eq_right hdc]
    simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true,sub_self,Pi.zero_apply]
  · rw [hg.inactive c (Bool.eq_false_iff.mpr hc)]
    exact (residualLinear s).map_zero

/-- Exact span membership is decided by the actual residual, without a span oracle. -/
theorem residual_zero_iff {m n : ℕ} (s : State m n) (hg : Good s) (row : Row n) :
    residual s row=0 ↔ row∈workSpan s := by
  constructor
  · intro hz
    have he : row=∑ c : Fin n,if s.active c then row c • s.rows c else 0 := by
      have hh := residual_eq s row
      rw [hz] at hh
      exact sub_eq_zero.mp hh.symm
    rw [he]
    exact eliminated_mem s row
  · intro hrow
    have hle : workSpan s≤LinearMap.ker (residualLinear s) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨c,rfl⟩
      exact residual_basis s hg c
    exact hle hrow

/-- Concrete exact span-membership test for rational replacement rows as well. -/
def inSpan {m n : ℕ} (s : State m n) (row : Row n) : Bool :=
  (findPivot (residual s row)).isNone

/-- The computed rational elimination test is the actual full-span predicate. -/
theorem inSpan_correct {m n : ℕ} (s : State m n) (hg : Good s) (row : Row n) :
    inSpan s row=true ↔ row∈workSpan s := by
  constructor
  · intro h
    have hp : findPivot (residual s row)=none := by
      simpa only [inSpan,Option.isNone_iff_eq_none] using h
    exact (residual_zero_iff s hg row).mp (findPivot_none _ hp)
  · intro h
    have hz := (residual_zero_iff s hg row).mpr h
    simp [inSpan,hz,findPivot]

end RiemannGaussian.SemiprimeRowSelectionExecution
