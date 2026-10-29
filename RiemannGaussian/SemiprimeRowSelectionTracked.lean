/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRowSelectionExecution

/-! # Rational-operation counts of the actual cached row selector -/
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace RiemannGaussian.SemiprimeRowSelectionTracked
open scoped BigOperators
open SemiprimeRowSelectionExecution

/-- One actually computed scalar with the number of rational arithmetic calls. -/
structure ScalarRun where
  /-- Returned rational value. -/
  value : ℚ
  /-- Actual addition/subtraction/multiplication/division calls. -/
  operations : ℕ

/-- Reading an existing scalar does not perform rational arithmetic. -/
def scalar (value : ℚ) : ScalarRun := ⟨value,0⟩

/-- Instrument the actual rational sum. -/
def add (a b : ScalarRun) : ScalarRun := ⟨a.value+b.value,a.operations+b.operations+1⟩

/-- Instrument the actual rational difference. -/
def sub (a b : ScalarRun) : ScalarRun := ⟨a.value-b.value,a.operations+b.operations+1⟩

/-- Instrument the actual rational product. -/
def mul (a b : ScalarRun) : ScalarRun := ⟨a.value*b.value,a.operations+b.operations+1⟩

/-- Instrument the actual rational quotient. -/
def divide (a b : ScalarRun) : ScalarRun := ⟨a.value/b.value,a.operations+b.operations+1⟩

/-- Literal finite scalar summation, including its addition calls. -/
def sumRun : {n : ℕ} → (Fin n → ScalarRun) → ScalarRun
  | 0,_ => scalar 0
  | _+1,f => add (f 0) (sumRun (f ∘ Fin.succ))

/-- Instrumented summation returns precisely the finite rational sum. -/
theorem sumRun_value {n : ℕ} (f : Fin n → ScalarRun) :
    (sumRun f).value=∑ i,(f i).value := by
  induction n with
  | zero => simp [sumRun,scalar]
  | succ n ih => simp only [sumRun,add,ih,Fin.sum_univ_succ,Function.comp_apply]

/-- Every child operation and all n addition calls are paid. -/
theorem sumRun_operations {n : ℕ} (f : Fin n → ScalarRun) :
    (sumRun f).operations=(∑ i,(f i).operations)+n := by
  induction n with
  | zero => simp [sumRun,scalar]
  | succ n ih => simp only [sumRun,add,ih,Fin.sum_univ_succ,Function.comp_apply]; omega

/-- A materialized row and the arithmetic actually used in its coordinate loops. -/
structure RowRun (n : ℕ) where
  /-- Stored computed values. -/
  row : Row n
  /-- Sum of all coordinate-operation calls. -/
  operations : ℕ

/-- Evaluate each coordinate once and cache its result before later reads. -/
def buildRow {n : ℕ} (f : Fin n → ScalarRun) : RowRun n :=
  let data := Vector.ofFn f
  ⟨fun i => (data.get i).value,∑ i,(data.get i).operations⟩

/-- The cached coordinate is exactly the scalar computation's value. -/
theorem buildRow_value {n : ℕ} (f : Fin n → ScalarRun) (i : Fin n) :
    (buildRow f).row i=(f i).value := by simp only [buildRow,Vector.get_ofFn]

/-- Uniform coordinate budgets sum over the actual finite coordinate loop. -/
theorem buildRow_operations {n budget : ℕ} (f : Fin n → ScalarRun)
    (h : ∀ i,(f i).operations≤budget) : (buildRow f).operations≤n*budget := by
  simp only [buildRow,Vector.get_ofFn]
  exact (Finset.sum_le_sum (fun i _ => h i)).trans_eq (by simp)

/-- Execute one residual with actual tracked products, additions and subtraction. -/
def residualRun {m n : ℕ} (s : State m n) (row : Row n) : RowRun n :=
  buildRow (fun v => sub (scalar (row v)) (sumRun (fun c =>
    if s.active c then mul (scalar (row c)) (scalar (s.rows c v)) else scalar 0)))

/-- The tracked residual is exactly the proved cached Gaussian residual. -/
theorem residualRun_value {m n : ℕ} (s : State m n) (row : Row n) :
    (residualRun s row).row=residual s row := by
  funext v
  simp only [residualRun,buildRow_value,sub,scalar,sumRun_value,SemiprimeRowSelectionExecution.residual,cacheRow_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  cases s.active c <;> rfl

/-- Every actual residual coordinate pays at most n products, n adds and one sub. -/
theorem residualRun_operations {m n : ℕ} (s : State m n) (row : Row n) :
    (residualRun s row).operations≤n*(2*n+1) := by
  apply buildRow_operations
  intro v
  have hc : ∀ c : Fin n,
      (if s.active c then mul (scalar (row c)) (scalar (s.rows c v)) else scalar 0).operations≤1 := by
    intro c
    cases s.active c <;> simp [scalar,mul]
  have hh := Finset.sum_le_sum (fun c (_ : c∈(Finset.univ : Finset (Fin n))) => hc c)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hh
  simp only [scalar] at hh
  simp only [sub,scalar,sumRun_operations]
  omega

/-- Normalize the already computed residual once, avoiding repeated residual work. -/
def normalizeRun {n : ℕ} (reduced : Row n) (pivot : Fin n) : RowRun n :=
  buildRow (fun v => divide (scalar (reduced v)) (scalar (reduced pivot)))

/-- Actual normalized coordinates have their exact rational meaning. -/
theorem normalizeRun_value {n : ℕ} (reduced : Row n) (pivot v : Fin n) :
    (normalizeRun reduced pivot).row v=reduced v/reduced pivot := by
  simp only [normalizeRun,buildRow_value,divide,scalar]

/-- Normalization computes exactly one division per coordinate. -/
theorem normalizeRun_operations {n : ℕ} (reduced : Row n) (pivot : Fin n) :
    (normalizeRun reduced pivot).operations≤n := by
  exact (buildRow_operations _ (budget:=1) (by intro i; rfl)).trans_eq (Nat.mul_one n)

/-- Materialized matrix values and their actual coordinate arithmetic. -/
structure MatrixRun (n : ℕ) where
  /-- Stored computed matrix. -/
  rows : Fin n → Row n
  /-- Sum of the coordinate arithmetic calls. -/
  operations : ℕ

/-- Evaluate every matrix coordinate once before retaining its finite array. -/
def buildMatrix {n : ℕ} (f : Fin n → Fin n → ScalarRun) : MatrixRun n :=
  let data := Vector.ofFn (fun i => Vector.ofFn (f i))
  ⟨fun i v => ((data.get i).get v).value,∑ i,∑ v,((data.get i).get v).operations⟩

/-- Matrix caching retains exactly the actual computed scalar value. -/
theorem buildMatrix_value {n : ℕ} (f : Fin n → Fin n → ScalarRun) (i v : Fin n) :
    (buildMatrix f).rows i v=(f i v).value := by simp only [buildMatrix,Vector.get_ofFn]

/-- The finite matrix loops pay n squared coordinate budgets. -/
theorem buildMatrix_operations {n budget : ℕ} (f : Fin n → Fin n → ScalarRun)
    (h : ∀ i v,(f i v).operations≤budget) : (buildMatrix f).operations≤n*n*budget := by
  simp only [buildMatrix,Vector.get_ofFn]
  calc
    _ ≤ ∑ _i : Fin n,∑ _v : Fin n,budget := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun v _ => h i v))
    _ = _ := by simp [Nat.mul_assoc]

/-- Execute all back-elimination coordinates from the cached normalized residual. -/
def updateRun {m n : ℕ} (s : State m n) (pivot : Fin n) (reduced : Row n) : MatrixRun n :=
  buildMatrix (fun c v => if c=pivot then scalar (reduced v) else if s.active c then
    sub (scalar (s.rows c v)) (mul (scalar (s.rows c pivot)) (scalar (reduced v))) else scalar 0)

/-- The actual back elimination computes the literal reduced-row update. -/
theorem updateRun_value {m n : ℕ} (s : State m n) (pivot c v : Fin n) (reduced : Row n) :
    (updateRun s pivot reduced).rows c v=
      if c=pivot then reduced v else if s.active c then s.rows c v-s.rows c pivot*reduced v else 0 := by
  simp only [updateRun,buildMatrix_value]
  split <;> rename_i hc
  · rfl
  · cases s.active c <;> rfl

/-- Every updated matrix cell has at most one actual product and subtraction. -/
theorem updateRun_operations {m n : ℕ} (s : State m n) (pivot : Fin n) (reduced : Row n) :
    (updateRun s pivot reduced).operations≤2*n*n := by
  have h := buildMatrix_operations
    (fun c v => if c=pivot then scalar (reduced v) else if s.active c then
      sub (scalar (s.rows c v)) (mul (scalar (s.rows c pivot)) (scalar (reduced v))) else scalar 0)
    (budget:=2) (by
      intro c v
      split
      · simp [scalar]
      · cases s.active c <;> simp [scalar,mul,sub])
  exact h.trans_eq (by ring)

/-- A computed pivot and the exact number of rational zero tests visited. -/
structure ScanRun (n : ℕ) where
  /-- First nonzero coordinate, if any. -/
  pivot : Option (Fin n)
  /-- Rational equality-to-zero tests. -/
  tests : ℕ

/-- Literal finite first-nonzero scan, stopping only on a computed nonzero value. -/
def scanRun {n : ℕ} (row : Row n) : List (Fin n) → ScanRun n
  | [] => ⟨none,0⟩
  | c::tail => if row c=0 then
      let child := scanRun row tail
      ⟨child.pivot,child.tests+1⟩
    else ⟨some c,1⟩

/-- The executed scan is the same literal predicate scan used by the selector. -/
theorem scanRun_value {n : ℕ} (row : Row n) (columns : List (Fin n)) :
    (scanRun row columns).pivot=columns.find? (fun c => decide (row c≠0)) := by
  induction columns with
  | nil => rfl
  | cons c tail ih =>
    by_cases hc : row c=0
    · simp [scanRun,hc,ih]
    · simp [scanRun,hc]

/-- At most one rational zero test per actual visited coordinate. -/
theorem scanRun_tests {n : ℕ} (row : Row n) (columns : List (Fin n)) :
    (scanRun row columns).tests≤columns.length := by
  induction columns with
  | nil => rfl
  | cons c tail ih =>
    dsimp only [scanRun]
    split <;> dsimp only [List.length_cons] <;> omega

/-- State returned by the actual cached arithmetic and its accumulated operations. -/
structure StateRun (m n : ℕ) where
  /-- Actual selector state. -/
  state : State m n
  /-- Executed rational arithmetic operations. -/
  operations : ℕ
  /-- Actual rational pivot-zero tests. -/
  tests : ℕ

/-- Execute one real pivot selection, retaining the actual computed residual. -/
def insertRun {m n : ℕ} (s : State m n) (j : Fin m) (row : Row n) : StateRun m n :=
  let reduced := residualRun s row
  let scanned := scanRun reduced.row (List.finRange n)
  match scanned.pivot with
  | none => ⟨s,reduced.operations,scanned.tests⟩
  | some pivot =>
      let normalizationInput := residualRun s row
      let normalized := normalizeRun normalizationInput.row pivot
      let updated := updateRun s pivot normalized.row
      ⟨{ active := fun c => if c=pivot then true else s.active c
         rows := updated.rows
         selected := j::s.selected },reduced.operations+normalizationInput.operations+normalized.operations+updated.operations,scanned.tests⟩

/-- The instrumented data path returns the complete previously proved selection step. -/
theorem insertRun_value {m n : ℕ} (s : State m n) (j : Fin m) (row : Row n) :
    (insertRun s j row).state=SemiprimeRowSelectionExecution.insert s j row := by
  dsimp only [insertRun]
  rw [scanRun_value,residualRun_value]
  unfold SemiprimeRowSelectionExecution.insert findPivot
  cases hp : (List.finRange n).find? (fun c => decide (SemiprimeRowSelectionExecution.residual s row c≠0)) with
  | none => rfl
  | some pivot =>
    dsimp only [pivotInsert]
    congr 1
    funext c v
    rw [updateRun_value,normalizeRun_value]
    simp only [cacheMatrix_apply,normalized,cacheRow_apply]

/-- A complete row insertion has an explicit polynomial rational-operation bound. -/
theorem insertRun_operations {m n : ℕ} (s : State m n) (j : Fin m) (row : Row n) :
    (insertRun s j row).operations≤8*(n+1)^2 := by
  have hr := residualRun_operations s row
  dsimp only [insertRun]
  rw [scanRun_value]
  split
  · exact hr.trans (by nlinarith)
  · rename_i pivot hp
    have hn := normalizeRun_operations (residualRun s row).row pivot
    have hu := updateRun_operations s pivot (normalizeRun (residualRun s row).row pivot).row
    dsimp only
    nlinarith

/-- Execute the full row list with the actual cached arithmetic frontend. -/
def runTracked {m n : ℕ} (C : Fin m → Fin n → ℤ) : List (Fin m) → StateRun m n
  | [] => ⟨empty m n,0,0⟩
  | j::tail =>
      let previous := runTracked C tail
      let step := insertRun previous.state j (originalRow C j)
      ⟨step.state,previous.operations+step.operations,previous.tests+step.tests⟩

/-- The counted implementation returns exactly the proved original-row selector. -/
theorem runTracked_value {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m)) :
    (runTracked C ids).state=run C ids := by
  induction ids with
  | nil => rfl
  | cons j tail ih => simp only [runTracked,insertRun_value,ih,run]; rfl

/-- Whole-list rational-operation count, charged from its actual arithmetic loops. -/
theorem runTracked_operations {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m)) :
    (runTracked C ids).operations≤ ids.length*8*(n+1)^2 := by
  induction ids with
  | nil => simp [runTracked]
  | cons j tail ih =>
    have h := insertRun_operations (runTracked C tail).state j (originalRow C j)
    dsimp only [runTracked,List.length_cons]
    nlinarith


/-- Every row insertion pays its actual finite pivot tests. -/
theorem insertRun_tests {m n : ℕ} (s : State m n) (j : Fin m) (row : Row n) :
    (insertRun s j row).tests≤n := by
  have h := scanRun_tests (residualRun s row).row (List.finRange n)
  simp only [List.length_finRange] at h
  dsimp only [insertRun]
  split <;> exact h

/-- Whole-list arithmetic selection has at most m*n rational zero tests. -/
theorem runTracked_tests {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m)) :
    (runTracked C ids).tests≤ ids.length*n := by
  induction ids with
  | nil => simp [runTracked]
  | cons j tail ih =>
    have h := insertRun_tests (runTracked C tail).state j (originalRow C j)
    dsimp only [runTracked,List.length_cons]
    nlinarith

end RiemannGaussian.SemiprimeRowSelectionTracked
