/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRowSelectionBitArithmetic

/-! # Actual physical-word row selection

The runtime state consists of finite word/Boolean/ID lists. All rational
arithmetic runs the Boolean primitives; logical values occur only in proofs.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
namespace RiemannGaussian.SemiprimeRowSelectionBits
open scoped BigOperators
open SemiprimeRowSelectionExecution SemiprimeRowSelectionBitArithmetic
open SemiprimeMaterializedSelectionTemporaries SemiprimeRationalBits
open SemiprimeBitArithmetic SemiprimeBitDivision

/-- Concrete physical selector state. No rational matrix is a runtime field. -/
structure State (m : ℕ) where
  /-- Cached active pivot flags. -/
  active : List Bool
  /-- Cached physical rational-word matrix. -/
  rows : List (List RationalWord)
  /-- Original input row IDs, never normalized or replaced. -/
  selected : List (Fin m)

/-- A physical selector result with every retained stage clock. -/
structure StateReport (m : ℕ) where
  /-- Actual returned physical state. -/
  state : State m
  /-- Boolean arithmetic and finite list/control work. -/
  clock : ℕ

/-- Materialized physical row and its actual loop report. -/
structure RowReport where
  /-- Stored physical row entries. -/
  words : List RationalWord
  /-- Retained instruction and traversal work. -/
  clock : ℕ

/-- Cache every supplied executed coordinate report once in literal order. -/
def runRow (n : ℕ) (f : Fin n → RationalReport) : RowReport :=
  let reports := List.ofFn f
  ⟨reports.map (fun x => x.word),(reports.map (fun x => x.clock)).sum+10*n+5⟩

/-- Cached row shape is exact. -/
theorem runRow_length (n : ℕ) (f : Fin n → RationalReport) : (runRow n f).words.length=n := by
  simp [runRow]

/-- An actual list scan retrieves the computed coordinate, with no lookup oracle. -/
theorem runRow_read (n : ℕ) (f : Fin n → RationalReport) (v : Fin n) :
    (readWord (runRow n f).words v.val).value=(f v).word := by
  simp only [runRow,List.map_ofFn,readWord]
  exact readAt_ofFn _ _ v

/-- Every executed coordinate clock is retained, with explicit conservative
finite cache/allocation traversal allowance. -/
theorem runRow_clock (n B : ℕ) (f : Fin n → RationalReport) (h : ∀ i,(f i).clock ≤ B) :
    (runRow n f).clock ≤ n*B+10*n+5 := by
  have hs := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin n))) => h i)
  simp only [runRow,List.map_ofFn,List.sum_ofFn]
  simpa using Nat.add_le_add_right (Nat.add_le_add_right hs (10*n)) 5

/-- Empty physical rows are literal legal zero words. -/
def empty (m n : ℕ) : StateReport m :=
  ⟨⟨List.ofFn (fun _ : Fin n => false),List.ofFn (fun _ : Fin n => List.ofFn (fun _ : Fin n => zeroWord)),[]⟩,n*(n+1)+n+2⟩

/-- Scan result is an original bounded column ID, not a rational pivot oracle. -/
structure ScanReport (n : ℕ) where
  /-- First actual nonzero physical numerator. -/
  pivot : Option (Fin n)
  /-- All list reads and complete numerator-bit scans. -/
  clock : ℕ

/-- Actual physical numerator nonzero test, including signed zero encodings. -/
def wordNonzero (word : RationalWord) : NonzeroReport := nonzeroBits word.numerator.magnitude

/-- Legal denominator words make the physical scan an exact rational-zero test. -/
theorem wordNonzero_correct (word : RationalWord) (hw : word.Valid) :
    (wordNonzero word).nonzero=true ↔ word.value≠0 := by
  rw [wordNonzero,nonzeroBits_correct,← SemiprimeBitIndexGeometry.signedWord_natAbs,Int.natAbs_pos]
  have hd : (bitValue word.denominator : ℚ)≠0 := by
    exact_mod_cast Nat.ne_of_gt hw
  constructor
  · intro hn
    exact div_ne_zero (by exact_mod_cast hn) hd
  · intro hq hz
    apply hq
    simp [RationalWord.value,hz]

/-- Exact numerator scan cost depends on the PHYSICAL supplied padding. -/
theorem wordNonzero_clock (word : RationalWord) :
    (wordNonzero word).clock=3*word.numerator.magnitude.length+1 := nonzeroBits_cost _

/-- Execute first-nonzero search over the concrete column metadata list. -/
def scan {n : ℕ} (row : List RationalWord) : List (Fin n) → ScanReport n
  | [] => ⟨none,1⟩
  | c::cs =>
    let input := readWord row c.val
    let tested := wordNonzero input.value
    if tested.nonzero then ⟨some c,input.clock+tested.clock+2⟩ else
      let rest := scan row cs
      ⟨rest.pivot,input.clock+tested.clock+rest.clock+3⟩

/-- The actual bit scan has the same FIRST pivot as the old rational selector. -/
theorem scan_value {n : ℕ} (row : List RationalWord) (cols : List (Fin n)) (q : Fin n → ℚ)
    (hv : ∀ c∈cols,(readWord row c.val).value.Valid ∧ (readWord row c.val).value.value=q c) :
    (scan row cols).pivot=cols.find? (fun c => decide (q c≠0)) := by
  induction cols with
  | nil => rfl
  | cons c cs ih =>
    have h := hv c (by simp)
    have he : (wordNonzero (readWord row c.val).value).nonzero=decide (q c≠0) := by
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq,h.2] using wordNonzero_correct _ h.1
    have hi := ih (fun a ha => hv a (by simp [ha]))
    by_cases hq : q c≠0 <;> simp [scan,he,hq,hi]

/-- A complete pivot scan pays list reads, physical numerator bits and control. -/
theorem scan_clock {n : ℕ} (row : List RationalWord) (cols : List (Fin n)) (W : ℕ)
    (hr : row.length ≤ n) (hw : ∀ c∈cols,Width (readWord row c.val).value W) :
    (scan row cols).clock ≤ cols.length*(2*n+3*W+6)+1 := by
  induction cols with
  | nil => simp [scan]
  | cons c cs ih =>
    have hi := ih (fun a ha => hw a (by simp [ha]))
    have hread := readAt_clock zeroWord row c.val
    have hword := (hw c (by simp)).1
    have htest := wordNonzero_clock (readWord row c.val).value
    simp only [scan]
    split <;> simp only [List.length_cons,Nat.add_mul,one_mul] <;> dsimp only [readWord] at * <;> omega

/-- Compute/cache all physical residual coordinates. -/
def residualRow {m : ℕ} (n : ℕ) (template : List Bool) (s : State m) (row : List RationalWord) : RowReport :=
  runRow n (fun v => residualWord n template row s.rows v.val)

/-- Normalize every coordinate using one retained pivot-word read. -/
def normalizeRow (n : ℕ) (template : List Bool) (row : List RationalWord) (p : Fin n) : RowReport :=
  let pivot := readWord row p.val
  let out := runRow n (fun v =>
    let input := readWord row v.val
    let result := normalizeWords input.value pivot.value template
    ⟨result.word,input.clock+result.clock+2⟩)
  ⟨out.words,pivot.clock+out.clock+2⟩

/-- A back-update row executes actual reads and physical multiplication/subtraction. -/
def updateRow {m : ℕ} (n : ℕ) (template : List Bool) (s : State m)
    (normalized : List RationalWord) (p c : Fin n) : RowReport :=
  let active := readAt false s.active c.val
  if c=p then ⟨normalized,active.clock+2⟩ else if active.value then
    let coefficient := readCell s.rows c.val p.val
    let out := runRow n (fun v =>
      let old := readCell s.rows c.val v.val
      let value := readWord normalized v.val
      let result := backWords old.value coefficient.value value.value template
      ⟨result.word,old.clock+value.clock+result.clock+3⟩)
    ⟨out.words,active.clock+coefficient.clock+out.clock+4⟩
  else ⟨List.ofFn (fun _ : Fin n => zeroWord),active.clock+n+2⟩

/-- One full physical insertion. The residual cache is retained and reused by
scan and normalization; no scalar stage is a function-valued result oracle. -/
def insert {m n : ℕ} (template : List Bool) (s : State m) (id : Fin m) (row : List RationalWord) : StateReport m :=
  let residual := residualRow n template s row
  let tested := scan residual.words (List.finRange n)
  match tested.pivot with
  | none => ⟨s,residual.clock+tested.clock+n+3⟩
  | some p =>
      let normalized := normalizeRow n template residual.words p
      let updates := List.ofFn (fun c : Fin n => updateRow n template s normalized.words p c)
      let activeReports := List.ofFn (fun c : Fin n =>
        if c=p then (true,2) else
          let old := readAt false s.active c.val
          (old.value,old.clock+2))
      ⟨⟨activeReports.map Prod.fst,updates.map RowReport.words,id::s.selected⟩,
        residual.clock+tested.clock+normalized.clock+(updates.map RowReport.clock).sum+
          (activeReports.map Prod.snd).sum+20*n+20⟩

/-- Whole physical selector on actual original input word rows and IDs. -/
def run {m : ℕ} (n : ℕ) (template : List Bool) (inputs : List (List RationalWord)) :
    List (Fin m) → StateReport m
  | [] => empty m n
  | id::ids =>
      let previous := run n template inputs ids
      let input := readAt [] inputs id.val
      let next := insert (n := n) template previous.state id input.value
      ⟨next.state,previous.clock+input.clock+next.clock+3⟩

/-- Concrete row-cache refinement: only original/cached input word meanings,
legality and physical width, not a supplied arithmetic result or minor. -/
structure RowRefines {n : ℕ} (words : List RationalWord) (row : Fin n → ℚ) (W : ℕ) : Prop where
  /-- The actual finite row has its declared number of cells. -/
  length_eq : words.length=n
  /-- Every original bounded coordinate is a legal physical cached value. -/
  cell : ∀ v : Fin n,(readWord words v.val).value.Valid ∧
    Width (readWord words v.val).value W ∧ (readWord words v.val).value.value=row v

/-- Full physical cache refinement to one exact old selector state. -/
structure Refines {m n : ℕ} (physical : State m) (logical : SemiprimeRowSelectionExecution.State m n)
    (W : ℕ) : Prop where
  /-- Actual active-flag storage shape. -/
  active_length : physical.active.length=n
  /-- Actual matrix row storage shape. -/
  matrix_length : physical.rows.length=n
  /-- Every stored matrix row has n physical cells. -/
  row_lengths : ∀ row∈physical.rows,row.length=n
  /-- Active flags are exact computed flags. -/
  active_eq : ∀ c : Fin n,(readAt false physical.active c.val).value=logical.active c
  /-- All stored word values refine actual logical entries. -/
  cell : ∀ c v : Fin n,(readCell physical.rows c.val v.val).value.Valid ∧
    Width (readCell physical.rows c.val v.val).value W ∧
    (readCell physical.rows c.val v.val).value.value=logical.rows c v
  /-- The original selected IDs agree exactly, including order. -/
  selected_eq : physical.selected=logical.selected

/-- The actual allocated empty matrix refines literal zero without advice. -/
theorem empty_refines (m n W : ℕ) (hW : 0<W) :
    Refines (empty m n).state (SemiprimeRowSelectionExecution.empty m n) W := by
  have hz : zeroWord.Valid := by change 0<1; decide
  have hw : Width zeroWord W := by change 0 ≤ W ∧ 1 ≤ W; omega
  refine ⟨by simp [empty],by simp [empty],?_,?_,?_,rfl⟩
  · intro row hm
    simp only [empty,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    simp
  · intro c
    simp only [empty,readAt_ofFn,SemiprimeRowSelectionExecution.empty]
  · intro c v
    simp only [empty,readCell_ofFn,SemiprimeRowSelectionExecution.empty]
    exact ⟨hz,hw,SemiprimeDotBits.zeroWord_value⟩

/-- Physical residual row has all actual old residual coordinates and widths. -/
theorem residualRow_refines {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v| ≤ (2^bits : ℕ)) (j : Fin m)
    (template : List Bool) (ht : template.length=selectorWidth n bits)
    (s : State m) (row : List RationalWord)
    (hs : Refines s (SemiprimeRowSelectionExecution.run C ids) template.length)
    (hr : RowRefines row (originalRow C j) template.length) :
    RowRefines (residualRow n template s row).words
      (SemiprimeRowSelectionExecution.residual (SemiprimeRowSelectionExecution.run C ids) (originalRow C j))
      template.length := by
  refine ⟨runRow_length _ _,?_⟩
  intro v
  rw [residualRow,runRow_read]
  have h := residualWord_correct C ids bits hC j v template ht row s.rows hr.cell (fun c => hs.cell c v)
  exact ⟨h.2.1,h.2.2,h.1⟩

/-- Cached normalization shape is exact. -/
theorem normalizeRow_length (n : ℕ) (template : List Bool) (row : List RationalWord) (p : Fin n) :
    (normalizeRow n template row p).words.length=n := runRow_length _ _

/-- Normalization really uses the computed residual cache, not a chosen answer. -/
theorem normalizeRow_refines {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v| ≤ (2^bits : ℕ)) (j : Fin m)
    (template : List Bool) (ht : template.length=selectorWidth n bits)
    (row : List RationalWord) (p : Fin n)
    (hr : RowRefines row (SemiprimeRowSelectionTracked.residualRun
      (SemiprimeRowSelectionExecution.run C ids) (originalRow C j)).row template.length) :
    RowRefines (normalizeRow n template row p).words
      (SemiprimeRowSelectionTracked.normalizeRun
        (SemiprimeRowSelectionTracked.residualRun (SemiprimeRowSelectionExecution.run C ids) (originalRow C j)).row p).row
      template.length := by
  refine ⟨normalizeRow_length _ _ _ _,?_⟩
  intro v
  simp only [normalizeRow,runRow_read]
  have h := normalizeWords_correct_cost C ids bits hC j p v
    (readWord row v.val).value (readWord row p.val).value template ht
    (hr.cell v).1 (hr.cell p).1 (hr.cell v).2.1 (hr.cell p).2.1 (hr.cell v).2.2 (hr.cell p).2.2
  exact ⟨h.2.1,h.2.2.1,h.1⟩

/-- Every branch of the physical row update returns n stored cells. -/
theorem updateRow_length {m n : ℕ} (template : List Bool) (s : State m)
    (normalized : List RationalWord) (p c : Fin n) (hn : normalized.length=n) :
    (updateRow n template s normalized p c).words.length=n := by
  unfold updateRow
  split
  · exact hn
  · dsimp only
    split
    · exact runRow_length _ _
    · simp

/-- Actual normalized row equals the frozen selector's mathematical normalization. -/
theorem normalized_cached_eq {m n : ℕ} (s : SemiprimeRowSelectionExecution.State m n)
    (row : Row n) (p v : Fin n) :
    (SemiprimeRowSelectionTracked.normalizeRun (SemiprimeRowSelectionTracked.residualRun s row).row p).row v=
      SemiprimeRowSelectionExecution.normalized s row p v := by
  rw [SemiprimeRowSelectionTracked.normalizeRun_value,SemiprimeRowSelectionTracked.residualRun_value,
    SemiprimeRowSelectionExecution.normalized,cacheRow_apply]

/-- Physical back elimination refines EACH old update row, including inactive
zero slots and the selected pivot's retained normalized payload. -/
theorem updateRow_refines {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v| ≤ (2^bits : ℕ)) (j : Fin m)
    (template : List Bool) (ht : template.length=selectorWidth n bits)
    (s : State m) (normalized : List RationalWord) (p c : Fin n)
    (hs : Refines s (SemiprimeRowSelectionExecution.run C ids) template.length)
    (hn : RowRefines normalized (SemiprimeRowSelectionExecution.normalized
      (SemiprimeRowSelectionExecution.run C ids) (originalRow C j) p) template.length) :
    RowRefines (updateRow n template s normalized p c).words
      (fun v => if c=p then SemiprimeRowSelectionExecution.normalized
          (SemiprimeRowSelectionExecution.run C ids) (originalRow C j) p v else
        if (SemiprimeRowSelectionExecution.run C ids).active c then
          (SemiprimeRowSelectionExecution.run C ids).rows c v-
          (SemiprimeRowSelectionExecution.run C ids).rows c p*
          SemiprimeRowSelectionExecution.normalized (SemiprimeRowSelectionExecution.run C ids) (originalRow C j) p v
        else 0) template.length := by
  refine ⟨updateRow_length _ _ _ _ _ hn.length_eq,?_⟩
  intro v
  by_cases hcp : c=p
  · subst c
    simpa only [updateRow,ite_true] using hn.cell v
  · rw [updateRow,ite_eq_right hcp,hs.active_eq]
    cases hc : (SemiprimeRowSelectionExecution.run C ids).active c with
    | false =>
      simp only [Bool.false_eq_true,ite_false,readWord,readAt_ofFn,hcp]
      have hz : zeroWord.Valid := by change 0<1; decide
      have hw : Width zeroWord template.length := by
        change 0 ≤ template.length ∧ 1 ≤ template.length
        rw [ht]
        unfold selectorWidth
        omega
      simpa only [hcp,ite_false,hc] using ⟨hz,hw,SemiprimeDotBits.zeroWord_value⟩
    | true =>
      simp only [ite_true,runRow_read]
      have hnv : (readWord normalized v.val).value.value=
        (SemiprimeRowSelectionTracked.normalizeRun (SemiprimeRowSelectionTracked.residualRun
          (SemiprimeRowSelectionExecution.run C ids) (originalRow C j)).row p).row v := by
        rw [(hn.cell v).2.2,normalized_cached_eq]
      have h := backWords_correct C ids bits hC j p c v hcp hc
        (readCell s.rows c.val v.val).value (readCell s.rows c.val p.val).value
        (readWord normalized v.val).value template ht
        (hs.cell c v).1 (hs.cell c p).1 (hn.cell v).1
        (hs.cell c v).2.2 (hs.cell c p).2.2 hnv
      exact ⟨h.2.1,h.2.2,by simpa only [hcp,ite_false,hc,ite_true,normalized_cached_eq] using h.1⟩

/-- The actual physical residual scan chooses exactly the frozen first pivot. -/
theorem residual_scan_eq {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v| ≤ (2^bits : ℕ)) (j : Fin m)
    (template : List Bool) (ht : template.length=selectorWidth n bits)
    (s : State m) (row : List RationalWord)
    (hs : Refines s (SemiprimeRowSelectionExecution.run C ids) template.length)
    (hr : RowRefines row (originalRow C j) template.length) :
    (scan (residualRow n template s row).words (List.finRange n)).pivot=
      findPivot (SemiprimeRowSelectionExecution.residual
        (SemiprimeRowSelectionExecution.run C ids) (originalRow C j)) := by
  have hres := residualRow_refines C ids bits hC j template ht s row hs hr
  exact scan_value _ _ _ (fun c _ => ⟨(hres.cell c).1,(hres.cell c).2.2⟩)

/-- Entire physical insertion refines the actual original-row selection step,
including active flags, all matrix slots and the original selected-ID order. -/
theorem insert_refines {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v| ≤ (2^bits : ℕ)) (j : Fin m)
    (template : List Bool) (ht : template.length=selectorWidth n bits)
    (s : State m) (row : List RationalWord)
    (hs : Refines s (SemiprimeRowSelectionExecution.run C ids) template.length)
    (hr : RowRefines row (originalRow C j) template.length) :
    Refines (insert (n := n) template s j row).state
      (SemiprimeRowSelectionExecution.insert (SemiprimeRowSelectionExecution.run C ids) j (originalRow C j))
      template.length := by
  have hscan := residual_scan_eq C ids bits hC j template ht s row hs hr
  cases hp : findPivot (SemiprimeRowSelectionExecution.residual
      (SemiprimeRowSelectionExecution.run C ids) (originalRow C j)) with
  | none => simpa only [insert,hscan,hp,SemiprimeRowSelectionExecution.insert] using hs
  | some p =>
    simp only [insert,hscan,hp,SemiprimeRowSelectionExecution.insert]
    let normalized := normalizeRow n template (residualRow n template s row).words p
    have hres := residualRow_refines C ids bits hC j template ht s row hs hr
    have hres' : RowRefines (residualRow n template s row).words
        (SemiprimeRowSelectionTracked.residualRun
          (SemiprimeRowSelectionExecution.run C ids) (originalRow C j)).row template.length := by
      rw [SemiprimeRowSelectionTracked.residualRun_value]
      exact hres
    have hnorm' := normalizeRow_refines C ids bits hC j template ht _ p hres'
    have hnorm : RowRefines normalized.words
        (SemiprimeRowSelectionExecution.normalized (SemiprimeRowSelectionExecution.run C ids) (originalRow C j) p)
        template.length := by
      have he : (SemiprimeRowSelectionTracked.normalizeRun
          (SemiprimeRowSelectionTracked.residualRun (SemiprimeRowSelectionExecution.run C ids) (originalRow C j)).row p).row=
          SemiprimeRowSelectionExecution.normalized (SemiprimeRowSelectionExecution.run C ids) (originalRow C j) p := by
        funext v
        exact normalized_cached_eq _ _ _ _
      rw [he] at hnorm'
      exact hnorm'
    let updates := List.ofFn (fun c : Fin n => updateRow n template s normalized.words p c)
    let flags := List.ofFn (fun c : Fin n => if c=p then (true,2) else
      let old := readAt false s.active c.val
      (old.value,old.clock+2))
    change Refines ⟨flags.map Prod.fst,updates.map RowReport.words,j::s.selected⟩
      (SemiprimeRowSelectionExecution.pivotInsert (SemiprimeRowSelectionExecution.run C ids) j (originalRow C j) p) _
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simp [flags]
    · simp [updates]
    · intro r hm
      change r∈updates.map RowReport.words at hm
      obtain ⟨report,hreport,rfl⟩ := List.mem_map.mp hm
      obtain ⟨c,rfl⟩ := List.mem_ofFn.mp hreport
      exact updateRow_length _ _ _ _ _ hnorm.length_eq
    · intro c
      simp only [flags,List.map_ofFn,Function.comp_def,readAt_ofFn,SemiprimeRowSelectionExecution.pivotInsert]
      split_ifs <;> simp only [hs.active_eq]
    · intro c v
      have hu := (updateRow_refines C ids bits hC j template ht s normalized.words p c hs hnorm).cell v
      change (readCell (updates.map RowReport.words) c.val v.val).value.Valid ∧ _
      simp only [updates,List.map_ofFn,Function.comp_def,readCell,readAt_ofFn]
      simpa only [readWord,SemiprimeRowSelectionExecution.pivotInsert,cacheMatrix_apply] using hu
    · simp only [SemiprimeRowSelectionExecution.pivotInsert,hs.selected_eq]

/-- The WHOLE physical list program returns precisely the proved selector's
state, on original encoded integer inputs. Original coefficient bounds are the
only height premise; no state/minor/output-fit advice is an input. -/
theorem run_refines {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v| ≤ (2^bits : ℕ))
    (template : List Bool) (ht : template.length=selectorWidth n bits)
    (inputs : List (List RationalWord))
    (hinput : ∀ j : Fin m,RowRefines (readAt [] inputs j.val).value (originalRow C j) template.length) :
    Refines (run n template inputs ids).state (SemiprimeRowSelectionExecution.run C ids) template.length := by
  induction ids with
  | nil =>
    exact empty_refines m n template.length (by rw [ht]; unfold selectorWidth; omega)
  | cons j ids ih =>
    exact insert_refines C ids bits hC j template ht _ _ ih (hinput j)

/-- The actually returned original integer rows are exactly the old selected
rows, including their order. No arbitrary row-space answer is substituted. -/
theorem run_selected_eq {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v| ≤ (2^bits : ℕ))
    (template : List Bool) (ht : template.length=selectorWidth n bits)
    (inputs : List (List RationalWord))
    (hinput : ∀ j : Fin m,RowRefines (readAt [] inputs j.val).value (originalRow C j) template.length) :
    (run n template inputs ids).state.selected=(SemiprimeRowSelectionExecution.run C ids).selected :=
  (run_refines C ids bits hC template ht inputs hinput).selected_eq

/-- All coordinates, actual dot loops and row-cache allocation are paid. -/
def residualRowBudget (n W : ℕ) : ℕ := n*residualBudget n W+10*n+5

/-- Actual residual-row clock, without unit-cost matrix reads or rationals. -/
theorem residualRow_clock {m n : ℕ} (template : List Bool) (s : State m)
    (logical : SemiprimeRowSelectionExecution.State m n) (row : List RationalWord) (q : Row n)
    (ht : 0<template.length) (hs : Refines s logical template.length)
    (hr : RowRefines row q template.length) :
    (residualRow n template s row).clock ≤ residualRowBudget n template.length := by
  apply runRow_clock
  intro v
  exact residualWord_clock n template row s.rows v ht hr.length_eq.le hs.matrix_length.le
    (fun r hm => (hs.row_lengths r hm).le) (fun c => (hr.cell c).2.1) (fun c => (hs.cell c v).2.1)

/-- One cached pivot read, all physical divisions and all row-cache traversals. -/
def normalizeRowBudget (n W : ℕ) : ℕ :=
  (2*n+1)+(n*(2*n+1+40002*(W+1)^3+2)+10*n+5)+2

/-- The entire normalization loop, not just one division, has its actual
finite-read and Boolean-arithmetic clock retained. -/
theorem normalizeRow_clock {n : ℕ} (template : List Bool) (row : List RationalWord) (p : Fin n)
    (ht : 0<template.length) (hr : row.length ≤ n)
    (hw : ∀ v : Fin n,Width (readWord row v.val).value template.length) :
    (normalizeRow n template row p).clock ≤ normalizeRowBudget n template.length := by
  have hc (v : Fin n) :
      (readWord row v.val).clock+
        (normalizeWords (readWord row v.val).value (readWord row p.val).value template).clock+2 ≤
      2*n+1+40002*(template.length+1)^3+2 := by
    have hread := readAt_clock zeroWord row v.val
    have hnorm := normalizeWords_clock _ _ template ht (hw v) (hw p)
    dsimp only [readWord] at hread hnorm ⊢
    omega
  have hout := runRow_clock n (2*n+1+40002*(template.length+1)^3+2)
    (fun v =>
      let input := readWord row v.val
      let result := normalizeWords input.value (readWord row p.val).value template
      (⟨result.word,input.clock+result.clock+2⟩ : RationalReport)) hc
  have hp := readAt_clock zeroWord row p.val
  unfold normalizeRow normalizeRowBudget
  dsimp only
  dsimp only [readWord] at hout hp ⊢
  omega

/-- Uniform branch budget for each actual physical matrix-update row. -/
def updateRowBudget (n W : ℕ) : ℕ :=
  (3*n+3)+(4*n+4)+(n*(6*n+8+60003*(W+1)^3)+10*n+5)+4

/-- Every updated row pays its actual flag/coefficient reads, all physical
back-elimination calls and row storage; pivot/zero branches are also charged. -/
theorem updateRow_clock {m n : ℕ} (template : List Bool) (s : State m)
    (logical : SemiprimeRowSelectionExecution.State m n) (normalized : List RationalWord)
    (q : Row n) (p c : Fin n) (ht : 0<template.length)
    (hs : Refines s logical template.length) (hn : RowRefines normalized q template.length) :
    (updateRow n template s normalized p c).clock ≤ updateRowBudget n template.length := by
  have hactive := readAt_clock false s.active c.val
  rw [hs.active_length] at hactive
  have hcoeff := readCell_clock s.rows n c.val p.val hs.matrix_length.le
    (fun r hm => (hs.row_lengths r hm).le)
  have hc (v : Fin n) :
      (readCell s.rows c.val v.val).clock+(readWord normalized v.val).clock+
        (backWords (readCell s.rows c.val v.val).value (readCell s.rows c.val p.val).value
          (readWord normalized v.val).value template).clock+3 ≤
      6*n+8+60003*(template.length+1)^3 := by
    have ho := readCell_clock s.rows n c.val v.val hs.matrix_length.le
      (fun r hm => (hs.row_lengths r hm).le)
    have hv := readAt_clock zeroWord normalized v.val
    rw [hn.length_eq] at hv
    have hb := backWords_clock _ _ _ template ht (hs.cell c v).2.1
      (hs.cell c p).2.1 (hn.cell v).2.1
    dsimp only [readWord] at hb hv ⊢
    omega
  have hout := runRow_clock n (6*n+8+60003*(template.length+1)^3)
    (fun v =>
      let old := readCell s.rows c.val v.val
      let value := readWord normalized v.val
      let result := backWords old.value (readCell s.rows c.val p.val).value value.value template
      (⟨result.word,old.clock+value.clock+result.clock+3⟩ : RationalReport)) hc
  dsimp only at hout
  unfold updateRow updateRowBudget
  split
  · dsimp only
    omega
  · dsimp only
    split <;> dsimp only <;> omega

/-- Physical first-pivot and full matrix-update insertion ledger. All terms
come from actual retained subreports; its degree is fixed independently of n. -/
def insertBudget (n W : ℕ) : ℕ :=
  residualRowBudget n W+(n*(2*n+3*W+6)+1)+normalizeRowBudget n W+
    n*updateRowBudget n W+n*(2*n+3)+20*n+20+n+3

/-- The WHOLE insertion has a polynomial bit-primitive/list-control clock.
Correctness and widths are derived from original integer bounds, not supplied
as state/minor/output-fit answers. Literal tape/address simulation is separate. -/
theorem insert_clock {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v| ≤ (2^bits : ℕ)) (j : Fin m)
    (template : List Bool) (ht : template.length=selectorWidth n bits)
    (s : State m) (row : List RationalWord)
    (hs : Refines s (SemiprimeRowSelectionExecution.run C ids) template.length)
    (hr : RowRefines row (originalRow C j) template.length) :
    (insert (n := n) template s j row).clock ≤  insertBudget n template.length := by
  have hpositive : 0<template.length := by rw [ht]; unfold selectorWidth; omega
  have hres := residualRow_refines C ids bits hC j template ht s row hs hr
  have hresCost := residualRow_clock template s _ row _ hpositive hs hr
  have hscan := scan_clock (residualRow n template s row).words (List.finRange n) template.length
    hres.length_eq.le (fun c _ => (hres.cell c).2.1)
  rw [List.length_finRange] at hscan
  unfold insert
  dsimp only
  split
  · dsimp only
    unfold insertBudget
    omega
  · rename_i p hp
    let normalized := normalizeRow n template (residualRow n template s row).words p
    have hnCost := normalizeRow_clock template (residualRow n template s row).words p hpositive
      hres.length_eq.le (fun v => (hres.cell v).2.1)
    have hres' : RowRefines (residualRow n template s row).words
        (SemiprimeRowSelectionTracked.residualRun (SemiprimeRowSelectionExecution.run C ids) (originalRow C j)).row
        template.length := by rw [SemiprimeRowSelectionTracked.residualRun_value]; exact hres
    have hn := normalizeRow_refines C ids bits hC j template ht _ p hres'
    have hu (c : Fin n) := updateRow_clock template s _ normalized.words _ p c hpositive hs hn
    have huSum := Finset.sum_le_sum (fun c (_ : c∈(Finset.univ : Finset (Fin n))) => hu c)
    have hf (c : Fin n) : (if c=p then (true,2) else
        let old := readAt false s.active c.val
        (old.value,old.clock+2)).2 ≤ 2*n+3 := by
      have h := readAt_clock false s.active c.val
      rw [hs.active_length] at h
      split_ifs <;> dsimp only <;> omega
    have hfSum := Finset.sum_le_sum (fun c (_ : c∈(Finset.univ : Finset (Fin n))) => hf c)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at huSum hfSum
    dsimp only
    simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def]
    unfold insertBudget
    change (residualRow n template s row).clock+
      (scan (residualRow n template s row).words (List.finRange n)).clock+
      normalized.clock+(∑ c : Fin n,(updateRow n template s normalized.words p c).clock)+
      (∑ c : Fin n,(if c=p then (true,2) else
        let old := readAt false s.active c.val
        (old.value,old.clock+2)).2)+20*n+20 ≤ _
    change normalized.clock ≤ normalizeRowBudget n template.length at hnCost
    dsimp only at huSum hfSum hnCost ⊢
    omega

/-- Entire selector clock, with every actual input-row read and initial state
allocation; this is an explicit fixed polynomial in m,n,W and row count. -/
def runBudget (m n W count : ℕ) : ℕ :=
  n*(n+1)+n+2+count*(2*m+1+insertBudget n W+3)

/-- Complete physical loop clock on encoded ORIGINAL integer inputs. All
stored widths are derived by run_refines and the actual pivot-minor invariant. -/
theorem run_clock {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v| ≤ (2^bits : ℕ))
    (template : List Bool) (ht : template.length=selectorWidth n bits)
    (inputs : List (List RationalWord)) (hshape : inputs.length ≤ m)
    (hinput : ∀ j : Fin m,RowRefines (readAt [] inputs j.val).value (originalRow C j) template.length) :
    (run n template inputs ids).clock ≤  runBudget m n template.length ids.length := by
  induction ids with
  | nil => simp [run,empty,runBudget]
  | cons j ids ih =>
    have href := run_refines C ids bits hC template ht inputs hinput
    have hstep := insert_clock C ids bits hC j template ht _ _ href (hinput j)
    have hread := readAt_clock ([] : List RationalWord) inputs j.val
    unfold run
    dsimp only
    unfold runBudget at ih ⊢
    simp only [List.length_cons,Nat.add_mul,one_mul]
    omega

/-- Logical interpretation of an actual word-list state, used only in proofs;
the physical selector never calls rational decoding. -/
def decodeState {m : ℕ} (n : ℕ) (s : State m) : SemiprimeRowSelectionExecution.State m n :=
  ⟨fun c => (readAt false s.active c.val).value,
    fun c v => (readCell s.rows c.val v.val).value.value,s.selected⟩

/-- Full state refinement implies exact old state equality after interpretation. -/
theorem Refines.decode_eq {m n W : ℕ} {physical : State m}
    {logical : SemiprimeRowSelectionExecution.State m n} (h : Refines physical logical W) :
    decodeState n physical=logical := by
  have ha := funext h.active_eq
  have hr := funext (fun c => funext (fun v => (h.cell c v).2.2))
  unfold decodeState
  rw [ha,hr,h.selected_eq]

/-- The entire returned physical matrix, flags and original row IDs decode to
the EXACT frozen executed selector, not merely an unspecified equal row space. -/
theorem run_decoded_eq {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v| ≤ (2^bits : ℕ))
    (template : List Bool) (ht : template.length=selectorWidth n bits)
    (inputs : List (List RationalWord))
    (hinput : ∀ j : Fin m,RowRefines (readAt [] inputs j.val).value (originalRow C j) template.length) :
    decodeState n (run n template inputs ids).state=SemiprimeRowSelectionExecution.run C ids :=
  (run_refines C ids bits hC template ht inputs hinput).decode_eq

end RiemannGaussian.SemiprimeRowSelectionBits
