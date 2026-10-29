/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedSelectionTemporaries
import RiemannGaussian.SemiprimeDotBits

/-! # Physical scalar/list primitives for executed row selection

Only physical rational words and finite list metadata occur on the runtime path.
Canonical rational values and original pivot minors occur in specifications.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
namespace RiemannGaussian.SemiprimeRowSelectionBitArithmetic
open scoped BigOperators
open SemiprimeRowSelectionExecution SemiprimeMaterializedSelectionHeight
open SemiprimeMaterializedSelectionTemporaries SemiprimeRationalBits SemiprimeJetArrayHeight

/-- A positive common denominator obtained from the ACTUAL pivot determinant. -/
noncomputable def stateDenominator {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m)) : ℕ :=
  (pivotDenominator C ids).natAbs^2

/-- Squaring the proved nonzero determinant gives a legal positive denominator. -/
theorem stateDenominator_pos {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m)) :
    0<stateDenominator C ids := by
  unfold stateDenominator
  exact pow_pos (Int.natAbs_pos.mpr (pivotDenominator_ne_zero C ids)) _

/-- A signed determinant ratio has positive-square-denominator representation. -/
theorem ratio_representation (a b : ℤ) (hb : b≠0) (A B : ℕ)
    (ha : a.natAbs≤A) (hB : b.natAbs≤B) :
    Representation ((a : ℚ)/(b : ℚ)) (b.natAbs^2) (A*B) := by
  refine ⟨a*b,?_,?_⟩
  · have hbQ : (b : ℚ)≠0 := by exact_mod_cast hb
    have he : ((b.natAbs^2 : ℕ) : ℚ)=(b : ℚ)^2 := by
      rw [Nat.cast_pow,← Int.cast_natCast,Int.natCast_natAbs]
      simp only [Int.cast_abs, sq_abs]
    rw [Int.cast_mul,he]
    field_simp
  · simpa only [Int.natAbs_mul] using Nat.mul_le_mul ha hB

/-- Actual active stored words share a proved positive denominator; this is
not an input invariant supplied by an oracle. -/
theorem working_representation {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (height : ℕ) (hC : ∀ j v,|C j v|≤(height : ℤ))
    (i : Fin (run C ids).selected.length) (v : Fin n) :
    Representation (workingMatrix C ids i v) (stateDenominator C ids)
      ((minorBound (run C ids).selected.length height)^2) := by
  rw [working_integer_ratio]
  simpa only [stateDenominator,pow_two] using ratio_representation
    (pivotNumerator C ids i v) (pivotDenominator C ids) (pivotDenominator_ne_zero C ids)
    (minorBound (run C ids).selected.length height) (minorBound (run C ids).selected.length height)
    (pivotNumerator_bound C ids height hC i v) (pivotDenominator_bound C ids height hC)

/-- The representation includes inactive physical slots, which are literal zero. -/
theorem state_representation {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (height : ℕ) (hC : ∀ j v,|C j v|≤(height : ℤ)) (c v : Fin n) :
    Representation ((run C ids).rows c v) (stateDenominator C ids)
      ((minorBound (run C ids).selected.length height)^2) := by
  by_cases hc : (run C ids).active c=true
  · let i := (pivotEquiv C ids).symm ⟨c,hc⟩
    have he : workingMatrix C ids i v=(run C ids).rows c v :=
      congrArg (fun z : Active (run C ids) => (run C ids).rows z.val v)
        ((pivotEquiv C ids).apply_symm_apply ⟨c,hc⟩)
    rw [← he]
    exact working_representation C ids height hC i v
  · rw [(run_good C ids).inactive c (Bool.eq_false_iff.mpr hc)]
    exact ⟨0,by simp,by simp⟩

/-- The positive denominator too has a quadratic-bit envelope. -/
theorem stateDenominator_bound {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v|≤(2^bits : ℕ)) :
    stateDenominator C ids≤2^(2*(n*(n+bits))) := by
  have hd := pivotDenominator_bound C ids (2^bits) hC
  have hm := minorBound_le_two_pow (run C ids).selected.length (2^bits) bits le_rfl
  have hr := prefix_rank_le_columns C ids
  have hb : (pivotDenominator C ids).natAbs≤2^(n*(n+bits)) := by
    apply (hd.trans hm).trans
    gcongr
  unfold stateDenominator
  simpa only [← Nat.pow_mul,Nat.mul_comm] using Nat.pow_le_pow_left hb 2

/-- Cached reads execute a real list scan, including the default case. -/
structure ReadRun (A : Type) where
  /-- Returned stored data. -/
  value : A
  /-- Actual list-cell/control visits. -/
  clock : ℕ

/-- Literal finite-list read, not a functional lookup oracle. -/
def readAt {A : Type} (fallback : A) : List A → ℕ → ReadRun A
  | [],_ => ⟨fallback,1⟩
  | a::_,0 => ⟨a,2⟩
  | _::as,k+1 => let rest := readAt fallback as k; ⟨rest.value,rest.clock+2⟩

/-- Exact defaulting list semantics for every index. -/
theorem readAt_value {A : Type} (fallback : A) (as : List A) (k : ℕ) :
    (readAt fallback as k).value=as.getD k fallback := by
  induction as generalizing k with
  | nil => simp [readAt]
  | cons a as ih => cases k <;> simp [readAt,ih,List.getD]

/-- Every actual read pays at most twice the whole list length plus one. -/
theorem readAt_clock {A : Type} (fallback : A) (as : List A) (k : ℕ) :
    (readAt fallback as k).clock≤2*as.length+1 := by
  induction as generalizing k with
  | nil => simp [readAt]
  | cons a as ih => cases k <;> simp only [readAt,List.length_cons] <;> grind

/-- A finite indexed payload, when already acquired as a list, reads correctly. -/
theorem readAt_ofFn {A : Type} {n : ℕ} (fallback : A) (f : Fin n → A) (i : Fin n) :
    (readAt fallback (List.ofFn f) i.val).value=f i := by
  rw [readAt_value,List.getD_eq_getElem _ _ (by simp [i.isLt]),List.getElem_ofFn]

/-- Cached rational-word read through actual list cells. -/
def readWord (row : List RationalWord) (i : ℕ) : ReadRun RationalWord := readAt zeroWord row i

/-- Read a matrix coefficient through both actual nested lists. -/
def readCell (rows : List (List RationalWord)) (i j : ℕ) : ReadRun RationalWord :=
  let row := readAt [] rows i
  let cell := readWord row.value j
  ⟨cell.value,row.clock+cell.clock+2⟩

/-- Canonical original matrix coordinates are obtained by the executed reads. -/
theorem readCell_ofFn {m n : ℕ} (f : Fin m → Fin n → RationalWord) (i : Fin m) (j : Fin n) :
    (readCell (List.ofFn (fun i => List.ofFn (f i))) i.val j.val).value=f i j := by
  simp only [readCell,readWord,readAt_ofFn]

/-- Every cached-state entry has a uniform derived positive common-denominator
representation at a quadratic exponent in original coefficient bits. -/
theorem state_representation_binary {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v|≤(2^bits : ℕ)) (c v : Fin n) :
    Representation ((run C ids).rows c v) (stateDenominator C ids) (2^(2*(n*(n+bits)))) := by
  have hs := state_representation C ids (2^bits) hC c v
  apply representation_mono hs
  have hb := minorBound_le_two_pow (run C ids).selected.length (2^bits) bits le_rfl
  have hr := prefix_rank_le_columns C ids
  have hp : minorBound (run C ids).selected.length (2^bits)≤2^(n*(n+bits)) := by
    apply hb.trans
    gcongr
  simpa only [← Nat.pow_mul,Nat.mul_comm] using Nat.pow_le_pow_left hp 2

/-- The proved selector width has enough slack for all n-term dot prefixes. -/
theorem selectorWidth_dot_margin (n bits : ℕ) :
    n+bits+2*(n*(n+bits))<selectorWidth n bits := by
  have hp : n≤n*(n+bits) := by
    by_cases hn : n=0
    · simp [hn]
    · have hnpos : 1≤n := by omega
      nlinarith
  have hr : 3*(leafBits n bits+1)≤residualBits n bits := by
    unfold residualBits
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (leafBits n bits+1) (show 3≤4*n+3 by omega)
  unfold leafBits at hr
  unfold selectorWidth
  omega

/-- Every element returned by the actual list scanner satisfies a preserved
payload predicate, including the default case. -/
theorem readAt_property {A : Type} (fallback : A) (xs : List A) (k : ℕ)
    (P : A → Prop) (hz : P fallback) (hx : ∀ x∈xs,P x) :
    P (readAt fallback xs k).value := by
  induction xs generalizing k with
  | nil => exact hz
  | cons x xs ih =>
    cases k with
    | zero => exact hx x (by simp)
    | succ k => exact ih k (fun a ha => hx a (by simp [ha]))

/-- Two actual list scans have a polynomial cell/control budget under the
literal matrix shape, with no constant-time matrix-lookup premise. -/
theorem readCell_clock (rows : List (List RationalWord)) (n i j : ℕ)
    (hs : rows.length≤n) (hr : ∀ row∈rows,row.length≤n) :
    (readCell rows i j).clock≤4*n+4 := by
  have h1 := readAt_clock ([] : List RationalWord) rows i
  have hl := readAt_property ([] : List RationalWord) rows i (fun row => row.length≤n)
    (by simp) hr
  have h2 := readAt_clock zeroWord (readAt [] rows i).value j
  simp only [readCell,readWord]
  omega

/-- Actual acquired vector of pairs for one ALL-column dot product. Inactive
working slots are zero by the old run invariant, so no branch is needed here. -/
def acquirePairs (n : ℕ) (row : List RationalWord) (rows : List (List RationalWord)) (v : ℕ) :
    ReadRun (List (RationalWord × RationalWord)) :=
  let reports := List.ofFn (fun c : Fin n =>
    let a := readWord row c.val
    let b := readCell rows c.val v
    ((a.value,b.value),a.clock+b.clock+1))
  ⟨reports.map Prod.fst,(reports.map Prod.snd).sum+10*n+5⟩

/-- The materialized pair payload is exactly its actual read results. -/
theorem acquirePairs_value (n : ℕ) (row : List RationalWord) (rows : List (List RationalWord)) (v : ℕ) :
    (acquirePairs n row rows v).value=List.ofFn (fun c : Fin n =>
      ((readWord row c.val).value,(readCell rows c.val v).value)) := by
  simp only [acquirePairs,List.map_ofFn,Function.comp_def]

/-- Explicit pair acquisition includes every original-row and matrix read. -/
theorem acquirePairs_clock (n : ℕ) (row : List RationalWord) (rows : List (List RationalWord)) (v : ℕ)
    (hrow : row.length≤n) (hrows : rows.length≤n) (hcell : ∀ r∈rows,r.length≤n) :
    (acquirePairs n row rows v).clock≤n*(6*n+6)+10*n+5 := by
  have hc (c : Fin n) : (readWord row c.val).clock+(readCell rows c.val v).clock+1≤6*n+6 := by
    have ha := readAt_clock zeroWord row c.val
    have hb := readCell_clock rows n c.val v hrows hcell
    unfold readWord
    omega
  have hs := Finset.sum_le_sum (fun c (_ : c∈(Finset.univ : Finset (Fin n))) => hc c)
  simp only [acquirePairs,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  simpa using Nat.add_le_add_right (Nat.add_le_add_right hs (10*n)) 5

/-- A scalar residual really runs physical dot arithmetic, negation and
addition; the output report retains all acquired data and instruction clocks. -/
def residualWord (n : ℕ) (template : List Bool) (row : List RationalWord)
    (rows : List (List RationalWord)) (v : ℕ) : RationalReport :=
  let pairs := acquirePairs n row rows v
  let dot := SemiprimeDotBits.dotBits template pairs.value
  let input := readWord row v
  let neg := executeOperation .neg dot.word zeroWord template
  let out := executeOperation .add input.value neg.word template
  ⟨out.word,pairs.clock+dot.clock+input.clock+neg.clock+out.clock+4⟩

/-- ALL-column dot products equal the exact old active-column elimination. -/
theorem all_dot_residual {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m)) (j : Fin m) (v : Fin n) :
    originalRow C j v-∑ c : Fin n,originalRow C j c*(run C ids).rows c v=
      SemiprimeRowSelectionExecution.residual (run C ids) (originalRow C j) v := by
  rw [SemiprimeRowSelectionExecution.residual,cacheRow_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : (run C ids).active c=true
  · simp [hc]
  · rw [(run_good C ids).inactive c (Bool.eq_false_iff.mpr hc)]
    simp [hc]

/-- Whole residual-coordinate budget, retained from real reads and bit calls. -/
def residualBudget (n W : ℕ) : ℕ :=
  (n*(6*n+6)+10*n+5)+(n*(40000*(W+1)^3+4)+4)+(2*n+1)+40000*(W+1)^3+4

/-- The physical residual's fits and shared denominators are derived from the
ACTUAL old integer run; no caller supplies a state/minor/fit answer. -/
theorem residualWord_correct {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v|≤(2^bits : ℕ)) (j : Fin m) (v : Fin n)
    (template : List Bool) (ht : template.length=selectorWidth n bits)
    (row : List RationalWord) (rows : List (List RationalWord))
    (hrow : ∀ c : Fin n,(readWord row c.val).value.Valid ∧
      Width (readWord row c.val).value template.length ∧
      (readWord row c.val).value.value=originalRow C j c)
    (hrows : ∀ c : Fin n,(readCell rows c.val v.val).value.Valid ∧
      Width (readCell rows c.val v.val).value template.length ∧
      (readCell rows c.val v.val).value.value=(run C ids).rows c v) :
    (residualWord n template row rows v.val).word.value=
      SemiprimeRowSelectionExecution.residual (run C ids) (originalRow C j) v ∧
    (residualWord n template row rows v.val).word.Valid ∧
    Width (residualWord n template row rows v.val).word template.length := by
  let pairs := (acquirePairs n row rows v.val).value
  let D := stateDenominator C ids
  let E := 2^(2*(n*(n+bits)))
  have hd : 0<D := stateDenominator_pos C ids
  have hlen : pairs.length=n := by simp [pairs,acquirePairs_value]
  have hmargin := selectorWidth_dot_margin n bits
  have hden : 1*D<2^template.length := by
    rw [Nat.one_mul]
    apply (stateDenominator_bound C ids bits hC).trans_lt
    rw [ht]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hnum : pairs.length*2^bits*E<2^template.length := by
    rw [hlen,ht]
    have hn : n≤2^n := (Nat.lt_two_pow_self (n := n)).le
    have hm := Nat.mul_le_mul_right E (Nat.mul_le_mul_right (2^bits) hn)
    have he : 2^n*2^bits*E=2^(n+bits+2*(n*(n+bits))) := by
      dsimp [E]
      rw [← Nat.pow_add,← Nat.pow_add]
    apply (hm.trans_eq he).trans_lt
    exact Nat.pow_lt_pow_right (by decide) hmargin
  have hp : ∀ pair∈pairs,pair.1.Valid ∧ pair.2.Valid ∧
      Representation pair.1.value 1 (2^bits) ∧ Representation pair.2.value D E := by
    intro pair hm
    rw [show pairs=List.ofFn (fun c : Fin n =>
      ((readWord row c.val).value,(readCell rows c.val v.val).value)) from acquirePairs_value _ _ _ _] at hm
    obtain ⟨c,rfl⟩ := List.mem_ofFn.mp hm
    refine ⟨(hrow c).1,(hrows c).1,?_,?_⟩
    · rw [(hrow c).2.2]
      exact ⟨C j c,by simp [originalRow],by exact_mod_cast (show ((C j c).natAbs : ℤ)≤(2^bits : ℕ) by
        simpa only [Int.natCast_natAbs] using hC j c)⟩
    · rw [(hrows c).2.2]
      exact state_representation_binary C ids bits hC c v
  have hdot := SemiprimeDotBits.dotBits_correct template pairs 1 D (2^bits) E
    (by decide) hd hden hnum hp
  have hdotValue : SemiprimeDotBits.dotValue pairs=
      ∑ c : Fin n,originalRow C j c*(run C ids).rows c v := by
    simp only [SemiprimeDotBits.dotValue,pairs,acquirePairs_value,List.map_ofFn,List.sum_ofFn,Function.comp_def]
    apply Finset.sum_congr rfl
    intro c _
    rw [(hrow c).2.2,(hrows c).2.2]
  have hdotFits : Fits (SemiprimeDotBits.dotBits template pairs).word.value template.length :=
    fits_of_representation (Nat.mul_pos (by decide) hd) hdot.2.2 hnum hden
  have hz : zeroWord.Valid := by change 0<1; decide
  have hnf : Fits (-(SemiprimeDotBits.dotBits template pairs).word.value) template.length := by
    simpa only [Fits,Rat.neg_num,Int.natAbs_neg,Rat.neg_den] using hdotFits
  have hneg := executeOperation_correct .neg (SemiprimeDotBits.dotBits template pairs).word zeroWord template
    hdot.2.1 hz hnf
  have hvalue : (readWord row v.val).value.value+
      (executeOperation .neg (SemiprimeDotBits.dotBits template pairs).word zeroWord template).word.value=
      SemiprimeRowSelectionExecution.residual (run C ids) (originalRow C j) v := by
    rw [hneg.1,(hrow v).2.2,hdot.1,hdotValue]
    simpa only [Operation.value,sub_eq_add_neg] using all_dot_residual C ids j v
  have hof : Fits ((readWord row v.val).value.value+
      (executeOperation .neg (SemiprimeDotBits.dotBits template pairs).word zeroWord template).word.value)
      template.length := by
    rw [hvalue,ht]
    have h := residual_trace_fits C ids bits hC j v _ (Expr.eval_mem_trace _)
    rwa [residualExpr_value,SemiprimeRowSelectionTracked.residualRun_value] at h
  have hout := executeOperation_correct .add (readWord row v.val).value
    (executeOperation .neg (SemiprimeDotBits.dotBits template pairs).word zeroWord template).word template
    (hrow v).1 hneg.2.1 hof
  exact ⟨hout.1.trans hvalue,hout.2.1,hout.2.2⟩

/-- Physical fitting returns bounded output width even before its semantic fit
proof; this supports the unconditional instruction-cost calculation. -/
theorem operation_width (op : Operation) (a b : RationalWord) (template : List Bool) :
    Width (executeOperation op a b template).word template.length := by
  have h := fitRationalBits_width (rawOperation op a b).word template
  exact ⟨h.1.le,h.2.le⟩

/-- The physical residual report includes its real pair reads, suffix loop,
integer arithmetic, reductions, copies and final subtraction instructions. -/
theorem residualWord_clock (n : ℕ) (template : List Bool) (row : List RationalWord)
    (rows : List (List RationalWord)) (v : Fin n) (ht : 0<template.length)
    (hrow : row.length≤n) (hrows : rows.length≤n) (hcell : ∀ r∈rows,r.length≤n)
    (haw : ∀ c : Fin n,Width (readWord row c.val).value template.length)
    (hbw : ∀ c : Fin n,Width (readCell rows c.val v.val).value template.length) :
    (residualWord n template row rows v.val).clock≤residualBudget n template.length := by
  let pairs := (acquirePairs n row rows v.val).value
  have hp : ∀ pair∈pairs,Width pair.1 template.length ∧ Width pair.2 template.length := by
    intro pair hm
    rw [show pairs=List.ofFn (fun c : Fin n =>
      ((readWord row c.val).value,(readCell rows c.val v.val).value)) from acquirePairs_value _ _ _ _] at hm
    obtain ⟨c,rfl⟩ := List.mem_ofFn.mp hm
    exact ⟨haw c,hbw c⟩
  have hlen : pairs.length=n := by simp [pairs,acquirePairs_value]
  have hpair := acquirePairs_clock n row rows v.val hrow hrows hcell
  have hdot := SemiprimeDotBits.dotBits_cost template ht pairs hp
  rw [hlen] at hdot
  have hdotW := SemiprimeDotBits.dotBits_width template ht pairs
  have hz : Width zeroWord template.length := by
    change 0≤template.length ∧ 1≤template.length
    exact ⟨Nat.zero_le _,ht⟩
  have hneg := executeOperation_cost .neg (SemiprimeDotBits.dotBits template pairs).word zeroWord template
    hdotW hz le_rfl
  have hnW := operation_width .neg (SemiprimeDotBits.dotBits template pairs).word zeroWord template
  have hout := executeOperation_cost .add (readWord row v.val).value
    (executeOperation .neg (SemiprimeDotBits.dotBits template pairs).word zeroWord template).word template
    (haw v) hnW le_rfl
  have hread := readAt_clock zeroWord row v.val
  unfold residualWord residualBudget
  dsimp only
  change (acquirePairs n row rows v.val).clock+(SemiprimeDotBits.dotBits template pairs).clock+
    (readWord row v.val).clock+
    (executeOperation .neg (SemiprimeDotBits.dotBits template pairs).word zeroWord template).clock+
    (executeOperation .add (readWord row v.val).value
      (executeOperation .neg (SemiprimeDotBits.dotBits template pairs).word zeroWord template).word template).clock+4≤_
  have hr : (readWord row v.val).clock≤2*n+1 := hread.trans (by omega)
  omega

/-- Actual physical back elimination, using multiplication then sign change
then addition. Every instruction clock is retained in the returned report. -/
def backWords (old coefficient normalized : RationalWord) (template : List Bool) : RationalReport :=
  let product := executeOperation .mul coefficient normalized template
  let negative := executeOperation .neg product.word zeroWord template
  let result := executeOperation .add old negative.word template
  ⟨result.word,product.clock+negative.clock+result.clock+3⟩

/-- The three real instructions have a fixed cubic physical-width budget. -/
theorem backWords_clock (old coefficient normalized : RationalWord) (template : List Bool)
    (ht : 0<template.length)
    (ho : Width old template.length) (hc : Width coefficient template.length)
    (hn : Width normalized template.length) :
    (backWords old coefficient normalized template).clock≤60003*(template.length+1)^3 := by
  have hz : Width zeroWord template.length := by
    change 0≤template.length ∧ 1≤template.length
    exact ⟨Nat.zero_le _,ht⟩
  have hm := executeOperation_cost .mul coefficient normalized template hc hn le_rfl
  have hmW := operation_width .mul coefficient normalized template
  have hneg := executeOperation_cost .neg (executeOperation .mul coefficient normalized template).word
    zeroWord template hmW hz le_rfl
  have hnegW := operation_width .neg (executeOperation .mul coefficient normalized template).word zeroWord template
  have ha := executeOperation_cost .add old (executeOperation .neg
    (executeOperation .mul coefficient normalized template).word zeroWord template).word template ho hnegW le_rfl
  have hp : 1≤(template.length+1)^3 := Nat.one_le_pow _ _ (by omega)
  unfold backWords
  dsimp only
  omega

/-- For an actual active nonpivot slot, physical back elimination refines the
old update with every product/result fit DERIVED from the actual integer run. -/
theorem backWords_correct {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (bits : ℕ) (hC : ∀ j v,|C j v|≤(2^bits : ℕ)) (j : Fin m) (p c v : Fin n)
    (hcp : c≠p) (hc : (run C ids).active c=true)
    (old coefficient normalized : RationalWord) (template : List Bool)
    (ht : template.length=selectorWidth n bits)
    (ho : old.Valid) (hcoeff : coefficient.Valid) (hn : normalized.Valid)
    (hov : old.value=(run C ids).rows c v)
    (hcv : coefficient.value=(run C ids).rows c p)
    (hnv : normalized.value=(SemiprimeRowSelectionTracked.normalizeRun
      (SemiprimeRowSelectionTracked.residualRun (run C ids) (originalRow C j)).row p).row v) :
    (backWords old coefficient normalized template).word.value=
      (run C ids).rows c v-(run C ids).rows c p*
        (SemiprimeRowSelectionTracked.normalizeRun
          (SemiprimeRowSelectionTracked.residualRun (run C ids) (originalRow C j)).row p).row v ∧
    (backWords old coefficient normalized template).word.Valid ∧
    Width (backWords old coefficient normalized template).word template.length := by
  let q := (SemiprimeRowSelectionTracked.normalizeRun
    (SemiprimeRowSelectionTracked.residualRun (run C ids) (originalRow C j)).row p).row v
  have hprodB : Bounded ((run C ids).rows c p*q) (2^updateBits n bits) := by
    apply update_trace_bounds C ids bits hC j p c v
    simp [updateExpr,hcp,hc,Expr.trace,Expr.eval,q]
  have hprodF : Fits (coefficient.value*normalized.value) template.length := by
    rw [hcv,hnv,ht]
    exact bounded_fits hprodB (by unfold selectorWidth; omega)
  have hm := executeOperation_correct .mul coefficient normalized template hcoeff hn hprodF
  simp only [Operation.value] at hm
  have hz : zeroWord.Valid := by change 0<1; decide
  have hnF : Fits (-(executeOperation .mul coefficient normalized template).word.value) template.length := by
    rw [hm.1]
    simpa only [Fits,Rat.neg_num,Int.natAbs_neg,Rat.neg_den] using hprodF
  have hneg := executeOperation_correct .neg (executeOperation .mul coefficient normalized template).word
    zeroWord template hm.2.1 hz hnF
  simp only [Operation.value] at hneg
  have hsubB : Bounded ((run C ids).rows c v-(run C ids).rows c p*q) (2^updateBits n bits) := by
    apply update_trace_bounds C ids bits hC j p c v
    simp [updateExpr,hcp,hc,Expr.trace,Expr.eval,q]
  have hsF : Fits (old.value+(executeOperation .neg
      (executeOperation .mul coefficient normalized template).word zeroWord template).word.value) template.length := by
    rw [hneg.1,hm.1,hov,hcv,hnv,ht]
    simpa only [sub_eq_add_neg,q] using
      bounded_fits hsubB (show updateBits n bits<selectorWidth n bits by unfold selectorWidth; omega)
  have ha := executeOperation_correct .add old (executeOperation .neg
    (executeOperation .mul coefficient normalized template).word zeroWord template).word template ho hneg.2.1 hsF
  refine ⟨?_,ha.2.1,ha.2.2⟩
  simpa only [backWords,Operation.value,hneg.1,hm.1,hov,hcv,hnv,sub_eq_add_neg] using ha.1

/-- The existing actual two-instruction normalization has a physical-width
clock bound independent of any unit-cost rational abstraction. -/
theorem normalizeWords_clock (a b : RationalWord) (template : List Bool)
    (ht : 0<template.length) (ha : Width a template.length) (hb : Width b template.length) :
    (normalizeWords a b template).clock≤40002*(template.length+1)^3 := by
  have hz : Width zeroWord template.length := by
    change 0≤template.length ∧ 1≤template.length
    exact ⟨Nat.zero_le _,ht⟩
  have hi := executeOperation_cost .inv b zeroWord template hb hz le_rfl
  have hiW := operation_width .inv b zeroWord template
  have hm := executeOperation_cost .mul a (executeOperation .inv b zeroWord template).word template ha hiW le_rfl
  have hp : 1≤(template.length+1)^3 := Nat.one_le_pow _ _ (by omega)
  unfold normalizeWords
  dsimp only
  omega

end RiemannGaussian.SemiprimeRowSelectionBitArithmetic
