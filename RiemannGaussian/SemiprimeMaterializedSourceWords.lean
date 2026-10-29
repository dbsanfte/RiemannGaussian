/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedScoreSearch
import RiemannGaussian.SemiprimeMaterializedSourceUniversal

/-!
# Acquisition of original source score programs and computed labels

Every numeric support code is found by an explicit original-index list scan.
The collision scores are computed by the finite cached-environment interpreter,
not supplied as terminal answers. Full word/address bit simulation is separate
from this exact scalar/list-control execution.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeMaterializedSourceWords
open OAI.Algorithms.SubexponentialSAT
open LocalExpectation MulticolorTypes SqrtLog
open SemiprimeMaterializedWords SemiprimeMaterializedScoreEnvironment

/-- Literal first-position scan, including the absent-index length convention. -/
def indexRun {A : Type*} [DecidableEq A] (a : A) : List A → Run ℕ
  | [] => ⟨0,1⟩
  | b::bs => if a=b then ⟨0,2⟩ else
    let rest := indexRun a bs
    ⟨rest.value+1,rest.work+2⟩

/-- The actual scan computes the source indexCode even on absent values. -/
theorem indexRun_value {A : Type*} [DecidableEq A] (a : A) (xs : List A) :
    (indexRun a xs).value=indexCode xs a := by
  induction xs with
  | nil => simp [indexRun,indexCode]
  | cons b bs ih =>
    by_cases h : a=b
    · simp [indexRun,indexCode,h]
    · simp [indexRun,indexCode,h,Ne.symm h,ih]

/-- Each comparison/read and recursive list step is explicitly counted. -/
theorem indexRun_work {A : Type*} [DecidableEq A] (a : A) (xs : List A) :
    (indexRun a xs).work≤2*xs.length+2 := by
  induction xs with
  | nil => simp [indexRun]
  | cons b bs ih => by_cases h : a=b <;> simp only [indexRun,h,ite_true,ite_false,List.length_cons] <;> omega

variable {I V E : Type*} [DecidableEq V] [DecidableEq E] {r Q : ℕ}

/-- Mathematical descriptor of the original term, used only for specification. -/
def descriptor (owner : I → V) (factor : I → E) (indices : List (V ⊕ E)) :
    Packing.ScoreTerm I V Q → ScoreProgram Q
  | .inl (i,j) => .incidence (indexCode indices (.inl (owner i)))
      (indexCode indices (.inr (factor i))) (indexCode indices (.inl (owner j)))
      (indexCode indices (.inr (factor j)))
  | .inr (t,v,w) => .head t (indexCode indices (.inl v)) (indexCode indices (.inl w))

/-- Acquire the actual numeric terminal and support descriptor; all code searches execute. -/
def compile (owner : I → V) (factor : I → E) (indices : List (V ⊕ E)) :
    Packing.ScoreTerm I V Q → Run (ScoreProgram Q)
  | .inl (i,j) =>
    let a := indexRun (.inl (owner i)) indices
    let b := indexRun (.inr (factor i)) indices
    let c := indexRun (.inl (owner j)) indices
    let d := indexRun (.inr (factor j)) indices
    ⟨.incidence a.value b.value c.value d.value,a.work+b.work+c.work+d.work+5⟩
  | .inr (t,v,w) =>
    let a := indexRun (.inl v) indices
    let b := indexRun (.inl w) indices
    ⟨.head t a.value b.value,a.work+b.work+3⟩

/-- No numeric support-code answer is an input to the compiler. -/
theorem compile_value (owner : I → V) (factor : I → E) (indices : List (V ⊕ E))
    (z : Packing.ScoreTerm I V Q) :
    (compile owner factor indices z).value=descriptor owner factor indices z := by
  cases z <;> simp only [compile,descriptor,indexRun_value]

/-- At most four original-index scans per acquired instruction. -/
theorem compile_work (owner : I → V) (factor : I → E) (indices : List (V ⊕ E))
    (z : Packing.ScoreTerm I V Q) :
    (compile owner factor indices z).work≤8*indices.length+13 := by
  have hr := fun a => indexRun_work a indices
  cases z with
  | inl p =>
    rcases p with ⟨i,j⟩
    simp only [compile]
    nlinarith [hr (.inl (owner i)),hr (.inr (factor i)),hr (.inl (owner j)),hr (.inr (factor j))]
  | inr p =>
    rcases p with ⟨t,v,w⟩
    simp only [compile]
    nlinarith [hr (.inl v),hr (.inl w)]

/-- Compiled code lists are exactly the original numbered score supports. -/
theorem descriptor_support (owner : I → V) (factor : I → E) (indices : List (V ⊕ E))
    (z : Packing.ScoreTerm I V Q) :
    (support (descriptor owner factor indices z)).toFinset=
      Packing.numberedScoreSupport owner factor indices z := by
  cases z <;> ext i <;> simp [support,descriptor,Packing.numberedScoreSupport,Packing.scoreSupport]

/-- Equality of the two actual incidence words is precisely the original universal-type collision. -/
theorem pair_type_eq {r Q : ℕ} (a b c d : Word r Q) :
    (⟨a,fun _ : Fin 1 => b⟩ : UniversalType r Q 1)=⟨c,fun _ => d⟩ ↔ a=c ∧ b=d := by
  constructor
  · intro h
    exact ⟨congrArg UniversalType.head h,congrArg (fun u : UniversalType r Q 1 => u.slot 0) h⟩
  · rintro ⟨rfl,rfl⟩
    rfl

/-- Compiled collision/head instructions preserve the ORIGINAL score formula. -/
theorem descriptor_value
    (owner : I → V) (factor : I → E) (indices : List (V ⊕ E)) (x y : ℚ)
    (z : Packing.ScoreTerm I V Q) (omega : ℕ → Word r Q) :
    programValue x y (descriptor owner factor indices z) omega=
      Packing.numberedScoreTerm owner factor indices x y z omega := by
  cases z <;> simp only [descriptor,programValue,Packing.numberedScoreTerm,reindexTerm,
    Packing.scoreTerm,Packing.incidenceType,pair_type_eq]

/-- Materialize all instruction reports once before search. -/
def compileAll (owner : I → V) (factor : I → E) (indices : List (V ⊕ E))
    (terms : List (Packing.ScoreTerm I V Q)) : Run (List (ScoreProgram Q)) :=
  let reports := terms.map (compile owner factor indices)
  ⟨reports.map (fun p => p.value),(reports.map (fun p => p.work)).sum+2*terms.length+1⟩

/-- The stored instruction list has the original source order. -/
theorem compileAll_value (owner : I → V) (factor : I → E) (indices : List (V ⊕ E))
    (terms : List (Packing.ScoreTerm I V Q)) :
    (compileAll owner factor indices terms).value=terms.map (descriptor owner factor indices) := by
  simp only [compileAll,List.map_map,Function.comp_def,compile_value]

/-- All descriptor acquisition is polynomial in original list dimensions. -/
theorem compileAll_work (owner : I → V) (factor : I → E) (indices : List (V ⊕ E))
    (terms : List (Packing.ScoreTerm I V Q)) :
    (compileAll owner factor indices terms).work≤terms.length*(8*indices.length+15)+1 := by
  have hs : ((terms.map (compile owner factor indices)).map (fun p => p.work)).sum≤
      terms.length*(8*indices.length+13) := by
    induction terms with
    | nil => simp
    | cons z zs ih =>
      have hz := compile_work owner factor indices z
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  simp only [compileAll]
  nlinarith

/-- Mapping the compiled programs changes neither local averaging nor the source evaluator. -/
theorem compiled_sequential
    (owner : I → V) (factor : I → E) (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I V Q)) (indices : List (V ⊕ E)) (x y offset : ℚ)
    (n : ℕ) (fixed : List (Word r Q)) :
    (SemiprimeMaterializedScoreSearch.sequential a tail (terms.map (descriptor owner factor indices))
      x y offset n fixed).value =
      sequentialEvaluator (a::tail) terms (Packing.numberedScoreSupport owner factor indices)
        (Packing.numberedScoreTerm owner factor indices x y) offset a n fixed := by
  rw [SemiprimeMaterializedScoreSearch.sequential_value]
  have hf (z : Packing.ScoreTerm I V Q) : programValue (r := r) x y (descriptor owner factor indices z)=
      Packing.numberedScoreTerm (r := r) owner factor indices x y z := by
    funext omega
    exact descriptor_value owner factor indices x y z omega
  simp only [sequentialEvaluator,localEvaluator,List.map_map,Function.comp_def,
    descriptor_support,hf]

/-- Complete acquired search with no terminal producer or support-code oracle. -/
def computedList (owner : I → V) (factor : I → E)
    (a : Word r Q) (tail : List (Word r Q)) (terms : List (Packing.ScoreTerm I V Q))
    (indices : List (V ⊕ E)) (x y offset : ℚ) : Run (List (Word r Q)) :=
  let compiled := compileAll owner factor indices terms
  let result := SemiprimeMaterializedScoreSearch.search a tail compiled.value x y offset indices.length
  ⟨result.value,compiled.work+result.work+1⟩

/-- EXACT source choices, not a supplied optimum or a merely comparable score. -/
theorem computedList_value
    (owner : I → V) (factor : I → E)
    (a : Word r Q) (tail : List (Word r Q)) (terms : List (Packing.ScoreTerm I V Q))
    (indices : List (V ⊕ E)) (x y offset : ℚ) :
    (computedList owner factor a tail terms indices x y offset).value=
      localAssign a tail terms (Packing.numberedScoreSupport owner factor indices)
        (Packing.numberedScoreTerm owner factor indices x y) offset a indices.length := by
  simp only [computedList,compileAll_value,SemiprimeMaterializedScoreSearch.search,assign_value,localAssign]
  congr 1
  funext n fixed
  exact compiled_sequential owner factor a tail terms indices x y offset n fixed

/-- Polynomial scalar/control work in alphabet and original-network list sizes. -/
theorem computedList_work (owner : I → V) (factor : I → E)
    (a : Word r Q) (tail : List (Word r Q)) (terms : List (Packing.ScoreTerm I V Q))
    (indices : List (V ⊕ E)) (x y offset : ℚ) :
    (computedList owner factor a tail terms indices x y offset).work≤
      terms.length*(8*indices.length+15)+1+
      (indices.length*(tail.length*(2*SemiprimeMaterializedScoreSearch.evaluatorBudget
        (a::tail).length terms.length indices.length Q+3)+4)+1)+1 := by
  have hc := compileAll_work owner factor indices terms
  have hs := SemiprimeMaterializedScoreSearch.search_work a tail
    (compileAll owner factor indices terms).value x y offset indices.length
  have hl : (compileAll owner factor indices terms).value.length=terms.length := by
    rw [compileAll_value,List.length_map]
  rw [hl] at hs
  exact Nat.add_le_add_right (Nat.add_le_add hc hs) 1

/-- Exact output length of the actually computed reverse-prefix label list. -/
theorem computedList_length (owner : I → V) (factor : I → E)
    (a : Word r Q) (tail : List (Word r Q)) (terms : List (Packing.ScoreTerm I V Q))
    (indices : List (V ⊕ E)) (x y offset : ℚ) :
    (computedList owner factor a tail terms indices x y offset).value.length=indices.length := by
  simp only [computedList,SemiprimeMaterializedScoreSearch.search,
    SemiprimeMaterializedWordSearch.assign_length,List.length_nil,Nat.add_zero]

/-- Explicit scalar power loop for the original universal-alphabet denominator. -/
def powNatRun (base : ℕ) : ℕ → Run ℕ
  | 0 => ⟨1,1⟩
  | k+1 => let old := powNatRun base k; ⟨old.value*base,old.work+2⟩

/-- This loop obtains the literal integer power, without enumerating its alphabet. -/
theorem powNatRun_value (base k : ℕ) : (powNatRun base k).value=base^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [powNatRun,ih,pow_succ]

/-- Every multiplication and loop step of denominator construction is counted. -/
theorem powNatRun_work (base k : ℕ) : (powNatRun base k).work=2*k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [powNatRun,ih]; omega

/-- Original score offset from input dimensions, with explicit power construction. -/
def offsetRun (M n r Q : ℕ) (x y : ℚ) : Run ℚ :=
  let den := powNatRun r (2*Q)
  ⟨y*y*(M : ℚ)*(M : ℚ)/(den.value : ℚ)+x*x*(Q : ℚ)*(n : ℚ)*(n : ℚ)/(r : ℚ),den.work+25⟩

omit [DecidableEq V] in
/-- The dimension-based finite construction is exactly the published offset. -/
theorem offsetRun_value [Fintype I] [Fintype V] (x y : ℚ) :
    (offsetRun (Fintype.card I) (Fintype.card V) r Q x y).value=
      Packing.scoreOffset (I := I) (V := V) (r := r) (Q := Q) x y := by
  simp only [offsetRun,powNatRun_value,Packing.scoreOffset,card_universalType,pow_two]
  norm_num only [show Q*(1+1)=2*Q by omega]
  ring

/-- Actual offset power and fixed rational scalar arithmetic are retained. -/
theorem offsetRun_work (M n r Q : ℕ) (x y : ℚ) :
    (offsetRun M n r Q x y).work=4*Q+26 := by
  simp only [offsetRun,powNatRun_work]
  omega

/-- One actual incidence label from an already acquired label list. Both original
code searches and BOTH reverse-prefix word reads execute and are paid. -/
def labelAt (owner : I → V) (factor : I → E) (a : Word r Q)
    (indices : List (V ⊕ E)) (labels : List (Word r Q)) (i : I) :
    SemiprimeMaterializedSourceUniversal.Run (UniversalType r Q 1) :=
  let cv := indexRun (.inl (owner i)) indices
  let ce := indexRun (.inr (factor i)) indices
  let wv := SemiprimeMaterializedWordSearch.readRun a labels cv.value
  let we := SemiprimeMaterializedWordSearch.readRun a labels ce.value
  ⟨⟨wv.value,fun _ => we.value⟩,cv.work+ce.work+wv.work+we.work+3⟩

/-- No final-label answer is supplied to the incidence-label constructor. -/
theorem labelAt_value
    (owner : I → V) (factor : I → E) (a : Word r Q)
    (indices : List (V ⊕ E)) (labels : List (Word r Q)) (i : I) :
    (labelAt owner factor a indices labels i).value=
      Packing.incidenceType owner factor
        (fun z => decode a labels (indexCode indices z)) i := by
  simp only [labelAt,indexRun_value,SemiprimeMaterializedWordSearch.readRun_value,Packing.incidenceType]

/-- Actual cached-label lookup, including nonconstant decoder and index scans. -/
theorem labelAt_work (owner : I → V) (factor : I → E) (a : Word r Q)
    (indices : List (V ⊕ E)) (labels : List (Word r Q)) (i : I) :
    (labelAt owner factor a indices labels i).work≤
      4*indices.length+6*(labels.length+1)^2+7 := by
  have hv := indexRun_work (.inl (owner i)) indices
  have he := indexRun_work (.inr (factor i)) indices
  have wv := SemiprimeMaterializedWordSearch.readRun_work a labels
    (indexRun (.inl (owner i)) indices).value
  have we := SemiprimeMaterializedWordSearch.readRun_work a labels
    (indexRun (.inr (factor i)) indices).value
  simp only [labelAt]
  omega

/-- Acquire the entire ORIGINAL score-based word search ONCE, then return an
actual paid label constructor reading that cached list. No hp/B/label oracle. -/
def producer [Fintype I] [Fintype V]
    (owner : I → V) (factor : I → E) (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I V Q)) (indices : List (V ⊕ E)) (x y : ℚ) :
    SemiprimeMaterializedSourceUniversal.Run
      (I → SemiprimeMaterializedSourceUniversal.Run (UniversalType r Q 1)) :=
  let offset := offsetRun (Fintype.card I) (Fintype.card V) r Q x y
  let labels := computedList owner factor a tail terms indices x y offset.value
  ⟨fun i => labelAt owner factor a indices labels.value i,offset.work+labels.work+1⟩

/-- The computed label producer has EXACTLY the original deterministic labels. -/
theorem producer_value [Fintype I] [Fintype V]
    (owner : I → V) (factor : I → E) (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I V Q)) (indices : List (V ⊕ E)) (x y : ℚ) (i : I) :
    ((producer owner factor a tail terms indices x y).value i).value=
      Packing.incidenceType owner factor
        (Packing.computedWords owner factor a tail terms indices x y) i := by
  simp only [producer,labelAt_value,offsetRun_value]
  have hw : (fun z => decode a
      (computedList owner factor a tail terms indices x y
        (Packing.scoreOffset (I := I) (V := V) (r := r) (Q := Q) x y)).value (indexCode indices z))=
      Packing.computedWords owner factor a tail terms indices x y := by
    rw [computedList_value]
    rfl
  exact congrArg (fun w => Packing.incidenceType owner factor w i) hw

/-- Preprocessing budget has no arbitrary terminal-cost parameter. -/
def producerBudget (A T N Q : ℕ) : ℕ :=
  (4*Q+26)+(T*(8*N+15)+1+
    (N*(A*(2*SemiprimeMaterializedScoreSearch.evaluatorBudget (A+1) T N Q+3)+4)+1)+1)+1

/-- Complete executed original-score search is polynomial in A,n,M,F,Q. -/
theorem producer_work [Fintype I] [Fintype V]
    (owner : I → V) (factor : I → E) (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I V Q)) (indices : List (V ⊕ E)) (x y : ℚ) :
    (producer owner factor a tail terms indices x y).work≤
      producerBudget tail.length terms.length indices.length Q := by
  have hc := computedList_work owner factor a tail terms indices x y
    (offsetRun (Fintype.card I) (Fintype.card V) r Q x y).value
  simp only [List.length_cons] at hc
  simp only [producer,offsetRun_work,producerBudget]
  omega

/-- After the search is cached, every incidence request has a polynomial REAL
list/index read budget, rather than a unit-cost functional assignment lookup. -/
theorem producer_label_work [Fintype I] [Fintype V]
    (owner : I → V) (factor : I → E) (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I V Q)) (indices : List (V ⊕ E)) (x y : ℚ) (i : I) :
    ((producer owner factor a tail terms indices x y).value i).work≤
      4*indices.length+6*(indices.length+1)^2+7 := by
  have h := labelAt_work owner factor a indices
    (computedList owner factor a tail terms indices x y
      (offsetRun (Fintype.card I) (Fintype.card V) r Q x y).value).value i
  rw [computedList_length] at h
  exact h

end RiemannGaussian.SemiprimeMaterializedSourceWords
