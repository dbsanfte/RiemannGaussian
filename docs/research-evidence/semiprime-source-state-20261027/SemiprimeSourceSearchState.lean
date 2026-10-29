/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedSourceWords
import RiemannGaussian.SemiprimeSourceOffsetHeight

/-! # Actual cached source-search IDs and environment storage
The proof relations below follow the literal recursive child calls. State
bounds follow from original lists, support scans and actual cached-array sizes;
no maximum-live-state or selected-value answer is an input.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeSourceSearchState
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open LocalExpectation MulticolorTypes SqrtLog Subexp.ConstructivePacking
open SemiprimeMaterializedWords SemiprimeMaterializedScoreEnvironment

/-- Even an absent value produces at most the literal list-length sentinel. -/
theorem indexRun_le {A : Type*} [DecidableEq A] (a : A) (xs : List A) :
    (SemiprimeMaterializedSourceWords.indexRun a xs).value≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons b bs ih => by_cases h : a=b <;> simp only [SemiprimeMaterializedSourceWords.indexRun,h,
      ite_true,ite_false,List.length_cons] <;> omega

/-- An original enumerated value never produces the absent-index sentinel. -/
theorem indexRun_lt {A : Type*} [DecidableEq A] (a : A) (xs : List A) (ha : a∈xs) :
    (SemiprimeMaterializedSourceWords.indexRun a xs).value< xs.length := by
  induction xs with
  | nil => simp at ha
  | cons b bs ih =>
    by_cases h : a=b
    · simp only [SemiprimeMaterializedSourceWords.indexRun,h,ite_true,List.length_cons]
      omega
    · have ham : a∈bs := by simpa only [List.mem_cons,h,false_or] using ha
      have ht := ih ham
      simp only [SemiprimeMaterializedSourceWords.indexRun,h,ite_false,List.length_cons]
      omega

/-- Every acquired support code is below the ACTUAL original index bank length. -/
theorem compile_support_lt {I V E : Type} [DecidableEq V] [DecidableEq E] {Q : ℕ}
    (owner : I → V) (factor : I → E) (indices : FiniteEnumeration (V⊕E))
    (z : Packing.ScoreTerm I V Q) (i : ℕ)
    (hi : i∈support (SemiprimeMaterializedSourceWords.compile owner factor indices.values z).value) :
    i< indices.values.length := by
  cases z with
  | inl z =>
    rcases z with ⟨a,b⟩
    simp only [SemiprimeMaterializedSourceWords.compile,support,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> exact indexRun_lt _ _ (indices.complete _)
  | inr z =>
    rcases z with ⟨t,a,b⟩
    simp only [SemiprimeMaterializedSourceWords.compile,support,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl <;> exact indexRun_lt _ _ (indices.complete _)

/-- No hidden instruction expansion occurs in acquired descriptor storage. -/
theorem compileAll_length {I V E : Type} [DecidableEq V] [DecidableEq E] {Q : ℕ}
    (owner : I → V) (factor : I → E) (indices : List (V⊕E)) (terms : List (Packing.ScoreTerm I V Q)) :
    (SemiprimeMaterializedSourceWords.compileAll owner factor indices terms).value.length=terms.length := by
  simp only [SemiprimeMaterializedSourceWords.compileAll_value,List.length_map]

/-- Every actually acquired instruction retains the same original ID bound. -/
theorem compileAll_support_lt {I V E : Type} [DecidableEq V] [DecidableEq E] {Q : ℕ}
    (owner : I → V) (factor : I → E) (indices : FiniteEnumeration (V⊕E))
    (terms : List (Packing.ScoreTerm I V Q)) (p : ScoreProgram Q)
    (hp : p∈(SemiprimeMaterializedSourceWords.compileAll owner factor indices.values terms).value)
    (i : ℕ) (hi : i∈support p) : i< indices.values.length := by
  rw [SemiprimeMaterializedSourceWords.compileAll_value] at hp
  obtain ⟨z,_,rfl⟩ := List.mem_map.mp hp
  rw [← SemiprimeMaterializedSourceWords.compile_value] at hi
  exact compile_support_lt owner factor indices z i hi

/-- Total allocated support-list cells are linear in the actual descriptor count. -/
theorem compileAll_support_cells {I V E : Type} [DecidableEq V] [DecidableEq E] {Q : ℕ}
    (owner : I → V) (factor : I → E) (indices : List (V⊕E)) (terms : List (Packing.ScoreTerm I V Q)) :
    ((SemiprimeMaterializedSourceWords.compileAll owner factor indices terms).value.map
      (fun p => (support p).length)).sum≤4*terms.length := by
  have hs : ∀ p : ScoreProgram Q,(support p).length≤4 := support_length
  have hm : ∀ ps : List (ScoreProgram Q),(ps.map (fun p => (support p).length)).sum≤4*ps.length := by
    intro ps
    induction ps with
    | nil => simp
    | cons p ps ih => simp only [List.map_cons,List.sum_cons,List.length_cons]; have h:=hs p; omega
  simpa only [compileAll_length] using hm (SemiprimeMaterializedSourceWords.compileAll owner factor indices terms).value

/-- Exact number of stored colour coordinates in an ACTUAL cached environment. -/
def colourCells {r Q : ℕ} (env : Environment r Q) : ℕ :=
  env.default.data.size+(env.fixed.map (fun w => w.data.size)).sum+
    (env.overrides.map (fun p => p.2.data.size)).sum

/-- CachedWord.size_eq turns physical array storage into a literal dimension formula. -/
theorem colourCells_eq {r Q : ℕ} (env : Environment r Q) :
    colourCells env=Q*(1+env.fixed.length+env.overrides.length) := by
  have hf : (env.fixed.map (fun w => w.data.size)).sum=env.fixed.length*Q := by
    have he : env.fixed.map (fun w => w.data.size)=env.fixed.map (fun _ => Q) := by
      apply List.map_congr_left
      intro w _
      exact w.size_eq
    rw [he]
    simp
  have ho : (env.overrides.map (fun p => p.2.data.size)).sum=env.overrides.length*Q := by
    have he : env.overrides.map (fun p => p.2.data.size)=env.overrides.map (fun _ => Q) := by
      apply List.map_congr_left
      intro p _
      exact p.2.size_eq
    rw [he]
    simp
  rw [colourCells,env.default.size_eq,hf,ho]
  ring

/-- Actual cached slots each contain a bounded original colour ID. -/
theorem cached_colour_lt {r Q : ℕ} (w : CachedWord r Q) (t : Fin Q) :
    (wordAt w t).val< r := (wordAt w t).isLt

/-- Every stored override has an original bounded variable/factor code. -/
def IdsBound {r Q : ℕ} (N : ℕ) (env : Environment r Q) : Prop :=
  ∀ p∈env.overrides,p.1< N

/-- The actual original base prefix has no new override IDs. -/
theorem base_ids {r Q : ℕ} (N : ℕ) (a : Word r Q) (fixed : List (Word r Q)) :
    IdsBound N (baseEnvironment a fixed) := by
  intro p hp
  simp [baseEnvironment] at hp

/-- Each literal extend operation preserves the original ID bound. -/
theorem extend_ids {r Q : ℕ} (N i : ℕ) (env : Environment r Q) (w : Word r Q)
    (henv : IdsBound N env) (hi : i< N) : IdsBound N (extend env i w) := by
  intro p hp
  simp only [extend,List.mem_cons] at hp
  rcases hp with rfl|hp
  · exact hi
  · exact henv p hp

/-- Base prefix caching materializes exactly Q coordinates per source word. -/
theorem base_cells {r Q : ℕ} (a : Word r Q) (fixed : List (Word r Q)) :
    colourCells (baseEnvironment a fixed)=Q*(1+fixed.length) := by
  rw [colourCells_eq]
  simp [baseEnvironment]

/-- An actual expectation child allocates precisely one more cached source word. -/
theorem extend_cells {r Q : ℕ} (env : Environment r Q) (i : ℕ) (w : Word r Q) :
    colourCells (extend env i w)=colourCells env+Q := by
  rw [colourCells_eq,colourCells_eq]
  simp only [extend,List.length_cons]
  ring

/-- Proof-side reachability matching the literal expectation recursion child calls. -/
inductive ExpectationFrame {r Q : ℕ} (alphabet : List (Word r Q))
    (initial : List ℕ) (base : Environment r Q) : List ℕ → Environment r Q → Prop
  | root : ExpectationFrame alphabet initial base initial base
  | child {i remaining env} : ExpectationFrame alphabet initial base (i::remaining) env →
      (w : Word r Q) → w∈alphabet →
      ExpectationFrame alphabet initial base remaining (extend env i w)

/-- Every actual recursive frame conserves remaining depth plus stored overrides. -/
theorem frame_dimensions {r Q : ℕ} {alphabet : List (Word r Q)} {initial : List ℕ}
    {base : Environment r Q} {remaining : List ℕ} {env : Environment r Q}
    (h : ExpectationFrame alphabet initial base remaining env) :
    env.fixed.length=base.fixed.length ∧
      env.overrides.length+remaining.length=base.overrides.length+initial.length := by
  induction h with
  | root => exact ⟨rfl,rfl⟩
  | child h w hw ih =>
    rcases ih with ⟨hf,ho⟩
    simp only [extend,List.length_cons]
    exact ⟨hf,by simp only [List.length_cons] at ho; omega⟩

/-- Remaining IDs are drawn from the actual original support list. -/
theorem frame_remaining_mem {r Q : ℕ} {alphabet : List (Word r Q)} {initial : List ℕ}
    {base : Environment r Q} {remaining : List ℕ} {env : Environment r Q}
    (h : ExpectationFrame alphabet initial base remaining env) :
    ∀ i∈remaining,i∈initial := by
  induction h with
  | root => exact fun _ hi => hi
  | child h w hw ih => exact fun i hi => ih i (List.mem_cons_of_mem _ hi)

/-- Every actual recursive override is bounded from original support IDs. -/
theorem frame_ids {r Q : ℕ} {alphabet : List (Word r Q)} {initial : List ℕ}
    {base : Environment r Q} {remaining : List ℕ} {env : Environment r Q}
    (N : ℕ) (h : ExpectationFrame alphabet initial base remaining env)
    (hb : IdsBound N base) (hi : ∀ i∈initial,i< N) : IdsBound N env := by
  induction h with
  | root => exact hb
  | @child i remaining env h w hw ih =>
    exact extend_ids N i env w ih (hi i (frame_remaining_mem h i List.mem_cons_self))

/-- All actual frame colour slots are bounded from ORIGINAL prefix/support lengths. -/
theorem frame_cells {r Q : ℕ} {alphabet : List (Word r Q)} {initial : List ℕ}
    {base : Environment r Q} {remaining : List ℕ} {env : Environment r Q}
    (h : ExpectationFrame alphabet initial base remaining env) :
    colourCells env≤ Q*(1+base.fixed.length+base.overrides.length+initial.length) := by
  have hd := frame_dimensions h
  rw [colourCells_eq,hd.1]
  exact Nat.mul_le_mul_left Q (by omega)

/-- The actual active support scan only removes original remaining IDs. -/
theorem activeRun_mem (support remaining : List ℕ) (i : ℕ)
    (hi : i∈(activeRun support remaining).value) : i∈remaining := by
  rw [activeRun_value] at hi
  exact (List.mem_filter.mp hi).1

/-- Actual localTerm support scans produce at most four ORIGINAL bounded IDs. -/
theorem local_initial_bound {Q : ℕ} (p : ScoreProgram Q) (fixedLength n N : ℕ)
    (hn : n+fixedLength≤ N) :
    let initial := (activeRun (support p) (List.range' fixedLength n)).value
    initial.length≤4 ∧ ∀ i∈initial,i< N := by
  refine ⟨?_,?_⟩
  · rw [activeRun_value]
    exact (active_length_le (support p).toFinset _ List.nodup_range').trans
      ((List.toFinset_card_le _).trans (support_length p))
  · intro i hi
    have hm := activeRun_mem _ _ i hi
    have hb := List.mem_range'.mp hm
    omega

/-- All actual localTerm recursive frames have bounded IDs, at most four
stored overrides, and the original prefix plus four cached words. -/
theorem local_frame_bound {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (p : ScoreProgram Q) (n N : ℕ) (fixed : List (Word r Q))
    (hn : n+fixed.length≤ N) (remaining : List ℕ) (env : Environment r Q)
    (h : ExpectationFrame (a::tail)
      (activeRun (support p) (List.range' fixed.length n)).value
      (baseEnvironment a fixed) remaining env) :
    IdsBound N env ∧ env.fixed.length=fixed.length ∧ env.overrides.length≤4 ∧
      remaining.length≤4 ∧ colourCells env≤ Q*(1+N+4) := by
  have hi := local_initial_bound p fixed.length n N hn
  have hd := frame_dimensions h
  have hc := frame_cells h
  have hid := frame_ids N h (base_ids N a fixed) hi.2
  simp only [baseEnvironment,List.length_map,List.length_nil,Nat.zero_add] at hd hc
  refine ⟨hid,hd.1,by omega,by omega,?_⟩
  exact hc.trans (Nat.mul_le_mul_left Q (by omega))

/-- An actual candidate comparison always selects from the literal candidate bank. -/
theorem choose_mem {W : Type*} (score : W → Run ℚ) (a : W) (tail : List W) :
    (choose score a tail).value∈a::tail := by
  induction tail generalizing a with
  | nil => simp [choose]
  | cons b bs ih =>
    simp only [choose]
    split
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih b)

/-- Proof-side reachability matching the ACTUAL original source assign recursion. -/
inductive SearchFrame {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (x y offset : ℚ) (N : ℕ) : ℕ → List (Word r Q) → Prop
  | root : SearchFrame a tail programs x y offset N N []
  | child {n fixed} : SearchFrame a tail programs x y offset N (n+1) fixed →
      SearchFrame a tail programs x y offset N n
        ((choose (fun w => SemiprimeMaterializedScoreSearch.sequential a tail programs x y offset n (w::fixed))
          a tail).value::fixed)

/-- Every actual assigned prefix keeps exactly the original total index count. -/
theorem search_frame_length {r Q : ℕ} {a : Word r Q} {tail : List (Word r Q)}
    {programs : List (ScoreProgram Q)} {x y offset : ℚ} {N n : ℕ} {fixed : List (Word r Q)}
    (h : SearchFrame a tail programs x y offset N n fixed) : n+fixed.length=N := by
  induction h with
  | root => simp
  | child h ih => simp only [List.length_cons]; omega

/-- The original search never manufactures a candidate outside its acquired word bank. -/
theorem search_frame_candidates {r Q : ℕ} {a : Word r Q} {tail : List (Word r Q)}
    {programs : List (ScoreProgram Q)} {x y offset : ℚ} {N n : ℕ} {fixed : List (Word r Q)}
    (h : SearchFrame a tail programs x y offset N n fixed) : ∀ w∈fixed,w∈a::tail := by
  induction h with
  | root => simp
  | child h ih =>
    intro w hw
    rcases List.mem_cons.mp hw with rfl|hw
    · exact choose_mem _ _ _
    · exact ih w hw

/-- Every actual candidate evaluator call has the SAME original remaining/prefix total. -/
theorem candidate_evaluator_length {r Q : ℕ} {a : Word r Q} {tail : List (Word r Q)}
    {programs : List (ScoreProgram Q)} {x y offset : ℚ} {N n : ℕ} {fixed : List (Word r Q)}
    (h : SearchFrame a tail programs x y offset N (n+1) fixed) (w : Word r Q) :
    n+(w::fixed).length=N := by
  have hh := search_frame_length h
  simp only [List.length_cons]
  omega

/-- Every local frame reached during any actual candidate evaluation has its
original-index bound and polynomial cached colour volume. -/
theorem search_local_frame_bound {r Q : ℕ} {a : Word r Q} {tail : List (Word r Q)}
    {programs : List (ScoreProgram Q)} {x y offset : ℚ} {N n : ℕ} {fixed : List (Word r Q)}
    (hsearch : SearchFrame a tail programs x y offset N (n+1) fixed)
    (w : Word r Q) (p : ScoreProgram Q) (remaining : List ℕ) (env : Environment r Q)
    (hframe : ExpectationFrame (a::tail)
      (activeRun (support p) (List.range' (w::fixed).length n)).value
      (baseEnvironment a (w::fixed)) remaining env) :
    IdsBound N env ∧ env.overrides.length≤4 ∧ colourCells env≤ Q*(1+N+4) := by
  have hh := local_frame_bound a tail p n N (w::fixed)
    (le_of_eq (candidate_evaluator_length hsearch w)) remaining env hframe
  exact ⟨hh.1,hh.2.2.1,hh.2.2.2.2⟩

/-- Constructor plus literal scalar fields in one actually acquired instruction. -/
def descriptorCells {Q : ℕ} : ScoreProgram Q → ℕ
  | .incidence _ _ _ _ => 5
  | .head _ _ _ => 4

/-- The cached descriptor bank has linear concrete constructor/field storage. -/
theorem compileAll_descriptor_cells {I V E : Type} [DecidableEq V] [DecidableEq E] {Q : ℕ}
    (owner : I → V) (factor : I → E) (indices : List (V⊕E)) (terms : List (Packing.ScoreTerm I V Q)) :
    ((SemiprimeMaterializedSourceWords.compileAll owner factor indices terms).value.map descriptorCells).sum≤
      5*terms.length := by
  have hm : ∀ ps : List (ScoreProgram Q),(ps.map descriptorCells).sum≤5*ps.length := by
    intro ps
    induction ps with
    | nil => simp
    | cons p ps ih => cases p <;> simp only [List.map_cons,List.sum_cons,List.length_cons,descriptorCells] <;> omega
  simpa only [compileAll_length] using hm (SemiprimeMaterializedSourceWords.compileAll owner factor indices terms).value

/-- Count exactly the NEW cached colour-coordinate allocations in the literal
expectation child-call tree. Base/fixed caching is accounted separately. -/
def overrideColourAllocations {r Q : ℕ} (alphabet : List (Word r Q)) : List ℕ → ℕ
  | [] => 0
  | _::remaining => alphabet.length*(Q+overrideColourAllocations alphabet remaining)

/-- The executed local completion tree allocates only a fixed power of its
ACTUAL alphabet size and support depth, never a full original assignment bank. -/
theorem override_allocations_bound {r Q : ℕ} (alphabet : List (Word r Q)) (remaining : List ℕ) :
    overrideColourAllocations alphabet remaining≤ Q*(alphabet.length+1)^(remaining.length+1) := by
  induction remaining with
  | nil => simp [overrideColourAllocations]
  | cons i remaining ih =>
    have hp : alphabet.length≤(alphabet.length+1)^(remaining.length+1) := by
      have hpow : (alphabet.length+1)^1≤(alphabet.length+1)^(remaining.length+1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      exact (Nat.le_succ _).trans (by simpa only [pow_one] using hpow)
    simp only [overrideColourAllocations,List.length_cons]
    rw [show remaining.length+1+1=(remaining.length+1)+1 by omega,pow_succ]
    have hm := Nat.mul_le_mul_left alphabet.length (Nat.add_le_add_left ih Q)
    have hq := Nat.mul_le_mul_left Q hp
    nlinarith

/-- Literal initial prefix cache plus all actual localTerm override allocations. -/
def sequentialColourAllocations {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (n : ℕ) (fixed : List (Word r Q)) : ℕ :=
  colourCells (baseEnvironment a fixed)+
    (programs.map (fun p => overrideColourAllocations (a::tail)
      (activeRun (support p) (List.range' fixed.length n)).value)).sum

/-- Every actual source evaluator's NEW cached-colour allocation is bounded
from original N, descriptor count, Q and the actual candidate alphabet size. -/
theorem sequential_allocations_bound {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (n N : ℕ) (fixed : List (Word r Q))
    (hn : n+fixed.length≤ N) :
    sequentialColourAllocations a tail programs n fixed≤
      Q*(1+N)+programs.length*(Q*((a::tail).length+1)^5) := by
  have hp (p : ScoreProgram Q) : overrideColourAllocations (a::tail)
      (activeRun (support p) (List.range' fixed.length n)).value≤ Q*((a::tail).length+1)^5 := by
    have hl := (local_initial_bound p fixed.length n N hn).1
    exact (override_allocations_bound (a::tail) _).trans
      (Nat.mul_le_mul_left Q (Nat.pow_le_pow_right (by simp) (by omega)))
  have hm : ∀ ps : List (ScoreProgram Q),
      (ps.map (fun p => overrideColourAllocations (a::tail)
        (activeRun (support p) (List.range' fixed.length n)).value)).sum≤
      ps.length*(Q*((a::tail).length+1)^5) := by
    intro ps
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      have hh := hp p
      simp only [List.length_cons] at hh ih
      nlinarith
  unfold sequentialColourAllocations
  rw [base_cells]
  exact Nat.add_le_add (Nat.mul_le_mul_left Q (by omega)) (hm programs)

/-- In an actual original source constructor, BOTH finite bank sizes are derived. -/
theorem original_bank_sizes {I V E : Type} {r Q : ℕ}
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) :
    (en.wordFirst::en.wordTail).length=r^Q ∧ en.types.values.length=r^(2*Q) :=
  ⟨SemiprimeSourceOffsetHeight.caller_word_length en,
    SemiprimeSourceOffsetHeight.caller_universal_length en⟩

/-- The actual completed assignment has the original number of labels. -/
theorem search_output_length {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (x y offset : ℚ) (N : ℕ) :
    (SemiprimeMaterializedScoreSearch.search a tail programs x y offset N).value.length=N := by
  simpa only [SemiprimeMaterializedScoreSearch.search,List.length_nil,Nat.add_zero] using
    SemiprimeMaterializedWordSearch.assign_length a tail
      (SemiprimeMaterializedScoreSearch.sequential a tail programs x y offset) N []

/-- The actual assign result is connected to the literal source-call frame
relation, rather than assumed to be a reachable completed state. -/
theorem assign_result_frame {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (x y offset : ℚ) (N n : ℕ) (fixed : List (Word r Q))
    (h : SearchFrame a tail programs x y offset N n fixed) :
    SearchFrame a tail programs x y offset N 0
      (assign a tail (SemiprimeMaterializedScoreSearch.sequential a tail programs x y offset) n fixed).value := by
  induction n generalizing fixed with
  | zero => exact h
  | succ n ih =>
    exact ih _ (SearchFrame.child h)

/-- The complete ACTUAL source search output is a reached terminal frame. -/
theorem search_output_frame {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (x y offset : ℚ) (N : ℕ) :
    SearchFrame a tail programs x y offset N 0
      (SemiprimeMaterializedScoreSearch.search a tail programs x y offset N).value :=
  assign_result_frame a tail programs x y offset N N [] SearchFrame.root

/-- All actual returned source labels belong to the original acquired candidate bank. -/
theorem search_output_candidates {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (x y offset : ℚ) (N : ℕ) :
    ∀ w∈(SemiprimeMaterializedScoreSearch.search a tail programs x y offset N).value,w∈a::tail :=
  search_frame_candidates (search_output_frame a tail programs x y offset N)

/-- Literal paid original-input enumeration sizes, including variable AND factor
IDs. The source search has N=n+F labels, not only the n variable labels. -/
theorem indexed_source_dimensions (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
    en.indices.values.length=n+F ∧
      en.terms.values.length=(∑ e,arity e)^2+Q*n^2 ∧
      (en.wordFirst::en.wordTail).length=r^Q ∧ en.types.values.length=r^(2*Q) := by
  exact ⟨SemiprimePaidFiniteEnumerations.indexed_indices_length n F r Q arity,
    SemiprimePaidFiniteEnumerations.indexed_score_length n F r Q arity,
    (original_bank_sizes _).1,(original_bank_sizes _).2⟩

/-- Actual right-recursive sum reports retain every callback's paid storage work. -/
theorem sumRun_work_ge_cells {A : Type*} (f : A → Run ℚ) (cells : A → ℕ) (xs : List A)
    (hf : ∀ a∈xs,cells a≤(f a).work) :
    (xs.map cells).sum≤(sumRun f xs).work := by
  induction xs with
  | nil => simp [sumRun]
  | cons a xs ih =>
    have ha := hf a List.mem_cons_self
    have ht := ih (fun b hb => hf b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons,List.sum_cons,sumRun]
    omega

/-- The exact expectation report ALREADY pays every newly cached override
coordinate; the allocation counter is attached to actual execution work. -/
theorem expectation_allocations_le_work {r Q : ℕ} (alphabet : List (Word r Q))
    (x y : ℚ) (p : ScoreProgram Q) (remaining : List ℕ) (env : Environment r Q) :
    overrideColourAllocations alphabet remaining≤
      (SemiprimeMaterializedScoreSearch.expectation alphabet x y p remaining env).work := by
  induction remaining generalizing env with
  | nil => simp [overrideColourAllocations]
  | cons i remaining ih =>
    have hs := sumRun_work_ge_cells
      (fun w => (⟨(SemiprimeMaterializedScoreSearch.expectation alphabet x y p remaining (extend env i w)).value,
        (SemiprimeMaterializedScoreSearch.expectation alphabet x y p remaining (extend env i w)).work+Q+2⟩ : Run ℚ))
      (fun _ => Q+overrideColourAllocations alphabet remaining) alphabet (by
        intro w _
        have hh := ih (extend env i w)
        dsimp only
        omega)
    simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id] at hs
    simp only [overrideColourAllocations,SemiprimeMaterializedScoreSearch.expectation]
    omega

/-- The actual sequential report pays initial prefix caching AND all local
completion cache allocations, with no assumed live-state bound. -/
theorem sequential_allocations_le_work {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (x y offset : ℚ) (n : ℕ) (fixed : List (Word r Q)) :
    sequentialColourAllocations a tail programs n fixed≤
      (SemiprimeMaterializedScoreSearch.sequential a tail programs x y offset n fixed).work := by
  have hs := sumRun_work_ge_cells
    (fun p => SemiprimeMaterializedScoreSearch.localTerm (a::tail) x y p (List.range' fixed.length n)
      (baseEnvironment a fixed))
    (fun p => overrideColourAllocations (a::tail) (activeRun (support p) (List.range' fixed.length n)).value)
    programs (by
      intro p _
      have hh := expectation_allocations_le_work (a::tail) x y p
        (activeRun (support p) (List.range' fixed.length n)).value (baseEnvironment a fixed)
      change _≤(activeRun _ _).work+_+5
      omega)
  have hb : colourCells (baseEnvironment a fixed)≤2*(Q+1)*(fixed.length+1) := by
    rw [base_cells]
    nlinarith
  unfold sequentialColourAllocations SemiprimeMaterializedScoreSearch.sequential
    SemiprimeMaterializedScoreSearch.evaluate
  dsimp only
  omega

end RiemannGaussian.SemiprimeSourceSearchState
