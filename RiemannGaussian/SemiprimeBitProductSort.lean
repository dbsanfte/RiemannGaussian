/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePrimeSieve
import Mathlib.Data.List.Induction
import Mathlib.Data.Nat.Size

/-!
# Witness-preserving product sorting with Boolean payload work

Both factor words and all product multiplicities survive sorting. The
comparison data path is the proved Boolean product circuit. Distribution,
merging and singleton outputs copy every payload bit through the existing
charged Boolean copy routine. The clocks count circuit primitives and
structural list visits/cells; they do not supply an input encoder, a public
root algorithm, or a complete machine/memory refinement for the factorizer.
-/

namespace RiemannGaussian.SemiprimeBitProductSort

open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimePrimeSieve

/-- The two actual factor words, before any natural-value projection. -/
abbrev WordPair := List Bool × List Bool

/-- Downstream factor decoding, never used by the sort data path. -/
def decodePair (v : WordPair) : ℕ×ℕ := (bitValue v.1,bitValue v.2)

/-- The mathematical product label of a retained word pair. -/
def pairValue (v : WordPair) : ℕ := bitValue v.1*bitValue v.2

/-- Only the Boolean circuit computes the comparison flag. -/
def pairLE (v w : WordPair) : Bool :=
  (compareProductBits v.1 v.2 w.1 w.2).lessEqual

theorem pairLE_correct (v w : WordPair) : pairLE v w=true ↔ pairValue v≤pairValue w :=
  compareProductBits_correct _ _ _ _

/-- The specification view of the Boolean ordering predicate. -/
theorem pairLE_eq_decide (v w : WordPair) : pairLE v w=decide (pairValue v≤pairValue w) := by
  rw [Bool.eq_iff_iff,decide_eq_true_eq]
  exact pairLE_correct v w

/-- Copying to the same physical template preserves the exact word,
including every high zero; numeric equality alone would lose padding. -/
theorem fitBits_self (bits : List Bool) : (fitBits bits bits).bits=bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp only [fitBits,ih]

/-- Full copy reports remain available before the copied-pair projection. -/
structure PairCopy where
  /-- Actual first word copy and all its primitive charges. -/
  left : BitReport
  /-- Actual second word copy and all its primitive charges. -/
  right : BitReport
  /-- Both primitive clocks and the factor-pair constructor cell. -/
  clock : ℕ

/-- Physically copy both factor payloads, without decoding their values. -/
def copyPair (v : WordPair) : PairCopy :=
  let left := fitBits v.1 v.1
  let right := fitBits v.2 v.2
  ⟨left,right,bitCost left+bitCost right+1⟩

/-- The downstream pair of actual copied word lists. -/
def PairCopy.row (r : PairCopy) : WordPair := (r.left.bits,r.right.bits)

theorem copyPair_row (v : WordPair) : (copyPair v).row=v := by
  simp only [PairCopy.row,copyPair,fitBits_self]

theorem copyPair_cost {L : ℕ} {v : WordPair}
    (h : v.1.length≤L ∧ v.2.length≤L) : (copyPair v).clock≤8*L+3 := by
  have hl := fitBits_cost v.1 v.1
  have hr := fitBits_cost v.2 v.2
  change bitCost (fitBits v.1 v.1)+bitCost (fitBits v.2 v.2)+1≤_
  omega

/-- Sorted or copied payloads and their actual structural/circuit clocks. -/
structure WordReport where
  /-- The full word-pair carrier, retaining every input occurrence. -/
  rows : List WordPair
  /-- Primitive payload work and every declared list visit/cell. -/
  clock : ℕ
  /-- Actual calls to the Boolean product comparison circuit. -/
  comparisons : ℕ

/-- Copy each row payload. Each frame pays its list test and cons cell;
the terminal empty list pays one test. -/
def copyRows : List WordPair → WordReport
  | [] => ⟨[],1,0⟩
  | v::vs =>
    let head := copyPair v
    let tail := copyRows vs
    ⟨head.row::tail.rows,head.clock+tail.clock+2,0⟩

theorem copyRows_rows (rows : List WordPair) : (copyRows rows).rows=rows := by
  induction rows with
  | nil => rfl
  | cons v vs ih => simp only [copyRows,copyPair_row,ih]

/-- Physical bounded-width premise, including any supplied padding. -/
def BoundedWords (L : ℕ) (rows : List WordPair) : Prop :=
  ∀ v∈rows, v.1.length≤L ∧ v.2.length≤L

theorem BoundedWords.of_perm {L : ℕ} {xs ys : List WordPair}
    (h : BoundedWords L xs) (hp : ys.Perm xs) : BoundedWords L ys :=
  fun v hv => h v (hp.mem_iff.mp hv)

theorem copyRows_cost {L : ℕ} {rows : List WordPair} (h : BoundedWords L rows) :
    (copyRows rows).clock≤(8*L+5)*rows.length+1 := by
  induction rows with
  | nil => simp only [copyRows,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons v vs ih =>
    have hh := copyPair_cost (h v List.mem_cons_self)
    have ht := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    simp only [copyRows,List.length_cons]
    nlinarith

/-- Merge by Boolean product comparisons. Selected payloads and remaining
tails are copied; no array index or natural-value comparison chooses a row.
Each nonterminal frame pays two list tests, a flag test and a cons cell. -/
def mergeWords : List WordPair → List WordPair → WordReport
  | [],ys =>
    let tail := copyRows ys
    ⟨tail.rows,tail.clock+2,0⟩
  | xs,[] =>
    let tail := copyRows xs
    ⟨tail.rows,tail.clock+2,0⟩
  | x::xs,y::ys =>
    let comparison := compareProductBits x.1 x.2 y.1 y.2
    if comparison.lessEqual=true then
      let head := copyPair x
      let tail := mergeWords xs (y::ys)
      ⟨head.row::tail.rows,comparison.clock+head.clock+tail.clock+4,tail.comparisons+1⟩
    else
      let head := copyPair y
      let tail := mergeWords (x::xs) ys
      ⟨head.row::tail.rows,comparison.clock+head.clock+tail.clock+4,tail.comparisons+1⟩
termination_by xs ys => xs.length+ys.length
decreasing_by all_goals simp_wf

/-- Exact whole-word output transport to the standard merge, preserving
padding and factor tags rather than only sorted product values. -/
theorem mergeWords_rows (xs ys : List WordPair) :
    (mergeWords xs ys).rows=List.merge xs ys pairLE := by
  cases xs with
  | nil => simp only [mergeWords,copyRows_rows,List.nil_merge]
  | cons x xs =>
    cases ys with
    | nil => simp only [mergeWords,copyRows_rows,List.merge_right]
    | cons y ys =>
      have hl := mergeWords_rows xs (y::ys)
      have hr := mergeWords_rows (x::xs) ys
      rw [mergeWords,List.merge]
      dsimp only [pairLE]
      split_ifs with h
      · simp [copyPair_row,hl,h]
      · simp [copyPair_row,hr,h]
termination_by xs.length+ys.length
decreasing_by all_goals (simp_all only [List.length_cons]; omega)

theorem mergeWords_perm (xs ys : List WordPair) : (mergeWords xs ys).rows.Perm (xs++ys) := by
  rw [mergeWords_rows]
  exact List.merge_perm_append pairLE

theorem mergeWords_comparisons (xs ys : List WordPair) :
    (mergeWords xs ys).comparisons≤xs.length+ys.length := by
  cases xs with
  | nil => simp only [mergeWords,Nat.zero_le]
  | cons x xs =>
    cases ys with
    | nil => simp only [mergeWords,Nat.zero_le]
    | cons y ys =>
      have hl := mergeWords_comparisons xs (y::ys)
      have hr := mergeWords_comparisons (x::xs) ys
      rw [mergeWords]
      split <;> dsimp only [List.length_cons] at hl hr ⊢ <;> omega
termination_by xs.length+ys.length
decreasing_by all_goals (simp_all only [List.length_cons]; omega)

/-- A merge's complete declared payload/list clock is linear in its
actual total row count and quadratic in physical factor width. -/
theorem mergeWords_cost {L : ℕ} {xs ys : List WordPair}
    (hx : BoundedWords L xs) (hy : BoundedWords L ys) :
    (mergeWords xs ys).clock≤80*(L+1)^2*(xs.length+ys.length)+3 := by
  cases xs with
  | nil =>
    have hc := copyRows_cost hy
    have hk : 8*L+5≤80*(L+1)^2 := by nlinarith
    have hm := Nat.mul_le_mul_right ys.length hk
    simp only [mergeWords,List.length_nil,Nat.zero_add]
    omega
  | cons x xs =>
    cases ys with
    | nil =>
      have hc := copyRows_cost hx
      have hk : 8*L+5≤80*(L+1)^2 := by nlinarith
      have hm := Nat.mul_le_mul_right (x::xs).length hk
      simp only [mergeWords,List.length_nil,Nat.add_zero]
      omega
    | cons y ys =>
      have hxx := hx x List.mem_cons_self
      have hyy := hy y List.mem_cons_self
      have hxt : BoundedWords L xs := fun v hv => hx v (List.mem_cons_of_mem _ hv)
      have hyt : BoundedWords L ys := fun v hv => hy v (List.mem_cons_of_mem _ hv)
      have hl := mergeWords_cost hxt hy
      have hr := mergeWords_cost hx hyt
      have hc := compareProductBits_cost hxx.1 hxx.2 hyy.1 hyy.2
      have hcx := copyPair_cost hxx
      have hcy := copyPair_cost hyy
      have hk : 72*(L+1)^2+(8*L+3)+4≤80*(L+1)^2 := by nlinarith
      rw [mergeWords]
      split <;> dsimp only [List.length_cons] at hl hr ⊢ <;> nlinarith
termination_by xs.length+ys.length
decreasing_by all_goals (simp_all only [List.length_cons]; omega)

/-- Actual alternating halves with their payload-copy/list clock. -/
structure SplitReport where
  /-- Every first, third and subsequent odd-position payload. -/
  left : List WordPair
  /-- Every second, fourth and subsequent even-position payload. -/
  right : List WordPair
  /-- All actual copies, input visits and new half-list cells. -/
  clock : ℕ

/-- Structural balanced splitting avoids a computed natural array index.
Every payload is copied; empty/singleton/two-row frames pay their tests
and output cells before the recursive alternating distribution. -/
def splitWords : List WordPair → SplitReport
  | [] => ⟨[],[],1⟩
  | [x] =>
    let head := copyPair x
    ⟨[head.row],[],head.clock+3⟩
  | x::y::xs =>
    let tail := splitWords xs
    let left := copyPair x
    let right := copyPair y
    ⟨left.row::tail.left,right.row::tail.right,tail.clock+left.clock+right.clock+5⟩

theorem splitWords_lengths (xs : List WordPair) :
    (splitWords xs).left.length=(xs.length+1)/2 ∧
      (splitWords xs).right.length=xs.length/2 := by
  induction xs using List.twoStepInduction with
  | nil => norm_num [splitWords]
  | singleton x => norm_num [splitWords]
  | cons_cons x y xs ih _ =>
    simp only [splitWords,List.length_cons] at ih ⊢
    omega

theorem splitWords_length_sum (xs : List WordPair) :
    (splitWords xs).left.length+(splitWords xs).right.length=xs.length := by
  have h := splitWords_lengths xs
  omega

theorem splitWords_perm (xs : List WordPair) :
    ((splitWords xs).left++(splitWords xs).right).Perm xs := by
  induction xs using List.twoStepInduction with
  | nil => exact List.Perm.refl _
  | singleton x => simp only [splitWords,copyPair_row,List.append_nil]; exact List.Perm.refl _
  | cons_cons x y xs ih _ =>
    simp only [splitWords,copyPair_row,List.cons_append]
    exact (List.perm_middle.cons x).trans ((ih.cons y).cons x)

theorem splitWords_bounded {L : ℕ} {xs : List WordPair} (h : BoundedWords L xs) :
    BoundedWords L (splitWords xs).left ∧ BoundedWords L (splitWords xs).right := by
  have hb := h.of_perm (splitWords_perm xs)
  exact ⟨fun v hv => hb v (List.mem_append_left _ hv),
    fun v hv => hb v (List.mem_append_right _ hv)⟩

theorem splitWords_cost {L : ℕ} {xs : List WordPair} (h : BoundedWords L xs) :
    (splitWords xs).clock≤12*(L+1)*xs.length+2 := by
  induction xs using List.twoStepInduction with
  | nil => simp only [splitWords,List.length_nil,Nat.mul_zero,Nat.zero_add]; omega
  | singleton x =>
    have hc := copyPair_cost (h x List.mem_cons_self)
    simp only [splitWords,List.length_cons,List.length_nil]
    nlinarith
  | cons_cons x y xs ih _ =>
    have hcx := copyPair_cost (h x List.mem_cons_self)
    have hcy := copyPair_cost (h y (List.mem_cons_of_mem _ List.mem_cons_self))
    have hct := ih (fun v hv => h v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)))
    simp only [splitWords,List.length_cons]
    nlinarith

/-- Both structural halves are strictly shorter when a split is needed. -/
theorem splitWords_shorter {xs : List WordPair} (h : 2≤xs.length) :
    (splitWords xs).left.length<xs.length ∧ (splitWords xs).right.length<xs.length := by
  have hs := splitWords_lengths xs
  omega

/-- Balanced structural merge sort. Termination lengths are proof-only;
the data path inspects lists and copies word payloads without decoding.
Each sort frame pays both list-pattern tests in addition to its subreports. -/
def sortWords (rows : List WordPair) : WordReport :=
  match rows with
  | [] => ⟨[],1,0⟩
  | [x] =>
    let head := copyPair x
    ⟨[head.row],head.clock+3,0⟩
  | x::y::xs =>
    let halves := splitWords (x::y::xs)
    let left := sortWords halves.left
    let right := sortWords halves.right
    let merged := mergeWords left.rows right.rows
    ⟨merged.rows,halves.clock+left.clock+right.clock+merged.clock+2,
      left.comparisons+right.comparisons+merged.comparisons⟩
termination_by rows.length
decreasing_by
  all_goals
    have h := splitWords_shorter (xs:=x::y::xs) (by simp only [List.length_cons]; omega)
    first | exact h.1 | exact h.2

/-- Full word-pair permutation, including identical products, repeated
factor pairs and all physical padding. No product deduplication occurs. -/
theorem sortWords_perm (rows : List WordPair) : (sortWords rows).rows.Perm rows := by
  cases rows with
  | nil => simp only [sortWords]; exact List.Perm.refl _
  | cons x xs =>
    cases xs with
    | nil => simp only [sortWords,copyPair_row]; exact List.Perm.refl _
    | cons y xs =>
      rw [sortWords]
      dsimp only
      exact (mergeWords_perm _ _).trans
        (((sortWords_perm _).append (sortWords_perm _)).trans (splitWords_perm _))
termination_by rows.length
decreasing_by
  all_goals
    have h := splitWords_shorter (xs:=x::y::xs) (by simp only [List.length_cons]; omega)
    first | exact h.1 | exact h.2

theorem sortWords_length (rows : List WordPair) : (sortWords rows).rows.length=rows.length :=
  (sortWords_perm rows).length_eq

theorem sortWords_bounded {L : ℕ} {rows : List WordPair} (h : BoundedWords L rows) :
    BoundedWords L (sortWords rows).rows := h.of_perm (sortWords_perm rows)

/-- Product order is a downstream property of the complete sorted carrier. -/
theorem sortWords_ordered (rows : List WordPair) :
    (sortWords rows).rows.Pairwise (fun v w => pairValue v≤pairValue w) := by
  cases rows with
  | nil => simp only [sortWords]; exact List.Pairwise.nil
  | cons x xs =>
    cases xs with
    | nil => simp only [sortWords,copyPair_row,List.pairwise_singleton]
    | cons y xs =>
      have hl := sortWords_ordered (splitWords (x::y::xs)).left
      have hr := sortWords_ordered (splitWords (x::y::xs)).right
      have hbl := hl.imp (fun {v w} hvw => (pairLE_correct v w).mpr hvw)
      have hbr := hr.imp (fun {v w} hvw => (pairLE_correct v w).mpr hvw)
      have hm := List.pairwise_merge (le:=pairLE)
        (fun a b c hab hbc => (pairLE_correct a c).mpr
          (((pairLE_correct a b).mp hab).trans ((pairLE_correct b c).mp hbc)))
        (fun a b => by
          simp only [Bool.or_eq_true,pairLE_correct]
          exact le_total _ _) _ _ hbl hbr
      rw [sortWords]
      dsimp only
      rw [mergeWords_rows]
      exact hm.imp (fun {v w} hvw => (pairLE_correct v w).mp hvw)
termination_by rows.length
decreasing_by
  all_goals
    have h := splitWords_shorter (xs:=x::y::xs) (by simp only [List.length_cons]; omega)
    first | exact h.1 | exact h.2

/-- Balanced depth bounds both actual comparison calls and the complete
declared circuit/payload/list clock. The power bound is used only in proof. -/
theorem sortWords_bounds_depth {L : ℕ} (depth : ℕ) (rows : List WordPair)
    (hlen : rows.length≤2^depth) (hw : BoundedWords L rows) :
    (sortWords rows).clock≤100*(L+1)^2*rows.length*(depth+1)+1 ∧
      (sortWords rows).comparisons≤rows.length*depth := by
  by_cases hs : rows.length≤1
  · cases rows with
    | nil => simp [sortWords]
    | cons x xs =>
      cases xs with
      | nil =>
        have hc := copyPair_cost (hw x List.mem_cons_self)
        have hd : 100*(L+1)^2≤100*(L+1)^2*(depth+1) :=
          Nat.le_mul_of_pos_right _ (by omega)
        simp only [sortWords,List.length_cons,List.length_nil,Nat.zero_add,Nat.mul_one]
        constructor
        · nlinarith
        · omega
      | cons y ys => simp only [List.length_cons] at hs; omega
  · have hn : 2≤rows.length := by omega
    cases depth with
    | zero => simp only [pow_zero] at hlen; omega
    | succ depth =>
      cases rows with
      | nil => simp only [List.length_nil] at hn; omega
      | cons x xs =>
        cases xs with
        | nil => simp only [List.length_cons,List.length_nil] at hn; omega
        | cons y xs =>
          have hlens := splitWords_lengths (x::y::xs)
          have hsum := splitWords_length_sum (x::y::xs)
          have hp : 2^(depth+1)=2*2^depth := by rw [pow_succ,Nat.mul_comm]
          rw [hp] at hlen
          have hll : (splitWords (x::y::xs)).left.length≤2^depth := by omega
          have hrl : (splitWords (x::y::xs)).right.length≤2^depth := by omega
          have hwidth := splitWords_bounded hw
          have hl := sortWords_bounds_depth depth _ hll hwidth.1
          have hr := sortWords_bounds_depth depth _ hrl hwidth.2
          have hsplit := splitWords_cost hw
          have hmerge := mergeWords_cost (sortWords_bounded hwidth.1)
            (sortWords_bounded hwidth.2)
          have hcompare := mergeWords_comparisons
            (sortWords (splitWords (x::y::xs)).left).rows
            (sortWords (splitWords (x::y::xs)).right).rows
          simp only [sortWords_length] at hmerge hcompare
          have hk : 12*(L+1)+80*(L+1)^2+4≤100*(L+1)^2 := by nlinarith
          have hkn := Nat.mul_le_mul_right (x::y::xs).length hk
          rw [sortWords]
          dsimp only
          constructor
          · nlinarith [hl.1,hr.1]
          · nlinarith [hl.2,hr.2]
termination_by depth

/-- For n physical word pairs, at most n*ceil(log2 n) Boolean comparisons
and 100*(L+1)^2*n*(ceil(log2 n)+1)+1 declared primitive/list work. -/
theorem sortWords_bounds {L : ℕ} {rows : List WordPair} (h : BoundedWords L rows) :
    (sortWords rows).clock≤100*(L+1)^2*rows.length*(Nat.clog 2 rows.length+1)+1 ∧
      (sortWords rows).comparisons≤rows.length*Nat.clog 2 rows.length :=
  sortWords_bounds_depth _ _ (Nat.le_pow_clog (by decide) _) h

/-- The canonical natural-word interface has the specified value.
This theorem supplies no price for creating those words from natural inputs. -/
theorem bitValue_natBits (n : ℕ) : bitValue n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => simp only [Nat.zero_bits,bitValue]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    simp only [bitValue,ih,Nat.bit_val]
    cases b <;> simp [bitNat,Nat.add_comm]

theorem natBits_length_le {n X : ℕ} (h : n≤X) :
    n.bits.length≤Nat.clog 2 (X+1) := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have hp := Nat.le_pow_clog (by decide : 1<(2 : ℕ)) (X+1)
  omega

/-- Canonical word inputs for the literal proper-pair enumeration.
Word creation is an explicit, still unpriced interface before sorting. -/
def wordEvents (X : ℕ) : List WordPair :=
  (properPairs X).map fun v => (v.1.bits,v.2.bits)

/-- Every original factor tag is preserved, with its original occurrence. -/
theorem wordEvents_decoded (X : ℕ) : (wordEvents X).map decodePair=properPairs X := by
  simp only [wordEvents,List.map_map,Function.comp_def,decodePair,bitValue_natBits]
  exact List.map_id _

theorem wordEvents_values (X : ℕ) : (wordEvents X).map pairValue=eventValues X := by
  simp only [wordEvents,List.map_map,Function.comp_def,pairValue,bitValue_natBits,eventValues]

theorem wordEvents_length (X : ℕ) : (wordEvents X).length=(properPairs X).length := by
  simp only [wordEvents,List.length_map]

/-- The actual public event words meet a logarithmic physical-width bound;
this premise is discharged for the literal source, not supplied as advice. -/
theorem wordEvents_bounded (X : ℕ) : BoundedWords (Nat.clog 2 (X+1)) (wordEvents X) := by
  intro v hv
  obtain ⟨tag,ht,rfl⟩ := List.mem_map.mp hv
  obtain ⟨hd,hk,hprod⟩ := properPairs_mem_iff.mp ht
  have hdX := (Nat.le_mul_of_pos_right _ (by omega : 0<tag.2)).trans hprod
  have hkX := (Nat.le_mul_of_pos_left _ (by omega : 0<tag.1)).trans hprod
  exact ⟨natBits_length_le hdX,natBits_length_le hkX⟩

/-- The sorted scalar projection is downstream of retained word witnesses. -/
def sortedWordValues (X : ℕ) : List ℕ := (sortWords (wordEvents X)).rows.map pairValue

theorem sortedWordValues_perm (X : ℕ) : (sortedWordValues X).Perm (eventValues X) := by
  have hp := (sortWords_perm (wordEvents X)).map pairValue
  rw [wordEvents_values] at hp
  exact hp

theorem sortedWordValues_ordered (X : ℕ) : (sortedWordValues X).Pairwise (·≤·) :=
  List.pairwise_map.mpr (sortWords_ordered (wordEvents X))

/-- Despite any tie order between different factor witnesses, the entire
sorted product list equals the preceding sieve list, with multiplicities. -/
theorem sortedWordValues_eq (X : ℕ) : sortedWordValues X=sortedValues X :=
  ((sortedWordValues_perm X).trans (sortedValues_perm X).symm).eq_of_pairwise'
    (sortedWordValues_ordered X) (sortedValues_ordered X)

/-- The logarithmic sort depth is bounded at the actual public event count. -/
theorem properPairs_clog_length_le (X : ℕ) :
    Nat.clog 2 (properPairs X).length≤3*Nat.clog 2 (X+1) := by
  have he := properPairs_length_le X
  have hl := Nat.add_le_add_right (Nat.log2_le_self X) 1
  have hm := Nat.mul_le_mul (Nat.le_succ X) (Nat.pow_le_pow_left hl 2)
  have hb : (properPairs X).length≤(X+1)^3 :=
    he.trans (by simpa only [pow_succ,pow_zero,Nat.mul_one,Nat.mul_comm] using hm)
  have hp := Nat.le_pow_clog (by decide : 1<(2 : ℕ)) (X+1)
  have hcube : (X+1)^3≤2^(3*Nat.clog 2 (X+1)) := by
    calc
      _ ≤ (2^Nat.clog 2 (X+1))^3 := Nat.pow_le_pow_left hp 3
      _ = _ := by rw [←pow_mul]; congr 1; omega
  exact Nat.clog_le_of_le_pow (hb.trans hcube)

/-- A uniform clock for sorting every literal proper-product witness.
Input word creation and the downstream prime-gap scan are separate costs. -/
theorem wordEvents_sort_bounds (X : ℕ) :
    (sortWords (wordEvents X)).clock≤100*(Nat.clog 2 (X+1)+1)^2*
      (X*(Nat.log2 X+1)^2)*(3*Nat.clog 2 (X+1)+1)+1 ∧
    (sortWords (wordEvents X)).comparisons≤
      3*(X*(Nat.log2 X+1)^2)*Nat.clog 2 (X+1) := by
  have hc := sortWords_bounds (wordEvents_bounded X)
  simp only [wordEvents_length] at hc
  have he := properPairs_length_le X
  have hl := properPairs_clog_length_le X
  constructor
  · have hm := Nat.mul_le_mul he (Nat.add_le_add_right hl 1)
    have hs := Nat.mul_le_mul_left (100*(Nat.clog 2 (X+1)+1)^2) hm
    have hs' : 100*(Nat.clog 2 (X+1)+1)^2*(properPairs X).length*
        (Nat.clog 2 (properPairs X).length+1)+1≤
        100*(Nat.clog 2 (X+1)+1)^2*(X*(Nat.log2 X+1)^2)*
        (3*Nat.clog 2 (X+1)+1)+1 := by
      simpa only [Nat.mul_assoc] using Nat.add_le_add_right hs 1
    exact hc.1.trans hs'
  · have hm := Nat.mul_le_mul he hl
    calc
      _ ≤ (X*(Nat.log2 X+1)^2)*(3*Nat.clog 2 (X+1)) := hc.2.trans hm
      _ = _ := by ring

/-- Scalar specification of acquisition after the priced word-sort stage.
The scalar projection and first-gap scan are not yet a Boolean data path. -/
def wordSortSievePrime (B : ℕ) : ℕ :=
  (firstGap (max 2 B) (2*max 1 B+1-max 2 B)
    (sortedWordValues (2*max 1 B))).getD 2

theorem wordSortSievePrime_eq (B : ℕ) : wordSortSievePrime B=publicSievePrime B := by
  simp only [wordSortSievePrime,sortedWordValues_eq,publicSievePrime]

/-- N-only selector using the word-sorted public witness carrier. -/
def wordSortedRowModulus (N : ℕ) : ℕ :=
  wordSortSievePrime (max 1 (SemiprimeLehmanCoverage.sixthWidth N))

theorem wordSortedRowModulus_eq (N : ℕ) :
    wordSortedRowModulus N=SemiprimeEuclidRowBudget.publicRowModulus N := by
  rw [wordSortedRowModulus,wordSortSievePrime_eq]
  exact sievedRowModulus_eq N

/-- Every row, center and occurrence is unchanged by the word-sort stage. -/
theorem wordSorted_publicPackets_eq (N : ℕ) :
    SemiprimeEuclidRowFamily.publicPackets N (wordSortedRowModulus N)=
      SemiprimeEuclidRowFamily.publicPackets N (SemiprimeEuclidRowBudget.publicRowModulus N) := by
  rw [wordSortedRowModulus_eq]

/-- Transport the complete shared companion recovery through word sorting. -/
noncomputable def recoverWordSortedCompanions (N : ℕ) : Option ℕ :=
  SemiprimeReflectedCompanions.recoverReflectedCompanions N (wordSortedRowModulus N)

theorem recoverWordSortedCompanions_eq (N : ℕ) : recoverWordSortedCompanions N=
    SemiprimeReflectedCompanions.recoverReflectedCompanions N
      (SemiprimeEuclidRowBudget.publicRowModulus N) := by
  rw [recoverWordSortedCompanions,wordSortedRowModulus_eq]

theorem recoverWordSortedCompanions_sound {N d : ℕ}
    (h : recoverWordSortedCompanions N=some d) : SemiprimeGroupSelection.ProperDivisor N d :=
  SemiprimeReflectedCompanions.recoverReflectedCompanions_sound h

end RiemannGaussian.SemiprimeBitProductSort
