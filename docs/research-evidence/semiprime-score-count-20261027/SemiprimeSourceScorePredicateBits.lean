/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceComparisonBits
import RiemannGaussian.SemiprimeSourceOffsetInputsCore
import RiemannGaussian.SemiprimeSourceScoreCounts

/-! # Physical original source collision predicates
Coordinates and keys are acquired from the ACTUAL original cached environment.
Every lookup scans physical keys, copies its selected coordinate row and reads
coordinates through physical Boolean addresses. Natural acquisition/control is
explicit; no terminal truth or rational score is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeSourceScorePredicateBits
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeRationalBits SemiprimeMaterializedWords
open SemiprimeMaterializedScoreEnvironment
open SemiprimeSourceOffsetInputsCore

/-- A physically cached row of denominator-one colour words. -/
abbrev Row := List RationalWord
/-- Physical key/row pairs preserve original scan order. -/
abbrev Pairs := List (RationalWord × Row)

/-- Physical rational equality, including arbitrary padding and signed zero. -/
def equalWord (x y : RationalWord) : Run Bool :=
  let forward := SemiprimeSourceComparisonBits.compare x y
  let backward := SemiprimeSourceComparisonBits.compare y x
  ⟨forward.order.le && backward.order.le,forward.clock+backward.clock+3⟩

/-- The actual double signed comparison is exact equality on valid input words. -/
theorem equalWord_correct (x y : RationalWord) (hx : x.Valid) (hy : y.Valid) :
    (equalWord x y).value=true ↔ x.value=y.value := by
  simp only [equalWord,Bool.and_eq_true,SemiprimeSourceComparisonBits.compare_correct x y hx hy,
    SemiprimeSourceComparisonBits.compare_correct y x hy hx]
  constructor
  · rintro ⟨hxy,hyx⟩; exact le_antisymm hxy hyx
  · intro h; rw [h]; exact ⟨le_rfl,le_rfl⟩

/-- Actual full coordinate-row copy, not a free returned list. -/
def copyRow (row : Row) : Run Row :=
  let out := SemiprimeSourceMemoryBits.copyMemory row
  ⟨out.words,out.clock+2⟩

/-- Row copies preserve every original bit and padding. -/
theorem copyRow_value (row : Row) : (copyRow row).value=row :=
  SemiprimeSourceMemoryBits.copyMemory_words row

/-- Materialize original finite colour cells by actual natural-bit acquisition. -/
def acquireCoordinates {r : ℕ} : List (Fin r) → Run Row
  | [] => ⟨[],1⟩
  | c::cs =>
    let head := encodeNat c.val
    let tail := acquireCoordinates cs
    ⟨head.word::tail.value,head.clock+tail.work+3⟩

/-- Every original cached coordinate is read once into the acquired row. -/
def acquireWord {r Q : ℕ} (w : CachedWord r Q) : Run Row :=
  let out := acquireCoordinates w.data.toList
  ⟨out.value,out.work+2*w.data.size+2⟩

/-- Acquired colour values are exactly the ORIGINAL array's values. -/
theorem acquireCoordinates_values {r : ℕ} (cs : List (Fin r)) :
    (acquireCoordinates cs).value.map RationalWord.value=cs.map (fun c => (c.val:ℚ)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [acquireCoordinates,List.map_cons,(encodeNat_spec c.val).1,ih]

/-- All acquired colour words are valid physical rationals. -/
theorem acquireCoordinates_valid {r : ℕ} (cs : List (Fin r)) :
    ∀ w∈(acquireCoordinates cs).value,w.Valid := by
  induction cs with
  | nil => simp [acquireCoordinates]
  | cons c cs ih =>
    intro w hw
    simp only [acquireCoordinates,List.mem_cons] at hw
    rcases hw with rfl|hw
    · exact (encodeNat_spec c.val).2.1
    · exact ih w hw

/-- Acquired row values follow the actual cached source array. -/
theorem acquireWord_values {r Q : ℕ} (w : CachedWord r Q) :
    (acquireWord w).value.map RationalWord.value=w.data.toList.map (fun c => (c.val:ℚ)) :=
  acquireCoordinates_values _

/-- Acquired row validity has no source truth premise. -/
theorem acquireWord_valid {r Q : ℕ} (w : CachedWord r Q) :
    ∀ x∈(acquireWord w).value,x.Valid := acquireCoordinates_valid _

/-- Acquire literal reverse-prefix IDs from the actual original fixed-list suffixes. -/
def acquireFixed {r Q : ℕ} : List (CachedWord r Q) → Run Pairs
  | [] => ⟨[],1⟩
  | w::ws =>
    let tail := acquireFixed ws
    let key := encodeNat ws.length
    let row := acquireWord w
    ⟨(key.word,row.value)::tail.value,tail.work+key.clock+row.work+ws.length+5⟩

/-- Acquire newest-first override keys and cached rows without an encoded-key oracle. -/
def acquireOverrides {r Q : ℕ} : List (ℕ × CachedWord r Q) → Run Pairs
  | [] => ⟨[],1⟩
  | p::ps =>
    let key := encodeNat p.1
    let row := acquireWord p.2
    let tail := acquireOverrides ps
    ⟨(key.word,row.value)::tail.value,key.clock+row.work+tail.work+4⟩

/-- Actual physical default/fixed/override cache. -/
structure PhysicalEnvironment where
  /-- Acquired fallback row. -/
  default : Row
  /-- Acquired fixed rows keyed by original reverse-prefix IDs. -/
  fixed : Pairs
  /-- Acquired local overrides, newest first. -/
  overrides : Pairs

/-- Acquire the ACTUAL original cached environment once. -/
def acquireEnvironment {r Q : ℕ} (env : Environment r Q) : Run PhysicalEnvironment :=
  let default := acquireWord env.default
  let fixed := acquireFixed env.fixed
  let overrides := acquireOverrides env.overrides
  ⟨⟨default.value,fixed.value,overrides.value⟩,default.work+fixed.work+overrides.work+5⟩

/-- Sequential physical-key lookup, with a lazy executed fallback and full selected-row copy. -/
def scan (target : RationalWord) (fallback : Unit → Run Row) : Pairs → Run Row
  | [] => fallback ()
  | p::ps =>
    let key := SemiprimeSourceMemoryBits.copyWord p.1
    let same := equalWord key.word target
    if same.value then
      let out := copyRow p.2
      ⟨out.value,key.clock+same.work+out.work+4⟩
    else
      let rest := scan target fallback ps
      ⟨rest.value,key.clock+same.work+rest.work+4⟩

/-- Acquired original ID followed by newest-override, fixed and default scans. -/
def readEnvironment (env : PhysicalEnvironment) (i : ℕ) : Run Row :=
  let target := encodeNat i
  let out := scan target.word (fun _ => scan target.word (fun _ => copyRow env.default) env.fixed) env.overrides
  ⟨out.value,target.clock+out.work+3⟩

/-- A coordinate is acquired through a generated Boolean address and actual memory scan. -/
def coordinate (row : Row) (i : ℕ) : RationalReport :=
  let address := natBits i
  let out := SemiprimeSourceMemoryBits.readWord row address.bits
  ⟨out.word,address.clock+out.clock+3⟩

/-- Coordinate values have only the actual finite-memory lookup interpretation. -/
theorem coordinate_value (row : Row) (i : ℕ) :
    (coordinate row i).word.value=((row.map RationalWord.value)[i]?).getD 0 := by
  simp only [coordinate,SemiprimeSourceProgramBits.readWord_value,natBits_value]

/-- Coordinate access preserves validity, including the finite-memory default. -/
theorem coordinate_valid (row : Row) (i : ℕ) (h : ∀ w∈row,w.Valid) :
    (coordinate row i).word.Valid := SemiprimeSourceMemoryBits.readWord_valid row _ h

/-- Compare all coordinates through actual scans; no functional word-equality oracle. -/
def equalRows (left right : Row) : ℕ → Run Bool
  | 0 => ⟨true,1⟩
  | q+1 =>
    let rest := equalRows left right q
    let a := coordinate left q
    let b := coordinate right q
    let same := equalWord a.word b.word
    ⟨same.value && rest.value,rest.work+a.clock+b.clock+same.work+3⟩

/-- Physical terminal truth over acquired coordinate caches and original score IDs. -/
def terminal (env : PhysicalEnvironment) {Q : ℕ} (p : ScoreProgram Q) : Run Bool :=
  match p with
  | .incidence a b c d =>
    let wa := readEnvironment env a
    let wb := readEnvironment env b
    let wc := readEnvironment env c
    let wd := readEnvironment env d
    let heads := equalRows wa.value wc.value Q
    let slots := equalRows wb.value wd.value Q
    ⟨heads.value && slots.value,wa.work+wb.work+wc.work+wd.work+heads.work+slots.work+4⟩
  | .head t a b =>
    let wa := readEnvironment env a
    let wb := readEnvironment env b
    let ca := coordinate wa.value t.val
    let cb := coordinate wb.value t.val
    let same := equalWord ca.word cb.word
    ⟨same.value,wa.work+wb.work+ca.clock+cb.clock+same.work+5⟩

/-- Original-data entry point: acquire the actual cached environment then test it physically. -/
def terminal_original {r Q : ℕ} (env : Environment r Q) (p : ScoreProgram Q) : Run Bool :=
  let cache := acquireEnvironment env
  let out := terminal cache.value p
  ⟨out.value,cache.work+out.work+2⟩

/-- Fixed-cache scan exactly preserves the ORIGINAL reverse-prefix lookup. -/
theorem scan_fixed_original {r Q : ℕ} (default : CachedWord r Q)
    (fixed : List (CachedWord r Q)) (target : RationalWord) (i : ℕ)
    (ht : target.Valid) (hval : target.value=(i:ℚ)) :
    (scan target (fun _ => copyRow (acquireWord default).value) (acquireFixed fixed).value).value=
      (acquireWord (SemiprimeMaterializedWordSearch.readRun default fixed i).value).value := by
  induction fixed with
  | nil => simp only [acquireFixed,scan,copyRow_value,SemiprimeMaterializedWordSearch.readRun]
  | cons w ws ih =>
    have heq : (equalWord (encodeNat ws.length).word target).value=true ↔ i=ws.length := by
      rw [equalWord_correct _ _ (encodeNat_spec ws.length).2.1 ht,(encodeNat_spec ws.length).1,hval]
      norm_cast
      exact eq_comm
    by_cases h : i=ws.length
    · simp only [acquireFixed,scan,SemiprimeSourceMemoryBits.copyWord_word,heq.mpr h,
        ite_true,copyRow_value,SemiprimeMaterializedWordSearch.readRun,h]
    · have he : (equalWord (encodeNat ws.length).word target).value=false :=
        Bool.eq_false_of_not_eq_true (fun hh => h (heq.mp hh))
      simpa only [acquireFixed,scan,SemiprimeSourceMemoryBits.copyWord_word,he,Bool.false_eq_true,
        ite_false,SemiprimeMaterializedWordSearch.readRun,h] using ih

/-- Override lookup preserves actual newest-first precedence, with a lazy exact fallback. -/
theorem scan_overrides_original {r Q : ℕ} (default : CachedWord r Q)
    (fixed : List (CachedWord r Q)) (overrides : List (ℕ × CachedWord r Q))
    (target : RationalWord) (i : ℕ) (ht : target.Valid) (hval : target.value=(i:ℚ))
    (fallback : Unit → Run Row)
    (hf : (fallback ()).value=(acquireWord (SemiprimeMaterializedWordSearch.readRun default fixed i).value).value) :
    (scan target fallback (acquireOverrides overrides).value).value=
      (acquireWord (readOverrides default fixed i overrides).value).value := by
  induction overrides with
  | nil => exact hf
  | cons p ps ih =>
    have heq : (equalWord (encodeNat p.1).word target).value=true ↔ p.1=i := by
      rw [equalWord_correct _ _ (encodeNat_spec p.1).2.1 ht,(encodeNat_spec p.1).1,hval]
      norm_cast
    by_cases h : p.1=i
    · simp only [acquireOverrides,scan,SemiprimeSourceMemoryBits.copyWord_word]
      rw [ite_eq_left (heq.mpr h)]
      simp only [copyRow_value,readOverrides,h,ite_true]
    · have he : (equalWord (encodeNat p.1).word target).value=false :=
        Bool.eq_false_of_not_eq_true (fun hh => h (heq.mp hh))
      simpa only [acquireOverrides,scan,SemiprimeSourceMemoryBits.copyWord_word,he,Bool.false_eq_true,
        ite_false,readOverrides,h] using ih

/-- Actual acquired environment lookup returns exactly the original selected
cached word, including misses, duplicate override IDs and reverse-prefix cases. -/
theorem readEnvironment_original {r Q : ℕ} (env : Environment r Q) (i : ℕ) :
    (readEnvironment (acquireEnvironment env).value i).value=
      (acquireWord (readEnv env i).value).value := by
  exact scan_overrides_original env.default env.fixed env.overrides (encodeNat i).word i
    (encodeNat_spec i).2.1 (encodeNat_spec i).1 _
    (scan_fixed_original env.default env.fixed (encodeNat i).word i
      (encodeNat_spec i).2.1 (encodeNat_spec i).1)

/-- Actual acquired coordinates recover the ORIGINAL CachedWord array entry. -/
theorem coordinate_original {r Q : ℕ} (w : CachedWord r Q) (t : Fin Q) :
    (coordinate (acquireWord w).value t.val).word.value=((wordAt w t).val:ℚ) := by
  rw [coordinate_value,acquireWord_values]
  have hi : t.val<w.data.toList.length := by rw [Array.length_toList,w.size_eq];exact t.isLt
  simp only [List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some]
  simp only [Array.getElem_toList,wordAt]

/-- Row comparison has exact pointwise finite-memory semantics for every q. -/
theorem equalRows_correct (left right : Row) (q : ℕ)
    (hl : ∀ x∈left,x.Valid) (hr : ∀ x∈right,x.Valid) :
    (equalRows left right q).value=true ↔
      ∀ i<q,(coordinate left i).word.value=(coordinate right i).word.value := by
  induction q with
  | zero => simp [equalRows]
  | succ q ih =>
    simp only [equalRows,Bool.and_eq_true,equalWord_correct _ _
      (coordinate_valid left q hl) (coordinate_valid right q hr),ih]
    constructor
    · rintro ⟨hq,hprev⟩ i hi
      by_cases he : i=q
      · simpa only [he] using hq
      · exact hprev i (by omega)
    · intro h
      exact ⟨h q (by omega),fun i hi => h i (by omega)⟩

/-- Physical whole-word equality equals equality of the ORIGINAL cached words. -/
theorem equalRows_original {r Q : ℕ} (left right : CachedWord r Q) :
    (equalRows (acquireWord left).value (acquireWord right).value Q).value=
      decide (wordAt left=wordAt right) := by
  apply Bool.eq_iff_iff.mpr
  rw [equalRows_correct _ _ _ (acquireWord_valid left) (acquireWord_valid right)]
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    funext t
    have hh := h t.val t.isLt
    rw [coordinate_original left t,coordinate_original right t] at hh
    exact Fin.ext (by exact_mod_cast hh)
  · intro h i hi
    let t : Fin Q := ⟨i,hi⟩
    rw [coordinate_original left t,coordinate_original right t]
    exact congrArg (fun c : Fin r => (c.val:ℚ)) (congrFun h t)

/-- Original head-colour equality is obtained through two actual coordinate scans. -/
theorem equalColour_original {r Q : ℕ} (left right : CachedWord r Q) (t : Fin Q) :
    (equalWord (coordinate (acquireWord left).value t.val).word
      (coordinate (acquireWord right).value t.val).word).value=
      decide (wordAt left t=wordAt right t) := by
  apply Bool.eq_iff_iff.mpr
  rw [equalWord_correct _ _ (coordinate_valid _ _ (acquireWord_valid left))
    (coordinate_valid _ _ (acquireWord_valid right)),coordinate_original left t,coordinate_original right t]
  simp only [decide_eq_true_eq]
  constructor
  · intro h; exact Fin.ext (by exact_mod_cast h)
  · intro h; rw [h]

/-- Actual acquired physical terminal is EXACTLY the original native hit,
with no supplied truth, label function or coefficient answer. -/
theorem terminal_original_value {r Q : ℕ} (env : Environment r Q) (p : ScoreProgram Q) :
    (terminal_original env p).value=(SemiprimeSourceScoreCounts.hit p env).value := by
  cases p with
  | incidence a b c d =>
    simp only [terminal_original,terminal,readEnvironment_original,equalRows_original,
      SemiprimeSourceScoreCounts.hit,equalCoordinates_value]
  | head t a b =>
    simp only [terminal_original,terminal,readEnvironment_original,equalColour_original,
      SemiprimeSourceScoreCounts.hit]

end RiemannGaussian.SemiprimeSourceScorePredicateBits
