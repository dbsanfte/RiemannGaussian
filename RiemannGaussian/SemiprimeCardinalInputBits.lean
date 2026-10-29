/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeEncodedRowSelection
import RiemannGaussian.SemiprimePaidFiniteEnumerationLists
import RiemannGaussian.SemiprimeHermiteArrayHeight

/-! # Cardinal slope words acquired from original finite node indices
No rational slope is synthesized and then encoded. Actual point digits feed
signed Boolean subtraction and word inversion. Nat index/digit extraction is
an explicitly counted scalar boundary; subtraction/copying are physical loops.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace RiemannGaussian.SemiprimeCardinalInputBits
open scoped BigOperators
open SemiprimeRationalBits SemiprimeBitArithmetic SemiprimeBitIndexClipping
open SemiprimeHermiteArrayHeight SemiprimeJetArrayHeight
open SemiprimeMaterializedSourceUniversal

/-- Acquired positive interpolation point and its digit-stage ledger. -/
structure IndexRun where
  /-- Signed physical index, always nonnegative. -/
  word : SignedWord
  /-- Actual scalar digit/cell construction work. -/
  clock : ℕ

/-- Construct t+1 directly from actual scalar index digits, not from a rational oracle. -/
def index (Q : ℕ) (t : Fin Q) : IndexRun :=
  let out := SemiprimeEncodedRowSelection.digits (Q+1) (t.val+1)
  ⟨⟨false,out.bits⟩,out.work+2⟩

/-- Exact original point represented by the acquired word. -/
theorem index_value (Q : ℕ) (t : Fin Q) : (index Q t).word.value=(t.val+1 : ℕ) := by
  have ht : t.val+1<2^(Q+1) := (by omega : t.val+1  ≤  Q).trans_lt
    ((Nat.lt_succ_self Q).trans Nat.lt_two_pow_self)
  simp only [index,SignedWord.value,Bool.false_eq_true,ite_false,
    SemiprimeEncodedRowSelection.digits_value (Q+1) (t.val+1) ht]

/-- Exact physical point word shape. -/
theorem index_length (Q : ℕ) (t : Fin Q) : (index Q t).word.magnitude.length=Q+1 :=
  SemiprimeEncodedRowSelection.digits_length _ _

/-- Every scalar digit stage and point-record operation is retained. -/
theorem index_clock (Q : ℕ) (t : Fin Q) : (index Q t).clock=4*(Q+1)+3 := by
  simp only [index,SemiprimeEncodedRowSelection.digits_work]

/-- Build one unique slope from the cached target point and the original source node. -/
def slope (Q : ℕ) (target : SignedWord) (t s : Fin Q) : RationalReport :=
  if s=t then ⟨zeroWord,1⟩ else
    let point := index Q s
    let delta := subSignedBits target point.word
    let inverse := rawInvBits ⟨delta.word,[true]⟩
    ⟨inverse.word,point.clock+delta.clock+inverse.clock+3⟩

/-- The actual Boolean subtraction has the original integer point difference. -/
theorem difference_value (Q : ℕ) (t s : Fin Q) :
    (subSignedBits (index Q t).word (index Q s).word).word.value=
      ((t.val+1 : ℕ):ℤ)-((s.val+1 : ℕ):ℤ) := by
  rw [subSignedBits_value,index_value,index_value]

/-- Acquired slopes have exactly the normalized cardinal coefficients. -/
theorem slope_value (Q : ℕ) (t s : Fin Q) :
    (slope Q (index Q t).word t s).word.value=
      if s.val=t.val then 0 else (((t.val:ℚ)+1)-((s.val:ℚ)+1))⁻¹ := by
  by_cases h : s=t
  · subst s
    simp [slope,zeroWord,RationalWord.value,bitValue,SignedWord.value,bitNat]
  · have hv : s.val≠t.val := by intro he; exact h (Fin.ext he)
    simp only [slope,h,ite_false,hv]
    rw [rawInvBits_value]
    congr 1
    change ((subSignedBits (index Q t).word (index Q s).word).word.value:ℚ)/1=_
    rw [div_one,difference_value]
    push_cast
    ring

/-- The self slope is literal zero; every other acquired denominator is nonzero. -/
theorem slope_valid (Q : ℕ) (t s : Fin Q) : (slope Q (index Q t).word t s).word.Valid := by
  by_cases h : s=t
  · subst s
    simp only [slope,ite_true,zeroWord,RationalWord.Valid,bitValue,bitNat]
    decide
  · have hn : (subSignedBits (index Q t).word (index Q s).word).word.value≠0 := by
      rw [difference_value]
      intro he
      apply h
      apply Fin.ext
      omega
    have hm : 0<bitValue (subSignedBits (index Q t).word (index Q s).word).word.magnitude := by
      by_contra hp
      have hz : bitValue (subSignedBits (index Q t).word (index Q s).word).word.magnitude=0 := by omega
      apply hn
      simp [SignedWord.value,hz]
    simpa only [slope,h,ite_false,rawInvBits,RationalWord.Valid] using hm

/-- The physical signed difference grows by at most one bit. -/
theorem slope_width (Q : ℕ) (t s : Fin Q) : Width (slope Q (index Q t).word t s).word (Q+2) := by
  by_cases h : s=t
  · subst s
    simp [slope,zeroWord,Width]
  · have hw := (subSignedBits_cost_width
      (left:=(index Q t).word) (right:=(index Q s).word)
      (le_of_eq (index_length Q t)) (le_of_eq (index_length Q s))).2
    constructor
    · simpa only [slope,h,ite_false,rawInvBits] using (show [true].length  ≤  Q+2 by simp)
    · simpa only [slope,h,ite_false,rawInvBits] using hw

/-- Explicit polynomial unique-slope acquisition budget. -/
def slopeBudget (Q : ℕ) : ℕ := 4*(Q+1)+3+41*(Q+2)+7

/-- The actual primitive subtraction and word inversion reports are paid. -/
theorem slope_clock (Q : ℕ) (t s : Fin Q) :
    (slope Q (index Q t).word t s).clock  ≤  slopeBudget Q := by
  have hw := (subSignedBits_cost_width
    (left:=(index Q t).word) (right:=(index Q s).word)
    (le_of_eq (index_length Q t)) (le_of_eq (index_length Q s))).1
  unfold slope slopeBudget
  split_ifs
  · dsimp only
    omega
  · dsimp only [rawInvBits]
    rw [index_clock]
    omega

/-- A real Boolean-list copy and its retained cell clock. -/
def copyBits : List Bool → Run (List Bool)
  | [] => ⟨[],1⟩
  | b::bs => let tail := copyBits bs; ⟨b::tail.value,tail.work+3⟩

/-- Copying does not interpret or normalize a magnitude. -/
theorem copyBits_value (xs : List Bool) : (copyBits xs).value=xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [copyBits,ih]

/-- Every copied Boolean cell is paid. -/
theorem copyBits_clock (xs : List Bool) : (copyBits xs).work=3*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [copyBits,ih,List.length_cons]; omega

/-- Physical copies of numerator/denominator payloads and a sign cell. -/
def copyWord (w : RationalWord) : RationalReport :=
  let n := copyBits w.numerator.magnitude
  let d := copyBits w.denominator
  ⟨⟨⟨w.numerator.negative,n.value⟩,d.value⟩,n.work+d.work+3⟩

/-- Exact literal physical-word copy, with no scalar rational extraction. -/
theorem copyWord_value (w : RationalWord) : (copyWord w).word=w := by
  cases w with
  | mk n d => cases n; simp only [copyWord,copyBits_value]

/-- Cached slope repeats pay each copied numerator/denominator/sign. -/
theorem copyWord_clock (w : RationalWord) (W : ℕ) (hw : Width w W) :
    (copyWord w).clock  ≤  6*W+5 := by
  simp only [copyWord,copyBits_clock]
  rcases hw with ⟨hn,hd⟩
  omega

/-- Literal repeated physical copies of one cached unique slope. -/
def repeatCopy : ℕ → RationalWord → Run (List RationalWord)
  | 0,_ => ⟨[],1⟩
  | J+1,w => let first := copyWord w; let tail := repeatCopy J w
    ⟨first.word::tail.value,first.clock+tail.work+2⟩

/-- Repetition has exactly the original cardinal factor order. -/
theorem repeatCopy_value (J : ℕ) (w : RationalWord) : (repeatCopy J w).value=List.replicate J w := by
  induction J with
  | zero => rfl
  | succ J ih => simp only [repeatCopy,copyWord_value,ih,List.replicate_succ]

/-- Every repeated cell/payload is acquired, not a shared rational oracle list. -/
theorem repeatCopy_clock (J : ℕ) (w : RationalWord) (W : ℕ) (hw : Width w W) :
    (repeatCopy J w).work  ≤  J*(6*W+7)+1 := by
  induction J with
  | zero => simp [repeatCopy]
  | succ J ih =>
    have h := copyWord_clock w W hw
    simp only [repeatCopy]
    nlinarith

/-- Cardinal slope list, negative evaluation point and their complete acquired report. -/
structure Inputs where
  /-- Repeated slopes in exact original source order. -/
  slopes : List RationalWord
  /-- Physical word for -(t+1). -/
  x : RationalWord
  /-- Scalar index/digit, physical arithmetic/copy and finite traversal work. -/
  clock : ℕ

/-- Cache one target index, acquire each unique slope, then copy its J repetitions. -/
def acquire (Q J : ℕ) (t : Fin Q) : Inputs :=
  let target := index Q t
  let indices := SemiprimePaidFiniteEnumerationLists.fin Q
  let out := collect (fun s =>
    let unique := slope Q target.word t s
    let repeats := repeatCopy J unique.word
    (⟨repeats.value,unique.clock+repeats.work+1⟩ : Run (List RationalWord))) indices.value
  let slopes := out.value.flatMap id
  ⟨slopes,⟨negateWord target.word,[true]⟩,
    target.clock+indices.work+out.work+slopes.length+out.value.length+7⟩

/-- Explicit Fin-node order agrees with the original range order. -/
theorem finRange_values (Q : ℕ) : (List.finRange Q).map Fin.val=List.range Q := by
  induction Q with
  | zero => rfl
  | succ Q ih =>
    rw [List.finRange_succ,List.map_cons,List.map_map,List.range_succ_eq_map]
    change 0::(List.finRange Q).map (fun i => i.val+1)=0::(List.range Q).map Nat.succ
    rw [← ih,List.map_map]
    rfl

/-- Cached repetitions are in their literal original node-major order. -/
theorem acquire_slopes (Q J : ℕ) (t : Fin Q) :
    (acquire Q J t).slopes=(List.finRange Q).flatMap
      (fun s => List.replicate J (slope Q (index Q t).word t s).word) := by
  simp only [acquire,collect_value,SemiprimePaidFiniteEnumerationLists.fin_value,
    repeatCopy_value,List.flatMap_map,id_eq]

/-- Exact normalized-cardinal slope list, including its J self-node zeros. -/
theorem slopes_value (Q J : ℕ) (t : Fin Q) :
    ((acquire Q J t).slopes.map RationalWord.value)=cardinalSlopes Q J t.val := by
  rw [acquire_slopes,List.map_flatMap]
  simp only [List.map_replicate,slope_value]
  unfold cardinalSlopes
  have h := congrArg (List.flatMap (fun s : ℕ => List.replicate J
    (if s=t.val then (0:ℚ) else (((t.val:ℚ)+1)-((s:ℚ)+1))⁻¹))) (finRange_values Q)
  simpa only [List.flatMap_map] using h

/-- Exact original coefficient-list length, not merely an upper bound. -/
theorem slopes_length (Q J : ℕ) (t : Fin Q) : (acquire Q J t).slopes.length=Q*J := by
  have h := congrArg List.length (slopes_value Q J t)
  simpa only [List.length_map,cardinalSlopes_length] using h

/-- All acquired slope words have positive physical denominators. -/
theorem slopes_valid (Q J : ℕ) (t : Fin Q) (w : RationalWord)
    (hw : w∈(acquire Q J t).slopes) : w.Valid := by
  rw [acquire_slopes] at hw
  obtain ⟨s,_,hs⟩ := List.mem_flatMap.mp hw
  obtain ⟨_,he⟩ := List.mem_replicate.mp hs
  subst w
  exact slope_valid Q t s

/-- The original acquisition width is linear in the finite node count. -/
theorem slopes_bounded (Q J : ℕ) (t : Fin Q) (w : RationalWord)
    (hw : w∈(acquire Q J t).slopes) : Width w (Q+2) := by
  rw [acquire_slopes] at hw
  obtain ⟨s,_,hs⟩ := List.mem_flatMap.mp hw
  obtain ⟨_,he⟩ := List.mem_replicate.mp hs
  subst w
  exact slope_width Q t s

/-- The actual decoded slopes have the established common factorial representation. -/
theorem slopes_representation (Q J : ℕ) (t : Fin Q) (w : RationalWord)
    (hw : w∈(acquire Q J t).slopes) : Representation w.value Q.factorial Q.factorial := by
  apply cardinalSlopes_representation Q J t w.value
  rw [← slopes_value]
  exact List.mem_map.mpr ⟨w,hw,rfl⟩

/-- The original negative evaluation point, used only to state semantics. -/
def xInt {Q : ℕ} (t : Fin Q) : ℤ := -((t.val+1:ℕ):ℤ)

/-- The negative evaluation point is obtained by the actual cached-word sign NOT. -/
theorem x_value (Q J : ℕ) (t : Fin Q) : (acquire Q J t).x.value=(xInt t:ℚ) := by
  change ((negateWord (index Q t).word).value:ℚ)/1=(xInt t:ℚ)
  rw [div_one,negateWord_value,index_value]
  rfl

/-- Literal denominator one gives validity without a fit promise. -/
theorem x_valid (Q J : ℕ) (t : Fin Q) : (acquire Q J t).x.Valid := by
  change 0<1
  decide

/-- The actual negative point has the same linear acquisition width. -/
theorem x_bounded (Q J : ℕ) (t : Fin Q) : Width (acquire Q J t).x (Q+2) := by
  constructor
  · change (index Q t).word.magnitude.length ≤ Q+2
    rw [index_length]
    omega
  · change 1 ≤ Q+2
    omega

/-- Its integer magnitude has the original node bound Q. -/
theorem x_natAbs_le (Q : ℕ) (t : Fin Q) : (xInt t).natAbs ≤ Q := by
  simp only [xInt,Int.natAbs_neg,Int.natAbs_natCast]
  omega

/-- Closed paid scalar-digit / physical-subtract-copy / finite-list budget. -/
def budget (Q J : ℕ) : ℕ :=
  4*(Q+1)+3+3*(Q+1)^2+Q*(slopeBudget Q+J*(6*(Q+2)+7)+4)+1+Q*J+Q+7

/-- Every unique slope, every copied repetition and all finite traversal work are retained. -/
theorem acquire_clock (Q J : ℕ) (t : Fin Q) : (acquire Q J t).clock ≤ budget Q J := by
  have h := collect_work (fun s : Fin Q =>
    let unique := slope Q (index Q t).word t s
    let repeats := repeatCopy J unique.word
    (⟨repeats.value,unique.clock+repeats.work+1⟩ : Run (List RationalWord)))
    (SemiprimePaidFiniteEnumerationLists.fin Q).value
    (slopeBudget Q+J*(6*(Q+2)+7)+2) (by
      intro s _
      have hu := slope_clock Q t s
      have hr := repeatCopy_clock J (slope Q (index Q t).word t s).word (Q+2) (slope_width Q t s)
      dsimp only
      omega)
  rw [SemiprimePaidFiniteEnumerationLists.fin_value,List.length_finRange] at h
  have hf := SemiprimePaidFiniteEnumerationLists.fin_work Q
  have hl := slopes_length Q J t
  dsimp only [acquire] at hl
  unfold acquire budget
  dsimp only
  rw [hl]
  simp only [collect_value,List.length_map,SemiprimePaidFiniteEnumerationLists.fin_value,List.length_finRange]
  rw [index_clock]
  dsimp only at h
  ring_nf at h hf ⊢
  omega

end RiemannGaussian.SemiprimeCardinalInputBits
