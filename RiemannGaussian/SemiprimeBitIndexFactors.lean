/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitIndexRoots

/-!
# Boolean factor reading on original mixed-index coefficient words

Original root words are tested against the canonical decoded residue with
Boolean borrow arithmetic and the existing charged GCD circuit. The scan
keeps original source occurrences and stops on its first proper factor.
Source enumeration/serialization, acquisition and the whole machine/memory
certificate remain separate costs.
-/

namespace RiemannGaussian.SemiprimeBitIndexFactors

open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitGcd
open SemiprimeBitIndexRoots SemiprimeIndexReader SemiprimeGroupSelection

/-- Original first difference, actual optional wrap and corrected residue. -/
structure DifferenceWordReport where
  /-- Actual first subtraction and its retained underflow diagnostic. -/
  first : SubReport
  /-- Actual modulus addition and second subtraction, only after underflow. -/
  wrap : Option (BitReport×SubReport)
  /-- Computed canonical difference when both original words are canonical. -/
  bits : List Bool
  /-- Every executed Boolean arithmetic primitive and wrap branch. -/
  clock : ℕ
  /-- Every created bit-list cell, including the discarded first difference. -/
  writes : ℕ

/-- Subtract the actual original index. If the first borrow underflows,
add the public modulus and subtract again. All failed first-work is paid;
no natural value, quotient or modular oracle computes the residue word. -/
def differenceBits (modulus decoded index : List Bool) : DifferenceWordReport :=
  let first := subBits decoded index false
  if first.borrow=true then
    let sum := addBits decoded modulus false
    let corrected := subBits sum.bits index false
    ⟨first,some (sum,corrected),corrected.result.bits,
      bitCost first.result+bitCost sum+bitCost corrected.result+4,
      first.result.writes+sum.writes+corrected.result.writes⟩
  else
    ⟨first,none,first.result.bits,bitCost first.result+4,first.result.writes⟩

/-- The original native modular difference has its explicit short-index
form; subtraction remains nontruncating in the wrapped branch. -/
theorem modularDifference_short {N s i : ℕ} (hs : s<N) (hi : i<N) :
    modularDifference N s i=if i≤s then s-i else s+N-i := by
  unfold modularDifference
  rw [Nat.mod_eq_of_lt hs,Nat.mod_eq_of_lt hi]
  by_cases h : i≤s
  · have he : s+N-i=N+(s-i) := by omega
    have hlt : s-i<N := by omega
    simp [h,he,Nat.mod_eq_of_lt hlt]
  · have hlt : s+N-i<N := by omega
    rw [if_neg h,Nat.mod_eq_of_lt hlt]

/-- Canonical decoded and original short index words give the exact
original modular difference, including zero and the wrapped orientation. -/
theorem differenceBits_exact {modulus decoded index : List Bool}
    (hs : bitValue decoded<bitValue modulus) (hi : bitValue index<bitValue modulus) :
    bitValue (differenceBits modulus decoded index).bits=
      modularDifference (bitValue modulus) (bitValue decoded) (bitValue index) := by
  have hcompare := subBits_borrow_iff decoded index false
  simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] at hcompare
  rw [modularDifference_short hs hi]
  by_cases hb : (subBits decoded index false).borrow=true
  · have hlt := hcompare.mp hb
    have hsum := addBits_correct decoded modulus false
    simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] at hsum
    have hbound : bitValue index≤bitValue (addBits decoded modulus false).bits := by
      rw [hsum]
      omega
    have hc := subBits_difference ((subBits_borrow_false _ _).mpr hbound)
    rw [hsum] at hc
    simp only [differenceBits,if_pos hb,if_neg (by omega : ¬bitValue index≤bitValue decoded),hc]
  · have hfalse : (subBits decoded index false).borrow=false := by
      cases he : (subBits decoded index false).borrow with
      | false => rfl
      | true => exact False.elim (hb he)
    have hge := (subBits_borrow_false decoded index).mp hfalse
    have hd := subBits_difference hfalse
    simp only [differenceBits,if_neg hb,if_pos hge,hd]

/-- All created difference/wrap cells appear in the complete primitive clock. -/
theorem differenceBits_writes_le_clock (modulus decoded index : List Bool) :
    (differenceBits modulus decoded index).writes≤
      (differenceBits modulus decoded index).clock := by
  unfold differenceBits
  dsimp only
  split <;> dsimp only [bitCost] <;> omega

/-- Physical corrected words have at most one additional carry cell,
including noncanonical or invalid input words. -/
theorem differenceBits_width {W : ℕ} {modulus decoded index : List Bool}
    (hm : modulus.length≤W) (hs : decoded.length≤W) (hi : index.length≤W) :
    (differenceBits modulus decoded index).bits.length≤W+1 := by
  have hsum := (bounded_addBits hs hm false).2
  have hfirst := (subBits_counts decoded index false).2.2.2.2
  have hsecond := (subBits_counts (addBits decoded modulus false).bits index false).2.2.2.2
  unfold differenceBits
  dsimp only
  split <;> dsimp only <;> omega

/-- Corrected subtraction costs linear physical-word work, including the
first subtraction when it underflows and all actual wrap arithmetic. -/
theorem differenceBits_cost {W : ℕ} {modulus decoded index : List Bool}
    (hm : modulus.length≤W) (hs : decoded.length≤W) (hi : index.length≤W) :
    (differenceBits modulus decoded index).clock≤40*(W+1) := by
  have hfirst := subBits_cost decoded index false
  have hmax : max decoded.length index.length≤W := max_le hs hi
  have hsum := bounded_addBits hs hm false
  have hsecond := subBits_cost (addBits decoded modulus false).bits index false
  have hmaxSecond : max (addBits decoded modulus false).bits.length index.length≤W+1 :=
    max_le hsum.2 (hi.trans (Nat.le_succ _))
  unfold differenceBits
  dsimp only
  split <;> dsimp only <;> omega

/-- Original tested index, computed difference and actual checked GCD word. -/
structure IndexTestWordReport where
  /-- Original root word, preserving its ordered source orientation. -/
  index : List Bool
  /-- Actual unwrapped/wrapped residue computation and diagnostics. -/
  difference : DifferenceWordReport
  /-- Actual Boolean GCD and proper-divisor comparisons. -/
  checked : CheckedBitsReport
  /-- A proper factor word only after both actual GCD checks. -/
  factor : Option (List Bool)
  /-- Full difference/GCD/check clock and retained source references. -/
  clock : ℕ

/-- Execute one original root test without a natural GCD, residue or
properness oracle. Saturated and unit GCDs are retained but not returned. -/
def testIndexBits (modulus decoded index : List Bool) : IndexTestWordReport :=
  let difference := differenceBits modulus decoded index
  let checked := checkedSignalBits modulus difference.bits
  ⟨index,difference,checked,checked.factor,difference.clock+checked.clock+2⟩

/-- The original tested word is retained unchanged on every branch. -/
theorem testIndexBits_source (modulus decoded index : List Bool) :
    (testIndexBits modulus decoded index).index=index := rfl

/-- One Boolean root test preserves the original native factor outcome
whenever its decoded residue and original index are canonical words. -/
theorem testIndexBits_exact {modulus decoded index : List Bool}
    (hs : bitValue decoded<bitValue modulus) (hi : bitValue index<bitValue modulus) :
    (testIndexBits modulus decoded index).factor.map bitValue=
      (testIndex (bitValue modulus) (bitValue decoded) (bitValue index)).factor := by
  rw [testIndexBits,checkedSignalBits_exact,differenceBits_exact hs hi,testIndex_factor]

/-- Every returned factor word is proper on arbitrary supplied words,
independently of canonicality and of how the original roots were acquired. -/
theorem testIndexBits_sound {modulus decoded index divisor : List Bool}
    (h : (testIndexBits modulus decoded index).factor=some divisor) :
    ProperDivisor (bitValue modulus) (bitValue divisor) := by
  exact checkedSignalBits_sound h

/-- A complete Boolean root test has cubic charged scalar bit work,
including Euclid fuel, corrected subtraction and both properness comparisons. -/
theorem testIndexBits_cost {W : ℕ} {modulus decoded index : List Bool}
    (hm : modulus.length≤W) (hs : decoded.length≤W) (hi : index.length≤W) :
    (testIndexBits modulus decoded index).clock≤5000*(W+1)^3 := by
  have hd := differenceBits_cost hm hs hi
  have hw := differenceBits_width hm hs hi
  have hg := checkedSignalBits_cost (hm.trans (Nat.le_succ _)) hw
  have hp : W+1≤(W+1)^3 := Nat.le_self_pow (by decide : 3≠0) (W+1)
  have htwice : W+2≤2*(W+1) := by omega
  have hc := Nat.pow_le_pow_left htwice 3
  dsimp only [testIndexBits]
  nlinarith

/-- Original rich word-root report and the actual first-success root tests. -/
structure PointFactorWordReport where
  /-- Original coefficient words, root diagnostics and checked root pair. -/
  rootReader : RootWordReport
  /-- Exactly the one or two executed GCD checks, or none on root rejection. -/
  checks : List IndexTestWordReport
  /-- First actual proper factor word returned from this coefficient point. -/
  factor : Option (List Bool)
  /-- Complete root/test clock and executed option/list decisions. -/
  clock : ℕ

/-- Reject roots without a GCD call; otherwise test the descending root
first and stop on a proper factor, retaining both roots and all failed work. -/
def readCoefficientFactorBits (modulus decoded bound a b : List Bool) : PointFactorWordReport :=
  let rootReader := readIntegerRootsBits bound a b
  match rootReader.roots with
  | none => ⟨rootReader,[],none,rootReader.clock+2⟩
  | some (i,j) =>
    let first := testIndexBits modulus decoded i
    match first.factor with
    | some divisor => ⟨rootReader,[first],some divisor,rootReader.clock+first.clock+4⟩
    | none =>
      let second := testIndexBits modulus decoded j
      ⟨rootReader,[first,second],second.factor,rootReader.clock+first.clock+second.clock+5⟩

/-- Every returned point-reader factor word is proper on arbitrary input. -/
theorem readCoefficientFactorBits_sound {modulus decoded bound a b divisor : List Bool}
    (h : (readCoefficientFactorBits modulus decoded bound a b).factor=some divisor) :
    ProperDivisor (bitValue modulus) (bitValue divisor) := by
  unfold readCoefficientFactorBits at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · rename_i d hd
      dsimp only at h
      cases h
      exact testIndexBits_sound hd
    · exact testIndexBits_sound h

/-- The original coefficient/root report is retained exactly on every path. -/
theorem readCoefficientFactorBits_rootReader (modulus decoded bound a b : List Bool) :
    (readCoefficientFactorBits modulus decoded bound a b).rootReader=
      readIntegerRootsBits bound a b := by
  unfold readCoefficientFactorBits
  dsimp only
  split
  · rfl
  · split <;> rfl

/-- The actual point reader executes at most two checked Boolean GCD calls. -/
theorem readCoefficientFactorBits_gcd_bound (modulus decoded bound a b : List Bool) :
    (readCoefficientFactorBits modulus decoded bound a b).checks.length≤2 := by
  unfold readCoefficientFactorBits
  dsimp only
  split
  · exact Nat.zero_le _
  · split <;> simp only [List.length_cons,List.length_nil] <;> omega

/-- Boolean original coefficient reading preserves the complete native
first-success result, for every unsigned source point under the original
canonical decoded residue and short interval bound. -/
theorem readCoefficientFactorBits_exact {modulus decoded bound a b : List Bool}
    (hs : bitValue decoded<bitValue modulus) (hbound : bitValue bound≤bitValue modulus) :
    (readCoefficientFactorBits modulus decoded bound a b).factor.map bitValue=
      (readCoefficientFactor (bitValue modulus) (bitValue decoded) (bitValue bound)
        ((bitValue a : ℤ),(bitValue b : ℤ))).factor := by
  have hr := readIntegerRootsBits_exact bound a b
  cases ho : (readIntegerRootsBits bound a b).roots with
  | none =>
    rw [ho,Option.map_none] at hr
    simp only [readCoefficientFactorBits,ho,Option.map_none,readCoefficientFactor,←hr]
  | some pair =>
    obtain ⟨i,j⟩ := pair
    obtain ⟨hi,hj,_,_⟩ := readIntegerRootsBits_sound ho
    have hf := testIndexBits_exact hs (hi.trans_le hbound)
    have hl := testIndexBits_exact hs (hj.trans_le hbound)
    rw [ho,Option.map_some] at hr
    cases hc : (testIndexBits modulus decoded i).factor with
    | some divisor =>
      rw [hc,Option.map_some] at hf
      simp only [readCoefficientFactorBits,ho,hc,Option.map_some,readCoefficientFactor,←hr,←hf]
    | none =>
      rw [hc,Option.map_none] at hf
      simp only [readCoefficientFactorBits,ho,hc,readCoefficientFactor,←hr,←hf]
      exact hl

/-- The Boolean point reader preserves the actual native GCD-call count,
including rejected roots, improper first checks and early first successes. -/
theorem readCoefficientFactorBits_gcd_exact {modulus decoded bound a b : List Bool}
    (hs : bitValue decoded<bitValue modulus) (hbound : bitValue bound≤bitValue modulus) :
    (readCoefficientFactorBits modulus decoded bound a b).checks.length=
      (readCoefficientFactor (bitValue modulus) (bitValue decoded) (bitValue bound)
        ((bitValue a : ℤ),(bitValue b : ℤ))).checks.length := by
  have hr := readIntegerRootsBits_exact bound a b
  cases ho : (readIntegerRootsBits bound a b).roots with
  | none =>
    rw [ho,Option.map_none] at hr
    simp only [readCoefficientFactorBits,ho,readCoefficientFactor,←hr]
    rfl
  | some pair =>
    obtain ⟨i,j⟩ := pair
    obtain ⟨hi,_,_,_⟩ := readIntegerRootsBits_sound ho
    have hf := testIndexBits_exact hs (hi.trans_le hbound)
    rw [ho,Option.map_some] at hr
    cases hc : (testIndexBits modulus decoded i).factor with
    | some divisor =>
      rw [hc,Option.map_some] at hf
      simp only [readCoefficientFactorBits,ho,hc,readCoefficientFactor,←hr,←hf]
      rfl
    | none =>
      rw [hc,Option.map_none] at hf
      simp only [readCoefficientFactorBits,ho,hc,readCoefficientFactor,←hr,←hf]
      rfl

/-- Scalar point costs retain the actual number of executed Boolean GCD
calls. All original root work and failed checks remain fully charged. -/
theorem readCoefficientFactorBits_cost_by_calls {W : ℕ}
    {modulus decoded bound a b : List Bool}
    (hm : modulus.length≤W) (hs : decoded.length≤W) (hbound : bound.length≤W)
    (ha : a.length≤W) (hb : b.length≤W) :
    (readCoefficientFactorBits modulus decoded bound a b).clock≤
      20000*(W+1)^2+
        (readCoefficientFactorBits modulus decoded bound a b).checks.length*
          (625000*(W+1)^3)+5 := by
  have hr := readIntegerRootsBits_cost hbound ha hb
  unfold readCoefficientFactorBits
  dsimp only
  split
  · dsimp only [List.length_nil,Nat.zero_mul]
    omega
  · rename_i i j hroots
    have hw := readIntegerRootsBits_width ha hb hroots
    have hi : i.length≤4*(W+1) := by omega
    have hj : j.length≤4*(W+1) := by omega
    have hm' : modulus.length≤4*(W+1) := by omega
    have hs' : decoded.length≤4*(W+1) := by omega
    have hfirst := testIndexBits_cost hm' hs' hi
    have hsecond := testIndexBits_cost hm' hs' hj
    have hp := Nat.pow_le_pow_left (by omega : 4*(W+1)+1≤5*(W+1)) 3
    rw [mul_pow] at hp
    norm_num only at hp
    have hf : (testIndexBits modulus decoded i).clock≤625000*(W+1)^3 := by
      nlinarith
    have hjc : (testIndexBits modulus decoded j).clock≤625000*(W+1)^3 := by
      nlinarith
    split <;> dsimp only [List.length_cons,List.length_nil] <;> nlinarith

/-- First proper word, actual stopping prefix and completely charged clock. -/
structure FactorScanWordReport where
  /-- First returned word after actual proper-GCD checks. -/
  factor : Option (List Bool)
  /-- Every actually visited original point report, retaining rejected work. -/
  visited : List PointFactorWordReport
  /-- Actual coefficient point visits, including the successful point. -/
  visits : ℕ
  /-- Actual Boolean checked-GCD calls, including improper outcomes. -/
  gcdCalls : ℕ
  /-- Complete scalar clocks and each executed list/option decision. -/
  clock : ℕ

/-- Execute successive original encoded points, stopping after the first
proper divisor. The source words and root orientations are never pooled. -/
def scanCoefficientsBits (modulus decoded bound : List Bool) :
    List (List Bool×List Bool) → FactorScanWordReport
  | [] => ⟨none,[],0,0,1⟩
  | pair::tail =>
    let current := readCoefficientFactorBits modulus decoded bound pair.1 pair.2
    match current.factor with
    | some divisor => ⟨some divisor,[current],1,current.checks.length,current.clock+4⟩
    | none =>
      let child := scanCoefficientsBits modulus decoded bound tail
      ⟨child.factor,current::child.visited,child.visits+1,
        current.checks.length+child.gcdCalls,current.clock+child.clock+4⟩

/-- Every scan success is a checked proper divisor on arbitrary words. -/
theorem scanCoefficientsBits_sound {modulus decoded bound divisor : List Bool}
    {pairs : List (List Bool×List Bool)}
    (h : (scanCoefficientsBits modulus decoded bound pairs).factor=some divisor) :
    ProperDivisor (bitValue modulus) (bitValue divisor) := by
  induction pairs with
  | nil => cases h
  | cons pair tail ih =>
    unfold scanCoefficientsBits at h
    dsimp only at h
    split at h
    · rename_i d hd
      dsimp only at h
      cases h
      exact readCoefficientFactorBits_sound hd
    · exact ih h

/-- The whole first-success word scan returns exactly the original native
factor result and executes the same number of GCD calls. This equality
covers every original encoded unsigned point list and rejected input. -/
theorem scanCoefficientsBits_exact {modulus decoded bound : List Bool}
    (hs : bitValue decoded<bitValue modulus) (hbound : bitValue bound≤bitValue modulus)
    (pairs : List (List Bool×List Bool)) :
    (scanCoefficientsBits modulus decoded bound pairs).factor.map bitValue=
        (scanCoefficients (bitValue modulus) (bitValue decoded) (bitValue bound)
          (pairs.map (fun pair => ((bitValue pair.1 : ℤ),(bitValue pair.2 : ℤ))))).factor ∧
      (scanCoefficientsBits modulus decoded bound pairs).gcdCalls=
        (scanCoefficients (bitValue modulus) (bitValue decoded) (bitValue bound)
          (pairs.map (fun pair => ((bitValue pair.1 : ℤ),(bitValue pair.2 : ℤ))))).gcdCalls := by
  induction pairs with
  | nil => exact ⟨rfl,rfl⟩
  | cons pair tail ih =>
    have hf := readCoefficientFactorBits_exact (a:=pair.1) (b:=pair.2) hs hbound
    have hg := readCoefficientFactorBits_gcd_exact (a:=pair.1) (b:=pair.2) hs hbound
    cases hc : (readCoefficientFactorBits modulus decoded bound pair.1 pair.2).factor with
    | some divisor =>
      rw [hc,Option.map_some] at hf
      simp only [scanCoefficientsBits,hc,Option.map_some,List.map_cons,scanCoefficients,←hf,hg]
      exact ⟨trivial,trivial⟩
    | none =>
      rw [hc,Option.map_none] at hf
      simp only [scanCoefficientsBits,hc,List.map_cons,scanCoefficients,←hf]
      exact ⟨ih.1,congrArg₂ (·+·) hg ih.2⟩

/-- Actual visits count the retained original reports, with at most two
Boolean GCD calls per visited coefficient point on every input list. -/
theorem scanCoefficientsBits_counts (modulus decoded bound : List Bool)
    (pairs : List (List Bool×List Bool)) :
    (scanCoefficientsBits modulus decoded bound pairs).visited.length=
        (scanCoefficientsBits modulus decoded bound pairs).visits ∧
      (scanCoefficientsBits modulus decoded bound pairs).visits≤pairs.length ∧
      (scanCoefficientsBits modulus decoded bound pairs).gcdCalls≤
        2*(scanCoefficientsBits modulus decoded bound pairs).visits := by
  induction pairs with
  | nil => exact ⟨rfl,Nat.le_refl _,Nat.le_refl _⟩
  | cons pair tail ih =>
    have hc := readCoefficientFactorBits_gcd_bound modulus decoded bound pair.1 pair.2
    unfold scanCoefficientsBits
    dsimp only
    split <;> dsimp only [List.length_cons,List.length_nil] <;> omega

/-- Every original coefficient word occurrence in the executed stopping
prefix is retained exactly, including the successful point. -/
theorem scanCoefficientsBits_source (modulus decoded bound : List Bool)
    (pairs : List (List Bool×List Bool)) :
    (scanCoefficientsBits modulus decoded bound pairs).visited.map
        (fun report => (report.rootReader.sumCoefficient,report.rootReader.productCoefficient))=
      pairs.take (scanCoefficientsBits modulus decoded bound pairs).visits := by
  induction pairs with
  | nil => rfl
  | cons pair tail ih =>
    have hr := readCoefficientFactorBits_rootReader modulus decoded bound pair.1 pair.2
    obtain ⟨_,ha,hb⟩ := readIntegerRootsBits_source bound pair.1 pair.2
    unfold scanCoefficientsBits
    dsimp only
    split
    · simp only [List.map_cons,List.map_nil,hr,ha,hb,List.take_succ_cons,List.take_zero,Prod.mk.eta]
    · simp only [List.map_cons,hr,ha,hb,List.take_succ_cons,Prod.mk.eta]
      rw [ih]

/-- Complete first-success scan clock: quadratic original root reading
per input point plus cubic work for each actually executed Boolean GCD.
All source widths are physical; no encoding or arithmetic call is free. -/
theorem scanCoefficientsBits_cost {W : ℕ} {modulus decoded bound : List Bool}
    (pairs : List (List Bool×List Bool)) (hm : modulus.length≤W) (hs : decoded.length≤W)
    (hbound : bound.length≤W) (hwords : ∀ pair∈pairs, pair.1.length≤W ∧ pair.2.length≤W) :
    (scanCoefficientsBits modulus decoded bound pairs).clock≤
      pairs.length*(20000*(W+1)^2+9)+
        (scanCoefficientsBits modulus decoded bound pairs).gcdCalls*(625000*(W+1)^3)+1 := by
  induction pairs with
  | nil => simp only [scanCoefficientsBits,List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.le_refl]
  | cons pair tail ih =>
    have hw := hwords pair List.mem_cons_self
    have hc := readCoefficientFactorBits_cost_by_calls hm hs hbound hw.1 hw.2
    have ht := ih (fun pair hp => hwords pair (List.mem_cons_of_mem _ hp))
    unfold scanCoefficientsBits
    dsimp only
    split <;> dsimp only [List.length_cons] <;> nlinarith

/-- Every exact word encoding of the original complete enumeration yields
a proper Boolean factor for the original mixed root pair. Private factors
and root indices certify arithmetic and never compute a point or branch. -/
theorem encoded_scan_complete {p q k l : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (modulus decoded bound : List Bool) (pairs : List (List Bool×List Bool))
    (hmodulus : bitValue modulus=p*q) (hs : bitValue decoded<bitValue modulus)
    (hk : k<bitValue bound) (hl : l<bitValue bound) (hLq : bitValue bound≤q) (hkl : k≠l)
    (hP : (bitValue decoded : ZMod p)=(k : ZMod p))
    (hQ : (bitValue decoded : ZMod q)=(l : ZMod q))
    (hencoding : pairs.map (fun pair => ((bitValue pair.1 : ℤ),(bitValue pair.2 : ℤ)))=
      (SemiprimeIndexEnumeration.enumerateCoefficients (bitValue modulus)
        (bitValue decoded) (bitValue bound)).points) :
    ∃ divisor, (scanCoefficientsBits modulus decoded bound pairs).factor=some divisor ∧
      ProperDivisor (bitValue modulus) (bitValue divisor) := by
  have hbound : bitValue bound≤bitValue modulus := by
    rw [hmodulus]
    nlinarith [hp.one_le]
  have he := (scanCoefficientsBits_exact hs hbound pairs).1
  rw [hencoding,hmodulus] at he
  change (scanCoefficientsBits modulus decoded bound pairs).factor.map bitValue=
    (recoverMixedIndex (p*q) (bitValue decoded) (bitValue bound)).reader.factor at he
  obtain ⟨d,hd,_⟩ := recoverMixedIndex_complete hp hq hpq hk hl hLq hkl hP hQ
  rw [hd] at he
  cases ho : (scanCoefficientsBits modulus decoded bound pairs).factor with
  | none => rw [ho,Option.map_none] at he; cases he
  | some divisor => exact ⟨divisor,rfl,scanCoefficientsBits_sound ho⟩

/-- The actual Boolean mixed-index scan preserves the original arithmetic
one-GCD bound. Rejected source points request no GCD; the first accepted
short pair succeeds on its first actual Boolean check. -/
theorem encoded_scan_gcd_bound {p q k l : ℕ} (hp : p.Prime) (hq : q.Prime)
    (modulus decoded bound : List Bool) (pairs : List (List Bool×List Bool))
    (hmodulus : bitValue modulus=p*q) (hs : bitValue decoded<bitValue modulus)
    (hk : k<bitValue bound) (hl : l<bitValue bound)
    (hLp : bitValue bound≤p) (hLq : bitValue bound≤q) (hkl : k≠l)
    (hP : (bitValue decoded : ZMod p)=(k : ZMod p))
    (hQ : (bitValue decoded : ZMod q)=(l : ZMod q))
    (hencoding : pairs.map (fun pair => ((bitValue pair.1 : ℤ),(bitValue pair.2 : ℤ)))=
      (SemiprimeIndexEnumeration.enumerateCoefficients (bitValue modulus)
        (bitValue decoded) (bitValue bound)).points) :
    (scanCoefficientsBits modulus decoded bound pairs).gcdCalls≤1 := by
  have hbound : bitValue bound≤bitValue modulus := by
    rw [hmodulus]
    nlinarith [hp.one_le]
  have he := (scanCoefficientsBits_exact hs hbound pairs).2
  rw [hencoding,hmodulus] at he
  rw [he]
  exact recoverMixedIndex_gcd_bound hp hq hk hl hLp hLq hkl hP hQ

/-- At actual public width the entire encoded mixed-index factor scan
returns a proper factor and has quadratic root work per original candidate
plus only one cubic Boolean GCD charge. Source construction/serialization
and full machine memory are explicit separate costs. -/
theorem public_encoded_factor_scan {p q k l W : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (modulus decoded bound : List Bool) (pairs : List (List Bool×List Bool))
    (hmodulus : bitValue modulus=p*q) (hs : bitValue decoded<bitValue modulus)
    (hbound : bitValue bound=SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
    (hk : k<bitValue bound) (hl : l<bitValue bound) (hLp : bitValue bound≤p) (hkl : k≠l)
    (hP : (bitValue decoded : ZMod p)=(k : ZMod p))
    (hQ : (bitValue decoded : ZMod q)=(l : ZMod q))
    (hencoding : pairs.map (fun pair => ((bitValue pair.1 : ℤ),(bitValue pair.2 : ℤ)))=
      (SemiprimeIndexEnumeration.enumerateCoefficients (bitValue modulus)
        (bitValue decoded) (bitValue bound)).points)
    (hmWidth : modulus.length≤W) (hsWidth : decoded.length≤W) (hbWidth : bound.length≤W)
    (hwords : ∀ pair∈pairs, pair.1.length≤W ∧ pair.2.length≤W) :
    (∃ divisor, (scanCoefficientsBits modulus decoded bound pairs).factor=some divisor ∧
      ProperDivisor (bitValue modulus) (bitValue divisor)) ∧
      (scanCoefficientsBits modulus decoded bound pairs).gcdCalls≤1 ∧
      (scanCoefficientsBits modulus decoded bound pairs).clock≤
        (524290*(3+6144*SemiprimeLehmanCoverage.sixthWidth (p*q)))*(20000*(W+1)^2+9)+
          625000*(W+1)^3+1 := by
  have hLq := hLp.trans hpq.le
  have hsuccess := encoded_scan_complete hp hq hpq.ne modulus decoded bound pairs
    hmodulus hs hk hl hLq hkl hP hQ hencoding
  have hgcd := encoded_scan_gcd_bound hp hq modulus decoded bound pairs
    hmodulus hs hk hl hLp hLq hkl hP hQ hencoding
  have hn := SemiprimeIndexEnumeration.public_mixed_index_enumeration_counts hp hq hpq.le hB
    (hbound ▸ hk) (hbound ▸ hl) (hbound ▸ hLp) hkl hP hQ
  have he := congrArg List.length hencoding
  simp only [List.length_map] at he
  have hlength : pairs.length≤524290*(3+6144*SemiprimeLehmanCoverage.sixthWidth (p*q)) := by
    rw [he,hmodulus,(SemiprimeIndexEnumeration.enumerateCoefficients_counts
      (p*q) (bitValue decoded) (bitValue bound)).1,hbound]
    exact hn.2
  have hc := scanCoefficientsBits_cost pairs hmWidth hsWidth hbWidth hwords
  have hpairs := Nat.mul_le_mul_right (20000*(W+1)^2+9) hlength
  have hcalls := Nat.mul_le_mul_right (625000*(W+1)^3) hgcd
  refine ⟨hsuccess,hgcd,?_⟩
  omega

/-- The actual accepted marked-index word is canonical as an output of
the existing Boolean modular reduction, rather than supplied as residue advice. -/
theorem marked_word_canonical {modulus target targetD baseD word : List Bool}
    (hN : 0<bitValue modulus)
    (hword : (SemiprimeBitInverse.decodeMarkedBits modulus target targetD baseD).index=some word) :
    bitValue word<bitValue modulus := by
  unfold SemiprimeBitInverse.decodeMarkedBits at hword
  dsimp only at hword
  split at hword
  · cases hword
    change bitValue (divideBits _ modulus).remainder<bitValue modulus
    rw [(divideBits_correct _ modulus).2]
    exact Nat.mod_lt _ hN
  · cases hword

/-- Accepted marked output has exactly the original modulus's physical
width, including its padding. No fresh residue serialization is assumed. -/
theorem marked_word_width {modulus target targetD baseD word : List Bool}
    (hN : 0<bitValue modulus)
    (hword : (SemiprimeBitInverse.decodeMarkedBits modulus target targetD baseD).index=some word) :
    word.length=modulus.length := by
  unfold SemiprimeBitInverse.decodeMarkedBits at hword
  dsimp only at hword
  split at hword
  · cases hword
    exact (divideBits_widths hN).1
  · cases hword

/-- The actual marked decoder feeds the actual Boolean first-success
factor scan. Original jet words and the exact bounded source acquisition
remain inputs; their production is not priced by the sum of these two
executed scalar clocks. The decoded word is computed, canonical and of
modulus width, rather than supplied as private mixed-index advice. -/
theorem public_marked_factor_scan {p q k l W : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (modulus target targetD baseD bound : List Bool)
    (source : List Bool→List (List Bool×List Bool))
    (hmodulus : bitValue modulus=p*q)
    (hbound : bitValue bound=SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
    (alpha x : (ZMod (bitValue modulus))ˣ)
    (hx : (bitValue target : ZMod (bitValue modulus))=(x : ZMod (bitValue modulus)))
    (hD : (bitValue targetD : ZMod (bitValue modulus))=
      SemiprimeIntervalJet.targetDerivative
        (alpha : ZMod (bitValue modulus)) (x : ZMod (bitValue modulus)) (bitValue bound))
    (hE : (bitValue baseD : ZMod (bitValue modulus))=
      SemiprimeIntervalJet.baseDerivative
        (alpha : ZMod (bitValue modulus)) (x : ZMod (bitValue modulus)) (bitValue bound))
    (denom : (ZMod (bitValue modulus))ˣ)
    (hdenom : (denom : ZMod (bitValue modulus))=
      (x : ZMod (bitValue modulus))*SemiprimeIntervalJet.targetDerivative
        (alpha : ZMod (bitValue modulus)) (x : ZMod (bitValue modulus)) (bitValue bound))
    (hk : k<bitValue bound) (hl : l<bitValue bound) (hLp : bitValue bound≤p) (hkl : k≠l)
    (hP : ZMod.castHom (hmodulus.symm ▸ dvd_mul_right p q) (ZMod p)
        (x : ZMod (bitValue modulus))=
      (ZMod.castHom (hmodulus.symm ▸ dvd_mul_right p q) (ZMod p)
        (alpha : ZMod (bitValue modulus)))^k)
    (hQ : ZMod.castHom (hmodulus.symm ▸ dvd_mul_left q p) (ZMod q)
        (x : ZMod (bitValue modulus))=
      (ZMod.castHom (hmodulus.symm ▸ dvd_mul_left q p) (ZMod q)
        (alpha : ZMod (bitValue modulus)))^l)
    (hencoding : ∀ word,
      (SemiprimeBitInverse.decodeMarkedBits modulus target targetD baseD).index=some word→
      (source word).map (fun pair => ((bitValue pair.1 : ℤ),(bitValue pair.2 : ℤ)))=
        (SemiprimeIndexEnumeration.enumerateCoefficients (bitValue modulus)
          (bitValue word) (bitValue bound)).points)
    (hmWidth : modulus.length≤W) (hxWidth : target.length≤W)
    (hDWidth : targetD.length≤W) (hEWidth : baseD.length≤W) (hbWidth : bound.length≤W)
    (hwords : ∀ word,
      (SemiprimeBitInverse.decodeMarkedBits modulus target targetD baseD).index=some word→
      ∀ pair∈source word, pair.1.length≤W ∧ pair.2.length≤W) :
    ∃ word, (SemiprimeBitInverse.decodeMarkedBits modulus target targetD baseD).index=some word ∧
      (∃ divisor, (scanCoefficientsBits modulus word bound (source word)).factor=some divisor ∧
        ProperDivisor (bitValue modulus) (bitValue divisor)) ∧
      (scanCoefficientsBits modulus word bound (source word)).gcdCalls≤1 ∧
      (SemiprimeBitInverse.decodeMarkedBits modulus target targetD baseD).clock+
        (scanCoefficientsBits modulus word bound (source word)).clock≤
        (524290*(3+6144*SemiprimeLehmanCoverage.sixthWidth (p*q)))*(20000*(W+1)^2+9)+
          630000*(W+1)^3+1 := by
  have hN : 0<bitValue modulus := by
    rw [hmodulus]
    exact Nat.mul_pos hp.pos hq.pos
  obtain ⟨word,hword,hpr⟩ := SemiprimeBitInverse.decodeMarkedBits_at_local_root hN
    (ZMod.castHom (hmodulus.symm ▸ dvd_mul_right p q) (ZMod p))
    target targetD baseD alpha x (bitValue bound) hx hD hE denom hdenom hk hP
  obtain ⟨word',hword',hqr⟩ := SemiprimeBitInverse.decodeMarkedBits_at_local_root hN
    (ZMod.castHom (hmodulus.symm ▸ dvd_mul_left q p) (ZMod q))
    target targetD baseD alpha x (bitValue bound) hx hD hE denom hdenom hl hQ
  have he : word=word' := Option.some.inj (hword.symm.trans hword')
  rw [← he] at hqr
  have hsP : (bitValue word : ZMod p)=(k : ZMod p) := by
    simpa only [map_natCast] using hpr
  have hsQ : (bitValue word : ZMod q)=(l : ZMod q) := by
    simpa only [map_natCast] using hqr
  have hs := marked_word_canonical hN hword
  have hwidth : word.length≤W := (marked_word_width hN hword).le.trans hmWidth
  have hreader := public_encoded_factor_scan hp hq hpq hB modulus word bound (source word)
    hmodulus hs hbound hk hl hLp hkl hsP hsQ (hencoding word hword)
    hmWidth hwidth hbWidth (hwords word hword)
  have hdecoder := SemiprimeBitInverse.decodeMarkedBits_cost hN hmWidth hxWidth hDWidth hEWidth
  refine ⟨word,hword,hreader.1,hreader.2.1,?_⟩
  nlinarith [hreader.2.2]

end RiemannGaussian.SemiprimeBitIndexFactors
