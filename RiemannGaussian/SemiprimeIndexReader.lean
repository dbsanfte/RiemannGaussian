/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeIndexEnumeration
import RiemannGaussian.SemiprimeWindowSqrt

/-!
# Integer-root factor reading on the native CRT-index enumeration

The original sum/product point is retained while its nonnegative integer
roots are checked using the restoring square root. A first-success scan
tests the two roots against the decoded residue. Native calls and restoring
steps are recorded separately from complete bit operations and memory.
-/

namespace RiemannGaussian.SemiprimeIndexReader

open SemiprimeIndexEnumeration SemiprimeIndexLattice SemiprimeWindowSqrt
open SemiprimeGroupSelection

/-- Original signed coefficients, optional checked roots and the actual
restoring-root report, including unsuccessful calls. -/
structure IntegerRootReport where
  /-- Original sum/product coefficient point. -/
  point : ℤ×ℤ
  /-- Checked roots in descending order, both in the original interval. -/
  roots : Option (ℕ×ℕ)
  /-- Actual restoring-root call; absent when a sign check rejects first. -/
  squareRoot : Option SqrtReport

/-- Read one original coefficient point, checking the discriminant sign
before natural subtraction and both original coefficient equations after
the native restoring-root call. -/
def readIntegerRoots (L : ℕ) (point : ℤ×ℤ) : IntegerRootReport :=
  if 0≤point.1 ∧ 0≤point.2 then
    let a := point.1.toNat
    let b := point.2.toNat
    if 4*b≤a^2 then
      let delta := a^2-4*b
      let report := countedSqrt delta
      let r := report.root
      let hi := (a+r)/2
      let lo := (a-r)/2
      let roots := if r^2=delta ∧ r≤a ∧ (a+r)%2=0 ∧ hi<L ∧ lo<L ∧
          hi+lo=a ∧ hi*lo=b then some (hi,lo) else none
      ⟨point,roots,some report⟩
    else ⟨point,none,none⟩
  else ⟨point,none,none⟩

/-- Actual number of restoring-root calls, including rejected roots. -/
def IntegerRootReport.sqrtCalls (report : IntegerRootReport) : ℕ :=
  match report.squareRoot with
  | none => 0
  | some _ => 1

/-- Actual positive digit-pair steps of the optional restoring-root call. -/
def IntegerRootReport.sqrtSteps (report : IntegerRootReport) : ℕ :=
  match report.squareRoot with
  | none => 0
  | some root => root.steps

/-- The rich signed source point survives every root-reader branch. -/
theorem readIntegerRoots_point (L : ℕ) (point : ℤ×ℤ) :
    (readIntegerRoots L point).point=point := by
  unfold readIntegerRoots
  split <;> dsimp only
  · split <;> rfl

/-- Accepted roots retain both original coefficient equations and
both original short-interval bounds. -/
theorem readIntegerRoots_sound {L i j : ℕ} {point : ℤ×ℤ}
    (h : (readIntegerRoots L point).roots=some (i,j)) :
    i<L ∧ j<L ∧ point.1=(i : ℤ)+j ∧ point.2=(i : ℤ)*j := by
  unfold readIntegerRoots at h
  split at h
  · rename_i hsign
    dsimp only at h
    split at h
    · dsimp only at h
      split at h
      · rename_i hcheck
        have he := Option.some.inj h
        cases he
        obtain ⟨_,_,_,hi,hj,ha,hb⟩ := hcheck
        refine ⟨hi,hj,?_,?_⟩
        · have hcast := congrArg (fun n : ℕ => (n : ℤ)) ha
          simpa only [Nat.cast_add,Int.toNat_of_nonneg hsign.1] using hcast.symm
        · have hcast := congrArg (fun n : ℕ => (n : ℤ)) hb
          simpa only [Nat.cast_mul,Int.toNat_of_nonneg hsign.2] using hcast.symm
      · cases h
    · cases h
  · cases h

/-- The genuine pair has a nonnegative discriminant equal to the square
of its ordered integer gap. Natural subtraction cannot lose its sign. -/
theorem ordered_pair_discriminant {k l : ℕ} (hkl : k≤l) :
    4*(k*l)≤(k+l)^2 ∧ (k+l)^2-4*(k*l)=(l-k)^2 := by
  have hgap := Nat.sub_add_cancel hkl
  have he : 4*(k*l)+(l-k)^2=(k+l)^2 := by nlinarith
  constructor <;> omega

/-- Every genuine short pair is accepted, in its actual descending
integer-root order, including a zero index and repeated roots. -/
theorem readIntegerRoots_ordered {L k l : ℕ} (hk : k<L) (hl : l<L) (hkl : k≤l) :
    (readIntegerRoots L ((k : ℤ)+l,(k : ℤ)*l)).roots=some (l,k) := by
  have hsign : 0≤(k : ℤ)+l ∧ 0≤(k : ℤ)*l := ⟨by positivity,by positivity⟩
  have ha : ((k : ℤ)+l).toNat=k+l := by omega
  have hb : ((k : ℤ)*l).toNat=k*l := by
    norm_cast
  obtain ⟨hdelta,he⟩ := ordered_pair_discriminant hkl
  have hr : (countedSqrt ((k+l)^2-4*(k*l))).root=l-k := by
    rw [he,countedSqrt_correct,Nat.sqrt_eq']
  have hgap := Nat.sub_add_cancel hkl
  have hhi : (k+l+(l-k))/2=l := by omega
  have hlo : (k+l-(l-k))/2=k := by omega
  unfold readIntegerRoots
  rw [if_pos hsign]
  dsimp only
  rw [ha,hb,if_pos hdelta]
  dsimp only
  rw [hr,hhi,hlo]
  have hcheck : (l-k)^2=(k+l)^2-4*(k*l) ∧ l-k≤k+l ∧
      (k+l+(l-k))%2=0 ∧ l<L ∧ k<L ∧ l+k=k+l ∧ l*k=k*l := by
    exact ⟨he.symm,by omega,by omega,hl,hk,by omega,Nat.mul_comm _ _⟩
  rw [if_pos hcheck]

/-- Both original index orientations are accepted; orientation is kept
in this theorem rather than inferred from a lossy discriminant. -/
theorem readIntegerRoots_pair {L k l : ℕ} (hk : k<L) (hl : l<L) :
    (readIntegerRoots L ((k : ℤ)+l,(k : ℤ)*l)).roots=some (l,k) ∨
      (readIntegerRoots L ((k : ℤ)+l,(k : ℤ)*l)).roots=some (k,l) := by
  by_cases hkl : k≤l
  · exact Or.inl (readIntegerRoots_ordered hk hl hkl)
  · have hpoint : ((k : ℤ)+l,(k : ℤ)*l)=((l : ℤ)+k,(l : ℤ)*k) := by
      ext <;> ring
    rw [hpoint]
    exact Or.inr (readIntegerRoots_ordered hl hk (by omega))

/-- Canonical native difference with one modulus of padding before natural
subtraction. No negative residue is silently truncated. -/
def modularDifference (N s i : ℕ) : ℕ := (s%N+N-i%N)%N

/-- The padded native expression is the canonical original ring difference. -/
theorem modularDifference_eq_val {N : ℕ} (hN : 0<N) (s i : ℕ) :
    modularDifference N s i=((s : ZMod N)-(i : ZMod N)).val := by
  have hborrow : i%N≤s%N+N := by have hh := Nat.mod_lt i hN; omega
  have he : (modularDifference N s i : ZMod N)=(s : ZMod N)-(i : ZMod N) := by
    simp only [modularDifference,ZMod.natCast_mod,Nat.cast_sub hborrow,Nat.cast_add,
      ZMod.natCast_self,add_zero]
  have hv := congrArg ZMod.val he
  have hlt : modularDifference N s i<N := Nat.mod_lt _ hN
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hlt] using hv

/-- Original tested index, residue and actual GCD, together with its proper
divisor check. These fields retain the prime-orientation source. -/
structure IndexGcdReport where
  /-- One of the two actual checked integer roots. -/
  index : ℕ
  /-- Original canonical decoded-index difference. -/
  residue : ℕ
  /-- Actual native Euclidean GCD, including 1 and the whole modulus. -/
  divisor : ℕ
  /-- Returned divisor only if the actual GCD passes both strict checks. -/
  factor : Option ℕ

/-- Compute one padded residue and its GCD once, then check properness. -/
def testIndex (N s i : ℕ) : IndexGcdReport :=
  let residue := modularDifference N s i
  let divisor := N.gcd residue
  ⟨i,residue,divisor,if 1<divisor ∧ divisor<N then some divisor else none⟩

/-- The native root check is exactly the existing certified GCD signal. -/
theorem testIndex_factor (N s i : ℕ) :
    (testIndex N s i).factor=checkedSignal N (modularDifference N s i) := rfl

/-- Every returned root-test result is a proper divisor, on every input. -/
theorem testIndex_sound {N s i d : ℕ} (h : (testIndex N s i).factor=some d) :
    ProperDivisor N d := checkedSignal_sound h

/-- Testing the original smaller-prime index recovers that prime when the
two original local indices differ. Both factors are private proof data. -/
theorem testIndex_mixed {p q L k l s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hk : k<L) (hl : l<L) (hLq : L≤q) (hkl : k≠l)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q)) :
    (testIndex (p*q) s k).factor=some p := by
  have hN := Nat.mul_pos hp.pos hq.pos
  have hg := SemiprimeIntervalJet.distinct_index_gcd hp hq hk hl hLq hkl
    (s : ZMod (p*q)) (by simpa only [map_natCast] using hP)
    (by simpa only [map_natCast] using hQ)
  have hproper : 1<p ∧ p<p*q := ⟨hp.one_lt,by nlinarith [hq.one_lt]⟩
  rw [testIndex_factor,modularDifference_eq_val hN,checkedSignal,hg,if_pos hproper]

/-- One actual point reader retains its root report and the one or two GCD
checks that were executed; it stops after the first proper divisor. -/
structure PointFactorReport where
  /-- Rich original point and actual square-root diagnostics. -/
  rootReader : IntegerRootReport
  /-- Every GCD check executed on this point, in its actual order. -/
  checks : List IndexGcdReport
  /-- First proper divisor returned from this point. -/
  factor : Option ℕ

/-- Test both roots of an accepted point, stopping after the first proper
GCD. Rejecting the root check makes no GCD call. -/
def readCoefficientFactor (N s L : ℕ) (point : ℤ×ℤ) : PointFactorReport :=
  let rootReader := readIntegerRoots L point
  match rootReader.roots with
  | none => ⟨rootReader,[],none⟩
  | some (i,j) =>
    let first := testIndex N s i
    match first.factor with
    | some d => ⟨rootReader,[first],some d⟩
    | none =>
      let second := testIndex N s j
      ⟨rootReader,[first,second],second.factor⟩

/-- Every successful point reader passes an actual proper-GCD check. -/
theorem readCoefficientFactor_sound {N s L d : ℕ} {point : ℤ×ℤ}
    (h : (readCoefficientFactor N s L point).factor=some d) : ProperDivisor N d := by
  unfold readCoefficientFactor at h
  dsimp only at h
  split at h
  · cases h
  · rename_i i j hroots
    split at h
    · rename_i d' hfirst
      dsimp only at h
      cases h
      exact testIndex_sound hfirst
    · exact testIndex_sound h

/-- Either successful original root check forces the point reader to return
some proper divisor. A success at its first root takes precedence. -/
theorem readCoefficientFactor_of_roots {N s L i j : ℕ} {point : ℤ×ℤ}
    (hroots : (readIntegerRoots L point).roots=some (i,j))
    (hsuccess : (testIndex N s i).factor≠none ∨ (testIndex N s j).factor≠none) :
    ∃ d, (readCoefficientFactor N s L point).factor=some d ∧ ProperDivisor N d := by
  unfold readCoefficientFactor
  dsimp only
  rw [hroots]
  dsimp only
  cases hfirst : (testIndex N s i).factor with
  | some d => exact ⟨d,rfl,testIndex_sound hfirst⟩
  | none =>
    have hsecond : (testIndex N s j).factor≠none := by
      rcases hsuccess with hh | hh
      · exact False.elim (hh hfirst)
      · exact hh
    cases hlast : (testIndex N s j).factor with
    | none => exact False.elim (hsecond hlast)
    | some d => exact ⟨d,rfl,testIndex_sound hlast⟩

/-- The genuine original sum/product point always yields a proper factor
for mixed decoded indices, including either zero index. -/
theorem readCoefficientFactor_genuine {p q L k l s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hk : k<L) (hl : l<L)
    (hLq : L≤q) (hkl : k≠l)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q)) :
    ∃ d, (readCoefficientFactor (p*q) s L ((k : ℤ)+l,(k : ℤ)*l)).factor=some d ∧
      ProperDivisor (p*q) d := by
  have hg := testIndex_mixed hp hq hk hl hLq hkl hP hQ
  have htest : (testIndex (p*q) s k).factor≠none := by rw [hg]; simp only [ne_eq,reduceCtorEq,not_false_eq_true]
  rcases readIntegerRoots_pair hk hl with hh | hh
  · exact readCoefficientFactor_of_roots hh (Or.inr htest)
  · exact readCoefficientFactor_of_roots hh (Or.inl htest)

/-- At most one restoring-root call is actually executed per point. -/
theorem readIntegerRoots_call_bound (L : ℕ) (point : ℤ×ℤ) :
    (readIntegerRoots L point).sqrtCalls≤1 := by
  by_cases hsign : 0≤point.1 ∧ 0≤point.2
  · by_cases hd : 4*point.2.toNat≤point.1.toNat^2
    · simp only [readIntegerRoots,if_pos hsign,if_pos hd,IntegerRootReport.sqrtCalls,le_refl]
    · simp only [readIntegerRoots,if_pos hsign,if_neg hd,IntegerRootReport.sqrtCalls,Nat.zero_le]
  · simp only [readIntegerRoots,if_neg hsign,IntegerRootReport.sqrtCalls,Nat.zero_le]

/-- The executed restoring call has logarithmically many native digit
steps in the original nonnegative sum coordinate. This is not a bit clock. -/
theorem readIntegerRoots_step_bound (L : ℕ) (point : ℤ×ℤ) :
    (readIntegerRoots L point).sqrtSteps≤Nat.clog 2 (point.1.toNat^2+1) := by
  by_cases hsign : 0≤point.1 ∧ 0≤point.2
  · by_cases hd : 4*point.2.toNat≤point.1.toNat^2
    · have hs := (countedSqrt_budget (point.1.toNat^2-4*point.2.toNat)).1.trans
        (Nat.clog_mono_right 2 (by omega : point.1.toNat^2-4*point.2.toNat+1≤point.1.toNat^2+1))
      simpa only [readIntegerRoots,if_pos hsign,if_pos hd,IntegerRootReport.sqrtSteps] using hs
    · simp only [readIntegerRoots,if_pos hsign,if_neg hd,IntegerRootReport.sqrtSteps,Nat.zero_le]
  · simp only [readIntegerRoots,if_neg hsign,IntegerRootReport.sqrtSteps,Nat.zero_le]

/-- A point in the original coefficient rectangle bounds the actual root
steps by one common public interval-size logarithm. -/
theorem readIntegerRoots_rectangle_steps {L : ℕ} {point : ℤ×ℤ}
    (hpoint : inCoefficientRectangle L point.1 point.2) :
    (readIntegerRoots L point).sqrtSteps≤Nat.clog 2 (4*L^2+1) := by
  have ha : point.1.toNat≤2*L := by
    obtain ⟨ha0,ha1,_,_⟩ := hpoint
    omega
  apply (readIntegerRoots_step_bound L point).trans
  apply Nat.clog_mono_right 2
  have hs := Nat.pow_le_pow_left ha 2
  nlinarith

/-- The factor reader keeps the exact original root report on every branch. -/
theorem readCoefficientFactor_rootReader (N s L : ℕ) (point : ℤ×ℤ) :
    (readCoefficientFactor N s L point).rootReader=readIntegerRoots L point := by
  unfold readCoefficientFactor
  dsimp only
  split
  · rfl
  · split <;> rfl

/-- At most two actual GCD calls are made per point; no GCD is called
for a rejected root report. -/
theorem readCoefficientFactor_gcd_bound (N s L : ℕ) (point : ℤ×ℤ) :
    (readCoefficientFactor N s L point).checks.length≤2 := by
  unfold readCoefficientFactor
  dsimp only
  split
  · simp only [List.length_nil,Nat.zero_le]
  · split <;> simp only [List.length_cons,List.length_nil] <;> omega

/-- The actual stopping scan, its retained visited point reports and its
native call/step counters. All instrumentation is separate from bit costs. -/
structure CoefficientScanReport where
  /-- First proper divisor returned by any visited point. -/
  factor : Option ℕ
  /-- Only the actually visited point reports, in original order. -/
  visited : List PointFactorReport
  /-- Actual number of visited coefficient points. -/
  visits : ℕ
  /-- Actual restoring-root calls, including unsuccessful calls. -/
  sqrtCalls : ℕ
  /-- Actual positive restoring digit-pair steps. -/
  sqrtSteps : ℕ
  /-- Actual Euclidean GCD calls, including improper results. -/
  gcdCalls : ℕ

/-- Execute the factor reader on successive native coefficient points,
stopping immediately at the first proper divisor. -/
def scanCoefficients (N s L : ℕ) : List (ℤ×ℤ) → CoefficientScanReport
  | [] => ⟨none,[],0,0,0,0⟩
  | point::tail =>
    let current := readCoefficientFactor N s L point
    match current.factor with
    | some d => ⟨some d,[current],1,current.rootReader.sqrtCalls,
        current.rootReader.sqrtSteps,current.checks.length⟩
    | none =>
      let rest := scanCoefficients N s L tail
      ⟨rest.factor,current::rest.visited,rest.visits+1,
        current.rootReader.sqrtCalls+rest.sqrtCalls,
        current.rootReader.sqrtSteps+rest.sqrtSteps,current.checks.length+rest.gcdCalls⟩

/-- Any scan success is an actual checked proper divisor. -/
theorem scanCoefficients_sound {N s L d : ℕ} {points : List (ℤ×ℤ)}
    (h : (scanCoefficients N s L points).factor=some d) : ProperDivisor N d := by
  induction points with
  | nil => cases h
  | cons point tail ih =>
    unfold scanCoefficients at h
    dsimp only at h
    split at h
    · rename_i d' hcurrent
      dsimp only at h
      cases h
      exact readCoefficientFactor_sound hcurrent
    · exact ih h

/-- A successful member is sufficient for success of the actual stopping
scan. An earlier success is retained instead of skipped. -/
theorem scanCoefficients_of_member {N s L : ℕ} {points : List (ℤ×ℤ)}
    {point : ℤ×ℤ} (hpoint : point∈points)
    (hsuccess : (readCoefficientFactor N s L point).factor≠none) :
    ∃ d, (scanCoefficients N s L points).factor=some d ∧ ProperDivisor N d := by
  induction points with
  | nil => cases hpoint
  | cons head tail ih =>
    unfold scanCoefficients
    dsimp only
    cases hh : (readCoefficientFactor N s L head).factor with
    | some d => exact ⟨d,rfl,readCoefficientFactor_sound hh⟩
    | none =>
      rcases List.mem_cons.mp hpoint with hhead | htail
      · subst head
        exact False.elim (hsuccess hh)
      · exact ih htail

/-- The actual scan visits a prefix of the input and makes at most one
root call and two GCD calls per visited point. -/
theorem scanCoefficients_counts (N s L : ℕ) (points : List (ℤ×ℤ)) :
    (scanCoefficients N s L points).visited.length=(scanCoefficients N s L points).visits ∧
      (scanCoefficients N s L points).visits≤points.length ∧
      (scanCoefficients N s L points).sqrtCalls≤(scanCoefficients N s L points).visits ∧
      (scanCoefficients N s L points).gcdCalls≤2*(scanCoefficients N s L points).visits := by
  induction points with
  | nil => simp only [scanCoefficients,List.length_nil,Nat.mul_zero,le_refl,and_self]
  | cons point tail ih =>
    have hr := readIntegerRoots_call_bound L point
    have hg := readCoefficientFactor_gcd_bound N s L point
    rw [← readCoefficientFactor_rootReader N s L point] at hr
    unfold scanCoefficients
    dsimp only
    split <;> dsimp only [List.length_cons,List.length_nil]
    · omega
    · omega

/-- Every original rectangle input gives a common native restoring-step
bound, multiplied only by the actual number of visited points. -/
theorem scanCoefficients_step_bound {N s L : ℕ} {points : List (ℤ×ℤ)}
    (hpoints : ∀ point∈points, inCoefficientRectangle L point.1 point.2) :
    (scanCoefficients N s L points).sqrtSteps≤
      (scanCoefficients N s L points).visits*Nat.clog 2 (4*L^2+1) := by
  induction points with
  | nil => simp only [scanCoefficients,Nat.zero_mul,le_refl]
  | cons point tail ih =>
    have hr := readIntegerRoots_rectangle_steps (hpoints point (List.mem_cons_self))
    rw [← readCoefficientFactor_rootReader N s L point] at hr
    have ht := ih (fun x hx => hpoints x (List.mem_cons_of_mem _ hx))
    unfold scanCoefficients
    dsimp only
    split
    · dsimp only
      simpa only [Nat.one_mul] using hr
    · dsimp only
      rw [Nat.add_mul,Nat.one_mul]
      omega

/-- Native enumeration and the actual first-success reader are retained
together, with the basis orientation and every executed candidate report. -/
structure IndexRecoveryReport where
  /-- Complete native enumerator output. -/
  enumeration : EnumerationReport
  /-- Actual stopping reader of that output. -/
  reader : CoefficientScanReport

/-- Recover a mixed short CRT index using only the public modulus, decoded
residue and original interval bound. No private index computes a point. -/
def recoverMixedIndex (N s L : ℕ) : IndexRecoveryReport :=
  let enumeration := enumerateCoefficients N s L
  ⟨enumeration,scanCoefficients N s L enumeration.points⟩

/-- Every result of the composed native stage is a proper divisor. -/
theorem recoverMixedIndex_sound {N s L d : ℕ}
    (h : (recoverMixedIndex N s L).reader.factor=some d) : ProperDivisor N d :=
  scanCoefficients_sound h

/-- The actual native enumeration and integer-root reader recover a
proper divisor for every original mixed pair. This universal arithmetic
statement has no successful-example or supplied-candidate premise. -/
theorem recoverMixedIndex_complete {p q L k l s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hk : k<L) (hl : l<L) (hLq : L≤q) (hkl : k≠l)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q)) :
    ∃ d, (recoverMixedIndex (p*q) s L).reader.factor=some d ∧ ProperDivisor (p*q) d := by
  have hpoint := mixed_index_genuine_point_visited hp hq hpq hk hl hP hQ
  obtain ⟨d,hd,_⟩ := readCoefficientFactor_genuine hp hq hk hl hLq hkl hP hQ
  apply scanCoefficients_of_member hpoint
  rw [hd]
  simp only [ne_eq,reduceCtorEq,not_false_eq_true]

/-- Both actual original index tests succeed, with their original prime
orientations retained even though the sum/product point is symmetric. -/
theorem testIndex_both_mixed {p q L k l s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hk : k<L) (hl : l<L) (hLp : L≤p) (hLq : L≤q) (hkl : k≠l)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q)) :
    (testIndex (p*q) s k).factor=some p ∧ (testIndex (p*q) s l).factor=some q := by
  refine ⟨testIndex_mixed hp hq hk hl hLq hkl hP hQ,?_⟩
  simpa only [Nat.mul_comm q p] using
    testIndex_mixed hq hp hl hk hLp hkl.symm hQ hP

/-- Any accepted short roots of any original congruence candidate are the
original local indices, with their two possible orientations explicit. -/
theorem accepted_candidate_pair {p q L k l s i j : ℕ} {point : ℤ×ℤ}
    (hp : p.Prime) (hq : q.Prime) (hk : k<L) (hl : l<L)
    (hLp : L≤p) (hLq : L≤q) (hkl : k≠l)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q))
    (hcandidate : coefficientCandidate (s : ZMod (p*q)) L point.1 point.2)
    (hroots : (readIntegerRoots L point).roots=some (i,j)) :
    (k=i ∧ l=j) ∨ (k=j ∧ l=i) := by
  obtain ⟨hi,hj,ha,hb⟩ := readIntegerRoots_sound hroots
  rw [ha,hb] at hcandidate
  exact mixed_index_root_pair_unique hp hq hLp hLq hk hl hi hj hkl
    (s : ZMod (p*q)) (by simpa only [map_natCast] using hP)
    (by simpa only [map_natCast] using hQ) hcandidate

/-- On every original candidate in the mixed regime, an accepted root
report makes exactly one GCD call and returns its oriented prime. -/
theorem accepted_candidate_first_gcd {p q L k l s i j : ℕ} {point : ℤ×ℤ}
    (hp : p.Prime) (hq : q.Prime) (hk : k<L) (hl : l<L)
    (hLp : L≤p) (hLq : L≤q) (hkl : k≠l)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q))
    (hcandidate : coefficientCandidate (s : ZMod (p*q)) L point.1 point.2)
    (hroots : (readIntegerRoots L point).roots=some (i,j)) :
    (readCoefficientFactor (p*q) s L point).checks.length=1 ∧
      ((readCoefficientFactor (p*q) s L point).factor=some p ∨
        (readCoefficientFactor (p*q) s L point).factor=some q) := by
  have hpair := accepted_candidate_pair hp hq hk hl hLp hLq hkl hP hQ hcandidate hroots
  have htests := testIndex_both_mixed hp hq hk hl hLp hLq hkl hP hQ
  unfold readCoefficientFactor
  dsimp only
  rw [hroots]
  dsimp only
  rcases hpair with hpair | hpair
  · have hi : i=k := hpair.1.symm
    rw [hi,htests.1]
    exact ⟨rfl,Or.inl rfl⟩
  · have hi : i=l := hpair.2.symm
    rw [hi,htests.2]
    exact ⟨rfl,Or.inr rfl⟩

/-- Every candidate either makes no GCD call or succeeds at its first GCD.
The second-root fallback is never reached in the proved mixed regime. -/
theorem mixed_candidate_gcd_state {p q L k l s : ℕ} {point : ℤ×ℤ}
    (hp : p.Prime) (hq : q.Prime) (hk : k<L) (hl : l<L)
    (hLp : L≤p) (hLq : L≤q) (hkl : k≠l)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q))
    (hcandidate : coefficientCandidate (s : ZMod (p*q)) L point.1 point.2) :
    let out := readCoefficientFactor (p*q) s L point
    (out.checks.length=0 ∧ out.factor=none) ∨
      (out.checks.length=1 ∧ (out.factor=some p ∨ out.factor=some q)) := by
  dsimp only
  cases hr : (readIntegerRoots L point).roots with
  | none =>
    left
    simp only [readCoefficientFactor,hr,List.length_nil,and_self]
  | some roots =>
    obtain ⟨i,j⟩ := roots
    exact Or.inr (accepted_candidate_first_gcd hp hq hk hl hLp hLq hkl hP hQ hcandidate hr)

/-- Every recorded scan counter is the sum of the actual retained visited
reports; rejected calls and improper GCDs are included. -/
theorem scanCoefficients_counter_sums (N s L : ℕ) (points : List (ℤ×ℤ)) :
    let out := scanCoefficients N s L points
    out.sqrtCalls=(out.visited.map (fun row => row.rootReader.sqrtCalls)).sum ∧
      out.sqrtSteps=(out.visited.map (fun row => row.rootReader.sqrtSteps)).sum ∧
      out.gcdCalls=(out.visited.map (fun row => row.checks.length)).sum := by
  dsimp only
  induction points with
  | nil => simp only [scanCoefficients,List.map_nil,List.sum_nil,and_self]
  | cons point tail ih =>
    unfold scanCoefficients
    dsimp only
    split
    · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,and_self]
    · simp only [List.map_cons,List.sum_cons]
      exact ⟨congrArg (fun n => (readCoefficientFactor N s L point).rootReader.sqrtCalls+n) ih.1,
        congrArg (fun n => (readCoefficientFactor N s L point).rootReader.sqrtSteps+n) ih.2.1,
        congrArg (fun n => (readCoefficientFactor N s L point).checks.length+n) ih.2.2⟩

/-- Generic actual reader counts are bounded by the executed enumerator's
visits, and all original candidates bound the restoring-step input. -/
theorem recoverMixedIndex_counts {N s L : ℕ} (hN : 0<N) (hL : 0<L) :
    let out := recoverMixedIndex N s L
    out.reader.visits≤out.enumeration.visits ∧
      out.reader.sqrtCalls≤out.reader.visits ∧ out.reader.gcdCalls≤2*out.reader.visits ∧
      out.reader.sqrtSteps≤out.reader.visits*Nat.clog 2 (4*L^2+1) := by
  dsimp only [recoverMixedIndex]
  obtain ⟨_,hv,hs,hg⟩ := scanCoefficients_counts N s L (enumerateCoefficients N s L).points
  rw [(enumerateCoefficients_counts N s L).1] at hv
  refine ⟨hv,hs,hg,scanCoefficients_step_bound ?_⟩
  intro point hpoint
  obtain ⟨ha0,ha1,hb0,hb1,_⟩ := (mem_enumerateCoefficients_points hN hL point).mp hpoint
  exact ⟨ha0,ha1,hb0,hb1⟩

/-- On a list of original mixed candidates the scan makes at most one
GCD call in total, because its first accepted pair succeeds immediately. -/
theorem mixed_scan_gcd_bound {p q L k l s : ℕ} {points : List (ℤ×ℤ)}
    (hp : p.Prime) (hq : q.Prime) (hk : k<L) (hl : l<L)
    (hLp : L≤p) (hLq : L≤q) (hkl : k≠l)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q))
    (hpoints : ∀ point∈points, coefficientCandidate (s : ZMod (p*q)) L point.1 point.2) :
    (scanCoefficients (p*q) s L points).gcdCalls≤1 := by
  induction points with
  | nil => exact Nat.zero_le _
  | cons point tail ih =>
    have hstate := mixed_candidate_gcd_state hp hq hk hl hLp hLq hkl hP hQ
      (hpoints point List.mem_cons_self)
    have ht := ih (fun x hx => hpoints x (List.mem_cons_of_mem _ hx))
    dsimp only at hstate
    unfold scanCoefficients
    dsimp only
    rcases hstate with ⟨hc,hf⟩ | ⟨hc,hf⟩
    · rw [hf]
      dsimp only
      rw [hc,Nat.zero_add]
      exact ht
    · rcases hf with hf | hf <;> rw [hf] <;> dsimp only <;> omega

/-- The actual mixed-index stage makes at most one native GCD call, without
testing every root in the original quadratic interval. -/
theorem recoverMixedIndex_gcd_bound {p q L k l s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hk : k<L) (hl : l<L)
    (hLp : L≤p) (hLq : L≤q) (hkl : k≠l)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q)) :
    (recoverMixedIndex (p*q) s L).reader.gcdCalls≤1 := by
  apply mixed_scan_gcd_bound hp hq hk hl hLp hLq hkl hP hQ
  intro point hpoint
  exact (mem_enumerateCoefficients_points (Nat.mul_pos hp.pos hq.pos) (by omega) point).mp hpoint

/-- Public-length discriminants have at most twice the modulus's ceiling
binary logarithm plus three. This bounds native digit steps, not bit work. -/
theorem interval_root_log_bound {N L : ℕ} (hLN : L≤N) :
    Nat.clog 2 (4*L^2+1)≤2*Nat.clog 2 (N+1)+3 := by
  let ell := Nat.clog 2 (N+1)
  have hbase : N+1≤2^ell := Nat.le_pow_clog (by decide) (N+1)
  have hLpow : L≤2^ell := hLN.trans (by omega)
  have hs := Nat.pow_le_pow_left hLpow 2
  have hp : 0<(2^ell)^2 := by positivity
  have hn : 4*L^2+1≤8*(2^ell)^2 := by nlinarith
  have he : 8*(2^ell)^2=2^(2*ell+3) := by
    rw [pow_add,Nat.mul_comm 2 ell,pow_mul]
    ring
  rw [he] at hn
  exact Nat.clog_le_of_le_pow hn

/-- Actual public-width reader traversal, root calls, native root steps
and GCD calls are bounded on every mixed original index pair. Complete
signed Boolean enumeration and working-memory costs remain separate. -/
theorem public_mixed_index_reader_counts {p q k l s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≤q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hk : k<SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
    (hl : l<SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
    (hLp : SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))≤p) (hkl : k≠l)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q)) :
    let L := SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))
    let out := recoverMixedIndex (p*q) s L
    let V := 524290*(3+6144*SemiprimeLehmanCoverage.sixthWidth (p*q))
    out.reader.visits≤V ∧ out.reader.sqrtCalls≤V ∧
      out.reader.sqrtSteps≤V*(2*Nat.clog 2 (p*q+1)+3) ∧ out.reader.gcdCalls≤1 := by
  dsimp only
  have hN := Nat.mul_pos hp.pos hq.pos
  have hLq := hLp.trans hpq
  have hLN : SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))≤p*q := by
    have hpN : p≤p*q := by nlinarith [hq.one_lt]
    exact hLp.trans hpN
  have hcounts := recoverMixedIndex_counts (s:=s) hN (by omega : 0<SemiprimeSeedSumAcquisition.seedLength
    (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
  have henum := public_mixed_index_enumeration_counts hp hq hpq hB hk hl hLp hkl hP hQ
  have hvisit := hcounts.1.trans henum.2
  refine ⟨hvisit,hcounts.2.1.trans hvisit,?_,
    recoverMixedIndex_gcd_bound hp hq hk hl hLp hLq hkl hP hQ⟩
  exact hcounts.2.2.2.trans (Nat.mul_le_mul hvisit (interval_root_log_bound hLN))

/-- The original marked decoder on the actual matched public long route
now feeds an executed, complete native factor reader. No hidden index or
factor is an executable input, and no balanced-factor premise is used.
This theorem does not pay original jet acquisition or full bit/memory cost. -/
theorem actual_public_route_native_reader {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hroute : SemiprimeWrapIndexRecovery.routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let g := ZMod.unitOfCoprime a hc
      let alpha := SemiprimeSeedSumAcquisition.seedBase
        (SemiprimeCentreFreeCover.projectedUnit g m) m
      let L := SemiprimeSeedSumAcquisition.seedLength m
      ∀ (x : ZMod (p*q)) (denom : (ZMod (p*q))ˣ),
        (denom : ZMod (p*q))=x*SemiprimeIntervalJet.targetDerivative (alpha : ZMod (p*q)) x L →
        ∀ k l : ℕ, k<L → l<L → k≠l →
        ZMod.castHom (dvd_mul_right p q) (ZMod p) x=
          (ZMod.castHom (dvd_mul_right p q) (ZMod p) (alpha : ZMod (p*q)))^k →
        ZMod.castHom (dvd_mul_left q p) (ZMod q) x=
          (ZMod.castHom (dvd_mul_left q p) (ZMod q) (alpha : ZMod (p*q)))^l →
        let s := SemiprimeIntervalJet.decodedIndex (alpha : ZMod (p*q)) x L denom
        let out := recoverMixedIndex (p*q) s.val L
        let V := 524290*(3+6144*SemiprimeLehmanCoverage.sixthWidth (p*q))
        (∃ d, out.reader.factor=some d ∧ ProperDivisor (p*q) d) ∧
          out.reader.visits≤V ∧ out.reader.sqrtCalls≤V ∧
          out.reader.sqrtSteps≤V*(2*Nat.clog 2 (p*q+1)+3) ∧ out.reader.gcdCalls≤1 ∧
          out.enumeration.iterationBudget≤2*Nat.clog 2 (s.val%(p*q)+1)+
            524290*(4+6144*SemiprimeLehmanCoverage.sixthWidth (p*q)) := by
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  have hdata := SemiprimeWrapIndexRecovery.routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hdata
  obtain ⟨hc,hlong⟩ := hdata
  have hN := Nat.mul_pos hp.pos hq.pos
  let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
  let g := ZMod.unitOfCoprime a hc
  let alpha := SemiprimeSeedSumAcquisition.seedBase
    (SemiprimeCentreFreeCover.projectedUnit g m) m
  let L := SemiprimeSeedSumAcquisition.seedLength m
  have hm : 4≤m := hB.trans (SemiprimeEuclidRowBudget.publicRowModulus_bounds hN).1
  have hperiods := SemiprimeSeedSumAcquisition.long_seed_interval_periods hm g hlong
  have hLp : L≤p := hperiods.1.trans
    (SemiprimeIntervalJet.local_unit_period_lt_prime hp (dvd_mul_right p q) alpha).le
  refine ⟨hc,?_⟩
  dsimp only
  intro x denom hdenom k l hk hl hkl hP hQ
  let s := SemiprimeIntervalJet.decodedIndex (alpha : ZMod (p*q)) x L denom
  have hpr := SemiprimeIntervalJet.decodedIndex_map_root
    (ZMod.castHom (dvd_mul_right p q) (ZMod p)) (alpha : ZMod (p*q)) x L denom hdenom hk hP
  have hqr := SemiprimeIntervalJet.decodedIndex_map_root
    (ZMod.castHom (dvd_mul_left q p) (ZMod q)) (alpha : ZMod (p*q)) x L denom hdenom hl hQ
  have hsP : (s.val : ZMod p)=(k : ZMod p) := by
    rw [SemiprimeCentreFreeCover.castHom_val (dvd_mul_right p q)]
    exact hpr
  have hsQ : (s.val : ZMod q)=(l : ZMod q) := by
    rw [SemiprimeCentreFreeCover.castHom_val (dvd_mul_left q p)]
    exact hqr
  have hcounts := public_mixed_index_reader_counts hp hq hpq.le hB hk hl hLp hkl hsP hsQ
  exact ⟨recoverMixedIndex_complete hp hq hpq.ne hk hl (hLp.trans hpq.le) hkl hsP hsQ,
    hcounts.1,hcounts.2.1,hcounts.2.2.1,hcounts.2.2.2,
    public_mixed_index_iteration_budget hp hq hpq.le hB hk hl hLp hkl hsP hsQ⟩

/-- The scan retains exactly the inspected input prefix, even when it
stops before the genuine point because an earlier candidate succeeds. -/
theorem scanCoefficients_visited_prefix (N s L : ℕ) (points : List (ℤ×ℤ)) :
    ((scanCoefficients N s L points).visited.map (fun row => row.rootReader.point))=
      points.take (scanCoefficients N s L points).visits := by
  induction points with
  | nil => rfl
  | cons point tail ih =>
    have hp : (readCoefficientFactor N s L point).rootReader.point=point := by
      rw [readCoefficientFactor_rootReader,readIntegerRoots_point]
    unfold scanCoefficients
    dsimp only
    split
    · simp only [List.map_cons,List.map_nil,List.take_succ_cons,List.take_zero,hp]
    · simp only [List.map_cons,List.take_succ_cons,hp]
      exact congrArg (List.cons point) ih

/-- A semantic handoff from the actual Boolean marked decoder to the
executed native enumeration and integer-root reader. The handoff interprets
the accepted word; serialization and native-to-Boolean reader refinement
are not priced by this theorem. Exact original jet words remain inputs. -/
theorem marked_bits_native_reader {modulus target targetD baseD : List Bool}
    {p q L k l : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hmodulus : SemiprimeBitArithmetic.bitValue modulus=p*q)
    (alpha x : (ZMod (SemiprimeBitArithmetic.bitValue modulus))ˣ)
    (hx : (SemiprimeBitArithmetic.bitValue target : ZMod (SemiprimeBitArithmetic.bitValue modulus))=
      (x : ZMod (SemiprimeBitArithmetic.bitValue modulus)))
    (hD : (SemiprimeBitArithmetic.bitValue targetD : ZMod (SemiprimeBitArithmetic.bitValue modulus))=
      SemiprimeIntervalJet.targetDerivative
        (alpha : ZMod (SemiprimeBitArithmetic.bitValue modulus))
        (x : ZMod (SemiprimeBitArithmetic.bitValue modulus)) L)
    (hE : (SemiprimeBitArithmetic.bitValue baseD : ZMod (SemiprimeBitArithmetic.bitValue modulus))=
      SemiprimeIntervalJet.baseDerivative
        (alpha : ZMod (SemiprimeBitArithmetic.bitValue modulus))
        (x : ZMod (SemiprimeBitArithmetic.bitValue modulus)) L)
    (denom : (ZMod (SemiprimeBitArithmetic.bitValue modulus))ˣ)
    (hdenom : (denom : ZMod (SemiprimeBitArithmetic.bitValue modulus))=
      (x : ZMod (SemiprimeBitArithmetic.bitValue modulus))*
        SemiprimeIntervalJet.targetDerivative
          (alpha : ZMod (SemiprimeBitArithmetic.bitValue modulus))
          (x : ZMod (SemiprimeBitArithmetic.bitValue modulus)) L)
    (hk : k<L) (hl : l<L) (hLq : L≤q) (hkl : k≠l)
    (hP : ZMod.castHom (hmodulus.symm ▸ dvd_mul_right p q) (ZMod p)
        (x : ZMod (SemiprimeBitArithmetic.bitValue modulus))=
      (ZMod.castHom (hmodulus.symm ▸ dvd_mul_right p q) (ZMod p)
        (alpha : ZMod (SemiprimeBitArithmetic.bitValue modulus)))^k)
    (hQ : ZMod.castHom (hmodulus.symm ▸ dvd_mul_left q p) (ZMod q)
        (x : ZMod (SemiprimeBitArithmetic.bitValue modulus))=
      (ZMod.castHom (hmodulus.symm ▸ dvd_mul_left q p) (ZMod q)
        (alpha : ZMod (SemiprimeBitArithmetic.bitValue modulus)))^l) :
    ∃ word, (SemiprimeBitInverse.decodeMarkedBits modulus target targetD baseD).index=some word ∧
      (∃ d, (recoverMixedIndex (SemiprimeBitArithmetic.bitValue modulus)
        (SemiprimeBitArithmetic.bitValue word) L).reader.factor=some d ∧
        ProperDivisor (SemiprimeBitArithmetic.bitValue modulus) d) := by
  have hN : 0<SemiprimeBitArithmetic.bitValue modulus := by
    rw [hmodulus]
    exact Nat.mul_pos hp.pos hq.pos
  obtain ⟨word,hword,hpr⟩ := SemiprimeBitInverse.decodeMarkedBits_at_local_root hN
    (ZMod.castHom (hmodulus.symm ▸ dvd_mul_right p q) (ZMod p))
    target targetD baseD alpha x L hx hD hE denom hdenom hk hP
  obtain ⟨word',hword',hqr⟩ := SemiprimeBitInverse.decodeMarkedBits_at_local_root hN
    (ZMod.castHom (hmodulus.symm ▸ dvd_mul_left q p) (ZMod q))
    target targetD baseD alpha x L hx hD hE denom hdenom hl hQ
  have he : word=word' := Option.some.inj (hword.symm.trans hword')
  rw [← he] at hqr
  have hsP : (SemiprimeBitArithmetic.bitValue word : ZMod p)=(k : ZMod p) := by
    simpa only [map_natCast] using hpr
  have hsQ : (SemiprimeBitArithmetic.bitValue word : ZMod q)=(l : ZMod q) := by
    simpa only [map_natCast] using hqr
  refine ⟨word,hword,?_⟩
  rw [hmodulus]
  exact recoverMixedIndex_complete hp hq hpq hk hl hLq hkl hsP hsQ

end RiemannGaussian.SemiprimeIndexReader
