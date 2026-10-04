/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeIndexReader
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Lazy marked-jet acquisition and a fixed geometric recurrence

The original detector and both derivative channels are retained in four
scalar components. One auxiliary component carries the current index times
the product, giving polynomial coefficients of degree one in the current
base power. There is no divided product or supplied index in this data path.
The literal recurrence is linear in interval length; a fast matrix-product
backend, detector batch, full bit clocks and memory remain separate work.
-/

namespace RiemannGaussian.SemiprimeSeedLazyJets

open Polynomial SemiprimeIntervalJet SemiprimeSharedIntervalJet
open SemiprimeSeedSumAcquisition SemiprimeGroupSelection
open scoped BigOperators Matrix

/-- Rich original interval channels and one auxiliary marked-product state. -/
structure GeometricJetState (R : Type*) where
  /-- Original interval product. -/
  product : R
  /-- Original derivative in the target variable. -/
  target : R
  /-- Original logarithmic derivative in the geometric base. -/
  base : R
  /-- Current interval length times its original product. -/
  marked : R

/-- Empty-interval detector, derivatives and auxiliary state. -/
def initialJet {R : Type*} [CommRing R] : GeometricJetState R := ⟨1,0,0,0⟩

/-- One literal scalar step. The mark is advanced by an addition rather
than supplied as an index or a division by the possibly zero product. -/
def jetStep {R : Type*} [CommRing R] (x t : R) (state : GeometricJetState R) :
    GeometricJetState R :=
  let f := x-t
  ⟨f*state.product,state.product+f*state.target,
    f*state.base-t*state.marked,f*(state.marked+state.product)⟩

/-- Actual scalar state, iterated base power and native iteration counter. -/
structure JetRunReport (R : Type*) where
  /-- Every original channel and the retained auxiliary mark. -/
  state : GeometricJetState R
  /-- Base power for the next literal step. -/
  power : R
  /-- Actual executed scalar steps, separate from any bit clock. -/
  steps : ℕ

/-- Execute the four-component recurrence and update the base power once
per step. No polynomial coefficients, cofactor list or pair matrix are built. -/
def geometricJetRun {R : Type*} [CommRing R] (alpha x : R) : ℕ → JetRunReport R
  | 0 => ⟨initialJet,1,0⟩
  | n+1 =>
    let child := geometricJetRun alpha x n
    ⟨jetStep x child.power child.state,child.power*alpha,child.steps+1⟩

/-- Literal one-factor block values, retaining its absolute exponent mark. -/
theorem singleton_block_jet {R : Type*} [CommRing R] (alpha x : R) (n : ℕ) :
    blockProduct alpha x n 1=x-alpha^n ∧
      blockTargetDerivative alpha x n 1=1 ∧
      blockBaseDerivative alpha x n 1= -(n : R)*alpha^n := by
  simp only [blockProduct,blockFactor,blockTargetDerivative,blockBaseDerivative,
    blockCofactor,Finset.range_one,Finset.prod_singleton,Finset.sum_singleton,
    Finset.erase_singleton,Finset.prod_empty,add_zero,mul_one,neg_mul,and_self]

/-- The recurrence preserves the exact original rich jet, including
saturated or repeated roots, over every commutative coefficient ring. -/
theorem geometricJetRun_exact {R : Type*} [CommRing R] (alpha x : R) (L : ℕ) :
    (geometricJetRun alpha x L).state.product=intervalProduct alpha x L ∧
      (geometricJetRun alpha x L).state.target=targetDerivative alpha x L ∧
      (geometricJetRun alpha x L).state.base=baseDerivative alpha x L ∧
      (geometricJetRun alpha x L).state.marked=(L : R)*intervalProduct alpha x L ∧
      (geometricJetRun alpha x L).power=alpha^L ∧
      (geometricJetRun alpha x L).steps=L := by
  induction L with
  | zero => simp only [geometricJetRun,initialJet,intervalProduct,targetDerivative,
      baseDerivative,Finset.range_zero,Finset.prod_empty,Finset.sum_empty,
      Nat.cast_zero,zero_mul,pow_zero,neg_zero,and_self]
  | succ n ih =>
    obtain ⟨hP,hD,hE,hmark,hpow,hsteps⟩ := ih
    obtain ⟨hblock,hblockD,hblockE⟩ := singleton_block_jet alpha x n
    have hPnext := intervalProduct_split alpha x n 1
    have hDnext := targetDerivative_split alpha x n 1
    have hEnext := baseDerivative_split alpha x n 1
    rw [hblock] at hPnext hDnext hEnext
    rw [hblockD] at hDnext
    rw [hblockE] at hEnext
    dsimp only [geometricJetRun,jetStep]
    rw [hP,hD,hE,hmark,hpow,hsteps]
    refine ⟨?_,?_,?_,?_,?_,rfl⟩
    · rw [hPnext]
      ring
    · rw [hDnext]
      ring
    · rw [hEnext]
      ring
    · rw [hPnext,Nat.cast_add,Nat.cast_one]
      ring
    · exact (pow_succ alpha n).symm

/-- The actual recurrence exposes the original detector/target/base triple. -/
def JetRunReport.jet {R : Type*} (report : JetRunReport R) : R×R×R :=
  (report.state.product,report.state.target,report.state.base)

/-- The scalar recurrence's triple is exactly the original interval triple. -/
theorem geometricJetRun_jet {R : Type*} [CommRing R] (alpha x : R) (L : ℕ) :
    (geometricJetRun alpha x L).jet=
      (intervalProduct alpha x L,targetDerivative alpha x L,baseDerivative alpha x L) := by
  obtain ⟨hP,hD,hE,_,_,_⟩ := geometricJetRun_exact alpha x L
  exact Prod.ext hP (Prod.ext hD hE)

/-- The four source components, with no scalar compression or channel sum. -/
def jetVector {R : Type*} (state : GeometricJetState R) : Fin 4 → R :=
  ![state.product,state.target,state.base,state.marked]

/-- Proof-side fixed four-by-four recurrence matrix, with polynomial
coefficients in the current base power. The scalar executor uses jetStep. -/
noncomputable def jetMatrix {R : Type*} [CommRing R] (x : R) :
    Matrix (Fin 4) (Fin 4) R[X] :=
  !![C x-X,0,0,0;
     1,C x-X,0,0;
     0,0,C x-X,-X;
     C x-X,0,0,C x-X]

/-- Every entry of the actual transfer specification has degree at most
one; dimension and degree do not grow with the interval length. -/
theorem jetMatrix_degree {R : Type*} [CommRing R] (x : R) (i j : Fin 4) :
    (jetMatrix x i j).natDegree≤1 := by
  have hf : (C x-X : R[X]).natDegree≤1 := by
    exact (natDegree_sub_le (C x) X).trans
      (max_le (by simp only [natDegree_C]; omega) natDegree_X_le)
  fin_cases i <;> fin_cases j <;> simp [jetMatrix,hf,natDegree_X_le]

/-- Evaluating the fixed degree-one matrix reproduces the literal scalar
step with all four original components and no inverse. -/
theorem jetMatrix_step {R : Type*} [CommRing R] (x t : R) (state : GeometricJetState R) :
    Matrix.mulVec (Matrix.of (fun i j => (jetMatrix x i j).eval t)) (jetVector state)=
      jetVector (jetStep x t state) := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
    jetMatrix,jetVector,jetStep] <;> ring

/-- Native detector selection stops on a proper factor or on the first
zero canonical residue, retaining the original seed label. -/
inductive DetectorOutcome (S : Type*) where
  /-- A proper GCD, checked before any marked jet is requested. -/
  | factor (divisor : ℕ)
  /-- The original label of the first saturated detector. -/
  | saturated (seed : S)

/-- Executed native detector selection and every visited labelled residue. -/
structure DetectorScanReport (S : Type*) where
  /-- First stopping outcome, if any. -/
  outcome : Option (DetectorOutcome S)
  /-- Exactly the detector rows inspected before stopping. -/
  visited : List (S×ℕ)
  /-- Actual native GCD calls, including improper results. -/
  gcdCalls : ℕ

/-- Inspect already acquired canonical detector residues. Derivative
acquisition is absent from this native selector and remains a later call. -/
def selectDetector {S : Type*} (N : ℕ) : List (S×ℕ) → DetectorScanReport S
  | [] => ⟨none,[],0⟩
  | row::tail =>
    match checkedSignal N row.2 with
    | some d => ⟨some (.factor d),[row],1⟩
    | none =>
      if row.2=0 then ⟨some (.saturated row.1),[row],1⟩
      else
        let child := selectDetector N tail
        ⟨child.outcome,row::child.visited,child.gcdCalls+1⟩

/-- Every selected factor is proper on arbitrary input detector words. -/
theorem selectDetector_factor_sound {S : Type*} {N d : ℕ} {rows : List (S×ℕ)}
    (h : (selectDetector N rows).outcome=some (.factor d)) : ProperDivisor N d := by
  induction rows with
  | nil => cases h
  | cons row tail ih =>
    unfold selectDetector at h
    split at h
    · rename_i d' hd
      dsimp only at h
      cases h
      exact checkedSignal_sound hd
    · split at h
      · cases h
      · exact ih h

/-- A saturated outcome retains an original label with an actually
inspected zero residue; zero is not inferred from missing factor output. -/
theorem selectDetector_saturated_source {S : Type*} {N : ℕ} {rows : List (S×ℕ)} {s : S}
    (h : (selectDetector N rows).outcome=some (.saturated s)) : (s,0)∈rows := by
  induction rows with
  | nil => cases h
  | cons row tail ih =>
    unfold selectDetector at h
    split at h
    · cases h
    · split at h
      · rename_i hz
        dsimp only at h
        have hs := DetectorOutcome.saturated.inj (Option.some.inj h)
        have hr : row=(s,0) := Prod.ext hs hz
        rw [hr]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

/-- Native selector counters count the actual inspected prefix, with one
GCD per visit and no hidden second detector traversal. -/
theorem selectDetector_counts {S : Type*} (N : ℕ) (rows : List (S×ℕ)) :
    (selectDetector N rows).gcdCalls=(selectDetector N rows).visited.length ∧
      (selectDetector N rows).gcdCalls≤rows.length ∧
      (selectDetector N rows).visited=rows.take (selectDetector N rows).gcdCalls := by
  induction rows with
  | nil => simp only [selectDetector,List.length_nil,List.take_nil,le_refl,and_self]
  | cons row tail ih =>
    unfold selectDetector
    split
    · exact ⟨rfl,by dsimp only [List.length_cons]; omega,rfl⟩
    · split
      · exact ⟨rfl,by dsimp only [List.length_cons]; omega,rfl⟩
      · dsimp only [List.length_cons]
        rw [List.take_succ_cons,← ih.2.2]
        exact ⟨by omega,by omega,rfl⟩

/-- A successful detector member forces a stopping selection, preserving
any earlier stopping outcome. This is a universal list theorem. -/
theorem selectDetector_of_member {S : Type*} {N : ℕ} {rows : List (S×ℕ)}
    {row : S×ℕ} (hrow : row∈rows) (hsuccess : checkedSignal N row.2≠none ∨ row.2=0) :
    (selectDetector N rows).outcome≠none := by
  induction rows with
  | nil => cases hrow
  | cons head tail ih =>
    unfold selectDetector
    cases hh : checkedSignal N head.2 with
    | some d => simp only [ne_eq,reduceCtorEq,not_false_eq_true]
    | none =>
      by_cases hz : head.2=0
      · simp only [if_pos hz,ne_eq,reduceCtorEq,not_false_eq_true]
      · rw [if_neg hz]
        rcases List.mem_cons.mp hrow with he | ht
        · subst head
          rcases hsuccess with hs | hs
          · exact False.elim (hs hh)
          · exact False.elim (hz hs)
        · exact ih ht

/-- Original derivative pair acquired by the literal four-state executor.
The original product is recomputed as internal state, not divided away. -/
def acquireSeedMarked {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (s : SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ)) : ZMod N×ZMod N :=
  let report := geometricJetRun ((seedBase g m : (ZMod N)ˣ) : ZMod N)
    (s.step : ZMod N) (seedLength m)
  (report.state.target,report.state.base)

/-- The actual singleton derivative acquisition is the original target
derivative and original logarithmic base derivative, including saturation. -/
theorem acquireSeedMarked_exact {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (s : SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ)) :
    acquireSeedMarked g m s=
      (targetDerivative ((seedBase g m : (ZMod N)ˣ) : ZMod N) (s.step : ZMod N) (seedLength m),
        baseDerivative ((seedBase g m : (ZMod N)ˣ) : ZMod N) (s.step : ZMod N) (seedLength m)) := by
  have hh := geometricJetRun_exact ((seedBase g m : (ZMod N)ˣ) : ZMod N)
    (s.step : ZMod N) (seedLength m)
  exact Prod.ext hh.2.1 hh.2.2.1

/-- A selected detector and only its actually requested marked scalars.
The established tag reader is still a semantic, noncomputable controller. -/
structure LazySeedReport (N : ℕ) where
  /-- Original native detector selection report. -/
  selection : DetectorScanReport (SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ))
  /-- The original selected seed and its computed marked derivative pair. -/
  requested : List (SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ)×(ZMod N×ZMod N))
  /-- First recovered factor, including a checked common-index sum candidate. -/
  factor : Option ℕ

/-- Feed one selected saturated seed's acquired derivatives to the existing
rich tagged reader. Proper detector factors bypass the acquisition callback.
This semantic adapter does not claim a complete physical controller clock. -/
noncomputable def lazySeedRecoveryWith {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (acquire : SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ) → ZMod N×ZMod N)
    (rows : List (SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ)×ℕ)) : LazySeedReport N :=
  let selection := selectDetector N rows
  match selection.outcome with
  | none => ⟨selection,[],none⟩
  | some (.factor d) => ⟨selection,[],some d⟩
  | some (.saturated s) =>
    let marked := acquire s
    let factor := match readSeedJet g m s (0,marked.1,marked.2) with
      | none => none
      | some (Sum.inl d) => some d
      | some (Sum.inr r) => recoverSeedSum N m s r
    ⟨selection,[(s,marked)],factor⟩

/-- Use the actual literal recurrence in the at-most-once marked callback. -/
noncomputable def lazySeedRecovery {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (rows : List (SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ)×ℕ)) : LazySeedReport N :=
  lazySeedRecoveryWith g m (acquireSeedMarked g m) rows

/-- At most one marked pair is requested for arbitrary rows and arbitrary
acquisition implementations; the bound follows from the actual call site. -/
theorem lazySeedRecoveryWith_request_bound {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (acquire : SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ) → ZMod N×ZMod N)
    (rows : List (SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ)×ℕ)) :
    (lazySeedRecoveryWith g m acquire rows).requested.length≤1 := by
  unfold lazySeedRecoveryWith
  dsimp only
  split <;> simp only [List.length_nil,List.length_cons] <;> omega

/-- The actual recurrence-backed adapter requests at most one original jet
pair. It does not eagerly construct the derivative batch for all seeds. -/
theorem lazySeedRecovery_request_bound {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (rows : List (SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ)×ℕ)) :
    (lazySeedRecovery g m rows).requested.length≤1 :=
  lazySeedRecoveryWith_request_bound g m _ rows

/-- The literal original detector rows retain every seed label. Their
acquisition is deliberately separate from the singleton marked callback. -/
def originalDetectorRows {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (xs : List (SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ))) :
    List (SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ)×ℕ) :=
  xs.map (fun s => (s,(intervalProduct ((seedBase g m : (ZMod N)ˣ) : ZMod N)
    (s.step : ZMod N) (seedLength m)).val))

/-- The literal detector batch has exactly the original number of labels. -/
theorem originalDetectorRows_length {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (xs : List (SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ))) :
    (originalDetectorRows g m xs).length=xs.length := by
  simp only [originalDetectorRows,List.length_map]

/-- Proper detector checks return the same factor tag before either
original derivative is inspected by the established seed reader. -/
theorem readSeed_of_detector_factor {N m d : ℕ} (g : (ZMod N)ˣ)
    (s : SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ))
    (h : checkedSignal N (intervalProduct ((seedBase g m : (ZMod N)ˣ) : ZMod N)
      (s.step : ZMod N) (seedLength m)).val=some d) : readSeed g m s=some (Sum.inl d) := by
  unfold checkedSignal at h
  split at h
  · rename_i hp
    cases h
    unfold readSeed SemiprimeWrapIndexRecovery.recoverTaggedInterval
      SemiprimeWrapIndexRecovery.recoverTaggedJet
    dsimp only
    rw [if_pos hp]
  · cases h

/-- A clear nonzero detector makes the established reader return none,
independently of any marked-derivative acquisition. -/
theorem readSeed_of_clear_nonzero {N m : ℕ} (g : (ZMod N)ˣ)
    (s : SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ))
    (hclear : checkedSignal N (intervalProduct ((seedBase g m : (ZMod N)ˣ) : ZMod N)
      (s.step : ZMod N) (seedLength m)).val=none)
    (hzero : intervalProduct ((seedBase g m : (ZMod N)ˣ) : ZMod N)
      (s.step : ZMod N) (seedLength m)≠0) : readSeed g m s=none := by
  have hn : ¬(1<N.gcd (intervalProduct ((seedBase g m : (ZMod N)ˣ) : ZMod N)
      (s.step : ZMod N) (seedLength m)).val ∧
      N.gcd (intervalProduct ((seedBase g m : (ZMod N)ˣ) : ZMod N)
        (s.step : ZMod N) (seedLength m)).val<N) := by
    intro hp
    rw [checkedSignal,if_pos hp] at hclear
    cases hclear
  unfold readSeed SemiprimeWrapIndexRecovery.recoverTaggedInterval
    SemiprimeWrapIndexRecovery.recoverTaggedJet
  dsimp only
  rw [if_neg hn,if_neg hzero]

/-- Exact acquired original derivatives restore the original saturated
seed reader. No divided half-product or unit ratio is used. -/
theorem readSeedJet_saturated_exact {N m : ℕ} (g : (ZMod N)ˣ)
    (s : SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ))
    (marked : ZMod N×ZMod N)
    (hmarked : marked=
      (targetDerivative ((seedBase g m : (ZMod N)ˣ) : ZMod N) (s.step : ZMod N) (seedLength m),
        baseDerivative ((seedBase g m : (ZMod N)ˣ) : ZMod N) (s.step : ZMod N) (seedLength m)))
    (hzero : intervalProduct ((seedBase g m : (ZMod N)ˣ) : ZMod N)
      (s.step : ZMod N) (seedLength m)=0) :
    readSeedJet g m s (0,marked.1,marked.2)=readSeed g m s := by
  rw [hmarked,← hzero]
  rfl

/-- For exact original detector rows, exact marked derivatives and a
successful original saturated reader, the lazy adapter is exactly the
established first-success seed scan. The saturation premise is discharged
from original local period data in the long-route theorem below. -/
theorem lazySeedRecoveryWith_exact {N : ℕ} (hN : 0<N) (g : (ZMod N)ˣ) (m : ℕ)
    (acquire : SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ) → ZMod N×ZMod N)
    (xs : List (SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ)))
    (hmarked : ∀ s∈xs, acquire s=
      (targetDerivative ((seedBase g m : (ZMod N)ˣ) : ZMod N) (s.step : ZMod N) (seedLength m),
        baseDerivative ((seedBase g m : (ZMod N)ˣ) : ZMod N) (s.step : ZMod N) (seedLength m)))
    (hsaturated : ∀ s∈xs, intervalProduct ((seedBase g m : (ZMod N)ˣ) : ZMod N)
      (s.step : ZMod N) (seedLength m)=0 → readSeed g m s≠none) :
    (lazySeedRecoveryWith g m acquire (originalDetectorRows g m xs)).factor=scanSeedSums g m xs := by
  let : NeZero N := ⟨hN.ne'⟩
  induction xs with
  | nil => rfl
  | cons s tail ih =>
    have ht := ih (fun t ht => hmarked t (List.mem_cons_of_mem _ ht))
      (fun t ht => hsaturated t (List.mem_cons_of_mem _ ht))
    have hPiff : (intervalProduct ((seedBase g m : (ZMod N)ˣ) : ZMod N)
        (s.step : ZMod N) (seedLength m)).val=0 ↔
        intervalProduct ((seedBase g m : (ZMod N)ˣ) : ZMod N)
          (s.step : ZMod N) (seedLength m)=0 := ZMod.val_eq_zero _
    cases hc : checkedSignal N (intervalProduct ((seedBase g m : (ZMod N)ˣ) : ZMod N)
      (s.step : ZMod N) (seedLength m)).val with
    | some d =>
      have hr := readSeed_of_detector_factor g s hc
      simp only [lazySeedRecoveryWith,originalDetectorRows,List.map_cons,selectDetector,hc,
        scanSeedSums,hr]
    | none =>
      by_cases hz : intervalProduct ((seedBase g m : (ZMod N)ˣ) : ZMod N)
        (s.step : ZMod N) (seedLength m)=0
      · have hv := hPiff.mpr hz
        have hr := readSeedJet_saturated_exact g s (acquire s) (hmarked s List.mem_cons_self) hz
        have hread := hsaturated s List.mem_cons_self hz
        cases ho : readSeed g m s with
        | none => exact False.elim (hread ho)
        | some outcome =>
          cases outcome <;> simp only [lazySeedRecoveryWith,originalDetectorRows,List.map_cons,
            selectDetector,hc,if_pos hv,hr,ho,scanSeedSums]
      · have hv : ¬(intervalProduct ((seedBase g m : (ZMod N)ˣ) : ZMod N)
          (s.step : ZMod N) (seedLength m)).val=0 := by
          intro hh
          exact hz (hPiff.mp hh)
        have hr := readSeed_of_clear_nonzero g s hc hz
        simp only [lazySeedRecoveryWith,originalDetectorRows,List.map_cons,selectDetector,hc,
          if_neg hv,scanSeedSums,hr] at ht ⊢
        cases ho : (selectDetector N (tail.map (fun s =>
          (s,(intervalProduct ((seedBase g m : (ZMod N)ˣ) : ZMod N)
            (s.step : ZMod N) (seedLength m)).val)))).outcome with
        | none => simpa only [ho] using ht
        | some outcome => cases outcome <;> simpa only [ho] using ht

/-- On the original long route the exact literal marked callback preserves
the complete original scan, for every original supplied seed list. -/
theorem long_lazySeedRecovery_exact {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : SemiprimeLocalOrderRouting.LongData g m)
    (xs : List (SemiprimeDenseRowCarries.ProgressionSeed ((ZMod (p*q))ˣ))) :
    (lazySeedRecovery (SemiprimeCentreFreeCover.projectedUnit g m) m
      (originalDetectorRows (SemiprimeCentreFreeCover.projectedUnit g m) m xs)).factor=
      scanSeedSums (SemiprimeCentreFreeCover.projectedUnit g m) m xs := by
  apply lazySeedRecoveryWith_exact (Nat.mul_pos hp.pos hq.pos)
  · intro s _
    exact acquireSeedMarked_exact _ _ s
  · intro s _ hz
    exact SemiprimeBitInverse.long_readSeed_saturated hp hq hpq hm g hlong s hz

/-- Ordered evaluated product of the fixed four-state transfer matrices.
This proof-side specification preserves multiplication order and is not
a claim that a fast polynomial backend has been implemented. -/
noncomputable def matrixJetRun {R : Type*} [CommRing R] (alpha x : R) :
    ℕ → Matrix (Fin 4) (Fin 4) R
  | 0 => 1
  | n+1 => Matrix.of (fun i j => (jetMatrix x i j).eval (alpha^n))*matrixJetRun alpha x n

/-- The complete ordered matrix product is exactly the actual scalar
recurrence on its rich initial state, without a determinant or channel loss. -/
theorem matrixJetRun_state {R : Type*} [CommRing R] (alpha x : R) (L : ℕ) :
    (matrixJetRun alpha x L).mulVec (jetVector (initialJet : GeometricJetState R))=
      jetVector (geometricJetRun alpha x L).state := by
  induction L with
  | zero => simp only [matrixJetRun,Matrix.one_mulVec,geometricJetRun]
  | succ n ih =>
    rw [matrixJetRun,← Matrix.mulVec_mulVec,ih,jetMatrix_step]
    rw [geometricJetRun]
    dsimp only
    rw [(geometricJetRun_exact alpha x n).2.2.2.2.1]

/-- Every original detector and derivative is an explicit component of
the fixed-degree transfer product, even at a saturated target. -/
theorem matrixJetRun_channels {R : Type*} [CommRing R] (alpha x : R) (L : ℕ) :
    (matrixJetRun alpha x L).mulVec (jetVector (initialJet : GeometricJetState R))=
      ![intervalProduct alpha x L,targetDerivative alpha x L,baseDerivative alpha x L,
        (L : R)*intervalProduct alpha x L] := by
  rw [matrixJetRun_state]
  obtain ⟨hP,hD,hE,hmarked,_,_⟩ := geometricJetRun_exact alpha x L
  simp only [jetVector,hP,hD,hE,hmarked]

/-- The actual literal marked acquisition has quadratic interval length,
not the square-root cost of a still-unimplemented fast transfer backend. -/
theorem literal_seed_marked_steps {N m : ℕ} (g : (ZMod N)ˣ)
    (s : SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ)) (hm : 4≤m) :
    2*m^2+2≤(geometricJetRun ((seedBase g m : (ZMod N)ˣ) : ZMod N)
      (s.step : ZMod N) (seedLength m)).steps ∧
      (geometricJetRun ((seedBase g m : (ZMod N)ˣ) : ZMod N)
        (s.step : ZMod N) (seedLength m)).steps≤4*m^2 := by
  rw [(geometricJetRun_exact _ _ _).2.2.2.2.2]
  exact seedLength_bounds hm

/-- At the actual matched public width the implemented literal marked
recurrence is quadratic in sixthWidth whenever its callback is requested.
The fixed-degree transfer structure is available for a faster backend. -/
theorem public_literal_seed_marked_steps {N : ℕ} (hN : 0<N)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth N) (g : (ZMod N)ˣ)
    (s : SemiprimeDenseRowCarries.ProgressionSeed ((ZMod N)ˣ)) :
    2*(SemiprimeLehmanCoverage.sixthWidth N)^2+2≤
      (geometricJetRun
        ((seedBase g (SemiprimeEuclidRowBudget.publicRowModulus N) : (ZMod N)ˣ) : ZMod N)
        (s.step : ZMod N)
        (seedLength (SemiprimeEuclidRowBudget.publicRowModulus N))).steps ∧
      (geometricJetRun
        ((seedBase g (SemiprimeEuclidRowBudget.publicRowModulus N) : (ZMod N)ˣ) : ZMod N)
        (s.step : ZMod N)
        (seedLength (SemiprimeEuclidRowBudget.publicRowModulus N))).steps≤
          16*(SemiprimeLehmanCoverage.sixthWidth N)^2 := by
  have hm := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hh := literal_seed_marked_steps g s (hB.trans hm.1)
  have hlo := Nat.pow_le_pow_left hm.1 2
  have hhi := Nat.pow_le_pow_left hm.2 2
  constructor <;> nlinarith [hh.1,hh.2]

/-- The lazy controller on the original long route succeeds on every
remaining distinct-prime ratio, with at most one marked acquisition request.
The detector source and literal/faster marked costs remain separate. -/
theorem long_lazySeedRecovery_complete {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : 4≤m) (hmprime : m.Prime)
    (hprefix : m^2≤p) (hN : m.Coprime (p*q)) (hsize : p*q≤m^6)
    (g : (ZMod (p*q))ˣ) (hlong : SemiprimeLocalOrderRouting.LongData g m) :
    let h := SemiprimeCentreFreeCover.projectedUnit g m
    let xs := SemiprimeDenseRowCarries.progressionSeeds h (p*q) m
    let out := lazySeedRecovery h m (originalDetectorRows h m xs)
    (∃ d, out.factor=some d ∧ ProperDivisor (p*q) d) ∧
      out.requested.length≤1 ∧ out.selection.gcdCalls≤m-1 := by
  dsimp only
  obtain ⟨d,hd⟩ := scanSeedSums_complete hp hq hpq hm hmprime hprefix hN hsize g hlong
  have he := long_lazySeedRecovery_exact hp hq hpq hm g hlong
    (SemiprimeDenseRowCarries.progressionSeeds
      (SemiprimeCentreFreeCover.projectedUnit g m) (p*q) m)
  refine ⟨⟨d,he.trans hd,scanSeedSums_sound _ _ hd⟩,lazySeedRecovery_request_bound _ _ _,?_⟩
  have hc := (selectDetector_counts (p*q) (originalDetectorRows
    (SemiprimeCentreFreeCover.projectedUnit g m) m
    (SemiprimeDenseRowCarries.progressionSeeds
      (SemiprimeCentreFreeCover.projectedUnit g m) (p*q) m))).2.1
  rw [originalDetectorRows_length,SemiprimeDenseRowCarries.progressionSeeds_length] at hc
  unfold lazySeedRecovery lazySeedRecoveryWith
  dsimp only
  split <;> exact hc

/-- The actual matched-width public long route after an unsuccessful
original prefix has a successful lazy semantic adapter, at most one marked
request and a linear number of actual native detector GCD calls. Neither
the original detector source nor the full recovery bit clock is priced here. -/
theorem actual_public_route_lazy_acquisition {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (hroute : SemiprimeWrapIndexRecovery.routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := SemiprimeCentreFreeCover.projectedUnit (ZMod.unitOfCoprime a hc) m
      let xs := SemiprimeDenseRowCarries.progressionSeeds h (p*q) m
      let out := lazySeedRecovery h m (originalDetectorRows h m xs)
      (∃ d, out.factor=some d ∧ ProperDivisor (p*q) d) ∧
        out.requested.length≤1 ∧ out.selection.gcdCalls≤m-1 ∧
          out.selection.gcdCalls≤2*SemiprimeLehmanCoverage.sixthWidth (p*q) := by
  have hd := SemiprimeWrapIndexRecovery.routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hd
  obtain ⟨hc,hlong⟩ := hd
  let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
  let g := ZMod.unitOfCoprime a hc
  have hN := Nat.mul_pos hp.pos hq.pos
  have hmBounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 4≤m := hB.trans hmBounds.1
  have hbudget : p*q≤m^6 := (SemiprimeLehmanCoverage.sixthWidth_upper (p*q)).trans
    (Nat.pow_le_pow_left hmBounds.1 6)
  have hcover : m^2<p*q := SemiprimeWideWrapCoverage.public_modulus_prefix_below_input hN hB
  have hprefix := SemiprimeStrassenPrefix.prefix_none_excludes_small_prime
    hcover hp (dvd_mul_right p q) hnone
  have hmprime : m.Prime := SemiprimeEuclidRowBudget.publicRowModulus_prime (p*q)
  have hcop := SemiprimeStrassenPrefix.prefix_none_coprime_integer hcover hnone hmprime.pos
    (by have hh := hmprime.two_le; nlinarith only [hh] : m≤m^2)
  obtain ⟨hfactor,hrequest,hgcd⟩ := long_lazySeedRecovery_complete hp hq hpq hm hmprime
    hprefix.le hcop.symm hbudget g hlong
  refine ⟨hc,hfactor,hrequest,hgcd,hgcd.trans ?_⟩
  exact (Nat.sub_le m 1).trans hmBounds.2

end RiemannGaussian.SemiprimeSeedLazyJets
