/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeLocalArrayFrontend
import RiemannGaussian.SemiprimeFibreArrayExecution

/-!
# Actual native local factors supply the group callback

Grouped Boolean bases are materialized once. Factors are traversed by their
literal Fin indices, with unassigned factors returning one. No groupValue or
whole-fibre answer is a runtime argument.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeNativeGroupExecution
open scoped BigOperators
open Polynomial
open SemiprimeJetArray SemiprimeArrayOps SemiprimeLocalArrayFrontend
open SemiprimeCounterCompose SemiprimeCounterPacketHeight SemiprimeFibreArrayExecution

/-- Conservative finite control/allocation charge for the executed local frontend. -/
def localControl (n w R J : ℕ) : ℕ :=
  (n + 1) * (w + 1) * (R + 1) * (J + 1) + 2 ^ (w + 1) * (w + J + 1)

/-- Wrap the ACTUAL local evaluator, retaining all rational/read work. -/
def localRun {n : ℕ} (w J R : ℕ) (t : ℚ)
    (source : Fin w → Fin n → Array ℚ) (base correction : Fin n → Bool)
    (T : (Fin w → Bool) → EntryReport) : Run :=
  let out := nativeLocal w J R t source base correction T
  ⟨out, out.arithmetic + out.reads + localControl n w R J⟩

theorem localRun_spec {n : ℕ} (w J R : ℕ) (t : ℚ)
    (source : Fin w → Fin n → Array ℚ) (rows : Fin w → Fin n → Polynomial ℚ)
    (hrows : ∀ v i, (rows v i).natDegree ≤ R)
    (hsource : ∀ v i k, k ≤ R → coefficient (source v i) k = (rows v i).coeff k)
    (x U : Finset (Fin n)) (T : (Fin w → Bool) → EntryReport) :
    Spec J (localRun w J R t source (fun v => decide (v ∈ x)) (fun v => decide (v ∈ U)) T)
      (SemiprimeStreamingTensor.evaluate w (fun eta => C ((T eta).value : ℚ))
        (fun v => correctedPort (rows v) t R x U)) :=
  specification_of_asPolynomial _ _ _ (nativeLocal_correct w J R t source rows hrows hsource x U T)

/-- Polynomial factors multiplying the sole local 2^w truth traversal. -/
def localBudget (n w R J A : ℕ) : ℕ :=
  2 * (w * (n * ((R + 1) * (J * (J + 1) + 2 * J) + J)) +
    w * (n * ((R + 1) * (J * (J + 1) + 3 * J + 1) + 3 * J)) +
    2 * (2 ^ w * (A + (w + 1) * localOverhead J + J))) + localControl n w R J

theorem localRun_work {n : ℕ} (w J R A : ℕ) (t : ℚ)
    (source : Fin w → Fin n → Array ℚ) (base correction : Fin n → Bool)
    (T : (Fin w → Bool) → EntryReport)
    (hT : ∀ eta, (T eta).arithmetic ≤ A ∧ (T eta).reads ≤ A) :
    (localRun w J R t source base correction T).work ≤ localBudget n w R J A := by
  have h := nativeLocal_work w J R A t source base correction T hT
  simp only [Run.work, localRun]
  unfold localBudget
  omega

variable {G : Type} [DecidableEq G] {L : G → Type}

/-- Concrete original-coordinate Boolean base, read from grouped bits. -/
def baseBits {n : ℕ} (grouping : Fin n ≃ Sigma L) (a : (g : G) → L g → Bool) : Fin n → Bool :=
  fun v => a (grouping v).1 (grouping v).2

/-- Actual group callback: cache base bits and multiply gated native local calls. -/
def nativeGroup {n F : ℕ} (arity : Fin F → ℕ) (J R : ℕ) (t : ℚ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (grouping : Fin n ≃ Sigma L) (assigned : Fin F → G)
    (correction : Fin n → Bool) (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (g : G) (a : (g : G) → L g → Bool) : Run :=
  let bits := Array.ofFn (baseBits grouping a)
  let getBit := fun v : Fin n => bits[v.val]'(by simp [bits])
  let result := productList J (List.ofFn (fun e : Fin F => e)) (fun e =>
    if assigned e = g then localRun (arity e) J R t (source e) getBit correction (T e) else oneRun J)
  ⟨result.jet, result.control + n + F + 2⟩

/-- Native grouped polynomial rows, with no representative/value acquisition. -/
noncomputable def groupedSource {n F : ℕ} (arity : Fin F → ℕ)
    (rows : (e : Fin F) → Fin (arity e) → Fin n → Polynomial ℚ)
    (t : ℚ) (grouping : Fin n ≃ Sigma L) :
    (e : Fin F) → Fin (arity e) → (g : G) → L g → ℚ :=
  fun e i g v => (rows e i (grouping.symm ⟨g, v⟩)).eval t

omit [DecidableEq G] in
/-- Cached base bits and the proof-only finite-set base are extensionally identical. -/
theorem baseBits_set {n : ℕ} (grouping : Fin n ≃ Sigma L) (a : (g : G) → L g → Bool) :
    (fun v : Fin n => decide (v ∈ (splitAssignment grouping).symm a)) = baseBits grouping a := by
  funext v
  simp [splitAssignment, baseBits]

/-- The actual group callback computes a finite product of native corrected factors. -/
theorem nativeGroup_product_spec {n F : ℕ} (arity : Fin F → ℕ) (J R : ℕ) (t : ℚ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (rows : (e : Fin F) → Fin (arity e) → Fin n → Polynomial ℚ)
    (hrows : ∀ e i v, (rows e i v).natDegree ≤ R)
    (hsource : ∀ e i v k, k ≤ R → coefficient (source e i v) k = (rows e i v).coeff k)
    (grouping : Fin n ≃ Sigma L) (assigned : Fin F → G) (U : Finset (Fin n))
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (g : G) (a : (g : G) → L g → Bool) :
    Spec J (nativeGroup arity J R t source grouping assigned (fun v => decide (v ∈ U)) T g a)
      (∏ e ∈ Finset.univ.filter (fun e => assigned e = g),
        SemiprimeStreamingTensor.evaluate (arity e) (fun eta => C ((T e eta).value : ℚ))
          (fun i => correctedPort (rows e i) t R ((splitAssignment grouping).symm a) U)) := by
  classical
  let x := (splitAssignment grouping).symm a
  let p := fun e : Fin F => SemiprimeStreamingTensor.evaluate (arity e)
    (fun eta => C ((T e eta).value : ℚ)) (fun i => correctedPort (rows e i) t R x U)
  let bits := Array.ofFn (baseBits grouping a)
  let getBit := fun v : Fin n => bits[v.val]'(by simp [bits])
  have hb : getBit = fun v => decide (v ∈ x) := by
    funext v
    simp only [getBit, bits, Array.getElem_ofFn]
    exact (congrFun (baseBits_set grouping a) v).symm
  have hf (e : Fin F) (_he : e ∈ List.ofFn (fun e : Fin F => e)) :
      Spec J (if assigned e = g then localRun (arity e) J R t (source e) getBit
        (fun v => decide (v ∈ U)) (T e) else oneRun J) (if assigned e = g then p e else 1) := by
    by_cases he : assigned e = g
    · simp only [ite_eq_left he]
      rw [hb]
      exact localRun_spec (arity e) J R t (source e) (rows e) (hrows e) (hsource e) x U (T e)
    · simp only [ite_eq_right he]
      exact oneRun_spec J
  have hs := productList_spec J (List.ofFn (fun e : Fin F => e)) _
    (fun e => if assigned e = g then p e else 1) hf
  simp only [List.map_ofFn, List.prod_ofFn, Function.comp_apply] at hs
  have hp : (∏ e : Fin F, if assigned e = g then p e else 1) =
      ∏ e ∈ Finset.univ.filter (fun e => assigned e = g), p e := by
    exact (Finset.prod_filter (fun e => assigned e = g) p).symm
  rw [hp] at hs
  exact hs

/-- The supplied groupValue callback is eliminated for ANY actual node certificate. -/
theorem nativeGroup_node_spec {n F : ℕ} (arity : Fin F → ℕ) (J R : ℕ) (t : ℚ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (rows : (e : Fin F) → Fin (arity e) → Fin n → Polynomial ℚ)
    (hrows : ∀ e i v, (rows e i v).natDegree ≤ R)
    (hsource : ∀ e i v k, k ≤ R → coefficient (source e i v) k = (rows e i v).coeff k)
    (d : NodeCertificate arity (fun e i v => (rows e i v).eval t)) (U : Finset (Fin n))
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (g : d.Group) (a : (g : d.Group) → d.Local g → Bool) :
    Spec J (nativeGroup arity J R t source d.grouping d.assigned
      (fun v => decide (v ∈ U)) T g a)
      (SemiprimeCounterSeparation.groupValue arity (fun e eta => ((T e eta).value : ℚ)) d.assigned
        (groupedRows arity (fun e i v => (rows e i v).eval t) d)
        (nativeCorrection arity rows t R U) g a) := by
  let x := (splitAssignment d.grouping).symm a
  have he := groupValue_corrected_product arity (fun e eta => (T e eta).value) rows t R d g x U
  have ha : splitAssignment d.grouping x = a := (splitAssignment d.grouping).apply_symm_apply a
  rw [ha] at he
  rw [he]
  exact nativeGroup_product_spec arity J R t source rows hrows hsource d.grouping d.assigned U T g a

/-- Monotonicity of the explicit local ledger under an arity bound. -/
theorem localBudget_mono (n w W R J A : ℕ) (hw : w ≤ W) :
    localBudget n w R J A ≤ localBudget n W R J A := by
  unfold localBudget localControl
  gcongr

/-- Complete group callback work: only a polynomial factor-count multiplier is added. -/
theorem nativeGroup_work {n F : ℕ} (arity : Fin F → ℕ) (J R A W : ℕ) (t : ℚ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (grouping : Fin n ≃ Sigma L) (assigned : Fin F → G)
    (correction : Fin n → Bool) (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (g : G) (a : (g : G) → L g → Bool)
    (hW : ∀ e, arity e ≤ W)
    (hT : ∀ e eta, (T e eta).arithmetic ≤ A ∧ (T e eta).reads ≤ A) :
    (nativeGroup arity J R t source grouping assigned correction T g a).work ≤
      F * (localBudget n W R J A + J + 1 + (2 * J * (J + 1) + J + 1)) +
        (J + 1) + n + F + 2 := by
  let bits := Array.ofFn (baseBits grouping a)
  let getBit := fun v : Fin n => bits[v.val]'(by simp [bits])
  let callback := fun e : Fin F => if assigned e = g then
    localRun (arity e) J R t (source e) getBit correction (T e) else oneRun J
  have hc (e : Fin F) (_he : e ∈ List.ofFn (fun e : Fin F => e)) :
      (callback e).work ≤ localBudget n W R J A + J + 1 := by
    by_cases he : assigned e = g
    · simp only [callback, ite_eq_left he]
      exact (localRun_work (arity e) J R A t (source e) getBit correction (T e) (hT e)).trans
        ((localBudget_mono n (arity e) W R J A (hW e)).trans (by omega))
    · simp only [callback, ite_eq_right he, Run.work, oneRun, SemiprimeArrayOps.oneJet]
      omega
  have hs := productList_work J (localBudget n W R J A + J + 1)
    (List.ofFn (fun e : Fin F => e)) callback hc
  simp only [List.length_ofFn] at hs
  change (productList J _ callback).jet.arithmetic + (productList J _ callback).jet.reads +
    ((productList J _ callback).control + n + F + 2) ≤ _
  unfold Run.work at hs
  omega

end RiemannGaussian.SemiprimeNativeGroupExecution
