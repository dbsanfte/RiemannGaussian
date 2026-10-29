/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceUniversalHeight

/-! # Actual acquired parity supplier scratch and payload state
Every view below is built from the existing tracked suppliers and their actual
cached solves. There is no new parity solver or supplied state-height bound.
Cell counts are payload/allocation views; full heap/address simulation is separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceParityState
open scoped BigOperators
open SemiprimeBinomialExecution SemiprimeBinomialExecutionBounds
open SemiprimeBinomialExecutionTracked SemiprimeSourceUniversalHeight

/-- Original acquired kernel, cached once by acquireParity. -/
def kernel (A R : ℕ) : Array ℕ := (acquireChoose R A).coefficients
/-- Original acquired geometric target cache. -/
def targets (A R : ℕ) : Array ℤ := (acquireLower (sign A).1 R).coefficients
/-- The exact reverse target lookup used in acquireParity. -/
def target (A R k : ℕ) : ℤ := coeff (targets A R) (R-(k+1))
/-- The exact acquired cached solve prefix. -/
def solvePrefix (A R len : ℕ) : SolveRun := solve (kernel A R) (target A R) len

/-- Every actual Pascal row has its original fixed width. -/
@[simp] theorem choose_size (R a : ℕ) : (acquireChoose R a).coefficients.size=R+1 := by
  rw [acquireChoose_value,chooseRow_size]

/-- EVERY acquired Pascal depth and zero-extended coordinate has the original bound. -/
theorem pascal_prefix_bound (A R a i : ℕ) (ha : a≤ A) :
    natCoeff (acquireChoose R a).coefficients i≤2^A := by
  by_cases hi : i≤ R
  · exact (acquired_kernel_bound a R i hi).trans (Nat.pow_le_pow_right (by decide) ha)
  · have hz : (acquireChoose R a).coefficients.size≤ i := by rw [choose_size];omega
    simp only [natCoeff,Array.getElem?_eq_none hz,Option.getD_none]
    exact Nat.zero_le _

/-- The raw next Pascal addition equals the actual successor entry, before any cancellation. -/
theorem pascal_update_eq (R a i : ℕ) (hi : i≤ R) :
    natCoeff (acquireChoose R a).coefficients i+
      (if i=0 then 0 else natCoeff (acquireChoose R a).coefficients (i-1))=
      natCoeff (acquireChoose R (a+1)).coefficients i := by
  simp only [acquireChoose,natCoeff,Array.getElem?_ofFn,dite_eq_left (by omega : i< R+1),Option.getD_some]

/-- All actual Pascal update inputs AND their raw sum have the original cap. -/
theorem pascal_update_bound (A R a i : ℕ) (ha : a< A) (hi : i≤ R) :
    natCoeff (acquireChoose R a).coefficients i≤2^A ∧
    (if i=0 then 0 else natCoeff (acquireChoose R a).coefficients (i-1))≤2^A ∧
    natCoeff (acquireChoose R a).coefficients i+
      (if i=0 then 0 else natCoeff (acquireChoose R a).coefficients (i-1))≤2^A := by
  refine ⟨pascal_prefix_bound A R a i (by omega),?_,?_⟩
  · split
    · exact Nat.zero_le _
    · exact pascal_prefix_bound A R a (i-1) (by omega)
  · rw [pascal_update_eq R a i hi]
    exact pascal_prefix_bound A R (a+1) i (by omega)

/-- Every actual sign recursion prefix remains a unit integer. -/
theorem sign_prefix (A a : ℕ) (ha : a≤ A) : |(sign a).1|=1 ∧ (sign a).2≤ A := by
  rw [sign_value,sign_work]
  exact ⟨by simp,ha⟩

/-- Every cached next target, including the final extra power, has the original cap. -/
theorem lower_next_bound (A R len : ℕ) (hlen : len≤ R) :
    |(acquireLower (sign A).1 len).next|≤(2^R:ℕ) := by
  rw [acquiredLower_next_bound A len]
  exact_mod_cast Nat.pow_le_pow_right (by decide : 0<2) hlen

/-- Every acquired target array prefix, including zero extension, has its original cap. -/
theorem lower_prefix_bound (A R len i : ℕ) (hlen : len≤ R) :
    |coeff (acquireLower (sign A).1 len).coefficients i|≤(2^R:ℕ) := by
  by_cases hi : i< len
  · rw [acquireLower_value _ _ _ hi,sign_value]
    exact (lower_abs A i).le.trans (by exact_mod_cast Nat.pow_le_pow_right (by decide : 0<2) (by omega : i≤ R))
  · have hz : (acquireLower (sign A).1 len).coefficients.size≤ i := by rw [acquireLower_size];omega
    simp only [coeff,Array.getElem?_eq_none hz,Option.getD_none,abs_zero]
    positivity

/-- The ACTUAL next multiplication, not only a retained target coefficient, is bounded. -/
theorem lower_product_bound (A R len : ℕ) (hlen : len< R) :
    |(acquireLower (sign A).1 len).next*(-2)|≤(2^R:ℕ) := by
  have h := lower_next_bound A R (len+1) (by omega)
  exact h

/-- Original numeric envelope for all actual acquired solve prefixes. -/
def solveCap (A R : ℕ) : ℕ := 2^R*solveBase R (2^A)^R

/-- Uniform original bound for EVERY cached solve coefficient and zero extension. -/
theorem solve_prefix_bound (A R len i : ℕ) (hlen : len≤ R) :
    |coeff (solvePrefix A R len).coefficients i|≤(solveCap A R:ℕ) := by
  by_cases hi : i< len
  · have h := acquired_solve_prefix_bound A R len hlen i hi
    have hp : solveBase R (2^A)^len≤ solveBase R (2^A)^R := Nat.pow_le_pow_right (by unfold solveBase;omega) hlen
    exact h.trans (by exact_mod_cast Nat.mul_le_mul_left (2^R) hp)
  · have hz : (solvePrefix A R len).coefficients.size≤ i := by rw [solvePrefix,solve_size];omega
    simp only [coeff,Array.getElem?_eq_none hz,Option.getD_none,abs_zero]
    positivity

/-- Every actual integer product entering a cached solve dot is bounded. -/
theorem solve_product_bound (A R len i : ℕ) (hlen : len≤ R) :
    |(natCoeff (kernel A R) (len-i):ℤ)*coeff (solvePrefix A R len).coefficients i|≤
      (2^A*solveCap A R:ℕ) := by
  rw [abs_mul,Int.abs_natCast]
  have hk : (natCoeff (kernel A R) (len-i):ℤ)≤((2^A:ℕ):ℤ) := by
    exact_mod_cast pascal_prefix_bound A R A (len-i) le_rfl
  have hm : (natCoeff (kernel A R) (len-i):ℤ)*|coeff (solvePrefix A R len).coefficients i|≤
      ((2^A:ℕ):ℤ)*((solveCap A R:ℕ):ℤ) :=
    mul_le_mul hk (solve_prefix_bound A R len i hlen) (abs_nonneg _) (by positivity)
  exact_mod_cast hm

/-- Every actual dot accumulator has a cancellation-independent original bound. -/
theorem solve_dot_bound (A R len m : ℕ) (hlen : len≤ R) (hm : m≤ len) :
    |(dot (kernel A R) (solvePrefix A R len).coefficients len m).value|≤
      (R*2^A*solveCap A R:ℕ) := by
  have h := dot_bound (kernel A R) (solvePrefix A R len).coefficients len m (2^A) (solveCap A R)
    (fun i _ => pascal_prefix_bound A R A (len-i) le_rfl)
    (fun i _ => solve_prefix_bound A R len i hlen)
  exact h.trans (by exact_mod_cast Nat.mul_le_mul_right _ (Nat.mul_le_mul_right (2^A) (hm.trans hlen)))

/-- The raw appended subtraction is itself an actual bounded successor coefficient. -/
theorem solve_subtraction_bound (A R len : ℕ) (hlen : len< R) :
    |target A R len-(dot (kernel A R) (solvePrefix A R len).coefficients len len).value|≤
      (solveCap A R:ℕ) := by
  have h := solve_prefix_bound A R (len+1) len (by omega)
  rw [solvePrefix,solve_new,← dot_value] at h
  exact h

/-- Payload cells of a literal list of ACTUAL returned arrays; no sharing is assumed. -/
def arrayCells {α : Type} (xs : List (Array α)) : ℕ := (xs.map Array.size).sum

/-- All actual Pascal return caches, including depth zero. -/
def pascalCaches (A R : ℕ) : List (Array ℕ) :=
  List.ofFn (fun a : Fin (A+1) => (acquireChoose R a.val).coefficients)
/-- All actual acquired target return caches, including the empty initial cache. -/
def lowerCaches (A R : ℕ) : List (Array ℤ) :=
  List.ofFn (fun len : Fin (R+1) => (acquireLower (sign A).1 len.val).coefficients)
/-- All actual solved return caches, including the empty initial prefix. -/
def solveCaches (A R : ℕ) : List (Array ℤ) :=
  List.ofFn (fun len : Fin (R+1) => (solvePrefix A R len.val).coefficients)

/-- Literal allocation/return payload of every Pascal depth has exact size. -/
theorem pascal_cells (A R : ℕ) : arrayCells (pascalCaches A R)=(A+1)*(R+1) := by
  simp [arrayCells,pascalCaches,List.map_ofFn,List.sum_ofFn]
  ring

/-- The actual Pascal additions pay every new row after the initial row. -/
theorem pascal_cells_le_work (A R : ℕ) :
    arrayCells (pascalCaches A R)≤(acquireChoose R A).additions+(R+1) := by
  rw [pascal_cells,(acquireChoose_work R A).1]
  nlinarith

/-- All actual target-return array cells have a quadratic original-length bound. -/
theorem lower_cells (A R : ℕ) : arrayCells (lowerCaches A R)≤(R+1)*R := by
  simp only [arrayCells,lowerCaches,List.map_ofFn,List.sum_ofFn,Function.comp_def,acquireLower_size]
  calc
    _ ≤ ∑ _i : Fin (R+1),R := Finset.sum_le_sum (fun i _ => by omega)
    _ = _ := by simp

/-- Retained next target scalars add one per actual return, and are paid polynomially. -/
theorem lower_cells_le_work (A R : ℕ) :
    arrayCells (lowerCaches A R)+(R+1)≤((acquireLower (sign A).1 R).arithmetic+1)^2 := by
  have hh := lower_cells A R
  rw [acquireLower_work]
  nlinarith

/-- Actual solve return arrays have no more than R slots each. -/
theorem solve_cells (A R : ℕ) : arrayCells (solveCaches A R)≤(R+1)*R := by
  simp only [arrayCells,solveCaches,List.map_ofFn,List.sum_ofFn,Function.comp_def,solvePrefix,solve_size]
  calc
    _ ≤ ∑ _i : Fin (R+1),R := Finset.sum_le_sum (fun i _ => by omega)
    _ = _ := by simp

/-- Actual cached solve arithmetic pays its full return-array payload up to linear slack. -/
theorem solve_cells_le_work (A R : ℕ) :
    arrayCells (solveCaches A R)≤(solvePrefix A R R).arithmetic+R+1 := by
  have hh := solve_cells A R
  rw [solvePrefix,(solve_work _ _ R).1]
  nlinarith

/-- Old/new Pascal row payload, allowing every computed new-prefix cell to coexist. -/
theorem pascal_simultaneous_cells (R a k : ℕ) (hk : k≤ R+1) :
    (acquireChoose R a).coefficients.size+k≤2*(R+1) := by
  rw [choose_size]
  omega

/-- Actual target old/new prefix payload plus both cached next scalars. -/
theorem lower_simultaneous_cells (A R len : ℕ) (hlen : len< R) :
    (acquireLower (sign A).1 len).coefficients.size+
      (acquireLower (sign A).1 (len+1)).coefficients.size+2≤2*R+2 := by
  rw [acquireLower_size,acquireLower_size]
  omega

/-- All actually returned dot accumulators in one solve frame. -/
def dotReturns (A R len : ℕ) : List ℤ :=
  List.ofFn (fun m : Fin (len+1) => (dot (kernel A R) (solvePrefix A R len).coefficients len m.val).value)

/-- Actual frame payload includes kernel, target, old/new solve arrays, ALL
dot-return scalars and two extra product/subtraction scratch scalars. -/
def solveFrameCells (A R len : ℕ) : ℕ :=
  (kernel A R).size+(targets A R).size+(solvePrefix A R len).coefficients.size+
    (solvePrefix A R (len+1)).coefficients.size+(dotReturns A R len).length+2

/-- A simultaneous acquired solve frame has a bound in original R alone. -/
theorem solve_frame_cells (A R len : ℕ) (hlen : len≤ R) :
    solveFrameCells A R len≤5*R+5 := by
  simp only [solveFrameCells,kernel,targets,choose_size,acquireLower_size,solvePrefix,solve_size,
    dotReturns,List.length_ofFn]
  omega

/-- All actually returned sign-prefix scalar values. -/
def signReturns (A : ℕ) : List ℤ := List.ofFn (fun a : Fin (A+1) => (sign a.val).1)

/-- Sign-return storage is exactly its actual negation count plus its initial scalar. -/
theorem sign_cells (A : ℕ) : (signReturns A).length=(sign A).2+1 := by
  simp [signReturns,sign_work]

/-- Conservative complete supplier payload view: all Pascal/target/sign
return caches, every solve frame, and the actual final output array. -/
def supplierCells (A R : ℕ) : ℕ :=
  arrayCells (pascalCaches A R)+arrayCells (lowerCaches A R)+(R+1)+(signReturns A).length+
    ((List.ofFn (fun len : Fin R => solveFrameCells A R len.val)).sum)+
    (acquireParity A R).coefficients.size+1

/-- The final tracked output has the original exact requested finite size. -/
@[simp] theorem parity_size (A R : ℕ) : (acquireParity A R).coefficients.size=R := by
  simp only [acquireParity,solve_size]

/-- All actual supplier return and simultaneous-cache payload is polynomial
in original dimensions, without a desired-state premise. -/
theorem supplier_cells (A R : ℕ) : supplierCells A R≤10*(A+R+2)^2 := by
  have hp := pascal_cells A R
  have hl := lower_cells A R
  have hs : (List.ofFn (fun len : Fin R => solveFrameCells A R len.val)).sum≤ R*(5*R+5) := by
    rw [List.sum_ofFn]
    calc
      _ ≤ ∑ _i : Fin R,(5*R+5) := Finset.sum_le_sum (fun (i : Fin R) _ => solve_frame_cells A R i.val (by omega))
      _ = _ := by simp
  unfold supplierCells
  rw [hp,parity_size,sign_cells,sign_work]
  nlinarith

/-- The actual acquired arithmetic/read ledger also supplies a polynomial
allocation bound, including initial-cell slack and no assumed cache budget. -/
theorem supplier_cells_le_work (A R : ℕ) :
    supplierCells A R≤10*((acquireParity A R).arithmetic+(acquireParity A R).reads+2)^2 := by
  have h := acquireParity_work A R
  have hd : A+R+2≤(acquireParity A R).arithmetic+(acquireParity A R).reads+2 := by
    rw [h.1,h.2]
    nlinarith
  exact (supplier_cells A R).trans (Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left hd 2))

/-- The raw next dot addition is an ACTUAL successor accumulator. -/
theorem solve_dot_add_bound (A R len m : ℕ) (hlen : len≤ R) (hm : m< len) :
    |(dot (kernel A R) (solvePrefix A R len).coefficients len m).value+
      (natCoeff (kernel A R) (len-m):ℤ)*coeff (solvePrefix A R len).coefficients m|≤
      (R*2^A*solveCap A R:ℕ) :=
  solve_dot_bound A R len (m+1) hlen (by omega)

/-- One original-data magnitude covers kernel, sign, target, solve and all raw
product/addition/subtraction operands/results. -/
def stateMagnitude (A R : ℕ) : ℕ :=
  2^A+2^R+solveCap A R+(R+1)*2^A*solveCap A R+2

/-- Every individual stage envelope is included in the original-data magnitude. -/
theorem magnitude_caps (A R : ℕ) :
    1≤ stateMagnitude A R ∧ 2^A≤ stateMagnitude A R ∧ 2^R≤ stateMagnitude A R ∧
    solveCap A R≤ stateMagnitude A R ∧ 2^A*solveCap A R≤ stateMagnitude A R ∧
    R*2^A*solveCap A R≤ stateMagnitude A R := by
  have hp : 2^A*solveCap A R≤(R+1)*2^A*solveCap A R := by
    calc
      _ = 1*2^A*solveCap A R := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (show 1≤ R+1 by omega))
  have hr : R*2^A*solveCap A R≤(R+1)*2^A*solveCap A R :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ R))
  unfold stateMagnitude
  generalize (2:ℕ)^A=p at *
  generalize (2:ℕ)^R=z at *
  generalize solveCap A R=s at *
  omega

/-- Original solve cache magnitudes have the same polynomial exponent as the
already proved acquired parity coefficients. -/
theorem solveCap_dyadic (A R : ℕ) : solveCap A R≤2^coefficientExponent A R := by
  have hbase : solveBase R (2^A)≤2^(A+Nat.clog 2 (R+1)) := by
    unfold solveBase
    calc
      R*2^A+1≤(R+1)*2^A := by have hp : 1≤2^A := Nat.one_le_two_pow; nlinarith
      _ ≤ 2^Nat.clog 2 (R+1)*2^A := Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) _)
      _ = _ := by rw [pow_add];ring
  calc
    solveCap A R = 2^R*solveBase R (2^A)^R := rfl
    _ ≤ 2^R*(2^(A+Nat.clog 2 (R+1)))^R := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase R)
    _ = _ := by
      rw [← pow_mul,← pow_add]
      congr 1
      unfold coefficientExponent
      ring

/-- Explicit binary exponent of EVERY actual acquired parity arithmetic frame. -/
def stateBits (A R : ℕ) : ℕ := A+R+coefficientExponent A R+Nat.clog 2 (R+1)+4

/-- The aggregate raw/cached magnitude has a polynomial ORIGINAL bit bound. -/
theorem magnitude_dyadic (A R : ℕ) : stateMagnitude A R≤2^stateBits A R := by
  let e := A+R+coefficientExponent A R+Nat.clog 2 (R+1)+1
  have ha : 2^A≤2^e := Nat.pow_le_pow_right (by decide) (by dsimp [e];omega)
  have hr : 2^R≤2^e := Nat.pow_le_pow_right (by decide) (by dsimp [e];omega)
  have hs : solveCap A R≤2^e := (solveCap_dyadic A R).trans
    (Nat.pow_le_pow_right (by decide) (by dsimp [e];omega))
  have hp : (R+1)*2^A*solveCap A R≤2^e := by
    calc
      _ ≤ 2^Nat.clog 2 (R+1)*2^A*2^coefficientExponent A R :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) _)) (solveCap_dyadic A R)
      _ = 2^(Nat.clog 2 (R+1)+A+coefficientExponent A R) := by rw [← pow_add,← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by dsimp [e];omega)
  have ht : 2≤2^e := by
    simpa only [pow_one] using (Nat.pow_le_pow_right (by decide : 0<2) (show 1≤ e by dsimp [e];omega))
  have he : stateBits A R=e+3 := by rfl
  unfold stateMagnitude
  rw [he,pow_add]
  norm_num only
  omega

/-- This numeric exponent is bounded by a fixed polynomial of original A,R. -/
theorem stateBits_polynomial (A R : ℕ) :
    stateBits A R≤ A+R+R*(A+(R+1)+1)+(R+1)+4 := by
  have h := SemiprimeHermiteArrayHeight.clog_two_le_self (R+1)
  unfold stateBits coefficientExponent
  gcongr

/-- A proof-only exhaustive family of scalar values appearing in the ACTUAL
supplier recursions. Constructors contain only original prefix indices. -/
inductive ScalarFrame (A R : ℕ) : ℤ → Prop
  | literalNegTwo : ScalarFrame A R (-2)
  | pascal (a i : ℕ) (ha : a≤ A) : ScalarFrame A R (natCoeff (acquireChoose R a).coefficients i)
  | pascalAdd (a i : ℕ) (ha : a< A) (hi : i≤ R) : ScalarFrame A R
      (natCoeff (acquireChoose R a).coefficients i+
        (if i=0 then 0 else natCoeff (acquireChoose R a).coefficients (i-1)):ℕ)
  | phase (a : ℕ) (ha : a≤ A) : ScalarFrame A R (sign a).1
  | lowerEntry (len i : ℕ) (hlen : len≤ R) : ScalarFrame A R (coeff (acquireLower (sign A).1 len).coefficients i)
  | lowerNext (len : ℕ) (hlen : len≤ R) : ScalarFrame A R (acquireLower (sign A).1 len).next
  | lowerProduct (len : ℕ) (hlen : len< R) : ScalarFrame A R ((acquireLower (sign A).1 len).next*(-2))
  | solved (len i : ℕ) (hlen : len≤ R) : ScalarFrame A R (coeff (solvePrefix A R len).coefficients i)
  | product (len i : ℕ) (hlen : len≤ R) : ScalarFrame A R
      ((natCoeff (kernel A R) (len-i):ℤ)*coeff (solvePrefix A R len).coefficients i)
  | accumulator (len m : ℕ) (hlen : len≤ R) (hm : m≤ len) : ScalarFrame A R
      (dot (kernel A R) (solvePrefix A R len).coefficients len m).value
  | dotAdd (len m : ℕ) (hlen : len≤ R) (hm : m< len) : ScalarFrame A R
      ((dot (kernel A R) (solvePrefix A R len).coefficients len m).value+
        (natCoeff (kernel A R) (len-m):ℤ)*coeff (solvePrefix A R len).coefficients m)
  | subtraction (len : ℕ) (hlen : len< R) : ScalarFrame A R
      (target A R len-(dot (kernel A R) (solvePrefix A R len).coefficients len len).value)

/-- ALL actual arithmetic families in the acquired supplier have an original
magnitude cap; there is no scalar/state-height advice in the constructors. -/
theorem scalar_frame_bound {A R : ℕ} {z : ℤ} (h : ScalarFrame A R z) :
    |z|≤(stateMagnitude A R:ℕ) := by
  have hc := magnitude_caps A R
  cases h with
  | literalNegTwo =>
    change (2:ℤ)≤(stateMagnitude A R:ℕ)
    have hh : 2≤ stateMagnitude A R := by unfold stateMagnitude;exact Nat.le_add_left 2 _
    exact_mod_cast hh
  | pascal a i ha =>
    rw [Int.abs_natCast]
    exact_mod_cast (pascal_prefix_bound A R a i ha).trans hc.2.1
  | pascalAdd a i ha hi =>
    rw [Int.abs_natCast]
    exact_mod_cast (pascal_update_bound A R a i ha hi).2.2.trans hc.2.1
  | phase a ha => rw [(sign_prefix A a ha).1];exact_mod_cast hc.1
  | lowerEntry len i hlen => exact (lower_prefix_bound A R len i hlen).trans (by exact_mod_cast hc.2.2.1)
  | lowerNext len hlen => exact (lower_next_bound A R len hlen).trans (by exact_mod_cast hc.2.2.1)
  | lowerProduct len hlen => exact (lower_product_bound A R len hlen).trans (by exact_mod_cast hc.2.2.1)
  | solved len i hlen => exact (solve_prefix_bound A R len i hlen).trans (by exact_mod_cast hc.2.2.2.1)
  | product len i hlen => exact (solve_product_bound A R len i hlen).trans (by exact_mod_cast hc.2.2.2.2.1)
  | accumulator len m hlen hm => exact (solve_dot_bound A R len m hlen hm).trans (by exact_mod_cast hc.2.2.2.2.2)
  | dotAdd len m hlen hm => exact (solve_dot_add_bound A R len m hlen hm).trans (by exact_mod_cast hc.2.2.2.2.2)
  | subtraction len hlen => exact (solve_subtraction_bound A R len hlen).trans (by exact_mod_cast hc.2.2.2.1)

/-- The same aggregate families have derived ORIGINAL binary-length bounds. -/
theorem scalar_frame_bits {A R : ℕ} {z : ℤ} (h : ScalarFrame A R z) :
    z.natAbs≤2^stateBits A R ∧ Nat.clog 2 (z.natAbs+1)≤ stateBits A R+1 := by
  have hm : z.natAbs≤ stateMagnitude A R := by
    have hh : (z.natAbs:ℤ)≤(stateMagnitude A R:ℕ) := by
      simpa only [Int.natCast_natAbs] using scalar_frame_bound h
    exact_mod_cast hh
  have hd := hm.trans (magnitude_dyadic A R)
  exact ⟨hd,SemiprimeHermiteArrayHeight.clog_two_succ_of_dyadic hd⟩

/-- The actual final acquired integer coefficient is an aggregate bounded frame,
not an assumed member of the scalar-state family. Zero extension is included. -/
theorem acquired_output_frame (A R i : ℕ) :
    ScalarFrame A R (coeff (acquireParity A R).coefficients i) := by
  exact ScalarFrame.solved R i le_rfl

/-- Original-input binary bounds for every actual acquired output coefficient. -/
theorem acquired_output_bits (A R i : ℕ) :
    (coeff (acquireParity A R).coefficients i).natAbs≤2^stateBits A R ∧
      Nat.clog 2 ((coeff (acquireParity A R).coefficients i).natAbs+1)≤ stateBits A R+1 :=
  scalar_frame_bits (acquired_output_frame A R i)

/-- All actual arithmetic/read counters at EVERY supplier prefix have closed
original-dimension bounds. These are metadata VALUES, not a unit-cost promise. -/
theorem prefix_counter_bounds (A R a len m : ℕ) (ha : a≤ A) (hlen : len≤ R) (hm : m≤ len) :
    (acquireChoose R a).additions≤ A*(R+1) ∧
    (acquireChoose R a).reads≤2*A*(R+1) ∧
    (sign a).2≤ A ∧ (acquireLower (sign A).1 len).arithmetic≤ R ∧
    (solvePrefix A R len).arithmetic≤ R^2 ∧ (solvePrefix A R len).reads≤ R^2 ∧
    (dot (kernel A R) (solvePrefix A R len).coefficients len m).arithmetic≤2*R ∧
    (dot (kernel A R) (solvePrefix A R len).coefficients len m).reads≤2*R := by
  have hp := acquireChoose_work R a
  have hs := solve_work (kernel A R) (target A R) len
  have hd := dot_work (kernel A R) (solvePrefix A R len).coefficients len m
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hp.1]
    exact Nat.mul_le_mul_right _ ha
  · rw [hp.2]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 ha)
  · rw [sign_work]
    exact ha
  · rw [acquireLower_work]
    exact hlen
  · exact hs.1.le.trans (Nat.pow_le_pow_left hlen 2)
  · exact hs.2.le.trans (Nat.pow_le_pow_left hlen 2)
  · exact hd.1.le.trans (Nat.mul_le_mul_left 2 (hm.trans hlen))
  · exact hd.2.le.trans (Nat.mul_le_mul_left 2 (hm.trans hlen))

end RiemannGaussian.SemiprimeSourceParityState
