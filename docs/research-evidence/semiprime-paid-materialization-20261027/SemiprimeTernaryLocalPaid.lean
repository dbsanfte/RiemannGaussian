/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeStreamingTensor

/-!
# Paid Boolean ring interpolation with cached port complements

The actual fixed register programs use only negation, addition and
multiplication, matching finite-ring word backends. Each port complement is
materialized once before the two-branch traversal. Only Mathlib-backed generic
ring code is imported; this is not yet an upstream Cmd40 AssignmentContract.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeTernaryLocalPaid
open scoped BigOperators
variable {R : Type*} [CommRing R]

/-- Scalar opcodes available in the finite-ring word interface. -/
inductive Opcode where
  | neg
  | mul
  | add
  deriving DecidableEq, Repr

/-- Exact scalar meaning; the second operand of negation is ignored. -/
def meaning (op : Opcode) (a b : R) : R := match op with
  | .neg => -a
  | .mul => a*b
  | .add => a+b

/-- One literal instruction appending its result to the retained registers. -/
structure Instruction where
  /-- Scalar backend opcode. -/
  op : Opcode
  /-- First cached register. -/
  left : ℕ
  /-- Second cached register. -/
  right : ℕ
  deriving Repr

/-- Input1,x becomes the cached complement1−x in register3. -/
def complementProgram : List Instruction := [⟨.neg,1,1⟩,⟨.add,0,2⟩]
/-- Inputs x,no,lo,hi combine by three operations; register6 is the result. -/
def booleanProgram : List Instruction := [⟨.mul,1,2⟩,⟨.mul,0,3⟩,⟨.add,4,5⟩]

/-- Produced ring value and paid scalar implementation work. -/
structure OperationResult (R : Type*) where
  /-- Actual scalar output. -/
  value : R
  /-- Actual supplied backend work. -/
  work : ℕ

/-- Retained registers and accumulated calls, work and operand reads. -/
structure Registers (R : Type*) where
  /-- Append-only value array. -/
  values : Array R
  /-- Accumulated scalar-backend work. -/
  work : ℕ
  /-- Actual scalar calls. -/
  calls : ℕ
  /-- Explicit operand reads. -/
  reads : ℕ

/-- Total register read; the fixed programs' semantic proofs eliminate defaults. -/
def read (values : Array R) (i : ℕ) : R := values[i]?.getD 0

/-- Actual instruction interpreter; each produced value is cached before reuse. -/
def execute (backend : Opcode → R → R → OperationResult R) : List Instruction → Registers R → Registers R
  | [], state => state
  | inst::todo, state =>
      let out := backend inst.op (read state.values inst.left) (read state.values inst.right)
      execute backend todo ⟨state.values.push out.value,state.work+out.work,state.calls+1,state.reads+2⟩

/-- The instruction interpreter charges every scalar call and both operand reads. -/
theorem execute_counts (backend : Opcode → R → R → OperationResult R) (todo : List Instruction) (state : Registers R) :
    (execute backend todo state).calls=state.calls+todo.length ∧
    (execute backend todo state).reads=state.reads+2*todo.length := by
  induction todo generalizing state with
  | nil => simp [execute]
  | cons inst todo ih =>
    simp only [execute,ih,List.length_cons]
    constructor <;> omega

/-- Uniform backend bounds apply to the actual operands, not to an unacquired node oracle. -/
theorem execute_work (backend : Opcode → R → R → OperationResult R) (B : ℕ)
    (hwork : ∀ op a b, (backend op a b).work≤B) (todo : List Instruction) (state : Registers R) :
    (execute backend todo state).work ≤ state.work+todo.length*B := by
  induction todo generalizing state with
  | nil => simp [execute]
  | cons inst todo ih =>
    have ht := ih ⟨state.values.push
      (backend inst.op (read state.values inst.left) (read state.values inst.right)).value,
      state.work+(backend inst.op (read state.values inst.left) (read state.values inst.right)).work,
      state.calls+1,state.reads+2⟩
    have ho := hwork inst.op (read state.values inst.left) (read state.values inst.right)
    change _≤_
    simpa only [execute,List.length_cons] using ht.trans (by nlinarith)

/-- A materialized source port and its complement with all preparation charges. -/
structure Port (R : Type*) where
  /-- Cached original port value. -/
  yes : R
  /-- Cached complement. -/
  no : R
  /-- Backend preparation work. -/
  work : ℕ
  /-- Preparation scalar calls. -/
  operations : ℕ
  /-- Register/output and source-port reads. -/
  reads : ℕ

/-- Execute negation and addition once for one source port. -/
def preparePort (backend : Opcode → R → R → OperationResult R) (x : R) : Port R :=
  let out := execute backend complementProgram ⟨#[1,x],0,0,0⟩
  ⟨x,read out.values 3,out.work,out.calls,out.reads+2⟩

/-- Prepared port semantics are exact in an arbitrary commutative ring. -/
theorem preparePort_correct (backend : Opcode → R → R → OperationResult R)
    (hbackend : ∀ op a b, (backend op a b).value=meaning op a b) (x : R) :
    (preparePort backend x).yes=x ∧ (preparePort backend x).no=1-x := by
  simp [preparePort,complementProgram,execute,read,hbackend,meaning,sub_eq_add_neg]

/-- Preparation performs exactly two scalar calls and six charged reads. -/
theorem preparePort_counts (backend : Opcode → R → R → OperationResult R) (x : R) :
    (preparePort backend x).operations=2 ∧ (preparePort backend x).reads=6 := by
  simp [preparePort,complementProgram,execute]

/-- Preparation includes both actual scalar backend costs. -/
theorem preparePort_work (backend : Opcode → R → R → OperationResult R) (B : ℕ)
    (hwork : ∀ op a b, (backend op a b).work≤B) (x : R) : (preparePort backend x).work≤2*B := by
  exact (execute_work backend B hwork complementProgram ⟨#[1,x],0,0,0⟩).trans_eq (by simp [complementProgram])

/-- One fixed-program node scalar with its backend costs. -/
structure KernelRun (R : Type*) where
  /-- Acquired scalar output. -/
  value : R
  /-- Paid backend work. -/
  work : ℕ
  /-- Actual scalar calls. -/
  calls : ℕ
  /-- Operand and output register reads. -/
  reads : ℕ

/-- The three-instruction node program actually multiplies and adds retained values. -/
def booleanKernel (backend : Opcode → R → R → OperationResult R) (x no lo hi : R) : KernelRun R :=
  let out := execute backend booleanProgram ⟨#[x,no,lo,hi],0,0,0⟩
  ⟨read out.values 6,out.work,out.calls,out.reads+1⟩

/-- Exact node semantics with independent precomputed complement input. -/
theorem booleanKernel_correct (backend : Opcode → R → R → OperationResult R)
    (hbackend : ∀ op a b, (backend op a b).value=meaning op a b) (x no lo hi : R) :
    (booleanKernel backend x no lo hi).value=no*lo+x*hi := by
  simp [booleanKernel,booleanProgram,execute,read,hbackend,meaning]

/-- Exactly three backend calls per interpolation node. -/
theorem booleanKernel_calls (backend : Opcode → R → R → OperationResult R) (x no lo hi : R) :
    (booleanKernel backend x no lo hi).calls=3 := by simp [booleanKernel,booleanProgram,execute]
/-- Six operand reads and one retained-output read per node. -/
theorem booleanKernel_reads (backend : Opcode → R → R → OperationResult R) (x no lo hi : R) :
    (booleanKernel backend x no lo hi).reads=7 := by simp [booleanKernel,booleanProgram,execute]
/-- All three actual backend calls are paid. -/
theorem booleanKernel_work (backend : Opcode → R → R → OperationResult R) (B : ℕ)
    (hwork : ∀ op a b, (backend op a b).work≤B) (x no lo hi : R) :
    (booleanKernel backend x no lo hi).work≤3*B :=
  (execute_work backend B hwork booleanProgram ⟨#[x,no,lo,hi],0,0,0⟩).trans_eq (by simp [booleanProgram])

/-- Original Boolean table entry and its actual callback work. -/
structure Entry (R : Type*) where
  /-- Original tensor value. -/
  value : R
  /-- Paid callback work. -/
  work : ℕ

/-- Actual local recursion report; scalar work excludes separately identified control costs. -/
structure Run (R : Type*) where
  /-- Produced scalar. -/
  value : R
  /-- All callback and backend work. -/
  work : ℕ
  /-- Boolean table calls. -/
  callbacks : ℕ
  /-- Backend scalar calls. -/
  operations : ℕ
  /-- Charged register and cached-port reads. -/
  reads : ℕ
  /-- Maximum recursion depth. -/
  depth : ℕ

/-- Stream both Boolean branches using already acquired immutable source ports. -/
def evaluatePrepared (backend : Opcode → R → R → OperationResult R) : (w : ℕ) →
    ((Fin w → Bool) → Entry R) → (Fin w → Port R) → Run R
  | 0, T, _ => let entry := T Fin.elim0; ⟨entry.value,entry.work,1,0,0,0⟩
  | w+1, T, ports =>
      let lo := evaluatePrepared backend w (fun a => T (Fin.cons false a)) (fun i => ports i.succ)
      let hi := evaluatePrepared backend w (fun a => T (Fin.cons true a)) (fun i => ports i.succ)
      let port := ports 0
      let out := booleanKernel backend port.yes port.no lo.value hi.value
      ⟨out.value,lo.work+hi.work+out.work,lo.callbacks+hi.callbacks,
        lo.operations+hi.operations+out.calls,lo.reads+hi.reads+out.reads+2,max lo.depth hi.depth+1⟩

/-- Prepared traversal equals the Boolean multilinear extension at the ORIGINAL ports. -/
theorem evaluatePrepared_correct (backend : Opcode → R → R → OperationResult R)
    (hbackend : ∀ op a b, (backend op a b).value=meaning op a b)
    (w : ℕ) (T : (Fin w → Bool) → Entry R) (ports : Fin w → Port R) (x : Fin w → R)
    (hp : ∀ i, (ports i).yes=x i ∧ (ports i).no=1-x i) :
    (evaluatePrepared backend w T ports).value=SemiprimeStreamingTensor.evaluate w (fun a => (T a).value) x := by
  induction w with
  | zero => rfl
  | succ w ih =>
    change (booleanKernel backend (ports 0).yes (ports 0).no
      (evaluatePrepared backend w (fun a => T (Fin.cons false a)) (fun i => ports i.succ)).value
      (evaluatePrepared backend w (fun a => T (Fin.cons true a)) (fun i => ports i.succ)).value).value=_
    rw [booleanKernel_correct backend hbackend,ih _ _ _ (fun i => hp i.succ),ih _ _ _ (fun i => hp i.succ),(hp 0).1,(hp 0).2]
    rfl

/-- Exact traversal counts retain two Boolean branches rather than a ternary expansion. -/
theorem evaluatePrepared_counts (backend : Opcode → R → R → OperationResult R)
    (w : ℕ) (T : (Fin w → Bool) → Entry R) (ports : Fin w → Port R) :
    (evaluatePrepared backend w T ports).callbacks=2^w ∧
    (evaluatePrepared backend w T ports).operations=3*(2^w-1) ∧
    (evaluatePrepared backend w T ports).reads=9*(2^w-1) ∧
    (evaluatePrepared backend w T ports).depth=w := by
  induction w with
  | zero => simp [evaluatePrepared]
  | succ w ih =>
    let lo := evaluatePrepared backend w (fun a => T (Fin.cons false a)) (fun i => ports i.succ)
    let hi := evaluatePrepared backend w (fun a => T (Fin.cons true a)) (fun i => ports i.succ)
    have hl := ih (fun a => T (Fin.cons false a)) (fun i => ports i.succ)
    have hh := ih (fun a => T (Fin.cons true a)) (fun i => ports i.succ)
    have hp : 1≤2^w := Nat.one_le_pow _ _ (by decide)
    have he := Nat.sub_add_cancel hp
    have hp' : 1≤2^(w+1) := Nat.one_le_pow _ _ (by decide)
    have he' := Nat.sub_add_cancel hp'
    change lo.callbacks+hi.callbacks=2^(w+1) ∧
      lo.operations+hi.operations+(booleanKernel backend (ports 0).yes (ports 0).no lo.value hi.value).calls=3*(2^(w+1)-1) ∧
      lo.reads+hi.reads+(booleanKernel backend (ports 0).yes (ports 0).no lo.value hi.value).reads+2=9*(2^(w+1)-1) ∧
      max lo.depth hi.depth+1=w+1
    rw [hl.1,hh.1,hl.2.1,hh.2.1,hl.2.2.1,hh.2.2.1,hl.2.2.2,hh.2.2.2,
      booleanKernel_calls,booleanKernel_reads,max_self]
    rw [pow_succ] at he' ⊢
    exact ⟨by omega,by omega,by omega,rfl⟩

/-- All callback and backend work is retained on the actual recursive execution. -/
theorem evaluatePrepared_work (backend : Opcode → R → R → OperationResult R) (A B w : ℕ)
    (T : (Fin w → Bool) → Entry R) (ports : Fin w → Port R)
    (hT : ∀ a, (T a).work≤A) (hwork : ∀ op a b, (backend op a b).work≤B) :
    (evaluatePrepared backend w T ports).work≤2^w*A+3*(2^w-1)*B := by
  induction w with
  | zero => simpa [evaluatePrepared] using hT Fin.elim0
  | succ w ih =>
    have hl := ih (fun a => T (Fin.cons false a)) (fun i => ports i.succ) (fun a => hT (Fin.cons false a))
    have hh := ih (fun a => T (Fin.cons true a)) (fun i => ports i.succ) (fun a => hT (Fin.cons true a))
    have hk := booleanKernel_work backend B hwork (ports 0).yes (ports 0).no
      (evaluatePrepared backend w (fun a => T (Fin.cons false a)) (fun i => ports i.succ)).value
      (evaluatePrepared backend w (fun a => T (Fin.cons true a)) (fun i => ports i.succ)).value
    change _+_+_≤_
    have hp : 1≤2^w := Nat.one_le_pow _ _ (by decide)
    have he := Nat.sub_add_cancel hp
    have hp' : 1≤2^(w+1) := Nat.one_le_pow _ _ (by decide)
    have he' := Nat.sub_add_cancel hp'
    rw [pow_succ] at he' ⊢
    nlinarith

/-- Complete interpreter: materialize each port/complement ONCE before traversal. -/
def evaluate (backend : Opcode → R → R → OperationResult R) (w : ℕ)
    (T : (Fin w → Bool) → Entry R) (x : Fin w → R) : Run R :=
  let cache := Array.ofFn (fun i : Fin w => preparePort backend (x i))
  let ports := fun i : Fin w => cache[i.val]'(by simp [cache])
  let out := evaluatePrepared backend w T ports
  ⟨out.value,(∑ i, (ports i).work)+out.work,out.callbacks,
    (∑ i, (ports i).operations)+out.operations,(∑ i, (ports i).reads)+out.reads,out.depth⟩

/-- Exact full interpreter scalar semantics, including its actual cached complement supplier. -/
theorem evaluate_correct (backend : Opcode → R → R → OperationResult R)
    (hbackend : ∀ op a b, (backend op a b).value=meaning op a b)
    (w : ℕ) (T : (Fin w → Bool) → Entry R) (x : Fin w → R) :
    (evaluate backend w T x).value=SemiprimeStreamingTensor.evaluate w (fun a => (T a).value) x := by
  apply evaluatePrepared_correct backend hbackend w T _ x
  intro i
  simpa only [Array.getElem_ofFn] using preparePort_correct backend hbackend (x i)

/-- Full exact call/read/depth counts, including once-per-port preprocessing. -/
theorem evaluate_counts (backend : Opcode → R → R → OperationResult R)
    (w : ℕ) (T : (Fin w → Bool) → Entry R) (x : Fin w → R) :
    (evaluate backend w T x).callbacks=2^w ∧
    (evaluate backend w T x).operations=2*w+3*(2^w-1) ∧
    (evaluate backend w T x).reads=6*w+9*(2^w-1) ∧
    (evaluate backend w T x).depth=w := by
  let cache := Array.ofFn (fun i : Fin w => preparePort backend (x i))
  let ports := fun i : Fin w => cache[i.val]'(by simp [cache])
  have h := evaluatePrepared_counts backend w T ports
  have hc : (∑ i : Fin w, (ports i).operations)=2*w := by
    simp only [ports,cache,Array.getElem_ofFn,(preparePort_counts _ _).1,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
    omega
  have hr : (∑ i : Fin w, (ports i).reads)=6*w := by
    simp only [ports,cache,Array.getElem_ofFn,(preparePort_counts _ _).2,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
    omega
  change (evaluatePrepared backend w T ports).callbacks=_ ∧
    (∑ i, (ports i).operations)+(evaluatePrepared backend w T ports).operations=_ ∧
    (∑ i, (ports i).reads)+(evaluatePrepared backend w T ports).reads=_ ∧
    (evaluatePrepared backend w T ports).depth=_
  rw [h.1,h.2.1,h.2.2.1,h.2.2.2,hc,hr]
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Explicit paid work bound for the full source-to-local-value interpreter. -/
theorem evaluate_work (backend : Opcode → R → R → OperationResult R) (A B w : ℕ)
    (T : (Fin w → Bool) → Entry R) (x : Fin w → R)
    (hT : ∀ a, (T a).work≤A) (hwork : ∀ op a b, (backend op a b).work≤B) :
    (evaluate backend w T x).work≤2*w*B+2^w*A+3*(2^w-1)*B := by
  have hp (i : Fin w) := preparePort_work backend B hwork (x i)
  have hs : (∑ i : Fin w, (preparePort backend (x i)).work)≤2*w*B := by
    calc
      _ ≤ ∑ _i : Fin w, 2*B := Finset.sum_le_sum (fun i _ => hp i)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]; ring
  have ht := evaluatePrepared_work backend A B w T (fun i => preparePort backend (x i)) hT hwork
  change _+_≤_
  simp only [Array.getElem_ofFn]
  nlinarith

/-- Adapter for an original Boolean checker's actual accepted/clock pair. -/
def ofBoolean {w : ℕ} (checker : (Fin w → Bool) → Bool × ℕ) (a : Fin w → Bool) : Entry R :=
  let out := checker a
  ⟨if out.1 then 1 else 0,out.2+1⟩

/-- Exact original Boolean table recovery over ANY commutative ring; unit2 is unnecessary. -/
theorem boolean_recovery (backend : Opcode → R → R → OperationResult R)
    (hbackend : ∀ op a b, (backend op a b).value=meaning op a b)
    (w : ℕ) (T : (Fin w → Bool) → Entry R) (a : Fin w → Bool) :
    (evaluate backend w T (fun i => SemiprimeStreamingTensor.bit (a i))).value=(T a).value := by
  rw [evaluate_correct backend hbackend,SemiprimeStreamingTensor.boolean_recovery]

/-- The actual callback adapter preserves the original accepted bit. -/
theorem ofBoolean_value {w : ℕ} (checker : (Fin w → Bool) → Bool × ℕ) (a : Fin w → Bool) :
    (ofBoolean (R := R) checker a).value=if (checker a).1 then 1 else 0 := rfl
/-- The original callback clock and its scalar-selection charge are retained. -/
theorem ofBoolean_work {w : ℕ} (checker : (Fin w → Bool) → Bool × ℕ) (a : Fin w → Bool) :
    (ofBoolean (R := R) checker a).work=(checker a).2+1 := rfl

/-- Source-checker and backend bounds give a complete local reported-work bound. -/
theorem evaluateBoolean_work (backend : Opcode → R → R → OperationResult R) (A B w : ℕ)
    (checker : (Fin w → Bool) → Bool × ℕ) (x : Fin w → R)
    (hchecker : ∀ a, (checker a).2≤A) (hwork : ∀ op a b, (backend op a b).work≤B) :
    (evaluate backend w (ofBoolean checker) x).work≤2*w*B+2^w*(A+1)+3*(2^w-1)*B :=
  evaluate_work backend (A+1) B w (ofBoolean checker) x
    (fun a => Nat.add_le_add_right (hchecker a) 1) hwork

/-- The paid Boolean interpreter retains the original incidence degree, without ternary doubling. -/
theorem natDegree_evaluate_le {C : Type*} [CommRing C]
    (backend : Opcode → Polynomial C → Polynomial C → OperationResult (Polynomial C))
    (hbackend : ∀ op a b, (backend op a b).value=meaning op a b)
    (w : ℕ) (T : (Fin w → Bool) → C) (paths : Fin w → Polynomial C) (r : ℕ)
    (hp : ∀ i, (paths i).natDegree≤r) :
    ((evaluate backend w (fun a => (⟨Polynomial.C (T a),0⟩ : Entry (Polynomial C))) paths).value).natDegree≤w*r := by
  rw [evaluate_correct backend hbackend]
  exact SemiprimeStreamingTensor.natDegree_evaluate_le w T paths r hp

end RiemannGaussian.SemiprimeTernaryLocalPaid
