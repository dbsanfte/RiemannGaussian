/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedFibreNative

/-! # Uniform budget for the actual materialized native counter
The hypotheses bound actual runtime designs and original table reports. They do
not supply a count value, a fibre answer or a replacement counter execution.
The result is a numerical bound on the retained interpreter ledger, not a
literal machine-bit clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeNativeCounterBudget
open scoped BigOperators
open SemiprimeNodeArrayExecution SemiprimeLocalArrayFrontend

/-- Increasing the actual summary-box bound increases the native fibre envelope. -/
theorem fibreBudget_summary_mono (n F J R A w H M r Y Z : ℕ) (hYZ : Y ≤ Z) :
    SemiprimeMaterializedFibreNative.fibreBudget n F J R A w H M r Y ≤
      SemiprimeMaterializedFibreNative.fibreBudget n F J R A w H M r Z := by
  unfold SemiprimeMaterializedFibreNative.fibreBudget
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hYZ) _

/-- Complete uniform envelope, retaining literal support, summary and local-head
exponentials and every Hermite node acquisition. -/
def nativeBudget (n F Q J R A w H M r Y : ℕ) : ℕ :=
  Q*(SemiprimeCounterEnumeration.weightedCount n (J-1)*
    (SemiprimeMaterializedFibreNative.fibreBudget n F J R A w H M r Y+
      3*J+3*n+2+n*(8*J+3))+
    r*(2^H*(H+M*(4*H+2)+3))+r+1)+
    Q*(2*J+4+2*SemiprimeHermiteArrayHeight.nodeWork Q J)

/-- The native envelope with its three combinatorial counts supplied as
independent natural variables. Only fixed additions, multiplications and a
square remain; this is a fixed polynomial, not a recursive cost oracle. -/
def polynomialBudget (n F Q J R A w H M r Y Cq Ew Eh : ℕ) : ℕ :=
  let localCost := 2*(w*(n*((R+1)*(J*(J+1)+2*J)+J))+
    w*(n*((R+1)*(J*(J+1)+3*J+1)+3*J))+
    2*(Ew*(A+(w+1)*(2*(J*(J+1))+5*J)+J)))+
    (n+1)*(w+1)*(R+1)*(J+1)+Ew*2*(w+J+1)
  let group := F*(localCost+J+1+(2*J*(J+1)+J+1))+(J+1)+n+F+2
  let one := r*((J+1)+Eh*(group+2*M+4*H+5*J+6)+(2*J*(J+1)+J+1))+(J+1)+
    r*(Eh*(2*M+3)+H+1)+r+1
  let fibre := (J+1)+Y*(one+(4*J+1))
  let hermite := Q*J*(J*(J+1))+3*(Q*J)+8*Q+3*J^2+4*J+2
  Q*(Cq*(fibre+3*J+3*n+2+n*(8*J+3))+
    r*(Eh*(H+M*(4*H+2)+3))+r+1)+Q*(2*J+4+2*hermite)

/-- The explicit polynomial is exactly the native bound at its actual support,
local truth-table and local-head cardinalities. -/
theorem nativeBudget_eq_polynomial (n F Q J R A w H M r Y : ℕ) :
    nativeBudget n F Q J R A w H M r Y =
      polynomialBudget n F Q J R A w H M r Y
        (SemiprimeCounterEnumeration.weightedCount n (J-1)) (2^w) (2^H) := by
  unfold nativeBudget polynomialBudget SemiprimeMaterializedFibreNative.fibreBudget
    SemiprimeMaterializedFibrePacket.oneSummaryBudget SemiprimeNodeArrayExecution.groupBudget
    SemiprimeNativeGroupExecution.localBudget SemiprimeNativeGroupExecution.localControl
    SemiprimeLocalArrayFrontend.localOverhead SemiprimeHermiteArrayHeight.nodeWork
  simp only [Nat.pow_succ]
  ring

/-- A single-variable fixed polynomial envelope. It dominates the actual budget
once all dimensions and the three retained combinatorial counts are bounded. -/
def polynomialEnvelope (S : ℕ) : ℕ :=
  polynomialBudget S S S S S S S S S S S S S S

/-- Componentwise numerical resources suffice; no evaluator or count value is
assumed in this polynomial comparison. -/
theorem polynomialBudget_le_envelope (n F Q J R A w H M r Y Cq Ew Eh S : ℕ)
    (hn : n≤S) (hF : F≤S) (hQ : Q≤S) (hJ : J≤S) (hR : R≤S)
    (hA : A≤S) (hw : w≤S) (hH : H≤S) (hM : M≤S) (hr : r≤S)
    (hY : Y≤S) (hCq : Cq≤S) (hEw : Ew≤S) (hEh : Eh≤S) :
    polynomialBudget n F Q J R A w H M r Y Cq Ew Eh ≤ polynomialEnvelope S := by
  unfold polynomialEnvelope polynomialBudget
  dsimp only
  gcongr

/-- The literal native envelope is bounded by one fixed polynomial in a common
bound on its actual dimensions and separate support/head/truth cardinalities. -/
theorem nativeBudget_le_envelope (n F Q J R A w H M r Y S : ℕ)
    (hn : n≤S) (hF : F≤S) (hQ : Q≤S) (hJ : J≤S) (hR : R≤S)
    (hA : A≤S) (hw : w≤S) (hH : H≤S) (hM : M≤S) (hr : r≤S)
    (hY : Y≤S) (hCq : SemiprimeCounterEnumeration.weightedCount n (J-1)≤S)
    (hEw : 2^w≤S) (hEh : 2^H≤S) :
    nativeBudget n F Q J R A w H M r Y ≤ polynomialEnvelope S := by
  rw [nativeBudget_eq_polynomial]
  exact polynomialBudget_le_envelope n F Q J R A w H M r Y _ _ _ S
    hn hF hQ hJ hR hA hw hH hM hr hY hCq hEw hEh

/-- Uniform resources bound the work of the ACTUAL native counter. In particular,
the summary bound concerns its actual selected runtime matrices, not an old
extensionally equivalent count or an assumed count-answer oracle. -/
theorem count_work {n F : ℕ} {arity : Fin F → ℕ}
    (Q J R A w H M r Y : ℕ)
    (design : Fin Q → RuntimeDesign n F)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (hr : ∀ a, (design a).r=r)
    (hh : ∀ a g, (design a).h g ≤ H) (hm : ∀ a g, (design a).m g ≤ M)
    (hw : ∀ e, arity e ≤ w)
    (hT : ∀ e eta, (T e eta).arithmetic ≤ A ∧ (T e eta).reads ≤ A)
    (hy : ∀ a, SemiprimePacketArrayExecution.summaryCount
      (design a).r (design a).h (design a).m (design a).W ≤ Y) :
    (SemiprimeMaterializedFibreNative.count Q J R design source T).work ≤
      nativeBudget n F Q J R A w H M r Y := by
  apply (SemiprimeMaterializedFibreNative.count_work Q J R A w H M design source T hh hm hw hT).trans
  unfold nativeBudget
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ _a : Fin Q, (SemiprimeCounterEnumeration.weightedCount n (J-1)*
        (SemiprimeMaterializedFibreNative.fibreBudget n F J R A w H M r Y+
          3*J+3*n+2+n*(8*J+3))+
        r*(2^H*(H+M*(4*H+2)+3))+r+1) := by
      apply Finset.sum_le_sum
      intro a _
      have hf : SemiprimeMaterializedFibreNative.fibreBudget n F J R A w H M
          (design a).r (SemiprimePacketArrayExecution.summaryCount
            (design a).r (design a).h (design a).m (design a).W) ≤
          SemiprimeMaterializedFibreNative.fibreBudget n F J R A w H M r Y := by
        calc
          _ ≤ SemiprimeMaterializedFibreNative.fibreBudget n F J R A w H M (design a).r Y :=
            fibreBudget_summary_mono n F J R A w H M (design a).r _ Y (hy a)
          _ = _ := by rw [hr a]
      calc
        _ ≤ SemiprimeCounterEnumeration.weightedCount n (J-1)*
          (SemiprimeMaterializedFibreNative.fibreBudget n F J R A w H M r Y+
            3*J+3*n+2+n*(8*J+3))+
          (design a).r*(2^H*(H+M*(4*H+2)+3))+(design a).r+1 := by
            have hc := Nat.mul_le_mul_left
              (SemiprimeCounterEnumeration.weightedCount n (J-1))
              (Nat.add_le_add_right hf (3*J+3*n+2+n*(8*J+3)))
            simp only [Nat.add_assoc] at hc ⊢
            omega
        _ = _ := by rw [hr a]
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

end RiemannGaussian.SemiprimeNativeCounterBudget
