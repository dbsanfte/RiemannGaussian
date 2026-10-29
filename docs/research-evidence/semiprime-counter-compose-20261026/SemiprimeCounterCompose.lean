/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCounterNative
import RiemannGaussian.SemiprimeCounterSeparation
import RiemannGaussian.SemiprimeHermiteRecovery

/-!
# Composed exact counting formula from original rows

This joins native row restoration and Taylor expansion, degree-truncated Boolean
cancellation, row-certified measurement separation and explicit Hermite recovery.
The result concerns the finite algebraic expression. Layout construction, array
execution refinement and bit-operation costs remain separate obligations.
-/

namespace RiemannGaussian.SemiprimeCounterCompose
open scoped BigOperators
open RiemannGaussian.SemiprimeBooleanDiagonal RiemannGaussian.SemiprimeStreamingTensor
noncomputable section
attribute [local instance] Classical.propDecidable
variable {A G : Type*} [Fintype A] [DecidableEq A]
variable {B : G → Type*}
/-- Boolean assignments split along an explicit variable partition. -/
def splitAssignment (s : A ≃ Sigma B) : Finset A ≃ ((g : G) → B g → Bool) where
  toFun x g v := decide (s.symm ⟨g,v⟩ ∈ x)
  invFun x := Finset.univ.filter (fun v => x (s v).1 (s v).2 = true)
  left_inv x := by
    ext v
    simp
  right_inv x := by
    funext g v
    simp
    change (fun y : Sigma B => x y.1 y.2) (s (s.symm ⟨g,v⟩)) = x g v
    rw [Equiv.apply_symm_apply]

theorem bit_splitAssignment (s : A ≃ Sigma B) (x : Finset A) (g : G) (v : B g) :
    (bit (splitAssignment s x g v) : ℚ) = indicator x (s.symm ⟨g,v⟩) := by
  simp [splitAssignment, bit, indicator]

theorem sum_grouped_row [Fintype G] [∀g,Fintype (B g)] (s : A ≃ Sigma B) (row : A → ℚ) (x : Finset A) :
    (∑ g, ∑ v, row (s.symm ⟨g,v⟩) * bit (splitAssignment s x g v)) =
      ∑ a, row a * indicator x a := by
  simp only [bit_splitAssignment]
  rw [← Fintype.sum_sigma (fun gv : Sigma B => row (s.symm gv) * indicator x (s.symm gv))]
  exact s.symm.sum_comp (fun a => row a * indicator x a)

theorem forced_splitAssignment (s : A ≃ Sigma B) (forced x : Finset A) :
    forced ⊆ x ↔ ∀ g v, s.symm ⟨g,v⟩ ∈ forced → splitAssignment s x g v = true := by
  simp only [splitAssignment, Equiv.coe_fn_mk, decide_eq_true_eq]
  constructor
  · intro h g v hv;exact h hv
  · intro h a ha
    have he := h (s a).1 (s a).2
    simpa using he (by simpa using ha)

end
noncomputable section
attribute [local instance] Classical.propDecidable
open Polynomial
open RiemannGaussian.SemiprimeCounterSeparation
open RiemannGaussian.SemiprimeCounterFiltration
open RiemannGaussian.SemiprimeCounterNative
open RiemannGaussian.SemiprimeHermiteRecovery

variable {A E : Type} [Fintype A] [DecidableEq A] [Fintype E]

/-- Locally checkable design information at one interpolation node. The only
algebraic certificates are measurement readouts and off-group row spans. -/
structure NodeCertificate (arity : E → ℕ)
    (rows : (e : E) → Fin (arity e) → A → ℚ) where
  /-- Group index type. -/
  Group : Type
  /-- Finite group enumeration. -/
  [groupFinite : Fintype Group]
  /-- Group equality test. -/
  [groupDecEq : DecidableEq Group]
  /-- Coordinates belonging to each group. -/
  Local : Group → Type
  /-- Finite local coordinate enumerations. -/
  [localFinite : ∀ g, Fintype (Local g)]
  /-- Explicit partition of all original coordinates. -/
  grouping : A ≃ Sigma Local
  /-- Group assigned to each original factor. -/
  assigned : E → Group
  /-- Measurement row indices. -/
  Index : Group → Type
  /-- Finite row enumeration. -/
  [indexFinite : ∀ g, Fintype (Index g)]
  /-- Original rational measurement rows. -/
  measureRows : (g : Group) → Index g → Local g → ℚ
  /-- Finite measurement enumeration, allowed to include empty fibres. -/
  Summary : Group → Type
  /-- Finite summary enumeration. -/
  [summaryFinite : ∀ g, Fintype (Summary g)]
  /-- Measurement computed from one local Boolean assignment. -/
  measurement : (g : Group) → (Local g → Bool) → Summary g
  /-- Rational interpretation of each measurement row. -/
  readout : (g : Group) → Summary g → Index g → ℚ
  /-- Every stored measurement gives the actual row dot product. -/
  readout_eq : ∀ g x a,
    readout g (measurement g x) a = rowValue (measureRows g a) x
  /-- Every off-group native row is a linear combination of measurement rows. -/
  row_span : ∀ e i g, g ≠ assigned e → ∃ c : Index g → ℚ,
    ∀ v, rows e i (grouping.symm ⟨g,v⟩) = ∑ a, c a * measureRows g a v
  /-- Selected Boolean representatives, without forced-coordinate restrictions. -/
  representative : ((g : Group) → Summary g) → (g : Group) → Local g → Bool
  /-- Representatives are correct on every nonempty measurement fibre. -/
  representative_valid : ∀ y g, (∃ a, measurement g a = y g) →
    measurement g (representative y g) = y g

attribute [instance] NodeCertificate.groupFinite NodeCertificate.groupDecEq
  NodeCertificate.localFinite NodeCertificate.indexFinite NodeCertificate.summaryFinite

/-- The scalar native rows in the certificate's local coordinates. -/
def groupedRows (arity : E → ℕ) (rows : (e : E) → Fin (arity e) → A → ℚ)
    (d : NodeCertificate arity rows) :
    (e : E) → Fin (arity e) → (g : d.Group) → d.Local g → ℚ :=
  fun e i g v => rows e i (d.grouping.symm ⟨g,v⟩)

/-- A forced original coordinate must equal one in its actual local assignment. -/
def localForced (arity : E → ℕ) (rows : (e : E) → Fin (arity e) → A → ℚ)
    (d : NodeCertificate arity rows) (S : Finset A) (g : d.Group)
    (x : d.Local g → Bool) : Prop :=
  ∀ v, d.grouping.symm ⟨g,v⟩ ∈ S → x v = true

/-- The polynomial result of the explicitly separated measurement/fibre sums. -/
def fibrePacket (arity : E → ℕ) (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → A → ℚ) (d : NodeCertificate arity rows)
    (correction : (e : E) → Fin (arity e) → Polynomial ℚ) (S : Finset A) : Polynomial ℚ :=
  ∑ y : (g : d.Group) → d.Summary g, ∏ g, ∑ a : d.Local g → Bool,
    if d.measurement g a = y g ∧ localForced arity rows d S g a then
      groupValue arity T d.assigned (groupedRows arity rows d) correction g
        (Function.update (d.representative y) g a)
    else 0

omit [Fintype E] in
theorem basePort_split (arity : E → ℕ)
    (rows : (e : E) → Fin (arity e) → A → ℚ) (d : NodeCertificate arity rows)
    (x : Finset A) (e : E) (i : Fin (arity e)) :
    basePort arity (groupedRows arity rows d) e i (splitAssignment d.grouping x) =
      ∑ v, rows e i v * indicator x v :=
  sum_grouped_row d.grouping (rows e i) x

/-- Native forced-assignment sums equal actual separated fibre sums, using
only the local certificates bundled above. -/
theorem fibrePacket_eq (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → A → ℚ) (d : NodeCertificate arity rows)
    (correction : (e : E) → Fin (arity e) → Polynomial ℚ) (S : Finset A) :
    fibrePacket arity T rows d correction S =
      ∑ x : Finset A, if S ⊆ x then ∏ e,
        evaluate (arity e) (fun a => C (T e a))
          (fun i => C (∑ v, rows e i v * indicator x v) + correction e i) else 0 := by
  have hs := separated_tensor_contraction arity T d.assigned
    (groupedRows arity rows d) correction d.measureRows d.measurement d.readout
    d.readout_eq d.row_span (localForced arity rows d S) d.representative d.representative_valid
  unfold fibrePacket
  rw [← hs]
  symm
  apply Fintype.sum_equiv (splitAssignment d.grouping)
  intro x
  have hf : (S ⊆ x) ↔ ∀ g, localForced arity rows d S g (splitAssignment d.grouping x g) :=
    forced_splitAssignment d.grouping S x
  simp only [← hf, factorValue, basePort_split]

/-- Positive-degree correction at a fixed independent Boolean subset. -/
def nativeCorrection (arity : E → ℕ)
    (rows : (e : E) → Fin (arity e) → A → Polynomial ℚ) (t : ℚ) (R : ℕ)
    (U : Finset A) (e : E) (i : Fin (arity e)) : Polynomial ℚ :=
  ∑ k ∈ Finset.range R,
    monomial (k+1) (∑ v, (taylor t (rows e i v)).coeff (k+1) * indicator U v)

theorem fibrePacket_native (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → A → Polynomial ℚ) (t : ℚ) (R : ℕ)
    (d : NodeCertificate arity (fun e i v => (rows e i v).eval t)) (S U : Finset A) :
    fibrePacket arity T (fun e i v => (rows e i v).eval t) d
      (nativeCorrection arity rows t R U) S =
      ∑ x : Finset A, if S ⊆ x then
        (correctedProduct arity T (shiftedBase arity rows t x) R
          (shiftedRows arity rows t)).map (MvPolynomial.eval (indicator U)) else 0 := by
  rw [fibrePacket_eq]
  apply Finset.sum_congr rfl
  intro x hx
  rw [correctedProduct_map]
  simp only [inputPort_map, shiftedBase, shiftedRows, nativeCorrection]

/-- Möbius combination of separated fibres before retaining its Taylor packet. -/
def rawPacket (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → A → Polynomial ℚ) (t : ℚ) (R J : ℕ)
    (d : NodeCertificate arity (fun e i v => (rows e i v).eval t)) : Polynomial ℚ :=
  ∑ S ∈ (Finset.univ : Finset A).powerset.filter (fun S => S.card ≤ J-1),
    ∑ U ∈ S.powerset, C ((-1 : ℚ)^(S.card-U.card)) *
      fibrePacket arity T (fun e i v => (rows e i v).eval t) d
        (nativeCorrection arity rows t R U) S

theorem rawPacket_coeff (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → A → Polynomial ℚ) (t : ℚ) (R J : ℕ)
    (d : NodeCertificate arity (fun e i v => (rows e i v).eval t))
    (hp : ∀ e i v, (rows e i v).natDegree ≤ R) (j : ℕ) (hj : j < J) :
    (rawPacket arity T rows t R J d).coeff j =
      (taylor t (globalPolynomial arity T rows)).coeff j := by
  rw [native_taylor_diagonal arity T rows t R J hp j hj]
  simp only [rawPacket, finsetSum_coeff, coeff_C_mul, fibrePacket_native]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro U hU
  congr 1
  rw [Finset.sum_filter]
  simp only [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp only [coeff_map, coeff_zero]

/-- Precisely the retained packet used by Hermite recovery. -/
def nodePacket (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → A → Polynomial ℚ) (t : ℚ) (R J : ℕ)
    (d : NodeCertificate arity (fun e i v => (rows e i v).eval t)) : Polynomial ℚ :=
  rawPacket arity T rows t R J d %ₘ X^J

/-- The actual separated Möbius expression returns the original global
polynomial's retained Taylor packet. -/
theorem nodePacket_eq (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → A → Polynomial ℚ) (t : ℚ) (R J : ℕ)
    (d : NodeCertificate arity (fun e i v => (rows e i v).eval t))
    (hp : ∀ e i v, (rows e i v).natDegree ≤ R) :
    nodePacket arity T rows t R J d = (taylor t (globalPolynomial arity T rows)) %ₘ X^J := by
  apply modByMonic_eq_of_dvd_sub (monic_X.pow J)
  rw [X_pow_dvd_iff]
  intro j hj
  simp only [coeff_sub, rawPacket_coeff arity T rows t R J d hp j hj, sub_self]

/-- Full explicit Hermite readout from the separated node packets. -/
def counterValue (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → A → Polynomial ℚ) (Q R J : ℕ)
    (design : (t : samplePoints Q) → NodeCertificate arity (fun e i v => (rows e i v).eval t)) : ℚ :=
  ∑ t : samplePoints Q, (cardinalFactor (samplePoints Q) J (t : ℚ)).eval 0 *
    (localQuotient (nodePacket arity T rows (t : ℚ) R J (design t))
      (taylor (t : ℚ) (cardinalFactor (samplePoints Q) J (t : ℚ))) J).eval (-(t : ℚ))

/-- Composed counter correctness: the expression consists of original streamed
factors, row-certified fibre sums, the finite Möbius menu, retained packets and
explicit Hermite reconstruction. Its only algebraic assumptions are bounded row
degrees, literal restoration, and the local node certificates. -/
theorem counterValue_eq_original (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → A → Polynomial ℚ) (Q R : ℕ) (hQ : 0 < Q)
    (design : (t : samplePoints Q) → NodeCertificate arity (fun e i v => (rows e i v).eval t))
    (hp : ∀ e i v, (rows e i v).natDegree ≤ R)
    (coordinate : (e : E) → Fin (arity e) → A)
    (hrestore : ∀ e i v, (rows e i v).eval 0 = if v=coordinate e i then 1 else 0) :
    counterValue arity T rows Q R ((∑ e, arity e)*R/Q+1) design =
      originalContraction arity T coordinate := by
  let J := (∑ e, arity e)*R/Q+1
  have hJ : 0 < J := Nat.succ_pos _
  have hdegree : (globalPolynomial arity T rows).natDegree < (samplePoints Q).card*J := by
    rw [samplePoints_card]
    exact (globalPolynomial_degree arity T rows R hp).trans_lt
      (counter_precision_sufficient Q (∑ e, arity e) R hQ)
  change counterValue arity T rows Q R J design = _
  unfold counterValue
  simp_rw [nodePacket_eq arity T rows _ R J _ hp]
  rw [Finset.sum_coe_sort (samplePoints Q) (fun t : ℚ =>
    (cardinalFactor (samplePoints Q) J t).eval 0 *
      (localQuotient ((taylor t (globalPolynomial arity T rows)) %ₘ X^J)
        (taylor t (cardinalFactor (samplePoints Q) J t)) J).eval (-t))]
  rw [← explicit_hermite_at_zero (samplePoints Q) J hJ (globalPolynomial arity T rows) hdegree]
  exact globalPolynomial_at_zero arity T rows coordinate hrestore

#print axioms counterValue_eq_original
#print axioms nodePacket_eq
#print axioms fibrePacket_eq
end
end RiemannGaussian.SemiprimeCounterCompose

