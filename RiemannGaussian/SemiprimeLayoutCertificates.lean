/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCounterCompose

/-!
# Integer layout constraints as actual counter certificates

Finite denominator clearing and rational duality turn integer-kernel locality
into row-span witnesses. Measurements use explicit signed integer boxes, and
representatives are found by finite Boolean scans without forced-bit conditions.
-/
namespace RiemannGaussian.SemiprimeLayoutCertificates
open scoped BigOperators
open Polynomial
open RiemannGaussian.SemiprimeCounterCompose
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V I : Type*} [Fintype V] [Fintype I]

/-- Common denominator clearing for a finite rational coordinate vector. -/
theorem clear_vector_denominators (x : V → ℚ) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ z : V → ℤ, ∀ v, (z v : ℚ) = (d : ℚ)*x v := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) x
  have hdn : (d : ℤ) ≠ 0 := nonZeroDivisors.ne_zero d.property
  have hz : ∀ v, ∃ z : ℤ, (z : ℚ) = (d : ℚ)*x v := by
    intro v
    obtain ⟨z, hz⟩ := hd v
    exact ⟨z, by simpa [Algebra.smul_def] using hz⟩
  choose z hz using hz
  exact ⟨d, hdn, z, hz⟩

omit [Fintype I] in
/-- Exact integer-kernel locality extends to the whole rational kernel. -/
theorem rational_kernel_locality (C : I → V → ℤ) (a : V → ℚ)
    (h : ∀ z : V → ℤ, (∀ i, ∑ v, C i v*z v = 0) → ∑ v, a v*(z v : ℚ) = 0)
    (x : V → ℚ) (hx : ∀ i, ∑ v, (C i v : ℚ)*x v = 0) :
    ∑ v, a v*x v = 0 := by
  obtain ⟨d, hd, z, hz⟩ := clear_vector_denominators x
  have hdz : ∀ i, ∑ v, C i v*z v = 0 := by
    intro i
    apply Int.cast_injective (α := ℚ)
    push_cast
    simp_rw [hz]
    calc
      ∑ v, (C i v : ℚ)*((d : ℚ)*x v) = (d : ℚ)*(∑ v, (C i v : ℚ)*x v) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        ring
      _ = 0 := by rw [hx i, mul_zero]
  have ha := h z hdz
  have he : ∑ v, a v*(z v : ℚ) = (d : ℚ)*(∑ v, a v*x v) := by
    simp_rw [hz]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  rw [he] at ha
  exact (mul_eq_zero.mp ha).resolve_left (by exact_mod_cast hd)

/-- A rational row as an actual linear functional. -/
def rowFunctional (a : V → ℚ) : (V → ℚ) →ₗ[ℚ] ℚ where
  toFun x := ∑ v, a v*x v
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]; congr 1; funext v; ring

/-- The needed converse: integer-kernel annihilation yields actual rational
row-span coefficients, without a row-span premise. -/
theorem row_span_of_integer_kernel (C : I → V → ℤ) (a : V → ℚ)
    (h : ∀ z : V → ℤ, (∀ i, ∑ v, C i v*z v = 0) → ∑ v, a v*(z v : ℚ) = 0) :
    ∃ c : I → ℚ, ∀ v, a v = ∑ i, c i*(C i v : ℚ) := by
  let L : I → (V → ℚ) →ₗ[ℚ] ℚ := fun i => rowFunctional (fun v => (C i v : ℚ))
  have hk : (⨅ i, LinearMap.ker (L i)) ≤ LinearMap.ker (rowFunctional a) := by
    intro x hx
    have hxi := (Submodule.mem_iInf _).mp hx
    exact rational_kernel_locality C a h x (fun i => hxi i)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp
    (FiniteDimensional.mem_span_of_iInf_ker_le_ker hk)
  refine ⟨c, fun v => ?_⟩
  have he := LinearMap.congr_fun hc (Pi.single v 1)
  simpa [L, rowFunctional, Pi.single_apply, mul_ite] using he.symm

/-- Actual integer signature of a Boolean local assignment. -/
def signature (C : I → V → ℤ) (x : V → Bool) (i : I) : ℤ :=
  ∑ v, C i v * (if x v then 1 else 0)

omit [Fintype I] in
theorem signature_bound (C : I → V → ℤ) (W : ℕ)
    (hC : ∀ i v, |C i v| ≤ (W : ℤ)) (x : V → Bool) (i : I) :
    |signature C x i| ≤ (Fintype.card V * W : ℕ) := by
  unfold signature
  calc
    _ ≤ ∑ v, |C i v * (if x v then 1 else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v : V, (W : ℤ) := by
      apply Finset.sum_le_sum
      intro v hv
      cases x v <;> simp [hC i v]
    _ = _ := by simp

/-- Full signed interval box, not an opaque type of attained signatures. -/
abbrev Summary (V I : Type*) [Fintype V] (W : ℕ) := I → Fin (2*(Fintype.card V*W)+1)

/-- Actual Boolean measurement encoded into the public signed interval box. -/
def measurement (C : I → V → ℤ) (W : ℕ) (hC : ∀ i v, |C i v| ≤ (W : ℤ))
    (x : V → Bool) : Summary V I W := fun i =>
  ⟨(signature C x i + (Fintype.card V*W : ℕ)).toNat, by
    have h := abs_le.mp (signature_bound C W hC x i)
    omega⟩

/-- Decode a public signed measurement coordinate as a rational value. -/
def readout (W : ℕ) (y : Summary V I W) (i : I) : ℚ :=
  ((y i).val : ℚ) - (Fintype.card V*W : ℕ)

omit [Fintype I] in
theorem readout_measurement (C : I → V → ℤ) (W : ℕ)
    (hC : ∀ i v, |C i v| ≤ (W : ℤ)) (x : V → Bool) (i : I) :
    readout W (measurement C W hC x) i =
      ∑ v, (C i v : ℚ) * (if x v then 1 else 0) := by
  have hb := abs_le.mp (signature_bound C W hC x i)
  have he : (((signature C x i + (Fintype.card V*W : ℕ)).toNat : ℤ) -
      (Fintype.card V*W : ℕ)) = signature C x i := by omega
  have heq : readout W (measurement C W hC x) i = (signature C x i : ℚ) := by
    dsimp only [readout, measurement]
    exact_mod_cast he
  rw [heq]
  simp only [signature, Int.cast_sum, Int.cast_mul, Int.cast_ite, Int.cast_one, Int.cast_zero]

theorem summary_card (W : ℕ) : Fintype.card (Summary V I W) =
    (2*(Fintype.card V*W)+1)^(Fintype.card I) := by
  simp [Summary]

/-- Tail-recursive ordered scan, retaining no list of candidates. -/
def scanFrom {X : Type*} (decode : ℕ → X) (test : X → Bool) : ℕ → ℕ → Option X
  | 0, _ => none
  | fuel+1, start => if test (decode start) then some (decode start)
      else scanFrom decode test fuel (start+1)

theorem scanFrom_complete {X : Type*} (decode : ℕ → X) (test : X → Bool)
    (fuel start : ℕ) (h : ∃ k < fuel, test (decode (start+k)) = true) :
    ∃ x, scanFrom decode test fuel start = some x ∧ test x = true := by
  induction fuel generalizing start with
  | zero => obtain ⟨k,hk,_⟩ := h; omega
  | succ fuel ih =>
    by_cases hp : test (decode start) = true
    · exact ⟨decode start, by simp [scanFrom, hp], hp⟩
    · obtain ⟨k,hk,hp'⟩ := h
      have hk0 : 0 < k := by cases k <;> simp_all
      obtain ⟨x, hx, htest⟩ := ih (start+1) ⟨k-1, by omega, by
        simpa only [show start+1+(k-1)=start+k by omega] using hp'⟩
      exact ⟨x, by simpa [scanFrom, hp] using hx, htest⟩

/-- Decode one Boolean assignment by its finite enumeration index. -/
def booleanDecode (k : ℕ) : V → Bool :=
  (Fintype.equivFin (V → Bool)).symm
    ⟨k % Fintype.card (V → Bool), Nat.mod_lt _ Fintype.card_pos⟩

theorem booleanDecode_covers (x : V → Bool) :
    ∃ k < Fintype.card (V → Bool), booleanDecode (V := V) k = x := by
  let i := Fintype.equivFin (V → Bool) x
  refine ⟨i.val, i.isLt, ?_⟩
  unfold booleanDecode
  have hi : (⟨i.val % Fintype.card (V → Bool), Nat.mod_lt _ Fintype.card_pos⟩ :
      Fin (Fintype.card (V → Bool))) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  rw [hi]
  exact Equiv.symm_apply_apply _ x

/-- First matching Boolean assignment by a bounded tail-recursive scan;
fallback is all-false and is used only for empty fibres. -/
def firstRepresentative {Y : Type*} [DecidableEq Y] (measure : (V → Bool) → Y) (y : Y) : V → Bool :=
  (scanFrom (booleanDecode (V := V)) (fun x => decide (measure x=y))
    (Fintype.card (V → Bool)) 0).getD (fun _ => false)

theorem firstRepresentative_valid {Y : Type*} [DecidableEq Y]
    (measure : (V → Bool) → Y) (y : Y) (hy : ∃ x, measure x=y) :
    measure (firstRepresentative measure y) = y := by
  obtain ⟨x, hx⟩ := hy
  obtain ⟨k, hk, hdecode⟩ := booleanDecode_covers x
  obtain ⟨z,hz,htest⟩ := scanFrom_complete (booleanDecode (V := V))
    (fun a => decide (measure a=y)) (Fintype.card (V → Bool)) 0
    ⟨k,hk,by simp only [zero_add, hdecode, hx, decide_true]⟩
  simp only [firstRepresentative, hz, Option.getD_some]
  exact of_decide_eq_true htest

/-- Assemble an actual NodeCertificate from bounded integer constraints and
integer-kernel locality. Rational row spans are derived, not supplied. -/
def ofIntegerConstraints {A E G : Type} [Fintype G] [DecidableEq G]
    (arity : E → ℕ) (rows : (e : E) → Fin (arity e) → A → ℚ)
    (Local : G → Type) [∀ g, Fintype (Local g)] (grouping : A ≃ Sigma Local)
    (assigned : E → G) (Index : G → Type) [∀ g, Fintype (Index g)]
    (C : (g : G) → Index g → Local g → ℤ) (W : G → ℕ)
    (hC : ∀ g i v, |C g i v| ≤ (W g : ℤ))
    (hlocal : ∀ e i g, g ≠ assigned e → ∀ z : Local g → ℤ,
      (∀ k, ∑ v, C g k v*z v = 0) →
        ∑ v, rows e i (grouping.symm ⟨g,v⟩)*(z v : ℚ) = 0) :
    NodeCertificate arity rows where
  Group := G
  Local := Local
  grouping := grouping
  assigned := assigned
  Index := Index
  measureRows g i v := (C g i v : ℚ)
  Summary g := Summary (Local g) (Index g) (W g)
  measurement g := measurement (C g) (W g) (hC g)
  readout g := readout (W g)
  readout_eq g x i := by
    simpa only [RiemannGaussian.SemiprimeCounterSeparation.rowValue,
      RiemannGaussian.SemiprimeStreamingTensor.bit] using readout_measurement (C g) (W g) (hC g) x i
  row_span e i g hg := row_span_of_integer_kernel (C g)
    (fun v => rows e i (grouping.symm ⟨g,v⟩)) (hlocal e i g hg)
  representative y g := firstRepresentative (measurement (C g) (W g) (hC g)) (y g)
  representative_valid y g hy := firstRepresentative_valid
    (measurement (C g) (W g) (hC g)) (y g) hy

/-- Exact public enumeration size of all group summary tuples. -/
theorem grouped_summary_card {G : Type*} [Fintype G]
    (Local Index : G → Type*) [∀ g, Fintype (Local g)] [∀ g, Fintype (Index g)]
    (W : G → ℕ) :
    Fintype.card ((g : G) → Summary (Local g) (Index g) (W g)) =
      ∏ g, (2*(Fintype.card (Local g)*W g)+1)^(Fintype.card (Index g)) := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro g hg
  exact summary_card (V := Local g) (I := Index g) (W g)

#print axioms ofIntegerConstraints
#print axioms grouped_summary_card
#print axioms summary_card
#print axioms firstRepresentative_valid
#print axioms row_span_of_integer_kernel
end
end RiemannGaussian.SemiprimeLayoutCertificates
