import RiemannGaussian.External.Zeta23InverseSamplingFiniteTail
import Mathlib.Data.Fintype.Sort

/-!
# Consecutive triple packing for the literal Zeta23 Gram

This file supplies the quantitative step that turns the finite endpoint
kernel into a genuine zero-side gain.  It keeps the three shifted packings
until the last moment; averaging their span costs loses only `2/3` of the
total ordered range.
-/

noncomputable section

open Complex Filter Real
open scoped BigOperators

namespace RiemannGaussian
namespace Zeta23InverseSampling

/-! ## Stability of the three-correlation energy -/

/-- Squared norm is stable from below under a small complex perturbation of
a uniformly bounded real target.  The rational constant is intentionally
loose so the result uses no numerical oracle. -/
lemma sq_norm_ge_sq_sub_six_mul
    {g : ℂ} {k e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hk : |k| ≤ (12 : ℝ) / 11) (hclose : ‖g - (k : ℂ)‖ ≤ e) :
    k ^ 2 - 6 * e ≤ ‖g‖ ^ 2 := by
  have hkNorm : ‖(k : ℂ)‖ = |k| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hk_le : |k| ≤ ‖g‖ + e := by
    calc
      |k| = ‖(k : ℂ)‖ := hkNorm.symm
      _ = ‖g - (g - (k : ℂ))‖ := by ring_nf
      _ ≤ ‖g‖ + ‖g - (k : ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖g‖ + e := by linarith
  have hg_le : ‖g‖ ≤ (12 : ℝ) / 11 + e := by
    calc
      ‖g‖ = ‖(g - (k : ℂ)) + (k : ℂ)‖ := by ring_nf
      _ ≤ ‖g - (k : ℂ)‖ + ‖(k : ℂ)‖ := norm_add_le _ _
      _ ≤ e + |k| := add_le_add hclose hkNorm.le
      _ ≤ e + (12 : ℝ) / 11 := by linarith
      _ = (12 : ℝ) / 11 + e := by ring
  have hk_sq : k ^ 2 ≤ (‖g‖ + e) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg k) hk_le 2
  nlinarith [sq_nonneg ‖g‖, sq_nonneg e,
    mul_nonneg he0 (sub_nonneg.mpr he1)]

/-- Three entrywise endpoint-kernel estimates give a lower bound for the
entire off-diagonal energy of a literal `3 × 3` Gram block. -/
lemma tripleOffDiagEnergy_ge_montgomeryTaylorTripleEnergy_sub
    (K : Matrix (Fin 3) (Fin 3) ℂ) {a b e : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (h01 : ‖K 0 1 - (montgomeryTaylorKernel a : ℂ)‖ ≤ e)
    (h12 : ‖K 1 2 - (montgomeryTaylorKernel b : ℂ)‖ ≤ e)
    (h02 : ‖K 0 2 - (montgomeryTaylorKernel (a + b) : ℂ)‖ ≤ e) :
    montgomeryTaylorTripleEnergy a b - 36 * e ≤
      ZeroBlockData.tripleOffDiagEnergy K := by
  have h01' := sq_norm_ge_sq_sub_six_mul he0 he1
    (abs_montgomeryTaylorKernel_le_twelve_elevenths a) h01
  have h12' := sq_norm_ge_sq_sub_six_mul he0 he1
    (abs_montgomeryTaylorKernel_le_twelve_elevenths b) h12
  have h02' := sq_norm_ge_sq_sub_six_mul he0 he1
    (abs_montgomeryTaylorKernel_le_twelve_elevenths (a + b)) h02
  unfold montgomeryTaylorTripleEnergy ZeroBlockData.tripleOffDiagEnergy
  linarith

/-- The endpoint kernel is even.  This lets an increasing ordinate list use
the Gram convention `gamma_i - gamma_j` without changing its real target. -/
lemma montgomeryTaylorKernel_neg (x : ℝ) :
    montgomeryTaylorKernel (-x) = montgomeryTaylorKernel x := by
  unfold montgomeryTaylorKernel
  rw [show (-x - Real.sqrt 2) / 2 = -((x + Real.sqrt 2) / 2) by ring,
    show (-x + Real.sqrt 2) / 2 = -((x - Real.sqrt 2) / 2) by ring,
    Real.sinc_neg, Real.sinc_neg]
  ring

/-! ## Three shifted span ledgers -/

/-- Consecutive gap of a real sequence. -/
def consecutiveGap (x : ℕ → ℝ) (i : ℕ) : ℝ := x (i + 1) - x i

/-- Gaps in one residue class modulo three, truncated to the first `n`
gaps. -/
def residueGapSum (x : ℕ → ℝ) (n r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, if i % 3 = r then consecutiveGap x i else 0

/-- Sum of the spans of triples beginning at the shift `r`. -/
def shiftedTripleSpanSum (x : ℕ → ℝ) (m r : ℕ) : ℝ :=
  ∑ b ∈ Finset.range ((m - r) / 3),
    (x (r + 3 * b + 2) - x (r + 3 * b))

/-- Indices of the first and second gaps internal to the shifted triples. -/
def shiftedFirstGapIndices (m r : ℕ) : Finset ℕ :=
  (Finset.range ((m - r) / 3)).image (fun b => r + 3 * b)

/-- Indices of the second internal gaps in the triples beginning at shift
`r`. -/
def shiftedSecondGapIndices (m r : ℕ) : Finset ℕ :=
  (Finset.range ((m - r) / 3)).image (fun b => r + 3 * b + 1)

/-- The first `n` gap indices lying in residue class `r` modulo three. -/
def gapResidueFinset (n r : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun i => i % 3 = r)

lemma consecutiveGap_nonneg {x : ℕ → ℝ} (hx : Monotone x) (i : ℕ) :
    0 ≤ consecutiveGap x i := by
  unfold consecutiveGap
  exact sub_nonneg.mpr (hx (Nat.le_add_right i 1))

lemma residueGapSum_nonneg {x : ℕ → ℝ} (hx : Monotone x) (n r : ℕ) :
    0 ≤ residueGapSum x n r := by
  unfold residueGapSum
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact consecutiveGap_nonneg hx i
  · exact le_rfl

lemma residueGapSum_eq_sum_gapResidueFinset
    (x : ℕ → ℝ) (n r : ℕ) :
    residueGapSum x n r =
      ∑ i ∈ gapResidueFinset n r, consecutiveGap x i := by
  unfold residueGapSum gapResidueFinset
  simp only [Finset.sum_filter]

lemma shiftedTripleSpanSum_eq_gap_sums
    (x : ℕ → ℝ) (m r : ℕ) :
    shiftedTripleSpanSum x m r =
      (∑ i ∈ shiftedFirstGapIndices m r, consecutiveGap x i) +
        ∑ i ∈ shiftedSecondGapIndices m r, consecutiveGap x i := by
  have hinj0 : Function.Injective (fun b : ℕ => r + 3 * b) := by
    intro a b h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) (Nat.add_left_cancel h)
  have hinj1 : Function.Injective (fun b : ℕ => r + 3 * b + 1) := by
    intro a b h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num)
      (Nat.add_left_cancel (Nat.add_right_cancel h))
  unfold shiftedTripleSpanSum shiftedFirstGapIndices shiftedSecondGapIndices
  rw [Finset.sum_image hinj0.injOn, Finset.sum_image hinj1.injOn,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  unfold consecutiveGap
  ring

lemma shiftedFirstGapIndices_zero_subset (m : ℕ) :
    shiftedFirstGapIndices m 0 ⊆ gapResidueFinset (m - 1) 0 := by
  intro i hi
  simp only [shiftedFirstGapIndices, Finset.mem_image, Finset.mem_range] at hi
  obtain ⟨b, hb, rfl⟩ := hi
  simp only [gapResidueFinset, Finset.mem_filter, Finset.mem_range,
    zero_add, Nat.mul_mod, Nat.reduceMod, zero_mul, and_true]
  omega

lemma shiftedSecondGapIndices_zero_subset (m : ℕ) :
    shiftedSecondGapIndices m 0 ⊆ gapResidueFinset (m - 1) 1 := by
  intro i hi
  simp only [shiftedSecondGapIndices, Finset.mem_image, Finset.mem_range] at hi
  obtain ⟨b, hb, rfl⟩ := hi
  simp only [gapResidueFinset, Finset.mem_filter, Finset.mem_range,
    zero_add, Nat.add_mod, Nat.mul_mod, Nat.reduceMod, zero_mul,
    and_true]
  omega

lemma shiftedFirstGapIndices_one_subset (m : ℕ) :
    shiftedFirstGapIndices m 1 ⊆ gapResidueFinset (m - 1) 1 := by
  intro i hi
  simp only [shiftedFirstGapIndices, Finset.mem_image, Finset.mem_range] at hi
  obtain ⟨b, hb, rfl⟩ := hi
  simp only [gapResidueFinset, Finset.mem_filter, Finset.mem_range,
    Nat.add_mod, Nat.mul_mod, Nat.reduceMod, zero_mul, add_zero, and_true]
  omega

lemma shiftedSecondGapIndices_one_subset (m : ℕ) :
    shiftedSecondGapIndices m 1 ⊆ gapResidueFinset (m - 1) 2 := by
  intro i hi
  simp only [shiftedSecondGapIndices, Finset.mem_image, Finset.mem_range] at hi
  obtain ⟨b, hb, rfl⟩ := hi
  simp only [gapResidueFinset, Finset.mem_filter, Finset.mem_range,
    Nat.add_mod, Nat.mul_mod, Nat.reduceMod, zero_mul, add_zero, and_true]
  omega

lemma shiftedFirstGapIndices_two_subset (m : ℕ) :
    shiftedFirstGapIndices m 2 ⊆ gapResidueFinset (m - 1) 2 := by
  intro i hi
  simp only [shiftedFirstGapIndices, Finset.mem_image, Finset.mem_range] at hi
  obtain ⟨b, hb, rfl⟩ := hi
  simp only [gapResidueFinset, Finset.mem_filter, Finset.mem_range,
    Nat.add_mod, Nat.mul_mod, Nat.reduceMod, zero_mul, add_zero, and_true]
  omega

lemma shiftedSecondGapIndices_two_subset (m : ℕ) :
    shiftedSecondGapIndices m 2 ⊆ gapResidueFinset (m - 1) 0 := by
  intro i hi
  simp only [shiftedSecondGapIndices, Finset.mem_image, Finset.mem_range] at hi
  obtain ⟨b, hb, rfl⟩ := hi
  simp only [gapResidueFinset, Finset.mem_filter, Finset.mem_range,
    Nat.add_mod, Nat.mul_mod, Nat.reduceMod, zero_mul, add_zero, and_true]
  omega

lemma shiftedTripleSpanSum_zero_le_residues
    {x : ℕ → ℝ} (hx : Monotone x) (m : ℕ) :
    shiftedTripleSpanSum x m 0 ≤
      residueGapSum x (m - 1) 0 + residueGapSum x (m - 1) 1 := by
  rw [shiftedTripleSpanSum_eq_gap_sums,
    residueGapSum_eq_sum_gapResidueFinset,
    residueGapSum_eq_sum_gapResidueFinset]
  apply add_le_add
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (shiftedFirstGapIndices_zero_subset m)
      (fun i hi hnot => consecutiveGap_nonneg hx i)
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (shiftedSecondGapIndices_zero_subset m)
      (fun i hi hnot => consecutiveGap_nonneg hx i)

lemma shiftedTripleSpanSum_one_le_residues
    {x : ℕ → ℝ} (hx : Monotone x) (m : ℕ) :
    shiftedTripleSpanSum x m 1 ≤
      residueGapSum x (m - 1) 1 + residueGapSum x (m - 1) 2 := by
  rw [shiftedTripleSpanSum_eq_gap_sums,
    residueGapSum_eq_sum_gapResidueFinset,
    residueGapSum_eq_sum_gapResidueFinset]
  apply add_le_add
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (shiftedFirstGapIndices_one_subset m)
      (fun i hi hnot => consecutiveGap_nonneg hx i)
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (shiftedSecondGapIndices_one_subset m)
      (fun i hi hnot => consecutiveGap_nonneg hx i)

lemma shiftedTripleSpanSum_two_le_residues
    {x : ℕ → ℝ} (hx : Monotone x) (m : ℕ) :
    shiftedTripleSpanSum x m 2 ≤
      residueGapSum x (m - 1) 2 + residueGapSum x (m - 1) 0 := by
  rw [shiftedTripleSpanSum_eq_gap_sums,
    residueGapSum_eq_sum_gapResidueFinset,
    residueGapSum_eq_sum_gapResidueFinset]
  apply add_le_add
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (shiftedFirstGapIndices_two_subset m)
      (fun i hi hnot => consecutiveGap_nonneg hx i)
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (shiftedSecondGapIndices_two_subset m)
      (fun i hi hnot => consecutiveGap_nonneg hx i)

/-- The three residue ledgers partition every gap exactly once. -/
lemma residueGapSum_zero_add_one_add_two
    (x : ℕ → ℝ) (n : ℕ) :
    residueGapSum x n 0 + residueGapSum x n 1 +
        residueGapSum x n 2 =
      ∑ i ∈ Finset.range n, consecutiveGap x i := by
  unfold residueGapSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hmod : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : i % 3 <;> simp

/-- All adjacent gaps telescope to the endpoint difference. -/
lemma sum_consecutiveGap_range (x : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, consecutiveGap x i) = x n - x 0 := by
  simpa only [consecutiveGap] using Finset.sum_range_sub x n

/-- One shifted packing pays at most two-thirds of the total ordered span.
The three alternatives are kept explicit so downstream code can construct
the corresponding literal packing without a choice oracle over real data. -/
theorem exists_shiftedTripleSpanSum_three_le_two_total
    {x : ℕ → ℝ} (hx : Monotone x) (m : ℕ) :
    ∃ r : ℕ, r ≤ 2 ∧
      3 * shiftedTripleSpanSum x m r ≤
        2 * (x (m - 1) - x 0) := by
  let R0 := residueGapSum x (m - 1) 0
  let R1 := residueGapSum x (m - 1) 1
  let R2 := residueGapSum x (m - 1) 2
  let S0 := shiftedTripleSpanSum x m 0
  let S1 := shiftedTripleSpanSum x m 1
  let S2 := shiftedTripleSpanSum x m 2
  have hs0 : S0 ≤ R0 + R1 := shiftedTripleSpanSum_zero_le_residues hx m
  have hs1 : S1 ≤ R1 + R2 := shiftedTripleSpanSum_one_le_residues hx m
  have hs2 : S2 ≤ R2 + R0 := shiftedTripleSpanSum_two_le_residues hx m
  have hres : R0 + R1 + R2 = x (m - 1) - x 0 := by
    dsimp [R0, R1, R2]
    rw [residueGapSum_zero_add_one_add_two,
      sum_consecutiveGap_range]
  by_cases h0 : 3 * S0 ≤ 2 * (x (m - 1) - x 0)
  · exact ⟨0, by norm_num, h0⟩
  by_cases h1 : 3 * S1 ≤ 2 * (x (m - 1) - x 0)
  · exact ⟨1, by norm_num, h1⟩
  refine ⟨2, by norm_num, ?_⟩
  by_contra h2
  have h0' := lt_of_not_ge h0
  have h1' := lt_of_not_ge h1
  have h2' := lt_of_not_ge h2
  linarith

/-! ## Extending selected triples to the exact zero-side padding ledger -/

lemma card_le_three_mul_ceilThird (n : ℕ) :
    n ≤ 3 * ((n + 2) / 3) := by omega

lemma ceilThird_padding_le_two (n : ℕ) :
    3 * ((n + 2) / 3) - n ≤ 2 := by omega

/-- Any injective family of selected triples can be placed in the first
blocks of a complete packing of `α`.  The complete packing adds exactly the
usual `0`, `1`, or `2` zero columns. -/
theorem exists_paddedTripleEquiv_extending
    {α : Type*} [Fintype α] (q : ℕ)
    (hq : q ≤ (Fintype.card α + 2) / 3)
    (f : Fin 3 × Fin q ↪ α) :
    ∃ e : Fin 3 × Fin ((Fintype.card α + 2) / 3) ≃
        Sum α (Fin (3 * ((Fintype.card α + 2) / 3) - Fintype.card α)),
      ∀ j b, e (j, Fin.castLE hq b) = Sum.inl (f (j, b)) := by
  classical
  let Q : ℕ := (Fintype.card α + 2) / 3
  let pad : ℕ := 3 * Q - Fintype.card α
  have hnQ : Fintype.card α ≤ 3 * Q := by
    dsimp [Q]
    exact card_le_three_mul_ceilThird _
  have hcard : Fintype.card (Fin 3 × Fin Q) =
      Fintype.card (Sum α (Fin pad)) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_sum]
    omega
  let e0 : Fin 3 × Fin Q ≃ Sum α (Fin pad) :=
    Fintype.equivOfCardEq hcard
  let u : Fin 3 × Fin q → Fin 3 × Fin Q :=
    fun p => (p.1, Fin.castLE hq p.2)
  have hu : Function.Injective u := by
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ hab
    simpa only [u, Prod.mk.injEq, Fin.castLE_inj] using hab
  let g : Fin 3 × Fin q → Sum α (Fin pad) :=
    fun p => Sum.inl (f p)
  have hg : Function.Injective g := Sum.inl_injective.comp f.injective
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun p => e0 (u p)) g (e0.injective.comp hu) hg
  refine ⟨e0.trans σ, ?_⟩
  intro j b
  change σ (e0 (u (j, b))) = g (j, b)
  exact hσ (j, b)

/-! ## Ordered literal simple zeros -/

/-- Ordinate of a literal simple critical zero in the enlarged Zeta23
window. -/
def simpleZeroOrdinate
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T : ℝ}
    {hconj : Zeta23.ZeroSide.PhiHatConj T P}
    (z : (Zeta23.ZeroSide.blockData Z T P hconj).S₁) : ℝ :=
  ((z.1 : Zeta23.ZeroSide.ZI Z T) : ℂ).im

lemma simpleZeroOrdinate_injective
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T : ℝ}
    {hconj : Zeta23.ZeroSide.PhiHatConj T P} :
    Function.Injective
      (simpleZeroOrdinate (Z := Z) (P := P) (T := T) (hconj := hconj)) := by
  intro z z' him
  apply Subtype.ext
  apply Subtype.ext
  apply Complex.ext
  · rw [blockData_simpleZero_re_eq_half z,
      blockData_simpleZero_re_eq_half z']
  · exact him

/-- Canonical ordering of literal simple critical zeros by ordinate. -/
noncomputable instance simpleZeroLinearOrder
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T : ℝ}
    {hconj : Zeta23.ZeroSide.PhiHatConj T P} :
    LinearOrder (Zeta23.ZeroSide.blockData Z T P hconj).S₁ :=
  LinearOrder.lift' simpleZeroOrdinate simpleZeroOrdinate_injective

/-- The literal simple zeros far enough from both finite-sampler endpoints. -/
def interiorSimpleZeros
    (Z : Zeta23.ZeroConfig) (P : Zeta23.Params) (T : ℝ)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    Finset (Zeta23.ZeroSide.blockData Z T P hconj).S₁ :=
  Finset.univ.filter (fun z =>
    T + Real.sqrt T ≤ simpleZeroOrdinate z ∧
      simpleZeroOrdinate z ≤ 2 * T - Real.sqrt T)

lemma mem_interiorSimpleZeros_iff
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T : ℝ}
    {hconj : Zeta23.ZeroSide.PhiHatConj T P}
    {z : (Zeta23.ZeroSide.blockData Z T P hconj).S₁} :
    z ∈ interiorSimpleZeros Z P T hconj ↔
      T + Real.sqrt T ≤ simpleZeroOrdinate z ∧
        simpleZeroOrdinate z ≤ 2 * T - Real.sqrt T := by
  simp [interiorSimpleZeros]

lemma shiftedTripleIndex_lt
    {m r q : ℕ} (hq : q = (m - r) / 3)
    (j : Fin 3) (b : Fin q) :
    r + 3 * (b : ℕ) + (j : ℕ) < m := by omega

lemma shiftedTripleIndex_injective
    {r q : ℕ} : Function.Injective
      (fun p : Fin 3 × Fin q => r + 3 * (p.2 : ℕ) + (p.1 : ℕ)) := by
  rintro ⟨j, b⟩ ⟨j', b'⟩ h
  change r + 3 * (b : ℕ) + (j : ℕ) =
    r + 3 * (b' : ℕ) + (j' : ℕ) at h
  have h0 : 3 * (b : ℕ) + (j : ℕ) =
      3 * (b' : ℕ) + (j' : ℕ) := by omega
  have hjval : (j : ℕ) = (j' : ℕ) := by
    have hm := congrArg (fun n : ℕ => n % 3) h0
    simpa [Nat.add_mod, Nat.mod_eq_of_lt j.isLt,
      Nat.mod_eq_of_lt j'.isLt] using hm
  have hj : j = j' := Fin.ext hjval
  subst j'
  have hbmul : 3 * (b : ℕ) = 3 * (b' : ℕ) :=
    Nat.add_right_cancel h0
  have hbval : (b : ℕ) = (b' : ℕ) :=
    Nat.eq_of_mul_eq_mul_left (by norm_num) hbmul
  exact Prod.ext rfl (Fin.ext hbval)

lemma shiftedTripleCount_le_ceilThird
    {m n r q : ℕ} (hmn : m ≤ n) (hq : q = (m - r) / 3) :
    q ≤ (n + 2) / 3 := by omega

lemma interiorCard_le_fullCard
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T : ℝ}
    {hconj : Zeta23.ZeroSide.PhiHatConj T P} :
    (interiorSimpleZeros Z P T hconj).card ≤
      Fintype.card (Zeta23.ZeroSide.blockData Z T P hconj).S₁ := by
  rw [← Finset.card_univ]
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma interiorCard_le_three_mul_shiftedCount_add_four
    {m r q : ℕ} (hr : r ≤ 2) (hq : q = (m - r) / 3) :
    m ≤ 3 * q + 4 := by omega

/-- The selected triples obtained by taking every three consecutive members
of a sorted finset after an initial shift. -/
def shiftedOrderEmbedding
    {α : Type*} [LinearOrder α]
    (s : Finset α) (r q : ℕ) (hq : q = (s.card - r) / 3) :
    Fin 3 × Fin q ↪ α :=
  let index : Fin 3 × Fin q ↪ Fin s.card :=
    { toFun := fun p =>
        ⟨r + 3 * (p.2 : ℕ) + (p.1 : ℕ),
          shiftedTripleIndex_lt hq p.1 p.2⟩
      inj' := fun _ _ h => shiftedTripleIndex_injective (Fin.ext_iff.mp h) }
  index.trans (s.orderEmbOfFin rfl).toEmbedding

@[simp] lemma shiftedOrderEmbedding_mem
    {α : Type*} [LinearOrder α]
    (s : Finset α) (r q : ℕ) (hq : q = (s.card - r) / 3)
    (p : Fin 3 × Fin q) :
    shiftedOrderEmbedding s r q hq p ∈ s := by
  exact Finset.orderEmbOfFin_mem s rfl _

lemma shiftedOrderEmbedding_monotone_first
    {α : Type*} [LinearOrder α]
    (s : Finset α) (r q : ℕ) (hq : q = (s.card - r) / 3)
    (b : Fin q) {i j : Fin 3} (hij : i ≤ j) :
    shiftedOrderEmbedding s r q hq (i, b) ≤
      shiftedOrderEmbedding s r q hq (j, b) := by
  apply (s.orderEmbOfFin rfl).monotone
  apply Fin.mk_le_mk.mpr
  change r + 3 * (b : ℕ) + (i : ℕ) ≤
    r + 3 * (b : ℕ) + (j : ℕ)
  omega

/-- Among the three shifts, a sorted finite family admits consecutive
triples whose total span is at most two-thirds of any enclosing interval. -/
theorem exists_shiftedOrderEmbedding_span_le
    {α : Type*} [LinearOrder α]
    (s : Finset α) (v : α → ℝ) (hv : Monotone v)
    {lo hi : ℝ} (hlohi : lo ≤ hi)
    (hbounds : ∀ z ∈ s, lo ≤ v z ∧ v z ≤ hi) :
    ∃ r q : ℕ, ∃ hq : q = (s.card - r) / 3,
      r ≤ 2 ∧
        3 * (∑ b : Fin q,
          (v (shiftedOrderEmbedding s r q hq (2, b)) -
            v (shiftedOrderEmbedding s r q hq (0, b)))) ≤
          2 * (hi - lo) := by
  by_cases hs0 : s.card = 0
  · refine ⟨0, 0, ?_, by norm_num, ?_⟩
    · simp [hs0]
    · simp
      linarith
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hs0
  let cap : ℕ → Fin s.card := fun n =>
    ⟨min n M, by omega⟩
  let x : ℕ → ℝ := fun n => v (s.orderEmbOfFin rfl (cap n))
  have hx : Monotone x := by
    intro a b hab
    apply hv
    apply (s.orderEmbOfFin rfl).monotone
    apply Fin.mk_le_mk.mpr
    exact min_le_min hab le_rfl
  obtain ⟨r, hr, hspan⟩ :=
    exists_shiftedTripleSpanSum_three_le_two_total hx s.card
  let q : ℕ := (s.card - r) / 3
  have hq : q = (s.card - r) / 3 := rfl
  let f : Fin 3 × Fin q ↪ α := shiftedOrderEmbedding s r q hq
  have hxapply : ∀ (j : Fin 3) (b : Fin q),
      x (r + 3 * (b : ℕ) + (j : ℕ)) = v (f (j, b)) := by
    intro j b
    have hidx := shiftedTripleIndex_lt hq j b
    have hleM : r + 3 * (b : ℕ) + (j : ℕ) ≤ M := by omega
    simp only [x, cap, Nat.min_eq_left hleM, f,
      shiftedOrderEmbedding, Function.Embedding.trans_apply]
    apply congrArg v
    apply congrArg (s.orderEmbOfFin rfl)
    apply Fin.ext
    rfl
  have hsum : shiftedTripleSpanSum x s.card r =
      ∑ b : Fin q,
        (v (f (2, b)) - v (f (0, b))) := by
    unfold shiftedTripleSpanSum
    rw [← hq]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro b hb
    have h2 := hxapply (2 : Fin 3) b
    have h0 := hxapply (0 : Fin 3) b
    norm_num at h2 h0 ⊢
    rw [h2, h0]
  have hfirst := hbounds (s.orderEmbOfFin rfl (cap 0))
    (Finset.orderEmbOfFin_mem s rfl _)
  have hlast := hbounds (s.orderEmbOfFin rfl (cap (s.card - 1)))
    (Finset.orderEmbOfFin_mem s rfl _)
  have hx0 : x 0 = v (s.orderEmbOfFin rfl (cap 0)) := rfl
  have hxlast : x (s.card - 1) =
      v (s.orderEmbOfFin rfl (cap (s.card - 1))) := rfl
  refine ⟨r, q, hq, hr, ?_⟩
  change 3 * (∑ b : Fin q, (v (f (2, b)) - v (f (0, b)))) ≤ _
  rw [← hsum]
  rw [hx0, hxlast] at hspan
  linarith [hfirst.1, hlast.2]

/-- A concrete packing of the actual literal simple-zero columns.  The
selected blocks are consecutive interior zeros, their span has the sharp
three-shift `2/3` ledger, and the full zero-side equivalence has at most two
padding columns. -/
theorem exists_literalInteriorTriplePacking
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T : ℝ}
    (hT : 4 ≤ T)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    let α := (Zeta23.ZeroSide.blockData Z T P hconj).S₁
    let s := interiorSimpleZeros Z P T hconj
    let Q := (Fintype.card α + 2) / 3
    let pad := 3 * Q - Fintype.card α
    ∃ r q : ℕ, ∃ f : Fin 3 × Fin q ↪ α,
      ∃ e : Fin 3 × Fin Q ≃ Sum α (Fin pad),
      ∃ hqQ : q ≤ Q,
        r ≤ 2 ∧
        q = (s.card - r) / 3 ∧
        (∀ p, f p ∈ s) ∧
        (∀ b : Fin q,
          simpleZeroOrdinate (f (0, b)) ≤
              simpleZeroOrdinate (f (1, b)) ∧
            simpleZeroOrdinate (f (1, b)) ≤
              simpleZeroOrdinate (f (2, b))) ∧
        3 * (∑ b : Fin q,
          (simpleZeroOrdinate (f (2, b)) -
            simpleZeroOrdinate (f (0, b)))) ≤ 2 * T ∧
        s.card ≤ 3 * q + 4 ∧
        pad ≤ 2 ∧
        ∀ j b, e (j, Fin.castLE hqQ b) = Sum.inl (f (j, b)) := by
  classical
  let α := (Zeta23.ZeroSide.blockData Z T P hconj).S₁
  let ord : α → ℝ := simpleZeroOrdinate
  let s : Finset α := interiorSimpleZeros Z P T hconj
  let Q : ℕ := (Fintype.card α + 2) / 3
  let pad : ℕ := 3 * Q - Fintype.card α
  have hord : Monotone ord := by
    intro a b hab
    exact hab
  have hsqrt : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hsqrtSq : Real.sqrt T ^ 2 = T := Real.sq_sqrt (by linarith)
  have hlohi : T + Real.sqrt T ≤ 2 * T - Real.sqrt T := by
    nlinarith [sq_nonneg (Real.sqrt T - 2)]
  have hbounds : ∀ z ∈ s,
      T + Real.sqrt T ≤ ord z ∧ ord z ≤ 2 * T - Real.sqrt T := by
    intro z hz
    exact mem_interiorSimpleZeros_iff.mp hz
  obtain ⟨r, q, hq, hr, hspan0⟩ :=
    exists_shiftedOrderEmbedding_span_le s ord hord hlohi hbounds
  let f : Fin 3 × Fin q ↪ α := shiftedOrderEmbedding s r q hq
  have hspan : 3 * (∑ b : Fin q,
      (ord (f (2, b)) - ord (f (0, b)))) ≤ 2 * T := by
    calc
      3 * (∑ b : Fin q, (ord (f (2, b)) - ord (f (0, b)))) ≤
          2 * ((2 * T - Real.sqrt T) - (T + Real.sqrt T)) := hspan0
      _ ≤ 2 * T := by nlinarith
  have hmn : s.card ≤ Fintype.card α := by
    exact interiorCard_le_fullCard
  have hqQ : q ≤ Q := by
    dsimp [Q]
    exact shiftedTripleCount_le_ceilThird hmn hq
  obtain ⟨e, he⟩ := exists_paddedTripleEquiv_extending q hqQ f
  refine ⟨r, q, f, e, hqQ, hr, hq, ?_, ?_, hspan, ?_, ?_, he⟩
  · intro p
    exact shiftedOrderEmbedding_mem s r q hq p
  · intro b
    constructor
    · have h := shiftedOrderEmbedding_monotone_first s r q hq b
          (show (0 : Fin 3) ≤ 1 by omega)
      exact h
    · have h := shiftedOrderEmbedding_monotone_first s r q hq b
          (show (1 : Fin 3) ≤ 2 by omega)
      exact h
  · exact interiorCard_le_three_mul_shiftedCount_add_four hr hq
  · exact ceilThird_padding_le_two _

/-! ## Selected blocks inside the literal packed Gram -/

/-- On positions mapped to actual zeros, the padded Gram is exactly the
corresponding principal entry of the literal simple-zero Gram. -/
lemma zetaSimplePackedGram_apply_of_inl
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T : ℝ}
    {κ β : Type*}
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (e : Fin 3 × β ≃
      Sum (Zeta23.ZeroSide.blockData Z T P hconj).S₁ κ)
    (p p' : Fin 3 × β)
    (z z' : (Zeta23.ZeroSide.blockData Z T P hconj).S₁)
    (hp : e p = Sum.inl z) (hp' : e p' = Sum.inl z') :
    zetaSimplePackedGram Z T P hconj e p p' =
      zetaSimpleGram Z T P hconj z z' := by
  classical
  unfold zetaSimplePackedGram zetaSimpleGram
  unfold ZeroBlockData.columnGram ZeroBlockData.simpleGram
  rw [Matrix.mul_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Matrix.conjTranspose_apply,
    Zeta23.ZeroSide.RankTraceMult.Wmat, RCLike.star_def,
    ZeroBlockData.paddedPackedFamily, hp, hp', Sum.elim_inl]

/-- Total entrywise endpoint-sampler error used uniformly on every selected
interior block. -/
def endpointSamplerError (P : Zeta23.Params) (T : ℝ) : ℝ :=
  14 * (P.w / P.L T) +
    finiteSamplerTailEnvelope P T /
      ((P.atD T).a T * P.L T ^ 2)

lemma endpointSamplerError_nonneg
    {P : Zeta23.Params} (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T) (hT : 0 < T) :
    0 ≤ endpointSamplerError P T := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have ha : 0 < (P.atD T).a T := by
    linarith [(Zeta23.ThmD.aD_range_of hP h8 h4pi).1]
  unfold endpointSamplerError
  exact add_nonneg
    (mul_nonneg (by norm_num) (div_nonneg (by linarith [hP.one_le_w]) hL.le))
    (div_nonneg (finiteSamplerTailEnvelope_nonneg hT hL)
      (mul_nonneg ha.le (sq_nonneg _)))

/-- The complete literal-Gram approximation error vanishes at the endpoint.
This combines the compact-window ramp error with the proved finite Poisson
tail estimate; no infinite sampler is retained in the conclusion. -/
theorem tendsto_endpointSamplerError_zero
    {P : Zeta23.Params} (hP : P.Valid) :
    Tendsto (endpointSamplerError P) atTop (nhds 0) := by
  have hramp : Tendsto (fun T : ℝ => 14 * (P.w / P.L T))
      atTop (nhds 0) := by
    have hquot : Tendsto (fun T : ℝ => P.w / P.L T)
        atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (Zeta23.ThmD.tendsto_L hP)
    simpa using hquot.const_mul 14
  change Tendsto (fun T : ℝ =>
    14 * (P.w / P.L T) +
      finiteSamplerTailEnvelope P T /
        ((P.atD T).a T * P.L T ^ 2)) atTop (nhds 0)
  simpa only [add_zero] using
    hramp.add (tendsto_finiteSamplerTailEnvelope_normalized_zero hP)

/-- A stable affine certificate may be capped at one after paying its explicit
kernel-approximation error. -/
lemma affine_le_min_energy_add_cost
    {A energy ideal cost err : ℝ}
    (hA1 : A ≤ 1)
    (hcost0 : 0 ≤ cost) (herr0 : 0 ≤ err)
    (haffine : A ≤ ideal + cost)
    (hclose : ideal - err ≤ energy) :
    A ≤ min energy 1 + cost + err := by
  rcases le_or_gt energy 1 with hle | hgt
  · rw [min_eq_left hle]
    linarith
  · rw [min_eq_right hgt.le]
    linarith

/-- The checked affine endpoint certificate produces a quantitative lower
bound on the capped energies of an actual packed literal Zeta23 Gram.  Every
loss is displayed: two-thirds span, vanishing sampler error, four discarded
interior columns, and at most two padding columns. -/
theorem exists_literalPackedEnergy_affine_lower
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} (hP : P.Valid)
    (hlam : P.lam = 1) {T : ℝ}
    (hT : 4 ≤ T)
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (hgrid : 2 * Real.pi / P.L T ≤ Real.sqrt T / 2)
    (hconj : Zeta23.ZeroSide.PhiHatConj T (P.atD T))
    {A B : ℝ} (hB0 : 0 < B) (hA1 : A ≤ 1)
    (hcert : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      A ≤ montgomeryTaylorTripleEnergy a b + B * (a + b))
    (herr1 : endpointSamplerError P T ≤ 1) :
    let α := (Zeta23.ZeroSide.blockData Z T (P.atD T) hconj).S₁
    let Q := (Fintype.card α + 2) / 3
    let pad := 3 * Q - Fintype.card α
    ∃ q : ℕ, ∃ e : Fin 3 × Fin Q ≃ Sum α (Fin pad),
      q ≤ Q ∧
      (interiorSimpleZeros Z (P.atD T) T hconj).card ≤ 3 * q + 4 ∧
      pad ≤ 2 ∧
      A * (q : ℝ) ≤
        (∑ b : Fin Q, min
          (ZeroBlockData.tripleOffDiagEnergy
            ((zetaSimplePackedGram Z T (P.atD T) hconj e).submatrix
              (fun j : Fin 3 => (j, b))
              (fun j : Fin 3 => (j, b)))) 1) +
          (2 * B * P.L T * T) / 3 +
          36 * endpointSamplerError P T * (q : ℝ) := by
  classical
  have hTpos : 0 < T := by linarith
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have herr0 : 0 ≤ endpointSamplerError P T :=
    endpointSamplerError_nonneg hP h8 h4pi hTpos
  obtain ⟨r, q, f, e, hqQ, hr, hq, hmem, hord, hspan,
      hcard, hpad, he⟩ :=
    exists_literalInteriorTriplePacking (Z := Z) (P := P.atD T) hT hconj
  let Q : ℕ :=
    (Fintype.card
      (Zeta23.ZeroSide.blockData Z T (P.atD T) hconj).S₁ + 2) / 3
  let packed := zetaSimplePackedGram Z T (P.atD T) hconj e
  let E : Fin Q → ℝ := fun b => min
    (ZeroBlockData.tripleOffDiagEnergy
      (packed.submatrix (fun j : Fin 3 => (j, b))
        (fun j : Fin 3 => (j, b)))) 1
  have hper : ∀ b : Fin q,
      A ≤ E (Fin.castLE hqQ b) +
        B * (P.L T *
          (simpleZeroOrdinate (f (2, b)) -
            simpleZeroOrdinate (f (0, b)))) +
        36 * endpointSamplerError P T := by
    intro b
    let z0 := f ((0 : Fin 3), b)
    let z1 := f ((1 : Fin 3), b)
    let z2 := f ((2 : Fin 3), b)
    let a : ℝ := P.L T *
      (simpleZeroOrdinate z1 - simpleZeroOrdinate z0)
    let c : ℝ := P.L T *
      (simpleZeroOrdinate z2 - simpleZeroOrdinate z1)
    let K : Matrix (Fin 3) (Fin 3) ℂ :=
      packed.submatrix
        (fun j : Fin 3 => (j, Fin.castLE hqQ b))
        (fun j : Fin 3 => (j, Fin.castLE hqQ b))
    have ha0 : 0 ≤ a := by
      dsimp [a, z0, z1]
      exact mul_nonneg hL.le (sub_nonneg.mpr (hord b).1)
    have hc0 : 0 ≤ c := by
      dsimp [c, z1, z2]
      exact mul_nonneg hL.le (sub_nonneg.mpr (hord b).2)
    have hz0 := mem_interiorSimpleZeros_iff.mp (hmem ((0 : Fin 3), b))
    have hz1 := mem_interiorSimpleZeros_iff.mp (hmem ((1 : Fin 3), b))
    have hz2 := mem_interiorSimpleZeros_iff.mp (hmem ((2 : Fin 3), b))
    have h01raw := atD_zetaSimpleGram_apply_close_montgomeryTaylorKernel
      hP hlam h8 h4pi hTpos hgrid z0 z1 hz0.1 hz0.2 hz1.1 hz1.2
    have h12raw := atD_zetaSimpleGram_apply_close_montgomeryTaylorKernel
      hP hlam h8 h4pi hTpos hgrid z1 z2 hz1.1 hz1.2 hz2.1 hz2.2
    have h02raw := atD_zetaSimpleGram_apply_close_montgomeryTaylorKernel
      hP hlam h8 h4pi hTpos hgrid z0 z2 hz0.1 hz0.2 hz2.1 hz2.2
    have h01 : ‖K 0 1 - (montgomeryTaylorKernel a : ℂ)‖ ≤
        endpointSamplerError P T := by
      change ‖packed (0, Fin.castLE hqQ b) (1, Fin.castLE hqQ b) -
        (montgomeryTaylorKernel a : ℂ)‖ ≤ _
      dsimp only [packed]
      rw [zetaSimplePackedGram_apply_of_inl hconj e _ _ z0 z1
        (he 0 b) (he 1 b)]
      have hsign : P.L T *
          (simpleZeroOrdinate z0 - simpleZeroOrdinate z1) = -a := by
        dsimp [a]
        ring_nf
      have hsignRaw : P.L T *
          (((z0.1 : Zeta23.ZeroSide.ZI Z T) : ℂ).im -
            ((z1.1 : Zeta23.ZeroSide.ZI Z T) : ℂ).im) = -a := by
        simpa only [simpleZeroOrdinate] using hsign
      rw [hsignRaw, montgomeryTaylorKernel_neg] at h01raw
      simpa only [endpointSamplerError] using h01raw
    have h12 : ‖K 1 2 - (montgomeryTaylorKernel c : ℂ)‖ ≤
        endpointSamplerError P T := by
      change ‖packed (1, Fin.castLE hqQ b) (2, Fin.castLE hqQ b) -
        (montgomeryTaylorKernel c : ℂ)‖ ≤ _
      dsimp only [packed]
      rw [zetaSimplePackedGram_apply_of_inl hconj e _ _ z1 z2
        (he 1 b) (he 2 b)]
      have hsign : P.L T *
          (simpleZeroOrdinate z1 - simpleZeroOrdinate z2) = -c := by
        dsimp [c]
        ring
      have hsignRaw : P.L T *
          (((z1.1 : Zeta23.ZeroSide.ZI Z T) : ℂ).im -
            ((z2.1 : Zeta23.ZeroSide.ZI Z T) : ℂ).im) = -c := by
        simpa only [simpleZeroOrdinate] using hsign
      rw [hsignRaw, montgomeryTaylorKernel_neg] at h12raw
      simpa only [endpointSamplerError] using h12raw
    have h02 : ‖K 0 2 - (montgomeryTaylorKernel (a + c) : ℂ)‖ ≤
        endpointSamplerError P T := by
      change ‖packed (0, Fin.castLE hqQ b) (2, Fin.castLE hqQ b) -
        (montgomeryTaylorKernel (a + c) : ℂ)‖ ≤ _
      dsimp only [packed]
      rw [zetaSimplePackedGram_apply_of_inl hconj e _ _ z0 z2
        (he 0 b) (he 2 b)]
      have hsign : P.L T *
          (simpleZeroOrdinate z0 - simpleZeroOrdinate z2) = -(a + c) := by
        dsimp [a, c]
        ring
      have hsignRaw : P.L T *
          (((z0.1 : Zeta23.ZeroSide.ZI Z T) : ℂ).im -
            ((z2.1 : Zeta23.ZeroSide.ZI Z T) : ℂ).im) = -(a + c) := by
        simpa only [simpleZeroOrdinate] using hsign
      rw [hsignRaw, montgomeryTaylorKernel_neg] at h02raw
      simpa only [endpointSamplerError] using h02raw
    have hstable :=
      tripleOffDiagEnergy_ge_montgomeryTaylorTripleEnergy_sub
        K herr0 herr1 h01 h12 h02
    have haffine := hcert a c ha0 hc0
    have hcost0 : 0 ≤ B * (a + c) :=
      mul_nonneg hB0.le (add_nonneg ha0 hc0)
    have hcap := affine_le_min_energy_add_cost hA1 hcost0
      (mul_nonneg (by norm_num) herr0) haffine hstable
    have hac : a + c = P.L T *
        (simpleZeroOrdinate z2 - simpleZeroOrdinate z0) := by
      dsimp [a, c]
      ring
    change A ≤ min (ZeroBlockData.tripleOffDiagEnergy K) 1 + _ + _
    rw [hac] at hcap
    exact hcap
  have hselected :
      A * (q : ℝ) ≤
        (∑ b : Fin q, E (Fin.castLE hqQ b)) +
          B * P.L T *
            (∑ b : Fin q,
              (simpleZeroOrdinate (f (2, b)) -
                simpleZeroOrdinate (f (0, b)))) +
          36 * endpointSamplerError P T * (q : ℝ) := by
    calc
      A * (q : ℝ) = ∑ _b : Fin q, A := by simp [mul_comm]
      _ ≤ ∑ b : Fin q, (E (Fin.castLE hqQ b) +
          B * (P.L T *
            (simpleZeroOrdinate (f (2, b)) -
              simpleZeroOrdinate (f (0, b)))) +
          36 * endpointSamplerError P T) :=
        Finset.sum_le_sum fun b hb => hper b
      _ = (∑ b : Fin q, E (Fin.castLE hqQ b)) +
          B * P.L T *
            (∑ b : Fin q,
              (simpleZeroOrdinate (f (2, b)) -
                simpleZeroOrdinate (f (0, b)))) +
          36 * endpointSamplerError P T * (q : ℝ) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring_nf
  have hE0 : ∀ b : Fin Q, 0 ≤ E b := by
    intro b
    unfold E
    exact le_min (by
      unfold ZeroBlockData.tripleOffDiagEnergy
      positivity) zero_le_one
  have hselectedFull :
      (∑ b : Fin q, E (Fin.castLE hqQ b)) ≤ ∑ b : Fin Q, E b := by
    let emb : Fin q ↪ Fin Q := Fin.castLEEmb hqQ
    calc
      (∑ b : Fin q, E (Fin.castLE hqQ b)) =
          ∑ b ∈ Finset.univ.map emb, E b := by
        rw [Finset.sum_map]
        rfl
      _ ≤ ∑ b ∈ (Finset.univ : Finset (Fin Q)), E b :=
        Finset.sum_le_sum_of_subset_of_nonneg (by simp)
          (fun b hb hnot => hE0 b)
      _ = ∑ b : Fin Q, E b := rfl
  have hspanCost :
      B * P.L T *
          (∑ b : Fin q,
            (simpleZeroOrdinate (f (2, b)) -
              simpleZeroOrdinate (f (0, b)))) ≤
        (2 * B * P.L T * T) / 3 := by
    have hBL : 0 ≤ B * P.L T := mul_nonneg hB0.le hL.le
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith [mul_le_mul_of_nonneg_left hspan hBL]
  refine ⟨q, e, hqQ, hcard, hpad, ?_⟩
  change A * (q : ℝ) ≤ (∑ b : Fin Q, E b) + _ + _
  linarith

end Zeta23InverseSampling
end RiemannGaussian
