import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.BlockPacking
import OpenAISemiprime.Algorithms.SubexponentialSAT.DirectSums

namespace OAI.Algorithms

/-!
# Full-block packing with a variable loss parameter

This is the arithmetic and finite packing step of Section 3.4 of the
multi-color manuscript. The variance and type-label assignment are inputs;
the blocks, coverage, and dimension consequences are proved here.
-/

namespace SubexponentialSAT.SubexpBlockPacking

open scoped BigOperators
open Module

/-- The exact ceiling threshold in equation (3.10). -/
def threshold (N : ℕ) (a ε : ℚ) : ℕ :=
  ⌈(N : ℚ) ^ 3 * a / ε ^ 2⌉₊

/-- The ceiling in the manuscript is precisely the division-free threshold. -/
theorem threshold_le_iff (N D : ℕ) (a ε : ℚ) (hε : 0 < ε) :
    threshold N a ε ≤ D ↔ (N : ℚ) ^ 3 * a ≤ ε ^ 2 * D := by
  rw [threshold, Nat.ceil_le, div_le_iff₀ (sq_pos_of_pos hε)]
  rw [mul_comm (D : ℚ)]

/-- The total squared-deviation estimate controls an individual scaled deviation. -/
theorem scaled_deviation_bound (N D a c ε : ℚ)
    (hN : 0 < N) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hlarge : N ^ 3 * a ≤ ε ^ 2 * D)
    (hsquare : (c - D / N) ^ 2 ≤ N * a * D) :
    |N * c - D| ≤ ε * D := by
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hs : (N * c - D) ^ 2 ≤ (ε * D) ^ 2 := by
    calc
      (N * c - D) ^ 2 = N ^ 2 * (c - D / N) ^ 2 := by
        field_simp
      _ ≤ N ^ 2 * (N * a * D) :=
        mul_le_mul_of_nonneg_left hsquare (sq_nonneg N)
      _ = (N ^ 3 * a) * D := by ring
      _ ≤ (ε ^ 2 * D) * D := mul_le_mul_of_nonneg_right hlarge hD
      _ = (ε * D) ^ 2 := by ring
  simpa only [abs_of_nonneg (mul_nonneg hε hD)] using (sq_le_sq.mp hs)

/-- A scaled lower bound avoids all divisibility and floor issues. -/
theorem count_lower_of_square_bound (N D a c ε : ℚ)
    (hN : 0 < N) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hlarge : N ^ 3 * a ≤ ε ^ 2 * D)
    (hsquare : (c - D / N) ^ 2 ≤ N * a * D) :
    (1 - ε) * D ≤ N * c := by
  have h := (abs_le.mp (scaled_deviation_bound N D a c ε hN hD hε hlarge hsquare)).1
  nlinarith

theorem count_lower_of_deviation_bound {U : Type*} [Fintype U]
    (C : U → ℕ) (D : ℕ) (a ε : ℚ)
    (hN : 0 < Fintype.card U) (hε : 0 ≤ ε)
    (hlarge : (Fintype.card U : ℚ) ^ 3 * a ≤ ε ^ 2 * D)
    (hdev : (∑ u, ((C u : ℚ) - (D : ℚ) / Fintype.card U) ^ 2) ≤
      (Fintype.card U : ℚ) * a * D) (u : U) :
    (1 - ε) * (D : ℚ) ≤ (Fintype.card U : ℚ) * C u := by
  have hone : ((C u : ℚ) - (D : ℚ) / Fintype.card U) ^ 2 ≤
      ∑ v, ((C v : ℚ) - (D : ℚ) / Fintype.card U) ^ 2 :=
    Finset.single_le_sum
      (fun v _ => sq_nonneg ((C v : ℚ) - (D : ℚ) / Fintype.card U))
      (Finset.mem_univ u)
  exact count_lower_of_square_bound (Fintype.card U) D a (C u) ε
    (by exact_mod_cast hN) (by positivity) hε hlarge (hone.trans hdev)

theorem count_fraction_lower_of_deviation_bound {U : Type*} [Fintype U]
    (C : U → ℕ) (D : ℕ) (a ε : ℚ)
    (hN : 0 < Fintype.card U) (hε : 0 ≤ ε)
    (hlarge : (Fintype.card U : ℚ) ^ 3 * a ≤ ε ^ 2 * D)
    (hdev : (∑ u, ((C u : ℚ) - (D : ℚ) / Fintype.card U) ^ 2) ≤
      (Fintype.card U : ℚ) * a * D) (u : U) :
    (1 - ε) * (D : ℚ) / Fintype.card U ≤ C u := by
  have h := count_lower_of_deviation_bound C D a ε hN hε hlarge hdev u
  apply (div_le_iff₀ (show (0 : ℚ) < Fintype.card U by exact_mod_cast hN)).mpr
  simpa only [mul_comm (C u : ℚ)] using h

section Packing

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq U]

/-- Taking the minimum actual fiber count incurs no additional rounding loss. -/
theorem exists_completeBlocks_of_count_lower (label : V → U) [Nonempty U] (ε : ℚ)
    (hlower : ∀ u, (1 - ε) * (Fintype.card V : ℚ) ≤
      (Fintype.card U : ℚ) * BlockPacking.count label u) :
    ∃ b, ∃ _P : BlockPacking.CompleteBlocks label b,
      (1 - ε) * (Fintype.card V : ℚ) ≤ (b : ℚ) * Fintype.card U := by
  classical
  obtain ⟨u, _, hu⟩ := Finset.exists_min_image (Finset.univ : Finset U)
    (BlockPacking.count label) Finset.univ_nonempty
  let P := BlockPacking.ofCountLE label (BlockPacking.count label u)
    (fun v => hu v (Finset.mem_univ v))
  refine ⟨BlockPacking.count label u, P, ?_⟩
  simpa only [mul_comm (BlockPacking.count label u : ℚ)] using hlower u

/-- The full parameterized packing implication in equation (3.10). -/
theorem exists_completeBlocks_of_deviation_bound (label : V → U) (a ε : ℚ)
    (hN : 0 < Fintype.card U) (hε : 0 ≤ ε)
    (hlarge : (Fintype.card U : ℚ) ^ 3 * a ≤ ε ^ 2 * Fintype.card V)
    (hdev : (∑ u, ((BlockPacking.count label u : ℚ) -
      (Fintype.card V : ℚ) / Fintype.card U) ^ 2) ≤
      (Fintype.card U : ℚ) * a * Fintype.card V) :
    ∃ b, ∃ _P : BlockPacking.CompleteBlocks label b,
      (1 - ε) * (Fintype.card V : ℚ) ≤ (b : ℚ) * Fintype.card U := by
  let _ : Nonempty U := Fintype.card_pos_iff.mp hN
  apply exists_completeBlocks_of_count_lower label ε
  exact count_lower_of_deviation_bound (BlockPacking.count label) (Fintype.card V)
    a ε hN hε hlarge hdev

/-- The same theorem using the manuscript's ceiling threshold literally. -/
theorem exists_completeBlocks_of_ceiling_threshold (label : V → U) (a ε : ℚ)
    (hN : 0 < Fintype.card U) (hε : 0 < ε)
    (hlarge : threshold (Fintype.card U) a ε ≤ Fintype.card V)
    (hdev : (∑ u, ((BlockPacking.count label u : ℚ) -
      (Fintype.card V : ℚ) / Fintype.card U) ^ 2) ≤
      (Fintype.card U : ℚ) * a * Fintype.card V) :
    ∃ b, ∃ _P : BlockPacking.CompleteBlocks label b,
      (1 - ε) * (Fintype.card V : ℚ) ≤ (b : ℚ) * Fintype.card U := by
  exact exists_completeBlocks_of_deviation_bound label a ε hN hε.le
    ((threshold_le_iff _ _ a ε hε).mp hlarge) hdev

end Packing

section PackedCardinality

variable {V U : Type*} [Fintype V] [Fintype U] {label : V → U} {b : ℕ}

/-- Packed coordinates occupy at most the entire coordinate set. -/
theorem packed_card_le (P : BlockPacking.CompleteBlocks label b) :
    b * Fintype.card U ≤ Fintype.card V := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    Fintype.card_le_of_embedding P.embed

omit [Fintype V] [Fintype U] in
/-- The support in the packed copies has exactly one copy per block. -/
theorem card_packedSupportFinset (P : BlockPacking.CompleteBlocks label b) (S : Finset U) :
    (DirectSums.packedSupportFinset P.embed S).card = b * S.card := by
  simp [DirectSums.packedSupportFinset]

/-- Equally sized color sides remain no larger than a `1/r` fraction of the input. -/
theorem packed_support_card_upper (P : BlockPacking.CompleteBlocks label b)
    (S : Finset U) (r : ℕ) (hside : r * S.card ≤ Fintype.card U) :
    r * (DirectSums.packedSupportFinset P.embed S).card ≤ Fintype.card V := by
  rw [card_packedSupportFinset]
  have hs := Nat.mul_le_mul_left b hside
  have hfit := packed_card_le P
  nlinarith

theorem packed_support_card_upper_fraction (P : BlockPacking.CompleteBlocks label b)
    (S : Finset U) (r : ℕ) (hr : 0 < r) (hside : r * S.card ≤ Fintype.card U) :
    ((DirectSums.packedSupportFinset P.embed S).card : ℚ) ≤
      (Fintype.card V : ℚ) / r := by
  apply (le_div_iff₀ (show (0 : ℚ) < r by exact_mod_cast hr)).mpr
  have h : (r : ℚ) * (DirectSums.packedSupportFinset P.embed S).card ≤
      Fintype.card V := by
    exact_mod_cast packed_support_card_upper P S r hside
  simpa only [mul_comm (r : ℚ)] using h

/-- At most an `ε` fraction of coordinates is left outside the complete blocks. -/
theorem leftovers_le [DecidableEq V] (P : BlockPacking.CompleteBlocks label b) (ε : ℚ)
    (hcover : (1 - ε) * (Fintype.card V : ℚ) ≤ (b : ℚ) * Fintype.card U) :
    (P.leftovers.card : ℚ) ≤ ε * Fintype.card V := by
  have hsum : (P.leftovers.card : ℚ) + (P.covered.card : ℚ) = Fintype.card V := by
    exact_mod_cast P.card_leftovers_add_covered
  rw [BlockPacking.CompleteBlocks.card_covered, Nat.cast_mul] at hsum
  nlinarith

end PackedCardinality

section ScalarDimensions

/-- Multiplying the loss in local dimension by the loss in block coverage. -/
theorem packed_color_lower (ε D N b r d : ℚ) (hb : 0 ≤ b) (hε : ε ≤ 1)
    (hcover : (1 - ε) * D ≤ b * N)
    (hlocal : (1 - ε) * N ≤ r * d) :
    (1 - ε) ^ 2 * D ≤ r * (b * d) := by
  have hc := mul_le_mul_of_nonneg_left hcover (sub_nonneg.mpr hε)
  have hl := mul_le_mul_of_nonneg_left hlocal hb
  nlinarith

theorem packed_color_upper (N b r d D : ℚ) (hb : 0 ≤ b)
    (hfit : b * N ≤ D) (hlocal : r * d ≤ N) :
    r * (b * d) ≤ D := by
  have hl := mul_le_mul_of_nonneg_left hlocal hb
  nlinarith

/-- Adding all color lower bounds cancels the number of colors. -/
theorem sum_color_lower {G : Type*} [Fintype G]
    (A : ℚ) (d : G → ℚ) (hG : 0 < Fintype.card G)
    (hlower : ∀ g, A ≤ (Fintype.card G : ℚ) * d g) :
    A ≤ ∑ g, d g := by
  have h := Finset.sum_le_sum (fun g (_ : g ∈ (Finset.univ : Finset G)) => hlower g)
  have hGq : (0 : ℚ) < Fintype.card G := by exact_mod_cast hG
  have hs : (Fintype.card G : ℚ) * A ≤
      (Fintype.card G : ℚ) * ∑ g, d g := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum] using h
  exact le_of_mul_le_mul_left hs hGq

end ScalarDimensions

section ActualDimensions

variable {K V U : Type*} [Field K] [Fintype V] [Fintype U]
variable {label : V → U} {b : ℕ}

/-- A subspace whose vectors vanish outside a finite coordinate set has at
most as many dimensions as that set has coordinates. -/
theorem finrank_le_card_support (W : Submodule K (U → K)) (S : Finset U)
    (hsupport : ∀ w ∈ W, ∀ u, u ∉ S → w u = 0) :
    finrank K W ≤ S.card := by
  classical
  let restrict : W →ₗ[K] (S → K) := {
    toFun := fun w u => w.val u.val
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  have hinj : Function.Injective restrict := by
    intro x y h
    apply Subtype.ext
    funext u
    by_cases hu : u ∈ S
    · exact congrFun h ⟨u, hu⟩
    · rw [hsupport x.val x.property u hu, hsupport y.val y.property u hu]
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_pi, Module.finrank_self, mul_one, Fintype.card_coe] using h

/-- Equation (3.11), with denominators cleared, for the actual packed subspace. -/
theorem packed_finrank_lower (P : BlockPacking.CompleteBlocks label b)
    (W : Submodule K (U → K)) (ε : ℚ) (r : ℕ) (hε : ε ≤ 1)
    (hcover : (1 - ε) * (Fintype.card V : ℚ) ≤ (b : ℚ) * Fintype.card U)
    (hlocal : (1 - ε) * (Fintype.card U : ℚ) ≤ (r : ℚ) * finrank K W) :
    (1 - ε) ^ 2 * (Fintype.card V : ℚ) ≤
      (r : ℚ) * finrank K (DirectSums.packedSubspace P.embed W) := by
  rw [DirectSums.finrank_packedSubspace, Fintype.card_fin, Nat.cast_mul]
  exact packed_color_lower ε (Fintype.card V) (Fintype.card U) b r (finrank K W)
    (by positivity) hε hcover hlocal

/-- The upper dimension bound follows from the local bound and injective packing. -/
theorem packed_finrank_upper (P : BlockPacking.CompleteBlocks label b)
    (W : Submodule K (U → K)) (r : ℕ)
    (hlocal : (r : ℚ) * finrank K W ≤ Fintype.card U) :
    (r : ℚ) * finrank K (DirectSums.packedSubspace P.embed W) ≤ Fintype.card V := by
  rw [DirectSums.finrank_packedSubspace, Fintype.card_fin, Nat.cast_mul]
  exact packed_color_upper (Fintype.card U) b r (finrank K W) (Fintype.card V)
    (by positivity) (by exact_mod_cast packed_card_le P) hlocal

/-- Derive the upper dimension bound directly from support containment and
the size of a local color side, without assuming the dimension bound. -/
theorem packed_finrank_upper_of_support (P : BlockPacking.CompleteBlocks label b)
    (W : Submodule K (U → K)) (S : Finset U) (r : ℕ)
    (hside : r * S.card ≤ Fintype.card U)
    (hsupport : ∀ w ∈ W, ∀ u, u ∉ S → w u = 0) :
    (r : ℚ) * finrank K (DirectSums.packedSubspace P.embed W) ≤ Fintype.card V := by
  apply packed_finrank_upper P W r
  have hdim := finrank_le_card_support W S hsupport
  have h : r * finrank K W ≤ Fintype.card U :=
    (Nat.mul_le_mul_left r hdim).trans hside
  exact_mod_cast h

/-- The displayed individual bound `d_g <= D/r`. -/
theorem packed_finrank_upper_fraction (P : BlockPacking.CompleteBlocks label b)
    (W : Submodule K (U → K)) (r : ℕ) (hr : 0 < r)
    (hlocal : (r : ℚ) * finrank K W ≤ Fintype.card U) :
    (finrank K (DirectSums.packedSubspace P.embed W) : ℚ) ≤
      (Fintype.card V : ℚ) / r := by
  apply (le_div_iff₀ (show (0 : ℚ) < r by exact_mod_cast hr)).mpr
  simpa only [mul_comm (finrank K (DirectSums.packedSubspace P.embed W) : ℚ)] using
    packed_finrank_upper P W r hlocal

/-- The displayed individual lower bound `(1-ε)^2 D/r <= d_g`. -/
theorem packed_finrank_lower_fraction (P : BlockPacking.CompleteBlocks label b)
    (W : Submodule K (U → K)) (ε : ℚ) (r : ℕ) (hr : 0 < r) (hε : ε ≤ 1)
    (hcover : (1 - ε) * (Fintype.card V : ℚ) ≤ (b : ℚ) * Fintype.card U)
    (hlocal : (1 - ε) * (Fintype.card U : ℚ) ≤ (r : ℚ) * finrank K W) :
    (1 - ε) ^ 2 * (Fintype.card V : ℚ) / r ≤
      finrank K (DirectSums.packedSubspace P.embed W) := by
  apply (div_le_iff₀ (show (0 : ℚ) < r by exact_mod_cast hr)).mpr
  simpa only [mul_comm (finrank K (DirectSums.packedSubspace P.embed W) : ℚ)] using
    packed_finrank_lower P W ε r hε hcover hlocal

/-- The total dimension bound used in the separated enumeration exponent. -/
theorem sum_packed_finrank_lower {G : Type*} [Fintype G]
    (P : BlockPacking.CompleteBlocks label b) (W : G → Submodule K (U → K))
    (ε : ℚ) (hG : 0 < Fintype.card G) (hε : ε ≤ 1)
    (hcover : (1 - ε) * (Fintype.card V : ℚ) ≤ (b : ℚ) * Fintype.card U)
    (hlocal : ∀ g, (1 - ε) * (Fintype.card U : ℚ) ≤
      (Fintype.card G : ℚ) * finrank K (W g)) :
    (1 - ε) ^ 2 * (Fintype.card V : ℚ) ≤
      ∑ g, (finrank K (DirectSums.packedSubspace P.embed (W g)) : ℚ) := by
  apply sum_color_lower _ _ hG
  intro g
  exact packed_finrank_lower P (W g) ε (Fintype.card G) hε hcover (hlocal g)

end ActualDimensions

end SubexponentialSAT.SubexpBlockPacking

end OAI.Algorithms
