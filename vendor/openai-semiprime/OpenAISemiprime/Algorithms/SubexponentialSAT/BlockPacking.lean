import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Packing complete type blocks

The squared-deviation bound and the threshold from Section 5.4 imply a lower
bound for every type count. Enumerating the finite fibers then constructs
pairwise disjoint complete blocks. The construction from supplied enumerations
is explicit; no running-time theorem is asserted here.
-/

namespace SubexponentialSAT.BlockPacking

open scoped BigOperators

/-- Scalar form of the imbalance estimate, with denominators cleared in the conclusion. -/
theorem three_quarters_of_square_bound (N D a c : ℚ)
    (hN : 0 < N) (hD : 0 ≤ D)
    (hlarge : 16 * N ^ 3 * a ≤ D)
    (hsquare : (c - D / N) ^ 2 ≤ N * a * D) :
    3 * D ≤ 4 * N * c := by
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hscaled : (4 * (N * c - D)) ^ 2 ≤ D ^ 2 := by
    calc
      (4 * (N * c - D)) ^ 2 = 16 * N ^ 2 * (c - D / N) ^ 2 := by
        field_simp
        ring
      _ ≤ 16 * N ^ 2 * (N * a * D) :=
        mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ = (16 * N ^ 3 * a) * D := by ring
      _ ≤ D * D := mul_le_mul_of_nonneg_right hlarge hD
      _ = D ^ 2 := by ring
  have habs : |4 * (N * c - D)| ≤ D := by
    simpa only [abs_of_nonneg hD] using (sq_le_sq.mp hscaled)
  have hlower := (abs_le.mp habs).1
  linarith

/-- The manuscript's threshold bounds every count, for any finite type space. -/
theorem count_lower_of_deviation_bound {τ : Type*} [Fintype τ]
    (C : τ → ℕ) (D : ℕ) (a : ℚ)
    (hN : 0 < Fintype.card τ)
    (hlarge : 16 * (Fintype.card τ : ℚ) ^ 3 * a ≤ D)
    (hdev : (∑ u, ((C u : ℚ) - (D : ℚ) / Fintype.card τ) ^ 2) ≤
      (Fintype.card τ : ℚ) * a * D) (u : τ) :
    3 * D ≤ 4 * (Fintype.card τ) * C u := by
  have hone : ((C u : ℚ) - (D : ℚ) / Fintype.card τ) ^ 2 ≤
      ∑ v, ((C v : ℚ) - (D : ℚ) / Fintype.card τ) ^ 2 :=
    Finset.single_le_sum
      (fun v _ => sq_nonneg ((C v : ℚ) - (D : ℚ) / Fintype.card τ))
      (Finset.mem_univ u)
  have h := three_quarters_of_square_bound (Fintype.card τ) D a (C u)
    (by exact_mod_cast hN) (by positivity) hlarge (hone.trans hdev)
  exact_mod_cast h

/-- The same lower bound in the fractional form used in Section 5.4. -/
theorem count_fraction_lower_of_deviation_bound {τ : Type*} [Fintype τ]
    (C : τ → ℕ) (D : ℕ) (a : ℚ)
    (hN : 0 < Fintype.card τ)
    (hlarge : 16 * (Fintype.card τ : ℚ) ^ 3 * a ≤ D)
    (hdev : (∑ u, ((C u : ℚ) - (D : ℚ) / Fintype.card τ) ^ 2) ≤
      (Fintype.card τ : ℚ) * a * D) (u : τ) :
    (3 * (D : ℚ)) / (4 * (Fintype.card τ : ℚ)) ≤ C u := by
  have h := count_lower_of_deviation_bound C D a hN hlarge hdev u
  have hq : 3 * (D : ℚ) ≤ 4 * (Fintype.card τ : ℚ) * (C u : ℚ) := by
    exact_mod_cast h
  have hpos : 0 < 4 * (Fintype.card τ : ℚ) := by positivity
  apply (div_le_iff₀ hpos).mpr
  nlinarith

/-- A collection of complete blocks is an injective placement of block/type pairs,
preserving the assigned type. This also allows factors to cross block boundaries. -/
structure CompleteBlocks {α τ : Type*} (label : α → τ) (b : ℕ) where
  embed : Fin b × τ ↪ α
  type_eq : ∀ (i : Fin b) (u : τ), label (embed (i, u)) = u

section FiniteFibers

variable {α τ : Type*} [Fintype α] [Fintype τ] [DecidableEq τ]

/-- The actual number of coordinates of a given type. -/
def count (label : α → τ) (u : τ) : ℕ :=
  Fintype.card {v : α // label v = u}

omit [Fintype τ] in
/-- Compatibility with type counts expressed by filtering the coordinates. -/
theorem count_eq_filter_card (label : α → τ) (u : τ) :
    count label u = (Finset.univ.filter fun v => label v = u).card := by
  exact Fintype.card_subtype (fun v => label v = u)

/-- Use the first `b` entries of each fiber enumeration. -/
def ofEnumerations (label : α → τ) (b : ℕ)
    (enumerate : ∀ u, Fin (count label u) ≃ {v : α // label v = u})
    (hb : ∀ u, b ≤ count label u) : CompleteBlocks label b where
  embed := {
    toFun := fun z => (enumerate z.2 (Fin.castLE (hb z.2) z.1)).val
    inj' := by
      rintro ⟨i, u⟩ ⟨j, v⟩ h
      have huv : u = v := by
        calc
          u = label (enumerate u (Fin.castLE (hb u) i)).val :=
            (enumerate u (Fin.castLE (hb u) i)).property.symm
          _ = label (enumerate v (Fin.castLE (hb v) j)).val := congrArg label h
          _ = v := (enumerate v (Fin.castLE (hb v) j)).property
      subst v
      have heq : enumerate u (Fin.castLE (hb u) i) =
          enumerate u (Fin.castLE (hb u) j) := Subtype.ext h
      have hij : i = j := Fin.castLE_injective (hb u) ((enumerate u).injective heq)
      exact Prod.ext hij rfl }
  type_eq := fun i u => (enumerate u (Fin.castLE (hb u) i)).property

/-- Finite fiber equivalences supply the enumerations for abstract finite types. -/
noncomputable def ofCountLE (label : α → τ) (b : ℕ)
    (hb : ∀ u, b ≤ count label u) : CompleteBlocks label b :=
  ofEnumerations label b (fun u => (Fintype.equivFin {v : α // label v = u}).symm) hb

end FiniteFibers

namespace CompleteBlocks

variable {α τ : Type*} {label : α → τ} {b : ℕ}

/-- Embedding of the type universe into an individual complete block. -/
def blockEmbedding (P : CompleteBlocks label b) (i : Fin b) : τ ↪ α where
  toFun := fun u => P.embed (i, u)
  inj' := fun _ _ h => congrArg Prod.snd (P.embed.injective h)

variable [Fintype τ]

/-- The coordinates of one block, as a finite set. -/
def block (P : CompleteBlocks label b) (i : Fin b) : Finset α :=
  Finset.univ.map (P.blockEmbedding i)

/-- All packed coordinates; coordinates outside this set are the leftovers. -/
def covered (P : CompleteBlocks label b) : Finset α :=
  Finset.univ.map P.embed

@[simp] theorem card_block (P : CompleteBlocks label b) (i : Fin b) :
    (P.block i).card = Fintype.card τ := by
  simp [block]

@[simp] theorem card_covered (P : CompleteBlocks label b) :
    P.covered.card = b * Fintype.card τ := by
  simp [covered, Fintype.card_prod]

/-- Distinct blocks have no coordinate in common. -/
theorem disjoint_blocks (P : CompleteBlocks label b) {i j : Fin b} (hij : i ≠ j) :
    Disjoint (P.block i) (P.block j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rcases Finset.mem_map.mp hx with ⟨u, _, hu⟩
  rcases Finset.mem_map.mp hy with ⟨v, _, hv⟩
  exact hij (congrArg Prod.fst (P.embed.injective (hu.trans hv.symm)))

/-- Every type occurs exactly once in every block. -/
theorem unique_type_in_block (P : CompleteBlocks label b) (i : Fin b) (u : τ) :
    ∃! x : α, x ∈ P.block i ∧ label x = u := by
  refine ⟨P.embed (i, u), ?_, ?_⟩
  · exact ⟨Finset.mem_map.mpr ⟨u, Finset.mem_univ u, rfl⟩, P.type_eq i u⟩
  · intro x hx
    rcases Finset.mem_map.mp hx.1 with ⟨v, _, hv⟩
    have hvu : v = u := by
      calc
        v = label (P.embed (i, v)) := (P.type_eq i v).symm
        _ = label x := congrArg label hv
        _ = u := hx.2
    rw [← hvu]
    exact hv.symm

variable [Fintype α] [DecidableEq α]

/-- Coordinates not assigned to any complete block. -/
def leftovers (P : CompleteBlocks label b) : Finset α :=
  Finset.univ \ P.covered

theorem card_leftovers_add_covered (P : CompleteBlocks label b) :
    P.leftovers.card + P.covered.card = Fintype.card α := by
  simpa only [leftovers, Finset.card_univ] using
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ P.covered)

/-- The uncovered coordinates occupy at most one quarter of the input. -/
theorem leftovers_le_quarter (P : CompleteBlocks label b)
    (hcover : 3 * Fintype.card α ≤ 4 * P.covered.card) :
    4 * P.leftovers.card ≤ Fintype.card α := by
  have hsum := P.card_leftovers_add_covered
  omega

end CompleteBlocks

section PackingTheorem

variable {α τ : Type*} [Fintype α] [Fintype τ] [DecidableEq τ]

/-- Pack as many blocks as the least populated fiber permits. The integer
minimum is used directly, so the coverage estimate loses no extra block. -/
theorem exists_completeBlocks_of_count_lower (label : α → τ) [Nonempty τ]
    (hlower : ∀ u, 3 * Fintype.card α ≤ 4 * Fintype.card τ * count label u) :
    ∃ b, ∃ P : CompleteBlocks label b,
      3 * Fintype.card α ≤ 4 * P.covered.card := by
  classical
  obtain ⟨u, _, hu⟩ :=
    Finset.exists_min_image (Finset.univ : Finset τ) (count label) Finset.univ_nonempty
  let P := ofCountLE label (count label u) (fun v => hu v (Finset.mem_univ v))
  refine ⟨count label u, P, ?_⟩
  simpa only [CompleteBlocks.card_covered, Nat.mul_comm (count label u),
    Nat.mul_assoc] using hlower u

/-- Section 5.4: squared deviations and `D >= 16 N^3 a` yield complete blocks
covering at least three quarters of the coordinate set. -/
theorem exists_completeBlocks_of_deviation_bound (label : α → τ) (a : ℚ)
    (hN : 0 < Fintype.card τ)
    (hlarge : 16 * (Fintype.card τ : ℚ) ^ 3 * a ≤ Fintype.card α)
    (hdev : (∑ u, ((count label u : ℚ) -
      (Fintype.card α : ℚ) / Fintype.card τ) ^ 2) ≤
      (Fintype.card τ : ℚ) * a * Fintype.card α) :
    ∃ b, ∃ P : CompleteBlocks label b,
      3 * Fintype.card α ≤ 4 * P.covered.card := by
  let _ : Nonempty τ := Fintype.card_pos_iff.mp hN
  apply exists_completeBlocks_of_count_lower label
  exact count_lower_of_deviation_bound (count label) (Fintype.card α) a hN hlarge hdev

/-- Natural-number threshold specialization. Take `a = 1 + Delta * k` to
recover exactly the threshold `D*` in equation (5.9). -/
theorem exists_completeBlocks_of_nat_threshold (label : α → τ) (a : ℕ)
    (hN : 0 < Fintype.card τ)
    (hlarge : 16 * (Fintype.card τ) ^ 3 * a ≤ Fintype.card α)
    (hdev : (∑ u, ((count label u : ℚ) -
      (Fintype.card α : ℚ) / Fintype.card τ) ^ 2) ≤
      (Fintype.card τ : ℚ) * a * Fintype.card α) :
    ∃ b, ∃ P : CompleteBlocks label b,
      3 * Fintype.card α ≤ 4 * P.covered.card := by
  apply exists_completeBlocks_of_deviation_bound label (a : ℚ) hN
  · exact_mod_cast hlarge
  · exact hdev

end PackingTheorem

end SubexponentialSAT.BlockPacking

end OAI.Algorithms
