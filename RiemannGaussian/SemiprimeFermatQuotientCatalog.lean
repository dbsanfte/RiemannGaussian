/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.NumberTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Public residue coverage for a small Fermat-quotient factor

The catalog depends only on `N,m`. A factor with Fermat quotient zero modulo
`m` has a Teichmuller residue modulo `m²`; reciprocating this public list also
covers the smaller factor when the other factor has that property. These are
arithmetic coverage and proper-leaf theorems, not a polynomial-evaluation bit
backend or a complete sixth-rate factoring theorem.
-/

namespace RiemannGaussian.SemiprimeFermatQuotientCatalog

/-- The publicly testable property on a supplied candidate integer. -/
def FermatQuotientZero (m p : ℕ) : Prop := p ^ (m - 1) ≡ 1 [MOD m ^ 2]

/-- Raising congruent integers to the modulus lifts congruence by one power. -/
theorem pow_modulus_lift {m : ℕ} {x y : ℤ} (h : x ≡ y [ZMOD m]) :
    x ^ m ≡ y ^ m [ZMOD m ^ 2] := by
  have hd : (m : ℤ) ∣ y - x := h.dvd
  have hs := dvd_geom_sum₂_self hd
  have hh := mul_dvd_mul hs hd
  rw [geom_sum₂_mul] at hh
  exact Int.modEq_of_dvd (by simpa only [Nat.cast_pow, pow_two] using hh)

/-- A zero Fermat quotient fixes the integer under the modulus power. -/
theorem pow_eq_self_mod_square {m p : ℕ} (hm : 0 < m)
    (hp : FermatQuotientZero m p) : p ^ m ≡ p [MOD m ^ 2] := by
  have h := hp.mul (Nat.ModEq.refl p)
  have he : m - 1 + 1 = m := Nat.sub_add_cancel hm
  simpa only [← pow_succ, he, one_mul] using h

/-- The Teichmuller lift is the explicit public power of the low residue. -/
theorem teichmuller_residue {m p : ℕ} (hm : 0 < m)
    (hp : FermatQuotientZero m p) : p ≡ (p % m) ^ m [MOD m ^ 2] := by
  have hbase : (p : ℤ) ≡ (p % m : ℕ) [ZMOD m] := by
    rw [Int.natCast_modEq_iff]
    exact (Nat.mod_modEq p m).symm
  have hlift := pow_modulus_lift hbase
  have hnat : p ^ m ≡ (p % m) ^ m [MOD m ^ 2] := by
    exact_mod_cast hlift
  exact (pow_eq_self_mod_square hm hp).symm.trans hnat

/-- At most `m-1` public Teichmuller candidates, with duplicates discarded. -/
def teichmullerResidues (m : ℕ) : Finset ℕ :=
  ((Finset.range m).filter (fun j => j ≠ 0)).image (fun j => j ^ m % (m ^ 2))

/-- Reciprocal completion is computed in the public ring modulo `m²`. -/
def reciprocalResidue (N m s : ℕ) : ℕ :=
  ((N : ZMod (m ^ 2)) * (s : ZMod (m ^ 2))⁻¹).val

/-- This complete residue catalog depends only on the supplied `N,m`. -/
def factorResidues (N m : ℕ) : Finset ℕ :=
  teichmullerResidues m ∪ (teichmullerResidues m).image (reciprocalResidue N m)

/-- The promised factor contributes its own low-square residue to the public list. -/
theorem residue_mem_teichmuller {m p : ℕ} (hm : 1 < m)
    (hcop : p.Coprime m) (hp : FermatQuotientZero m p) :
    p % (m ^ 2) ∈ teichmullerResidues m := by
  have hj : p % m ≠ 0 := by
    intro hz
    have hg : Nat.gcd (p % m) m = 1 := by
      rw [← Nat.gcd_rec]
      exact hcop.symm
    simp only [hz, Nat.gcd_zero_left] at hg
    omega
  apply Finset.mem_image.mpr
  refine ⟨p % m, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt p (by omega)), hj⟩, ?_⟩
  exact (teichmuller_residue (by omega) hp).symm

/-- A public reciprocal residue recovers the complementary factor residue. -/
theorem reciprocal_complement {m p q : ℕ} (hm : 0 < m) (hq : q.Coprime m) :
    reciprocalResidue (p * q) m (q % (m ^ 2)) = p % (m ^ 2) := by
  have : NeZero (m ^ 2) := ⟨pow_ne_zero 2 hm.ne'⟩
  have hu : IsUnit (q : ZMod (m ^ 2)) :=
    (ZMod.isUnit_iff_coprime q (m ^ 2)).mpr (hq.pow_right 2)
  unfold reciprocalResidue
  have hc : ((q % (m ^ 2) : ℕ) : ZMod (m ^ 2)) = (q : ZMod (m ^ 2)) := by simp
  rw [hc, Nat.cast_mul, mul_assoc, ZMod.mul_inv_of_unit _ hu, mul_one,
    ZMod.val_natCast]

/-- Either factor's zero Fermat quotient covers the first factor, without advice
in the catalog's construction. -/
theorem either_factor_residue_mem {m p q : ℕ} (hm : 1 < m)
    (hp : p.Coprime m) (hq : q.Coprime m)
    (hzero : FermatQuotientZero m p ∨ FermatQuotientZero m q) :
    p % (m ^ 2) ∈ factorResidues (p * q) m := by
  rcases hzero with h | h
  · exact Finset.mem_union_left _ (residue_mem_teichmuller hm hp h)
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨q % (m ^ 2), residue_mem_teichmuller hm hq h,
      reciprocal_complement (by omega) hq⟩

/-- The covered small factor has an index in the public interval `0,...,m`. -/
theorem public_index_coverage {m p q : ℕ} (hm : 1 < m)
    (hp : p.Coprime m) (hq : q.Coprime m) (hsize : p ≤ m ^ 3)
    (hzero : FermatQuotientZero m p ∨ FermatQuotientZero m q) :
    ∃ s ∈ factorResidues (p * q) m, ∃ k ≤ m, p = s + m ^ 2 * k := by
  refine ⟨p % (m ^ 2), either_factor_residue_mem hm hp hq hzero,
    p / (m ^ 2), ?_, (Nat.mod_add_div p (m ^ 2)).symm⟩
  apply Nat.div_le_of_le_mul
  nlinarith [hsize]

/-- The catalog is never larger than twice the raw tag range. -/
theorem factorResidues_card_le (N m : ℕ) : (factorResidues N m).card ≤ 2 * m := by
  calc
    (factorResidues N m).card ≤ (teichmullerResidues m).card +
        ((teichmullerResidues m).image (reciprocalResidue N m)).card :=
      Finset.card_union_le _ _
    _ ≤ 2 * (teichmullerResidues m).card := by
      have := Finset.card_image_le (s := teichmullerResidues m) (f := reciprocalResidue N m)
      omega
    _ ≤ 2 * m := by
      have hi := Finset.card_image_le
        (s := (Finset.range m).filter (fun j => j ≠ 0))
        (f := fun j => j ^ m % (m ^ 2))
      have hf := Finset.card_filter_le (s := Finset.range m) (p := fun j => j ≠ 0)
      simp only [Finset.card_range] at hf
      change 2 * (((Finset.range m).filter (fun j => j ≠ 0)).image
        (fun j => j ^ m % (m ^ 2))).card ≤ 2 * m
      omega

/-- Every listed residue is reduced modulo the public square. -/
theorem factorResidues_lt {N m s : ℕ} (hm : 0 < m)
    (hs : s ∈ factorResidues N m) : s < m ^ 2 := by
  have : NeZero (m ^ 2) := ⟨pow_ne_zero 2 hm.ne'⟩
  rcases Finset.mem_union.mp hs with hs | hs
  · rcases Finset.mem_image.mp hs with ⟨j, _, rfl⟩
    exact Nat.mod_lt _ (pow_pos hm _)
  · rcases Finset.mem_image.mp hs with ⟨j, _, rfl⟩
    exact ZMod.val_lt _

/-- The covered factor residue is nonzero, so a zero candidate may safely be skipped. -/
theorem factor_residue_pos {m p : ℕ} (hm : 1 < m) (hp : p.Coprime m) :
    0 < p % (m ^ 2) := by
  have hc := hp.pow_right 2
  have hg : Nat.gcd (p % (m ^ 2)) (m ^ 2) = 1 := by
    rw [← Nat.gcd_rec]
    exact hc.symm
  apply Nat.pos_of_ne_zero
  intro he
  simp only [he, Nat.gcd_zero_left] at hg
  nlinarith

/-- Every retained nonzero candidate lies below the explicit public cubic cap. -/
theorem candidate_bounds {m s k : ℕ} (hs : 0 < s)
    (hslt : s < m ^ 2) (hk : k ≤ m) :
    0 < s + m ^ 2 * k ∧ s + m ^ 2 * k < m ^ 3 + m ^ 2 := by
  constructor
  · omega
  · have hx := Nat.mul_le_mul_left (m ^ 2) hk
    nlinarith

/-- The strong-prefix product bound makes every such positive leaf smaller than N. -/
theorem candidate_lt_modulus {N m s k : ℕ} (hm : 1 < m) (hs : 0 < s)
    (hslt : s < m ^ 2) (hk : k ≤ m) (hN : (16 * m ^ 2) ^ 2 < N) :
    0 < s + m ^ 2 * k ∧ s + m ^ 2 * k < N := by
  obtain ⟨hpos, hcap⟩ := candidate_bounds hs hslt hk
  refine ⟨hpos, hcap.trans_le ?_⟩
  have hm2 : 2 ≤ m := hm
  have hsq : m ^ 2 ≤ m ^ 3 := by nlinarith [Nat.mul_le_mul_right (m ^ 2) (by omega : 1 ≤ m)]
  have hfour : m ^ 3 ≤ m ^ 4 := by nlinarith [Nat.mul_le_mul_left (m ^ 3) (by omega : 1 ≤ m)]
  nlinarith

/-- A nonunit gcd at a positive bounded leaf is automatically a proper factor. -/
theorem proper_gcd_of_bounded_leaf {N c : ℕ} (hc : 0 < c) (hcN : c < N)
    (hg : 1 < Nat.gcd c N) :
    1 < Nat.gcd c N ∧ Nat.gcd c N < N := by
  exact ⟨hg, (Nat.gcd_le_left N hc).trans_lt hcN⟩

/-- Publicly discard the zero residue; this cannot remove a coprime factor. -/
def positiveFactorResidues (N m : ℕ) : Finset ℕ :=
  (factorResidues N m).filter (fun s => 0 < s)

/-- The positive catalog keeps the same linear cardinality bound. -/
theorem positiveFactorResidues_card_le (N m : ℕ) :
    (positiveFactorResidues N m).card ≤ 2 * m :=
  (Finset.card_filter_le _ _).trans (factorResidues_card_le N m)

/-- Either hidden zero Fermat quotient has an actual bounded positive public leaf. -/
theorem positive_public_index_coverage {m p q : ℕ} (hm : 1 < m)
    (hp : p.Coprime m) (hq : q.Coprime m) (hsize : p ≤ m ^ 3)
    (hzero : FermatQuotientZero m p ∨ FermatQuotientZero m q) :
    ∃ s ∈ positiveFactorResidues (p * q) m, ∃ k ≤ m,
      p = s + m ^ 2 * k := by
  refine ⟨p % (m ^ 2), ?_, p / (m ^ 2), ?_, (Nat.mod_add_div p (m ^ 2)).symm⟩
  · exact Finset.mem_filter.mpr ⟨either_factor_residue_mem hm hp hq hzero,
      factor_residue_pos hm hp⟩
  · apply Nat.div_le_of_le_mul
    nlinarith [hsize]

/-- Every public positive leaf is strictly between zero and the modulus. -/
theorem all_public_leaves_bounded {N m s k : ℕ} (hm : 1 < m)
    (hs : s ∈ positiveFactorResidues N m) (hk : k ≤ m)
    (hN : (16 * m ^ 2) ^ 2 < N) :
    0 < s + m ^ 2 * k ∧ s + m ^ 2 * k < N := by
  obtain ⟨hmem, hpos⟩ := Finset.mem_filter.mp hs
  exact candidate_lt_modulus hm hpos (factorResidues_lt (by omega) hmem) hk hN

/-- A nonunit at any catalog leaf is already a proper factor, never a saturated leaf. -/
theorem public_leaf_proper_gcd {N m s k : ℕ} (hm : 1 < m)
    (hs : s ∈ positiveFactorResidues N m) (hk : k ≤ m)
    (hN : (16 * m ^ 2) ^ 2 < N) (hg : 1 < Nat.gcd (s + m ^ 2 * k) N) :
    1 < Nat.gcd (s + m ^ 2 * k) N ∧ Nat.gcd (s + m ^ 2 * k) N < N := by
  obtain ⟨hc, hcN⟩ := all_public_leaves_bounded hm hs hk hN
  exact proper_gcd_of_bounded_leaf hc hcN hg

/-- Sixth-root scale bounds the smaller factor by the public cube. -/
theorem smaller_factor_le_cube {m p q : ℕ} (hpq : p ≤ q)
    (hsize : p * q ≤ m ^ 6) : p ≤ m ^ 3 := by
  have hpp := Nat.mul_le_mul_left p hpq
  have he : m ^ 6 = (m ^ 3) ^ 2 := by ring
  rw [he] at hsize
  by_contra! h
  have hlt := Nat.mul_self_lt_mul_self h
  have hle : p * p ≤ m ^ 3 * m ^ 3 := by
    simpa only [pow_two] using hpp.trans hsize
  exact (not_lt_of_ge hle) hlt

/-- Complete public arithmetic coverage from the semiprime sixth-scale hypotheses. -/
theorem sixth_scale_public_index_coverage {m p q : ℕ} (hm : 1 < m)
    (hp : p.Coprime m) (hq : q.Coprime m) (hpq : p ≤ q)
    (hsize : p * q ≤ m ^ 6)
    (hzero : FermatQuotientZero m p ∨ FermatQuotientZero m q) :
    ∃ s ∈ positiveFactorResidues (p * q) m, ∃ k ≤ m,
      p = s + m ^ 2 * k :=
  positive_public_index_coverage hm hp hq (smaller_factor_le_cube hpq hsize) hzero

end RiemannGaussian.SemiprimeFermatQuotientCatalog
