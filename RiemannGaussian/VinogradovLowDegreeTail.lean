/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovPolynomialNonsingular

/-!
# Low-degree tail conditioning with its explicit residue cost

The first `d` tail equations retain the complete low-degree power sums
modulo the selected prime. Newton rigidity bounds every residue signature
fibre, including repeated entries. These are the low-degree constraints
needed before replacing a whole tail by one residue class.
-/

namespace RiemannGaussian.VinogradovLowDegreeTail
noncomputable section
open scoped BigOperators Classical
open Polynomial MeasureTheory UnitAddTorus VinogradovMeanValue VinogradovShiftedMoment
open VinogradovMomentPartition VinogradovPartitionEnergy VinogradovColourProducts
open VinogradovPolynomialNonsingular VinogradovDifferenceEnergy

/-- Use the original enumeration of the nonsingular block window. -/
local instance windowFintype (p m P : ℕ) : Fintype (Window p m P) := Fintype.ofFinite _

/-- The complete first-`d` power-sum signature of a tail residue tuple. -/
def lowSignature {p s : ℕ} (d : ℕ) (x : Fin s → ZMod p) : Fin d → ZMod p :=
  fun i => ∑ j, x j ^ (i.val + 1)

/-- Newton rigidity bounds every complete prime-field fibre by `d!`,
without deleting repeated residue entries. -/
theorem complete_fibre_le {p d : ℕ} [Fact p.Prime] (hdp : d < p)
    (a : Fin d → ZMod p) :
    (Finset.univ.filter (fun x : Fin d → ZMod p => lowSignature d x = a)).card ≤
      d.factorial := by
  let S := Finset.univ.filter (fun x : Fin d → ZMod p => lowSignature d x = a)
  by_cases hS : S.Nonempty
  · obtain ⟨v, hv⟩ := hS
    have hv' := (Finset.mem_filter.mp hv).2
    have hsub : S.image List.ofFn ⊆ (List.ofFn v).permutations.toFinset := by
      intro l hl
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl
      have hx' := (Finset.mem_filter.mp hx).2
      have he := VinogradovPrimePowerRigidity.prime_multiset_eq hdp x v
        (fun i => (congrFun hx' i).trans (congrFun hv' i).symm)
      rw [List.mem_toFinset, List.mem_permutations]
      simpa only [Fin.univ_val_map, Multiset.coe_eq_coe] using he
    calc
      S.card = (S.image List.ofFn).card :=
        (Finset.card_image_of_injective S List.ofFn_injective).symm
      _ ≤ (List.ofFn v).permutations.toFinset.card := Finset.card_le_card hsub
      _ ≤ (List.ofFn v).permutations.length := List.toFinset_card_le _
      _ = d.factorial := by rw [List.length_permutations, List.length_ofFn]
  · change S.card ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp

/-- Fixing the remaining tail entries pays exactly one free prime
residue per entry, while retaining all low-degree correlations. -/
theorem lowSignature_fibre_le {p d s : ℕ} [Fact p.Prime]
    (hdp : d < p) (hds : d ≤ s) (a : Fin d → ZMod p) :
    (Finset.univ.filter (fun x : Fin s → ZMod p => lowSignature d x = a)).card ≤
      p ^ (s - d) * d.factorial := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_add_of_le hds
  simp only [Nat.add_sub_cancel_left]
  let S := Finset.univ.filter (fun x : Fin (d + h) → ZMod p => lowSignature d x = a)
  let tail (x : Fin (d + h) → ZMod p) := fun j : Fin h => x (Fin.natAdd d j)
  have hf (b : Fin h → ZMod p) : (S.filter (fun x => tail x = b)).card ≤ d.factorial := by
    let target : Fin d → ZMod p := fun i => a i - ∑ j, b j ^ (i.val + 1)
    apply le_trans (Finset.card_le_card_of_injOn
      (fun x : Fin (d + h) → ZMod p => fun j : Fin d => x (Fin.castAdd h j)) ?_ ?_)
      (complete_fibre_le hdp target)
    · intro x hx
      obtain ⟨hx, htail⟩ := Finset.mem_filter.mp hx
      have hx' := (Finset.mem_filter.mp hx).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      funext i
      have he := congrFun hx' i
      change (∑ j, x j ^ (i.val + 1)) = a i at he
      rw [Fin.sum_univ_add] at he
      have hb : (fun j : Fin h => x (Fin.natAdd d j)) = b := htail
      change (∑ j : Fin d, x (Fin.castAdd h j) ^ (i.val + 1)) =
        a i - ∑ j, b j ^ (i.val + 1)
      rw [← hb]
      exact eq_sub_of_add_eq he
    · intro x hx y hy he
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      funext i
      refine Fin.addCases (fun j => congrFun he j) (fun j => ?_) i
      exact (congrFun hx' j).trans (congrFun hy' j).symm
  calc
    S.card = ∑ b : Fin h → ZMod p, (S.filter (fun x => tail x = b)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _b : Fin h → ZMod p, d.factorial :=
      Finset.sum_le_sum (fun b _ => hf b)
    _ = p ^ h * d.factorial := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, ZMod.card, nsmul_eq_mul, Nat.cast_id]

/-- The literal positive tail residue, without changing its endpoint. -/
def tailResidue {p Q : ℕ} (x : Fin Q) : ZMod p := ((x.val + 1 : ℕ) : ZMod p)

/-- The tail residue mask factors from the complete original block. -/
theorem tail_configuration_polynomial (p m d P Q q s : ℕ)
    (F : Fin m → ℤ[X]) (c : Fin s → ZMod p)
    (theta : UnitAddTorus (Fin d ⊕ Fin m)) :
    polynomial (configurationFrequency (p := p) (P := P) d s F (monomialTail m d 1 q Q))
      (targetWeight (fun z => tupleLabel s tailResidue z.2) (fun _ => 1) c) theta =
      polynomial (windowFrequency (p := p) (P := P) d F) (fun _ => 1) theta *
        polynomial (tupleFrequency s (monomialTail m d 1 q Q))
          (targetWeight (tupleLabel s tailResidue) (fun _ => 1) c) theta := by
  have hw : targetWeight
      (fun z : Window p m P × (Fin s → Fin Q) => tupleLabel s tailResidue z.2)
      (fun _ => (1 : ℂ)) c =
      fun z => (1 : ℂ) * targetWeight (tupleLabel s tailResidue) (fun _ => 1) c z.2 := by
    funext z
    simp only [targetWeight, one_mul]
  rw [hw]
  unfold configurationFrequency
  exact VinogradovProductEnergy.polynomial_prod _ _ (fun _ => 1) _ theta

/-- Every full collision preserves the low-degree tail signature.
The nonzero integer dilation is cancelled before reduction modulo `p`;
no coprimality between `p` and `q` is required. -/
theorem collision_lowSignature {p m d P Q q s : ℕ} (hq : 0 < q)
    (F : Fin m → ℤ[X]) (z z' : Window p m P × (Fin s → Fin Q))
    (he : configurationFrequency d s F (monomialTail m d 1 q Q) z =
      configurationFrequency d s F (monomialTail m d 1 q Q) z') :
    lowSignature d (tupleLabel s (tailResidue (p := p)) z.2) =
      lowSignature d (tupleLabel s (tailResidue (p := p)) z'.2) := by
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  funext i
  have hi := congrFun he (Sum.inl i)
  simp only [configurationFrequency, Pi.add_apply, windowFrequency,
    VinogradovPolynomialConditioning.blockFrequency,
    VinogradovPolynomialDifferencing.fullFrequency, Sum.elim_inl,
    Finset.sum_apply, Finset.sum_const_zero, zero_add, tupleFrequency,
    monomialTail, Nat.one_mul, mul_pow, ← Finset.mul_sum] at hi
  have hh := mul_left_cancel₀ (pow_ne_zero (i.val + 1) hqz) hi
  have hc := congrArg (Int.castRingHom (ZMod p)) hh
  simpa only [lowSignature, tupleLabel, tailResidue, map_sum, map_pow,
    Int.coe_castRingHom, Int.cast_add, Int.cast_natCast, Int.cast_one,
    Nat.cast_add, Nat.cast_one] using hc

/-- The normalized Haar measure used by the original count. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- Circle Haar measure has mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Low-degree correlations control the actual original nonsingular
count by its tail residue energy, with the explicit Newton fibre cost. -/
theorem count_le_tail_energy {p m d s : ℕ} [Fact p.Prime]
    (hdp : d < p) (hds : d ≤ s) (P Q q : ℕ) (hq : 0 < q) (F : Fin m → ℤ[X]) :
    (nonsingularCount p m d P s F (monomialTail m d 1 q Q) : ℝ) ≤
      ((p ^ (s - d) * d.factorial : ℕ) : ℝ) *
        ∫ theta : UnitAddTorus (Fin d ⊕ Fin m),
          ‖polynomial (windowFrequency (p := p) (P := P) d F) (fun _ => 1) theta‖ ^ 2 *
            colourEnergy (tailResidue (p := p))
              (fun x => mFourier (monomialTail m d 1 q Q x) theta) ^ s := by
  let V := configurationFrequency (p := p) (P := P) d s F (monomialTail m d 1 q Q)
  let label := fun z : Window p m P × (Fin s → Fin Q) =>
    tupleLabel s (tailResidue (p := p)) z.2
  have he := whole_integral_le V (fun _ => 1) label (lowSignature d)
    (((p ^ (s - d) * d.factorial : ℕ) : ℝ))
    (fun z z' hz => collision_lowSignature hq F z z' hz) (by
      intro a
      have hc : ((Finset.univ.filter (fun x : Fin s → ZMod p => lowSignature d x = a)).card : ℝ) ≤
          ((p ^ (s - d) * d.factorial : ℕ) : ℝ) := by
        exact_mod_cast lowSignature_fibre_le hdp hds a
      convert hc using 1
      congr 2
      ext c
      simp)
  have hnorm : (∫ theta : UnitAddTorus (Fin d ⊕ Fin m),
      ‖polynomial V (fun _ => 1) theta‖ ^ 2) =
      (nonsingularCount p m d P s F (monomialTail m d 1 q Q) : ℝ) := by
    rw [← nonsingularMoment_eq_count]
    apply integral_congr_ae
    filter_upwards [] with theta
    simp only [V, VinogradovPolynomialNonsingular.configuration_polynomial, norm_mul, norm_pow, mul_pow,
      ← pow_mul, Nat.mul_comm s 2]
  rw [hnorm] at he
  apply he.trans_eq
  congr 1
  have hi (c : Fin s → ZMod p) : Integrable (fun theta : UnitAddTorus (Fin d ⊕ Fin m) =>
      ‖polynomial V (targetWeight label (fun _ => 1) c) theta‖ ^ 2) :=
    ((continuous_polynomial V (targetWeight label (fun _ => 1) c)).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ theta : UnitAddTorus (Fin d ⊕ Fin m),
        ∑ c : Fin s → ZMod p, ‖polynomial V (targetWeight label (fun _ => 1) c) theta‖ ^ 2 :=
      (integral_finsetSum _ (fun c _ => hi c)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with theta
      simp only [V, label, tail_configuration_polynomial, norm_mul, mul_pow,
        ← Finset.mul_sum, tuple_colour_energy]

/-- The actual original block coupled to one fixed tail residue class. -/
def tailClassMoment (p m d P Q q s : ℕ) (F : Fin m → ℤ[X]) (c : ZMod p) : ℝ :=
  ∫ theta : UnitAddTorus (Fin d ⊕ Fin m),
    ‖polynomial (windowFrequency (p := p) (P := P) d F) (fun _ => 1) theta‖ ^ 2 *
      ‖polynomial (monomialTail m d 1 q Q)
        (targetWeight tailResidue (fun _ => 1) c) theta‖ ^ (2 * s)

/-- Finite Holder pays the tail residue energy before integration.
The complete sum of the individual class moments is retained. -/
theorem tail_energy_le_sum {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (m d P Q q : ℕ) (F : Fin m → ℤ[X]) :
    (∫ theta : UnitAddTorus (Fin d ⊕ Fin m),
      ‖polynomial (windowFrequency (p := p) (P := P) d F) (fun _ => 1) theta‖ ^ 2 *
        colourEnergy (tailResidue (p := p))
          (fun x => mFourier (monomialTail m d 1 q Q x) theta) ^ s) ≤
      (p : ℝ) ^ (s - 1) * ∑ c : ZMod p, tailClassMoment p m d P Q q s F c := by
  let B (theta : UnitAddTorus (Fin d ⊕ Fin m)) :=
    ‖polynomial (windowFrequency (p := p) (P := P) d F) (fun _ => 1) theta‖ ^ 2
  let g (c : ZMod p) (theta : UnitAddTorus (Fin d ⊕ Fin m)) :=
    ‖polynomial (monomialTail m d 1 q Q) (targetWeight tailResidue (fun _ => 1) c) theta‖ ^ 2
  have hB : Continuous B := (continuous_polynomial _ _).norm.pow 2
  have hg (c : ZMod p) : Continuous (g c) := (continuous_polynomial _ _).norm.pow 2
  have hE (theta : UnitAddTorus (Fin d ⊕ Fin m)) :
      colourEnergy (tailResidue (p := p)) (fun x => mFourier (monomialTail m d 1 q Q x) theta) =
        ∑ c : ZMod p, g c theta := by
    simp only [g, colourEnergy, polynomial, targetWeight, ite_mul, one_mul, zero_mul]
  have hi (c : ZMod p) : Integrable (fun theta => B theta * g c theta ^ s) :=
    (hB.mul ((hg c).pow s)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpoint (theta : UnitAddTorus (Fin d ⊕ Fin m)) :
      B theta * (∑ c : ZMod p, g c theta) ^ s ≤
        (p : ℝ) ^ (s - 1) * ∑ c : ZMod p, B theta * g c theta ^ s := by
    have hp := VinogradovMomentReduction.weighted_power_bound Finset.univ
      (fun _ : ZMod p => (1 : ℝ)) (fun c => g c theta)
      (by simp) (fun c _ => by dsimp [g]; positivity) hs
    simp only [one_mul, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, mul_one] at hp
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ B theta by dsimp [B]; positivity)
    simpa only [Finset.mul_sum, mul_left_comm] using hh
  simp_rw [hE]
  calc
    _ ≤ ∫ theta : UnitAddTorus (Fin d ⊕ Fin m),
        (p : ℝ) ^ (s - 1) * ∑ c : ZMod p, B theta * g c theta ^ s :=
      integral_mono
        ((hB.mul ((continuous_finsetSum _ (fun c _ => hg c)).pow s)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
        ((integrable_finsetSum _ (fun c _ => hi c)).const_mul _) hpoint
    _ = (p : ℝ) ^ (s - 1) * ∑ c : ZMod p, tailClassMoment p m d P Q q s F c := by
      rw [integral_const_mul, integral_finsetSum _ (fun c _ => hi c)]
      simp only [B, g, pow_mul, tailClassMoment]

/-- One fixed residue class controls the actual original nonsingular
count with Ford's explicit `d! * p^(2s-d)` cost. The class is selected
after integration, and all original endpoints and equations are retained. -/
theorem exists_tail_class_bound {p d s : ℕ} [Fact p.Prime]
    (hdp : d < p) (hds : d ≤ s) (hs : 1 ≤ s)
    (m P Q q : ℕ) (hq : 0 < q) (F : Fin m → ℤ[X]) :
    ∃ c : ZMod p,
      (nonsingularCount p m d P s F (monomialTail m d 1 q Q) : ℝ) ≤
        ((d.factorial * p ^ (2 * s - d) : ℕ) : ℝ) * tailClassMoment p m d P Q q s F c := by
  obtain ⟨c, _, hc⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod p))
    (tailClassMoment p m d P Q q s F) Finset.univ_nonempty
  refine ⟨c, ?_⟩
  have hsum : (∑ a : ZMod p, tailClassMoment p m d P Q q s F a) ≤
      (p : ℝ) * tailClassMoment p m d P Q q s F c := by
    simpa using Finset.sum_le_sum (fun a ha => hc a ha)
  have he := (count_le_tail_energy hdp hds P Q q hq F).trans
    (mul_le_mul_of_nonneg_left (tail_energy_le_sum hs m d P Q q F) (Nat.cast_nonneg _))
  have he' := he.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hsum (by positivity)) (Nat.cast_nonneg _))
  have hexp : s - d + (s - 1) + 1 = 2 * s - d := by omega
  have hcoef : ((p ^ (s - d) * d.factorial : ℕ) : ℝ) * (p : ℝ) ^ (s - 1) * p =
      ((d.factorial * p ^ (2 * s - d) : ℕ) : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_pow]
    calc
      _ = (d.factorial : ℝ) * ((p : ℝ) ^ (s - d) * p ^ (s - 1) * p ^ 1) := by ring
      _ = _ := by rw [← pow_add, ← pow_add, hexp]
  simpa only [← mul_assoc, hcoef] using he'

end
end RiemannGaussian.VinogradovLowDegreeTail
