/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovMixedRepeated

/-!
# Absorbing repeated blocks in the actual mixed count

Count repetitions on both original blocks using unordered position pairs.
Compression and permutation preserve every tail equation. The repeated
integral is paid by maximality under doubling and the actual diagonal
reserve, not by scaling the fixed tail.
-/

namespace RiemannGaussian.VinogradovMixedExceptional
noncomputable section
open scoped BigOperators Classical ComplexConjugate
open MeasureTheory UnitAddTorus VinogradovMeanValue VinogradovShiftedMoment
open VinogradovPartitionEnergy VinogradovProductEnergy VinogradovCrossMoment
open VinogradovMixedMoments VinogradovMixedRepeated VinogradovRepeatedSolutions
open VinogradovRepeatedSolutions.Pairs

/-- The original normalized Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle has probability mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- All original mixed collisions, with both complete frequency vectors retained. -/
def fullCount {ι κ d : Type*} [Fintype ι] [Fintype κ]
    (m s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) : ℕ :=
  crossCount (configurationFrequency m s v u) (configurationFrequency m s v u)

/-- Both polynomial blocks are physically distinct; the tail remains unrestricted. -/
def distinctCount {ι κ d : Type*} [Fintype ι] [Fintype κ]
    (m s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) : ℕ :=
  (Finset.univ.filter (fun xy : ((Fin m → ι) × (Fin s → κ)) ×
      ((Fin m → ι) × (Fin s → κ)) =>
    (Function.Injective xy.1.1 ∧ Function.Injective xy.2.1) ∧
      configurationFrequency m s v u xy.1 = configurationFrequency m s v u xy.2)).card

/-- The complementary collisions with a repetition in either block. -/
def exceptionalCount {ι κ d : Type*} [Fintype ι] [Fintype κ]
    (m s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) : ℕ :=
  (Finset.univ.filter (fun xy : ((Fin m → ι) × (Fin s → κ)) ×
      ((Fin m → ι) × (Fin s → κ)) =>
    ¬(Function.Injective xy.1.1 ∧ Function.Injective xy.2.1) ∧
      configurationFrequency m s v u xy.1 = configurationFrequency m s v u xy.2)).card

/-- The literal mixed integral counts exactly these complete collisions. -/
theorem fullCount_eq_mixedMoment {ι κ d : Type*}
    [Fintype ι] [Fintype κ] [Fintype d]
    (m s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) :
    (fullCount m s v u : ℝ) = mixedMoment m s v u := by
  rw [mixedMoment_eq_count]
  unfold fullCount crossCount differenceCount
  congr 2
  ext xy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, add_zero]

/-- Distinct and repeated pairs partition the original count exactly. -/
theorem distinct_add_exceptional {ι κ d : Type*} [Fintype ι] [Fintype κ]
    (m s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) :
    distinctCount m s v u + exceptionalCount m s v u = fullCount m s v u := by
  unfold distinctCount exceptionalCount fullCount crossCount
  rw [← Finset.card_union_of_disjoint (by
    apply Finset.disjoint_left.mpr
    intro xy hx hy
    exact (Finset.mem_filter.mp hy).2.1 (Finset.mem_filter.mp hx).2.1)]
  congr 1
  ext xy
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- An original solution with a prescribed repeated pair in the left block. -/
def pairCount {ι κ d : Type*} [Fintype ι] [Fintype κ]
    (r s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) (a b : Fin (r + 2)) : ℕ :=
  (Finset.univ.filter (fun xy : ((Fin (r + 2) → ι) × (Fin s → κ)) ×
      ((Fin (r + 2) → ι) × (Fin s → κ)) =>
    xy.1.1 a = xy.1.1 b ∧
      configurationFrequency (r + 2) s v u xy.1 =
        configurationFrequency (r + 2) s v u xy.2)).card

/-- Compress the repeated entry without changing any tail frequency. -/
def repeatedConfiguration {ι κ d : Type*} (r s : ℕ)
    (v : ι → d → ℤ) (u : κ → d → ℤ)
    (x : (ι × (Fin r → ι)) × (Fin s → κ)) : d → ℤ :=
  repeatedFrequency r v x.1 + tupleFrequency s u x.2

/-- The compressed polynomial retains its doubled atom and entire original tail. -/
theorem repeated_configuration_polynomial {ι κ d : Type*}
    [Fintype ι] [Fintype κ] [Fintype d] (r s : ℕ)
    (v : ι → d → ℤ) (u : κ → d → ℤ) (t : UnitAddTorus d) :
    polynomial (repeatedConfiguration r s v u) (fun _ => 1) t =
      polynomial (fun i j => 2 * v i j) (fun _ => 1) t *
        polynomial v (fun _ => 1) t ^ r * polynomial u (fun _ => 1) t ^ s := by
  unfold repeatedConfiguration
  simpa only [one_mul, repeated_polynomial, tuple_polynomial_one] using
    polynomial_prod (repeatedFrequency r v) (tupleFrequency s u)
      (fun _ => 1) (fun _ => 1) t

/-- Compression injects actual first-pair collisions into the complete mixed cross count. -/
theorem first_pair_le_crossCount {ι κ d : Type*} [Fintype ι] [Fintype κ]
    (r s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) :
    pairCount r s v u 0 1 ≤
      crossCount (repeatedConfiguration r s v u) (configurationFrequency (r + 2) s v u) := by
  unfold pairCount crossCount
  apply Finset.card_le_card_of_injOn
    (fun xy => (((xy.1.1 0, fun j => xy.1.1 j.succ.succ), xy.1.2), xy.2))
  · intro xy hxy
    have hx := (Finset.mem_filter.mp hxy).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa only [configurationFrequency, repeatedConfiguration,
      tupleFrequency_eq_repeated r v xy.1.1 hx.1] using hx.2
  · intro xy hxy zw hzw he
    have hx := (Finset.mem_filter.mp hxy).2.1
    have hz := (Finset.mem_filter.mp hzw).2.1
    have hh := congrArg (fun z => z.1.1.1) he
    have ht := congrArg (fun z => z.1.1.2) he
    have hu := congrArg (fun z => z.1.2) he
    have hr := congrArg Prod.snd he
    dsimp only at hh ht hu hr
    refine Prod.ext (Prod.ext ?_ hu) hr
    funext i
    refine Fin.cases hh (fun j => ?_) i
    refine Fin.cases ?_ (fun l => congrFun ht l) j
    exact hx.symm.trans (hh.trans hz)

/-- Moving only block positions preserves the entire mixed frequency. -/
theorem configuration_comp_perm {ι κ d : Type*} (m s : ℕ)
    (v : ι → d → ℤ) (u : κ → d → ℤ)
    (x : (Fin m → ι) × (Fin s → κ)) (e : Equiv.Perm (Fin m)) :
    configurationFrequency m s v u (x.1 ∘ e, x.2) = configurationFrequency m s v u x := by
  simp only [configurationFrequency, tupleFrequency_comp_perm]

/-- Every prescribed distinct pair is bounded by the first-pair class. -/
theorem pair_le_first {ι κ d : Type*} [Fintype ι] [Fintype κ]
    (r s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ)
    (a b : Fin (r + 2)) (hab : a ≠ b) : pairCount r s v u a b ≤ pairCount r s v u 0 1 := by
  obtain ⟨e, he0, he1⟩ := exists_pair_permutation (0 : Fin (r + 2)) 1 a b
    (by exact Fin.zero_ne_one) hab
  unfold pairCount
  apply Finset.card_le_card_of_injOn (fun xy => ((xy.1.1 ∘ e, xy.1.2), xy.2))
  · intro xy hxy
    have hx := (Finset.mem_filter.mp hxy).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa only [Function.comp_apply, he0, he1] using hx.1
    · simpa only [configuration_comp_perm] using hx.2
  · intro xy hxy zw hzw he
    have hr := congrArg (fun z : ((Fin (r + 2) → ι) × (Fin s → κ)) ×
      ((Fin (r + 2) → ι) × (Fin s → κ)) => z.2) he
    refine Prod.ext (Prod.ext ?_ (congrArg (fun z => z.1.2) he)) hr
    have h := congrArg (fun z => z.1.1) he
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    exact congrFun h i

/-- Fourier orthogonality places the repeated actual solutions under the
fixed-tail integral before Holder or maximality is used. -/
theorem first_pair_le_integral {ι κ d : Type*}
    [Fintype ι] [Fintype κ] [Fintype d]
    (r s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) :
    (pairCount r s v u 0 1 : ℝ) ≤
      ∫ t : UnitAddTorus d,
        ‖polynomial v (fun _ => 1) t‖ ^ (2 * (r + 2) - 2) *
          ‖polynomial (fun i j => 2 * v i j) (fun _ => 1) t‖ *
            ‖polynomial u (fun _ => 1) t‖ ^ (2 * s) := by
  have hcount : (pairCount r s v u 0 1 : ℝ) ≤
      crossCount (repeatedConfiguration r s v u) (configurationFrequency (r + 2) s v u) := by
    exact_mod_cast first_pair_le_crossCount r s v u
  apply hcount.trans
  have he := congrArg norm (crossGram_one (repeatedConfiguration r s v u)
    (configurationFrequency (r + 2) s v u))
  rw [Complex.norm_natCast] at he
  rw [← he, crossGram_eq_integral]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [] with t
  have hfull := configuration_polynomial (r + 2) s v u (fun _ => 1) (fun _ => 1) t
  simp only [tupleWeight, Finset.prod_const_one, one_mul] at hfull
  rw [norm_mul, Complex.norm_conj, repeated_configuration_polynomial, hfull]
  simp only [norm_mul, norm_pow]
  calc
    _ = (‖polynomial v (fun _ => 1) t‖ ^ r *
        ‖polynomial v (fun _ => 1) t‖ ^ (r + 2)) *
        ‖polynomial (fun i j => 2 * v i j) (fun _ => 1) t‖ *
        (‖polynomial u (fun _ => 1) t‖ ^ s *
          ‖polynomial u (fun _ => 1) t‖ ^ s) := by ring
    _ = _ := by
      rw [← pow_add, ← pow_add,
        show r + (r + 2) = 2 * (r + 2) - 2 by omega,
        show s + s = 2 * s by omega]

/-- An unordered position pair is counted once on each side. -/
theorem exceptional_le_pairs {ι κ d : Type*} [Fintype ι] [Fintype κ]
    (r s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) :
    exceptionalCount (r + 2) s v u ≤ (r + 2) ^ 2 * pairCount r s v u 0 1 := by
  let E := Finset.univ.filter (fun xy : ((Fin (r + 2) → ι) × (Fin s → κ)) ×
      ((Fin (r + 2) → ι) × (Fin s → κ)) =>
    ¬Function.Injective xy.1.1 ∧ configurationFrequency (r + 2) s v u xy.1 =
      configurationFrequency (r + 2) s v u xy.2)
  let I := (Finset.univ : Finset (Fin (r + 2) × Fin (r + 2))).filter (fun ij => ij.1 < ij.2)
  let B (ij : Fin (r + 2) × Fin (r + 2)) := Finset.univ.filter
    (fun xy : ((Fin (r + 2) → ι) × (Fin s → κ)) × ((Fin (r + 2) → ι) × (Fin s → κ)) =>
      xy.1.1 ij.1 = xy.1.1 ij.2 ∧ configurationFrequency (r + 2) s v u xy.1 =
        configurationFrequency (r + 2) s v u xy.2)
  have hcover : E ⊆ I.biUnion B := by
    intro xy hxy
    have hx := (Finset.mem_filter.mp hxy).2
    have hex : ∃ i j : Fin (r + 2), i < j ∧ xy.1.1 i = xy.1.1 j := by
      by_contra hn
      apply hx.1
      intro i j he
      by_contra hij
      rcases lt_or_gt_of_ne hij with hij | hij
      · exact hn ⟨i, j, hij, he⟩
      · exact hn ⟨j, i, hij, he.symm⟩
    obtain ⟨i, j, hij, he⟩ := hex
    exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, hx.2⟩⟩
  have hE : E.card ≤ (r + 2).choose 2 * pairCount r s v u 0 1 := by
    have hi : I.card = (r + 2).choose 2 := by
      simpa only [I, Finset.univ_product_univ, Finset.card_univ, Fintype.card_fin] using
        Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin (r + 2))))
    apply (Finset.card_le_card hcover).trans
    rw [← hi]
    apply Finset.card_biUnion_le_card_mul
    intro ij hij
    exact pair_le_first r s v u ij.1 ij.2 (ne_of_lt (Finset.mem_filter.mp hij).2)
  have hbad : exceptionalCount (r + 2) s v u ≤ 2 * E.card := by
    apply (Finset.card_le_card (t := E ∪ E.image Prod.swap) ?_).trans
    · exact (Finset.card_union_le _ _).trans (by
        have h := Finset.card_image_le (f := Prod.swap) (s := E)
        omega)
    · intro xy hxy
      have hx := (Finset.mem_filter.mp hxy).2
      by_cases hl : Function.Injective xy.1.1
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨xy.swap, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hx.2.symm⟩, by simp⟩
        exact fun hr => hx.1 ⟨hl, hr⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl, hx.2⟩)
  have hchoose : 2 * (r + 2).choose 2 ≤ (r + 2) ^ 2 := by
    rw [Nat.choose_two_right, mul_comm 2, pow_two]
    exact (Nat.div_mul_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  calc
    _ ≤ 2 * E.card := hbad
    _ ≤ 2 * ((r + 2).choose 2 * pairCount r s v u 0 1) := Nat.mul_le_mul_left _ hE
    _ ≤ _ := by rw [← mul_assoc]; exact Nat.mul_le_mul_right _ hchoose

/-- Every original block tuple is diagonal for every genuine tail collision. -/
theorem diagonal_block_le {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (m s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) :
    (Fintype.card ι : ℝ) ^ m * moment s u ≤ mixedMoment m s v u := by
  apply (VinogradovEndpointDeletion.diagonal_tail_le s m u v).trans_eq
  unfold mixedMoment
  apply integral_congr_ae
  filter_upwards [] with t
  exact mul_comm _ _

/-- The literal two-sided exceptional count has its fixed-tail fractional deficit. -/
theorem exceptional_le_moment {ι κ d : Type*}
    [Fintype ι] [Fintype κ] [Fintype d] {m : ℕ} (hm : 2 ≤ m)
    (s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ)
    (hdouble : mixedMoment m s (fun i j => 2 * v i j) u ≤ mixedMoment m s v u) :
    (exceptionalCount m s v u : ℝ) ≤ (m : ℝ) ^ 2 *
      (mixedMoment m s v u ^ (1 - 1 / (2 * (m : ℝ))) *
        moment s u ^ (1 / (2 * (m : ℝ)))) := by
  have hn := exceptional_le_pairs (m - 2) s v u
  simp only [Nat.sub_add_cancel hm] at hn
  have hc : (exceptionalCount m s v u : ℝ) ≤
      (m : ℝ) ^ 2 * (pairCount (m - 2) s v u 0 1 : ℝ) := by exact_mod_cast hn
  have hi := first_pair_le_integral (m - 2) s v u
  simp only [Nat.sub_add_cancel hm] at hi
  exact hc.trans (mul_le_mul_of_nonneg_left
    (hi.trans (repeated_integral_le_of_doubling hm s v u hdouble)) (sq_nonneg _))

/-- The exact diagonal reserve pays the repeated-coordinate allowance,
including zero moments and equality at the size threshold. -/
theorem repeated_allowance_absorption {m : ℕ} (hm : 1 ≤ m) {K J C : ℝ}
    (hK : 0 ≤ K) (hJ : 0 ≤ J) (hC : 0 ≤ C)
    (hdiag : C ^ (2 * m) * J ≤ K) :
    C * (K ^ (1 - 1 / (2 * (m : ℝ))) * J ^ (1 / (2 * (m : ℝ)))) ≤ K := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hb : 0 ≤ 1 / (2 * (m : ℝ)) := by positivity
  have ha : 0 ≤ 1 - 1 / (2 * (m : ℝ)) :=
    sub_nonneg.mpr ((div_le_one (by positivity)).mpr (by linarith))
  have hroot := Real.rpow_le_rpow (mul_nonneg (pow_nonneg hC _) hJ) hdiag hb
  rw [Real.mul_rpow (pow_nonneg hC _) hJ, ← Real.rpow_natCast,
    ← Real.rpow_mul hC] at hroot
  have he : ((2 * m : ℕ) : ℝ) * (1 / (2 * (m : ℝ))) = 1 := by
    push_cast
    field_simp
  rw [he, Real.rpow_one] at hroot
  calc
    _ = (C * J ^ (1 / (2 * (m : ℝ)))) * K ^ (1 - 1 / (2 * (m : ℝ))) := by ring
    _ ≤ K ^ (1 / (2 * (m : ℝ))) * K ^ (1 - 1 / (2 * (m : ℝ))) :=
      mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg hK _)
    _ = K := by
      rw [← Real.rpow_add_of_nonneg hK hb ha,
        show 1 / (2 * (m : ℝ)) + (1 - 1 / (2 * (m : ℝ))) = 1 by ring,
        Real.rpow_one]

/-- At an actual doubling-dominant system, both distinct blocks retain
at least half of the full mixed count once the alphabet has 4*m^4 entries. -/
theorem mixedMoment_le_twice_distinct {ι κ d : Type*}
    [Fintype ι] [Fintype κ] [Fintype d] {m : ℕ} (hm : 2 ≤ m)
    (s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ)
    (hdouble : mixedMoment m s (fun i j => 2 * v i j) u ≤ mixedMoment m s v u)
    (hsize : 4 * m ^ 4 ≤ Fintype.card ι) :
    mixedMoment m s v u ≤ 2 * (distinctCount m s v u : ℝ) := by
  have hJ : 0 ≤ moment s u := integral_nonneg (fun _ => by positivity)
  have hCsize : (2 * (m : ℝ) ^ 2) ^ 2 ≤ (Fintype.card ι : ℝ) := by
    have h : (4 : ℝ) * (m : ℝ) ^ 4 ≤ Fintype.card ι := by exact_mod_cast hsize
    nlinarith
  have hdiag : (2 * (m : ℝ) ^ 2) ^ (2 * m) * moment s u ≤ mixedMoment m s v u := by
    rw [pow_mul]
    exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (sq_nonneg _) hCsize m) hJ).trans (diagonal_block_le m s v u)
  have habs := repeated_allowance_absorption (m := m) (by omega)
    (mixedMoment_nonneg m s v u) hJ (by positivity) hdiag
  have hbad := exceptional_le_moment hm s v u hdouble
  have hsplit : (distinctCount m s v u : ℝ) + (exceptionalCount m s v u : ℝ) =
      mixedMoment m s v u := by
    rw [← fullCount_eq_mixedMoment]
    exact_mod_cast distinct_add_exceptional m s v u
  linarith

end
end RiemannGaussian.VinogradovMixedExceptional
