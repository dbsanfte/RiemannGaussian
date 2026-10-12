import RiemannGaussian.SemiprimeSignedMomentAcquisitionObstruction

/-!
# Fixed original row gaps and isolated signed poles

For every prescribed integer gap, the exact original off-diagonal row
pairs have total mass at most `2 * (m - 1)^2` over all unit two-digit input
states. The quadratic lower residue supplies at most two partners; each
distinct pair has at most one second carry.

Independently, any globally unique labels with nonzero arbitrary signed
weights retain their poles in an exact normalized whole-series relation.
Deleting both endpoints of a collision edge set yields the grid bound
`(M - 2 * E.card) * J ≤ U.natDegree`.

The actual infinite semiprime family, prime-incidence envelope, selector
summation and acquisition-cost consequences are classical audit arguments.
They are not assumptions or additional claims of this native leaf.
-/

namespace RiemannGaussian.SemiprimeIsolatedRowAcquisitionObstruction

open scoped BigOperators
open RiemannGaussian.SemiprimeGlobalPhaseCancellation
open RiemannGaussian.SemiprimeOffsetCarryObstruction
open RiemannGaussian.SemiprimeSeedEnergyAcquisitionObstruction

/-- Any prescribed exact difference between two distinct original rows
can occur at only one second carry, even when that difference is nonzero. -/
theorem prescribed_difference_unique_carry {s m j k u v : ℕ} (hm : m.Prime)
    (hj : 1 ≤ j) (hjm : j < m) (hk : 1 ≤ k) (hkm : k < m) (hjk : j ≠ k)
    (hu : u < m) (hv : v < m) (d : ℤ)
    (he : seedOffset (s+m*u) m j-seedOffset (s+m*u) m k=d)
    (he₀ : seedOffset (s+m*v) m j-seedOffset (s+m*v) m k=d) : u=v := by
  have hjcop : j.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjm)).symm
  have hkcop : k.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hkm)).symm
  let D := seedOffset (s+m*u) m j-seedOffset (s+m*v) m j
  have hJ := offset_difference_modEq hm.pos hjcop (carry_class (s:=s) (u:=u) (v:=v))
  have hK := offset_difference_modEq hm.pos hkcop (carry_class (s:=s) (u:=u) (v:=v))
  have hKD : seedOffset (s+m*u) m k-seedOffset (s+m*v) m k=D := by
    dsimp only [D]
    linear_combination -he+he₀
  rw [hKD] at hK
  change (j : ℤ)*D ≡ -(((s+m*u : ℕ) : ℤ)-(s+m*v : ℕ)) [ZMOD (m : ℤ)^2] at hJ
  change (k : ℤ)*D ≡ -(((s+m*u : ℕ) : ℤ)-(s+m*v : ℕ)) [ZMOD (m : ℤ)^2] at hK
  have hd : (m : ℤ)^2 ∣ ((j : ℤ)-k)*D := by
    have h := (hJ.sub hK).symm.dvd
    convert h using 1
    ring
  have hdiff : (((j : ℤ)-k : ℤ) : ZMod m) ≠ 0 := by
    intro heq
    have heq' : (j : ZMod m)=(k : ZMod m) := by
      simpa only [Int.cast_sub,Int.cast_natCast,sub_eq_zero] using heq
    have hv' := congrArg ZMod.val heq'
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hjm,Nat.mod_eq_of_lt hkm] at hv'
    exact hjk hv'
  have hD := (integer_coprime_square hm ((j : ℤ)-k) hdiff).dvd_of_dvd_mul_left hd
  have hDmod : D ≡ 0 [ZMOD (m : ℤ)^2] := Int.modEq_iff_dvd.mpr (by simpa using hD.neg_right)
  have hN := (hDmod.mul_left (j : ℤ)).symm.trans hJ
  have hclass : ((s+m*u : ℕ) : ℤ) ≡ ((s+m*v : ℕ) : ℤ) [ZMOD (m : ℤ)^2] := by
    apply Int.modEq_iff_dvd.mpr
    simpa only [mul_zero,sub_zero,neg_sub] using hN.dvd
  exact equal_input_carry hm.pos hu hv hclass

/-- Every ordered off-diagonal pair realizing one prescribed integer gap. -/
noncomputable def exactDifferencePairs (N m : ℕ) (d : ℤ) : Finset (ℕ × ℕ) :=
  ((Finset.range (m-1)) ×ˢ (Finset.range (m-1))).filter fun jk =>
    jk.1 ≠ jk.2 ∧ seedOffset N m (jk.1+1)-seedOffset N m (jk.2+1)=d

/-- The necessary lower-residue pairs for the prescribed gap. -/
noncomputable def differenceCandidates (s m : ℕ) (d : ℤ) : Finset (ℕ × ℕ) :=
  ((Finset.range (m-1)) ×ˢ (Finset.range (m-1))).filter fun jk =>
    jk.1 ≠ jk.2 ∧ (seedOffset s m (jk.1+1) : ZMod m)-
      (seedOffset s m (jk.2+1) : ZMod m)=(d : ZMod m)

/-- A prescribed difference has at most two lower-residue partners for each row. -/
theorem differenceCandidates_card_le {s m : ℕ} (hm : m.Prime) (hs : m.Coprime s) (d : ℤ) :
    (differenceCandidates s m d).card ≤ 2*(m-1) := by
  classical
  have hfold : (differenceCandidates s m d).card =
      ∑ j ∈ Finset.range (m-1), ((Finset.range (m-1)).filter fun k => j ≠ k ∧
        (seedOffset s m (j+1) : ZMod m)-(seedOffset s m (k+1) : ZMod m)=(d : ZMod m)).card := by
    simp only [differenceCandidates, Finset.card_eq_sum_ones, Finset.sum_filter,
      Finset.sum_product]
  rw [hfold]
  calc
    _ ≤ ∑ _j ∈ Finset.range (m-1), 2 := by
      apply Finset.sum_le_sum
      intro j _
      have hsub : ((Finset.range (m-1)).filter fun k => j ≠ k ∧
          (seedOffset s m (j+1) : ZMod m)-(seedOffset s m (k+1) : ZMod m)=(d : ZMod m)) ⊆
          phaseFiber s m (seedOffset s m (j+1)-d) := by
        intro k hk
        have h := Finset.mem_filter.mp hk
        apply Finset.mem_filter.mpr
        refine ⟨h.1, ?_⟩
        push_cast
        linear_combination -h.2.2
      exact (Finset.card_le_card hsub).trans (phaseFiber_card_le_two hm hs _)
    _ = 2*(m-1) := by simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring

/-- Lower-state candidates exactly contain the original carry realization filter. -/
theorem exactDifferencePairs_eq_candidates_filter {s m u : ℕ} (hm : m.Prime) (d : ℤ) :
    exactDifferencePairs (s+m*u) m d = (differenceCandidates s m d).filter fun jk =>
      seedOffset (s+m*u) m (jk.1+1)-seedOffset (s+m*u) m (jk.2+1)=d := by
  classical
  ext jk
  simp only [exactDifferencePairs, differenceCandidates, Finset.mem_filter]
  constructor
  · rintro ⟨hjk, hne, he⟩
    refine ⟨⟨hjk, hne, ?_⟩, he⟩
    have hb := Finset.mem_product.mp hjk
    have hj : jk.1+1 < m := by have h := Finset.mem_range.mp hb.1; omega
    have hk : jk.2+1 < m := by have h := Finset.mem_range.mp hb.2; omega
    have hecast := congrArg (fun z : ℤ => (z : ZMod m)) he
    simp only [Int.cast_sub] at hecast
    rw [carry_offset_residue hm hj, carry_offset_residue hm hk] at hecast
    exact hecast
  · exact fun h => ⟨h.1.1, h.1.2.1, h.2⟩

/-- Whole second-carry mass of any prescribed off-diagonal gap is linear. -/
theorem prescribed_difference_carry_mass_le {s m : ℕ} (hm : m.Prime)
    (hs : m.Coprime s) (d : ℤ) :
    ∑ u ∈ Finset.range m, (exactDifferencePairs (s+m*u) m d).card ≤ 2*(m-1) := by
  classical
  have hrewrite : (∑ u ∈ Finset.range m, (exactDifferencePairs (s+m*u) m d).card) =
      ∑ jk ∈ differenceCandidates s m d, ((Finset.range m).filter fun u =>
        seedOffset (s+m*u) m (jk.1+1)-seedOffset (s+m*u) m (jk.2+1)=d).card := by
    simp_rw [exactDifferencePairs_eq_candidates_filter hm d, Finset.card_eq_sum_ones,
      Finset.sum_filter]
    exact Finset.sum_comm
  rw [hrewrite]
  calc
    _ ≤ ∑ _jk ∈ differenceCandidates s m d, 1 := by
      apply Finset.sum_le_sum
      intro jk hjk
      have hp := Finset.mem_product.mp (Finset.mem_filter.mp hjk).1
      have hne := (Finset.mem_filter.mp hjk).2.1
      have hj : jk.1+1 < m := by have h := Finset.mem_range.mp hp.1; omega
      have hk : jk.2+1 < m := by have h := Finset.mem_range.mp hp.2; omega
      apply Finset.card_le_one.mpr
      intro u hu v hv
      exact prescribed_difference_unique_carry hm (by omega) hj (by omega) hk
        (by omega) (Finset.mem_range.mp (Finset.mem_filter.mp hu).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hv).1) d
        (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2
    _ = (differenceCandidates s m d).card := by simp
    _ ≤ 2*(m-1) := differenceCandidates_card_le hm hs d

/-- Across every unit two-digit input state, a prescribed exact original
row gap has only quadratic labelled mass. No prime distribution is used. -/
theorem prescribed_difference_two_digit_mass_le {m : ℕ} (hm : m.Prime) (d : ℤ) :
    ∑ s ∈ Finset.range (m-1), ∑ u ∈ Finset.range m,
      (exactDifferencePairs (s+1+m*u) m d).card ≤ 2*(m-1)^2 := by
  calc
    _ ≤ ∑ _s ∈ Finset.range (m-1), 2*(m-1) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsm : s+1 < m := by have h := Finset.mem_range.mp hs; omega
      have hcop : m.Coprime (s+1) :=
        hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hsm)
      exact prescribed_difference_carry_mass_le hm hcop d
    _ = 2*(m-1)^2 := by simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring

open scoped BigOperators
open Polynomial RiemannGaussian.SemiprimeSeedMomentPoleRetention

theorem labelled_weighted_group {K ι : Type*} [CommRing K] [DecidableEq K]
    (I : Finset ι) (x weight : ι → K) :
    (∑ i ∈ I, PowerSeries.C (weight i) * positiveMoments (x i)) =
      ∑ y ∈ I.image x, PowerSeries.C
        (∑ i ∈ I.filter (fun i => x i = y), weight i) * positiveMoments y := by
  classical
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun i hi => Finset.mem_image_of_mem x hi)
    (fun i => PowerSeries.C (weight i) * positiveMoments (x i))]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_congr rfl (fun i hi =>
    congrArg (fun z => PowerSeries.C (weight i) * positiveMoments z)
      (Finset.mem_filter.mp hi).2)]
  rw [←Finset.sum_mul, ←map_sum]

/-- Globally unique labels with nonzero signed weight cannot lose their
pole through cancellation by any of the remaining original labels. -/
theorem unique_label_denominator_degree {K ι : Type*} [Field K]
    (I G : Finset ι) (x weight : ι → K) (hG : G ⊆ I)
    (hx : ∀ i ∈ I, x i ≠ 0)
    (hunique : ∀ i ∈ G, ∀ j ∈ I, x j = x i → j = i)
    (hw : ∀ i ∈ G, weight i ≠ 0)
    (U V : K[X]) (hU : U.coeff 0 = 1)
    (hUV : (U : PowerSeries K) *
      (∑ i ∈ I, PowerSeries.C (weight i) * positiveMoments (x i)) =
      (V : PowerSeries K)) : G.card ≤ U.natDegree := by
  classical
  let mu := fun y => ∑ i ∈ I.filter (fun i => x i = y), weight i
  let T := (I.image x).filter fun y => mu y ≠ 0
  have hsum : (∑ y ∈ T, PowerSeries.C (mu y) * positiveMoments y) =
      (∑ i ∈ I, PowerSeries.C (weight i) * positiveMoments (x i)) := by
    rw [labelled_weighted_group I x weight]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro y hy hyT
    have hz : mu y = 0 := by
      by_contra hne
      exact hyT (Finset.mem_filter.mpr ⟨hy, hne⟩)
    simp only [hz, map_zero, zero_mul]
  have hT : T.card ≤ U.natDegree := by
    apply weighted_denominator_degree T mu
      (by
        intro y hy
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hy).1
        exact hx i hi)
      (fun _ hy => (Finset.mem_filter.mp hy).2) U V hU
    rw [hsum]
    exact hUV
  have hsub : G.image x ⊆ T := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image_of_mem x (hG hi), ?_⟩
    have hf : I.filter (fun j => x j = x i) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro h
        exact hunique i hi j h.1 h.2
      · intro h
        subst j
        exact ⟨hG hi, rfl⟩
    dsimp only [mu]
    rw [hf, Finset.sum_singleton]
    exact hw i hi
  have hinj : Set.InjOn x G := by
    intro i hi j hj he
    exact (hunique i hi j (hG hj) he.symm).symm
  rw [←Finset.card_image_of_injOn hinj]
  exact (Finset.card_le_card hsub).trans hT

/-- Delete both endpoints of every possible off-row collision edge. -/
def isolatedRows {M : ℕ} (E : Finset (Fin M × Fin M)) : Finset (Fin M) :=
  Finset.univ \ (E.image Prod.fst ∪ E.image Prod.snd)

theorem isolatedRows_card_bound {M : ℕ} (E : Finset (Fin M × Fin M)) :
    M ≤ (isolatedRows E).card + 2 * E.card := by
  classical
  have he : (E.image Prod.fst ∪ E.image Prod.snd).card ≤ 2 * E.card := by
    exact (Finset.card_union_le _ _).trans
      (by nlinarith only [Finset.card_image_le (f := Prod.fst) (s := E),
        Finset.card_image_le (f := Prod.snd) (s := E)])
  have hc := Finset.card_sdiff_add_card_eq_card
    (s := E.image Prod.fst ∪ E.image Prod.snd)
    (t := (Finset.univ : Finset (Fin M))) (Finset.subset_univ _)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  change (isolatedRows E).card + (E.image Prod.fst ∪ E.image Prod.snd).card = M at hc
  omega

/-- Any signed label weights nonzero on isolated rows retain every grid
point on those rows, irrespective of cancellation elsewhere. -/
theorem isolated_grid_denominator_degree {K : Type*} [Field K] {M J : ℕ}
    (point weight : Fin M × Fin J → K)
    (hrow : ∀ i, Function.Injective (fun k => point (i, k)))
    (E : Finset (Fin M × Fin M))
    (hcollision : ∀ i j, i ≠ j → ∀ k l, point (i, k) = point (j, l) →
      (i, j) ∈ E ∨ (j, i) ∈ E)
    (hx : ∀ ik, point ik ≠ 0)
    (hw : ∀ i ∈ isolatedRows E, ∀ k, weight (i, k) ≠ 0)
    (U V : K[X]) (hU : U.coeff 0 = 1)
    (hUV : (U : PowerSeries K) *
      (∑ ik : Fin M × Fin J, PowerSeries.C (weight ik) * positiveMoments (point ik)) =
      (V : PowerSeries K)) :
    (M - 2 * E.card) * J ≤ U.natDegree := by
  classical
  let G := isolatedRows E ×ˢ (Finset.univ : Finset (Fin J))
  have hdeg : G.card ≤ U.natDegree := by
    apply unique_label_denominator_degree Finset.univ G point weight
      (Finset.subset_univ _) (fun ik _ => hx ik)
      (by
        intro a ha b _ he
        have hiso := (Finset.mem_product.mp ha).1
        have hr : b.1 = a.1 := by
          by_contra hne
          obtain hedge | hedge := hcollision a.1 b.1 (Ne.symm hne) a.2 b.2 he.symm
          · have hm := Finset.mem_image_of_mem Prod.fst hedge
            exact (Finset.mem_sdiff.mp hiso).2 (Finset.mem_union_left _ hm)
          · have hm := Finset.mem_image_of_mem Prod.snd hedge
            exact (Finset.mem_sdiff.mp hiso).2 (Finset.mem_union_right _ hm)
        have hk : b.2 = a.2 := by
          apply hrow a.1
          change point (b.1, b.2) = point (a.1, a.2) at he
          simpa only [hr] using he
        exact Prod.ext hr hk)
      (fun a ha => hw a.1 (Finset.mem_product.mp ha).1 a.2) U V hU hUV
  have hrows : M - 2 * E.card ≤ (isolatedRows E).card := by
    have h := isolatedRows_card_bound E
    omega
  calc
    _ ≤ (isolatedRows E).card * J := Nat.mul_le_mul_right _ hrows
    _ = G.card := by simp only [G, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ ≤ _ := hdeg

end RiemannGaussian.SemiprimeIsolatedRowAcquisitionObstruction
