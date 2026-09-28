/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFiveOwnerCredit

/-!
# Kernel-checked extra owner credit for the literal five-prime family

Small rational cofactor cubes are disjoint from the old angular region
with owner share at most one half. The same literal population contains
both regions. The table is proposed by `generate_riesz_owner_boxes.py`;
all its inequalities and its final score are checked by Lean's kernel.
-/

namespace RiemannGaussian.ZetaRieszFiveOwnerBoxes
open scoped BigOperators

private abbrev Entry := ℕ × ℕ × ℕ × ℕ × ℕ

private def indices (r : Entry) : Fin 4 → ℕ := ![r.1,r.2.1,r.2.2.1,r.2.2.2.1]

private def numerator (r : Entry) : ℕ := r.2.2.2.2

private def rationalLo (r : Entry) (i : Fin 4) : ℚ := (indices r i : ℚ)/100+1/1000000

private def width : ℚ := 9998/1000000

private def rationalCap (a b : Fin 4 → ℚ) : ℚ :=
  min (a 0) (max 0 (min (69/100-1+a 2+a 1+a 0) (1-7/10-b 2))) +
  min (a 0) (max 0 (min (69/100-1+a 3+a 1+a 0) (1-7/10-b 3))) +
  min (a 0) (max 0 (min (69/100-b 3-b 2) (a 3+a 2+a 1+a 0-7/10)))

private def goodRow (r : Entry) : Prop :=
  let a := rationalLo r
  (∀ i, (1/100 : ℚ) ≤ a i ∧ a i+width ≤ 1) ∧
  (∀ i k, i < k → a i+width+1/1000000 ≤ a k) ∧
  (1/10 : ℚ)+1/1000000 ≤ 1-∑ i, (a i+width) ∧
  a 3+width+1/1000000 ≤ 1-∑ i, (a i+width) ∧
  1-(∑ i, a i)+1/1000000 ≤ (9/16 : ℚ) ∧
  1-a 3-a 2+1/1000000 ≤ (69/100 : ℚ) ∧
  (7/10 : ℚ)+1/1000000 ≤ 1-(a 1+width)-(a 0+width) ∧
  (1/2 : ℚ) < 1-∑ i, (a i+width) ∧
  (numerator r : ℚ)/1000000000 ≤ width^4*rationalCap a (fun i => a i+width)/
    ((7/10 : ℚ)*(1-∑ i, a i)*∏ i, (a i+width))

private instance (r : Entry) : Decidable (goodRow r) := by unfold goodRow; infer_instance

private def rows : List Entry :=
  -- BEGIN GENERATED EXACT BOXES
  [(2,3,11,28,6104),
   (2,3,12,27,5837),
   (2,3,12,28,5737),
   (2,3,13,26,1),
   (2,3,13,27,5519),
   (2,3,14,26,1),
   (2,4,10,28,5327),
   (2,4,11,27,10116),
   (2,4,11,28,4972),
   (2,4,12,26,4843),
   (2,4,12,27,9507),
   (2,4,13,25,1),
   (2,4,13,26,4578),
   (2,4,14,25,1),
   (2,5,9,28,4883),
   (2,5,10,27,9196),
   (2,5,10,28,4520),
   (2,5,11,26,8742),
   (2,5,11,27,8583),
   (2,5,12,25,4191),
   (2,5,12,26,8216),
   (2,5,13,24,1),
   (2,5,13,25,3962),
   (2,5,14,24,1),
   (2,6,8,28,4651),
   (2,6,9,27,8671),
   (2,6,9,28,4262),
   (2,6,10,26,8174),
   (2,6,10,27,8026),
   (2,6,11,25,7781),
   (2,6,11,26,7629),
   (2,6,12,24,3736),
   (2,6,12,25,7313),
   (2,6,13,23,1),
   (2,6,13,24,3532),
   (2,6,14,23,1),
   (2,7,8,27,8430),
   (2,7,8,28,4143),
   (2,7,9,26,7868),
   (2,7,9,27,7725),
   (2,7,10,25,7427),
   (2,7,10,26,7282),
   (2,7,11,24,7081),
   (2,7,11,25,6932),
   (2,7,12,23,3405),
   (2,7,12,24,6655),
   (2,7,13,23,3219),
   (2,8,9,25,7262),
   (2,8,9,26,7121),
   (2,8,10,24,6866),
   (2,8,10,25,6722),
   (2,8,11,23,6556),
   (2,8,11,24,6408),
   (2,8,12,22,3158),
   (2,8,12,23,6162),
   (2,8,13,22,2986),
   (2,9,10,23,6437),
   (2,9,10,24,6292),
   (2,9,11,22,6157),
   (2,9,11,23,6008),
   (2,9,12,21,2971),
   (2,9,12,22,5787),
   (2,9,13,21,2809),
   (2,10,11,21,5852),
   (2,10,11,22,5699),
   (2,10,12,20,2830),
   (2,10,12,21,5500),
   (2,10,13,20,2676),
   (2,11,12,19,2724),
   (2,11,12,20,5282),
   (2,11,13,19,2575),
   (2,12,13,18,2502),
   (3,4,9,28,4395),
   (3,4,10,27,8276),
   (3,4,10,28,4068),
   (3,4,11,26,7868),
   (3,4,11,27,7725),
   (3,4,12,25,3772),
   (3,4,12,26,7395),
   (3,4,13,24,1),
   (3,4,13,25,3566),
   (3,4,14,24,1),
   (3,5,8,28,4069),
   (3,5,9,27,7587),
   (3,5,9,28,3729),
   (3,5,10,26,10729),
   (3,5,10,27,7022),
   (3,5,11,25,6809),
   (3,5,11,26,10013),
   (3,5,12,24,3269),
   (3,5,12,25,6400),
   (3,5,13,24,3090),
   (3,6,7,28,3924),
   (3,6,8,27,7225),
   (3,6,8,28,3551),
   (3,6,9,26,10115),
   (3,6,9,27,6621),
   (3,6,10,25,9550),
   (3,6,10,26,9363),
   (3,6,11,24,6070),
   (3,6,11,25,8913),
   (3,6,12,23,2918),
   (3,6,12,24,5705),
   (3,6,13,23,2759),
   (3,7,8,26,9834),
   (3,7,8,27,6437),
   (3,7,9,25,9191),
   (3,7,9,26,9012),
   (3,7,10,24,8690),
   (3,7,10,25,8508),
   (3,7,11,23,5532),
   (3,7,11,24,8111),
   (3,7,12,22,2665),
   (3,7,12,23,5200),
   (3,7,13,22,2519),
   (3,8,9,24,8497),
   (3,8,9,25,8319),
   (3,8,10,23,8046),
   (3,8,10,24,7865),
   (3,8,11,22,5131),
   (3,8,11,23,7510),
   (3,8,12,21,2476),
   (3,8,12,22,4823),
   (3,8,13,21,2341),
   (3,9,10,22,7556),
   (3,9,10,23,7373),
   (3,9,11,21,4828),
   (3,9,11,22,7053),
   (3,9,12,20,2335),
   (3,9,12,21,4538),
   (3,9,13,20,2207),
   (3,10,11,20,4598),
   (3,10,11,21,6703),
   (3,10,12,19,2228),
   (3,10,12,20,4322),
   (3,10,13,19,2107),
   (3,11,12,19,4160),
   (3,11,13,18,2033),
   (4,5,7,28,3662),
   (4,5,8,27,6744),
   (4,5,8,28,3315),
   (4,5,9,26,9441),
   (4,5,9,27,6180),
   (4,5,10,25,8913),
   (4,5,10,26,8739),
   (4,5,11,24,5665),
   (4,5,11,25,8319),
   (4,5,12,23,2724),
   (4,5,12,24,5324),
   (4,5,13,23,2575),
   (4,6,7,27,6503),
   (4,6,7,28,3196),
   (4,6,8,26,8991),
   (4,6,8,27,5885),
   (4,6,9,25,11205),
   (4,6,9,26,8239),
   (4,6,10,24,7946),
   (4,6,10,25,10371),
   (4,6,11,23,5058),
   (4,6,11,24,7416),
   (4,6,12,22,2436),
   (4,6,12,23,4754),
   (4,6,13,22,2303),
   (4,7,8,25,10893),
   (4,7,8,26,8010),
   (4,7,9,24,10196),
   (4,7,9,25,9982),
   (4,7,10,23,7242),
   (4,7,10,24,9438),
   (4,7,11,22,4618),
   (4,7,11,23,6759),
   (4,7,12,21,2228),
   (4,7,12,22,4340),
   (4,7,13,21,2107),
   (4,8,9,23,9441),
   (4,8,9,24,9228),
   (4,8,10,22,6717),
   (4,8,10,23,8739),
   (4,8,11,21,4292),
   (4,8,11,22,6269),
   (4,8,12,20,2075),
   (4,8,12,21,4033),
   (4,8,13,20,1962),
   (4,9,10,21,6320),
   (4,9,10,22,8207),
   (4,9,11,20,4046),
   (4,9,11,21,5899),
   (4,9,12,19,1961),
   (4,9,12,20,3803),
   (4,9,13,19,1854),
   (4,10,11,20,5618),
   (4,10,12,19,3630),
   (4,10,13,18,1774),
   (5,6,7,26,8429),
   (5,6,7,27,5517),
   (5,6,8,25,10375),
   (5,6,8,26,7629),
   (5,6,9,24,9711),
   (5,6,9,25,9507),
   (5,6,10,23,6897),
   (5,6,10,24,8989),
   (5,6,11,22,4398),
   (5,6,11,23,6437),
   (5,6,12,21,2122),
   (5,6,12,22,4134),
   (5,6,13,21,2006),
   (5,7,8,24,11801),
   (5,7,8,25,9243),
   (5,7,9,23,8851),
   (5,7,9,24,10814),
   (5,7,10,22,6297),
   (5,7,10,23,8193),
   (5,7,11,21,4023),
   (5,7,11,22,5877),
   (5,7,12,20,1945),
   (5,7,12,21,3781),
   (5,7,13,20,1839),
   (5,8,9,22,8210),
   (5,8,9,23,10013),
   (5,8,10,21,5852),
   (5,8,10,22,7599),
   (5,8,11,20,3747),
   (5,8,11,21,5462),
   (5,8,12,19,1816),
   (5,8,12,20,3521),
   (5,8,13,19,1717),
   (5,9,10,21,7150),
   (5,9,11,20,5150),
   (5,9,12,19,3327),
   (5,9,13,18,1626),
   (6,7,8,23,10537),
   (6,7,8,24,10299),
   (6,7,9,22,7917),
   (6,7,9,23,9656),
   (6,7,10,21,5643),
   (6,7,10,22,7328),
   (6,7,11,20,3613),
   (6,7,11,21,5267),
   (6,7,12,19,1751),
   (6,7,12,20,3395),
   (6,7,13,19,1655),
   (6,8,9,22,8956),
   (6,8,10,21,6810),
   (6,8,11,20,4904),
   (6,8,12,19,3169),
   (6,8,13,18,1549)]
  -- END GENERATED EXACT BOXES

private def certified : Finset Entry := rows.toFinset

private theorem rows_valid : ∀ r ∈ certified, goodRow r := by decide +kernel

private theorem rows_injective : Set.InjOn indices (certified : Set Entry) := by decide +kernel

private theorem rows_total : (∑ r ∈ certified, numerator r) = 1397410 := by decide +kernel

noncomputable section
open MeasureTheory Filter Topology
open scoped Classical
open ZetaRieszFiveOwnerCredit ZetaRieszFivePrimeCells ZetaRieszFiveInteriorBudget
open ZetaRieszFiveAngularBoundary

private def realLo (r : Entry) (i : Fin 4) : ℝ := rationalLo r i

private theorem real_geometry (r : Entry) (hr : r ∈ certified) :
    (∀ i, (1/100 : ℝ) ≤ realLo r i ∧ realLo r i+(width : ℝ) ≤ 1) ∧
    (∀ i k, i < k → realLo r i+(width : ℝ)+1/1000000 ≤ realLo r k) ∧
    (1/10 : ℝ)+1/1000000 ≤ 1-∑ i, (realLo r i+(width : ℝ)) ∧
    realLo r 3+(width : ℝ)+1/1000000 ≤ 1-∑ i, (realLo r i+(width : ℝ)) ∧
    1-(∑ i, realLo r i)+1/1000000 ≤ (9/16 : ℝ) ∧
    1-realLo r 3-realLo r 2+1/1000000 ≤ (69/100 : ℝ) ∧
    (7/10 : ℝ)+1/1000000 ≤ 1-(realLo r 1+(width : ℝ))-(realLo r 0+(width : ℝ)) ∧
    (1/2 : ℝ) < 1-∑ i, (realLo r i+(width : ℝ)) := by
  obtain ⟨hc,ho,hmin,howner,hmax,hsat,htri,hhalf,_⟩ := rows_valid r hr
  dsimp [realLo]
  refine ⟨fun i => ?_,fun i k hik => ?_,?_,?_,?_,?_,?_,?_⟩
  · constructor
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using
        (Rat.cast_le (K := ℝ)).mpr (hc i).1
    · simpa only [Rat.cast_add,Rat.cast_one] using
        (Rat.cast_le (K := ℝ)).mpr (hc i).2
  · simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using
      (Rat.cast_le (K := ℝ)).mpr (ho i k hik)
  · simpa only [Rat.cast_add,Rat.cast_sub,Rat.cast_sum,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hmin
  · simpa only [Rat.cast_add,Rat.cast_sub,Rat.cast_sum,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr howner
  · simpa only [Rat.cast_add,Rat.cast_sub,Rat.cast_sum,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hmax
  · simpa only [Rat.cast_add,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hsat
  · simpa only [Rat.cast_add,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr htri
  · simpa only [Rat.cast_add,Rat.cast_sub,Rat.cast_sum,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr hhalf

private theorem row_credit (r : Entry) (hr : r ∈ certified) {lam : ℝ}
    (hl : (69/100 : ℝ) ≤ lam) (hu : lam ≤ 7/10) :
    (numerator r : ℝ)/1000000000 ≤ ∫ x in cell (realLo r) (width : ℝ), density lam x := by
  have hg := real_geometry r hr
  have hlow := cube_integral_lower hl hu (by linarith : 0 < lam)
    (by norm_num [width] : (0 : ℝ) ≤ (width : ℝ))
    (fun i => by linarith [(hg.1 i).1] : ∀ i, 0 < realLo r i)
    (by linarith [hg.2.2.1] : 0 < 1-∑ i, (realLo r i+(width : ℝ)))
  apply le_trans _ hlow
  have hc := (rows_valid r hr).2.2.2.2.2.2.2.2
  rw [← mul_div_assoc]
  dsimp only [realLo,lowerCap]
  dsimp only [rationalCap] at hc
  simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_sub,Rat.cast_add,Rat.cast_sum,Rat.cast_prod,
    Rat.cast_min,Rat.cast_max,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one] using
    (Rat.cast_le (K := ℝ)).mpr hc

private theorem cubes_disjoint : Set.PairwiseDisjoint (certified : Set Entry)
    (fun r => cell (realLo r) (width : ℝ)) := by
  intro r hr q hq hne
  have hi : indices r ≠ indices q := fun he => hne (rows_injective hr hq he)
  obtain ⟨i,hi⟩ : ∃ i, indices r i ≠ indices q i := by
    by_contra hn
    push Not at hn
    exact hi (funext hn)
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx := (Set.mem_pi.mp hx) i (Set.mem_univ i)
  have hy := (Set.mem_pi.mp hy) i (Set.mem_univ i)
  have hcast (a b : ℕ) (hab : a < b) : (a : ℝ)+1 ≤ b := by exact_mod_cast hab
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have hh := hcast _ _ hlt
    norm_num [realLo,rationalLo,width] at hx hy
    linarith
  · have hh := hcast _ _ hgt
    norm_num [realLo,rationalLo,width] at hx hy
    linarith

/-- The extra domain lies entirely ABOVE the old one-half owner cap. It
is used only to strengthen the integral for the existing literal family. -/
def ownerRegion : Set (Fin 4 → ℝ) :=
  ⋃ r ∈ certified, cell (realLo r) (width : ℝ)

/-- The extra domain is a finite measurable union of disjoint rational cubes. -/
theorem ownerRegion_measurable : MeasurableSet ownerRegion := by
  apply MeasurableSet.iUnion
  intro r
  apply MeasurableSet.iUnion
  intro _hr
  exact (measurableSet_pi (Set.to_countable _)).mpr (Or.inl (fun _ _ => measurableSet_Ioc))

/-- All 246 rational lower scores are checked and added exactly. This
credit is uniform throughout the cutoff ratio 69/100..7/10. -/
theorem owner_integral_lower {lam : ℝ} (hl : (69/100 : ℝ) ≤ lam) (hu : lam ≤ 7/10) :
    (1/750 : ℝ) ≤ ∫ x in ownerRegion, density lam x := by
  have hf (r : Entry) (hr : r ∈ certified) :
      IntegrableOn (density lam) (cell (realLo r) (width : ℝ)) := by
    have hg := real_geometry r hr
    exact integrableOn_density (by linarith : 0 < lam)
      (fun i => by linarith [(hg.1 i).1]) (by linarith [hg.2.2.1])
  have hi := integral_biUnion_finset certified
    (fun r _ => (measurableSet_pi (Set.to_countable _)).mpr
      (Or.inl (fun _ _ => measurableSet_Ioc))) cubes_disjoint hf
  change (∫ x in ⋃ r ∈ certified, cell (realLo r) (width : ℝ), density lam x) =
    ∑ r ∈ certified, ∫ x in cell (realLo r) (width : ℝ), density lam x at hi
  have hs := Finset.sum_le_sum (fun r hr => row_credit r hr hl hu)
  rw [← Finset.sum_div,← Nat.cast_sum,rows_total] at hs
  rw [← hi] at hs
  change (1/750 : ℝ) ≤ ∫ x in ⋃ r ∈ certified, cell (realLo r) (width : ℝ), density lam x
  linarith only [hs]

/-- Extra cubes and the old credited domain have no common angular point. -/
theorem ownerRegion_disjoint (lo hi : ℝ) : Disjoint ownerRegion (orderedRegion lo hi) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨r,hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hr,hx⟩ := Set.mem_iUnion.mp hx
  have hg := real_geometry r hr
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4)))
    (fun i _ => ((Set.mem_pi.mp hx) i (Set.mem_univ i)).2)
  have hh := hg.2.2.2.2.2.2.2
  have howner := hy.2.2.2.2.2.1
  linarith

/-- Every extra cube is covered by the original fine interior grid,
uniformly over all cutoff bins inside 69/100..7/10. No new prime mask is
introduced and no boundary mass is silently discarded. -/
theorem ownerRegion_subset_cells {M : ℕ} {lo hi e b : ℝ}
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000)
    (he : e ≤ b) (hcover : (1 : ℝ) ≤ M*b)
    (hl : (69/100 : ℝ) ≤ lo) (hu : hi ≤ 7/10) :
    ownerRegion ⊆ ⋃ v ∈ interiorFamily M lo hi e b, cell (gridLo 0 b v) b := by
  intro x hx
  obtain ⟨r,hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hr,hx⟩ := Set.mem_iUnion.mp hx
  have hx (i : Fin 4) : realLo r i < x i ∧ x i ≤ realLo r i+(width : ℝ) :=
    (Set.mem_pi.mp hx) i (Set.mem_univ i)
  obtain ⟨hc,ho,hmin,howner,hmax,hsat,htri,_⟩ := real_geometry r hr
  have hslo := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4)))
    (fun i _ => (hx i).1.le)
  have hshi := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4)))
    (fun i _ => (hx i).2)
  apply covered_of_strict_geometry hb hsmall he hcover
  · exact fun i => ⟨(hc i).1.trans (hx i).1.le,(hx i).2.trans (hc i).2⟩
  · intro i k hik
    linarith [ho i k hik,hx i,hx k]
  · linarith
  · linarith [hx 3]
  · linarith
  · linarith [hx 3,hx 2]
  · linarith [hx 1,hx 0]

/-- The same literal five-prime family earns an ADDITIONAL 1/800 angular
credit, after all box/counting/allocation and boundary losses. This
strengthens its original core comparison and keeps its one signed rest. -/
theorem eventually_owner_core_floor {u h b lo hi : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b)
    (hlo : (69/100 : ℝ) ≤ lo) (hhi : hi ≤ 7/10) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let I := interiorFamily M lo hi (h/t) b
      let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h y
        (fun i => t*gridLo 0 b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N → lo ≤ L/t → L/t ≤ hi →
      (∑ n ∈ S\D, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (((996/1000 : ℝ)*(∫ x in orderedRegion lo hi, density (L/t) x)-1/50000+1/800)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*
            max 0 (-Real.cos (y*t)-|y| * h)*h)) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  have hwidth : ∀ᶠ N : ℕ in atTop, h ≤ b*N :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hb).eventually_ge_atTop h
  filter_upwards [eventually_family_core_floor (a := 0) (M := M) hu hU hh hhu hb
      (by linarith : b ≤ 1/1000000000000000000),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hwidth,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hwidth hj t y
  dsimp only
  intro htlo hthi hlt htl
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let I := interiorFamily M lo hi (h/t) b
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hj
  have ht : 0 < t := by nlinarith only [htlo,hn]
  have hhb : h/t ≤ b := (div_le_iff₀ ht).mpr (by nlinarith only [hwidth,htlo,hn,hb])
  have hL : (17/25 : ℝ) ≤ L/t := by linarith only [hlo,hlt]
  have hf := hJ I t y htlo hthi (by
    intro v hv
    have hg := (Finset.mem_filter.mp hv).2
    dsimp only at hg
    exact ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2.1,hg.2.2.2.2.1,
      hg.2.2.2.2.2.1.trans hlt,htl.trans hg.2.2.2.2.2.2⟩)
  have hang := ordered_plus_extra_le_cells hL hb hsmall hhb hcover
    ownerRegion ownerRegion_measurable (ownerRegion_subset_cells hb hsmall hhb hcover hlo hhi)
    (ownerRegion_disjoint lo hi) (owner_integral_lower (hlo.trans hlt) (htl.trans hhi))
  have hnum : (996/1000 : ℝ)*(∫ x in orderedRegion lo hi, density (L/t) x)-1/50000+1/800 ≤
      (996/1000 : ℝ)*(∫ x in ⋃ v ∈ I, cell (gridLo 0 b v) b, density (L/t) x)-1/100000 := by
    linarith only [hang]
  have hmul := mul_le_mul_of_nonneg_right hnum
    (show 0 ≤ (Real.exp (-(t+h)/2)*t^N/N.factorial)*
      max 0 (-Real.cos (y*t)-|y| * h)*h by positivity)
  linarith only [hmul,hf]

/-- The extra owner credit also improves the original-height ceiling.
Calibration only pays its explicit relative phase cost; no term of the
literal sum or its signed complement is changed. -/
theorem eventually_owner_core_ceiling {u h b lo hi : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b)
    (hlo : (69/100 : ℝ) ≤ lo) (hhi : hi ≤ 7/10) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let I := interiorFamily M lo hi (h/t) b
      let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h (Real.pi/t)
        (fun i => t*gridLo 0 b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N → lo ≤ L/t → L/t ≤ hi →
      0 ≤ Real.cos (y*t)-|y| * h →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ S\D, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
        (((996/1000 : ℝ)*(∫ x in orderedRegion lo hi, density (L/t) x)-1/50000+1/800)*
          ((1-|Real.pi/t| * h)*(Real.exp (-(t+h)/2)*t^N/N.factorial)*
            (Real.cos (y*t)-|y| * h)*h)) := by
  filter_upwards [eventually_owner_core_floor hu hU hh hhu hb hsmall hcover hlo hhi,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hN t y
  dsimp only
  intro htlo hthi hlt htl hphase
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let I := interiorFamily M lo hi (h/t) b
  let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h (Real.pi/t)
    (fun i => t*gridLo 0 b v i) (fun _ => t*b))
  let f := fun (y : ℝ) (n : ℕ) =>
    ZetaRieszJointAllocation.residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let C := ((996/1000 : ℝ)*(∫ x in orderedRegion lo hi, density (L/t) x)-1/50000+1/800)*
      ((Real.exp (-(t+h)/2)*t^N/N.factorial)*(1-|Real.pi/t| * h)*h)
  have ht : 1 ≤ t := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith only [htlo,hn]
  have ht0 : 0 < t := by linarith only [ht]
  have hcal := ZetaRieszOppositePhase.calibration_phase ht hh.le hhu
  have hf := hJ t (Real.pi/t) htlo hthi hlt htl
  rw [hcal.1] at hf
  have heps : 0 ≤ 1-|Real.pi/t| * h := by linarith only [hcal.2]
  simp only [neg_neg,max_eq_right heps] at hf
  have hez := congrArg Complex.re
    (Finset.sum_sdiff (f := f (Real.pi/t : ℝ)) (Finset.inter_subset_left (s₂ := D) : S ∩ D ⊆ S))
  have hey := congrArg Complex.re
    (Finset.sum_sdiff (f := f y) (Finset.inter_subset_left (s₂ := D) : S ∩ D ⊆ S))
  simp only [Finset.sdiff_inter_self_left,Complex.add_re] at hez hey
  have hfloor : C ≤ (∑ n ∈ S ∩ D, f (Real.pi/t : ℝ) n).re := by
    change (∑ n ∈ S\D, f (Real.pi/t : ℝ) n).re+C ≤ (∑ n ∈ S, f (Real.pi/t : ℝ) n).re at hf
    linarith only [hez,hf]
  have hupper := ZetaRieszOppositePhase.ceiling_of_calibrated_floor (S ∩ D) A N L t h y (Real.pi/t) C
    (by
      intro n hn
      obtain ⟨v,hv,hn⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hn).2
      exact ZetaRieszJointCapacityCeiling.interior_supply_coefficient_nonpos ht0
        (SquarefreeVaughanLogSource.length_pos u N) hlt htl hv hn)
    (by
      intro n hn
      obtain ⟨v,_,hn⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hn).2
      have ht' := ZetaRieszJointCapacityFloor.supplyCell_log_bounds hn
      exact ⟨ht'.1.le,ht'.2⟩) hphase hfloor
  change (∑ n ∈ S, f y n).re ≤ _
  have hsum := hey.symm.le.trans (add_le_add (le_refl (∑ n ∈ S\D, f y n).re) hupper)
  convert hsum using 1 <;> first | rfl | (dsimp only [C]; ring)

end
end RiemannGaussian.ZetaRieszFiveOwnerBoxes
