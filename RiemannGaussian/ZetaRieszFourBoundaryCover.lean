/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointPrimeCells

/-!
# A complete adverse four-prime cover with ordering boundaries

A finite cofactor grid covers the entire positive-coefficient,
negative-cosine four-prime population above a given logarithmic prime
threshold. Actual prime ordering is retained in each cell. The resulting
signed inequality charges explicit Darboux debits and keeps every other
carrier term signed. A numerical comparison against five-prime credit is
still required; the finite debit is not asserted small at source scale.
-/

namespace RiemannGaussian.ZetaRieszFourBoundaryCover
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic
open ZetaRieszCoupledWindow ZetaRieszMacroPrimeWindows ZetaRieszFourPrimeCells

/-- Uniform half-open cells include every point of their full interval,
including points lying exactly on an interior grid endpoint. -/
theorem exists_grid_index {a b x : ℝ} (M : ℕ)
    (hlo : a < x) (hhi : x ≤ a+M*b) :
    ∃ i : Fin M, a+(i : ℕ)*b < x ∧ x ≤ a+((i : ℕ)+1)*b := by
  induction M with
  | zero => simp only [Nat.cast_zero,zero_mul,add_zero] at hhi; linarith
  | succ M ih =>
    by_cases hx : x ≤ a+M*b
    · obtain ⟨i,hi⟩ := ih hx
      exact ⟨i.castSucc,hi⟩
    · refine ⟨⟨M,Nat.lt_succ_self M⟩,lt_of_not_ge hx,?_⟩
      simpa only [Nat.cast_succ] using hhi

/-- Coordinate origins of a finite three-prime logarithmic grid. -/
def gridLo (a b : ℝ) {M : ℕ} (v : Fin 3 → Fin M) (i : Fin 3) : ℝ :=
  a+(v i : ℕ)*b

/-- Cells with a uniformly long largest-prime window. Cells crossing the
other prime-order faces remain present with literal ordering masks. -/
def gridCover (M : ℕ) (a b t : ℝ) : Finset (Fin 3 → Fin M) :=
  Finset.univ.filter (fun v => v 0 ≤ v 1 ∧ v 1 ≤ v 2 ∧
    t/4 ≤ t-∑ i, (gridLo a b v i+b))

/-- The whole adverse four-prime population in a total-log interval,
above a specified prime-log threshold, inside the original finite support. -/
def adversePopulation (S : Finset ℕ) (L t h y a : ℝ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ n.primeFactors.card = 4 ∧
    (∀ p ∈ n.primeFactors, a < Real.log p) ∧
    t < Real.log n ∧ Real.log n ≤ t+h ∧
    0 < (SquarefreeVaughanLogSource.coefficient L n).re ∧ Real.cos (y*Real.log n) ≤ 0)

/-- The full adverse population is covered, including both middle-prime
ordering boundaries. The final-window restriction deletes no adverse atom:
its exact positive coefficient forces the largest-prime log above 9T/25. -/
theorem adversePopulation_subset_grid (S : Finset ℕ) {L t h y a b : ℝ} (M : ℕ)
    (hhT : h ≤ t/100) (hb : 0 < b) (hbT : b ≤ t/100)
    (hL : 0 < L) (hLt : L ≤ t)
    (hcut : (17/25 : ℝ)*(t+h) ≤ L) (hcover : t+h ≤ a+M*b) :
    adversePopulation S L t h y a ⊆
      (gridCover M a b t).biUnion (fun v => boundaryCell S L t h y (gridLo a b v) (fun _ => b)) := by
  intro n hn
  obtain ⟨hnS,hs,hc,hsmall,hTlo,hThi,hpos,hcos⟩ := Finset.mem_filter.mp hn
  obtain ⟨v,hv,horder,he⟩ := exists_ordered_four_factorization hs hc
  have hdiv (i : Fin 4) : v i ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hv i,by rw [he]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i),hs.ne_zero⟩
  have hlog (i : Fin 4) : Real.log (v i) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast (hv i).pos)
      (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) (Nat.mem_primeFactors.mp (hdiv i)).2.1)
  let w : Fin 3 → ℕ := fun i => v i.castSucc
  have he' : n = v 3*(v 2*(v 1*v 0)) := by rw [he,Fin.prod_univ_four]; ring
  have ho : w 0 < w 1 ∧ w 1 < w 2 := ⟨horder (by decide),horder (by decide)⟩
  have hlast : w 2 < v 3 := horder (by decide)
  have hew : (∏ i, w i)*v 3 = n := by
    rw [he',Fin.prod_univ_three]
    dsimp [w]
    ring
  have hgeom := ZetaRieszOrderedCapacity.positive_four_geometry (hv 3) (hv 2) (hv 1) (hv 0)
    ho.1 ho.2 hlast (by simpa only [← he'] using hs) hL
    (by rw [← he']; linarith) (by rw [← he']; linarith)
    (by simpa only [← he'] using hpos)
  rw [← he'] at hgeom
  have hpbig : (9/25 : ℝ)*t < Real.log (v 3) := by linarith [hgeom.1]
  have hi (i : Fin 3) : ∃ k : Fin M,
      a+(k : ℕ)*b < Real.log (w i) ∧ Real.log (w i) ≤ a+((k : ℕ)+1)*b :=
    exists_grid_index M (hsmall (w i) (hdiv i.castSucc)) ((hlog i.castSucc).trans (hThi.trans hcover))
  choose k hk using hi
  have htuple : w ∈ Fintype.piFinset (fun i => logPrimes (gridLo a b k i) b) := by
    apply Fintype.mem_piFinset.mpr
    intro i
    exact (mem_logPrimes_iff _ _ _).mpr ⟨hv i.castSucc,(hk i).1,by
      simpa only [gridLo,add_mul,one_mul,add_assoc] using (hk i).2⟩
  have hksum : (∑ i, (gridLo a b k i+b)) ≤ (∑ i, Real.log (w i))+3*b := by
    calc
      _ ≤ ∑ i, (Real.log (w i)+b) := Finset.sum_le_sum
        (fun i _ => by change a+(k i : ℕ)*b+b ≤ Real.log (w i)+b; linarith [(hk i).1])
      _ = _ := by simp [Finset.sum_add_distrib]
  have hTsum : Real.log n = (∑ i, Real.log (w i))+Real.log (v 3) := by
    rw [← hew,Nat.cast_mul,Real.log_mul]
    · rw [Nat.cast_prod,Real.log_prod]
      exact fun i _ => by exact_mod_cast (hv i.castSucc).ne_zero
    · exact_mod_cast (show (∏ i, w i : ℕ) ≠ 0 from
        Finset.prod_ne_zero_iff.mpr (fun i _ => (hv i.castSucc).ne_zero))
    · exact_mod_cast (hv 3).ne_zero
  have hkmono {i j : Fin 3} (hij : w i < w j) : k i ≤ k j := by
    by_contra hn
    have hji : ((k j : ℕ) : ℝ)+1 ≤ (k i : ℕ) := by
      exact_mod_cast (show (k j : ℕ)+1 ≤ (k i : ℕ) by omega)
    have hscale := mul_le_mul_of_nonneg_right hji hb.le
    have hlogs : Real.log (w i) < Real.log (w j) := Real.log_lt_log (by exact_mod_cast (hv i.castSucc).pos)
      (by exact_mod_cast hij)
    nlinarith [(hk i).1,(hk j).2]
  have hkcover : k ∈ gridCover M a b t := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,hkmono ho.1,hkmono ho.2,by linarith⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨k,hkcover,?_⟩
  have hm := mem_boundaryCell S L t h y (gridLo a b k) (fun _ => b)
    htuple ho (hv 3) hlast (by simpa only [hew] using hnS)
    (by simpa only [hew] using hTlo) (by simpa only [hew] using hThi)
    (by simpa only [hew] using hpos) (by simpa only [hew] using hcos)
  simpa only [hew] using hm


/-- Every grid cell retains only nonpositive atoms from the original
support. This remains true on both ordering boundaries. -/
theorem grid_atom_nonpos (S A : Finset ℕ) (N M : ℕ) (L t h y a b : ℝ)
    {n : ℕ} (hn : n ∈ (gridCover M a b t).biUnion
      (fun v => boundaryCell S L t h y (gridLo a b v) (fun _ => b))) :
    (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤ 0 := by
  obtain ⟨v,_hv,hn⟩ := Finset.mem_biUnion.mp hn
  exact boundaryCell_atom_nonpos S A N L t h y (gridLo a b v) (fun _ => b) hn

/-- The ENTIRE adverse four-prime population above the chosen prime-log
threshold has an explicit finite-grid debit. All order faces and the true
product phase are retained. This does not claim that the debit decays or
that a numerical supply comparison has been paid. -/
theorem eventually_adverse_population_floor {h α β : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (M : ℕ) (L t y a b : ℝ),
      α*N ≤ a → β*N ≤ b → α*N ≤ t/4 → h ≤ t/100 → b ≤ t/100 →
      0 < L → L ≤ t → 2*(t+h) ≤ 3*L → (17/25 : ℝ)*(t+h) ≤ L → t+h ≤ a+M*b →
      -(∑ v ∈ gridCover M a b t, cellDebit N L t h y (gridLo a b v) (fun _ => b)) ≤
        (∑ n ∈ adversePopulation S L t h y a,
          residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  filter_upwards [eventually_boundary_cell_floor hh hhu hα hβ,
    eventually_ge_atTop (1 : ℕ)]
    with N hN hn S A M L t y a b ha hb hmin hhT hbT hL hLt hTc hcut hcover
  let I := gridCover M a b t
  let D := fun v : Fin 3 → Fin M => boundaryCell S L t h y (gridLo a b v) (fun _ => b)
  let U := I.biUnion D
  let Q := adversePopulation S L t h y a
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hb0 : 0 < b := by
    have hnR : (1 : ℝ) ≤ N := by exact_mod_cast hn
    nlinarith
  have hbound (v : Fin 3 → Fin M) (hv : v ∈ I) :
      -cellDebit N L t h y (gridLo a b v) (fun _ => b) ≤ (∑ n ∈ D v, f n).re := by
    exact hN (gridLo a b v) (fun _ => b) A S L t y
      (fun i => ha.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hb0.le)))
      (fun _ => hb) hL hLt hTc (hmin.trans (Finset.mem_filter.mp hv).2.2.2)
  have hsum := Finset.sum_le_sum hbound
  have hdup := ZetaRieszJointPrimeCells.sum_cells_le_union_of_nonpos I D (fun n => (f n).re)
    (fun v _ n hn' => boundaryCell_atom_nonpos S A N L t h y (gridLo a b v) (fun _ => b) hn')
  simp only [← Complex.re_sum,Finset.sum_neg_distrib] at hsum
  simp only [← Complex.re_sum] at hdup
  have hQU : Q ⊆ U := adversePopulation_subset_grid S M hhT hb0 hbT hL hLt hcut hcover
  have hrest : (∑ n ∈ U\Q, f n).re ≤ 0 := by
    rw [Complex.re_sum]
    exact Finset.sum_nonpos (fun n hn' => grid_atom_nonpos S A N M L t h y a b
      (Finset.mem_sdiff.mp hn').1)
  have he := congrArg Complex.re (Finset.sum_sdiff (f := f) hQU)
  rw [Complex.add_re] at he
  exact (hsum.trans hdup).trans (by linarith)

/-- The grid debit is an independent signed floor in the ORIGINAL core.
Every adverse four-prime label above the threshold in this phase interval
is charged; the full remaining carrier stays signed. -/
theorem eventually_core_population_floor {u h α β : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ j : ℕ in atTop, ∀ (M : ℕ) (t y a b : ℝ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let Q := adversePopulation S L t h y a
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      α*N ≤ a → β*N ≤ b → α*N ≤ t/4 → h ≤ t/100 → b ≤ t/100 → t+h ≤ a+M*b →
      (∑ n ∈ S\Q, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
        (∑ v ∈ gridCover M a b t, cellDebit N L t h y (gridLo a b v) (fun _ => b)) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (eventually_adverse_population_floor hh hhu hα hβ),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_core_length_chamber hu hU (h := h)),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszFivePrimePairSupply.eventually_core_cutoff_ratio hu.le hU)]
    with j hN hch hratio M t y a b
  dsimp only
  intro htlo hthi ha hb hmin hhT hbT hcover
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let Q := adversePopulation S L t h y a
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hch' := hch t htlo hthi
  have ht : 0 < t+h := by
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hcut := (le_div_iff₀ ht).mp (hratio (t+h) (by linarith) hthi).1
  have hbound := hN S A M L t y a b ha hb hmin hhT hbT
    (SquarefreeVaughanLogSource.length_pos u N) hch'.1 hch'.2 (by linarith) hcover
  have hQS : Q ⊆ S := Finset.filter_subset _ _
  have he := congrArg Complex.re (Finset.sum_sdiff (f := f) hQS)
  rw [Complex.add_re] at he
  change _ ≤ (∑ n ∈ S, f n).re
  linarith


/-- A fixed finite grid works for the exact exponential prime threshold
already available after head compensation. No unevaluated cell-geometry
premise remains. The debit is still explicit and must be paid jointly by
favorable populations; this is not a decay theorem for the adverse part. -/
theorem eventually_exponential_threshold_floor {u h δ : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128) :
    ∃ M : ℕ, ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let a := δ*N
      let b := (δ/1000)*N
      let Q := adversePopulation S L t h y a
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (∑ n ∈ S\Q, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
        (∑ v ∈ gridCover M a b t, cellDebit N L t h y (gridLo a b v) (fun _ => b)) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  let M := ⌈3000/δ⌉₊
  have hM : (3 : ℝ) ≤ M*(δ/1000) := by
    have he := Nat.le_ceil (3000/δ)
    have hmul := mul_le_mul_of_nonneg_right he hδ.le
    rw [div_mul_cancel₀ _ hδ.ne'] at hmul
    dsimp [M]
    nlinarith
  refine ⟨M,?_⟩
  filter_upwards [eventually_core_population_floor hu hU hh hhu hδ
    (by positivity : (0 : ℝ) < δ/1000),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hN hj t y
  dsimp only
  intro htlo hthi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hj
  have hn0 : (0 : ℝ) ≤ N := by positivity
  have hdN := mul_le_mul_of_nonneg_right hδu hn0
  have hδN : 0 ≤ δ*N := mul_nonneg hδ.le hn0
  have hcover := mul_le_mul_of_nonneg_right hM hn0
  apply hN M t y (δ*N) ((δ/1000)*N) htlo hthi le_rfl le_rfl
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

end
end RiemannGaussian.ZetaRieszFourBoundaryCover
