/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFourBoundaryCover

/-!
# A numerical debit for adverse four-prime ordering cells

The positive four-prime coefficient cancels the least-prime harmonic
singularity. On the largest-share cutoff 601/1000, its other three prime
logs stay uniformly positive. Counting the two repeated-index faces of
the literal grid gives a small relative debit before any source scaling.
All exterior terms and the full phase remain in the signed carrier.
-/

namespace RiemannGaussian.ZetaRieszFourOrderingBudget
noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic
open ZetaRieszCoupledWindow ZetaRieszMacroPrimeWindows ZetaRieszFourPrimeCells
open ZetaRieszFourBoundaryCover ZetaRieszPhaseBudget

/-- On the explicit geometric chamber the least-prime cap cancels its
harmonic denominator. Counting and all remaining denominators cost less
than 800 per unit three-dimensional grid volume. -/
theorem cell_angular_le {L t h b : ℝ} {lo : Fin 3 → ℝ}
    (ht : 0 < t) (hb : 0 < b) (hhT : h ≤ t/100000)
    (hL : (17/25 : ℝ)*t ≤ L) (hr : 1000*b ≤ lo 0)
    (ha : t/25 ≤ lo 1) (hq : (13/100 : ℝ)*t ≤ lo 2)
    (hp : (9/25 : ℝ)*t ≤ t-∑ i, (lo i+b)) :
    (501/500 : ℝ)*((t+h)/L)*boxCap L t h lo (fun i => lo i+b) /
        (t-∑ i, (lo i+b))*(∏ i, b/lo i) ≤ 800*(b/t)^3 := by
  have hL0 : 0 < L := by linarith
  have hr0 : 0 < lo 0 := by linarith
  have ha0 : 0 < lo 1 := by linarith
  have hq0 : 0 < lo 2 := by linarith
  have hp0 : 0 < t-∑ i, (lo i+b) := by linarith
  have hc : boxCap L t h lo (fun i => lo i+b) ≤ (1001/1000 : ℝ)*lo 0 := by
    have he : boxCap L t h lo (fun i => lo i+b) ≤ lo 0+b := min_le_left _ _
    linarith
  have hc0 : 0 ≤ boxCap L t h lo (fun i => lo i+b) := boxCap_nonneg _ _ _ (by linarith)
  have hratio : (t+h)/L ≤ (100001/100000 : ℝ)*(25/17) := by
    apply (div_le_iff₀ hL0).mpr
    nlinarith
  have hcap : boxCap L t h lo (fun i => lo i+b)/lo 0 ≤ (1001/1000 : ℝ) :=
    (div_le_iff₀ hr0).mpr hc
  have hden : ((9/25 : ℝ)*t)*(t/25)*((13/100 : ℝ)*t) ≤
      (t-∑ i, (lo i+b))*(lo 1)*(lo 2) := by gcongr
  have hkernel : b^3/((t-∑ i, (lo i+b))*(lo 1)*(lo 2)) ≤
      b^3/(((9/25 : ℝ)*t)*(t/25)*((13/100 : ℝ)*t)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  calc
    _ = (501/500 : ℝ)*((t+h)/L)*(boxCap L t h lo (fun i => lo i+b)/lo 0)*
        (b^3/((t-∑ i, (lo i+b))*(lo 1)*(lo 2))) := by
      rw [Fin.prod_univ_three]
      field_simp
    _ ≤ (501/500 : ℝ)*((100001/100000)*(25/17))*(1001/1000)*
        (b^3/(((9/25 : ℝ)*t)*(t/25)*((13/100 : ℝ)*t))) := by
      apply mul_le_mul _ hkernel (by positivity) (by norm_num)
      apply mul_le_mul _ hcap (div_nonneg hc0 hr0.le) (by norm_num)
      exact mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ = (1285912859/1632000 : ℝ)*(b/t)^3 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-- The preceding numerical budget is for the original finite-cell debit,
including its full negative-cosine envelope and radial factorial kernel. -/
theorem cellDebit_le {N : ℕ} {L t h y b : ℝ} {lo : Fin 3 → ℝ}
    (ht : 0 < t) (hb : 0 < b) (hh : 0 ≤ h) (hhT : h ≤ t/100000)
    (hL : (17/25 : ℝ)*t ≤ L) (hr : 1000*b ≤ lo 0)
    (ha : t/25 ≤ lo 1) (hq : (13/100 : ℝ)*t ≤ lo 2)
    (hp : (9/25 : ℝ)*t ≤ t-∑ i, (lo i+b)) :
    cellDebit N L t h y lo (fun _ => b) ≤
      800*(b/t)^3*(Real.exp (-t/2)*(t+h)^N/N.factorial)*
        (max 0 (-Real.cos (y*t))+|y| * h)*h := by
  have he := mul_le_mul_of_nonneg_right (cell_angular_le ht hb hhT hL hr ha hq hp)
    (show 0 ≤ (Real.exp (-t/2)*(t+h)^N/N.factorial)*
      (max 0 (-Real.cos (y*t))+|y| * h)*h by positivity)
  dsimp only [cellDebit]
  convert he using 1 <;> first | rfl | ring


/-- The angular certificate's exact largest-share restriction, retained
as a literal mask. Its exterior remains in the signed core rest. -/
def clippedSupport (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ ∀ p ∈ n.primeFactors,
    Real.log p ≤ (601/1000 : ℝ)*Real.log n)

/-- An actual adverse label in a clipped cell forces every denominator
needed for the numerical cell bound, and a uniform upper endpoint for the
cofactor grid. Empty cells are never charged by the boundary budget. -/
theorem active_cell_geometry (S : Finset ℕ) {L t h y b : ℝ} {lo : Fin 3 → ℝ}
    (hhb : h ≤ b) (hbT : b ≤ t/249600)
    (hL : (693/1015 : ℝ)*t ≤ L) (hLt : L ≤ t)
    (hne : (boundaryCell (clippedSupport S) L t h y lo (fun _ => b)).Nonempty) :
    t/25 ≤ lo 1 ∧ (13/100 : ℝ)*t ≤ lo 2 ∧
      (9/25 : ℝ)*t ≤ t-∑ i, (lo i+b) ∧ lo 2 < t/3 := by
  obtain ⟨n,hn⟩ := hne
  obtain ⟨m,hm,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have howner := (Finset.mem_filter.mp hp).2
  have hp' := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
  have hsel := hp'.2
  have hclip := (Finset.mem_filter.mp hsel.1).2
  have hpB := logPrimes_bounds hp'.1
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hm
  have hw' := Finset.mem_filter.mp hw
  have hb (i : Fin 3) := logPrimes_bounds (Fintype.mem_piFinset.mp hw'.1 i)
  have hm0 : (∏ i, w i : ℕ) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (hb i).1.ne_zero)
  have hqp : w 2 < p := howner (w 2)
    (Nat.mem_primeFactors.mpr ⟨(hb 2).1,Finset.dvd_prod_of_mem _ (Finset.mem_univ 2),hm0⟩)
  have he : (∏ i, w i)*p = p*(w 2*(w 1*w 0)) := by rw [Fin.prod_univ_three]; ring
  have hT := product_log_bounds hm0 hp'.1
  have hL0 : 0 < L := by linarith
  have hg := ZetaRieszOrderedCapacity.positive_four_geometry hpB.1 (hb 2).1 (hb 1).1 (hb 0).1
    hw'.2.1 hw'.2.2 hqp (by simpa only [← he] using hclip.1) hL0
    (by rw [← he]; linarith [hT.2.1]) (by rw [← he]; linarith [hT.2.2])
    (by simpa only [← he] using hsel.2.1)
  rw [← he] at hg
  have hP := hclip.2 p (Nat.mem_primeFactors.mpr
    ⟨hpB.1,Nat.dvd_mul_left _ _,mul_ne_zero hm0 hpB.1.ne_zero⟩)
  have hl : Real.log ((∏ i, w i)*p : ℕ) =
      (∑ i, Real.log (w i))+Real.log p := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hm0) (by exact_mod_cast hpB.1.ne_zero),
      Nat.cast_prod,Real.log_prod (fun i _ => by exact_mod_cast (hb i).1.ne_zero)]
  have hra : Real.log (w 0) ≤ Real.log (w 1) :=
    Real.log_le_log (by exact_mod_cast (hb 0).1.pos) (by exact_mod_cast hw'.2.1.le)
  have haq : Real.log (w 1) ≤ Real.log (w 2) :=
    Real.log_le_log (by exact_mod_cast (hb 1).1.pos) (by exact_mod_cast hw'.2.2.le)
  have hb0 := (hb 0).2
  have hb1 := (hb 1).2
  have hb2 := (hb 2).2
  simp only [Fin.sum_univ_three] at hl ⊢
  refine ⟨?_,?_,?_,?_⟩ <;> linarith [hg.1,hg.2.1,hg.2.2.1,hT.2.1,hT.2.2]


/-- Repeated-index ordering cells have only two free coordinates. Their
number is at most twice the square of the actual cofactor index range,
independently of the much larger ambient grid. -/
theorem repeated_index_card {M J : ℕ} (I : Finset (Fin 3 → Fin M))
    (hI : ∀ v ∈ I, v 0 ≤ v 1 ∧ v 1 ≤ v 2 ∧ (v 2 : ℕ) < J ∧
      (v 0 = v 1 ∨ v 1 = v 2)) : I.card ≤ 2*J^2 := by
  let P := (Finset.range J).product (Finset.range J)
  let f : ℕ × ℕ → Fin 3 → ℕ := fun v => ![v.1,v.1,v.2]
  let g : ℕ × ℕ → Fin 3 → ℕ := fun v => ![v.1,v.2,v.2]
  let T := P.image f ∪ P.image g
  have hmap : Set.MapsTo (fun v : Fin 3 → Fin M => fun i => (v i : ℕ)) I T := by
    intro v hv
    obtain ⟨h01,h12,h2,hface⟩ := hI v hv
    have h0 : (v 0 : ℕ) < J := by omega
    have h1 : (v 1 : ℕ) < J := by omega
    rcases hface with hf | hf
    · apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨((v 1 : ℕ),(v 2 : ℕ)),
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr h1,Finset.mem_range.mpr h2⟩,?_⟩
      ext i
      fin_cases i <;> simp [f,hf]
    · apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨((v 0 : ℕ),(v 1 : ℕ)),
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr h0,Finset.mem_range.mpr h1⟩,?_⟩
      ext i
      fin_cases i <;> simp [g,hf]
  have hc : I.card ≤ T.card := Finset.card_le_card_of_injOn _ hmap (by
    intro v _ w _ he
    funext i
    exact Fin.ext (congrFun he i))
  have hT := (Finset.card_union_le (P.image f) (P.image g)).trans
    (add_le_add (Finset.card_image_le) (Finset.card_image_le))
  have hP : P.card = J^2 := by simp [P,pow_two]
  dsimp only [T] at hc
  rw [hP] at hT
  omega

/-- Exact boundary cells of the clipped literal grid. An empty adverse
population spends no debit; every nonempty repeated-index cell is retained. -/
def edgeIndices (S : Finset ℕ) (M : ℕ) (L t h y a b : ℝ) : Finset (Fin 3 → Fin M) :=
  (gridCover M a b t).filter (fun v => (v 0 = v 1 ∨ v 1 = v 2) ∧
    (boundaryCell (clippedSupport S) L t h y (gridLo a b v) (fun _ => b)).Nonempty)

/-- Ordering-boundary index count uses the actual upper cofactor share,
not the ambient grid size, and retains the largest-share cutoff. -/
theorem edgeIndices_card (S : Finset ℕ) (M : ℕ) {L t h y a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hhb : h ≤ b) (hbT : b ≤ t/249600)
    (hL : (693/1015 : ℝ)*t ≤ L) (hLt : L ≤ t) :
    (edgeIndices S M L t h y a b).card ≤ 2*(⌈t/(3*b)⌉₊)^2 := by
  apply repeated_index_card
  intro v hv
  have hv' := Finset.mem_filter.mp hv
  have hgrid := (Finset.mem_filter.mp hv'.1).2
  have hg := active_cell_geometry S hhb hbT hL hLt hv'.2.2
  refine ⟨hgrid.1,hgrid.2.1,?_,hv'.2.1⟩
  apply Nat.lt_ceil.mpr
  apply (lt_div_iff₀ (show (0 : ℝ) < 3*b by positivity)).mpr
  dsimp [gridLo] at hg
  nlinarith [hg.2.2.2]

/-- The two-dimensional face count and cubic cell volume leave a linear
mesh cost. At the literal grid width it is strictly below 1/1250. -/
theorem numerical_face_budget {t b : ℝ} (ht : 0 < t) (hb : 0 < b)
    (hbT : b ≤ t/249600) :
    (2*(⌈t/(3*b)⌉₊ : ℝ)^2)*(800*(b/t)^3) ≤ 1/1250 := by
  have hx : 0 ≤ t/(3*b) := by positivity
  have hceil := (Nat.ceil_lt_add_one hx).le
  have hw0 : 0 ≤ b/t := by positivity
  have hw : b/t ≤ (1/249600 : ℝ) := (div_le_iff₀ ht).mpr (by linarith)
  have hscaled : (⌈t/(3*b)⌉₊ : ℝ)*(b/t) ≤ 1/3+b/t := by
    have h := mul_le_mul_of_nonneg_right hceil hw0
    convert h using 1 <;> first | rfl | field_simp
  calc
    _ = 1600*((⌈t/(3*b)⌉₊ : ℝ)*(b/t))^2*(b/t) := by ring
    _ ≤ 1600*(1/3+b/t)^2*(b/t) := by gcongr
    _ ≤ 1600*(1/3+(1/249600 : ℝ))^2*(1/249600) := by gcongr
    _ ≤ _ := by norm_num


/-- The aggregate debit of every nonempty ordering-boundary cell is at
most 1/1250 of the common original radial/phase factor. The estimate is
uniform in the grid size, finite support, allocation and moment order. -/
theorem sum_edge_debit_le (S : Finset ℕ) (N M : ℕ) {L t h y a b : ℝ}
    (ht : 0 < t) (hb : 0 < b) (hh : 0 ≤ h) (hhb : h ≤ b)
    (hbT : b ≤ t/249600) (ha : 1000*b ≤ a)
    (hL : (693/1015 : ℝ)*t ≤ L) (hLt : L ≤ t) :
    (∑ v ∈ edgeIndices S M L t h y a b,
      cellDebit N L t h y (gridLo a b v) (fun _ => b)) ≤
      (1/1250 : ℝ)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*
        (max 0 (-Real.cos (y*t))+|y| * h)*h := by
  let I := edgeIndices S M L t h y a b
  let E := (Real.exp (-t/2)*(t+h)^N/N.factorial)*
    (max 0 (-Real.cos (y*t))+|y| * h)*h
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have ha0 : 0 ≤ a := by linarith
  have hcell (v : Fin 3 → Fin M) (hv : v ∈ I) :
      cellDebit N L t h y (gridLo a b v) (fun _ => b) ≤ 800*(b/t)^3*E := by
    have hg := active_cell_geometry S hhb hbT hL hLt (Finset.mem_filter.mp hv).2.2
    have hr : 1000*b ≤ gridLo a b v 0 :=
      ha.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hb.le))
    simpa only [E,mul_assoc] using cellDebit_le (N := N) (y := y) ht hb hh
      (by linarith) (by linarith) hr hg.1 hg.2.1 hg.2.2.1
  have hs := Finset.sum_le_sum hcell
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hc : (I.card : ℝ) ≤ 2*(⌈t/(3*b)⌉₊ : ℝ)^2 := by
    exact_mod_cast edgeIndices_card S M ha0 hb hhb hbT hL hLt
  have hc' := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ 800*(b/t)^3*E by positivity)
  have hn := mul_le_mul_of_nonneg_right (numerical_face_budget ht hb hbT) hE
  have htotal := (hs.trans hc').trans (by simpa only [mul_assoc] using hn)
  simpa only [E,mul_assoc] using htotal

/-- The literal adverse ordering-boundary population. All other labels,
including the largest-share exterior, remain in the signed complement. -/
def edgePopulation (S : Finset ℕ) (M : ℕ) (L t h y a b : ℝ) : Finset ℕ :=
  (edgeIndices S M L t h y a b).biUnion
    (fun v => boundaryCell (clippedSupport S) L t h y (gridLo a b v) (fun _ => b))

/-- The charged boundary population stays inside the original support. -/
theorem edgePopulation_subset (S : Finset ℕ) (M : ℕ) (L t h y a b : ℝ) :
    edgePopulation S M L t h y a b ⊆ S := by
  apply Finset.biUnion_subset.mpr
  intro v _hv
  exact (boundaryCell_subset _ _ _ _ _ _ _).trans (Finset.filter_subset _ _)

/-- The numerical face budget controls the actual retained signed prime
sum, not only a continuum slab. Population estimates keep exact ordering,
coefficient, phase, allocation and the largest-share cutoff. -/
theorem eventually_edge_population_floor {h α β : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (M : ℕ) (L t y a b : ℝ),
      α*N ≤ a → β*N ≤ b → α*N ≤ t/4 → 0 < t → h ≤ b →
      b ≤ t/249600 → 1000*b ≤ a → (693/1015 : ℝ)*t ≤ L → L ≤ t →
      2*(t+h) ≤ 3*L →
      -((1/1250 : ℝ)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*
        (max 0 (-Real.cos (y*t))+|y| * h)*h) ≤
        (∑ n ∈ edgePopulation S M L t h y a b,
          residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  filter_upwards [eventually_boundary_cell_floor hh hhu hα hβ,
    eventually_ge_atTop (1 : ℕ)]
    with N hN hn S A M L t y a b ha hb hmin ht hhb hbT hba hL hLt hTc
  let I := edgeIndices S M L t h y a b
  let D := fun v : Fin 3 → Fin M =>
    boundaryCell (clippedSupport S) L t h y (gridLo a b v) (fun _ => b)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hb0 : 0 < b := by
    have hnR : (1 : ℝ) ≤ N := by exact_mod_cast hn
    nlinarith
  have hcell (v : Fin 3 → Fin M) (hv : v ∈ I) :
      -cellDebit N L t h y (gridLo a b v) (fun _ => b) ≤ (∑ n ∈ D v, f n).re := by
    have hgrid := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
    exact hN (gridLo a b v) (fun _ => b) A (clippedSupport S) L t y
      (fun i => ha.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hb0.le)))
      (fun _ => hb) (by linarith) hLt hTc (hmin.trans hgrid.2.2)
  have hs := Finset.sum_le_sum hcell
  have hu := ZetaRieszJointPrimeCells.sum_cells_le_union_of_nonpos I D (fun n => (f n).re)
    (fun v _ n hn' => boundaryCell_atom_nonpos (clippedSupport S) A N L t h y
      (gridLo a b v) (fun _ => b) hn')
  simp only [← Complex.re_sum,Finset.sum_neg_distrib] at hs
  simp only [← Complex.re_sum] at hu
  exact (neg_le_neg (sum_edge_debit_le S N M ht hb0 hh.le hhb hbT hba hL hLt)).trans
    (hs.trans hu)


/-- Outside the two repeated-index faces, the cofactor windows are
strictly separated. Thus the face budget covers every failure of the
interior-cell ordering condition, not an arbitrary selected subset. -/
theorem grid_ordered_or_edge (S : Finset ℕ) (M : ℕ) {L t h y a b : ℝ}
    (hb : 0 ≤ b) {v : Fin 3 → Fin M} (hv : v ∈ gridCover M a b t)
    (hne : (boundaryCell (clippedSupport S) L t h y (gridLo a b v) (fun _ => b)).Nonempty) :
    (∀ i j, i < j → gridLo a b v i+b ≤ gridLo a b v j) ∨
      v ∈ edgeIndices S M L t h y a b := by
  by_cases hf : v 0 = v 1 ∨ v 1 = v 2
  · exact Or.inr (Finset.mem_filter.mpr ⟨hv,hf,hne⟩)
  left
  have hv' := (Finset.mem_filter.mp hv).2
  have h01 : v 0 < v 1 := lt_of_le_of_ne hv'.1 (by tauto)
  have h12 : v 1 < v 2 := lt_of_le_of_ne hv'.2.1 (by tauto)
  have hm : StrictMono v := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · exact h01
    · exact h12
  intro i j hij
  have he : ((v i : ℕ) : ℝ)+1 ≤ (v j : ℕ) := by
    exact_mod_cast (show (v i : ℕ)+1 ≤ (v j : ℕ) from hm hij)
  have hmul := mul_le_mul_of_nonneg_right he hb
  dsimp [gridLo]
  linarith

/-- All ordering-boundary debits in the actual exponential-threshold grid
cost at most 1/1250 times the original common radial/phase factor. The
whole signed complement, including the largest-share exterior, remains.
This relative budget is intended for joint compensation, not separate
source-normalized decay of the boundary population. -/
theorem eventually_core_ordering_floor {u h δ : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128) :
    ∀ᶠ j : ℕ in atTop, ∀ (M : ℕ) (t y : ℝ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let D := edgePopulation S M L t h y (δ*N) ((δ/1000)*N)
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (∑ n ∈ S\D, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
        (1/1250 : ℝ)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (-Real.cos (y*t))+|y| * h)*h ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  have hβ : (0 : ℝ) < δ/1000 := by positivity
  have hlinear : ∀ᶠ N : ℕ in atTop, h ≤ (δ/1000)*N :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hβ).eventually_ge_atTop h
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_edge_population_floor hh hhu hδ hβ),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_core_length_chamber hu hU (h := h)),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszFivePrimePairSupply.eventually_core_cutoff_ratio hu.le hU),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hlinear,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hN hch hratio hwidth hj M t y
  dsimp only
  intro htlo hthi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let D := edgePopulation S M L t h y (δ*N) ((δ/1000)*N)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hj
  have ht : 0 < t := by nlinarith
  have hdN := mul_le_mul_of_nonneg_right hδu (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hch' := hch t htlo hthi
  have hcut := (le_div_iff₀ (show 0 < t+h by linarith)).mp
    (hratio (t+h) (by linarith) hthi).1
  have hf := hN S A M L t y (δ*N) ((δ/1000)*N) le_rfl le_rfl
    (by nlinarith) ht hwidth (by nlinarith) (by ring_nf; rfl)
    (by linarith) hch'.1 hch'.2
  have hDS : D ⊆ S := edgePopulation_subset S M L t h y _ _
  have he := congrArg Complex.re (Finset.sum_sdiff (f := f) hDS)
  rw [Complex.add_re] at he
  change _ ≤ (∑ n ∈ S, f n).re
  linarith


/-- The remaining grid cells have distinct increasing cofactor indices.
No arithmetic support is completed: the original boundaryCell selection
still applies inside every such cell. -/
def interiorIndices (M : ℕ) (a b t : ℝ) : Finset (Fin 3 → Fin M) :=
  (gridCover M a b t).filter (fun v => v 0 < v 1 ∧ v 1 < v 2)

/-- The full clipped adverse population costs the explicit interior-grid
debit plus the proved 1/1250 ordering allowance. This is a bound on the
actual signed population, including all ordering faces; it leaves only
the interior angular comparison to sharpen within this population. -/
theorem eventually_interior_plus_edge_floor {h α β : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (M : ℕ) (L t y a b : ℝ),
      α*N ≤ a → β*N ≤ b → α*N ≤ t/4 → 0 < t → h ≤ b →
      b ≤ t/249600 → 1000*b ≤ a → (693/1015 : ℝ)*(t+h) ≤ L → L ≤ t →
      2*(t+h) ≤ 3*L → t+h ≤ a+M*b →
      -(∑ v ∈ interiorIndices M a b t,
          cellDebit N L t h y (gridLo a b v) (fun _ => b))-
        (1/1250 : ℝ)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (-Real.cos (y*t))+|y| * h)*h ≤
      (∑ n ∈ adversePopulation (clippedSupport S) L t h y a,
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  filter_upwards [eventually_boundary_cell_floor hh hhu hα hβ,
    eventually_ge_atTop (1 : ℕ)]
    with N hN hn S A M L t y a b ha hb hmin ht hhb hbT hba hL hLt hTc hcover
  let I := interiorIndices M a b t
  let E := edgeIndices S M L t h y a b
  let D := fun v : Fin 3 → Fin M =>
    boundaryCell (clippedSupport S) L t h y (gridLo a b v) (fun _ => b)
  let U := (I ∪ E).biUnion D
  let Q := adversePopulation (clippedSupport S) L t h y a
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hb0 : 0 < b := by
    have hnR : (1 : ℝ) ≤ N := by exact_mod_cast hn
    nlinarith
  have hsub : I ∪ E ⊆ gridCover M a b t := Finset.union_subset
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hbound (v : Fin 3 → Fin M) (hv : v ∈ I ∪ E) :
      -cellDebit N L t h y (gridLo a b v) (fun _ => b) ≤ (∑ n ∈ D v, f n).re :=
    hN (gridLo a b v) (fun _ => b) A (clippedSupport S) L t y
      (fun i => ha.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hb0.le)))
      (fun _ => hb) (by linarith) hLt hTc
      (hmin.trans (Finset.mem_filter.mp (hsub hv)).2.2.2)
  have hsum := Finset.sum_le_sum hbound
  have hdup := ZetaRieszJointPrimeCells.sum_cells_le_union_of_nonpos (I ∪ E) D (fun n => (f n).re)
    (fun v _ n hn' => boundaryCell_atom_nonpos _ A N L t h y (gridLo a b v) (fun _ => b) hn')
  simp only [← Complex.re_sum,Finset.sum_neg_distrib] at hsum
  simp only [← Complex.re_sum] at hdup
  have hQU : Q ⊆ U := by
    intro n hn'
    have hg := adversePopulation_subset_grid (clippedSupport S) M
      (by linarith) hb0 (by linarith) (by linarith) hLt (by linarith) hcover hn'
    obtain ⟨v,hv,hnv⟩ := Finset.mem_biUnion.mp hg
    refine Finset.mem_biUnion.mpr ⟨v,?_,hnv⟩
    by_cases hf : v 0 = v 1 ∨ v 1 = v 2
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv,hf,⟨n,hnv⟩⟩)
    · have hv' := (Finset.mem_filter.mp hv).2
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨hv,lt_of_le_of_ne hv'.1 (by tauto),lt_of_le_of_ne hv'.2.1 (by tauto)⟩)
  have hrest : (∑ n ∈ U\Q, f n).re ≤ 0 := by
    rw [Complex.re_sum]
    apply Finset.sum_nonpos
    intro n hn'
    obtain ⟨v,_hv,hnv⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hn').1
    exact boundaryCell_atom_nonpos _ A N L t h y (gridLo a b v) (fun _ => b) hnv
  have he := congrArg Complex.re (Finset.sum_sdiff (f := f) hQU)
  rw [Complex.add_re] at he
  have hdis : Disjoint I E := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    have hi := (Finset.mem_filter.mp hv).2
    have he' := (Finset.mem_filter.mp hv').2.1
    rcases he' with h | h
    · exact hi.1.ne h
    · exact hi.2.ne h
  rw [Finset.sum_union hdis] at hsum
  have hpay := sum_edge_debit_le S N M (y := y) ht hb0 hh.le hhb hbT hba (by linarith) hLt
  have hf := hsum.trans hdup
  change _ ≤ (∑ n ∈ Q, f n).re
  linarith


/-- The entire clipped four-prime debit above the already available
exponential threshold has a floor in the unchanged core: its interior
cell sum plus at most 1/1250 of the common radial/phase factor. Every
ordering face is included and every exterior term remains signed. -/
theorem eventually_core_interior_floor {u h δ : ℝ}
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
      let Q := adversePopulation (clippedSupport S) L t h y a
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (∑ n ∈ S\Q, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
        (∑ v ∈ interiorIndices M a b t, cellDebit N L t h y (gridLo a b v) (fun _ => b))-
        (1/1250 : ℝ)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (-Real.cos (y*t))+|y| * h)*h ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  let M := ⌈3000/δ⌉₊
  have hM : (3 : ℝ) ≤ M*(δ/1000) := by
    have he := Nat.le_ceil (3000/δ)
    have hmul := mul_le_mul_of_nonneg_right he hδ.le
    rw [div_mul_cancel₀ _ hδ.ne'] at hmul
    dsimp [M]
    nlinarith
  have hβ : (0 : ℝ) < δ/1000 := by positivity
  have hlinear : ∀ᶠ N : ℕ in atTop, h ≤ (δ/1000)*N :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hβ).eventually_ge_atTop h
  refine ⟨M,?_⟩
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_interior_plus_edge_floor hh hhu hδ hβ),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_core_length_chamber hu hU (h := h)),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszFivePrimePairSupply.eventually_core_cutoff_ratio hu.le hU),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hlinear,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hN hch hratio hwidth hj t y
  dsimp only
  intro htlo hthi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let Q := adversePopulation (clippedSupport S) L t h y (δ*N)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hj
  have ht : 0 < t := by nlinarith
  have hn0 : (0 : ℝ) ≤ N := by positivity
  have hdN := mul_le_mul_of_nonneg_right hδu hn0
  have hch' := hch t htlo hthi
  have hcut := (le_div_iff₀ (show 0 < t+h by linarith)).mp
    (hratio (t+h) (by linarith) hthi).1
  have hcover := mul_le_mul_of_nonneg_right hM hn0
  have hδN : 0 ≤ δ*N := mul_nonneg hδ.le hn0
  have hf := hN S A M L t y (δ*N) ((δ/1000)*N) le_rfl le_rfl
    (by nlinarith) ht hwidth (by nlinarith) (by ring_nf; rfl)
    hcut hch'.1 hch'.2 (by nlinarith)
  have hQS : Q ⊆ S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have he := congrArg Complex.re (Finset.sum_sdiff (f := f) hQS)
  rw [Complex.add_re] at he
  change _ ≤ (∑ n ∈ S, f n).re
  linarith


/-- Two percent of angular surplus suffices after the same one-percent
aggregate loss, radial factor 501/500 and full phase uncertainty. A positive
one-percent joint budget remains; three percent is not necessary. -/
theorem two_percent_phase_budget {D S ε : ℝ} (hD : 0 ≤ D)
    (hS : (102/100 : ℝ)*D ≤ S) (hε : 0 ≤ ε) (hεu : ε ≤ 1/10000) :
    (1/100 : ℝ)*D ≤ ∫ x in (-Real.pi)..Real.pi,
      (99/100 : ℝ)*S*max 0 (Real.cos x-ε)-
        (501/500 : ℝ)*D*(max 0 (Real.cos x)+ε) := by
  have hb := rational_phase_budgets hε hεu
  have hS0 : 0 ≤ S := (by positivity : (0 : ℝ) ≤ (102/100)*D).trans hS
  have hc₁ : Continuous (fun x : ℝ => max 0 (Real.cos x-ε)) :=
    continuous_const.max (Real.continuous_cos.sub continuous_const)
  have hc₂ : Continuous (fun x : ℝ => max 0 (Real.cos x)+ε) :=
    (continuous_const.max Real.continuous_cos).add continuous_const
  rw [intervalIntegral.integral_sub
    ((hc₁.const_mul ((99/100 : ℝ)*S)).intervalIntegrable _ _)
    ((hc₂.const_mul ((501/500 : ℝ)*D)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hl := mul_le_mul_of_nonneg_left hb.1
    (by positivity : (0 : ℝ) ≤ (99/100)*S)
  have hu := mul_le_mul_of_nonneg_left hb.2
    (by positivity : (0 : ℝ) ≤ (501/500)*D)
  nlinarith


/-- The sharper two-percent comparison keeps the varying original radial
weight and leaves a positive one-percent reserve before integration. -/
theorem weighted_two_percent_budget {D S ε V₀ : ℝ} {V : ℝ → ℝ}
    (hD : 0 ≤ D) (hS : (102/100 : ℝ)*D ≤ S)
    (hε : 0 ≤ ε) (hεu : ε ≤ 1/10000) (hV₀ : 0 ≤ V₀)
    (hVc : ContinuousOn V (Set.Icc (-Real.pi) Real.pi))
    (hV : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      V₀ ≤ V x ∧ V x ≤ (501/500 : ℝ)*V₀) :
    (1/100 : ℝ)*D*V₀ ≤ ∫ x in (-Real.pi)..Real.pi,
      V x*((99/100 : ℝ)*S*max 0 (Real.cos x-ε)-
        D*(max 0 (Real.cos x)+ε)) := by
  have hS0 : 0 ≤ S := (by positivity : (0 : ℝ) ≤ (102/100)*D).trans hS
  have hc₁ : Continuous (fun x : ℝ => max 0 (Real.cos x-ε)) :=
    continuous_const.max (Real.continuous_cos.sub continuous_const)
  have hc₂ : Continuous (fun x : ℝ => max 0 (Real.cos x)+ε) :=
    (continuous_const.max Real.continuous_cos).add continuous_const
  have ha : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hi := intervalIntegral.integral_mono_on (μ := volume) ha
    ((((hc₁.const_mul ((99/100 : ℝ)*S)).sub
      (hc₂.const_mul ((501/500 : ℝ)*D))).const_mul V₀).intervalIntegrable _ _)
    ((hVc.mul ((hc₁.const_mul ((99/100 : ℝ)*S)).sub
      (hc₂.const_mul D)).continuousOn).intervalIntegrable_of_Icc ha)
    (fun x hx => show V₀*((99/100 : ℝ)*S*max 0 (Real.cos x-ε)-
          (501/500 : ℝ)*D*(max 0 (Real.cos x)+ε)) ≤
        V x*((99/100 : ℝ)*S*max 0 (Real.cos x-ε)-
          D*(max 0 (Real.cos x)+ε)) by
      have h₁ := mul_le_mul_of_nonneg_right (hV x hx).1
        (show 0 ≤ (99/100 : ℝ)*S*max 0 (Real.cos x-ε) by positivity)
      have h₂ := mul_le_mul_of_nonneg_right (hV x hx).2
        (show 0 ≤ D*(max 0 (Real.cos x)+ε) by positivity)
      nlinarith)
  rw [intervalIntegral.integral_const_mul] at hi
  have hj := mul_le_mul_of_nonneg_left (two_percent_phase_budget hD hS hε hεu) hV₀
  simpa only [Pi.mul_apply, Pi.sub_apply, mul_comm, mul_left_comm, mul_assoc] using hj.trans hi


/-- On the unchanged core, two percent of angular surplus gives a
positive complete radial/phase-period comparison. The angular supply and
arithmetic transport premises remain explicit. -/
theorem original_two_percent_budget {N : ℕ} (hN : 0 < N) {b y D S ε : ℝ}
    (hy : 54 ≤ |y|) (hpeak : Real.cos (y*b) = -1)
    (hlo : (39/20 : ℝ)*N ≤ b-Real.pi/|y|)
    (hhi : b+Real.pi/|y| ≤ (203/100 : ℝ)*N)
    (hD : 0 < D) (hS : (102/100 : ℝ)*D ≤ S)
    (hε : 0 ≤ ε) (hεu : ε ≤ 1/10000) :
    0 < ∫ x in (-Real.pi)..Real.pi,
      (Real.exp (-(b+x/|y|)/2)*(b+x/|y|)^N/N.factorial)*
        ((99/100 : ℝ)*S*max 0 (-Real.cos (y*(b+x/|y|))-ε)-
          D*(max 0 (-Real.cos (y*(b+x/|y|)))+ε)) := by
  obtain ⟨V₀,hV₀,hV⟩ := radial_period_comparable hN hy hlo hhi
  have hy0 : y ≠ 0 := by intro he; simp only [he,abs_zero] at hy; linarith
  simp_rw [phase_at_negative_peak hy0 hpeak]
  have hc : Continuous (fun x : ℝ =>
      Real.exp (-(b+x/|y|)/2)*(b+x/|y|)^N/N.factorial) := by fun_prop
  have hh := weighted_two_percent_budget hD.le hS hε hεu hV₀.le hc.continuousOn hV
  exact (by positivity : (0 : ℝ) < (1/100)*D*V₀).trans_le hh


/-- The proposed first-bin supply leaves room for both the PROVED 1/1250
ordering cost and another 1/2000 angular approximation cost. This rational
inequality does not certify the proposed supply or its arithmetic transfer. -/
theorem first_bin_budget_room :
    (102/100 : ℝ)*(133011/1000000+1/1250+1/2000) ≤ 137044/1000000 := by norm_num

end
end RiemannGaussian.ZetaRieszFourOrderingBudget
