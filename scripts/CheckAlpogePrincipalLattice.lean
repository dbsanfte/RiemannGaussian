import RiemannGaussian.AlpogeLatticeImage
import CheckAlpogeLatticeLocalization

/-! # Full lattices for each member of a comparison family -/

namespace RiemannGaussian.AlpogeWindow
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions
open RiemannGaussian.AlpogeWindow.Localization

private theorem inLoc_smul {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module (𝓞 K) V] {v : HeightOneSpectrum (𝓞 K)} {A : Submodule (𝓞 K) V}
    {y : V} (h : InLoc v A y) (c : 𝓞 K) : InLoc v A (c • y) := by
  obtain ⟨s, hs, hsy⟩ := h
  exact ⟨s, hs, by rw [smul_comm]; exact A.smul_mem c hsy⟩

/-- The rational outputs of the level operator have a common denominator
at each place. No bound on its size or on the index of the image is needed. -/
private theorem level_image_denominator (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    ∃ c : 𝓞 D.what₂.LL, c ≠ 0 ∧ ∀ y, D.nuIn u y ∈ LT.Nlam D u w →
      InLoc (D.plEq w) (DV.MramL D u) (c • y) := by
  let A := ((D.fm u).lat 0).L
  let op := ((((D.mem u).A.T : ℂ) ^ LT.expT D u w) • (LT.Uprod D u 0 w) ^ D.R.m)
  obtain ⟨N, hN, houtput⟩ := AlpogeLattice.rational_outputs_fg ((D.fm u).emb 0)
    ((D.fm u).emb_inj 0) op A ((D.fm u).lat_good 0).2.1
  have hspan : Submodule.span D.what₂.LL (A : Set ((D.fm u).lat 0).V) = ⊤ :=
    ((D.fm u).lat_good 0).2.2
  obtain ⟨c, hc, hclear⟩ := exists_common_mul N A hN fun z _ =>
    Formalism.HN.sizeIneq_exists_mul_mem A z (by rw [hspan]; trivial)
  refine ⟨c, hc, fun y hy => ?_⟩
  obtain ⟨z, hz, he⟩ := hy
  obtain ⟨s, hs, hsz⟩ := D.locSpan u w z hz.1
  have he' : (D.fm u).emb 0 (s • D.nuIn u y) = op ((D.fm u).emb 0 (s • z)) := by
    rw [← algebraMap_smul D.what₂.LL s (D.nuIn u y), ← algebraMap_smul D.what₂.LL s z, LinearMap.map_smulₛₗ,
      LinearMap.map_smulₛₗ, map_smul, he]
  refine ⟨s, hs, ?_⟩
  change (D.nuIn u).restrictScalars (𝓞 D.what₂.LL) (s • (c • y)) ∈ A
  rw [map_smul, map_smul, smul_comm s c]
  exact hclear _ (houtput _ hsz _ he')

/-- The level places are finite. Clearing their denominators simultaneously
makes the entire defining lattice a submodule of the ramified lattice. -/
private theorem nuLat_fg {D : D7} {L : SizeData₂ D} (hNu : DV.NuDef D L)
    (hT : NuAtTDef D L) (u : D.what₂.Word) : (L.NuLat u).FG := by
  classical
  let p := (D.mem u).A.T
  obtain ⟨S, hS⟩ := J.finite_places_over (K := D.what₂.LL) p (D.mem u).A.T_prime
  choose d hd hloc using level_image_denominator D u
  let c : 𝓞 D.what₂.LL := ∏ v ∈ S, d (D.plEq.symm v)
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hd (D.plEq.symm v)
  apply Localization.fg_of_clearing (D.MramL_fg u) c hc
  intro y hy
  apply mem_of_locally
  intro v
  let w := D.plEq.symm v
  have hw : D.plEq w = v := D.plEq.apply_symm_apply v
  change InLoc v (DV.MramL D u) (c • y)
  rw [← hw]
  by_cases hp : D.what₂.places.resChar w = p
  · have hv : v ∈ S := (hS v).2 (by simpa only [← hp, ← hw] using J.resChar_mem D w)
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun v => d (D.plEq.symm v)) hv
    have hy' : D.nuIn u y ∈ LT.Nlam D u w :=
      (hT u w hp y).1 ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h),
        by rwa [one_smul]⟩
    change c = d w * k at hk
    rw [hk, mul_comm, mul_smul]
    exact inLoc_smul (hloc w y hy') k
  · exact inLoc_smul (locLe_zero (hNu.1 u w hp) y hy) c

/-- A common nonzero multiple of the ramified lattice lies in the defining
lattice. An ordinary place gives a denominator for each generator. -/
theorem principal_nu_commens {D : D7} {L : SizeData₂ D} (hNu : DV.NuDef D L)
    (hT : NuAtTDef D L) (u : D.what₂.Word) :
    (L.NuLat u).FG ∧ ∃ c : 𝓞 D.what₂.LL, c ≠ 0 ∧ ∀ y ∈ DV.MramL D u, c • y ∈ L.NuLat u := by
  obtain ⟨w, hw, hfree⟩ := Localization.exists_ordinary_place D u
  refine ⟨nuLat_fg hNu hT u, exists_common_mul _ _ (D.MramL_fg u) fun y hy => ?_⟩
  obtain ⟨s, hs, hsy⟩ := Localization.locLe_zero (hNu.2.1 u w hw (Or.inr hfree)).2 y hy
  exact ⟨s, fun hz => hs (hz ▸ Ideal.zero_mem _), hsy⟩

/-- Every sufficiently late member has a finitely generated, full-span
division lattice. The ordinary-place equality supplies the lower inclusion. -/
theorem principal_family_nuFull {ε : ℝ} (Fm : FamP ε) : NuFullF Fm := by
  refine ⟨Fm.x1 + 1, fun x hx i u => ?_⟩
  have hx' : Fm.x1 < x := by linarith
  let D := Fm.D x i
  let L := Fm.L x i
  have hNu := Fm.nuDef x hx' i
  have hdef := Fm.nprimeDef x hx' i u
  change (D.div.Nu u).L = Submodule.span (𝓞 D.what₂.LL) _ at hdef
  obtain ⟨hfg, s, hs, hclear⟩ := principal_nu_commens hNu (Fm.ex x hx' i).lat.atT u
  constructor
  · obtain ⟨d, hd, hI⟩ := (DV.Iu D L u).isFractional
    apply Localization.fg_of_clearing hfg d (nonZeroDivisors.ne_zero hd)
    change (D.div.Nu u).L ≤ (L.NuLat u).comap (LinearMap.lsmul (𝓞 D.what₂.LL) _ d)
    rw [hdef, Submodule.span_le]
    rintro _ ⟨a, ha, y, hy, rfl⟩
    obtain ⟨z, hz⟩ := hI a ha
    change d • (a • y) ∈ L.NuLat u
    rw [← smul_assoc, ← hz, algebraMap_smul]
    exact (L.NuLat u).smul_mem z hy
  · have hI : DV.Iu D L u ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ =>
      zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr (D.plEq v).ne_bot)
    obtain ⟨a, ha, haI⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI
    rw [eq_top_iff]
    intro y _
    let A := ((D.fm u).lat 0).L
    have hspan : Submodule.span D.what₂.LL (A : Set ((D.fm u).lat 0).V) = ⊤ :=
      ((D.fm u).lat_good 0).2.2
    obtain ⟨d, hd, hdy⟩ := Formalism.HN.sizeIneq_exists_mul_mem A (D.nuIn u y)
      (by rw [hspan]; trivial)
    have hin : d • y ∈ DV.MramL D u := by
      change (D.nuIn u).restrictScalars (𝓞 D.what₂.LL) (d • y) ∈ A
      rwa [map_smul]
    apply Localization.mem_span_of_multiple _ y (a * (s * d)) (mul_ne_zero ha (mul_ne_zero hs hd))
    rw [hdef, mul_smul, mul_smul, ← algebraMap_smul D.what₂.LL a]
    exact Submodule.subset_span ⟨_, haI, _, hclear _ hin, rfl⟩

/-- Sum of the image dimensions of the local norm operators on the unramified space. -/
noncomputable def levelNormRankSum (D : D7) (u : D.what₂.Word) : ℕ :=
  let A := (D.mem u).A
  ∑ v : A.vT, Module.finrank ℂ (LinearMap.range ((A.Nm v).domRestrict A.Mu0))

/-- Simultaneous rank-nullity for the norm operators. The ramified space is their
common kernel inside the unramified space. -/
theorem ramified_dimension_bound (D : D7) (u : D.what₂.Word) :
    D.duS u ≤ levelNormRankSum D u + (D.mem u).A.du := by
  classical
  let A := (D.mem u).A
  have := A.Mu0_fd
  let f := fun v : A.vT => (A.Nm v).domRestrict A.Mu0
  let F := LinearMap.pi fun v : A.vT => (f v).rangeRestrict
  have : FiniteDimensional ℂ A.Mram := Submodule.finiteDimensional_of_le (show A.Mram ≤ A.Mu0 from inf_le_left)
  let kernelMap : LinearMap.ker F →ₗ[ℂ] A.Mram :=
    (A.Mu0.subtype.comp (LinearMap.ker F).subtype).codRestrict A.Mram fun z => by
      refine ⟨z.val.property, (Submodule.mem_iInf _).2 fun v => ?_⟩
      exact congrArg (fun t : (f v).range => t.val) (congrFun (LinearMap.mem_ker.1 z.property) v)
  have hker : Function.Injective kernelMap := fun _ _ h =>
    Subtype.ext (Subtype.ext (congrArg (fun t : A.Mram => t.val) h))
  have hk := LinearMap.finrank_le_finrank_of_injective hker
  have hr : Module.finrank ℂ (LinearMap.range F) ≤ levelNormRankSum D u := by
    apply (Submodule.finrank_le _).trans_eq
    exact Module.finrank_pi_fintype ℂ
  exact F.finrank_range_add_finrank_ker.symm.le.trans (Nat.add_le_add hr hk)

/-- On a family, strict inequality of the rank sum with the unramified dimension
suffices for positive division rank at every level word. -/
theorem principal_family_muRank_of_norm_ranks {ε : ℝ} (Fm : FamP ε)
    (h : ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u,
      levelNormRankSum (Fm.D x i) u < (Fm.D x i).duS u) : J.MuRank Fm := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := principal_family_nuFull Fm
  refine ⟨max a b, fun x hx i u => ?_⟩
  have hl := ha x (le_of_max_le_left hx) i u
  have hd := ramified_dimension_bound (Fm.D x i) u
  change 0 < (Fm.D x i).div.d u
  rw [(hb x (le_of_max_le_right hx) i).rank u]
  omega

/-- The exponential frame estimate only needs the level prime to exceed the
scale b, uniformly in the index and the word. -/
def LevelPrimeGrowth {ε : ℝ} (Fm : FamP ε) : Prop :=
  ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u, (Fm.L x i).sc.b ≤ (((Fm.D x i).mem u).A.T : ℝ)

theorem levelPrimeGrowth_of_tuGe {ε : ℝ} {Fm : FamP ε}
    (ht : ∃ a : ℝ, ∀ x ≥ a, ∀ i : Fm.Ix x, (Fm.L x i).TuGe) : LevelPrimeGrowth Fm := by
  obtain ⟨a, ha⟩ := ht
  refine ⟨a, fun x hx i u => ?_⟩
  let D := Fm.D x i
  let L := Fm.L x i
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  calc L.sc.b = L.sc.b ^ (1 : ℝ) := (Real.rpow_one _).symm
       _ ≤ L.sc.b ^ ((D.R.m : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le
         (Real.one_le_exp (Real.rpow_nonneg (zero_lt_one.trans L.sc.one_lt_alt).le _)) (by linarith)
       _ ≤ _ := ha x hx i u

theorem levelPrimeGrowth_of_tuSize {ε : ℝ} {Fm : FamP ε} (ht : TuSize Fm) : LevelPrimeGrowth Fm := by
  obtain ⟨a, ha⟩ := ht
  exact levelPrimeGrowth_of_tuGe ⟨a, fun x hx i => (ha x hx i).1⟩

private theorem places_to_level_ratio {ε : ℝ} (Fm : FamP ε) (hε : 0 < ε) (ht : LevelPrimeGrowth Fm) :
    ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u,
      (2 : ℝ) * (Fm.D x i).R.f ≤ ((Fm.D x i).mem u).A.T * Real.exp (-(x ^ (ε / 8))) ^ 2 := by
  obtain ⟨a, ha⟩ := ht
  have hg := (tendsto_exp_mul_div_rpow_atTop (3 / ε) (1/2) (by norm_num)).comp (tendsto_rpow_atTop hε)
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 (hg.eventually_gt_atTop 4)
  obtain ⟨c, hc⟩ := Filter.eventually_atTop.1 ((tendsto_rpow_atTop (by positivity : 0 < 7*ε/8)).eventually_ge_atTop 4)
  refine ⟨max (max a b) (max c (Fm.x1 + 1)), fun x hx i u => ?_⟩
  let D := Fm.D x i
  let L := Fm.L x i
  have hlate : Fm.x1 < x := by linarith [le_of_max_le_right (le_of_max_le_right hx)]
  have hxL : L.sc.x = x := Fm.L_x x i hlate
  have hεL : L.sc.eps = ε := Fm.L_eps x i
  have hx1 : 1 ≤ x := hxL ▸ L.sc.one_lt_alt.le
  have hxp : 0 < x := zero_lt_one.trans_le hx1
  have hg' := hb x (le_of_max_le_right (le_of_max_le_left hx))
  change 4 < Real.exp (1/2 * x ^ ε) / ((x ^ ε) ^ (3 / ε)) at hg'
  rw [← Real.rpow_mul hxp.le, show ε * (3 / ε) = (3 : ℝ) by field_simp,
    show x ^ (3 : ℝ) = x ^ (3 : ℕ) by norm_cast] at hg'
  have hn : (D.R.n : ℝ) ≤ x ^ (3 : ℕ) := by
    have hn := ((Fm.sizes x hlate i).1).2.trans
      (Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (J.th_bounds L).2.2.2.1)
    change (D.R.n : ℝ) ≤ L.sc.x ^ (3 : ℝ) at hn
    rw [hxL] at hn
    exact_mod_cast hn
  have hbT := ha x (le_of_max_le_left (le_of_max_le_left hx)) i u
  change Real.exp (L.sc.x ^ L.sc.eps) ≤ _ at hbT
  rw [hxL, hεL] at hbT
  have h3 := (lt_div_iff₀ (pow_pos hxp 3)).mp hg'
  have hf : (D.R.f : ℝ) = 2 * D.R.n := by simp [Ranks.f]
  have htiny : 4 * x ^ (ε/8) ≤ x ^ ε := by
    have he : x ^ ε = x ^ (ε/8) * x ^ (7*ε/8) := by
      rw [← Real.rpow_add hxp]; congr 1; ring
    rw [he, mul_comm]
    exact mul_le_mul_of_nonneg_left (hc x (le_of_max_le_left (le_of_max_le_right hx)))
      (Real.rpow_nonneg hxp.le _)
  have hexp : Real.exp (1/2 * x ^ ε) ≤ Real.exp (x ^ ε) * Real.exp (-(x ^ (ε/8))) ^ 2 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [htiny])
  exact (show 2 * (D.R.f : ℝ) ≤ Real.exp (1/2 * x ^ ε) by linarith only [hf, hn, h3]).trans
    (hexp.trans (mul_le_mul_of_nonneg_right hbT (sq_nonneg _)))

/-- The level prime eventually exceeds the number of local norm operators by more than one. -/
theorem principal_level_gt_places {ε : ℝ} (Fm : FamP ε) (hε : 0 < ε) (ht : TuSize Fm) :
    ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u, (Fm.D x i).R.f + 1 < ((Fm.D x i).mem u).A.T := by
  obtain ⟨a, ha⟩ := places_to_level_ratio Fm hε (levelPrimeGrowth_of_tuSize ht)
  refine ⟨max a 1, fun x hx i u => ?_⟩
  let D := Fm.D x i
  have hf : 2 ≤ D.R.f := D.R.two_le_m.trans D.R.m_le_f
  have hp : 0 ≤ x ^ (ε/8) := Real.rpow_nonneg (zero_le_one.trans (le_of_max_le_right hx)) _
  have he : Real.exp (-(x ^ (ε/8))) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hp)
  have hratio := (ha x (le_of_max_le_left hx) i u).trans (mul_le_of_le_one_right
    (Nat.cast_nonneg _) (pow_le_one₀ (Real.exp_pos _).le he))
  have h2 : 2 * D.R.f ≤ (D.mem u).A.T := by exact_mod_cast hratio
  change D.R.f + 1 < (D.mem u).A.T
  omega

private theorem unramified_dim_pos {D : D7} {L : SizeData₂ D} {C0 : ℝ}
    (hC0 : 0 < C0) (hP : ChProviso_at L C0) (u : D.what₂.Word) : 0 < D.duS u := by
  by_contra! h
  have hl := (hP u).1
  simp [Nat.eq_zero_of_le_zero h] at hl
  exact (not_le_of_gt hC0) hl

/-- At each level place the norm image has at most a `1/(T-1)` share
of the unramified dimension. -/
def LocalNormRankBound (D : D7) (u : D.what₂.Word) : Prop :=
  let A := (D.mem u).A
  ∀ v : A.vT, (A.T - 1) * Module.finrank ℂ (LinearMap.range ((A.Nm v).domRestrict A.Mu0)) ≤ D.duS u

private theorem norm_rank_sum_le (D : D7) (u : D.what₂.Word) (h : LocalNormRankBound D u) :
    ((D.mem u).A.T - 1) * levelNormRankSum D u ≤ D.R.f * D.duS u := by
  unfold levelNormRankSum
  rw [Finset.mul_sum]
  exact (Finset.sum_le_sum fun v _ => h v).trans_eq (by simp [ColumnsAtT.card_vT])

/-- The ramified dimension misses at most the exponentially small fraction of the
unramified dimension used by the archive's frame comparison, uniformly in the word. -/
theorem principal_ramified_share_of_level_growth {ε : ℝ} (Fm : FamP ε) (hε : 0 < ε)
    (hTu : LevelPrimeGrowth Fm) (h : ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u, LocalNormRankBound (Fm.D x i) u) :
    ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u,
      ((Fm.D x i).duS u : ℝ) - (((Fm.D x i).mem u).A.du : ℝ) ≤
        Real.exp (-(x ^ (ε / 8))) ^ 2 * ((Fm.D x i).duS u : ℝ) := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := places_to_level_ratio Fm hε hTu
  refine ⟨max a b, fun x hx i u => ?_⟩
  let D := Fm.D x i
  let T := (D.mem u).A.T
  have hT : 2 ≤ T := (D.mem u).A.T_prime.two_le
  have hsum := norm_rank_sum_le D u (ha x (le_of_max_le_left hx) i u)
  have hsum' : T * levelNormRankSum D u ≤ 2 * (D.R.f * D.duS u) := by
    calc _ ≤ (2 * (T - 1)) * levelNormRankSum D u := Nat.mul_le_mul_right _ (by omega)
         _ = 2 * ((T - 1) * levelNormRankSum D u) := Nat.mul_assoc _ _ _
         _ ≤ _ := Nat.mul_le_mul_left _ hsum
  have hr : (T : ℝ) * levelNormRankSum D u ≤ 2 * ((D.R.f : ℝ) * D.duS u) := by exact_mod_cast hsum'
  have hdim : (D.duS u : ℝ) ≤ levelNormRankSum D u + ((D.mem u).A.du : ℝ) := by
    exact_mod_cast ramified_dimension_bound D u
  have hh := mul_le_mul_of_nonneg_right (hb x (le_of_max_le_right hx) i u) (Nat.cast_nonneg (D.duS u))
  have hcancel : (levelNormRankSum D u : ℝ) ≤ Real.exp (-(x ^ (ε/8))) ^ 2 * (D.duS u : ℝ) := by
    apply le_of_mul_le_mul_left _ (by exact_mod_cast (show 0 < T by omega) : (0 : ℝ) < T)
    linarith only [hr, hh]
  linarith only [hdim, hcancel]

theorem principal_ramified_share_of_local_norms {ε : ℝ} (Fm : FamP ε) (hε : 0 < ε)
    (hTu : TuSize Fm) (h : ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u, LocalNormRankBound (Fm.D x i) u) :
    ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u,
      ((Fm.D x i).duS u : ℝ) - (((Fm.D x i).mem u).A.du : ℝ) ≤
        Real.exp (-(x ^ (ε / 8))) ^ 2 * ((Fm.D x i).duS u : ℝ) :=
  principal_ramified_share_of_level_growth Fm hε (levelPrimeGrowth_of_tuSize hTu) h

/-- Bounding each separate norm image by one level share suffices. No formula for
the dimension of their common kernel is required of the family. -/
theorem principal_family_muRank_of_positive_dimension {ε : ℝ} (Fm : FamP ε) (hε : 0 < ε)
    (hTu : TuSize Fm) (hP : ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u, 0 < (Fm.D x i).duS u)
    (h : ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u, LocalNormRankBound (Fm.D x i) u) : J.MuRank Fm := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := principal_level_gt_places Fm hε hTu
  obtain ⟨c, hc⟩ := hP
  apply principal_family_muRank_of_norm_ranks Fm
  refine ⟨max (max a b) c, fun x hx i u => ?_⟩
  let D := Fm.D x i
  let A := (D.mem u).A
  have htf : D.R.f + 1 < A.T := hb x (le_of_max_le_right (le_of_max_le_left hx)) i u
  have hpos := hc x (le_of_max_le_right hx) i u
  have hsum := norm_rank_sum_le D u (ha x (le_of_max_le_left (le_of_max_le_left hx)) i u)
  have hlt : D.R.f * D.duS u < (A.T - 1) * D.duS u :=
    Nat.mul_lt_mul_of_pos_right (by omega) hpos
  exact Nat.lt_of_mul_lt_mul_left (hsum.trans_lt hlt)

theorem principal_family_muRank_of_local_norms {ε C0 : ℝ} (Fm : FamP ε) (hε : 0 < ε)
    (hC0 : 0 < C0) (hP : ChosenProviso Fm C0) (hTu : TuSize Fm)
    (h : ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u, LocalNormRankBound (Fm.D x i) u) : J.MuRank Fm := by
  obtain ⟨a, ha⟩ := hP
  exact principal_family_muRank_of_positive_dimension Fm hε hTu
    ⟨a, fun x hx i u => unramified_dim_pos hC0 (ha x hx i) u⟩ h

/-- The chosen lower bound and the ramified dimension formula give positive
rank on the same family. Its size bound gives a level prime strictly above two. -/
theorem principal_family_muRank_of_rank_line {ε C0 : ℝ} (Fm : FamP ε)
    (hC0 : 0 < C0) (hP : ChosenProviso Fm C0) (hTu : TuSize Fm)
    (hr : ∃ b : ℝ, ∀ x ≥ b, ∀ (i : Fm.Ix x) u,
      (((Fm.D x i).mem u).A.du : ℚ) = ((Fm.D x i).duS u : ℚ) *
        (1 - 1 / ((((Fm.D x i).mem u).A.T : ℚ) - 1)) ^ (Fm.D x i).R.f) :
    J.MuRank Fm := by
  obtain ⟨a, ha⟩ := principal_family_nuFull Fm
  obtain ⟨b, hb⟩ := hr
  obtain ⟨z, hz⟩ := hP
  obtain ⟨t, ht⟩ := hTu
  refine ⟨max (max a b) (max z t), fun x hx i u => ?_⟩
  let D := Fm.D x i
  let L := Fm.L x i
  have hx₁ := le_of_max_le_left hx
  have hx₂ := le_of_max_le_right hx
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hb₂ : 2 < L.sc.b := lt_of_lt_of_le (lt_trans (by norm_num) Real.exp_one_gt_d9)
    (Real.exp_le_exp.mpr hL)
  have hm : 2 ≤ (D.R.m : ℝ) := by exact_mod_cast D.R.two_le_m
  have hb₁ : L.sc.b ≤ L.sc.b ^ ((D.R.m : ℝ) / 2) := by
    calc
      L.sc.b = L.sc.b ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith only [hb₂]) (by linarith only [hm])
  have hT : 2 < (D.mem u).A.T := by
    exact_mod_cast hb₂.trans_le (hb₁.trans ((ht x (le_of_max_le_right hx₂) i).1 u))
  have hS := unramified_dim_pos hC0 (hz x (le_of_max_le_left hx₂) i) u
  have hT' : 2 < ((D.mem u).A.T : ℚ) := by exact_mod_cast hT
  have hfactor : (0 : ℚ) < 1 - 1 / (((D.mem u).A.T : ℚ) - 1) := by
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have hrank := (ha x (le_of_max_le_left hx₁) i).rank u
  rw [show ((D.div.Nu u).rank) = (D.mem u).A.du from hrank]
  have hdu : (0 : ℚ) < (D.mem u).A.du := by
    rw [hb x (le_of_max_le_right hx₁) i u]
    exact mul_pos (by exact_mod_cast hS) (pow_pos hfactor _)
  exact_mod_cast hdu

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeWindow.principal_family_nuFull,
      ``RiemannGaussian.AlpogeWindow.ramified_dimension_bound,
      ``RiemannGaussian.AlpogeWindow.principal_family_muRank_of_norm_ranks,
      ``RiemannGaussian.AlpogeWindow.principal_level_gt_places,
      ``RiemannGaussian.AlpogeWindow.principal_ramified_share_of_local_norms,
      ``RiemannGaussian.AlpogeWindow.principal_family_muRank_of_local_norms,
      ``RiemannGaussian.AlpogeWindow.principal_family_muRank_of_rank_line] do
    let axs ← collectAxioms decl
    for ax in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
    logInfo m!"{decl} depends on {axs}"
