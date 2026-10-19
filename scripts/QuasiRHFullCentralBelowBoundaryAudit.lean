/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHMomentBelowBoundaryAudit
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCollected
import OAI.NumberTheory.DirichletL.PrimeRows.CentralSupportedSplit
import OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorCollected
import OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeBins
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual complete central cube rows below the imported final wrapper

The original finite central rows, including all floor bins and zero calibration
rows, are estimated using an independent positive moment gap. No claim is
made for the physical probe/theta correlation or a new zero-free region.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical BigOperators Topology ContDiff SchwartzMap
open Filter Set
namespace OpenAIReview.FullCentralBelowBoundary
open OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
open HeckeInverseAmplification HeckeDetectorPhysicalSelection HeckeDetectorFiberPartition
open ProbeMellinBoundary ProbeFinalAssembly ProbeRaySlots
open ProbeFinalAssemblyCertifiedBands
open CenteredMomentDetectorPlainSlotProfile

/-- The original fine-data constructor also makes all central costs explicit. -/
theorem exists_prepared_data (Δ:ℝ)(hΔ:0<Δ)(mesh:ℝ→ℝ)
    (hmesh:∀t:ℝ,0<t→0<mesh t):
    ∃D:HighData Δ, (∀j,D.ell j≤mesh D.t/200) ∧
      2000*D.ε≤D.t ∧ 2000*D.e≤D.t ∧ ((D.N:ℝ)+8)*D.eps≤D.t:=by
  obtain ⟨t,ht,htΔ,ht1,_,_,hgeo,hdtop,ht3,hω,hωΔ,hhigh,hallow⟩ := exists_central_budget Δ hΔ
  obtain ⟨N,hN,ell,rmin,hr,hell,hsum,hbounds,_⟩ :=
    exists_physical_slot_lengths (1/200) (7/8) (min t (mesh t)) t (by norm_num) (by norm_num)
      (lt_min ht (hmesh t ht)) ht
  obtain ⟨allowance,ha,hbud⟩ := hallow N
  let small := min allowance (t/((N:ℝ)+2000))
  have hsmall : 0<small := lt_min ha (div_pos ht (by positivity))
  have hsa : small≤allowance := min_le_left _ _
  have hst : small≤t/((N:ℝ)+2000) := min_le_right _ _
  have hst0 : small≤t/2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N]))
  let ellMin := (7/8:ℝ)*rmin
  have hmin : 0<ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small/2
  have heps : 0<eps := by dsimp [eps];positivity
  have hepss : eps≤small := by dsimp [eps];linarith only [hsmall]
  have heps1 : eps≤1 := by linarith only [hepss, hst0, ht1]
  have hbud' := hbud ε e eps hε.le (hεa.trans hsa) he.le (hea.trans hsa)
    heps.le (hepss.trans hsa)
  have heN : ((N:ℝ)+2000)*eps≤t := by
    have h := (le_div_iff₀ (show 0<(N:ℝ)+2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((N:ℝ)+8)*eps≤t := by nlinarith only [heN, heps.le]
  have het : 2000*e≤t := by linarith only [hea, hst0]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0<sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma≤t/2 := min_le_left _ _
  have hsell : sigma≤ellMin/4 := min_le_right _ _
  refine ⟨{
    t:=t,N:=N,ell:=ell,rmin:=rmin,ε:=ε,e:=e,κ:=κ,cost:=cost,eps:=eps,sigma:=sigma
    t_pos:=ht,t_delta:=htΔ,t_small:=ht1,slots_pos:=hN,slots_injective:=hell,slots_sum:=hsum
    slots_bounds:=fun j=>⟨(hbounds j).1,(hbounds j).2.1,(hbounds j).2.2.2⟩
    rmin_pos:=hr,epsilon_pos:=hε,epsilon_small:=hε1,epsilon_gap:=hεgap
    e_pos:=he,e_small:=he1,kappa_pos:=hκ,kappa_small:=hκ1,cost_pos:=hcost
    eps_pos:=heps,eps_small:=heps1,sigma_pos:=hs,detector_budget:=by linarith only [hdet]
    phase_budget:=hphase,count_budget:=hbud'.1,central_budget:=hbud'.2
    geometric_budget:=by linarith only [hst2, het, ht1]
    principal_budget:=by linarith only [hst2, ht1]
    window_budget:=by change sigma+e≤(7/8)*ellMin;linarith only [hsell, heell, hmin]
    floor_budget:=by linarith only [hst2, het, he8, ht1]
    high_saving:=by linarith only [hst2, ht]
    height_choice:=?_ },?_⟩
  · intro J hJ
    let τ := min ((1/200:ℝ)*cost/16) (min (1/800) (t/(4*(J+7))))
    have htau : 0<τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have hτc : τ≤(1/200:ℝ)*cost/16 := min_le_left _ _
    have hτd : τ≤1/800 := (min_le_right _ _).trans (min_le_left _ _)
    have hτt : τ≤t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
    have hτJ : τ*(4*(J+7))≤t := (le_div_iff₀ (by positivity)).mp hτt
    have hprod : 0≤τ*J := mul_nonneg htau.le hJ
    have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
    refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc, hcost],
      by nlinarith only [hτJ, hprod, htau],by nlinarith only [hτJ, hprod, htau],
      by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
  · refine ⟨?_, by change 2000*ε≤t; linarith only [hεa,hst0], het, he8⟩
    intro j
    change ell j≤mesh t/200
    calc
      ell j≤(1/200:ℝ)*min t (mesh t):=(hbounds j).2.2.1
      _≤(1/200:ℝ)*mesh t:=mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _=mesh t/200:=by ring

/-- All original central rows, with their floor and nonfloor bins kept. -/
theorem actual_central_rows_bound {Δ : ℝ} (hΔ : 0 ≤ Δ) (hΔ1 : Δ ≤ 1/8)
    (D : HighData Δ) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t)
    (hεt : 2000*D.ε ≤ D.t) (het : 2000*D.e ≤ D.t)
    (hepst : ((D.N:ℝ)+8)*D.eps ≤ D.t)
    (n : ℕ) (τ : ℝ) (hτ : 0<τ) (hτd : τ<(1/200:ℝ)/2)
    (hτcost : 4*τ<(1/200:ℝ)*D.cost) (hτ2 : 2*τ≤D.t)
    (hτeps : τ*(2+4*D.eps)<D.t)
    (hsource : ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      SourceMomentBound F counts η Z τ (C*Z^D.t) (Z^(2*τ))) :
    letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
    ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      ∀idx grid : FreeRow→ℕ,
      (∀u,idx u≤n ∧ grid u≤⌊(49/100:ℝ)/D.e⌋₊ ∧ 51/100+D.e*grid u≤1) →
      (∀u,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(idx u+1:ℕ)*Z^τ)<51/100+D.e*grid u+2*D.e) →
      (∀u,51/100+D.e*grid u≤detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        ((3*idx u:ℕ)*Z^τ)) →
      let Yp : Fin D.N→ℝ := fun j=>Z^(D.ell j)
      let T : Fin D.N→Finset ProbePhysical.PrimeIdeal :=
        fun j=>pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Yp j)
      let normer := PrincipalMellinResidues.sourceResidueConstant F.W F.W (∏P∈F.S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (PrincipalSignalComparison.slotMass T
            (ProbePrincipalResidueActual.residueWeights (fun _=>F.w) Yp)) : ℂ)
      normer≠0 ∧
      ‖finiteCentralCubeRows F.S F.exclusions F.maximal η
        (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+D.t))) T
        (nonfloorPoolOutside F.modulus ⊤ F.S D.N 1 2 Yp)
        (fun _ y=>(F.w y:ℂ)) Yp F.W F.W
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z D.e
        (fun u=>51/100+D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖ ≤
        C*Z^(3/16+Δ-21/200000+D.t/4) := by
  let : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  have ht := D.t_pos
  have ht1 := D.t_small
  have hconductor : (13/16:ℝ)+D.t+2*D.t≤7/8 := by linarith
  have hcosts : (13/16:ℝ)*(159*D.ε+D.t+D.t+7*D.t)+2*D.t+(3/2)*(2*D.t)+
      (26*D.e+(D.N+8)*D.eps+D.t+D.t/6)+(D.t+2*τ+D.t)+21/200000≤49/440640 := by
    linarith
  obtain ⟨Cn,hCn,hnonfloor⟩ := actual_nonfloor_rows_saving F.modulus ⊤ le_top D.N n
    D.e D.eps 1 2 1 D.t (1/200) (7/8) D.rmin τ D.ε D.κ D.cost D.t D.t D.t
    D.e_pos D.e_small D.eps_pos (by norm_num) (by norm_num) (by norm_num)
    ht.le (by norm_num) (by norm_num) (by norm_num) D.rmin_pos hτ D.epsilon_pos D.kappa_pos
    D.cost_pos.le ht D.phase_budget D.epsilon_gap ht (by linarith) hτeps
    F.S F.exclusions F.first F.maximal D.ell D.slots_injective
    (fun j=>(D.slots_bounds j).2.1) (fun j=>(D.slots_bounds j).2.2)
    (fun _=>F.w) (fun _=>F.support) (fun _=>F.smooth) (fun _=>F.bounded)
    (fun _=>F.compact) (fun _=>F.nonzero) D.slots_sum
    (by norm_num) D.epsilon_small D.kappa_small hτd hτcost (by nlinarith [D.detector_budget])
    F.w F.smooth F.compact F.positive_support (fun y=>(F.bounded y).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support (fun y=>(F.bounded y).2)
    D.t Δ D.t D.t (2*τ) D.t ht hΔ hΔ1 ht ht (by linarith)
    D.t (2*D.t) (21/200000) ht.le (by linarith) (by positivity) D.count_budget hcosts
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t/8) (by positivity) ⌊(49/100:ℝ)/D.e⌋₊ (D.t/8) (by positivity)
    (by norm_num) hconductor (by linarith) counts
  have hfloorcost : 2*D.t+26*D.e+(D.N+8)*D.eps+D.t+D.t/6+D.t/8+
      21/200000≤(7/1200:ℝ) := by linarith
  obtain ⟨Cf,hCf,hfloor⟩ := actual_floor_rows_saving F.modulus ⊤ le_top D.N n
    D.e D.eps 1 2 1 D.t (1/200) (7/8) D.rmin τ D.ε D.κ D.cost D.t (1/100) D.t D.t
    D.e_pos D.e_small D.eps_pos (by norm_num) (by norm_num) (by norm_num)
    ht.le (by norm_num) (by norm_num) (by norm_num) D.rmin_pos hτ D.epsilon_pos D.kappa_pos
    D.cost_pos.le ht (by norm_num) D.phase_budget D.epsilon_gap ht (by linarith) hτeps
    F.S F.exclusions F.first F.maximal D.ell D.slots_injective
    (fun j=>(D.slots_bounds j).2.1) (fun j=>(D.slots_bounds j).2.2)
    (fun _=>F.w) (fun _=>F.support) (fun _=>F.smooth) (fun _=>F.bounded)
    (fun _=>F.compact) (fun _=>F.nonzero) D.slots_sum
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t/8) (by positivity) D.t (21/200000) ht.le (by linarith) (by norm_num) hfloorcost
  intro η
  obtain ⟨Cm,hCm,hmoments⟩ := hsource η
  refine ⟨1+(Cf+Cn*Cm)*(η.modulus.absNorm:ℝ)^(2*D.eps),by positivity,?_⟩
  filter_upwards [hnonfloor η,hfloor η,hmoments,
    sourceDyad_geometry_eventually (1/200) (7/8) D.t (13/16+D.t)
      (by norm_num) (by norm_num) ht hconductor,
    HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+1) τ hτ,
    eventually_gt_atTop (1:ℝ)] with Z hn hf hmom hgeo hnheight hZ
  intro idx grid hlabels hnext hcurrent
  dsimp only
  let Yp : Fin D.N→ℝ := fun j=>Z^(D.ell j)
  let T : Fin D.N→Finset ProbePhysical.PrimeIdeal :=
    fun j=>pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Yp j)
  let hT := nonfloorPoolOutside F.modulus ⊤ F.S D.N 1 2 Yp
  let WC : Fin D.N→ℝ→ℂ := fun _ y=>(F.w y:ℂ)
  let normer := PrincipalMellinResidues.sourceResidueConstant F.W F.W (∏P∈F.S,P)*
    (Probe.principalScalar Finset.univ Z (1/6)
      (PrincipalSignalComparison.slotMass T
        (ProbePrincipalResidueActual.residueWeights (fun _=>F.w) Yp)) : ℂ)
  let allRows := rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+D.t))
  let rows := supportedNonfloorRows F.S F.maximal allRows grid
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(13/16+D.t) := by
    intro u hu
    rcases (mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu with ⟨hur,hcal,_⟩
    have hh := mem_rowBand.mp hur
    exact ⟨hh.1,hh.2.1,hcal,hh.2.2.le⟩
  have hlabel : ∀u∈rows,idx u≤n ∧ grid u≤⌊(49/100:ℝ)/D.e⌋₊ ∧
      grid u≠0 ∧ 51/100+D.e*grid u≤1 := by
    intro u hu
    exact ⟨(hlabels u).1,(hlabels u).2.1,
      ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu).2.2,(hlabels u).2.2⟩
  have hnon := hn Cm hCm.le rows hrows idx grid hlabel
    (fun u _=>hnext u) (fun u _=>hcurrent u) ?_
  rotate_left
  · intro k hk i hi j hj
    dsimp only
    intro hne t htheight
    let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
    have hsub : rows'⊆rows∩dyadicRows 1 k := Finset.filter_subset _ _
    have hsubr : rows'⊆rows := hsub.trans Finset.inter_subset_left
    have hg := hgeo rows (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.1,(hrows u hu).2.2.2⟩)
      k (hne.mono hsub)
    obtain ⟨u,hu⟩ := hne
    have huj : grid u=j := ((mem_cubeBinRows _ idx grid i j u).mp hu).2.2
    have hjne : j≠0 := huj ▸ ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp (hsubr hu)).2.2
    have ha : (51/100:ℝ)<51/100+D.e*j := by
      have hjp : (0:ℝ)<j := by exact_mod_cast Nat.pos_of_ne_zero hjne
      nlinarith [D.e_pos]
    have ha' : (51/100:ℝ)+D.e*j≤1 := by simpa only [huj] using (hlabels u).2.2
    have hrow' : ∀v∈rows',v.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm v ∧
        (calibrationForSet F.S F.maximal).residueMonoid v.val≠0 ∧
        rowNorm v≤Z^(sourceDyadConductor Z D.t k-D.t) := by
      intro v hv
      exact ⟨(hrows v (hsubr hv)).1,(hrows v (hsubr hv)).2.1,
        (hrows v (hsubr hv)).2.2.1,hg.2.2.2.2.2 v (hsub hv)⟩
    have hi' : (i:ℝ)≤n := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hheight : (3*i+1:ℕ)*Z^τ≤Z^(2*τ) := by
      have hZp : 0<Z := zero_lt_one.trans hZ
      calc
        _≤(3*(n:ℝ)+1)*Z^τ := by push_cast;gcongr
        _≤Z^τ*Z^τ := mul_le_mul_of_nonneg_right hnheight (by positivity)
        _=Z^(2*τ) := by rw [←Real.rpow_add hZp];congr 1;ring
    apply hmom rows' (sourceDyadConductor Z D.t k) (51/100+D.e*j)
      hg.2.2.1 hg.2.2.2.1 ha ha' hrow' i ((17/50:ℂ)+t.1.2*Complex.I)
    · simp
    · simpa using htheight.2.trans hheight
  let floors := supportedFloorRows F.S F.maximal allRows grid
  have hfrows : ∀u∈floors,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^((7/8:ℝ)-D.t) := by
    intro u hu
    rcases (mem_supportedFloorRows F.S F.maximal allRows grid u).mp hu with ⟨hur,hcal,_⟩
    have hh := mem_rowBand.mp hur
    exact ⟨hh.1,hh.2.1,hcal,hh.2.2.le.trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))⟩
  have hfnorms : ∀u∈floors,rowNorm u≤Z^((13/16:ℝ)+D.t) := by
    intro u hu
    exact (mem_rowBand.mp ((mem_supportedFloorRows F.S F.maximal allRows grid u).mp hu).1).2.2.le
  have hfbin : ∀u∈floors,detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      (3*(idx u+1:ℕ)*Z^τ)<51/100+2*D.e := by
    intro u hu
    have hg := ((mem_supportedFloorRows F.S F.maximal allRows grid u).mp hu).2.2
    simpa only [hg,Nat.cast_zero,mul_zero,add_zero] using hnext u
  have hfl := hf (7/8) (by norm_num) le_rfl (13/16+D.t) (by linarith) le_rfl
    floors hfrows hfnorms idx (fun u _=>(hlabels u).1) hfbin
  refine ⟨hnon.1,?_⟩
  change ‖finiteCentralCubeRows F.S F.exclusions F.maximal η allRows T hT WC Yp F.W F.W
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z D.e
    (fun u=>51/100+D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
  rw [finiteCentralCubeRows_supported_split,add_div]
  apply (norm_add_le _ _).trans
  have hexp : Z^(3/16-21/200000:ℝ)≤Z^(3/16+Δ-21/200000+D.t/4) :=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have heq : (3/16:ℝ)+Δ-21/200000+D.t/8+D.t/8=3/16+Δ-21/200000+D.t/4 := by ring
  have hnon' := hnon.2
  rw [heq] at hnon'
  calc
    _ ≤ Cf*(η.modulus.absNorm:ℝ)^(2*D.eps)*Z^(3/16-21/200000)+
      Cn*Cm*(η.modulus.absNorm:ℝ)^(2*D.eps)*Z^(3/16+Δ-21/200000+D.t/4) :=
        add_le_add hfl.2 hnon'
    _ ≤ Cf*(η.modulus.absNorm:ℝ)^(2*D.eps)*Z^(3/16+Δ-21/200000+D.t/4)+
      Cn*Cm*(η.modulus.absNorm:ℝ)^(2*D.eps)*Z^(3/16+Δ-21/200000+D.t/4) := by gcongr
    _ = ((Cf+Cn*Cm)*(η.modulus.absNorm:ℝ)^(2*D.eps))*
      Z^(3/16+Δ-21/200000+D.t/4) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
      linarith

/-- Native prepared data and actual buffered bins give a full central source saving
for every compatible fixed source datum, including rebuilt finite exclusions.
The remaining normalized physical probe is not estimated by this theorem. -/
theorem exists_full_central_source_saving
    (hbeta : (8749/10000:ℝ)≤HeckeZeroSupremum.beta)
    (hupper : HeckeZeroSupremum.beta≤(7/8:ℝ)) :
    ∃D : HighData (1/10000000:ℝ),∀F : SourceData D,∃τ : ℝ,∃n : ℕ,
      0<τ ∧ 0<n ∧
      letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
      ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
        ∃idx grid : FreeRow→ℕ,
        (∀u : FreeRow,
          1 ≤ idx u ∧ idx u≤n ∧ grid u≤⌊(49/100:ℝ)/D.e⌋₊ ∧
          let a : ℝ := 51/100+D.e*grid u
          let H : ℝ := (3*idx u+1:ℕ)*Z^τ
          (51/100:ℝ)≤a ∧ a≤1 ∧ Z^τ≤H ∧ H+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ ∧
          a≤detectorMaximum
            (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
            (3*idx u*Z^τ) ∧
          detectorMaximum
            (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
            (3*idx u*Z^τ)<a+D.e ∧
          detectorMaximum
            (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
            (3*(idx u+1:ℕ)*Z^τ)<a+2*D.e ∧
          (51/100<a → ∃j s,
            LFunction (sourceDetectorFamily F.S F.exclusions.prime η u
              (rayCubeFamily F.modulus ⊤ le_top u) j) s=0 ∧
            ¬((sourceDetectorFamily F.S F.exclusions.prime η u
              (rayCubeFamily F.modulus ⊤ le_top u) j).residue=1 ∧ s=1) ∧
            a≤s.re ∧ s.re<a+D.e ∧ |s.im|≤3*idx u*Z^τ)) ∧
        let Yp : Fin D.N→ℝ := fun j=>Z^(D.ell j)
        let T : Fin D.N→Finset ProbePhysical.PrimeIdeal :=
          fun j=>pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Yp j)
        let normer := PrincipalMellinResidues.sourceResidueConstant F.W F.W (∏P∈F.S,P)*
          (Probe.principalScalar Finset.univ Z (1/6)
            (PrincipalSignalComparison.slotMass T
              (ProbePrincipalResidueActual.residueWeights (fun _=>F.w) Yp)) : ℂ)
        normer≠0 ∧
        ‖finiteCentralCubeRows F.S F.exclusions F.maximal η
          (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+D.t))) T
          (nonfloorPoolOutside F.modulus ⊤ F.S D.N 1 2 Yp)
          (fun _ y=>(F.w y:ℂ)) Yp F.W F.W
          (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z D.e
          (fun u=>51/100+D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖ ≤
          C*Z^(HeckeZeroSupremum.beta-11/16-1/250000) := by
  obtain ⟨D,hfine,hεt,het,hepst⟩ := exists_prepared_data (1/10000000) (by norm_num)
    (detectorMesh (1/10000000)) (fun t ht=>detectorMesh_pos (by norm_num) ht)
  refine ⟨D,?_⟩
  intro F
  obtain ⟨counts⟩ := source_count_parameters F
  obtain ⟨τ,hτ,hτd,hτcost,_,hτ2,hτeps,hsource⟩ :=
    MomentBelowBoundary.chosen_height_below_boundary (by norm_num) D F counts hfine
      (by linarith) hupper
  obtain ⟨n,hn,hwidth⟩ := exists_source_cube_bin_number D.e D.e_pos
  have hbound := actual_central_rows_bound (by norm_num : (0:ℝ)≤1/10000000)
    (by norm_num) D F counts hεt het hepst n τ hτ hτd hτcost hτ2 hτeps hsource
  refine ⟨τ,n,hτ,hn,?_⟩
  let : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  intro η
  obtain ⟨C,hC,hb⟩ := hbound η
  refine ⟨C,hC,?_⟩
  filter_upwards [hb,source_cube_height_eventually τ hτ] with Z hb hZ
  obtain ⟨idx,grid,hbins⟩ := exists_source_cube_bins D.e (Z^τ) D.e_pos hZ.2 n hn hwidth
    F.S F.exclusions.prime η (rayCubeFamily F.modulus ⊤ le_top)
  refine ⟨idx,grid,hbins,?_⟩
  have hl : ∀u,idx u≤n ∧ grid u≤⌊(49/100:ℝ)/D.e⌋₊ ∧ 51/100+D.e*grid u≤1 := by
    intro u
    obtain ⟨_,hin,hg,_,ha,_⟩ := hbins u
    exact ⟨hin,hg,ha⟩
  have hnext : ∀u,detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      (3*(idx u+1:ℕ)*Z^τ)<51/100+D.e*grid u+2*D.e := by
    intro u
    obtain ⟨_,_,_,_,_,_,_,_,_,hh,_⟩ := hbins u
    exact hh
  have hcurrent : ∀u,51/100+D.e*grid u≤detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      ((3*idx u:ℕ)*Z^τ) := by
    intro u
    obtain ⟨_,_,_,_,_,_,_,hh,_⟩ := hbins u
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh
  have hb' := hb idx grid hl hnext hcurrent
  dsimp only at hb' ⊢
  refine ⟨hb'.1,hb'.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le hZ.1 (by linarith [D.t_small])

end OpenAIReview.FullCentralBelowBoundary
#lint+ in OpenAIReview.FullCentralBelowBoundary

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty actual central bound audit."
  logInfo m!"Full central audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-full-central-below-boundary-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-full-central-below-boundary-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual complete central rows source-small in native betaSup band[8749/10000,7/8]; no physical theta estimate or new zero exclusion"),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("namespaceLinters",toJson (15:Nat)),("allLocalModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("details",Json.arr reports)]).pretty
