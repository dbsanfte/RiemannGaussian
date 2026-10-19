/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHSquareGaussianPayment
import OAI.NumberTheory.DirichletL.Detector.LowNormalized
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData

/-!
The original ray pools have distinct positive slot lengths, hence are
eventually pairwise disjoint. The SAME actual source pools, bounded-one
original profiles, finite common-Gaussian profile family and whole source
normalizer are joined here. No scalar normer bound or source allocation to
a numerator subset is supplied as a premise.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped Classical ContDiff BigOperators SchwartzMap
open Filter
namespace OpenAIReview.SquareSourceNormalized
open OAI OAI.SevenEighths OAI.CompletedGauss
open OAI.SevenEighths.ProbePhysical OAI.SevenEighths.CubicSieve
open RayFourExpansion CanonicalQuadraticSieve SquareSectorTransfer ProbeRaySlots
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- Literal finite compensation-subset sum of the ORIGINAL central-square
Gaussian dyads. This only names the actual summands in the original identity. -/
def centralSquareSum {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (ell : Fin K → ℝ) (W : Fin K → ℝ → ℂ)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (T : Fin K → Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (Z : ℝ) (hZ : 0<Z) (ε : ℝ)
    (V : Finset (Fin K) → SchwartzMap ℝ ℂ) (hV : ∀J,HasCompactSupport (V J:ℝ→ℂ)) : ℂ :=
  ∑J∈(Finset.univ : Finset (Fin K)).powerset, ∑'j : ℕ,
    if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then 0 else
      SquareGaussianPayment.gaussianSectorDyad SquareNumerator η S hS W0 W1
        (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
        (fun i=>canonicalSlotSupport (T i)) (fun i=>canonicalSlotSupport_nonzero _ (hT i))
        J W (fun i=>Z^(ell i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ))
        (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) ((2:ℝ)^j)
        (Z^(1+lowSelectedLength ell J)) (V J) (hV J)

/-- Actual finite-J central square payment, retaining each fixed common
Gaussian profile and uniformity over the original admissible slot sets. -/
theorem centralSquareSum_bound {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε εG : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1) (hεG : 0<εG)
    (W : Fin K→ℝ→ℂ) (hWnorm : ∀i x,‖W i x‖≤1)
    (V : Finset (Fin K)→SchwartzMap ℝ ℂ) (hV : ∀J,HasCompactSupport (V J:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1) (hM1 : 0≤M1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hWM1 : ∀x,‖W1 x‖≤M1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(hZ : 0<Z)(T : Fin K→Finset PrimeIdeal)(hT : ∀i P,P∈T i→Supported P.val),
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
      ‖centralSquareSum η S hS ell W W0 W1 a0 b0 a1 b1 ha0 ha1 T hT Z hZ ε V hV‖ ≤
        C*Z^(5/72+255*ε+2*εG:ℝ) := by
  choose C hC he using fun J : Finset (Fin K)=>
    SquareGaussianPayment.central_square_gaussian_payment η S hS hbad ell hell hsum
      a b ε εG ha hε hε1 hεG (V J) (hV J) W0 W1 a0 b0 a1 b1 M1
      ha0 ha1 hM1 hW0 hW1 hW0s hWM1
  let C0 := (∑J∈(Finset.univ : Finset (Fin K)).powerset,C J)+1
  have hC0 : 0<C0 := by
    have hn := Finset.sum_nonneg (fun J (_ : J∈(Finset.univ : Finset (Fin K)).powerset)=>(hC J).le)
    dsimp only [C0]
    linarith
  refine ⟨C0,hC0,?_⟩
  filter_upwards [Filter.eventually_all.mpr he] with Z hZ
  refine ⟨(hZ ∅).1,?_⟩
  intro hz T hT hout hdis hnorm
  unfold centralSquareSum
  apply (norm_sum_le _ _).trans
  have hh := Finset.sum_le_sum (fun J (_ : J∈(Finset.univ : Finset (Fin K)).powerset)=>
    ((hZ J).2 hz T hT hout hdis hnorm J W hWnorm).2.2.2)
  apply hh.trans
  rw [←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (by dsimp [C0];linarith) (Real.rpow_nonneg hz.le _)

/-- Same-family whole-source normalization of the ORIGINAL central-square
sum. The fixed Gaussian profiles are produced from the same actual W and the
original raw Gaussian identity is returned. Pairwise disjointness and the
whole normer inverse bound are proved using the actual native ray pools. -/
theorem original_source_normalized_square {K : ℕ}
    (M : Id) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b ε εG nu : ℝ) (ha : 0<a) (hab : a≤b) (hε : 0<ε) (hε1 : ε≤1)
    (hεG : 0<εG) (hnu : 0<nu)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤W j y ∧ W j y≤1) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
    ∃V : Finset (Fin K)→SchwartzMap ℝ ℂ,
    ∃hV : ∀J,HasCompactSupport (V J:ℝ→ℂ),
      (∀(η : HeckeFamily.Character)(Z : ℝ),0<Z→
        let Yp := fun j=>Z^(ell j)
        let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
        compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z =
          ∑J∈(Finset.univ : Finset (Fin K)).powerset,∑'j : ℕ,
            lowCommonDyad η (calibrationForSet S hmax) W0 W1 (fun i=>canonicalSlotSupport (T i))
              WC Yp J (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) ((2:ℝ)^j)
              (Z^(1+lowSelectedLength ell J)) (V J) (hV J)) ∧
      (∀η : HeckeFamily.Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
        let Yp := fun j=>Z^(ell j)
        let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
        let hT := fun j=>pool_supported (RayQuotient.identityClass M H) S hS a b (Yp j)
        let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
          (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ)
        normer≠0 ∧ ∀hZ : 0<Z,
          ‖centralSquareSum η S hmax ell WC W0 W1 a0 b0 a1 b1 ha0 ha1 T hT Z hZ ε V hV/normer‖ ≤
            C*Z^(5/72+255*ε+2*εG+nu:ℝ)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin K) : Function.support (WC j)⊆Set.Icc a b := by
    intro y hy
    apply Set.Ioo_subset_Icc_self (hsupp j _)
    intro hz
    exact hy (by dsimp [WC];rw [hz];simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖≤1 := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  obtain ⟨V,hV,_,hidentity⟩ := compensatedPhysicalProbe_common_gaussian WC
    (fun _=>|Real.log a|+|Real.log b|) (fun _=>by positivity)
    (fun j=>low_window_log_support (WC j) a b ha (hWC j))
  refine ⟨V,hV,?_,?_⟩
  · intro η Z hz
    dsimp only
    let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Z^(ell j))
    have ht := fun j=>pool_supported (RayQuotient.identityClass M H) S hS a b (Z^(ell j))
    have hslots : ∀i n,n∈canonicalSlotSupport (T i)→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (ht i)
    rw [hidentity η (calibrationForSet S hmax) W0 W1
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
      _ hslots (fun j=>Z^(ell j)) (fun _=>by positivity)
      (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (by positivity) (by positivity) hz]
    apply Finset.sum_congr rfl
    intro J _
    have hc : Z*(∏i∈Finset.univ\J,Z^(ell i))=Z^(1+lowSelectedLength ell J) := by
      rw [lowSelectedScale_product ell J Z hz,Real.rpow_add hz,Real.rpow_one]
    rw [hc]
    rfl
  · obtain ⟨Cn,hCn,hnorm⟩ := ProbeHighRowFamily.actual_ray_normalizer_inverse M H hH S hS a b ha hab
      ell hell hsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
    intro η
    obtain ⟨Cs,hCs,hsquare⟩ := centralSquareSum_bound η S hmax hS.bad ell (fun j=>(hell j).le) hsum.le
      a b ε εG ha hε hε1 hεG WC hWCB V hV W0 W1 a0 b0 a1 b1
      (SchwartzMap.seminorm ℝ 0 0 W1) ha0 ha1 (by positivity) hW0 hW1
      (W0.smooth (⊤ : ℕ∞)) (SchwartzMap.norm_le_seminorm ℝ W1)
    refine ⟨Cs*Cn,by positivity,?_⟩
    filter_upwards [hsquare,hnorm,power_pools_eventually_disjoint (RayQuotient.identityClass M H) S
      (fun _=>a) (fun _=>b) ell (fun _=>ha) (fun _=>hab) hinj] with Z hs hn hd
    refine ⟨hs.1,?_⟩
    dsimp only at hn ⊢
    refine ⟨hn.1,?_⟩
    intro hz
    let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Z^(ell j))
    have ht := fun j=>pool_supported (RayQuotient.identityClass M H) S hS a b (Z^(ell j))
    have hb0 := hs.2 hz T ht
      (fun j P hP=>((mem_pool (RayQuotient.identityClass M H) S a b (Z^(ell j)) P).mp hP).2.2.2)
      (fun i j hij=>hd i j hij) (fun j P hP=>by
        have hh := pool_norm_bounds (RayQuotient.identityClass M H) S ha.le hab
          (Real.rpow_pos_of_pos hz _) P hP
        simpa only [mul_comm] using And.intro hh.1.le hh.2)
    rw [div_eq_mul_inv,norm_mul]
    calc
      _≤(Cs*Z^(5/72+255*ε+2*εG:ℝ))*(Cn*Z^nu) :=
        mul_le_mul hb0 hn.2 (norm_nonneg _) (by positivity)
      _=(Cs*Cn)*Z^(5/72+255*ε+2*εG+nu:ℝ) := by
        rw [mul_mul_mul_comm,←Real.rpow_add hz]

end OpenAIReview.SquareSourceNormalized
#lint+ in OpenAIReview.SquareSourceNormalized

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut details : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    details := details.push (Json.mkObj [("declaration", toJson n.toString),
      ("isTheorem", toJson ci.isTheorem), ("axioms", toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty same-family square source normalization audit."
  logInfo m!"Same-family square source normalization audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-square-source-normalized"
  IO.FS.writeFile ".lake/arithmetic-operator-square-source-normalized/axioms.json"
    (Json.mkObj [("scope", toJson "actual same source ray-pool and bounded-one profile finite-J central-square normalization5/72+255epsilon+2epsilonG+nu; original common-Gaussian identity returned; native actual normer inverse used; no subset source"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("allLocalModuleProvenance", toJson true),
      ("declarations", toJson declarations), ("theoremsIncludingHelpers", toJson theorems),
      ("details", Json.arr details)]).pretty
