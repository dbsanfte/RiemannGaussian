/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszUnpaidCountTiltFloor
import RiemannGaussian.ZetaRieszHighSignCoverFloor
import RiemannGaussian.ZetaRieszRadialPeriodPayment

set_option autoImplicit false

/-!
# Literal dense-count owner fibres and their signed floor

The hard lower count is retained after signed prime-period cancellation.
The cofactors below are extracted from original integer labels. Every
extended owner-prime fibre is proved to stay inside the original core;
there is no original-mask or signed arithmetic estimate assumed in the
floor. The old fixed-count cofactor cap is not used.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszDenseCountCoverFloor
open ZetaRieszUnpaidCountTiltFloor ZetaRieszPrimeEndpoint
open ZetaRieszParityPacket ZetaRieszPrimeCountFrequency ZetaRieszJointAllocation
open ZetaRieszAllowancePrimeBoxes ZetaRieszClippedOwnerPeriodFloor
open ZetaRieszTinyOwnerPeriodFloor ZetaRieszSignedPeriodFloor
open ZetaRieszStaggeredFloor ZetaRieszBroadOwnerPeriodFloor
open ZetaRieszDenseSmallTopFloor ZetaRieszSmallCofactorCancellation

set_option maxHeartbeats 1000000

/-- A slightly wider share cap than the old fixed-count rectangle. This
uses the original support proof, not completion of the arithmetic sum. -/
theorem mem_core_of_share_le (j : ℕ) (hj : 32≤j) {u : ℝ}
    (hu : 1/2<u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j≤SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    {n : ℕ} (hs : Squarefree n) (hc : 3≤n.primeFactors.card)
    (hK : n.primeFactors.card<dyadicPrimeCount j)
    (hlo : (39/20 : ℝ)*dyadicMomentOrder j<log n)
    (hhi : log n≤(203/100 : ℝ)*dyadicMomentOrder j)
    (hmax : ∀ p∈n.primeFactors,log p≤(61/100 : ℝ)*log n) :
    n∈coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  have hN : (0 : ℝ)<N := by
    dsimp [N,dyadicMomentOrder,dyadicPrimeCount]
    positivity
  have ht : 0<log n := by change (39/20 : ℝ)*N<_ at hlo; linarith
  have hW : n∈literalWindow N := (mem_literalWindow N n).mpr
    (by constructor <;> dsimp [N] at * <;> nlinarith)
  have hpX : ∀ p∈n.primeFactors,
      p<(ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 := by
    intro p hp
    have hplog : log p<SquarefreeVaughanLogSource.length u N := by
      have hm := hmax p hp
      change log n≤(203/100 : ℝ)*N at hhi
      change (11/8 : ℝ)*N≤_ at hL
      nlinarith
    have he : log (((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) : ℝ)=
        SquarefreeVaughanLogSource.length u N := by
      simp only [SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
    exact_mod_cast (log_lt_log_iff (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
      (by positivity)).mp (he ▸ hplog)
  have hL' : (5/4 : ℝ)*dyadicMomentOrder j≤SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (dyadicMomentOrder j)]
  have hm := ZetaRieszMaskSupport.window_mem_originalMask j hj hu
    (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le) hL' hW hs hc hK hpX
  have hdom (p : ℕ) (hp : p∈n.primeFactors) : log p<(13/20 : ℝ)*log n := by
    nlinarith [hmax p hp]
  have hcancel : n∉cancellingSector u N K := by
    intro hh
    obtain ⟨_,_,_,_,_,p,hp,_,_,_,hshare⟩ := Finset.mem_filter.mp hh
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hd : log (n/p : ℕ)=log n-log p := by
      rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hp) (by exact_mod_cast hpp.ne_zero),
        log_div (by exact_mod_cast hs.ne_zero) (by exact_mod_cast hpp.ne_zero)]
    have hh := (div_le_iff₀ ht).mp hshare
    rw [hd] at hh
    nlinarith [hdom p hp]
  have hret : n∈ZetaRieszMaskSupport.retainedBand u N K := Finset.mem_sdiff.mpr ⟨hm,hcancel⟩
  have hnd : n∈ZetaRieszDominantAllocation.nondominantBand u N K := by
    refine Finset.mem_sdiff.mpr ⟨hret,?_⟩
    intro hd
    obtain ⟨_,_,_,_,p,hp,_,_,hl⟩ := Finset.mem_filter.mp hd
    exact (hdom p hp).not_ge hl
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨hnd,by constructor <;> dsimp [N] at * <;> nlinarith⟩,hlo,hhi⟩

/-- Original cofactors selected once. H fixes the lower owner endpoint,
not the individual cofactor-prime shares or their number of log bins. -/
def countCofactors (S : Finset ℕ) (N : ℕ) (H v y : ℝ) : Finset ℕ :=
  (S.image (fun n => n/largestPrime n)).filter (fun a =>
    Squarefree a ∧ 7≤a.primeFactors.card ∧
    5*log ((N : ℝ)+1)+1≤(a.primeFactors.card : ℝ) ∧
    a.primeFactors.card+1<ZetaRieszLogCountBudget.countThreshold N ∧
    (79/200 : ℝ)*v≤log a ∧
    (H<v-Real.pi/y-log a ∧ v-Real.pi/y-log a≤2*H) ∧
    ∀ q∈a.primeFactors,log q≤v-Real.pi/y-log a)

/-- The complete owner-prime fibres of these actual cofactors. -/
def countPeriod (S : Finset ℕ) (N : ℕ) (H v y : ℝ) : Finset ℕ :=
  (countCofactors S N H v y).biUnion (fun a =>
    (logPrimes (v-Real.pi/y-log a) (2*Real.pi/y)).image (fun p => a*p))

theorem countPeriod_data {S : Finset ℕ} {N n : ℕ} {H v y : ℝ}
    (hy : 54≤y) (hv : 100≤v) (hn : n∈countPeriod S N H v y) :
    Squarefree n ∧ 8≤n.primeFactors.card ∧
    5*log ((N : ℝ)+1)+2≤(n.primeFactors.card : ℝ) ∧
    n.primeFactors.card<ZetaRieszLogCountBudget.countThreshold N ∧
    (v-Real.pi/y<log n ∧ log n≤v+Real.pi/y) ∧
    ∀ p∈n.primeFactors,log p≤(61/100 : ℝ)*log n := by
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨_,hs,hc,hclo,hchi,hloga,_,ho⟩ := Finset.mem_filter.mp ha
  have hg := owner_fibre_geometry hs ho hp
  have hd := owner_fibre_count hs ho hp
  have he : log (a*p : ℕ)=log p+log a := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hs.ne_zero) (by exact_mod_cast hg.1.ne_zero)]
    ring
  have hπ : Real.pi/y≤1/16 :=
    (div_le_iff₀ (by linarith : 0<y)).mpr (by nlinarith [Real.pi_lt_d4])
  have hm : log p≤(61/100 : ℝ)*log (a*p : ℕ) := by
    rw [he]
    nlinarith only [hg.2.2.2.1,hg.2.2.2.2,hloga,hπ,hv]
  refine ⟨hd.1,by omega,?_,by rwa [hd.2],?_,?_⟩
  · rw [hd.2,Nat.cast_add,Nat.cast_one]
    linarith only [hclo]
  · simpa only [he] using And.intro hg.2.2.2.1 hg.2.2.2.2
  · intro q hq
    rw [Nat.primeFactors_mul hs.ne_zero hg.1.ne_zero,hg.1.primeFactors,
      Finset.mem_union,Finset.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact (log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos)
        (by exact_mod_cast (hg.2.1 q hq).le)).trans hm
    · exact hm

/-- Every extended label satisfies ALL original core masks. No artificial
fixed-count cofactor cap and no assumed core containment remains. -/
theorem countPeriod_subset_core (j : ℕ) (hj : 32≤j) (S : Finset ℕ)
    {u H v y : ℝ} (hu : 1/2<u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤y) (hv : 100≤v)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j≤SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hK : ZetaRieszLogCountBudget.countThreshold (dyadicMomentOrder j)≤dyadicPrimeCount j)
    (hlo : (39/20 : ℝ)*dyadicMomentOrder j≤v-Real.pi/y)
    (hhi : v+Real.pi/y≤(203/100 : ℝ)*dyadicMomentOrder j) :
    countPeriod S (dyadicMomentOrder j) H v y⊆coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  intro n hn
  obtain ⟨hs,hc,_,hct,hT,hmax⟩ := countPeriod_data hy hv hn
  exact mem_core_of_share_le j hj hu hU hL hs (by omega) (hct.trans_le hK)
    (hlo.trans_lt hT.1) (hT.2.trans hhi) hmax

/-- Every whole prime fibre has the physical owner cutoff. The original
cofactor masks need not be removed or completed to obtain this fact. -/
theorem countCofactors_owner_physical (S : Finset ℕ) {N : ℕ} (hN : 1≤N)
    {u H v y : ℝ} (hy : 54≤y) (_hv : 100≤v)
    (hH : 2*log N≤H)
    (hL : (11/8 : ℝ)*N≤SquarefreeVaughanLogSource.length u N)
    (hhi : v+Real.pi/y≤(203/100 : ℝ)*N) :
    ∀ a∈countCofactors S N H v y,∀ p∈logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
      p∈ZetaRieszAnnulusJoint.intermediatePrimes u N := by
  intro a ha
  obtain ⟨_,_,_,_,_,hloga,hstart,_⟩ := Finset.mem_filter.mp ha
  have hπ : Real.pi/y≤1/16 :=
    (div_le_iff₀ (by linarith : 0<y)).mpr (by nlinarith [Real.pi_lt_d4])
  have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
  apply whole_fibre_mem_intermediate hN (hH.trans hstart.1.le)
  have hπ0 : 0≤Real.pi/y := by positivity
  nlinarith only [hloga,hhi,hL,hπ,hπ0,hNR]

/-- The old count ceiling implies the large owner scale on every
nonempty literal cofactor population. It is not an extra scale assumption. -/
theorem countCofactors_scale {S : Finset ℕ} {N a : ℕ} (hN : 7≤N)
    {H v y : ℝ} (hH : 5000≤H) (hy : 54≤y)
    (ha : a∈countCofactors S N H v y) : v≤128*H*log ((N : ℝ)+1) := by
  obtain ⟨_,hs,_,_,hc,_,hstart,ho⟩ := Finset.mem_filter.mp ha
  have hH0 : 0<H := by linarith
  have hcR : (a.primeFactors.card : ℝ)≤16*log ((N : ℝ)+1) := by
    have hh : (a.primeFactors.card : ℝ)<ZetaRieszLogCountBudget.countThreshold N := by
      exact_mod_cast (show a.primeFactors.card<ZetaRieszLogCountBudget.countThreshold N by omega)
    exact hh.le.trans (paid_count_threshold_le hN)
  have hloga := ZetaRieszParityLayerCost.cofactor_log_le_count hs
    (show ∀ p∈a.primeFactors,log p≤4*H by intro p hp; linarith [ho p hp])
  have hsum := mul_le_mul_of_nonneg_left hcR (show 0≤4*H by linarith)
  have hl : 1≤log ((N : ℝ)+1) := by
    have hx : (8 : ℝ)≤(N : ℝ)+1 := by exact_mod_cast (show 8≤N+1 by omega)
    have hh := log_le_log (by norm_num : (0 : ℝ)<8) hx
    rw [show (8 : ℝ)=(2 : ℝ)^3 by norm_num,log_pow] at hh
    norm_num at hh
    linarith [log_two_gt_d9]
  have hπ : Real.pi/y≤1/16 :=
    (div_le_iff₀ (by linarith : 0<y)).mpr (by nlinarith [Real.pi_lt_d4])
  have hp := mul_le_mul_of_nonneg_left hl hH0.le
  nlinarith only [hloga,hsum,hstart.2,hπ,hp,hH]

/-- The actual finite cofactor prime universe, with no lower prime-share
cutoff. Its leading-one reciprocal mass is already proved in the repo. -/
def countPrimeUniverse (H : ℝ) : Finset ℕ := Nat.primesLE ⌊exp (4*H)⌋₊

theorem countPrimeUniverse_data {H : ℝ} {p : ℕ} (hp : p∈countPrimeUniverse H) :
    p.Prime ∧ log p≤4*H := by
  obtain ⟨hp,hprime⟩ := Nat.mem_primesLE.mp hp
  have hh : (p : ℝ)≤exp (4*H) :=
    (by exact_mod_cast hp : (p : ℝ)≤⌊exp (4*H)⌋₊).trans (Nat.floor_le (exp_nonneg _))
  exact ⟨hprime,by simpa using log_le_log (by exact_mod_cast hprime.pos) hh⟩

theorem mem_countPrimeUniverse {H : ℝ} {p : ℕ} (hp : p.Prime) (hlog : log p≤4*H) :
    p∈countPrimeUniverse H := by
  apply Nat.mem_primesLE.mpr
  refine ⟨?_,hp⟩
  apply Nat.le_floor
  simpa only [exp_log (by exact_mod_cast hp.pos : (0 : ℝ)<p)] using exp_le_exp.mpr hlog

theorem countCofactors_prime_support {S : Finset ℕ} {N a : ℕ} {H v y : ℝ}
    (_hH : 0≤H) (ha : a∈countCofactors S N H v y) : a.primeFactors⊆countPrimeUniverse H := by
  obtain ⟨_,_,_,_,_,_,hstart,ho⟩ := Finset.mem_filter.mp ha
  intro p hp
  exact mem_countPrimeUniverse (Nat.prime_of_mem_primeFactors hp) (by linarith [ho p hp])

/-- Signed cancellation on an ACTUAL finite population, rather than
a row estimate conditional on an unproved physical-support hypothesis.
All counts, prime-log spreads, phases, both hinges and owner weights stay.
The price is relative to the true supply unit, not an absolute source norm. -/
theorem countPeriod_raw_floor (S : Finset ℕ) {N : ℕ} (hN : 7≤N) {e : ℝ} (he : |e|=1)
    {u H v y : ℝ} (hy : 54≤y) (hH : 5000≤H) (hHx : H≤4*((N : ℝ)+1))
    (hphysical : 2*log N≤H) (hNv : (N : ℝ)+2≤v)
    (hL : (11/8 : ℝ)*N≤SquarefreeVaughanLogSource.length u N)
    (hhi : v+Real.pi/y≤(203/100 : ℝ)*N)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0) :
    -(481*exp (5*(smallPrimeHeadMass+log 16+1/5000+log ((N : ℝ)+1))-
      5*log ((N : ℝ)+1)*log (5/2 : ℝ))/H)*(amplitude N v/v)≤
    ∑ n∈countPeriod S N H v y,signedPart e
      (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) y N n := by
  by_cases hem : countCofactors S N H v y=∅
  · simp only [countPeriod,hem,Finset.biUnion_empty,Finset.sum_empty]
    have hv0 : 0≤v := by linarith [Nat.cast_nonneg (α := ℝ) N]
    have hh : 0≤(481*exp (5*(smallPrimeHeadMass+log 16+1/5000+log ((N : ℝ)+1))-
        5*log ((N : ℝ)+1)*log (5/2 : ℝ))/H)*(amplitude N v/v) := by
      positivity [amplitude_nonneg N hv0]
    linarith only [hh]
  obtain ⟨a₀,ha₀⟩ := Finset.nonempty_iff_ne_empty.mpr hem
  have hv : 100≤v := by
    have hd := (Finset.mem_filter.mp ha₀).2
    have hπ : 0≤Real.pi/y := by positivity
    linarith [hd.2.2.2.2.2.1,log_natCast_nonneg a₀]
  let M₀ := countCofactors S N H v y
  let I := M₀.image (fun a => a.primeFactors.card)
  let rows := fun k => M₀.filter (fun a => a.primeFactors.card=k)
  let C := smallPrimeHeadMass+log 16+1/5000
  let M := C+log ((N : ℝ)+1)
  let Q := countPrimeUniverse H
  have hx : 1≤(N : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hQ : (∑ p∈Q,(p : ℝ)⁻¹)≤M := whole_mass_log_bound Q hx hH hHx
    (fun p hp => countPrimeUniverse_data hp)
  have hM : 0≤M := (Finset.sum_nonneg (fun _ _ => by positivity)).trans hQ
  have hd a (ha : a∈M₀) := (Finset.mem_filter.mp ha).2
  have hrows k (_hk : k∈I) a (ha : a∈rows k) := Finset.mem_filter.mp ha
  have hI k (hk : k∈I) : 2≤k := by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hk
    have hh := (hd a ha).2.1
    omega
  have hcount k (hk : k∈I) : 5*log ((N : ℝ)+1)≤(k : ℝ) := by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hk
    linarith only [(hd a ha).2.2.1]
  have hL' : v/2≤SquarefreeVaughanLogSource.length u N := by
    have hπ : 0≤Real.pi/y := by positivity
    nlinarith only [hhi,hL,hπ,Nat.cast_nonneg (α := ℝ) N]
  have hphysical' := countCofactors_owner_physical S (by omega : 1≤N) hy hv hphysical hL hhi
  have hb := retained_literal_count_floor I N e
    (ZetaRieszAnnulusJoint.intermediatePrimes u N) rows Q hI he hH hNv hy hL' hM hQ
    (fun p hp => (countPrimeUniverse_data hp).2)
    (by
      intro k hk a ha
      have hh := hrows k hk a ha
      exact ⟨(hd a hh.1).1,hh.2,countCofactors_prime_support (by linarith : 0≤H) hh.1⟩)
    hx hcount
    (by intro k hk a ha; exact (hd a (hrows k hk a ha).1).2.2.2.2.2.1.1.le)
    (by intro k hk a ha; exact (hd a (hrows k hk a ha).1).2.2.2.2.2.2)
    (by intro k hk a ha; exact hphysical' a (hrows k hk a ha).1)
    hpeak hsign
  have heq : I.biUnion rows=M₀ := by
    ext a
    simp only [Finset.mem_biUnion,rows,Finset.mem_filter]
    constructor
    · rintro ⟨_,_,ha,_⟩; exact ha
    · intro ha; exact ⟨a.primeFactors.card,Finset.mem_image_of_mem _ ha,ha,rfl⟩
  rw [heq] at hb
  change -(481*exp (5*M-5*log ((N : ℝ)+1)*log (5/2 : ℝ))/H)*(amplitude N v/v)≤
    ∑ n∈countPeriod S N H v y,signedPart e
      (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) y N n at hb
  exact hb

/-- An interior original label with an ownership gap belongs to a
complete fibre extracted from its OWN cofactor. The threshold on the
largest prime is only geometric; its small-owner complement is already
the subject of the independent polynomial-owner payment. -/
theorem dense_label_covered (S : Finset ℕ) {N n : ℕ} (hn : n∈S)
    (hs : Squarefree n) (hc : 8≤n.primeFactors.card)
    (hclo : 5*log ((N : ℝ)+1)+2≤(n.primeFactors.card : ℝ))
    (hchi : n.primeFactors.card<ZetaRieszLogCountBudget.countThreshold N)
    {v y : ℝ} (hy : 54≤y) (hv : 100≤v)
    (hT : v-Real.pi/y<log n ∧ log n≤v+Real.pi/y)
    (hshare : log (largestPrime n)≤(601/1000 : ℝ)*log n)
    (hlarge : 20000<log (largestPrime n)) :
    ZetaRieszOwnerTieFloor.CloseOwners n ∨
      ∃ i : ℕ,n∈countPeriod S N (10000*(2 : ℝ)^i) v y := by
  by_cases htie : ZetaRieszOwnerTieFloor.CloseOwners n
  · exact Or.inl htie
  right
  have hd := canonical_owner_data hs (by omega : 3≤n.primeFactors.card)
  have hlog : log n=log (largestPrime n)+log (n/largestPrime n : ℕ) := by
    conv_lhs => rw [← hd.2.1,Nat.cast_mul,log_mul
      (by exact_mod_cast hd.1.ne_zero) (by exact_mod_cast hd.2.2.1.ne_zero)]
  have hπ : Real.pi/y≤1/16 :=
    (div_le_iff₀ (by linarith : 0<y)).mpr (by nlinarith [Real.pi_lt_d4])
  have hlow : 10000<v-Real.pi/y-log (n/largestPrime n : ℕ) := by
    linarith only [hT.2,hlog,hlarge,hπ]
  obtain ⟨i,hi,_⟩ := ZetaRieszDenseShellCost.exists_unique_log_shell
    (by norm_num : (0 : ℝ)<10000) hlow
  refine ⟨i,Finset.mem_biUnion.mpr ⟨n/largestPrime n,?_,?_⟩⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image_of_mem (fun n => n/largestPrime n) hn,hd.2.2.1,?_,?_,?_,?_,hi,?_⟩
    · have hh := hd.2.2.2.1
      omega
    · have he : (n.primeFactors.card : ℝ)=(n/largestPrime n).primeFactors.card+1 := by
        exact_mod_cast hd.2.2.2.1
      linarith only [hclo,he]
    · rwa [← hd.2.2.2.1]
    · nlinarith only [hlog,hshare,hT.1,hπ,hv]
    · exact no_close_owner_period_gap hs (by omega : 3≤n.primeFactors.card) hy hT htie
  · apply Finset.mem_image.mpr
    refine ⟨largestPrime n,?_,by simpa only [Nat.mul_comm] using hd.2.1⟩
    apply (ZetaRieszMacroPrimeWindows.mem_logPrimes_iff _ _ _).mpr
    refine ⟨hd.1,by linarith only [hT.1,hlog],?_⟩
    simp only [mul_div_assoc]
    linarith only [hT.2,hlog]

/-- Counts and every old credit remain disjoint after the literal
complete-fibre extension. Unlike the earlier row theorem, containment in
the original core is proved here, rather than left as a premise. -/
theorem countPeriod_subset_unpaid (j : ℕ) (hj : 32≤j) (S : Finset ℕ)
    {u H v y η h : ℝ} {Q P V R : ℕ}
    (hu : 1/2<u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤y) (hv : 100≤v) (hN : 1000≤dyadicMomentOrder j)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j≤SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hK : ZetaRieszLogCountBudget.countThreshold (dyadicMomentOrder j)≤dyadicPrimeCount j)
    (hlo : (39/20 : ℝ)*dyadicMomentOrder j≤v-Real.pi/y)
    (hhi : v+Real.pi/y≤(203/100 : ℝ)*dyadicMomentOrder j)
    (hh : 0<h) (hhu : h≤1/20) (w : ℕ→ℝ)
    (hw : ∀ M∈ZetaRieszRadialCompensation.radialIndices (dyadicMomentOrder j),0≤w M ∧ w M≤1/2) :
    countPeriod S (dyadicMomentOrder j) H v y ⊆
      coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)\
        ZetaRieszRoughFivePeriodFloor.spent
          (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)) (dyadicMomentOrder j)
          Q P V R η h (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) w := by
  apply middle_population_subset_unpaid _ _ hN η hh hhu w hw
    (countPeriod_subset_core j hj S hu hU hy hv hL hK hlo hhi)
  intro n hn
  have hd := countPeriod_data hy hv hn
  exact ⟨hd.2.1,hd.2.2.2.1⟩

/-- Disjoint scales of the lower owner endpoint cannot copy a literal
integer. The canonical prime and its cofactor are recovered exactly. -/
theorem countPeriod_scale_disjoint (S : Finset ℕ) (N : ℕ) {B v y : ℝ}
    (hB : 0<B) {i j : ℕ} (hij : i≠j) :
    Disjoint (countPeriod S N (B*(2 : ℝ)^i) v y) (countPeriod S N (B*(2 : ℝ)^j) v y) := by
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,hpn⟩ := Finset.mem_image.mp hn
  obtain ⟨b,hb,hn'⟩ := Finset.mem_biUnion.mp hn'
  obtain ⟨q,hq,hqn⟩ := Finset.mem_image.mp hn'
  have hda := (Finset.mem_filter.mp ha).2
  have hdb := (Finset.mem_filter.mp hb).2
  have hpa := owner_fibre_geometry hda.1 hda.2.2.2.2.2.2 hp
  have hqb := owner_fibre_geometry hdb.1 hdb.2.2.2.2.2.2 hq
  have he := ZetaRieszCoupledWindow.largest_prime_product_unique hpa.1 hqb.1
    (fun r hr hrd => hpa.2.1 r (hr.mem_primeFactors hrd hda.1.ne_zero))
    (fun r hr hrd => hqb.2.1 r (hr.mem_primeFactors hrd hdb.1.ne_zero))
    (hpn.trans hqn.symm)
  have hb' : b=a := he.1.symm
  rw [hb'] at hdb
  rcases lt_or_gt_of_ne hij with h | h
  · have hp := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (show i + 1 ≤ j by omega)) hB.le
    rw [pow_succ] at hp
    nlinarith only [hp,hda.2.2.2.2.2.1.2,hdb.2.2.2.2.2.1.1]
  · have hp := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (show j + 1 ≤ i by omega)) hB.le
    rw [pow_succ] at hp
    nlinarith only [hp,hdb.2.2.2.2.2.1.2,hda.2.2.2.2.2.1.1]

/-- Complete total-log periods at disjoint centres do not reuse a label.
This holds at growing counts without the old fixed-count cofactor cap. -/
theorem countPeriod_radial_disjoint (S T : Finset ℕ) (N : ℕ) {H J v w y : ℝ}
    (hy : 54≤y) (hv : 100≤v) (hw : 100≤w) (hsep : v+Real.pi/y≤w-Real.pi/y) :
    Disjoint (countPeriod S N H v y) (countPeriod T N J w y) := by
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  have hd := (countPeriod_data hy hv hn).2.2.2.2.1
  have hd' := (countPeriod_data hy hw hn').2.2.2.2.1
  linarith only [hd.2,hd'.1,hsep]

/-- Literal near-tied owners, assigned by their canonical SECOND prime.
This prevents different close-pair witnesses from duplicating the debit. -/
def countBoundary (S : Finset ℕ) (N : ℕ) (H v y : ℝ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ 8≤n.primeFactors.card ∧
    5*log ((N : ℝ)+1)+2≤(n.primeFactors.card : ℝ) ∧
    n.primeFactors.card<ZetaRieszLogCountBudget.countThreshold N ∧
    (v-Real.pi/y<log n ∧ log n≤v+Real.pi/y) ∧
    ZetaRieszOwnerTieFloor.CloseOwners n ∧
    (H<log (largestPrime (n/largestPrime n)) ∧ log (largestPrime (n/largestPrime n))≤2*H))

theorem close_second_owner {n : ℕ} (hs : Squarefree n) (hc : 3≤n.primeFactors.card)
    (htie : ZetaRieszOwnerTieFloor.CloseOwners n) :
    largestPrime (n/largestPrime n)∈(n/largestPrime n).primeFactors ∧
    log (largestPrime n)-1/8<log (largestPrime (n/largestPrime n)) := by
  have hd := canonical_owner_data hs hc
  have hq := ZetaRieszOwnedCells.largestPrime_mem_of_two
    (by have hh := hd.2.2.2.1; omega : 2≤(n/largestPrime n).primeFactors.card)
  obtain ⟨q,hqa,hclose⟩ := close_owner_canonical hs hc htie
  have hle := ZetaRieszPolynomialOwnerPayment.prime_le_largestPrime hqa
  exact ⟨hq,hclose.trans_le (log_le_log
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hqa).pos) (by exact_mod_cast hle))⟩

theorem countBoundary_data {S : Finset ℕ} {N n : ℕ} {H v y : ℝ}
    (hH : 1≤H) (hy : 54≤y) (hn : n∈countBoundary S N H v y) :
    Squarefree n ∧ 3≤n.primeFactors.card ∧
    5*log ((N : ℝ)+1)+2≤(n.primeFactors.card : ℝ) ∧
    (v-1/16<log n ∧ log n≤v+1/16) ∧
    (∃ q∈(n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
    (n/largestPrime n).primeFactors⊆countPrimeUniverse H := by
  obtain ⟨_,hs,hc,hclo,_,hT,htie,hqH⟩ := Finset.mem_filter.mp hn
  have hq := close_second_owner hs (by omega : 3≤n.primeFactors.card) htie
  have hπ : Real.pi/y≤1/16 :=
    (div_le_iff₀ (by linarith : 0<y)).mpr (by nlinarith [Real.pi_lt_d4])
  refine ⟨hs,by omega,hclo,⟨by linarith only [hT.1,hπ],by linarith only [hT.2,hπ]⟩,
    ⟨_,hq.1,hqH.1.le,by linarith only [hq.2]⟩,?_⟩
  intro p hp
  have hmax := ZetaRieszPolynomialOwnerPayment.prime_le_largestPrime hp
  have hlog : log p≤log (largestPrime (n/largestPrime n)) := log_le_log
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos) (by exact_mod_cast hmax)
  exact mem_countPrimeUniverse (Nat.prime_of_mem_primeFactors hp) (by linarith only [hlog,hqH.2,hH])

theorem countBoundary_all_prime_logs {S : Finset ℕ} {N n : ℕ} {H v y : ℝ}
    (hH : 1≤H) (hn : n∈countBoundary S N H v y) :
    ∀ p∈n.primeFactors,log p≤4*H := by
  obtain ⟨_,hs,hc,_,_,_,htie,hqH⟩ := Finset.mem_filter.mp hn
  have hd := canonical_owner_data hs (by omega : 3≤n.primeFactors.card)
  have hq := close_second_owner hs (by omega : 3≤n.primeFactors.card) htie
  intro p hp
  have hmax : log p≤log (largestPrime n) := log_le_log
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos) (by exact_mod_cast hd.2.2.2.2.1 p hp)
  linarith only [hmax,hq.2,hqH.2,hH]

/-- The count ceiling pays the scale for actual boundary labels too.
The two removed close primes keep the exact count shift in the debit. -/
theorem countBoundary_scale {S : Finset ℕ} {N n : ℕ} (hN : 7≤N)
    {H v y : ℝ} (hH : 1≤H) (hv : 100≤v) (hy : 54≤y)
    (hn : n∈countBoundary S N H v y) : v≤128*H*log ((N : ℝ)+1) := by
  have hd := (Finset.mem_filter.mp hn).2
  have hcR : (n.primeFactors.card : ℝ)≤16*log ((N : ℝ)+1) := by
    have hh : (n.primeFactors.card : ℝ)≤ZetaRieszLogCountBudget.countThreshold N := by
      exact_mod_cast hd.2.2.2.1.le
    exact hh.trans (paid_count_threshold_le hN)
  have hsum := Finset.sum_le_sum (countBoundary_all_prime_logs hH hn)
  rw [Finset.sum_const,nsmul_eq_mul,
    ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hd.1] at hsum
  have hh := mul_le_mul_of_nonneg_left hcR (show 0≤4*H by linarith)
  have hπ : Real.pi/y≤1/16 :=
    (div_le_iff₀ (by linarith : 0<y)).mpr (by nlinarith [Real.pi_lt_d4])
  have hcore : v/2≤log n := by linarith only [hd.2.2.2.2.1.1,hπ,hv]
  nlinarith only [hcore,hsum,hh]

/-- Exact cover of the literal tied-owner population, without choosing
one of several arbitrary marked-pair incidences. -/
theorem countBoundary_covered (S : Finset ℕ) {N n : ℕ} (hn : n∈S)
    (hs : Squarefree n) (hc : 8≤n.primeFactors.card)
    (hclo : 5*log ((N : ℝ)+1)+2≤(n.primeFactors.card : ℝ))
    (hchi : n.primeFactors.card<ZetaRieszLogCountBudget.countThreshold N)
    {v y : ℝ} (hT : v-Real.pi/y<log n ∧ log n≤v+Real.pi/y)
    (htie : ZetaRieszOwnerTieFloor.CloseOwners n)
    (hlarge : 20000<log (largestPrime n)) :
    ∃ i : ℕ,n∈countBoundary S N (10000*(2 : ℝ)^i) v y := by
  have hq := close_second_owner hs (by omega : 3≤n.primeFactors.card) htie
  have hlow : 10000<log (largestPrime (n/largestPrime n)) := by linarith only [hq.2,hlarge]
  obtain ⟨i,hi,_⟩ := ZetaRieszDenseShellCost.exists_unique_log_shell
    (by norm_num : (0 : ℝ)<10000) hlow
  exact ⟨i,Finset.mem_filter.mpr ⟨hn,hs,hc,hclo,hchi,hT,htie,hi⟩⟩

/-- Every actual dense label with the paid geometry removed is covered
by a complete physical owner fibre or by its explicit tied-owner debit.
The cover retains total log, both count endpoints and original ownership. -/
theorem dense_label_full_cover (S : Finset ℕ) {N n : ℕ} (hn : n∈S)
    (hs : Squarefree n) (hc : 8≤n.primeFactors.card)
    (hclo : 5*log ((N : ℝ)+1)+2≤(n.primeFactors.card : ℝ))
    (hchi : n.primeFactors.card<ZetaRieszLogCountBudget.countThreshold N)
    {v y : ℝ} (hy : 54≤y) (hv : 100≤v)
    (hT : v-Real.pi/y<log n ∧ log n≤v+Real.pi/y)
    (hshare : log (largestPrime n)≤(601/1000 : ℝ)*log n)
    (hlarge : 20000<log (largestPrime n)) :
    (∃ i : ℕ,n∈countPeriod S N (10000*(2 : ℝ)^i) v y) ∨
      ∃ i : ℕ,n∈countBoundary S N (10000*(2 : ℝ)^i) v y := by
  rcases dense_label_covered S hn hs hc hclo hchi hy hv hT hshare hlarge with htie | hh
  · exact Or.inr (countBoundary_covered S hn hs hc hclo hchi hT htie hlarge)
  · exact Or.inl hh

/-- Signed complete owner fibres and BOTH missed arithmetic sign parts
use ONE literal boundary debit. The hard count survives removal of two
close owners and the main signed prime sum is never normed. -/
theorem countPeriod_boundary_raw_floor (S : Finset ℕ) (Pplus Pminus : Finset ℕ)
    {N : ℕ} (hN : 7≤N) {e : ℝ} (he : |e|=1)
    {u H v y : ℝ} (hy : 54≤y) (hH : 10000≤H) (hHx : H≤4*((N : ℝ)+1))
    (hphysical : 2*log N≤H) (hNv : (N : ℝ)+2≤v)
    (hL : (11/8 : ℝ)*N≤SquarefreeVaughanLogSource.length u N)
    (hhi : v+Real.pi/y≤(203/100 : ℝ)*N)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0) :
    -(2017*exp (5*(smallPrimeHeadMass+log 16+1/5000+log ((N : ℝ)+1))-
      5*log ((N : ℝ)+1)*log (5/2 : ℝ))/H)*(amplitude N v/v)≤
    (∑ n∈countPeriod S N H v y,signedPart e
      (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) y N n)+
    (∑ n∈countBoundary S N H v y\Pplus,signedPart 1
      (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) y N n)+
    (∑ n∈countBoundary S N H v y\Pminus,signedPart (-1)
      (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) y N n) := by
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let Q := countPrimeUniverse H
  let M := smallPrimeHeadMass+log 16+1/5000+log ((N : ℝ)+1)
  have hx : 1≤(N : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hQ : (∑ p∈Q,(p : ℝ)⁻¹)≤M := whole_mass_log_bound Q hx
    (by linarith : 5000≤H) hHx (fun p hp => countPrimeUniverse_data hp)
  have hM : 0≤M := (Finset.sum_nonneg (fun _ _ => by positivity)).trans hQ
  have hL' : v/2≤L := by
    have hπ : 0≤Real.pi/y := by positivity
    dsimp [L]
    nlinarith only [hhi,hL,hπ,Nat.cast_nonneg (α := ℝ) N]
  have hb := countPeriod_raw_floor S hN he hy (by linarith : 5000≤H) hHx
    hphysical hNv hL hhi hpeak hsign
  have hD := clipped_count_lower_norm_bound ∅ (countBoundary S N H v y) Q y N hH
    (by linarith [Nat.cast_nonneg (α := ℝ) N] : 0<v)
    (by linarith only [hNv] : (N : ℝ)+1≤v) hL' hM hQ
    (fun p hp => (countPrimeUniverse_data hp).2) hx
    (fun n hn => countBoundary_data (by linarith : 1≤H) hy hn)
  have hA := (Finset.sum_le_sum (fun n (_hn : n∈countBoundary S N H v y) =>
    ZetaRieszParityLayerCost.allocation_family_atom_norm_le
      (fun n => A∩{largestPrime n}) L y N n)).trans hD
  have hm := ZetaRieszDenseSmallTopFloor.missed_parts_floor
    (fun n => A∩{largestPrime n}) (countBoundary S N H v y) Pplus Pminus L y N
  have hh := add_le_add hb ((neg_le_neg hA).trans hm)
  convert! hh using 1 <;> ring

/-- This single period price is vanishing relative to its exact supply
unit. The needed scale follows from a NONEMPTY literal main or boundary,
not from a cofactor-size or parity hypothesis inserted into the estimate. -/
theorem countPeriod_boundary_floor (S : Finset ℕ) (Pplus Pminus : Finset ℕ)
    {N : ℕ} (hN : 7≤N) {e : ℝ} (he : |e|=1)
    {u H v y : ℝ} (hy : 54≤y) (hH : 10000≤H) (hHx : H≤4*((N : ℝ)+1))
    (hphysical : 2*log N≤H) (hNv : (N : ℝ)+2≤v)
    (hL : (11/8 : ℝ)*N≤SquarefreeVaughanLogSource.length u N)
    (hhi : v+Real.pi/y≤(203/100 : ℝ)*N)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0) :
    -(258176*exp (5*(smallPrimeHeadMass+log 16+1/5000))*log ((N : ℝ)+1)*
      exp (-log ((N : ℝ)+1)/2))*(amplitude N v/v)≤
    (∑ n∈countPeriod S N H v y,signedPart e
      (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) y N n)+
    (∑ n∈countBoundary S N H v y\Pplus,signedPart 1
      (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) y N n)+
    (∑ n∈countBoundary S N H v y\Pminus,signedPart (-1)
      (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u N) y N n) := by
  have hx : 1≤(N : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hv : 0<v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hl := log_nonneg hx
  by_cases hm : countCofactors S N H v y=∅ ∧ countBoundary S N H v y=∅
  · simp only [countPeriod,hm.1,Finset.biUnion_empty,hm.2,Finset.empty_sdiff,Finset.sum_empty,
      zero_add]
    have hh : 0≤(258176*exp (5*(smallPrimeHeadMass+log 16+1/5000))*log ((N : ℝ)+1)*
        exp (-log ((N : ℝ)+1)/2))*(amplitude N v/v) := by positivity [amplitude_nonneg N hv.le]
    linarith only [hh]
  have hscale : v≤128*H*log ((N : ℝ)+1) := by
    by_cases hc : countCofactors S N H v y=∅
    · obtain ⟨n,hn⟩ := Finset.nonempty_iff_ne_empty.mpr (fun hd => hm ⟨hc,hd⟩)
      have hd := (Finset.mem_filter.mp hn).2
      have hv100 : 100≤v := by
        have hq := close_second_owner hd.1 (by have := hd.2.1; omega : 3≤n.primeFactors.card) hd.2.2.2.2.2.1
        have hpn := ZetaRieszOwnedCells.largestPrime_mem_of_two
          (by have := hd.2.1; omega : 2≤n.primeFactors.card)
        have hqd : largestPrime (n/largestPrime n)∣n :=
          (Nat.dvd_of_mem_primeFactors hq.1).trans
            (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hpn))
        have hlogn : log (largestPrime (n/largestPrime n))≤log n := log_le_log
          (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq.1).pos)
          (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hd.1.ne_zero) hqd)
        have hπ : Real.pi/y≤1/16 :=
          (div_le_iff₀ (by linarith : 0<y)).mpr (by nlinarith [Real.pi_lt_d4])
        linarith only [hd.2.2.2.2.2.2.1,hlogn,hd.2.2.2.2.1.2,hπ,hH]
      exact countBoundary_scale hN (by linarith : 1≤H) hv100 hy hn
    · obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr hc
      exact countCofactors_scale hN (by linarith : 5000≤H) hy ha
  have hb := countPeriod_boundary_raw_floor S Pplus Pminus hN he hy hH hHx
    hphysical hNv hL hhi hpeak hsign
  have hr := lower_count_rate_bound hx (by linarith : 0<H)
    (le_refl (smallPrimeHeadMass+log 16+1/5000+log ((N : ℝ)+1)))
    (by linarith only [hNv] : (N : ℝ)+1≤v) hscale
  simp only [neg_mul] at hb ⊢
  exact (neg_le_neg (mul_le_mul_of_nonneg_right hr
    (div_nonneg (amplitude_nonneg N hv.le) hv.le))).trans hb

/-- Global signed dense-count price for the literal cofactors and
canonical second-owner boundaries. No rowwise arithmetic bound, omitted
prime mask or count-dependent eventual threshold is a hypothesis. -/
theorem global_countPeriod_floor (V : Finset ℕ) (O : ℕ→Finset ℕ) (S : Finset ℕ)
    (Pplus Pminus : ℕ→ℕ→Finset ℕ) {N : ℕ} (hN : 7≤N) (v e : ℕ→ℝ)
    {u y : ℝ} (hy : 54≤y)
    (hNv : ∀ i∈V,(N : ℝ)+2≤v i) (hvG : ∀ i∈V,v i≤4*((N : ℝ)+1))
    (hO : ∀ i∈V,∀ j∈O i,10000*(2 : ℝ)^j≤v i)
    (hphysical : ∀ i∈V,∀ j∈O i,2*log N≤10000*(2 : ℝ)^j)
    (he : ∀ i∈V,|e i|=1)
    (hL : (11/8 : ℝ)*N≤SquarefreeVaughanLogSource.length u N)
    (hhi : ∀ i∈V,v i+Real.pi/y≤(203/100 : ℝ)*N)
    (hpeak : ∀ i∈V,sin (y*v i)=0) (hsign : ∀ i∈V,e i*cos (y*v i)≤0) :
    -unpaidCountSupplyPrice N*(∑ i∈V,amplitude N (v i)/v i)≤
      ∑ i∈V,∑ j∈O i,
        ((∑ n∈countPeriod S N (10000*(2 : ℝ)^j) (v i) y,signedPart (e i)
          (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
          (SquarefreeVaughanLogSource.length u N) y N n)+
         (∑ n∈countBoundary S N (10000*(2 : ℝ)^j) (v i) y\Pplus i j,signedPart 1
          (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
          (SquarefreeVaughanLogSource.length u N) y N n)+
         (∑ n∈countBoundary S N (10000*(2 : ℝ)^j) (v i) y\Pminus i j,signedPart (-1)
          (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
          (SquarefreeVaughanLogSource.length u N) y N n)) := by
  have hrow i (hi : i∈V) j (hj : j∈O i) := countPeriod_boundary_floor S
    (Pplus i j) (Pminus i j) hN (he i hi) hy
    (show 10000≤10000*(2 : ℝ)^j by
      have hh := one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := j)
      nlinarith only [hh])
    ((hO i hi j hj).trans (hvG i hi)) (hphysical i hi j hj) (hNv i hi) hL
    (hhi i hi) (hpeak i hi) (hsign i hi)
  have hs := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (hrow i hi))
  have hc := global_lower_count_cost_le V O N v (by norm_num : (1 : ℝ)≤10000) hNv hvG hO
  simp only [neg_mul,Finset.sum_neg_distrib] at hs
  simpa only [neg_mul] using (neg_le_neg hc).trans hs

theorem core_count_lt {u : ℝ} {N K n : ℕ} (hn : n∈coreBand u N K) :
    n.primeFactors.card<K := by
  simp only [coreBand,ZetaRieszTypeII.narrowBand,LogarithmicDeviation.deviationBand,
    ZetaRieszDominantAllocation.nondominantBand,ZetaRieszMaskSupport.retainedBand,
    ZetaRieszCompanionMask.originalMask,ZetaRieszHarmonicWindow.fewBand,
    Finset.mem_filter,Finset.mem_sdiff] at hn
  tauto

/-- Extracting the cofactor from an actual original squarefree label
retains the ORIGINAL count cutoff under the complete owner extension. -/
theorem countPeriod_count_lt_from_seeds {S : Finset ℕ} {u H v y : ℝ} {N K n : ℕ}
    (hS : ∀ n∈S,n∈coreBand u N K ∧ Squarefree n) (hn : n∈countPeriod S N H v y) :
    n.primeFactors.card<K := by
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hh := Finset.mem_filter.mp ha
  obtain ⟨n₀,hn₀,he⟩ := Finset.mem_image.mp hh.1
  have hd := canonical_owner_data (hS n₀ hn₀).2
    (ZetaRieszJointPrimeEnergy.core_count (hS n₀ hn₀).1)
  have hc := owner_fibre_count hh.2.1 hh.2.2.2.2.2.2.2 hp
  rw [hc.2,←he,←hd.2.2.2.1]
  exact core_count_lt (hS n₀ hn₀).1

/-- This core containment needs only the ORIGINAL seed support. No
comparison between the old paid count threshold and the dyadic cutoff
is assumed, and no completed label loses the actual count mask. -/
theorem countPeriod_subset_core_from_seeds (j : ℕ) (hj : 32≤j) (S : Finset ℕ)
    {u H v y : ℝ} (hu : 1/2<u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤y) (hv : 100≤v)
    (hS : ∀ n∈S,n∈coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) ∧ Squarefree n)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j≤SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hlo : (39/20 : ℝ)*dyadicMomentOrder j≤v-Real.pi/y)
    (hhi : v+Real.pi/y≤(203/100 : ℝ)*dyadicMomentOrder j) :
    countPeriod S (dyadicMomentOrder j) H v y⊆coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  intro n hn
  obtain ⟨hs,hc,_,_,hT,hmax⟩ := countPeriod_data hy hv hn
  exact mem_core_of_share_le j hj hu hU hL hs (by omega)
    (countPeriod_count_lt_from_seeds hS hn) (hlo.trans_lt hT.1) (hT.2.trans hhi) hmax

/-- The actual dense band of the existing core, with no spread, occupied
bin, roughness or parity condition. This is a literal support filter. -/
def denseBand (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (coreBand u N K).filter (fun n => Squarefree n ∧ 8≤n.primeFactors.card ∧
    5*log ((N : ℝ)+1)+2≤(n.primeFactors.card : ℝ) ∧
    n.primeFactors.card<ZetaRieszLogCountBudget.countThreshold N)

/-- Complete fibres seeded by this dense band remain INSIDE that SAME
literal band. Thus no external prime or previously spent head is added. -/
theorem countPeriod_subset_denseBand (j : ℕ) (hj : 32≤j)
    {u H v y : ℝ} (hu : 1/2<u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤y) (hv : 100≤v)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j≤SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hlo : (39/20 : ℝ)*dyadicMomentOrder j≤v-Real.pi/y)
    (hhi : v+Real.pi/y≤(203/100 : ℝ)*dyadicMomentOrder j) :
    countPeriod (denseBand u (dyadicMomentOrder j) (dyadicPrimeCount j))
      (dyadicMomentOrder j) H v y⊆denseBand u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  intro n hn
  have hd := countPeriod_data hy hv hn
  have hcore := countPeriod_subset_core_from_seeds j hj _ hu hU hy hv
    (fun n hn => ⟨(Finset.mem_filter.mp hn).1,(Finset.mem_filter.mp hn).2.1⟩) hL hlo hhi hn
  exact Finset.mem_filter.mpr ⟨hcore,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1⟩

/-- The physical lower cutoff eventually follows from the ALREADY
proved unpaid-count scale. This is uniform over all literal active owner
scales and avoids deleting a growing exceptional population. -/
theorem eventually_physical_from_count_scale :
    ∀ᶠ N : ℕ in atTop,∀ H v : ℝ,(N : ℝ)+2≤v →
      v≤128*H*log ((N : ℝ)+1) → 2*log N≤H := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 1 2 one_ne_zero).comp hn
  filter_upwards [ht.eventually_lt_const (by norm_num : (0 : ℝ)<1/256),
    eventually_ge_atTop (2 : ℕ)] with N hsmall hN H v hNv hscale
  have hN0 : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hx : 1<(N : ℝ)+1 := by linarith
  have hl : 0<log ((N : ℝ)+1) := log_pos hx
  have hln : log N≤log ((N : ℝ)+1) := log_le_log hN0 (by linarith)
  have hsmall' : 256*(log ((N : ℝ)+1))^2<(N : ℝ)+2 := by
    have hh := (div_lt_iff₀ (show 0<1*((N : ℝ)+1)+1 by linarith)).mp hsmall
    nlinarith only [hh]
  have hh : 2*log ((N : ℝ)+1)≤H := by
    nlinarith only [hsmall',hNv,hscale,hl]
  linarith only [hh,hln]

/-- A nonempty literal owner or clipped-second-owner population selects
only scales below its own radial centre. No count of unrelated scales is
charged in the global cost. -/
theorem active_scale_le_center {S : Finset ℕ} {N : ℕ} {H v y : ℝ}
    (hy : 54≤y) (hv : 100≤v)
    (hactive : countCofactors S N H v y≠∅ ∨ countBoundary S N H v y≠∅) : H≤v := by
  rcases hactive with ha | hd
  · obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr ha
    have hh := (Finset.mem_filter.mp ha).2
    have hπ : 0≤Real.pi/y := by positivity
    linarith only [hh.2.2.2.2.2.1.1,hπ,log_natCast_nonneg a]
  · obtain ⟨n,hn⟩ := Finset.nonempty_iff_ne_empty.mpr hd
    have hh := (Finset.mem_filter.mp hn).2
    have hc : 3≤n.primeFactors.card := by have := hh.2.1; omega
    have hd := canonical_owner_data hh.1 hc
    have hq := (close_second_owner hh.1 hc hh.2.2.2.2.2.1).1
    have hpn := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2≤n.primeFactors.card)
    have hqn := (Nat.prime_of_mem_primeFactors hq).mem_primeFactors
      ((Nat.dvd_of_mem_primeFactors hq).trans
        (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hpn))) hh.1.ne_zero
    have hqp : log (largestPrime (n/largestPrime n))≤log (largestPrime n) :=
      log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos)
        (by exact_mod_cast hd.2.2.2.2.1 _ hqn)
    have hqaNat : largestPrime (n/largestPrime n)≤n/largestPrime n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2.2.1.ne_zero) (Nat.dvd_of_mem_primeFactors hq)
    have hqa : log (largestPrime (n/largestPrime n))≤log (n/largestPrime n : ℕ) :=
      log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos)
        (by exact_mod_cast hqaNat)
    have hlog : log n=log (largestPrime n)+log (n/largestPrime n : ℕ) := by
      conv_lhs => rw [← hd.2.1,Nat.cast_mul,log_mul
        (by exact_mod_cast hd.1.ne_zero) (by exact_mod_cast hd.2.2.1.ne_zero)]
    have hπ : Real.pi/y≤1/16 :=
      (div_le_iff₀ (by linarith : 0<y)).mpr (by nlinarith [Real.pi_lt_d4])
    linarith only [hh.2.2.2.2.2.2.1,hqp,hqa,hlog,hh.2.2.2.2.1.2,hπ,hv]

/-- The terminal literal signed estimate joins every selected active
count, owner scale, clipped-start population and radial period. The
physical prime cutoff and owner scale follow automatically; only the
actual phase-period geometry and original length remain as premises. -/
theorem eventually_global_countPeriod_floor :
    ∀ᶠ N : ℕ in atTop,∀ (V : Finset ℕ) (O : ℕ→Finset ℕ) (S : Finset ℕ)
      (Pplus Pminus : ℕ→ℕ→Finset ℕ) (v e : ℕ→ℝ) (u y : ℝ),
      54≤y →
      (∀ i∈V,(N : ℝ)+2≤v i) → (∀ i∈V,v i≤4*((N : ℝ)+1)) →
      (∀ i∈V,∀ j∈O i,countCofactors S N (10000*(2 : ℝ)^j) (v i) y≠∅ ∨
        countBoundary S N (10000*(2 : ℝ)^j) (v i) y≠∅) →
      (∀ i∈V,|e i|=1) →
      (11/8 : ℝ)*N≤SquarefreeVaughanLogSource.length u N →
      (∀ i∈V,v i+Real.pi/y≤(203/100 : ℝ)*N) →
      (∀ i∈V,sin (y*v i)=0) → (∀ i∈V,e i*cos (y*v i)≤0) →
      -unpaidCountSupplyPrice N*(∑ i∈V,amplitude N (v i)/v i)≤
        ∑ i∈V,∑ j∈O i,
          ((∑ n∈countPeriod S N (10000*(2 : ℝ)^j) (v i) y,signedPart (e i)
            (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
            (SquarefreeVaughanLogSource.length u N) y N n)+
           (∑ n∈countBoundary S N (10000*(2 : ℝ)^j) (v i) y\Pplus i j,signedPart 1
            (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
            (SquarefreeVaughanLogSource.length u N) y N n)+
           (∑ n∈countBoundary S N (10000*(2 : ℝ)^j) (v i) y\Pminus i j,signedPart (-1)
            (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
            (SquarefreeVaughanLogSource.length u N) y N n)) := by
  filter_upwards [eventually_physical_from_count_scale,eventually_ge_atTop (1000 : ℕ)]
    with N hphysical hN V O S Pplus Pminus v e u y hy hNv hvG hactive he hL hhi hpeak hsign
  have hv100 i (hi : i∈V) : 100≤v i := by
    have hNR : (1000 : ℝ)≤N := by exact_mod_cast hN
    linarith only [hNv i hi,hNR]
  have hO i (hi : i∈V) j (hj : j∈O i) := active_scale_le_center hy (hv100 i hi) (hactive i hi j hj)
  have hscale i (hi : i∈V) j (hj : j∈O i) : v i≤128*(10000*(2 : ℝ)^j)*log ((N : ℝ)+1) := by
    have hH : 10000≤10000*(2 : ℝ)^j := by
      have hh := one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := j)
      nlinarith only [hh]
    rcases hactive i hi j hj with ha | hd
    · obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr ha
      exact countCofactors_scale (by omega : 7≤N) (by linarith : 5000≤10000*(2 : ℝ)^j) hy ha
    · obtain ⟨n,hn⟩ := Finset.nonempty_iff_ne_empty.mpr hd
      exact countBoundary_scale (by omega : 7≤N) (by linarith : 1≤10000*(2 : ℝ)^j) (hv100 i hi) hy hn
  exact global_countPeriod_floor V O S Pplus Pminus (by omega : 7≤N) v e hy hNv hvG hO
    (fun i hi j hj => hphysical _ _ (hNv i hi) (hscale i hi j hj)) he hL hhi hpeak hsign

/-- A finite grid of ONLY actual active owner/second-owner scales. -/
def denseScaleGrid (S : Finset ℕ) (N : ℕ) (v y : ℝ) : Finset ℕ :=
  (Finset.range (⌊v⌋₊+1)).filter (fun i =>
    countCofactors S N (10000*(2 : ℝ)^i) v y≠∅ ∨
    countBoundary S N (10000*(2 : ℝ)^i) v y≠∅)

theorem mem_denseScaleGrid (S : Finset ℕ) (N : ℕ) {v y : ℝ}
    (hy : 54≤y) (hv : 100≤v) {i : ℕ}
    (hactive : countCofactors S N (10000*(2 : ℝ)^i) v y≠∅ ∨
      countBoundary S N (10000*(2 : ℝ)^i) v y≠∅) :
    i∈denseScaleGrid S N v y := by
  have hs := active_scale_le_center hy hv hactive
  have hi : (i : ℝ)<(2 : ℝ)^i := by
    exact_mod_cast (Nat.lt_two_pow_self : i < 2^i)
  have hp : 0≤(2 : ℝ)^i := by positivity
  have hiv : (i : ℝ)≤v := by nlinarith only [hi,hp,hs]
  have hfloor : i≤⌊v⌋₊ := Nat.le_floor hiv
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hactive⟩

/-- Both staggered full-period grids cover the ACTUAL dense core
interior, at arbitrary growing count. The ONLY geometric failures are
the paid radial edges, large-owner sector and small-owner population.
Near-tied owners are included explicitly, with a unique second-prime scale. -/
theorem dense_label_grid_cover {u : ℝ} {N K n : ℕ}
    (hn : n∈denseBand u N K) (hN : 4000≤N) {y b : ℝ} (hy : 54≤y)
    (hb : Real.pi/y≤b ∧ b≤2*Real.pi/y)
    (hlo : (244/125 : ℝ)*N<log n) (hhi : log n≤(2029/1000 : ℝ)*N)
    (hshare : log (largestPrime n)≤(601/1000 : ℝ)*log n)
    (hlarge : 20000<log (largestPrime n)) :
    ∃ i∈ZetaRieszFiveSignCoverFloor.completeGrid N b y,
      ∃ j∈denseScaleGrid (denseBand u N K) N (ZetaRieszMultiPeriodSix.center b y i) y,
        n∈countPeriod (denseBand u N K) N (10000*(2 : ℝ)^j)
          (ZetaRieszMultiPeriodSix.center b y i) y ∨
        n∈countBoundary (denseBand u N K) N (10000*(2 : ℝ)^j)
          (ZetaRieszMultiPeriodSix.center b y i) y := by
  obtain ⟨i,hi,hT⟩ := ZetaRieszFiveSignCoverFloor.exists_completeGrid_period hN hy hb hlo hhi
  have hv : 100≤ZetaRieszMultiPeriodSix.center b y i := by
    have hNR : (4000 : ℝ)≤N := by exact_mod_cast hN
    have hπ : Real.pi/y≤1/16 :=
      (div_le_iff₀ (by linarith : 0<y)).mpr (by nlinarith [Real.pi_lt_d4])
    linarith only [hT.2,hlo,hNR,hπ]
  obtain ⟨_,hs,hc,hclo,hchi⟩ := Finset.mem_filter.mp hn
  have hh := dense_label_full_cover (denseBand u N K) hn hs hc hclo hchi hy hv hT hshare hlarge
  refine ⟨i,hi,?_⟩
  rcases hh with ⟨j,hp⟩ | ⟨j,hd⟩
  · have ha : countCofactors (denseBand u N K) N (10000*(2 : ℝ)^j)
        (ZetaRieszMultiPeriodSix.center b y i) y≠∅ := by
      intro hem
      simp only [countPeriod,hem,Finset.biUnion_empty,Finset.notMem_empty] at hp
    exact ⟨j,mem_denseScaleGrid _ _ hy hv (Or.inl ha),Or.inl hp⟩
  · exact ⟨j,mem_denseScaleGrid _ _ hy hv
      (Or.inr (Finset.ne_empty_of_mem hd)),Or.inr hd⟩

/-- The finite active grid leaves no support/scale hypothesis in the
signed aggregate inequality. This is a literal arithmetic estimate,
uniform over the original seed labels and all count parities. -/
theorem eventually_dense_grid_floor :
    ∀ᶠ N : ℕ in atTop,∀ (V : Finset ℕ) (S : Finset ℕ)
      (Pplus Pminus : ℕ→ℕ→Finset ℕ) (v e : ℕ→ℝ) (u y : ℝ),
      54≤y →
      (∀ i∈V,(N : ℝ)+2≤v i) → (∀ i∈V,v i≤4*((N : ℝ)+1)) →
      (∀ i∈V,|e i|=1) →
      (11/8 : ℝ)*N≤SquarefreeVaughanLogSource.length u N →
      (∀ i∈V,v i+Real.pi/y≤(203/100 : ℝ)*N) →
      (∀ i∈V,sin (y*v i)=0) → (∀ i∈V,e i*cos (y*v i)≤0) →
      -unpaidCountSupplyPrice N*(∑ i∈V,amplitude N (v i)/v i)≤
        ∑ i∈V,∑ j∈denseScaleGrid S N (v i) y,
          ((∑ n∈countPeriod S N (10000*(2 : ℝ)^j) (v i) y,signedPart (e i)
            (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
            (SquarefreeVaughanLogSource.length u N) y N n)+
           (∑ n∈countBoundary S N (10000*(2 : ℝ)^j) (v i) y\Pplus i j,signedPart 1
            (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
            (SquarefreeVaughanLogSource.length u N) y N n)+
           (∑ n∈countBoundary S N (10000*(2 : ℝ)^j) (v i) y\Pminus i j,signedPart (-1)
            (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n})
            (SquarefreeVaughanLogSource.length u N) y N n)) := by
  filter_upwards [eventually_global_countPeriod_floor] with N hfloor
    V S Pplus Pminus v e u y hy hNv hvG he hL hhi hpeak hsign
  exact hfloor V (fun i => denseScaleGrid S N (v i) y) S Pplus Pminus v e u y hy hNv hvG
    (fun _i _hi _j hj => (Finset.mem_filter.mp hj).2) he hL hhi hpeak hsign

/-- The canonical second prime assigns a near-owner label to just ONE
dyadic scale, even if several pairs witness the ownership crossing. -/
theorem countBoundary_scale_disjoint (S : Finset ℕ) (N : ℕ) {B v y : ℝ}
    (hB : 0<B) {i j : ℕ} (hij : i≠j) :
    Disjoint (countBoundary S N (B*(2 : ℝ)^i) v y)
      (countBoundary S N (B*(2 : ℝ)^j) v y) := by
  apply Finset.disjoint_left.mpr
  intro n hn hm
  have hi := (Finset.mem_filter.mp hn).2.2.2.2.2.2.2
  have hj := (Finset.mem_filter.mp hm).2.2.2.2.2.2.2
  rcases lt_or_gt_of_ne hij with h | h
  · have hp := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (show i + 1 ≤ j by omega)) hB.le
    rw [pow_succ] at hp
    nlinarith only [hp,hi.2,hj.1]
  · have hp := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (show j + 1 ≤ i by omega)) hB.le
    rw [pow_succ] at hp
    nlinarith only [hp,hj.2,hi.1]

theorem countBoundary_radial_disjoint (S T : Finset ℕ) (N : ℕ) {H J v w y : ℝ}
    (hsep : v+Real.pi/y≤w-Real.pi/y) :
    Disjoint (countBoundary S N H v y) (countBoundary T N J w y) := by
  apply Finset.disjoint_left.mpr
  intro n hn hm
  have hv := (Finset.mem_filter.mp hn).2.2.2.2.2.1
  have hw := (Finset.mem_filter.mp hm).2.2.2.2.2.1
  linarith only [hv.2,hw.1,hsep]

/-- These finite unions only assemble the ALREADY defined literal rows.
They change neither weights, support nor prime-count masks. -/
def densePeriodGrid (S : Finset ℕ) (N : ℕ) (b y : ℝ) : Finset ℕ :=
  (ZetaRieszFiveSignCoverFloor.completeGrid N b y).biUnion (fun i =>
    (denseScaleGrid S N (ZetaRieszMultiPeriodSix.center b y i) y).biUnion
      (fun j => countPeriod S N (10000*(2 : ℝ)^j)
        (ZetaRieszMultiPeriodSix.center b y i) y))

/-- Actual canonical second-owner clips over all active scales and
complete radial phase periods; each original boundary label occurs once. -/
def denseBoundaryGrid (S : Finset ℕ) (N : ℕ) (b y : ℝ) : Finset ℕ :=
  (ZetaRieszFiveSignCoverFloor.completeGrid N b y).biUnion (fun i =>
    (denseScaleGrid S N (ZetaRieszMultiPeriodSix.center b y i) y).biUnion
      (fun j => countBoundary S N (10000*(2 : ℝ)^j)
        (ZetaRieszMultiPeriodSix.center b y i) y))

private theorem grid_center_gap {b y : ℝ} (hy : 0<y) {i j : ℕ} (hij : i<j) :
    ZetaRieszMultiPeriodSix.center b y i+Real.pi/y≤
      ZetaRieszMultiPeriodSix.center b y j-Real.pi/y := by
  have hh : (i : ℝ)+1≤j := by exact_mod_cast hij
  have hm := mul_le_mul_of_nonneg_right hh
    (show 0≤2*Real.pi/y by positivity)
  dsimp only [ZetaRieszMultiPeriodSix.center]
  rw [abs_of_pos hy]
  ring_nf at hm ⊢
  linarith only [hm]

private theorem grid_center_bounds {N : ℕ} (hN : 1000≤N) {b y : ℝ} (hy : 54≤y)
    {i : ℕ} (hi : i∈ZetaRieszFiveSignCoverFloor.completeGrid N b y) :
    100≤ZetaRieszMultiPeriodSix.center b y i ∧
    (N : ℝ)+2≤ZetaRieszMultiPeriodSix.center b y i ∧
    ZetaRieszMultiPeriodSix.center b y i≤4*((N : ℝ)+1) := by
  have hd := (Finset.mem_filter.mp hi).2
  have hNR : (1000 : ℝ)≤N := by exact_mod_cast hN
  have hp : 0≤Real.pi/y := by positivity
  constructor
  · linarith only [hd.1,hNR,hp]
  constructor <;> linarith only [hd.1,hd.2.1,hNR,hp]

private theorem nested_grid_sum (I : Finset ℕ) (O : ℕ→Finset ℕ)
    (P : ℕ→ℕ→Finset ℕ) (f : ℕ→ℝ)
    (hs : ∀ i∈I,(O i : Set ℕ).Pairwise (fun j k => Disjoint (P i j) (P i k)))
    (hr : ∀ i∈I,∀ k∈I,i≠k → ∀ j∈O i,∀ l∈O k,Disjoint (P i j) (P k l)) :
    (∑ n∈I.biUnion (fun i => (O i).biUnion (P i)),f n)=
      ∑ i∈I,∑ j∈O i,∑ n∈P i j,f n := by
  rw [Finset.sum_biUnion (by
    intro i hi k hk hne
    apply Finset.disjoint_left.mpr
    intro n hn hm
    obtain ⟨j,hj,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨l,hl,hm⟩ := Finset.mem_biUnion.mp hm
    exact Finset.disjoint_left.mp (hr i hi k hk hne j hj l hl) hn hm)]
  exact Finset.sum_congr rfl (fun i hi => Finset.sum_biUnion (hs i hi))

theorem densePeriodGrid_sum (S : Finset ℕ) {N : ℕ} (hN : 1000≤N)
    {b y : ℝ} (hy : 54≤y) (f : ℕ→ℝ) :
    (∑ n∈densePeriodGrid S N b y,f n)=
      ∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N b y,
        ∑ j∈denseScaleGrid S N (ZetaRieszMultiPeriodSix.center b y i) y,
          ∑ n∈countPeriod S N (10000*(2 : ℝ)^j)
            (ZetaRieszMultiPeriodSix.center b y i) y,f n := by
  apply nested_grid_sum
  · intro i _hi j _hj k _hk hne
    exact countPeriod_scale_disjoint S N (by norm_num) hne
  · intro i hi k hk hne j _hj l _hl
    have hv := (grid_center_bounds hN hy hi).1
    have hw := (grid_center_bounds hN hy hk).1
    rcases lt_or_gt_of_ne hne with h | h
    · exact countPeriod_radial_disjoint S S N hy hv hw
        (grid_center_gap (by linarith) h)
    · exact (countPeriod_radial_disjoint S S N hy hw hv
        (grid_center_gap (by linarith) h)).symm

theorem denseBoundaryGrid_sum (S X : Finset ℕ) (N : ℕ) {b y : ℝ} (hy : 54≤y)
    (f : ℕ→ℝ) :
    (∑ n∈denseBoundaryGrid S N b y\X,f n)=
      ∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N b y,
        ∑ j∈denseScaleGrid S N (ZetaRieszMultiPeriodSix.center b y i) y,
          ∑ n∈countBoundary S N (10000*(2 : ℝ)^j)
            (ZetaRieszMultiPeriodSix.center b y i) y\X,f n := by
  have he : denseBoundaryGrid S N b y\X=
      (ZetaRieszFiveSignCoverFloor.completeGrid N b y).biUnion (fun i =>
        (denseScaleGrid S N (ZetaRieszMultiPeriodSix.center b y i) y).biUnion (fun j =>
          countBoundary S N (10000*(2 : ℝ)^j) (ZetaRieszMultiPeriodSix.center b y i) y\X)) := by
    ext n
    simp only [denseBoundaryGrid,Finset.mem_biUnion,Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨i,hi,j,hj,hn⟩,hX⟩
      exact ⟨i,hi,j,hj,hn,hX⟩
    · rintro ⟨i,hi,j,hj,hn,hX⟩
      exact ⟨⟨i,hi,j,hj,hn⟩,hX⟩
  rw [he]
  apply nested_grid_sum
  · intro i _hi j _hj k _hk hne
    exact (countBoundary_scale_disjoint S N (by norm_num) hne).mono
      Finset.sdiff_subset Finset.sdiff_subset
  · intro i _hi k _hk hne j _hj l _hl
    apply Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset
    rcases lt_or_gt_of_ne hne with h | h
    · exact countBoundary_radial_disjoint S S N (grid_center_gap (by linarith) h)
    · exact (countBoundary_radial_disjoint S S N (grid_center_gap (by linarith) h)).symm

theorem denseBoundaryGrid_subset (S : Finset ℕ) (N : ℕ) (b y : ℝ) :
    denseBoundaryGrid S N b y⊆S := by
  intro n hn
  obtain ⟨i,_hi,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨j,_hj,hn⟩ := Finset.mem_biUnion.mp hn
  exact (Finset.mem_filter.mp hn).1

theorem densePeriodGrid_subset_denseBand (j : ℕ) (hj : 32≤j) {u b y : ℝ}
    (hu : 1/2<u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤y)
    (hN : 1000≤dyadicMomentOrder j)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j≤SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    densePeriodGrid (denseBand u (dyadicMomentOrder j) (dyadicPrimeCount j))
      (dyadicMomentOrder j) b y⊆denseBand u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  intro n hn
  obtain ⟨i,hi,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨k,_hk,hn⟩ := Finset.mem_biUnion.mp hn
  have hd := (Finset.mem_filter.mp hi).2
  exact countPeriod_subset_denseBand j hj hu hU hy (grid_center_bounds hN hy hi).1
    hL hd.1 hd.2.1 hn

private theorem family_two_cover_ledger (A : ℕ→Finset ℕ) (S P Q : Finset ℕ)
    (L y : ℝ) (N : ℕ) (hP : P⊆S) (hQ : Q⊆S) :
    (∑ n∈S,residualCoefficient (A n) L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re=
      (∑ n∈P,signedPart 1 (A n) L y N n)+
      (∑ n∈Q,signedPart (-1) (A n) L y N n)+
      (∑ n∈S\P,signedPart 1 (A n) L y N n)+
      (∑ n∈S\Q,signedPart (-1) (A n) L y N n) := by
  rw [Complex.re_sum]
  simp_rw [← signedPart_add]
  rw [Finset.sum_add_distrib]
  have hp := Finset.sum_sdiff hP (f := fun n => signedPart 1 (A n) L y N n)
  have hq := Finset.sum_sdiff hQ (f := fun n => signedPart (-1) (A n) L y N n)
  linarith only [hp,hq]

/-- This cancellation spends no negative orientation at a positive-grid
boundary (and conversely). It prevents duplicate boundary credits. -/
theorem countBoundary_sdiff_seed (S : Finset ℕ) (N : ℕ) (H v y : ℝ) :
    countBoundary S N H v y\S=∅ :=
  Finset.sdiff_eq_empty_iff_subset.mpr (Finset.filter_subset _ _)

/-- A LITERAL two-grid signed floor for the entire unpaid dense band.
Only the two explicitly displayed unmatched geometric populations remain;
all complete owner periods AND canonical near-owner clips have ONE
vanishing relative price. No rowwise signed hypothesis is assumed.
The owner allocation is unchanged and both arithmetic signs are joined. -/
theorem eventually_dense_two_grid_floor {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤y) :
    ∀ᶠ j : ℕ in atTop,
      let N := dyadicMomentOrder j
      let K := dyadicPrimeCount j
      let S := denseBand u N K
      let A := fun n => ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n}
      let L := SquarefreeVaughanLogSource.length u N
      let b := Real.pi/y
      let P := densePeriodGrid S N b y
      let Q := densePeriodGrid S N (b+Real.pi/y) y
      let D := denseBoundaryGrid S N b y
      let F := denseBoundaryGrid S N (b+Real.pi/y) y;
      (∑ n∈S\(P∪D),signedPart 1 (A n) L y N n)+
        (∑ n∈S\(Q∪F),signedPart (-1) (A n) L y N n)-
        unpaidCountSupplyPrice N*
          ((∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N b y,
            amplitude N (ZetaRieszMultiPeriodSix.center b y i)/
              ZetaRieszMultiPeriodSix.center b y i)+
           (∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N (b+Real.pi/y) y,
            amplitude N (ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y i)/
              ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y i))≤
          (∑ n∈S,residualCoefficient (A n) L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hy0 : 0<y := by linarith
  have hpeak : cos (y*(Real.pi/y))=-1 := by
    rw [mul_div_cancel₀ _ hy0.ne',Real.cos_pi]
  have hroom := hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  filter_upwards [tendsto_dyadicMomentOrder.eventually eventually_dense_grid_floor,
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0<u) (by norm_num : (0 : ℝ)≤11/16) hroom),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hf hL hN hj
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  let S := denseBand u N K
  let A := fun n => ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n}
  let L := SquarefreeVaughanLogSource.length u N
  let b := Real.pi/y
  let P := densePeriodGrid S N b y
  let Q := densePeriodGrid S N (b+Real.pi/y) y
  let D := denseBoundaryGrid S N b y
  let F := denseBoundaryGrid S N (b+Real.pi/y) y
  let I := ZetaRieszFiveSignCoverFloor.completeGrid N b y
  let J := ZetaRieszFiveSignCoverFloor.completeGrid N (b+Real.pi/y) y
  norm_num only at hL
  have hp := hf I S (fun _ _ => P) (fun _ _ => S)
    (ZetaRieszMultiPeriodSix.center b y) (fun _ => 1) u y hy
    (fun _ hi => (grid_center_bounds hN hy hi).2.1)
    (fun _ hi => (grid_center_bounds hN hy hi).2.2)
    (by intros; norm_num) hL
    (fun _ hi => (Finset.mem_filter.mp hi).2.2.1)
    (fun i _ => (staggered_peaks hy0 hpeak i).1.1)
    (by intro i _; rw [one_mul,(staggered_peaks hy0 hpeak i).1.2]; norm_num)
  have hq := hf J S (fun _ _ => S) (fun _ _ => Q)
    (ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y) (fun _ => -1) u y hy
    (fun _ hi => (grid_center_bounds hN hy hi).2.1)
    (fun _ hi => (grid_center_bounds hN hy hi).2.2)
    (by intros; norm_num) hL
    (fun _ hi => (Finset.mem_filter.mp hi).2.2.1)
    (fun i _ => (staggered_peaks hy0 hpeak i).2.1)
    (by intro i _; rw [(staggered_peaks hy0 hpeak i).2.2]; norm_num)
  simp only [countBoundary_sdiff_seed,Finset.sum_empty,add_zero,
    Finset.sum_add_distrib] at hp hq
  rw [← densePeriodGrid_sum S hN hy,
    ← denseBoundaryGrid_sum S P N hy] at hp
  rw [← densePeriodGrid_sum S hN hy,
    ← denseBoundaryGrid_sum S Q N hy] at hq
  have hP := densePeriodGrid_subset_denseBand j hj hu hU hy hN hL (b := b)
  have hQ := densePeriodGrid_subset_denseBand j hj hu hU hy hN hL (b := b+Real.pi/y)
  have he := family_two_cover_ledger A S P Q L y N hP hQ
  rw [ZetaRieszOwnerTieFloor.missed_boundary_split S D P
      (denseBoundaryGrid_subset S N b y) (fun n => signedPart 1 (A n) L y N n),
    ZetaRieszOwnerTieFloor.missed_boundary_split S F Q
      (denseBoundaryGrid_subset S N (b+Real.pi/y) y)
      (fun n => signedPart (-1) (A n) L y N n)] at he
  dsimp only
  change _≤(∑ n∈S,residualCoefficient (A n) L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
  change -unpaidCountSupplyPrice N*(∑ i∈I,
    amplitude N (ZetaRieszMultiPeriodSix.center b y i)/ZetaRieszMultiPeriodSix.center b y i)≤
      (∑ n∈P,signedPart 1 (A n) L y N n)+(∑ n∈D\P,signedPart 1 (A n) L y N n) at hp
  change -unpaidCountSupplyPrice N*(∑ i∈J,
    amplitude N (ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y i)/
      ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y i)≤
      (∑ n∈Q,signedPart (-1) (A n) L y N n)+
      (∑ n∈F\Q,signedPart (-1) (A n) L y N n) at hq
  linarith only [he,hp,hq]

/-- Every unmatched label has an EXPLICIT geometric cause: a paid radial
edge, a large-owner share, or a small-owner head. There is no anonymous
intermediate-count, bin, parity, roughness or clipped-phase remainder. -/
theorem dense_grid_unmatched_geometry {u : ℝ} {N K n : ℕ}
    (hN : 4000≤N) {b y : ℝ} (hy : 54≤y)
    (hb : Real.pi/y≤b ∧ b≤2*Real.pi/y)
    (hn : n∈denseBand u N K\
      (densePeriodGrid (denseBand u N K) N b y∪
       denseBoundaryGrid (denseBand u N K) N b y)) :
    ¬((244/125 : ℝ)*N<log n ∧ log n≤(2029/1000 : ℝ)*N) ∨
      (601/1000 : ℝ)*log n<log (largestPrime n) ∨
      log (largestPrime n)≤20000 := by
  obtain ⟨hn,hnot⟩ := Finset.mem_sdiff.mp hn
  by_contra h
  push Not at h
  obtain ⟨i,hi,k,hk,hp|hd⟩ := dense_label_grid_cover hn hN hy hb h.1.1 h.1.2 h.2.1 h.2.2
  · exact hnot (Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr
      ⟨i,hi,Finset.mem_biUnion.mpr ⟨k,hk,hp⟩⟩)))
  · exact hnot (Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
      ⟨i,hi,Finset.mem_biUnion.mpr ⟨k,hk,hd⟩⟩)))

/-- The original upper count and radial window force the largest-prime
logarithm to infinity, uniformly over ALL labels in this unpaid band.
Thus no small-owner head has to be discarded by an absolute envelope. -/
theorem eventually_dense_owner_large :
    ∀ᶠ N : ℕ in atTop,∀ (u : ℝ) (K n : ℕ),n∈denseBand u N K →
      20000<log (largestPrime n) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 1 1 one_ne_zero).comp hn
  filter_upwards [ht.eventually_lt_const (by norm_num : (0 : ℝ)<1/640000),
    eventually_ge_atTop (7 : ℕ)] with N hsmall hN u K n hn
  obtain ⟨hc,hs,_h8,_hcnt,hct⟩ := Finset.mem_filter.mp hn
  have hlo := (Finset.mem_filter.mp hc).2.1
  have hNR : (7 : ℝ)≤N := by exact_mod_cast hN
  have hx : 1<(N : ℝ)+1 := by linarith only [hNR]
  have hl : 0≤log ((N : ℝ)+1) := log_nonneg hx.le
  have hcnt : (n.primeFactors.card : ℝ)≤16*log ((N : ℝ)+1) :=
    (show (n.primeFactors.card : ℝ)≤ZetaRieszLogCountBudget.countThreshold N by
      exact_mod_cast hct.le).trans (paid_count_threshold_le hN)
  have hpoint p (hp : p∈n.primeFactors) : log p≤log (largestPrime n) := log_le_log
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    (by exact_mod_cast ZetaRieszPolynomialOwnerPayment.prime_le_largestPrime hp)
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_const,nsmul_eq_mul,← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs] at hsum
  have hsmall' : 640000*log ((N : ℝ)+1)<(N : ℝ)+2 := by
    have hh := (div_lt_iff₀ (show 0<1*((N : ℝ)+1)+1 by linarith)).mp hsmall
    norm_num only [pow_one,one_mul] at hh
    nlinarith only [hh]
  by_contra hlarge
  have hlarge' : log (largestPrime n)≤20000 := le_of_not_gt hlarge
  have hh := mul_le_mul_of_nonneg_left hlarge' (Nat.cast_nonneg n.primeFactors.card)
  have hh' := mul_le_mul_of_nonneg_right hcnt (by norm_num : (0 : ℝ)≤20000)
  nlinarith only [hsmall',hlo,hsum,hh,hh',hNR]

/-- ANY literal signed subset of an unmatched dense-grid population has
only the already certified radial/large-owner source errors. This pays the
exterior masks, not the retained resonant sum or its absolute allowance. -/
theorem exists_dense_unmatched_bound {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤y) :
    ∃ r C : ℝ,0≤r ∧ r<1 ∧ 0≤C ∧
      ∀ᶠ j : ℕ in atTop,∀ (b : ℝ) (G : Finset ℕ),
        (Real.pi/y≤b ∧ b≤2*Real.pi/y) →
        let N := dyadicMomentOrder j
        let K := dyadicPrimeCount j
        let S := denseBand u N K
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N;
        G⊆S\(densePeriodGrid S N b y∪denseBoundaryGrid S N b y) →
        ‖(u : ℂ)^(N+1)*∑ n∈G,residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n‖≤
          2*zetaMoebiusLogMajorantMass (1+1/262144)*exp (-(N : ℝ)/1000000)+r^N*C := by
  obtain ⟨r,C,hr,hr1,hC,houter⟩ := ZetaRieszFiveSignCoverFloor.exists_outer_subset_bound
  refine ⟨r,C,hr,hr1,hC,?_⟩
  filter_upwards [tendsto_dyadicMomentOrder.eventually eventually_dense_owner_large,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hlarge hN hj
  intro b G hb
  dsimp only
  intro hG
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  let S := denseBand u N K
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let dom := fun n : ℕ => Squarefree n ∧ 1<n ∧ ¬n.Prime ∧
    ∃ p∈n.primeFactors,p∈A ∧ eligibleCofactor p (n/p) ∧ (601/1000 : ℝ)*log n≤log p
  let D := G.filter dom
  let F := (G\D).filter (fun n : ℕ => ¬((244/125 : ℝ)*N<log n ∧ log n≤(2029/1000 : ℝ)*N))
  have he : (∑ n∈G,f n)=(∑ n∈D,f n)+(∑ n∈F,f n) := by
    have hs := Finset.sum_sdiff (Finset.filter_subset dom G) (f := f)
    have hf : (∑ n∈F,f n)=∑ n∈G\D,f n := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro n hn hnotF
      obtain ⟨hnG,hnotD⟩ := Finset.mem_sdiff.mp hn
      obtain ⟨hnS,_⟩ := Finset.mem_sdiff.mp (hG hnG)
      have hnCore := (Finset.mem_filter.mp hnS).1
      have hnotdom : ¬dom n := fun hd => hnotD (Finset.mem_filter.mpr ⟨hnG,hd⟩)
      have hgeo : (244/125 : ℝ)*N<log n ∧ log n≤(2029/1000 : ℝ)*N := by
        by_contra hg
        exact hnotF (Finset.mem_filter.mpr ⟨hn,hg⟩)
      have hgeom := dense_grid_unmatched_geometry hN hy hb (hG hnG)
      have howner : (601/1000 : ℝ)*log n<log (largestPrime n) :=
        (hgeom.resolve_left (not_not.mpr hgeo)).resolve_right
          (not_le.mpr (hlarge u K n hnS))
      have hz : residualCoefficient A L N n=0 := by
        by_contra hzero
        have hh := ZetaRieszJointDominantFloor.Refined.remaining_prime_log_lt j hj u
          (Finset.mem_filter.mpr ⟨hnCore,hnotdom⟩) hzero
          (largestPrime n) (ZetaRieszOwnedCells.largestPrime_mem_of_two
            (by have hc := (Finset.mem_filter.mp hnS).2.2.1; omega))
        exact (not_lt_of_ge howner.le) hh
      simp only [f,hz,zero_mul]
    rw [← hf] at hs
    change (∑ n∈F,f n)+(∑ n∈D,f n)=∑ n∈G,f n at hs
    exact hs.symm.trans (add_comm _ _)
  have hLhi : L≤(139/100 : ℝ)*N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu.le (by omega : 2≤N)
    have hl : 2*log 2≤(139/100 : ℝ) := by linarith [log_two_lt_d9]
    exact h.trans (mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg _))
  have hd := ZetaRieszJointDominantFloor.Refined.norm_scaled_sum_le A D N (by omega) y
    (by linarith : 0≤u) hU (SquarefreeVaughanLogSource.length_pos u N) hLhi (by
      intro n hn
      obtain ⟨_,hs,hn1,hnp,p,hp,hpA,hel,hdom⟩ := Finset.mem_filter.mp hn
      refine ⟨hs,hn1,hnp,p,hp,hpA,hel,?_,hdom⟩
      have hp' := (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mp hpA
      have hlogcut : log (((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) : ℝ)=L := by
        simp only [L,SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
      change log p≤L
      rw [← hlogcut]
      exact (log_lt_log (by exact_mod_cast hp'.1.pos) (by exact_mod_cast hp'.2.2)).le)
  have hf := houter N A F y u (by linarith : 0≤u) hU (by
    intro n hn; exact (Finset.mem_filter.mp hn).2)
  change ‖(u : ℂ)^(N+1)*∑ n∈G,f n‖≤_
  rw [he,mul_add]
  exact (norm_add_le _ _).trans (add_le_add hd hf)

/-- The existing global nonowner error, named only to keep the signed
floor readable. This is already geometrically source-small. -/
def ownerPaymentError (N : ℕ) : ℝ :=
  (4*((N : ℝ)+1)/3)*(ZetaRieszNonownerAllocation.nonownerRate^N*
    ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))

theorem tendsto_ownerPaymentError : Tendsto ownerPaymentError atTop (𝓝 0) := by
  have hr : 0<ZetaRieszNonownerAllocation.nonownerRate := by
    unfold ZetaRieszNonownerAllocation.nonownerRate
    positivity
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1 hr
    (ZetaRieszNonownerAllocation.nonownerRate_bounds.2.trans (by norm_num))).mul_const
      ((4/3 : ℝ)*((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))
  simp only [pow_one,zero_mul] at ht
  convert ht using 1
  funext N
  dsimp only [ownerPaymentError]
  ring

private theorem norm_owner_subset_le (A G : Finset ℕ) {N : ℕ} {u y L B : ℝ}
    (hu : 0≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hL : 0<L)
    (hG : G⊆literalWindow N)
    (hB : ‖(u : ℂ)^(N+1)*∑ n∈G,residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖≤B) :
    ‖(u : ℂ)^(N+1)*∑ n∈G,residualCoefficient (A∩{largestPrime n}) L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖≤B+ownerPaymentError N := by
  have hb := ZetaRieszNonownerAllocation.residual_sub_owner_bound (fun _ => A) G
    (fun _ => 1) hL N hG (by intros; norm_num) y hu
    (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le)
  simp only [one_mul,sub_mul,Finset.sum_sub_distrib,mul_sub] at hb
  have ht := norm_sub_le
    ((u : ℂ)^(N+1)*∑ n∈G,residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)
    (((u : ℂ)^(N+1)*∑ n∈G,residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
     ((u : ℂ)^(N+1)*∑ n∈G,residualCoefficient (A∩{largestPrime n}) L N n*
       zetaPrimeLogKernel N (3/2+Complex.I*y) n))
  rw [sub_sub_cancel] at ht
  exact ht.trans (add_le_add hB hb)

private theorem family_positive_part_sum (A : ℕ→Finset ℕ) (D : Finset ℕ)
    (L y : ℝ) (N : ℕ) :
    (∑ n∈D,signedPart 1 (A n) L y N n)=
      (∑ n∈D.filter (fun n => 0<(SquarefreeVaughanLogSource.coefficient L n).re),
        residualCoefficient (A n) L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  rw [Complex.re_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : 0<(SquarefreeVaughanLogSource.coefficient L n).re
  · rw [if_pos hp,← signedPart_add]
    have hz : signedPart (-1) (A n) L y N n=0 := by
      simp only [signedPart,neg_one_mul,max_eq_right (by linarith :
        -(SquarefreeVaughanLogSource.coefficient L n).re≤0),mul_zero,zero_mul]
    rw [hz,add_zero]
  · rw [if_neg hp]
    simp only [signedPart,one_mul,max_eq_right (le_of_not_gt hp),mul_zero,zero_mul]

private theorem family_negative_part_sum (A : ℕ→Finset ℕ) (D : Finset ℕ)
    (L y : ℝ) (N : ℕ) :
    (∑ n∈D,signedPart (-1) (A n) L y N n)=
      (∑ n∈D.filter (fun n => (SquarefreeVaughanLogSource.coefficient L n).re<0),
        residualCoefficient (A n) L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  rw [Complex.re_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : (SquarefreeVaughanLogSource.coefficient L n).re<0
  · rw [if_pos hp,← signedPart_add]
    have hz : signedPart 1 (A n) L y N n=0 := by
      simp only [signedPart,one_mul,max_eq_right hp.le,mul_zero,zero_mul]
    rw [hz,zero_add]
  · rw [if_neg hp]
    simp only [signedPart,neg_one_mul,max_eq_right (by linarith :
      -(SquarefreeVaughanLogSource.coefficient L n).re≤0),mul_zero,zero_mul]

/-- The ENTIRE original unpaid dense band now has an independent signed
floor, with one relative supply price and source-geometric errors. Both
literal phase grids, all counts and all original masks are covered; no
unmatched signed population or completion correction is a hypothesis. -/
theorem exists_dense_band_floor {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤y) :
    ∃ r C : ℝ,0≤r ∧ r<1 ∧ 0≤C ∧
      ∀ᶠ j : ℕ in atTop,
        let N := dyadicMomentOrder j
        let K := dyadicPrimeCount j
        let S := denseBand u N K
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let b := Real.pi/y;
        -u^(N+1)*unpaidCountSupplyPrice N*
          ((∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N b y,
            exp (-ZetaRieszMultiPeriodSix.center b y i/2)*
              (ZetaRieszMultiPeriodSix.center b y i)^N/N.factorial)+
           (∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N (b+Real.pi/y) y,
            exp (-ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y i/2)*
              (ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y i)^N/N.factorial))-
          4*zetaMoebiusLogMajorantMass (1+1/262144)*exp (-(N : ℝ)/1000000)-
          2*r^N*C-3*ownerPaymentError N≤
            ((u : ℂ)^(N+1)*∑ n∈S,residualCoefficient A L N n*
              zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨r,C,hr,hr1,hC,hunmatched⟩ := exists_dense_unmatched_bound hu hU hy
  refine ⟨r,C,hr,hr1,hC,?_⟩
  filter_upwards [eventually_dense_two_grid_floor hu hU hy,hunmatched,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1000 : ℕ))]
      with j hfloor hbound hN
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  let S := denseBand u N K
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let Ao := fun n => A∩{largestPrime n}
  let b := Real.pi/y
  let U := S\(densePeriodGrid S N b y∪denseBoundaryGrid S N b y)
  let V := S\(densePeriodGrid S N (b+Real.pi/y) y∪denseBoundaryGrid S N (b+Real.pi/y) y)
  let G := U.filter (fun n => 0<(SquarefreeVaughanLogSource.coefficient L n).re)
  let H := V.filter (fun n => (SquarefreeVaughanLogSource.coefficient L n).re<0)
  have hy0 : 0<y := by linarith
  have hπ : 0≤Real.pi/y := by positivity
  have hb : Real.pi/y≤b ∧ b≤2*Real.pi/y := by
    refine ⟨le_rfl,?_⟩
    calc
      b ≤ Real.pi/y+Real.pi/y := by dsimp [b]; linarith only [hπ]
      _ = 2*Real.pi/y := by ring
  have hb' : Real.pi/y≤b+Real.pi/y ∧ b+Real.pi/y≤2*Real.pi/y := by
    constructor
    · dsimp [b]; linarith only [hπ]
    · exact le_of_eq (by dsimp [b]; ring)
  have hG := hbound b G hb (Finset.filter_subset _ _)
  have hH := hbound (b+Real.pi/y) H hb' (Finset.filter_subset _ _)
  have hwindow : S⊆literalWindow N :=
    Finset.Subset.trans (Finset.filter_subset _ _) (ZetaRieszNonownerAllocation.coreBand_subset_literalWindow u N K)
  have hGw : G⊆literalWindow N :=
    Finset.Subset.trans (Finset.Subset.trans (Finset.filter_subset _ _) Finset.sdiff_subset) hwindow
  have hHw : H⊆literalWindow N :=
    Finset.Subset.trans (Finset.Subset.trans (Finset.filter_subset _ _) Finset.sdiff_subset) hwindow
  have hGp := norm_owner_subset_le A G (by linarith : 0≤u) hU
    (SquarefreeVaughanLogSource.length_pos u N) hGw hG
  have hHp := norm_owner_subset_le A H (by linarith : 0≤u) hU
    (SquarefreeVaughanLogSource.length_pos u N) hHw hH
  have hp := (abs_le.mp ((Complex.abs_re_le_norm _).trans hGp)).1
  have hq := (abs_le.mp ((Complex.abs_re_le_norm _).trans hHp)).1
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul,← family_positive_part_sum] at hp
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul,← family_negative_part_sum] at hq
  have hscaled := mul_le_mul_of_nonneg_left hfloor
    (pow_nonneg (by linarith : 0≤u) (N+1))
  have ho := (ZetaRieszNonownerAllocation.signed_owner_bounds (fun _ => A) S (fun _ => 1)
    (SquarefreeVaughanLogSource.length_pos u N) N hwindow (by intros; norm_num) y
    (by linarith : 0≤u) (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le)).1
  simp only [one_mul] at ho
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at ho
  simp only [Complex.re_ofReal_mul] at ho
  have hunit {c : ℝ} (hc : 0<c) : amplitude N c/c=exp (-c/2)*c^N/N.factorial := by
    unfold amplitude
    rw [pow_succ]
    field_simp
  have hsum (d : ℝ) :
      (∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N d y,
        amplitude N (ZetaRieszMultiPeriodSix.center d y i)/ZetaRieszMultiPeriodSix.center d y i)=
      ∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N d y,
        exp (-ZetaRieszMultiPeriodSix.center d y i/2)*(ZetaRieszMultiPeriodSix.center d y i)^N/N.factorial := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hunit (by have hh := (grid_center_bounds hN hy hi).1; linarith)
  dsimp only at hscaled
  rw [hsum b,hsum (b+Real.pi/y)] at hscaled
  dsimp only
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul]
  change _≤u^(N+1)*(∑ n∈S,residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
  change -(2*zetaMoebiusLogMajorantMass (1+1/262144)*exp (-(N : ℝ)/1000000)+r^N*C+
    ownerPaymentError N)≤u^(N+1)*(∑ n∈U,signedPart 1 (Ao n) L y N n) at hp
  change -(2*zetaMoebiusLogMajorantMass (1+1/262144)*exp (-(N : ℝ)/1000000)+r^N*C+
    ownerPaymentError N)≤u^(N+1)*(∑ n∈V,signedPart (-1) (Ao n) L y N n) at hq
  change u^(N+1)*(∑ n∈S,residualCoefficient (Ao n) L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
    ownerPaymentError N≤u^(N+1)*(∑ n∈S,residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re at ho
  nlinarith only [hp,hq,hscaled,ho]

open ZetaRieszFiveSignCoverFloor ZetaRieszRoughFiveJoinedFloor
open ZetaRieszRadialCompensation ZetaRieszBandCompensation
open ZetaRieszSmallPrimeCompensation ZetaRieszFourPrimeHead
open ZetaRieszFivePositiveHead ZetaRieszFiveNegativeHead ZetaRieszSevenCountTail
open ZetaRieszRoughFivePeriodFloor ZetaRieszMultiPeriodSix
open ZetaRieszOneSidedArithmetic

/-- The ENTIRE newly unpaid dense-count band leaves the authoritative
joinedPhysical floor, together with the previously paid five-prime class.
The SAME quantitative supply pays both prices, with 1/256 still retained.
Every old credit and the literal lower-count remainder survives exactly.
This strengthens the global gap; it does NOT assert the numeric floor. -/
theorem eventually_joined_floor_without_dense_band {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ η h δ ε ζ θ : ℝ, ∃ err : ℕ → ℝ,
      0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧ 0 < ζ ∧ ζ ≤ 1/128 ∧
      0 < θ ∧ θ ≤ 1/128 ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ w : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let P := ⌊Real.exp (ε*N)⌋₊
        let V := ⌊Real.exp (ζ*N)⌋₊
        let R := ⌊Real.exp (θ*N)⌋₊
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
        let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
        let Gs := radialHeads S N P V L
        let Ts := radialTail S N R
        let Ys := radialSupply N h w
        let E := S\spent S N Q P V R η h L w
        let E5 := E.filter (fun n : ℕ => n.primeFactors.card = 5)
        let Ds := denseBand u N (dyadicPrimeCount j)
        let Eo := (E\E5)\Ds
        let W := ∑ n ∈ Eo, if 7 ≤ n.primeFactors.card then
          max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
        let G := ∑ n ∈ Eo.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
          weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
            ZetaRieszPairChamberFloor.pairSaving L y n)
        0 < (∑ n ∈ Ys, f n).re ∧ 0 ≤ G ∧
          u^(N+1)*(W+G+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
            max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+
            (∑ n ∈ Ys, f n).re/256)-err j ≤
              ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,ε,ζ,θ,c,κ,r₀,C₀,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
      hc,hκ,hκeq,hr₀,hr₀1,hC₀,hbase⟩ := eventually_core_full_floor_with_scale hu hU hy
  obtain ⟨r₁,C₁,hr₁,hr₁1,hC₁,hfive⟩ := exists_unpaid_five_floor hu hU hy hκ
  obtain ⟨r₂,C₂,hr₂,hr₂1,hC₂,hdense⟩ := exists_dense_band_floor hu hU hy
  let e := fun j => ‖(u : ℂ)^(dyadicMomentOrder j+1)*
    (coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j))‖
  let d := fun j => 4*zetaMoebiusLogMajorantMass (1+1/262144)*
    Real.exp (-(dyadicMomentOrder j : ℝ)/1000000)
  have he0 (j : ℕ) : 0 ≤ e j := norm_nonneg _
  have hd0 (j : ℕ) : 0 ≤ d j := by
    dsimp [d]
    positivity [zetaMoebiusLogMajorantMass_nonneg (1+1/262144)]
  have heLim : Tendsto e atTop (𝓝 0) := by
    have ht := (ZetaRieszGammaJoint.tendsto_core_sub_joined (by linarith : 0 < u)
      hU (fun _ => y) dyadicMomentOrder dyadicPrimeCount tendsto_dyadicMomentOrder).norm
    simpa only [norm_zero] using ht
  have hdLim : Tendsto d atTop (𝓝 0) := by
    have ht := (ZetaRieszJointDominantFloor.Refined.tendsto_allowance.const_mul (2 : ℝ)).comp
      tendsto_dyadicMomentOrder
    simp only [mul_zero] at ht
    convert ht using 1
    funext j
    dsimp [d,Function.comp_def]
    ring
  have h₀ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₀1).mul_const C₀).comp
    tendsto_dyadicMomentOrder
  have h₁ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₁ hr₁1).mul_const (2*C₁)).comp
    tendsto_dyadicMomentOrder
  have h₂ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₂ hr₂1).mul_const (2*C₂)).comp
    tendsto_dyadicMomentOrder
  have h₃ := (tendsto_ownerPaymentError.comp tendsto_dyadicMomentOrder).const_mul (3 : ℝ)
  let err := fun j => r₀^(dyadicMomentOrder j)*C₀+e j+2*d j+2*r₁^(dyadicMomentOrder j)*C₁+
    2*r₂^(dyadicMomentOrder j)*C₂+3*ownerPaymentError (dyadicMomentOrder j)
  have herr : Tendsto err atTop (𝓝 0) := by
    have ht := ((h₀.add heLim).add (hdLim.add hdLim)).add (h₁.add (h₂.add h₃))
    simp only [zero_mul,mul_zero,zero_add] at ht
    convert ht using 1
    funext j
    dsimp [err,Function.comp_def]
    ring
  have ho0 (j : ℕ) : 0≤ownerPaymentError (dyadicMomentOrder j) := by
    unfold ownerPaymentError
    positivity [zetaMoebiusLogMajorantMass_nonneg (2049/2048),
      ZetaRieszNonownerAllocation.nonownerRate_bounds.1]
  refine ⟨η,h,δ,ε,ζ,θ,err,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
    (fun j => by dsimp [err]; positivity [he0 j,hd0 j,ho0 j]),herr,?_⟩
  filter_upwards [hbase,hfive,hdense,
    tendsto_dyadicMomentOrder.eventually (eventually_count_cost_paid_by_same_supply hc hy),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszPairChamberFloor.eventually_core_subset_floor hu hU),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1000 : ℕ))]
      with j hj hfive hdense hcost hbound hN
  obtain ⟨w,hw,hY,hscale,hcore⟩ := hj
  let N := dyadicMomentOrder j
  let Q := ⌊Real.exp (δ*N)⌋₊
  let P := ⌊Real.exp (ε*N)⌋₊
  let V := ⌊Real.exp (ζ*N)⌋₊
  let R := ⌊Real.exp (θ*N)⌋₊
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let Xs := radialTriples S N η
  let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
  let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let Gs := radialHeads S N P V L
  let Ts := radialTail S N R
  let Ys := radialSupply N h w
  let E := S\spent S N Q P V R η h L w
  let E5 := E.filter (fun n : ℕ => n.primeFactors.card = 5)
  let Ds := denseBand u N (dyadicPrimeCount j)
  let Eo := (E\E5)\Ds
  let W := ∑ n ∈ Eo, if 7 ≤ n.primeFactors.card then
    max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
  let G := ∑ n ∈ Eo.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
    weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
      ZetaRieszPairChamberFloor.pairSaving L y n)
  have hG : 0 ≤ G := Finset.sum_nonneg (fun n _ => mul_nonneg (weight_nonneg A N n)
    (add_nonneg (ZetaRieszJoinedPrefixFloor.cutoffSaving_nonneg L y n)
      (ZetaRieszPairChamberFloor.pairSaving_nonneg L y n)))
  refine ⟨w,hw,hY,hG,?_⟩
  have hp := hfive Q P V R η h w hh hhu hw
  let units := (∑ i ∈ completeGrid N (Real.pi/y) y,
    Real.exp (-center (Real.pi/y) y i/2)*(center (Real.pi/y) y i)^N/N.factorial)+
    (∑ i ∈ completeGrid N (Real.pi/y+Real.pi/y) y,
      Real.exp (-center (Real.pi/y+Real.pi/y) y i/2)*
        (center (Real.pi/y+Real.pi/y) y i)^N/N.factorial)
  change -u^(N+1)*κ*units-d j-2*r₁^N*C₁ ≤ ((u : ℂ)^(N+1)*∑ n ∈ E5, f n).re at hp
  have hbudget := period_grids_cost_paid (by omega : 1≤N) hc hy hhu hκeq w f (radialIndices N)
    (slabGrid N (Real.pi/y) y) (slabGrid N (Real.pi/y+Real.pi/y) y) hw hscale
    (Finset.Subset.refl _)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
  rw [biUnion_slabGrid_eq,biUnion_slabGrid_eq] at hbudget
  change κ*units ≤ (1/128 : ℝ)*(∑ n ∈ Ys, f n).re at hbudget
  have hscaled := mul_le_mul_of_nonneg_left hbudget
    (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  have hpaid : -u^(N+1)*(∑ n ∈ Ys, f n).re/128-d j-2*r₁^N*C₁ ≤
      ((u : ℂ)^(N+1)*∑ n ∈ E5, f n).re := by
    linarith only [hscaled,hp]
  have hDpaid := hdense
  change -u^(N+1)*unpaidCountSupplyPrice N*units-d j-2*r₂^N*C₂-3*ownerPaymentError N≤
    ((u : ℂ)^(N+1)*∑ n∈Ds,f n).re at hDpaid
  have hDbudget := hcost h (Real.pi/y) w f (radialIndices N)
    (slabGrid N (Real.pi/y) y) (slabGrid N (Real.pi/y+Real.pi/y) y) hhu hw hscale
    (Finset.Subset.refl _)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
  rw [biUnion_slabGrid_eq,biUnion_slabGrid_eq] at hDbudget
  change unpaidCountSupplyPrice N*units≤(1/256 : ℝ)*(∑ n∈Ys,f n).re at hDbudget
  have hDscaled := mul_le_mul_of_nonneg_left hDbudget
    (pow_nonneg (by linarith : 0≤u) (N+1))
  have hDpaid' : -u^(N+1)*(∑ n∈Ys,f n).re/256-d j-2*r₂^N*C₂-3*ownerPaymentError N≤
      ((u : ℂ)^(N+1)*∑ n∈Ds,f n).re := by
    linarith only [hDscaled,hDpaid]
  have hDsub : Ds⊆E\E5 := by
    have hsub := middle_population_subset_unpaid S Ds
      (N := N) (Q := Q) (P := P) (V := V) (R := R) (h := h) (L := L)
      (by omega : 1000≤N) η hh hhu w hw
      (Finset.filter_subset _ _) (by
        intro n hn
        have hd := (Finset.mem_filter.mp hn).2
        exact ⟨hd.2.1,hd.2.2.2⟩)
    intro n hn
    refine Finset.mem_sdiff.mpr ⟨hsub hn,?_⟩
    intro hh5
    have hc5 := (Finset.mem_filter.mp hh5).2
    have hc8 := (Finset.mem_filter.mp hn).2.2.1
    omega
  have hDs := congrArg Complex.re (Finset.sum_sdiff hDsub (f := f))
  change (∑ n∈Eo,f n).re+(∑ n∈Ds,f n).re=(∑ n∈E\E5,f n).re at hDs
  have hb := hbound (dyadicPrimeCount j) y Eo
    (Finset.Subset.trans Finset.sdiff_subset
      (Finset.Subset.trans Finset.sdiff_subset Finset.sdiff_subset))
  change u^(N+1)*(W+G) ≤ ((u : ℂ)^(N+1)*∑ n ∈ Eo, f n).re at hb
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hb hpaid hDpaid'
  have hs := congrArg Complex.re (Finset.sum_sdiff (Finset.filter_subset
    (fun n : ℕ => n.primeFactors.card = 5) E) (f := f))
  change (∑ n ∈ E\E5, f n).re+(∑ n ∈ E5, f n).re = (∑ n ∈ E, f n).re at hs
  rw [← hDs] at hs
  let credits := max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
    max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
    max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0
  change u^(N+1)*((∑ n ∈ E, f n).re+max (∑ n ∈ Xs, f n).re 0+
    max (∑ n ∈ Zs, f n).re 0+max (∑ n ∈ Hs, f n).re 0+
    max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+
    max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)-r₀^N*C₀ ≤
      ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re at hcore
  have hcore' : u^(N+1)*((∑ n ∈ E, f n).re+credits+(∑ n ∈ Ys, f n).re/64)-r₀^N*C₀ ≤
      ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
    convert hcore using 1
    dsimp only [credits]
    ring
  have hbridge := Complex.re_le_norm ((u : ℂ)^(N+1)*
    (coreResponse u y N (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)))
  rw [mul_sub,Complex.sub_re] at hbridge
  conv at hbridge => rhs; rw [← mul_sub]
  change ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re-
    ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re ≤ e j at hbridge
  have hscaledLedger := congrArg (fun x : ℝ => u^(N+1)*x) hs
  have hfinal : u^(N+1)*(W+G+credits+(∑ n ∈ Ys, f n).re/256)-
      (r₀^N*C₀+e j+2*d j+2*r₁^N*C₁+2*r₂^N*C₂+3*ownerPaymentError N) ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
    nlinarith only [hcore',hb,hpaid,hDpaid',hbridge,hscaledLedger]
  convert hfinal using 1
  dsimp only [credits]
  ring

/-- The actual remaining squarefree labels have a STRICTLY LOWER count
ceiling after the new whole-band payment. This refers to the SAME old
spent set and supply, rather than a postulated or completed population. -/
theorem remaining_count_ceiling (u : ℝ) (N K Q P V R : ℕ) (η h L : ℝ)
    (w : ℕ→ℝ) {n : ℕ}
    (hn : n∈
      (((coreBand u N K\spent (coreBand u N K) N Q P V R η h L w)\
        (coreBand u N K\spent (coreBand u N K) N Q P V R η h L w).filter
          (fun n => n.primeFactors.card=5))\denseBand u N K))
    (hs : Squarefree n) :
    3≤n.primeFactors.card ∧ n.primeFactors.card≠5 ∧
      (n.primeFactors.card<8 ∨ (n.primeFactors.card : ℝ)<5*log ((N : ℝ)+1)+2) := by
  obtain ⟨hn,hnotdense⟩ := Finset.mem_sdiff.mp hn
  obtain ⟨hn,hnotfive⟩ := Finset.mem_sdiff.mp hn
  have hnCore := (Finset.mem_sdiff.mp hn).1
  have hc := ZetaRieszJointPrimeEnergy.core_count hnCore
  have hfive : n.primeFactors.card≠5 := fun h5 =>
    hnotfive (Finset.mem_filter.mpr ⟨hn,h5⟩)
  refine ⟨hc,hfive,?_⟩
  by_contra hbad
  push Not at hbad
  exact hnotdense (Finset.mem_filter.mpr ⟨hnCore,hs,hbad.1,hbad.2,
    unpaid_count_lt _ N Q P V R η h L w hn hs⟩)

/-- Exhaustive count enumeration for the actual new unpaid remainder.
Five and the whole growing upper band are gone; the fixed low counts
and the lower growing population are kept, without claiming a floor
for any of those remaining populations. -/
theorem remaining_count_cases (u : ℝ) (N K Q P V R : ℕ) (η h L : ℝ)
    (w : ℕ→ℝ) {n : ℕ}
    (hn : n∈
      (((coreBand u N K\spent (coreBand u N K) N Q P V R η h L w)\
        (coreBand u N K\spent (coreBand u N K) N Q P V R η h L w).filter
          (fun n => n.primeFactors.card=5))\denseBand u N K))
    (hs : Squarefree n) :
    n.primeFactors.card=3 ∨ n.primeFactors.card=4 ∨
      n.primeFactors.card=6 ∨ n.primeFactors.card=7 ∨
      (8≤n.primeFactors.card ∧
        (n.primeFactors.card : ℝ)<5*log ((N : ℝ)+1)+2) := by
  have hc := remaining_count_ceiling u N K Q P V R η h L w hn hs
  by_cases hlo : n.primeFactors.card<8
  · omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨by omega,(hc.2.2.resolve_left hlo)⟩)))

end RiemannGaussian.ZetaRieszDenseCountCoverFloor
