/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointPhaseCredit
import RiemannGaussian.ZetaRieszCompensationSupply

/-!
# The remaining rising-edge clipping loss on actual primes

The edge in the improved signed compensation inequality is confined to
counts at most six, but is not a bounded source-scale allowance. Three
actual prime intervals at log slopes 0.42, 0.46 and 1.12 remain in the
literal core with the original allocation. A bounded translation gives
negative observation, and the sum of the exact discarded edge grows at
rate `(2*u)^N/(N+1)^4` for every fixed nonzero height.

This is an audit of that lossy inequality, not a lower bound for the
joint signed carrier or evidence that its cancellation is impossible.
-/

namespace RiemannGaussian.ZetaRieszJointEdgeLoss
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszAllowanceGrowth
open ZetaRieszJointAllocation ZetaRieszPrimeCountFrequency
open ZetaRieszParityPacket

/-- The coordinates are in increasing prime order. -/
private def slope (i : Fin 3) : ℝ :=
  if i = 0 then 21/50 else if i = 1 then 23/50 else 28/25

/-- Only the largest-prime interval receives the bounded translation. -/
private def start (N : ℕ) (v : ℝ) (i : Fin 3) : ℝ :=
  slope i*N + if i = 2 then v else 0

/-- Actual ordinary-prime choices in the three disjoint log intervals. -/
private def tuples (N : ℕ) (h v : ℝ) : Finset (Fin 3 → ℕ) :=
  Fintype.piFinset (fun i => logPrimes (start N v i) h)

/-- Distinct integers, with no incidence multiplicity. -/
private def products (N : ℕ) (h v : ℝ) : Finset ℕ :=
  (tuples N h v).image (fun p => ∏ i, p i)

private theorem slope_pos (i : Fin 3) : 0 < slope i := by
  fin_cases i <;> norm_num [slope, Fin.ext_iff]

private theorem slope_gap {i j : Fin 3} (hij : i < j) : slope i+1/1000 < slope j := by
  fin_cases i <;> fin_cases j <;> norm_num [slope, Fin.ext_iff] at *

private theorem tuple_bounds {N : ℕ} {h v : ℝ} {p : Fin 3 → ℕ}
    (hp : p ∈ tuples N h v) (i : Fin 3) :
    (p i).Prime ∧ start N v i < Real.log (p i) ∧
      Real.log (p i) ≤ start N v i+h :=
  logPrimes_bounds (Fintype.mem_piFinset.mp hp i)

/-- The finite boxes are disjoint, even across two different tuples. -/
private theorem coordinate_order {N : ℕ} (hN : 0 < N) {h v : ℝ}
    (hv : 0 ≤ v) (hwidth : h+v ≤ (N : ℝ)/1000)
    {p q : Fin 3 → ℕ} (hp : p ∈ tuples N h v) (hq : q ∈ tuples N h v)
    {i j : Fin 3} (hij : i < j) : p i < q j := by
  apply logPrimes_order (a := start N v i) (b := start N v j) _
    (Fintype.mem_piFinset.mp hp i) (Fintype.mem_piFinset.mp hq j)
  have hgap := mul_lt_mul_of_pos_right (slope_gap hij)
    (show (0 : ℝ) < N by exact_mod_cast hN)
  dsimp [start]
  split_ifs <;> nlinarith

private theorem product_injective {N : ℕ} (hN : 0 < N) {h v : ℝ}
    (hv : 0 ≤ v) (hwidth : h+v ≤ (N : ℝ)/1000) :
    Set.InjOn (fun p : Fin 3 → ℕ => ∏ i, p i) (tuples N h v : Set _) := by
  intro p hp q hq he
  dsimp only at he
  funext i
  have hpi := (tuple_bounds hp i).1
  have hd : p i ∣ ∏ j, q j := by
    rw [← he]
    exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)
  obtain ⟨j, _, hj⟩ := (hpi.prime.dvd_finsetProd_iff q).mp hd
  have heq := (Nat.prime_dvd_prime_iff_eq hpi (tuple_bounds hq j).1).mp hj
  have hij : i = j := by
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim ((coordinate_order hN hv hwidth hp hq hij).ne heq)
    · exact hij
    · exact False.elim ((coordinate_order hN hv hwidth hq hp hij).ne heq.symm)
  simpa only [hij] using heq

private theorem products_card {N : ℕ} (hN : 0 < N) {h v : ℝ}
    (hv : 0 ≤ v) (hwidth : h+v ≤ (N : ℝ)/1000) :
    (products N h v).card = ∏ i, (logPrimes (start N v i) h).card := by
  rw [products, Finset.card_image_of_injOn (product_injective hN hv hwidth)]
  simp [tuples]

private theorem tuple_squarefree {N : ℕ} (hN : 0 < N) {h v : ℝ}
    (hv : 0 ≤ v) (hwidth : h+v ≤ (N : ℝ)/1000)
    {p : Fin 3 → ℕ} (hp : p ∈ tuples N h v) : Squarefree (∏ i, p i) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    apply Nat.coprime_iff_isRelPrime.mp
    apply (tuple_bounds hp i).1.coprime_iff_not_dvd.mpr
    intro hd
    have he := (Nat.prime_dvd_prime_iff_eq (tuple_bounds hp i).1
      (tuple_bounds hp j).1).mp hd
    rcases lt_or_gt_of_ne hij with hh | hh
    · exact (coordinate_order hN hv hwidth hp hp hh).ne he
    · exact (coordinate_order hN hv hwidth hp hp hh).ne he.symm
  · intro i _
    exact (tuple_bounds hp i).1.squarefree

private theorem tuple_log {N : ℕ} {h v : ℝ} {p : Fin 3 → ℕ}
    (hp : p ∈ tuples N h v) : Real.log (∏ i, p i : ℕ) = ∑ i, Real.log (p i) := by
  rw [Nat.cast_prod, Real.log_prod]
  intro i _
  exact_mod_cast (tuple_bounds hp i).1.ne_zero

private theorem tuple_log_bounds {N : ℕ} {h v : ℝ} {p : Fin 3 → ℕ}
    (hp : p ∈ tuples N h v) :
    2*(N : ℝ)+v < Real.log (∏ i, p i : ℕ) ∧
      Real.log (∏ i, p i : ℕ) ≤ 2*(N : ℝ)+v+3*h := by
  have hl := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin 3)))
    (fun i _ => (tuple_bounds hp i).2.1.le)
    ⟨0, Finset.mem_univ _, (tuple_bounds hp 0).2.1⟩
  have hu := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
    (fun i _ => (tuple_bounds hp i).2.2)
  rw [tuple_log hp]
  simp only [Fin.sum_univ_three] at hl hu ⊢
  norm_num [start,slope,Fin.ext_iff] at hl hu
  constructor <;> linarith

private theorem tuple_primeFactors {N : ℕ} (hN : 0 < N) {h v : ℝ}
    (hv : 0 ≤ v) (hwidth : h+v ≤ (N : ℝ)/1000)
    {p : Fin 3 → ℕ} (hp : p ∈ tuples N h v) :
    (∏ i, p i).primeFactors = Finset.univ.image p := by
  have hi : Function.Injective p :=
    (show StrictMono p from fun _ _ hij => coordinate_order hN hv hwidth hp hp hij).injective
  have he := Finset.prod_image (f := fun n : ℕ => n) (s := Finset.univ) hi.injOn
  rw [← he]
  apply Nat.primeFactors_prod
  intro a ha
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
  exact (tuple_bounds hp i).1

/-- Canonical extremes and exact count: the box has no repeated prime factors. -/
private theorem tuple_extremes {N : ℕ} (hN : 0 < N) {h v : ℝ}
    (hv : 0 ≤ v) (hwidth : h+v ≤ (N : ℝ)/1000)
    {p : Fin 3 → ℕ} (hp : p ∈ tuples N h v) :
    (∏ i, p i).primeFactors.card = 3 ∧
      ZetaRieszPrimeEndpoint.largestPrime (∏ i, p i) = p 2 ∧
      (∏ i, p i).minFac = p 0 := by
  have hm : StrictMono p := fun _ _ hij => coordinate_order hN hv hwidth hp hp hij
  have hf := tuple_primeFactors hN hv hwidth hp
  have hs := tuple_squarefree hN hv hwidth hp
  have hn1 : 1 < ∏ i, p i := by
    apply (tuple_bounds hp 0).1.one_lt.trans_le
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero)
      (Finset.dvd_prod_of_mem p (Finset.mem_univ 0))
  refine ⟨?_,?_,?_⟩
  · rw [hf,Finset.card_image_of_injective _ hm.injective]
    simp
  · apply ZetaRieszPrimeIntervals.largestPrime_eq_of_max
    · rw [hf]; exact Finset.mem_image.mpr ⟨2,Finset.mem_univ _,rfl⟩
    · intro a ha
      rw [hf] at ha
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      exact hm.monotone (by omega)
  · apply le_antisymm
    · exact Nat.minFac_le_of_dvd (tuple_bounds hp 0).1.two_le
        (Finset.dvd_prod_of_mem p (Finset.mem_univ 0))
    · have hr := (Nat.minFac_prime hn1.ne').mem_primeFactors
        (Nat.minFac_dvd (∏ i, p i)) hs.ne_zero
      rw [hf] at hr
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hr
      rw [← hi]
      exact hm.monotone (Fin.zero_le i)

/-- The three boxes contain exponentially many distinct actual integers.
No continuum density or phase approximation is used in this count. -/
private theorem eventually_products_card_lower {h C : ℝ} (hh : 0 < h) (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ C →
      c*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3 ≤ (products N h v).card := by
  have hi (i : Fin 3) := eventually_logPrimes_card_lower_slope (slope_pos i) hh hC
  choose c hc he using hi
  refine ⟨∏ i, c i, Finset.prod_pos (fun i _ => hc i), ?_⟩
  filter_upwards [Filter.eventually_all.mpr he, eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (1000*(h+C))]
    with N hcounts hN hsize v hv hvC
  have hw : h+v ≤ (N : ℝ)/1000 := by linarith
  rw [products_card hN hv hw, Nat.cast_prod]
  have hj (i : Fin 3) : c i*Real.exp (slope i*N)/((N : ℝ)+1) ≤
      ((logPrimes (start N v i) h).card : ℝ) := by
    apply hcounts i
    · dsimp [start]; split_ifs <;> linarith
    · dsimp [start]; split_ifs <;> linarith
  have hprod := Finset.prod_le_prod
    (s := (Finset.univ : Finset (Fin 3)))
    (fun i _ => div_nonneg (mul_nonneg (hc i).le (Real.exp_pos _).le) (by positivity))
    (fun i _ => hj i)
  have hex : (∏ i : Fin 3, Real.exp (slope i*N)) = Real.exp (2*(N : ℝ)) := by
    rw [← Real.exp_sum, ← Finset.sum_mul]
    simp only [Fin.sum_univ_three]
    norm_num [slope,Fin.ext_iff]
  simpa only [Finset.prod_div_distrib, Finset.prod_mul_distrib, hex,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hprod


private theorem prime_log_bounds {N : ℕ} (hN : 0 < N) {h v : ℝ}
    (hv : 0 ≤ v) (hwidth : h+v ≤ (N : ℝ)/1000)
    {p : Fin 3 → ℕ} (hp : p ∈ tuples N h v)
    {q : ℕ} (hq : q ∈ (∏ i, p i).primeFactors) :
    (N : ℝ)/25 < Real.log q ∧ Real.log q ≤ (5/4 : ℝ)*N ∧
      Real.log q ≤ (9/16 : ℝ)*Real.log (∏ i, p i : ℕ) := by
  rw [tuple_primeFactors hN hv hwidth hp] at hq
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨_,hi,hu⟩ := tuple_bounds hp i
  obtain ⟨hl,_⟩ := tuple_log_bounds hp
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : (1/25 : ℝ) ≤ slope i ∧ slope i ≤ 28/25 := by
    fin_cases i <;> norm_num [slope,Fin.ext_iff]
  have hlo := mul_le_mul_of_nonneg_right hs.1 hNR.le
  have hhi := mul_le_mul_of_nonneg_right hs.2 hNR.le
  dsimp [start] at hi hu
  split_ifs at hi hu <;> constructor <;> first | constructor | linarith
  all_goals linarith

private theorem tuple_edge_lower {N : ℕ} (hN : 0 < N) {h v L : ℝ}
    (hv : 0 ≤ v) (hwidth : h+v ≤ (N : ℝ)/1000)
    (hLlo : (137/100 : ℝ)*N ≤ L) (hLhi : L ≤ (7/5 : ℝ)*N)
    {p : Fin 3 → ℕ} (hp : p ∈ tuples N h v) :
    (N : ℝ)/10 ≤ max 0 (Real.log (∏ i, p i : ℕ).minFac-
      max 0 (L-Real.log (ZetaRieszPrimeEndpoint.largestPrime (∏ i, p i)))) ∧
      1 ≤ Real.log (∏ i, p i : ℕ)/L := by
  obtain ⟨_,hP,hr⟩ := tuple_extremes hN hv hwidth hp
  have b0 := tuple_bounds hp 0
  have b2 := tuple_bounds hp 2
  norm_num [start,slope,Fin.ext_iff] at b0 b2
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hD : 0 ≤ L-Real.log (p 2) := by linarith
  have hL : 0 < L := by linarith
  rw [hP,hr,max_eq_right hD]
  refine ⟨le_trans ?_ (le_max_right _ _),?_⟩
  · linarith
  · apply (le_div_iff₀ hL).mpr
    linarith [(tuple_log_bounds hp).1]

private theorem eventually_unassigned : ∀ᶠ N : ℕ in atTop,
    ∀ (A : Finset ℕ) (h v : ℝ), 0 ≤ v → h+v ≤ (N : ℝ)/1000 →
      ∀ p ∈ tuples N h v, (1/2 : ℝ) ≤ 1-boundedShare A N (∏ i, p i) := by
  have ht : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ)/1000)) atTop (𝓝 0) := by
    have hn := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const
      (by norm_num : (0 : ℝ) < 1000)
    simpa only [neg_div,Function.comp_def] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hn
  filter_upwards [eventually_ge_atTop 1,ht.eventually_lt_const
    (by norm_num : (0 : ℝ) < 1/6)] with N hN hsmall A h v hv hw p hp
  by_cases he : Squarefree (∏ i, p i) ∧ 1 < ∏ i, p i ∧ ¬(∏ i, p i).Prime
  · have hshare := ZetaRieszParityOrderTail.share_small_of_selected_primes_interior
      A N he.1 he.2.1 (fun q hq _ _ => (prime_log_bounds hN hv hw hp hq).2.2)
    rw [(tuple_extremes hN hv hw hp).1,Nat.cast_ofNat] at hshare
    rw [boundedShare,if_pos he]
    linarith
  · simp only [boundedShare,if_neg he]
    norm_num

private theorem products_subset_core (j : ℕ) (hj : 32 ≤ j) {u h v : ℝ}
    (hu : 1/2 < u) (huU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hv : 0 ≤ v) (hwidth : h+v ≤ (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ)/1000)
    (hL : (137/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
    (hsmall : 2*Real.log (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) <
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ)/25) :
    products (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) h v ⊆
      coreBand u
        (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
        (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) := by
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  have hN : 0 < N := by dsimp [N,ZetaRieszPrimeCountFrequency.dyadicMomentOrder,
    ZetaRieszPrimeCountFrequency.dyadicPrimeCount]; positivity
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hK : 3 < K := by
    have hh : (2 : ℕ)^3 ≤ 2^(j+3) := Nat.pow_le_pow_right (by decide) (by omega)
    dsimp [K,ZetaRieszPrimeCountFrequency.dyadicPrimeCount]
    norm_num at hh
    omega
  intro n hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hs := tuple_squarefree hN hv hwidth hp
  obtain ⟨hk,hP,hr⟩ := tuple_extremes hN hv hwidth hp
  have ht : 0 < Real.log (∏ i, p i : ℕ) :=
    by linarith [(tuple_log_bounds hp).1]
  obtain ⟨hlo,hhi⟩ := tuple_log_bounds hp
  have hwindow : (39/20 : ℝ)*N < Real.log (∏ i, p i : ℕ) ∧
      Real.log (∏ i, p i : ℕ) ≤ (203/100 : ℝ)*N := by constructor <;> linarith
  have hpCap : ∀ q ∈ (∏ i, p i).primeFactors, Real.log q ≤ (5/4 : ℝ)*N :=
    fun q hq => (prime_log_bounds hN hv hwidth hp hq).2.1
  have hpA : ∀ q ∈ (∏ i, p i).primeFactors,
      q ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    apply (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N q).mpr
    refine ⟨hqp,?_,?_⟩
    · have hh : (N : ℝ)/25 < Real.log q :=
        (prime_log_bounds hN hv hwidth hp hq).1
      have hl : Real.log (N^2 : ℕ) < Real.log q := by
        rw [Nat.cast_pow,Real.log_pow]
        change 2*Real.log N < _
        exact hsmall.trans hh
      exact_mod_cast (Real.log_lt_log_iff (by positivity : (0 : ℝ) < (N^2 : ℕ)) hq0).mp hl
    · have hlog : Real.log q < SquarefreeVaughanLogSource.length u N :=
        lt_of_le_of_lt (hpCap q hq) (by dsimp [N] at *; linarith)
      have he : Real.log (((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) : ℝ) =
          SquarefreeVaughanLogSource.length u N := by
        simp only [SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
      exact_mod_cast (Real.log_lt_log_iff hq0 (by positivity)).mp (he ▸ hlog)
  have hdom (q : ℕ) (hq : q ∈ (∏ i, p i).primeFactors) :
      Real.log q < (13/20 : ℝ)*Real.log (∏ i, p i : ℕ) := by
    nlinarith [hpCap q hq,hwindow.1]
  have hmem := ZetaRieszMaskSupport.window_mem_originalMask j hj hu
    (huU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le) (by dsimp [N] at *; linarith)
    ((ZetaRieszJointAllocation.mem_literalWindow N _).mpr
      (by constructor <;> nlinarith [hwindow.1,hwindow.2])) hs
    (by rw [hk]) (by rw [hk]; exact hK)
    (fun q hq => ((ZetaRieszAnnulusJoint.mem_intermediatePrimes u N q).mp (hpA q hq)).2.2)
  have hcancel : (∏ i, p i) ∉ ZetaRieszJointAllocation.cancellingSector u N K := by
    intro hc
    obtain ⟨_,_,_,_,_,q,hq,_,_,_,hhi⟩ := Finset.mem_filter.mp hc
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hlogs : Real.log ((∏ i, p i)/q : ℕ) = Real.log (∏ i, p i : ℕ)-Real.log q := by
      rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hq) (by exact_mod_cast hqp.ne_zero),
        Real.log_div (by exact_mod_cast hs.ne_zero) (by exact_mod_cast hqp.ne_zero)]
    have hh := (div_le_iff₀ ht).mp hhi
    rw [hlogs] at hh
    nlinarith [hdom q hq]
  have hret : (∏ i, p i) ∈ ZetaRieszMaskSupport.retainedBand u N K :=
    Finset.mem_sdiff.mpr ⟨hmem,hcancel⟩
  have hnd : (∏ i, p i) ∈ ZetaRieszDominantAllocation.nondominantBand u N K := by
    refine Finset.mem_sdiff.mpr ⟨hret,?_⟩
    intro hd
    obtain ⟨_,_,_,_,q,hq,_,_,hlarge⟩ := Finset.mem_filter.mp hd
    exact (hdom q hq).not_ge hlarge
  exact
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨hnd,by constructor <;> nlinarith [hwindow.1,hwindow.2]⟩,hwindow⟩

private theorem box_loss_lower (A : Finset ℕ) {N : ℕ} (hN : 10 ≤ N)
    {h v C L y : ℝ} (hv : 0 ≤ v) (hvC : v ≤ C)
    (hwidth : h+v ≤ (N : ℝ)/1000)
    (hLlo : (137/100 : ℝ)*N ≤ L) (hLhi : L ≤ (7/5 : ℝ)*N)
    {p : Fin 3 → ℕ} (hp : p ∈ tuples N h v)
    (hw : (1/2 : ℝ) ≤ 1-boundedShare A N (∏ i, p i))
    (hcos : Real.cos (y*Real.log (∏ i, p i : ℕ)) ≤ -(1/2 : ℝ)) :
    Real.exp (-(3/2 : ℝ)*(2*N+C+3*h))*(2*N)^N/N.factorial/4 ≤
      (Real.log (∏ i, p i : ℕ)/L)*
        max 0 (Real.log (∏ i, p i : ℕ).minFac-
          max 0 (L-Real.log (ZetaRieszPrimeEndpoint.largestPrime (∏ i, p i))))*
        max (-(((1-boundedShare A N (∏ i, p i) : ℝ) : ℂ)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (∏ i, p i)).re) 0 := by
  have hN0 : 0 < N := by omega
  have hNR : (10 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨he,hratio⟩ := tuple_edge_lower hN0 hv hwidth hLlo hLhi hp
  have he1 : 1 ≤ max 0 (Real.log (∏ i, p i : ℕ).minFac-
      max 0 (L-Real.log (ZetaRieszPrimeEndpoint.largestPrime (∏ i, p i)))) := by linarith
  have hpre := mul_le_mul hratio he1 (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
  let E := Real.exp (-(3/2 : ℝ)*Real.log (∏ i, p i : ℕ))*
    (Real.log (∏ i, p i : ℕ))^N/N.factorial
  have hE : 0 ≤ E := ZetaRieszCosineCarrier.factorial_envelope_nonneg N (∏ i, p i)
  have hx : E/4 ≤ -(((1-boundedShare A N (∏ i, p i) : ℝ) : ℂ)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (∏ i, p i)).re := by
    rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      zetaPrimeLogKernel,← SquarefreeEulerQuadratic.primeFilterKernel_one,
      ZetaRieszCosineCarrier.re_filterKernel_one]
    have hphase := mul_le_mul hw (show (1/2 : ℝ) ≤ -Real.cos
      (y*Real.log (∏ i, p i : ℕ)) by linarith)
      (by norm_num : (0 : ℝ) ≤ 1/2) (by linarith)
    have hm := mul_le_mul_of_nonneg_right hphase hE
    change E/4 ≤ -((1-boundedShare A N (∏ i, p i))*
      (E*Real.cos (y*Real.log (∏ i, p i : ℕ))))
    nlinarith
  have hl := tuple_log_bounds hp
  have hlog : 2*(N : ℝ) ≤ Real.log (∏ i, p i : ℕ) := by linarith [hl.1]
  have ha : Real.exp (-(3/2 : ℝ)*(2*N+C+3*h))*(2*N)^N/N.factorial ≤ E := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul
    · exact Real.exp_le_exp.mpr (by linarith [hl.2])
    · exact pow_le_pow_left₀ (by positivity) hlog N
    · positivity
    · positivity
  apply (div_le_div_of_nonneg_right ha (by norm_num : (0 : ℝ) ≤ 4)).trans
  have hm := hx.trans (le_max_left _ 0)
  have hh := mul_le_mul hpre hm (by positivity : 0 ≤ E/4) (by linarith)
  simpa only [one_mul] using hh

/-- The original factorial normalization of a fixed-width three-prime
box has the same exponential rate 2u as the dangerous mass. -/
private theorem box_scalar_lower {u c D : ℝ} (hu : 0 ≤ u) (hc : 0 ≤ c)
    {N : ℕ} (hN : 1 ≤ N) :
    (u*c*Real.exp (-(3/2 : ℝ)*D)/24)*(2*u)^N/((N : ℝ)+1)^4 ≤
      u^(N+1)*((c*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3)*
        (Real.exp (-(3/2 : ℝ)*(2*N+D))*(2*N)^N/N.factorial/4)) := by
  have hs := PrimeWindow.local_monomial_lower hN (by norm_num : (0 : ℝ) ≤ 2)
  norm_num [PrimeWindow.localGrowth] at hs
  rw [show -(2*(N : ℝ))/2 = -(N : ℝ) by ring] at hs
  have hs' : (2 : ℝ)^N/(6*((N : ℝ)+1)) ≤
      Real.exp (-(N : ℝ))*(2*N)^N/N.factorial := by
    apply le_trans _ hs
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have he : Real.exp (2*(N : ℝ))*Real.exp (-(3/2 : ℝ)*(2*N+D)) =
      Real.exp (-(3/2 : ℝ)*D)*Real.exp (-(N : ℝ)) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  let k := u^(N+1)*c*Real.exp (-(3/2 : ℝ)*D)/(4*((N : ℝ)+1)^3)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  calc
    _ = k*((2 : ℝ)^N/(6*((N : ℝ)+1))) := by
      dsimp [k]
      rw [mul_pow,pow_succ]
      field_simp
      ring
    _ ≤ k*(Real.exp (-(N : ℝ))*(2*N)^N/N.factorial) :=
      mul_le_mul_of_nonneg_left hs' hk
    _ = _ := by
      dsimp [k]
      calc
        _ = (u^(N+1)*c/(4*((N : ℝ)+1)^3))*
          (Real.exp (-(3/2 : ℝ)*D)*Real.exp (-(N : ℝ)))*
          ((2*N)^N/N.factorial) := by ring
        _ = _ := by rw [← he]; field_simp


/-- The exact rising-edge clipping loss contains an exponentially growing
actual three-prime subfamily. All original core and allocation masks are
retained; no bound on the signed sum itself follows. -/
theorem eventually_edge_loss_growth {u y : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : y ≠ 0) :
    ∃ k : ℝ, 0 < k ∧ ∀ᶠ j : ℕ in atTop,
      k*(2*u)^dyadicMomentOrder j/((dyadicMomentOrder j : ℝ)+1)^4 ≤
        u^(dyadicMomentOrder j+1)*
          ∑ n ∈ (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)).filter
            (fun n => n.primeFactors.card = 3),
            (Real.log n/SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))*
            max 0 (Real.log n.minFac-max 0
              (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)-
                Real.log (ZetaRieszPrimeEndpoint.largestPrime n)))*
            max (-(((1-boundedShare (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
                (dyadicMomentOrder j) n : ℝ) : ℂ)*
              zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re) 0 := by
  have hu0 : 0 < u := by linarith
  obtain ⟨h,C,hh,hC,hphase⟩ := ZetaRieszCompensationSupply.exists_negative_phase_window hy
  obtain ⟨c,hc,hcount⟩ := eventually_products_card_lower hh hC
  let D := C+3*h
  let k := u*c*Real.exp (-(3/2 : ℝ)*D)/24
  refine ⟨k,by dsimp [k]; positivity,?_⟩
  have hroom : u < Real.exp (-(137/200 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans
      (Real.exp_lt_exp.mpr (by norm_num)))
  have hL := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu0
    (by norm_num : (0 : ℝ) ≤ 137/200) hroom
  have hlogs : Tendsto (fun N : ℕ => 2*Real.log N/(N : ℝ)) atTop (𝓝 0) := by
    have hl := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def,pow_one,one_mul,add_zero,mul_div_assoc,mul_zero]
      using hl.const_mul 2
  have hsize : ∀ᶠ N : ℕ in atTop,
      10 ≤ N ∧ 1000*(h+C) ≤ (N : ℝ) ∧ 2*Real.log N < (N : ℝ)/25 := by
    filter_upwards [eventually_ge_atTop 10,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (1000*(h+C)),
      hlogs.eventually_lt_const (by norm_num : (0 : ℝ) < 1/25)] with N hN hwidth hlog
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    refine ⟨hN,hwidth,?_⟩
    have hlog' := (div_lt_iff₀ hNR).mp hlog
    linarith
  filter_upwards [eventually_ge_atTop 32,tendsto_dyadicMomentOrder.eventually hcount,
    tendsto_dyadicMomentOrder.eventually eventually_unassigned,
    tendsto_dyadicMomentOrder.eventually hL,tendsto_dyadicMomentOrder.eventually hsize]
    with j hj hcountj hunassigned hLj hsizej
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let f := fun n : ℕ => (Real.log n/L)*
    max 0 (Real.log n.minFac-max 0 (L-Real.log (ZetaRieszPrimeEndpoint.largestPrime n)))*
    max (-(((1-boundedShare A N n : ℝ) : ℂ)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re) 0
  have hfn (n : ℕ) : 0 ≤ f n := by
    apply mul_nonneg
    · exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg _)
        (SquarefreeVaughanLogSource.length_pos u N).le) (le_max_left _ _)
    · exact le_max_right _ _
  have hLlo : (137/100 : ℝ)*N ≤ L := by dsimp [N,L]; nlinarith [hLj]
  have hLhi : L ≤ (7/5 : ℝ)*N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu.le (show 2 ≤ N by omega)
    nlinarith [Real.log_two_lt_d9,Nat.cast_nonneg (α := ℝ) N]
  obtain ⟨v,hv,hvC,hcos⟩ := hphase (2*N)
  have hw : h+v ≤ (N : ℝ)/1000 := by dsimp [N]; linarith [hsizej.2.1]
  let T := products N h v
  have hsub : T ⊆ (coreBand u N (dyadicPrimeCount j)).filter
      (fun n => n.primeFactors.card = 3) := by
    intro n hn
    refine Finset.mem_filter.mpr ⟨products_subset_core j hj hu hU hv hw hLlo hsizej.2.2 hn,?_⟩
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    exact (tuple_extremes (by omega : 0 < N) hv hw hp).1
  let Q := Real.exp (-(3/2 : ℝ)*(2*N+D))*(2*N)^N/N.factorial/4
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hs : (T.card : ℝ)*Q ≤ ∑ n ∈ T, f n := by
    rw [← nsmul_eq_mul,← Finset.sum_const]
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    have hb := tuple_log_bounds hp
    simpa only [Q,D,f,add_assoc] using box_loss_lower A hsizej.1 hv hvC hw hLlo hLhi hp
      (hunassigned A h v hv hw p hp) (hcos _ hb.1.le (by linarith [hb.2]))
  have hwhole : (∑ n ∈ T, f n) ≤ ∑ n ∈ (coreBand u N (dyadicPrimeCount j)).filter
      (fun n => n.primeFactors.card = 3), f n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hfn n)
  have hcard := hcountj v hv hvC
  change k*(2*u)^N/((N : ℝ)+1)^4 ≤
    u^(N+1)*∑ n ∈ (coreBand u N (dyadicPrimeCount j)).filter
      (fun n => n.primeFactors.card = 3), f n
  calc
    _ ≤ u^(N+1)*((c*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3)*Q) :=
      box_scalar_lower hu0.le hc.le (show 1 ≤ N by omega)
    _ ≤ u^(N+1)*((T.card : ℝ)*Q) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hQ) (pow_nonneg hu0.le _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (hs.trans hwhole) (pow_nonneg hu0.le _)

/-- A bounded, vanishing, or merely cofinally bounded allowance cannot pay
the remaining rising-edge clipping loss. This conclusion concerns the
specified loss, not the actual joint signed carrier. -/
theorem edge_loss_tendsto_atTop {u y : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : y ≠ 0) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*
      ∑ n ∈ (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)).filter
            (fun n => n.primeFactors.card = 3),
        (Real.log n/SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))*
        max 0 (Real.log n.minFac-max 0
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)-
            Real.log (ZetaRieszPrimeEndpoint.largestPrime n)))*
        max (-(((1-boundedShare (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
            (dyadicMomentOrder j) n : ℝ) : ℂ)*
          zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re) 0) atTop atTop := by
  obtain ⟨k,hk,hbound⟩ := eventually_edge_loss_growth hu hU hy
  have ht := ((geometric_over_successor_four_tendsto (by linarith : 1 < 2*u)).comp
    tendsto_dyadicMomentOrder).const_mul_atTop hk
  apply tendsto_atTop_mono' atTop hbound
  simpa only [Function.comp_def,mul_div_assoc] using ht

/-- Under the existing exposed-zero source theorem, charging even just
the three-prime edge loss drives the proposed lower comparison to minus
infinity. Asking for a cofinal floor instead of an eventual floor does
not repair this particular information loss. The unchanged core itself
still has its original finite source. -/
theorem edge_charged_core_tendsto_atBot (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    let u := 3/2-rho.1.re
    Tendsto (fun j =>
      ((u : ℂ)^(dyadicMomentOrder j+1)*
        coreResponse u rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
      u^(dyadicMomentOrder j+1)*
        ∑ n ∈ (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)).filter
          (fun n => n.primeFactors.card = 3),
          (Real.log n/SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))*
          max 0 (Real.log n.minFac-max 0
            (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)-
              Real.log (ZetaRieszPrimeEndpoint.largestPrime n)))*
          max (-(((1-boundedShare (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
              (dyadicMomentOrder j) n : ℝ) : ℂ)*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*rho.1.im) n).re) 0)
      atTop atBot := by
  let u := 3/2-rho.1.re
  have hu : 1/2 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu0 : 0 ≤ u := by linarith
  have hy : rho.1.im ≠ 0 := by
    have h := ZetaRieszShiftedCenter.height_gt_fiftyFour rho hrho
    intro he
    rw [he,abs_zero] at h
    norm_num at h
  let c : ℂ := -(analyticZetaZeroMultiplicity rho : ℂ)+
    (analyticZetaZeroMultiplicity rho : ℂ)^2*(ZetaRieszMaskSupport.retainedCost u : ℂ)
  have hc : Tendsto (fun j => (u : ℂ)^(dyadicMomentOrder j+1)*
      coreResponse u rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)) atTop (𝓝 c) := by
    have hs := (ZetaRieszDominantAllocation.tendsto_nondominant_exact_source rho hrho hexposed
      (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)).sub
        (ZetaRieszJointFloor.tendsto_nondominant_sub_core hu0 hU rho.1.im)
    simp only [sub_zero] at hs
    exact hs.congr' (Eventually.of_forall fun _ => by ring)
  have hb := (Complex.continuous_re.tendsto c |>.comp hc).eventually_lt_const
    (show c.re < c.re+1 by linarith)
  have he := edge_loss_tendsto_atTop hu hU hy
  apply tendsto_atBot.mpr
  intro b
  filter_upwards [hb,he.eventually_ge_atTop (c.re+1-b)] with j hbj hej
  dsimp only [Function.comp_def] at hbj
  linarith

end
end RiemannGaussian.ZetaRieszJointEdgeLoss
