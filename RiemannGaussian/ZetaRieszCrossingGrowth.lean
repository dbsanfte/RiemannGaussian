/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSignedCrossing
import RiemannGaussian.ZetaRieszSharpPrimeWindows
import RiemannGaussian.ZetaRieszRectangleGeometry
/-!
# Actual prime boxes testing the cutoff-crossing cost

These are ordinary-prime labels at the literal moving cutoff, with the
original allocation and phase. Their crossing correction is favorable at a
negative cosine peak. Paying its absolute value instead loses that credit.
The quantitative lower bound uses proved prime counts, not numerical density
transport of the signed carrier.
-/

namespace RiemannGaussian.ZetaRieszCrossingGrowth
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszSignedCrossing ZetaRieszAllowancePrimeBoxes ZetaRieszJointAllocation
open ZetaRieszAllowanceGrowth ZetaRieszSharpPrimeWindows ZetaRieszOneSidedArithmetic

/-- Three ordered windows meet the moving Riesz crossing exactly. -/
def starts (L v w : ℝ) : Fin 3 → ℝ := ![v-L+w,L/2-w,L/2+3*w]

/-- Literal prime tuples, with no continuum replacement. -/
def primeTuples (L v w : ℝ) : Finset (Fin 3 → ℕ) :=
  Fintype.piFinset (fun i => logPrimes (starts L v w i) w)

/-- The same crossing error as in the global affine estimate, on the
concrete uniquely ordered prime box. -/
def boxCrossing (A : Finset ℕ) (L : ℝ) (N : ℕ) (y v w : ℝ) : ℝ :=
  ∑ p ∈ primeTuples L v w, crossingAtom A L N y v (p 1*p 0) (p 2)

private theorem window_geometry {N : ℕ} (hN : 100 ≤ N) {L v w : ℝ}
    (hLl : (137/100 : ℝ)*N ≤ L) (hLu : L ≤ (7/5 : ℝ)*N)
    (hvl : 2*(N : ℝ) ≤ v) (hvu : v ≤ 2*N+1/2)
    (hw : 0 < w) (hwu : w ≤ 1/100) :
    (∀ i, (1/2 : ℝ)*N ≤ starts L v w i ∧ starts L v w i+w ≤ (N : ℝ)+1) ∧
      (∀ i j, i < j → starts L v w i+w ≤ starts L v w j) ∧
      0 < v-L ∧ v-L < L/2-w ∧ v-L/2+6*w ≤ L ∧
        2*(N : ℝ) ≤ v+3*w ∧ v+6*w ≤ 2*N+1 := by
  have hn : (100 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    fin_cases i <;> norm_num [starts] <;> constructor <;> linarith
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> norm_num [starts] <;> linarith
  all_goals linarith

/-- The product map is injective: the box never multiplies its credit by
counting different prime incidences of the same integer. -/
theorem product_injective {N : ℕ} (hN : 100 ≤ N) {L v w : ℝ}
    (hLl : (137/100 : ℝ)*N ≤ L) (hLu : L ≤ (7/5 : ℝ)*N)
    (hvl : 2*(N : ℝ) ≤ v) (hvu : v ≤ 2*N+1/2)
    (hw : 0 < w) (hwu : w ≤ 1/100) :
    Set.InjOn (fun p : Fin 3 → ℕ => ∏ i, p i) (primeTuples L v w : Set _) :=
  ordered_product_injective (window_geometry hN hLl hLu hvl hvu hw hwu).2.1

private theorem tuple_logs {L v w : ℝ} {p : Fin 3 → ℕ}
    (hp : p ∈ primeTuples L v w) :
    (∀ i, (p i).Prime) ∧
    (v-L+w < Real.log (p 0) ∧ Real.log (p 0) ≤ v-L+2*w) ∧
    (L/2-w < Real.log (p 1) ∧ Real.log (p 1) ≤ L/2) ∧
    (L/2+3*w < Real.log (p 2) ∧ Real.log (p 2) ≤ L/2+4*w) := by
  have hb i := logPrimes_bounds (Fintype.mem_piFinset.mp hp i)
  refine ⟨fun i => (hb i).1,?_,?_,?_⟩
  · simpa [starts,show v-L+w+w = v-L+2*w by ring] using (hb 0).2
  · simpa [starts] using (hb 1).2
  · simpa [starts,show L/2+3*w+w = L/2+4*w by ring] using (hb 2).2

/-- Each literal box atom supplies a positive crossing correction of at
least `w/2` times its original factorial envelope. -/
theorem box_atom_lower (A : Finset ℕ) {N : ℕ} (hN : 100 ≤ N) {L v w y : ℝ}
    (hLl : (137/100 : ℝ)*N ≤ L) (hLu : L ≤ (7/5 : ℝ)*N)
    (hvl : 2*(N : ℝ) ≤ v) (hvu : v ≤ 2*N+1/2)
    (hw : 0 < w) (hwu : w ≤ 1/100) (hwy : 6 * |y| * w ≤ 1/2)
    (hphase : Real.cos (y*v) = -1)
    (hshare : (1/2 : ℝ) ≤ 1-3*Real.exp (-(N : ℝ)/64))
    {p : Fin 3 → ℕ} (hp : p ∈ primeTuples L v w) :
    (w/2)*(Real.exp (-(3/2 : ℝ)*(2*N+1))*(2*N)^N/N.factorial) ≤
      crossingAtom A L N y v (p 1*p 0) (p 2) := by
  have hn : (100 : ℝ) ≤ N := by exact_mod_cast hN
  have hg := window_geometry hN hLl hLu hvl hvu hw hwu
  obtain ⟨hpp,hr,hq,hp'⟩ := tuple_logs hp
  have ho i j (hij : i < j) : p i < p j := logPrimes_order (hg.2.1 i j hij)
    (Fintype.mem_piFinset.mp hp i) (Fintype.mem_piFinset.mp hp j)
  have hqp := ho 1 2 (by decide)
  have hrq := ho 0 1 (by decide)
  have hdata := ZetaRieszSkewAllocation.ordered_triple_data (hpp 2) (hpp 1) (hpp 0) hqp hrq
  let n := p 2*(p 1*p 0)
  have hlog : Real.log n = Real.log (p 2)+Real.log (p 1)+Real.log (p 0) := by
    dsimp [n]
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast (hpp 2).ne_zero)
      (by exact_mod_cast Nat.mul_ne_zero (hpp 1).ne_zero (hpp 0).ne_zero),Nat.cast_mul,
      Real.log_mul (by exact_mod_cast (hpp 1).ne_zero) (by exact_mod_cast (hpp 0).ne_zero)]
    ring
  have ht : v+3*w < Real.log n ∧ Real.log n ≤ v+6*w := by rw [hlog]; constructor <;> linarith
  have hbal : ∀ q ∈ n.primeFactors, Real.log q ≤ Real.log n/2 := by
    intro q hqn
    rw [hdata.2.1] at hqn
    simp only [Finset.mem_insert,Finset.mem_singleton] at hqn
    rcases hqn with rfl | rfl | rfl <;> rw [hlog] <;> linarith
  have hn1 : 1 < n := (hpp 2).one_lt.trans_le
    (Nat.le_mul_of_pos_right _ (Nat.mul_pos (hpp 1).pos (hpp 0).pos))
  have halloc : boundedShare A N n ≤ 3*Real.exp (-(N : ℝ)/64) := by
    unfold boundedShare
    split_ifs
    · have ha := ZetaRieszBalancedCompanion.share_small_of_selected_primes_balanced
        A N hdata.1 hn1 (fun q hq _ _ => hbal q hq)
      rw [hdata.2.2.1] at ha
      norm_num only [Nat.cast_ofNat] at ha
      exact ha
    · positivity
  have hcos : Real.cos (y*Real.log n) ≤ -(1/2 : ℝ) := by
    have he := Real.abs_cos_sub_cos_le (y*Real.log n) (y*v)
    rw [hphase,← mul_sub,abs_mul,abs_of_nonneg (by linarith : 0 ≤ Real.log n-v)] at he
    have hm := mul_le_mul_of_nonneg_left (show Real.log n-v ≤ 6*w by linarith) (abs_nonneg y)
    linarith [le_abs_self (Real.cos (y*Real.log n)-(-1))]
  have hl := triple_crossingAtom_lower A N (hpp 2) (hpp 1) (hpp 0) hqp.ne'
    (hrq.trans hqp).ne' hrq.ne' (by linarith : 0 < L) hw.le hg.2.2.1
    (by linarith [hg.2.2.2.1]) (by linarith) (by linarith) (by linarith [hg.2.2.2.2.1])
    (by change (1/2 : ℝ) ≤ 1-boundedShare A N n; linarith) hcos
  apply le_trans _ hl
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ w/2)
  unfold amplitude
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul
  · exact Real.exp_le_exp.mpr (by change -(3/2 : ℝ)*(2*N+1) ≤ -(3/2 : ℝ)*Real.log n; linarith [hg.2.2.2.2.2.2])
  · exact pow_le_pow_left₀ (by positivity) (by change 2*(N : ℝ) ≤ Real.log n; linarith) N
  · positivity
  · positivity

/-- The literal moving crossing box contains a positive full-density
population. The prime theorem is used only for an unsigned count. -/
theorem eventually_box_count {w : ℝ} (hw : 0 < w) (hwu : w ≤ 1/100) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ L v : ℝ,
      (137/100 : ℝ)*N ≤ L → L ≤ (7/5 : ℝ)*N →
      2*(N : ℝ) ≤ v → v ≤ 2*N+1/2 →
      c^3*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3 ≤ ((primeTuples L v w).card : ℝ) := by
  let c := (Real.exp w-1)/2
  have hc : 0 < c := by dsimp [c]; linarith [Real.one_lt_exp_iff.mpr hw]
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_card_bounds hw (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (0 : ℝ) < 1/2),eventually_ge_atTop (100 : ℕ)]
      with N hcount hN L v hLl hLu hvl hvu
  have hg := window_geometry hN hLl hLu hvl hvu hw hwu
  have hb i : c*Real.exp (starts L v w i)/((N : ℝ)+1) ≤
      ((logPrimes (starts L v w i) w).card : ℝ) := by
    have h := (hcount (starts L v w i) (hg.1 i).1).1
    have ha : 0 < starts L v w i+w := by
      have hn : (100 : ℝ) ≤ N := by exact_mod_cast hN
      linarith [(hg.1 i).1]
    apply le_trans _ h
    convert div_le_div_of_nonneg_left (by positivity : 0 ≤ c*Real.exp (starts L v w i))
      ha (hg.1 i).2 using 1
    dsimp [c]
    ring
  have hprod : (∏ i : Fin 3, c*Real.exp (starts L v w i)/((N : ℝ)+1)) ≤
      ((primeTuples L v w).card : ℝ) := by
    rw [primeTuples,Fintype.card_piFinset,Nat.cast_prod]
    exact Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hb i)
  have he : (∏ i : Fin 3, c*Real.exp (starts L v w i)/((N : ℝ)+1)) =
      c^3*Real.exp (v+3*w)/((N : ℝ)+1)^3 := by
    rw [Fin.prod_univ_three]
    change (c*Real.exp (v-L+w)/((N : ℝ)+1))*(c*Real.exp (L/2-w)/((N : ℝ)+1))*
      (c*Real.exp (L/2+3*w)/((N : ℝ)+1)) = _
    have he : Real.exp (v-L+w)*Real.exp (L/2-w)*Real.exp (L/2+3*w) = Real.exp (v+3*w) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    calc
      _ = c^3*(Real.exp (v-L+w)*Real.exp (L/2-w)*Real.exp (L/2+3*w))/((N : ℝ)+1)^3 := by
        field_simp
      _ = _ := by rw [he]
  rw [he] at hprod
  apply le_trans _ hprod
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)) (by positivity)

/-- The actual favorable crossing correction has the same superunit source
rate as the absolute carrier. It cannot be paid as a source-small error. -/
theorem eventually_box_crossing_growth {w y : ℝ} (hw : 0 < w) (hwu : w ≤ 1/100)
    (hwy : 6 * |y| * w ≤ 1/2) {u : ℝ} (hu : 0 < u) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (L v : ℝ),
      (137/100 : ℝ)*N ≤ L → L ≤ (7/5 : ℝ)*N →
      2*(N : ℝ) ≤ v → v ≤ 2*N+1/2 → Real.cos (y*v) = -1 →
      c*(2*u)^N/((N : ℝ)+1)^4 ≤ u^(N+1)*boxCrossing A L N y v w := by
  obtain ⟨c,hc,hcount⟩ := eventually_box_count hw hwu
  let k := 2*w*(u*c^3*Real.exp (-(3/2 : ℝ))/24)
  refine ⟨k,by dsimp [k]; positivity,?_⟩
  filter_upwards [hcount,eventually_triple_unassigned,eventually_ge_atTop (100 : ℕ)]
    with N hcount hshare hN A L v hLl hLu hvl hvu hphase
  let Q := Real.exp (-(3/2 : ℝ)*(2*N+1))*(2*N)^N/N.factorial
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hsum : ((primeTuples L v w).card : ℝ)*(w/2*Q) ≤ boxCrossing A L N y v w := by
    rw [← nsmul_eq_mul,← Finset.sum_const]
    exact Finset.sum_le_sum (fun p hp => box_atom_lower A hN hLl hLu hvl hvu hw hwu hwy hphase hshare hp)
  have hscalar := mul_le_mul_of_nonneg_left
    (triple_box_scalar_lower hu.le hc.le (by omega : 1 ≤ N) (D := 1))
    (by positivity : (0 : ℝ) ≤ 2*w)
  simp only [mul_one] at hscalar
  calc
    k*(2*u)^N/((N : ℝ)+1)^4 ≤
        u^(N+1)*(c^3*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3*(w/2*Q)) := by
      calc
        _ = 2*w*((u*c^3*Real.exp (-(3/2 : ℝ))/24)*(2*u)^N/((N : ℝ)+1)^4) := by
          dsimp [k]
          ring
        _ ≤ _ := hscalar
        _ = _ := by dsimp [Q]; ring
    _ ≤ u^(N+1)*(((primeTuples L v w).card : ℝ)*(w/2*Q)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hcount L v hLl hLu hvl hvu)
        (mul_nonneg (by positivity) hQ)) (pow_nonneg hu.le _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (pow_nonneg hu.le _)

private theorem tuple_log_product {L v w : ℝ} {p : Fin 3 → ℕ}
    (hp : p ∈ primeTuples L v w) :
    Real.log (p 2*(p 1*p 0) : ℕ) = Real.log (p 2)+Real.log (p 1)+Real.log (p 0) := by
  have hpp := (tuple_logs hp).1
  rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast (hpp 2).ne_zero)
    (by exact_mod_cast Nat.mul_ne_zero (hpp 1).ne_zero (hpp 0).ne_zero),Nat.cast_mul,
    Real.log_mul (by exact_mod_cast (hpp 1).ne_zero) (by exact_mod_cast (hpp 0).ne_zero)]
  ring

/-- Every tested integer belongs to the unchanged literal core. Physical,
count and nondominant masks follow from the actual prime geometry. -/
theorem tuple_mem_core (j : ℕ) (hj : 32 ≤ j) {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hN : 100 ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) {v w : ℝ}
    (hLl : (137/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
    (hLu : SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) ≤
      (7/5 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
    (hvl : 2*(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ) ≤ v)
    (hvu : v ≤ 2*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1/2)
    (hw : 0 < w) (hwu : w ≤ 1/100) {p : Fin 3 → ℕ}
    (hp : p ∈ primeTuples (SquarefreeVaughanLogSource.length u
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)) v w) :
    (∏ i, p i) ∈ ZetaRieszParityPacket.coreBand u
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) := by
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  have hn : (100 : ℝ) ≤ N := by exact_mod_cast hN
  have hg := window_geometry hN hLl hLu hvl hvu hw hwu
  obtain ⟨hpp,hr,hq,hp'⟩ := tuple_logs hp
  have ho i j (hij : i < j) : p i < p j := logPrimes_order (hg.2.1 i j hij)
    (Fintype.mem_piFinset.mp hp i) (Fintype.mem_piFinset.mp hp j)
  have hd := ZetaRieszSkewAllocation.ordered_triple_data (hpp 2) (hpp 1) (hpp 0)
    (ho 1 2 (by decide)) (ho 0 1 (by decide))
  have he : (∏ i, p i) = p 2*(p 1*p 0) := by rw [Fin.prod_univ_three]; ring
  rw [he]
  apply ZetaRieszCoupledWindow.mem_core_of_prime_share_le j hj hu hU (by dsimp [N] at *; linarith)
    hd.1 (by rw [hd.2.2.1]) (by
      rw [hd.2.2.1]
      exact lt_of_lt_of_le (by decide : 3 < 4)
        (ZetaRieszPrimeCountFrequency.four_le_dyadicPrimeCount j))
  · rw [tuple_log_product hp]
    change (39/20 : ℝ)*N < _
    change 2*(N : ℝ) ≤ v at hvl
    linarith
  · rw [tuple_log_product hp]
    change _ ≤ (203/100 : ℝ)*N
    change v ≤ 2*(N : ℝ)+1/2 at hvu
    linarith
  · intro q hqmem
    rw [hd.2.1] at hqmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hqmem
    rw [tuple_log_product hp]
    change (137/100 : ℝ)*N ≤ L at hLl
    change L ≤ (7/5 : ℝ)*N at hLu
    change 2*(N : ℝ) ≤ v at hvl
    change v ≤ 2*(N : ℝ)+1/2 at hvu
    change v-L+w < _ ∧ _ ≤ v-L+2*w at hr
    change L/2-w < _ ∧ _ ≤ L/2 at hq
    change L/2+3*w < _ ∧ _ ≤ L/2+4*w at hp'
    rcases hqmem with rfl | rfl | rfl <;> linarith

/-- The tuple sum is exactly the unique-largest-prime incidence sum over
integer labels. No pair averaging or artificial multiplicity is used. -/
theorem boxCrossing_eq_owned (A : Finset ℕ) {N : ℕ} (hN : 100 ≤ N) {L v w y : ℝ}
    (hLl : (137/100 : ℝ)*N ≤ L) (hLu : L ≤ (7/5 : ℝ)*N)
    (hvl : 2*(N : ℝ) ≤ v) (hvu : v ≤ 2*N+1/2)
    (hw : 0 < w) (hwu : w ≤ 1/100) :
    boxCrossing A L N y v w = ∑ n ∈ (primeTuples L v w).image (fun p => ∏ i, p i),
      crossingAtom A L N y v (n/ZetaRieszPrimeEndpoint.largestPrime n)
        (ZetaRieszPrimeEndpoint.largestPrime n) := by
  rw [Finset.sum_image (product_injective hN hLl hLu hvl hvu hw hwu)]
  apply Finset.sum_congr rfl
  intro p hp
  have hg := window_geometry hN hLl hLu hvl hvu hw hwu
  have hpp := (tuple_logs hp).1
  have ho i j (hij : i < j) : p i < p j := logPrimes_order (hg.2.1 i j hij)
    (Fintype.mem_piFinset.mp hp i) (Fintype.mem_piFinset.mp hp j)
  have hd := ZetaRieszSkewAllocation.ordered_triple_data (hpp 2) (hpp 1) (hpp 0)
    (ho 1 2 (by decide)) (ho 0 1 (by decide))
  have he : (∏ i, p i) = p 2*(p 1*p 0) := by rw [Fin.prod_univ_three]; ring
  rw [he,hd.2.2.2.1,Nat.mul_div_cancel_left _ (hpp 2).pos]

/-- The literal absolute crossing cost in a single full radial period.
It is an audit of the proposed separate error payment, not a new carrier. -/
def absolutePeriodCrossing (u y : ℝ) (j : ℕ) (v : ℝ) : ℝ :=
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  u^(N+1)*(∑ n ∈ (ZetaRieszParityPacket.coreBand u N
    (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).filter
      (fun n : ℕ => |Real.log n-v| ≤ Real.pi/|y|),
    |crossingAtom A L N y v (n/ZetaRieszPrimeEndpoint.largestPrime n)
      (ZetaRieszPrimeEndpoint.largestPrime n)|)

/-- The actual core period pays at least the full positive crossing box.
This lower bound survives every literal support and ownership restriction. -/
theorem box_le_absolutePeriod (j : ℕ) (hj : 32 ≤ j) {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hN : 100 ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) {v w y : ℝ}
    (hLl : (137/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
    (hLu : SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) ≤
      (7/5 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
    (hvl : 2*(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ) ≤ v)
    (hvu : v ≤ 2*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1/2)
    (hw : 0 < w) (hwu : w ≤ 1/100) (hperiod : 6*w ≤ Real.pi/|y|) :
    u^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      boxCrossing (ZetaRieszAnnulusJoint.intermediatePrimes u
        (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
        (SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
        (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) y v w ≤ absolutePeriodCrossing u y j v := by
  rw [boxCrossing_eq_owned _ hN hLl hLu hvl hvu hw hwu]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith : 0 ≤ u) _)
  apply le_trans (Finset.sum_le_sum (fun n _ => le_abs_self _))
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun n _ _ => abs_nonneg _)
  intro n hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  refine Finset.mem_filter.mpr ⟨tuple_mem_core j hj hu hU hN hLl hLu hvl hvu hw hwu hp,?_⟩
  have hb := tuple_logs hp
  have he : (∏ i, p i) = p 2*(p 1*p 0) := by rw [Fin.prod_univ_three]; ring
  rw [he,tuple_log_product hp]
  apply abs_le.mpr
  constructor <;> linarith [hb.2.1,hb.2.2.1,hb.2.2.2]

/-- The actual moving-length core has a superunit lower bound for the
absolute crossing cost at every negative saddle peak. This is a lower
bound for literal primes, not just divergence of a loose majorant. -/
theorem eventually_period_crossing_growth {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ |y|) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      2*(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ) ≤ v →
      v ≤ 2*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1/2 → Real.cos (y*v) = -1 →
      c*(2*u)^ZetaRieszPrimeCountFrequency.dyadicMomentOrder j/
        ((ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ)+1)^4 ≤
          absolutePeriodCrossing u y j v := by
  have hy0 : 0 < |y| := by linarith
  let w := Real.pi/(64*|y|)
  have hw : 0 < w := by dsimp [w]; positivity
  have hwu : w ≤ 1/100 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 64*|y|)).mpr
    nlinarith [Real.pi_lt_four]
  have hwy : 6 * |y| * w ≤ 1/2 := by
    dsimp [w]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    field_simp
    nlinarith [Real.pi_lt_four]
  have hperiod : 6*w ≤ Real.pi/|y| := by
    dsimp [w]
    field_simp
    nlinarith [Real.pi_pos]
  obtain ⟨c,hc,hgrowth⟩ := eventually_box_crossing_growth hw hwu hwy (by linarith : 0 < u)
  refine ⟨c,hc,?_⟩
  have hlu : u < Real.exp (-(137/200 : ℝ)) :=
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source).trans
      (Real.exp_lt_exp.mpr (by norm_num))
  have hlength := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200) hlu
  norm_num only [show (2 : ℝ)*(137/200) = 137/100 by norm_num] at hlength
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hgrowth,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hlength,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (100 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hgrowth hLl hN hj v hvl hvu hphase
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  have hLu : L ≤ (7/5 : ℝ)*N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu.le (by omega : 2 ≤ N)
    change L ≤ _ at h
    nlinarith [Real.log_two_lt_d9,Nat.cast_nonneg (α := ℝ) N]
  exact (hgrowth (ZetaRieszAnnulusJoint.intermediatePrimes u N) L v hLl hLu hvl hvu hphase).trans
    (box_le_absolutePeriod j hj hu hU hN hLl hLu hvl hvu hw hwu hperiod)

/-- No constant can bound all full-period absolute crossing costs at source
scale. The combined signed moments and crossing correction must remain
coupled; refining only their separate absolute payment cannot close RH. -/
theorem not_eventually_period_cost_bounded {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ |y|) (C : ℝ) :
    ¬∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      2*(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ) ≤ v →
      v ≤ 2*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1/2 → Real.cos (y*v) = -1 →
        absolutePeriodCrossing u y j v ≤ C := by
  obtain ⟨c,hc,hgrowth⟩ := eventually_period_crossing_growth hu hU hy
  have ht := ((geometric_over_successor_four_tendsto (by linarith : 1 < 2*u)).comp
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder).const_mul_atTop hc
  simp only [Function.comp_def] at ht
  intro hbound
  obtain ⟨j,hj,hb,hcN⟩ := (hgrowth.and (hbound.and (ht.eventually_gt_atTop C))).exists
  obtain ⟨v,hvl,hvu,hphase⟩ := ZetaRieszCapacityPhaseBudget.exists_negative_peak hy
    (2*(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ))
  have hl := hj v hvl hvu hphase
  have hu' := hb v hvl hvu hphase
  rw [mul_div_assoc] at hl
  linarith only [hl,hu',hcN]

end
end RiemannGaussian.ZetaRieszCrossingGrowth
