/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFourOrderingBudget

/-!
# A finite phase-period budget for the checked capacity constants

The favorable and adverse radial factors are compared before summing.
The central quarter of a full cosine period provides enough credit even
with a deliberately crude phase bound. Every cosine-zero neighborhood
remains charged; no phase cell or radial endpoint is removed.
-/

namespace RiemannGaussian.ZetaRieszCapacityPhaseBudget
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- A short original total-log interval loses at most one percent of its
left-endpoint radial weight on the favorable side. -/
theorem lower_radial {N : ℕ} {t h : ℝ} (ht : 0 ≤ t) (hhu : h ≤ 1/100000) :
    (99/100 : ℝ)*(Real.exp (-t/2)*t^N/N.factorial) ≤
      Real.exp (-(t+h)/2)*t^N/N.factorial := by
  have hex : (99/100 : ℝ) ≤ Real.exp (-h/2) := by
    have hh := Real.add_one_le_exp (-h/2)
    linarith
  have hm := mul_le_mul_of_nonneg_right hex
    (show 0 ≤ Real.exp (-t/2)*t^N/N.factorial by positivity)
  calc
    _ ≤ Real.exp (-h/2)*(Real.exp (-t/2)*t^N/N.factorial) := hm
    _ = _ := by
      rw [show -(t+h)/2 = -h/2+(-t/2) by ring,Real.exp_add]
      ring

/-- The adverse radial factor costs at most one thousandth on the same
literal short interval, without changing the factorial moment. -/
theorem upper_radial {N : ℕ} {t h : ℝ} (ht : 0 < t) (hNt : (N : ℝ) ≤ t)
    (hh : 0 ≤ h) (hhu : h ≤ 1/100000) :
    Real.exp (-t/2)*(t+h)^N/N.factorial ≤
      (1001/1000 : ℝ)*(Real.exp (-t/2)*t^N/N.factorial) := by
  have hth : 0 < t+h := by linarith
  have hlog := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hth ht)) (Nat.cast_nonneg N)
  rw [Real.log_div hth.ne' ht.ne'] at hlog
  have hratio : (N : ℝ)/t ≤ 1 := (div_le_iff₀ ht).mpr (by linarith)
  have hid : (N : ℝ)*((t+h)/t-1) = h*((N : ℝ)/t) := by field_simp; ring
  rw [hid] at hlog
  have hexp : -t/2+(N : ℝ)*Real.log (t+h) ≤
      (1/100000 : ℝ)+(-t/2+(N : ℝ)*Real.log t) := by
    nlinarith [mul_le_mul_of_nonneg_left hratio hh]
  have hpow (x : ℝ) (hx : 0 < x) : x^N = Real.exp ((N : ℝ)*Real.log x) := by
    rw [Real.exp_nat_mul,Real.exp_log hx]
  rw [hpow t ht,hpow (t+h) hth,← Real.exp_add,← Real.exp_add]
  have hb : Real.exp (1/100000 : ℝ) ≤ 1001/1000 :=
    (Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1/100000)
      (by norm_num : (1/100000 : ℝ) < 1)).trans (by norm_num)
  calc
    _ ≤ Real.exp ((1/100000 : ℝ)+(-t/2+(N : ℝ)*Real.log t))/N.factorial :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = Real.exp (1/100000 : ℝ)*(Real.exp (-t/2+(N : ℝ)*Real.log t)/N.factorial) := by
      rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (by positivity)

/-- The calibrated capacity constants pay the opposite-phase population
at a positive cosine peak, with an explicit strictly negative surplus. -/
theorem positive_peak_capacity_budget {N : ℕ} {t h ε : ℝ}
    (ht : 0 < t) (hNt : (N : ℝ) ≤ t) (hh : 0 ≤ h) (hhu : h ≤ 1/100000)
    (he : 0 ≤ ε) (heu : ε ≤ 1/10000) :
    (133555/1000000 : ℝ)*((Real.exp (-t/2)*(t+h)^N/N.factorial)*(1+ε)*h)-
      (6823/50000 : ℝ)*((Real.exp (-(t+h)/2)*t^N/N.factorial)*(1-ε)*h) ≤
      -(1/1000 : ℝ)*(Real.exp (-t/2)*t^N/N.factorial)*h := by
  have hlow := lower_radial (N := N) ht.le hhu
  have hupp := upper_radial (N := N) ht hNt hh hhu
  have he1 : 0 ≤ 1-ε := by linarith only [heu]
  have hmL := mul_le_mul_of_nonneg_right hlow
    (show 0 ≤ (6823/50000 : ℝ)*(1-ε)*h by positivity)
  have hmU := mul_le_mul_of_nonneg_right hupp
    (show 0 ≤ (133555/1000000 : ℝ)*(1+ε)*h by positivity)
  have hcoef : (133555/1000000 : ℝ)*(1001/1000)*(1+ε)-
      (6823/50000)*(99/100)*(1-ε) ≤ -(1/1000 : ℝ) := by linarith only [heu]
  have hpaid := mul_le_mul_of_nonneg_right hcoef
    (show 0 ≤ (Real.exp (-t/2)*t^N/N.factorial)*h by positivity)
  nlinarith only [hmL,hmU,hpaid]

/-- The same five-prime population still pays the four-prime debit PLUS
the explicit balanced-triple debit at a negative cosine peak. -/
theorem negative_peak_with_triples {N : ℕ} {t h ε : ℝ}
    (ht : 0 < t) (hNt : (N : ℝ) ≤ t) (hh : 0 ≤ h) (hhu : h ≤ 1/100000)
    (he : 0 ≤ ε) (heu : ε ≤ 1/10000) :
    (1/1000 : ℝ)*(Real.exp (-t/2)*t^N/N.factorial)*h ≤
      (8529739/62500000 : ℝ)*((Real.exp (-(t+h)/2)*t^N/N.factorial)*(1-ε)*h)-
        (133521/1000000 : ℝ)*((Real.exp (-t/2)*(t+h)^N/N.factorial)*(1+ε)*h) := by
  have hlow := lower_radial (N := N) ht.le hhu
  have hupp := upper_radial (N := N) ht hNt hh hhu
  have he1 : 0 ≤ 1-ε := by linarith only [heu]
  have hmL := mul_le_mul_of_nonneg_right hlow
    (show 0 ≤ (8529739/62500000 : ℝ)*(1-ε)*h by positivity)
  have hmU := mul_le_mul_of_nonneg_right hupp
    (show 0 ≤ (133521/1000000 : ℝ)*(1+ε)*h by positivity)
  have hcoef : (1/1000 : ℝ) ≤ (8529739/62500000)*(99/100)*(1-ε)-
      (133521/1000000)*(1001/1000)*(1+ε) := by linarith only [heu]
  have hpaid := mul_le_mul_of_nonneg_right hcoef
    (show 0 ≤ (Real.exp (-t/2)*t^N/N.factorial)*h by positivity)
  nlinarith only [hmL,hmU,hpaid]

/-- At the opposite peak, the balanced triple band fits the calibrated
upper budget too, leaving the same one-thousandth negative surplus. -/
theorem positive_peak_with_triples {N : ℕ} {t h ε : ℝ}
    (ht : 0 < t) (hNt : (N : ℝ) ≤ t) (hh : 0 ≤ h) (hhu : h ≤ 1/100000)
    (he : 0 ≤ ε) (heu : ε ≤ 1/10000) :
    (133655/1000000 : ℝ)*((Real.exp (-t/2)*(t+h)^N/N.factorial)*(1+ε)*h)-
      (6823/50000 : ℝ)*((Real.exp (-(t+h)/2)*t^N/N.factorial)*(1-ε)*h) ≤
        -(1/1000 : ℝ)*(Real.exp (-t/2)*t^N/N.factorial)*h := by
  have hlow := lower_radial (N := N) ht.le hhu
  have hupp := upper_radial (N := N) ht hNt hh hhu
  have he1 : 0 ≤ 1-ε := by linarith only [heu]
  have hmL := mul_le_mul_of_nonneg_right hlow
    (show 0 ≤ (6823/50000 : ℝ)*(1-ε)*h by positivity)
  have hmU := mul_le_mul_of_nonneg_right hupp
    (show 0 ≤ (133655/1000000 : ℝ)*(1+ε)*h by positivity)
  have hcoef : (133655/1000000 : ℝ)*(1001/1000)*(1+ε)-
      (6823/50000)*(99/100)*(1-ε) ≤ -(1/1000 : ℝ) := by linarith only [heu]
  have hpaid := mul_le_mul_of_nonneg_right hcoef
    (show 0 ≤ (Real.exp (-t/2)*t^N/N.factorial)*h by positivity)
  nlinarith only [hmL,hmU,hpaid]

/-- The left edge of a complete negative-peak period is a positive peak,
for either sign of the original height. -/
theorem cos_left_edge {y v : ℝ} (hy : 0 < |y|) (hv : Real.cos (y*v) = -1) :
    Real.cos (y*(v-Real.pi/|y|)) = 1 := by
  by_cases hpos : 0 ≤ y
  · rw [abs_of_nonneg hpos] at hy ⊢
    have he : y*(v-Real.pi/y) = y*v-Real.pi := by field_simp
    rw [he,Real.cos_sub_pi,hv]
    norm_num
  · have hn : y < 0 := lt_of_not_ge hpos
    rw [abs_of_neg hn]
    have he : y*(v-Real.pi/(-y)) = y*v+Real.pi := by
      field_simp [hn.ne]
      ring
    rw [he,Real.cos_add_pi,hv]
    norm_num

/-- Equal angular steps around a complete negative-cosine period. -/
def periodAngle (m i : ℕ) : ℝ := -Real.pi+(i : ℝ)*Real.pi/(4*m)

/-- Every grid point, including the right endpoint when requested,
lies in the original complete phase period. -/
theorem periodAngle_bounds {m i : ℕ} (hm : 0 < m) (hi : i ≤ 8*m) :
    -Real.pi ≤ periodAngle m i ∧ periodAngle m i ≤ Real.pi := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hiR : (i : ℝ) ≤ 8*m := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := by positivity
  unfold periodAngle
  constructor
  · have hp : 0 ≤ (i : ℝ)*Real.pi/(4*m) := by positivity
    linarith
  · have hp : (i : ℝ)*Real.pi/(4*m) ≤ 2*Real.pi := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4*m)).mpr
      nlinarith [Real.pi_pos]
    linarith

/-- The angular grid retains its exact constant step, including the last
cell's right endpoint. -/
theorem periodAngle_succ (m i : ℕ) :
    periodAngle m (i+1) = periodAngle m i+Real.pi/(4*m) := by
  simp only [periodAngle,Nat.cast_add,Nat.cast_one]
  ring

/-- Ordered grid points stay ordered without any approximation of the phase. -/
theorem periodAngle_mono {m i j : ℕ} (hm : 0 < m) (hij : i ≤ j) :
    periodAngle m i ≤ periodAngle m j := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
  unfold periodAngle
  have he := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hijR Real.pi_pos.le)
    (show (0 : ℝ) ≤ 4*m by positivity)
  linarith only [he]

/-- Equal total-log cells fit together exactly when their width is the
angular step divided by the fixed absolute height. -/
theorem period_start_succ (m i : ℕ) (b y : ℝ) :
    b+periodAngle m (i+1)/|y| =
      b+periodAngle m i/|y|+Real.pi/(4*m*|y|) := by
  rw [periodAngle_succ,add_div,div_mul_eq_div_div]
  ring

/-- One grid can be fixed for each fixed nonzero height, independent of
the growing factorial moment. Its cells have the required phase accuracy. -/
theorem exists_period_mesh {y : ℝ} (hy : 54 ≤ |y|) :
    ∃ m : ℕ, 0 < m ∧ 0 < Real.pi/(4*m*|y|) ∧
      Real.pi/(4*m*|y|) ≤ 1/100000 ∧
      |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000 := by
  have hy0 : 0 < |y| := by linarith
  refine ⟨100000,by norm_num,?_,?_,?_⟩
  · positivity
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4*(100000 : ℕ)*|y|)).mpr
    norm_num
    nlinarith [Real.pi_lt_d4]
  · have he : |y| * (Real.pi/(4*(100000 : ℕ)*|y|)) = Real.pi/400000 := by
      field_simp [ne_of_gt hy0]
      ring
    rw [he]
    nlinarith [Real.pi_lt_d4]

/-- Every real starting point has an exact negative phase peak within
half a unit in total logarithm, for either sign of the fixed ordinate. -/
theorem exists_negative_peak {y : ℝ} (hy : 54 ≤ |y|) (a : ℝ) :
    ∃ v : ℝ, a ≤ v ∧ v ≤ a+1/2 ∧ Real.cos (y*v) = -1 := by
  let z := |y|
  have hz : 0 < z := by dsimp [z]; linarith
  let k : ℤ := ⌈(z*a-Real.pi)/(2*Real.pi)⌉
  let v := ((k : ℝ)*(2*Real.pi)+Real.pi)/z
  have hklo : z*a-Real.pi ≤ (k : ℝ)*(2*Real.pi) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 2*Real.pi)).mp (Int.le_ceil _)
  have hkhi : (k : ℝ)*(2*Real.pi) < z*a-Real.pi+2*Real.pi := by
    have he := mul_lt_mul_of_pos_right (Int.ceil_lt_add_one ((z*a-Real.pi)/(2*Real.pi)))
      (by positivity : (0 : ℝ) < 2*Real.pi)
    simpa only [add_mul,div_mul_cancel₀ _ (by positivity : 2*Real.pi ≠ 0),one_mul] using he
  have hv : z*v = (k : ℝ)*(2*Real.pi)+Real.pi := by dsimp [v]; field_simp
  have hcos : Real.cos (z*v) = -1 := by
    rw [hv,Real.cos_add_pi,Real.cos_int_mul_two_pi]
  have hphase : Real.cos (z*v) = Real.cos (y*v) := by
    dsimp only [z]
    rcases le_or_gt 0 y with hp | hn
    · rw [abs_of_nonneg hp]
    · rw [abs_of_neg hn,neg_mul,Real.cos_neg]
  refine ⟨v,?_,?_,?_⟩
  · nlinarith
  · have hz54 : (54 : ℝ) ≤ z := hy
    nlinarith [Real.pi_lt_four]
  · rwa [← hphase]

/-- The original floor-defined length admits a complete phase period
inside the first certified angular bin, at every sufficiently large order.
This is literal core geometry, not a frozen T=2N substitution. -/
theorem eventually_exists_first_bin_period {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ y : ℝ, 54 ≤ |y| → ∃ v : ℝ,
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      ∀ t : ℝ, v-Real.pi/|y| ≤ t → t ≤ v+Real.pi/|y| →
        (1979971/2900000 : ℝ) ≤ SquarefreeVaughanLogSource.length u N/t ∧
        SquarefreeVaughanLogSource.length u N/t ≤ 77646131/113100000 := by
  filter_upwards [ZetaRieszFivePrimePairSupply.eventually_core_cutoff_ratio hu hU,
    eventually_ge_atTop (10000 : ℕ)] with N hratio hN y hy
  have hn : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have hy0 : 0 < |y| := by linarith
  have hpi : Real.pi/|y| ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ hy0).mpr
    linarith [Real.pi_lt_four]
  have hl := (hratio ((203/100 : ℝ)*N) (by linarith) le_rfl).1
  have hl' := (le_div_iff₀ (show (0 : ℝ) < (203/100 : ℝ)*N by positivity)).mp hl
  have hLlo : (693/500 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N := by
    linarith only [hl']
  have hLhi : SquarefreeVaughanLogSource.length u N ≤ (139/100 : ℝ)*N :=
    (ZetaRieszHeadOrders.length_le_two_log_two hu (by omega)).trans
      (mul_le_mul_of_nonneg_right (by linarith [Real.log_two_lt_d9]) (Nat.cast_nonneg N))
  obtain ⟨v,hv,hv',hpeak⟩ := exists_negative_peak hy ((81/40 : ℝ)*N)
  refine ⟨v,hpeak,by linarith,by linarith,?_⟩
  intro t ht ht'
  have ht0 : 0 < t := by linarith
  have htl : (81/40 : ℝ)*N-1 ≤ t := by linarith
  have htu : t ≤ (81/40 : ℝ)*N+1 := by linarith
  constructor
  · apply (le_div_iff₀ ht0).mpr
    linarith only [hLlo,htu,hn]
  · apply (div_le_iff₀ ht0).mpr
    linarith only [hLhi,htl,hn]

/-- The bin containing the factorial saddle covers an actual central
radial band uniformly in the restricted radius. The moving Riesz length
is retained; these bounds require no numerical angular certificate. -/
theorem eventually_central_bin_ratio {u : ℝ}
    (hu : 1/2 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ,
      (1999/1000 : ℝ)*N ≤ t → t ≤ (2001/1000 : ℝ)*N →
      (78068869/113100000 : ℝ) ≤ SquarefreeVaughanLogSource.length u N/t ∧
      SquarefreeVaughanLogSource.length u N/t ≤ 26165377/37700000 := by
  filter_upwards [ZetaRieszFivePrimePairSupply.eventually_core_cutoff_ratio hu hU,
    eventually_ge_atTop (2 : ℕ)] with N hratio hN t htlo hthi
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl := (hratio ((203/100 : ℝ)*N) (by linarith) le_rfl).1
  have hl' := (le_div_iff₀ (show (0 : ℝ) < (203/100 : ℝ)*N by positivity)).mp hl
  have hLlo : (693/500 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N := by
    linarith only [hl']
  have hLhi : SquarefreeVaughanLogSource.length u N ≤ (1387/1000 : ℝ)*N :=
    (ZetaRieszHeadOrders.length_le_two_log_two hu hN).trans
      (mul_le_mul_of_nonneg_right (by linarith [Real.log_two_lt_d9]) (Nat.cast_nonneg N))
  have ht : 0 < t := by linarith only [htlo,hn]
  constructor
  · apply (le_div_iff₀ ht).mpr
    linarith only [hLlo,hthi,hn]
  · apply (div_le_iff₀ ht).mpr
    linarith only [hLhi,htlo,hn]

/-- A full original phase period can be placed near 2N inside the central
bin and the literal core at every sufficiently large order. -/
theorem eventually_exists_central_bin_period_at_saddle {u : ℝ}
    (hu : 1/2 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ y : ℝ, 54 ≤ |y| → ∃ v : ℝ,
      (2 : ℝ)*N ≤ v ∧ v ≤ 2*N+1/2 ∧
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      ∀ t : ℝ, v-Real.pi/|y| ≤ t → t ≤ v+Real.pi/|y| →
        (78068869/113100000 : ℝ) ≤ SquarefreeVaughanLogSource.length u N/t ∧
        SquarefreeVaughanLogSource.length u N/t ≤ 26165377/37700000 := by
  filter_upwards [eventually_central_bin_ratio hu hU,eventually_ge_atTop (10000 : ℕ)]
    with N hratio hN y hy
  have hn : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have hy0 : 0 < |y| := by linarith
  have hpi : Real.pi/|y| ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ hy0).mpr
    linarith [Real.pi_lt_four]
  obtain ⟨v,hv,hv',hpeak⟩ := exists_negative_peak hy ((2 : ℝ)*N)
  refine ⟨v,hv,hv',hpeak,by linarith,by linarith,?_⟩
  intro t ht ht'
  exact hratio t (by linarith) (by linarith)

/-- The original period geometry follows while the stronger theorem also
retains the bounded displacement from the literal factorial saddle. -/
theorem eventually_exists_central_bin_period {u : ℝ}
    (hu : 1/2 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ y : ℝ, 54 ≤ |y| → ∃ v : ℝ,
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      ∀ t : ℝ, v-Real.pi/|y| ≤ t → t ≤ v+Real.pi/|y| →
        (78068869/113100000 : ℝ) ≤ SquarefreeVaughanLogSource.length u N/t ∧
        SquarefreeVaughanLogSource.length u N/t ≤ 26165377/37700000 := by
  filter_upwards [eventually_exists_central_bin_period_at_saddle hu hU] with N hN y hy
  obtain ⟨v,_,_,hv⟩ := hN y hy
  exact ⟨v,hv⟩

/-- The phase coordinates agree exactly with the usual half-open
uniform total-log grid. -/
theorem period_start_eq_linear (m i : ℕ) (b y : ℝ) :
    b+periodAngle m i/|y| = b-Real.pi/|y|+(i : ℝ)*(Real.pi/(4*m*|y|)) := by
  simp only [periodAngle,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Each complete-period cell fits in the original period, including
its right endpoint and excluding only the period's left endpoint. -/
theorem period_cell_bounds {m i : ℕ} (hm : 0 < m) (hi : i < 8*m) (b : ℝ)
    {y : ℝ} (hy : 0 < |y|) :
    b-Real.pi/|y| ≤ b+periodAngle m i/|y| ∧
      b+periodAngle m i/|y|+Real.pi/(4*m*|y|) ≤ b+Real.pi/|y| := by
  have hlo := div_le_div_of_nonneg_right (periodAngle_bounds hm hi.le).1 hy.le
  rw [neg_div] at hlo
  have hhi := div_le_div_of_nonneg_right
    (periodAngle_bounds hm (Nat.succ_le_of_lt hi)).2 hy.le
  have hs : b+periodAngle m (i+1)/|y| ≤ b+Real.pi/|y| := by linarith only [hhi]
  rw [period_start_succ] at hs
  exact ⟨by linarith only [hlo],hs⟩

/-- Successive and separated period cells have disjoint half-open
total-log interiors. This retains shared endpoints exactly once. -/
theorem period_cells_separated {m i j : ℕ} (hm : 0 < m) (hij : i < j) (b : ℝ)
    {y : ℝ} (hy : 0 < |y|) :
    b+periodAngle m i/|y|+Real.pi/(4*m*|y|) ≤ b+periodAngle m j/|y| := by
  have he := div_le_div_of_nonneg_right
    (periodAngle_mono hm (Nat.succ_le_of_lt hij)) hy.le
  have hs : b+periodAngle m (i+1)/|y| ≤ b+periodAngle m j/|y| := by linarith only [he]
  simpa only [period_start_succ] using hs

/-- No logarithm inside the complete half-open period is omitted by the
finite grid. This includes all cosine-zero neighborhoods. -/
theorem period_cells_cover {m : ℕ} (hm : 0 < m) {b y T : ℝ} (hy : 0 < |y|)
    (hlo : b-Real.pi/|y| < T) (hhi : T ≤ b+Real.pi/|y|) :
    ∃ i ∈ Finset.range (8*m), b+periodAngle m i/|y| < T ∧
      T ≤ b+periodAngle m i/|y|+Real.pi/(4*m*|y|) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hend : b-Real.pi/|y|+(8*m : ℕ)*(Real.pi/(4*m*|y|)) = b+Real.pi/|y| := by
    push_cast
    field_simp [ne_of_gt hmR,ne_of_gt hy]
    ring
  obtain ⟨i,hil,hih⟩ := ZetaRieszFourBoundaryCover.exists_grid_index (8*m)
    (b := Real.pi/(4*m*|y|)) hlo (by rw [hend]; exact hhi)
  refine ⟨i,Finset.mem_range.mpr i.isLt,?_,?_⟩
  · simpa only [period_start_eq_linear] using hil
  · rw [period_start_eq_linear]
    nlinarith only [hih]

/-- A central quarter of the grid has cosine at least one half. -/
theorem central_cos_lower {m i : ℕ} (hm : 0 < m) (hi : 3*m ≤ i ∧ i < 5*m) :
    (1/2 : ℝ) ≤ Real.cos (periodAngle m i) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlow : (3 : ℝ)*m ≤ i := by exact_mod_cast hi.1
  have hupp : (i : ℝ) ≤ 5*m := by exact_mod_cast hi.2.le
  have ha : |periodAngle m i| ≤ Real.pi/3 := by
    apply abs_le.mpr
    unfold periodAngle
    have hlo : (3/4 : ℝ)*Real.pi ≤ (i : ℝ)*Real.pi/(4*m) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4*m)).mpr
      nlinarith [Real.pi_pos]
    have hhi : (i : ℝ)*Real.pi/(4*m) ≤ (5/4 : ℝ)*Real.pi := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4*m)).mpr
      nlinarith [Real.pi_pos]
    constructor <;> linarith [Real.pi_pos]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (periodAngle m i))
    (show Real.pi/3 ≤ Real.pi by linarith [Real.pi_pos]) ha
  simpa only [Real.cos_pi_div_three,Real.cos_abs] using hc

/-- A deliberately coarse discrete cosine mass suffices: all other
angles remain present and are merely assigned their nonnegative credit. -/
theorem sum_positive_cos_lower {m : ℕ} (hm : 0 < m) :
    (m : ℝ) ≤ ∑ i ∈ Finset.range (8*m), max 0 (Real.cos (periodAngle m i)) := by
  have hsub : Finset.Ico (3*m) (5*m) ⊆ Finset.range (8*m) := by
    intro i hi
    simp only [Finset.mem_Ico,Finset.mem_range] at hi ⊢
    omega
  have hc : (∑ _i ∈ Finset.Ico (3*m) (5*m), (1/2 : ℝ)) = m := by
    simp only [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul]
    have he : 5*m-3*m = 2*m := by omega
    rw [he]
    push_cast
    ring
  rw [← hc]
  exact (Finset.sum_le_sum (fun i hi => (central_cos_lower hm
    (Finset.mem_Ico.mp hi)).trans (le_max_right _ _))).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => le_max_left _ _))

/-- The opposite half of the SAME full-period grid has the same positive
cosine mass. No interval is removed at a phase transition. -/
theorem sum_negative_cos_lower {m : ℕ} (hm : 0 < m) :
    (m : ℝ) ≤ ∑ i ∈ Finset.range (8*m), max 0 (-Real.cos (periodAngle m i)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hshift (i : ℕ) : Real.cos (periodAngle m (4*m+i)) =
      -Real.cos (periodAngle m i) := by
    have he : periodAngle m (4*m+i) = periodAngle m i+Real.pi := by
      unfold periodAngle
      push_cast
      field_simp [ne_of_gt hmR]
      ring
    rw [he,Real.cos_add_pi]
  have he : (∑ i ∈ Finset.range (8*m), max 0 (-Real.cos (periodAngle m i))) =
      ∑ i ∈ Finset.range (8*m), max 0 (Real.cos (periodAngle m i)) := by
    rw [show 8*m = 4*m+4*m by omega,Finset.sum_range_add,Finset.sum_range_add]
    simp_rw [hshift,neg_neg]
    exact add_comm _ _
  rw [he]
  exact sum_positive_cos_lower hm

/-- The calibrated upper constants retain a negative surplus over a
complete phase period, including every phase-uncertainty debit. -/
theorem finite_upper_phase_budget {m : ℕ} {c : ℕ → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hεu : ε ≤ 1/10000)
    (hc : (m : ℝ) ≤ ∑ i ∈ Finset.range (8*m), max 0 (c i)) :
    (∑ i ∈ Finset.range (8*m),
      ((501/500 : ℝ)*(1001/1000)*(133555/1000000)*(max 0 (c i)+ε)-
        (99/100 : ℝ)*(6823/50000)*max 0 (c i-ε))) ≤ -(m : ℝ)/2000 := by
  have hp (i : ℕ) : max 0 (c i)-ε ≤ max 0 (c i-ε) := by
    by_cases hi : 0 ≤ c i
    · rw [max_eq_right hi]
      exact le_max_right _ _
    · rw [max_eq_left (le_of_not_ge hi)]
      exact (by linarith : (0 : ℝ)-ε ≤ 0).trans (le_max_left _ _)
  have hs := Finset.sum_le_sum (s := Finset.range (8*m)) (fun i _ => hp i)
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  have heps : (m : ℝ)*ε ≤ (m : ℝ)/10000 := by
    have hn : (0 : ℝ) ≤ m := by positivity
    nlinarith
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  push_cast at hs ⊢
  have hn : (0 : ℝ) ≤ m := by positivity
  nlinarith

/-- The actual checked angular constants retain a strict finite-period
surplus after both radial factors and every phase-uncertainty debit.
This is a scalar bound to be applied to the literal disjoint ledger. -/
theorem finite_phase_budget {m : ℕ} {c : ℕ → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hεu : ε ≤ 1/10000)
    (hc : (m : ℝ) ≤ ∑ i ∈ Finset.range (8*m), max 0 (c i)) :
    (m : ℝ)/1000 ≤ ∑ i ∈ Finset.range (8*m),
      ((99/100 : ℝ)*(8529739/62500000)*max 0 (c i-ε)-
        (501/500 : ℝ)*(1001/1000)*(133421/1000000)*(max 0 (c i)+ε)) := by
  have hp (i : ℕ) : max 0 (c i)-ε ≤ max 0 (c i-ε) := by
    by_cases hi : 0 ≤ c i
    · rw [max_eq_right hi]
      exact le_max_right _ _
    · rw [max_eq_left (le_of_not_ge hi)]
      exact (by linarith : (0 : ℝ)-ε ≤ 0).trans (le_max_left _ _)
  have hs := Finset.sum_le_sum (s := Finset.range (8*m)) (fun i _ => hp i)
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  have heps : (m : ℝ)*ε ≤ (m : ℝ)/10000 := by
    have hn : (0 : ℝ) ≤ m := by positivity
    nlinarith
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  push_cast at hs ⊢
  have hn : (0 : ℝ) ≤ m := by positivity
  nlinarith

/-- The entire finite phase period has a positive quantitative surplus
for the checked first-bin constants, retaining the original two radial
envelopes and every phase uncertainty. The constant radial reference is
the proved minimum on the original core period, not a frozen saddle. -/
theorem original_finite_period_budget {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    {b y h : ℝ} (hy : 54 ≤ |y|) (hpeak : Real.cos (y*b) = -1)
    (hlo : (39/20 : ℝ)*N ≤ b-Real.pi/|y|)
    (hhi : b+Real.pi/|y| ≤ (203/100 : ℝ)*N)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hε : |y| * h ≤ 1/10000) :
    ∃ V₀ : ℝ, 0 < V₀ ∧ (m : ℝ)/1000*V₀*h ≤
      ∑ i ∈ Finset.range (8*m),
        let t := b+periodAngle m i/|y|
        (8529739/62500000 : ℝ)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*max 0 (-Real.cos (y*t)-|y| * h)*h)-
        (133421/1000000 : ℝ)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*(max 0 (-Real.cos (y*t))+|y| * h)*h) := by
  obtain ⟨V₀,hV₀,hV⟩ := ZetaRieszPhaseBudget.radial_period_comparable hN hy hlo hhi
  have hy0 : 0 < |y| := by linarith
  have hyne : y ≠ 0 := by intro he; simp only [he,abs_zero] at hy; linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let T : ℕ → ℝ := fun i => b+periodAngle m i/|y|
  let c : ℕ → ℝ := fun i => Real.cos (periodAngle m i)
  let ε := |y| * h
  have hrow (i : ℕ) (hi : i ∈ Finset.range (8*m)) :
      (((99/100 : ℝ)*(8529739/62500000)*max 0 (c i-ε)-
        (501/500 : ℝ)*(1001/1000)*(133421/1000000)*(max 0 (c i)+ε))*V₀*h) ≤
        (8529739/62500000 : ℝ)*
          ((Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*max 0 (-Real.cos (y*T i)-|y| * h)*h)-
        (133421/1000000 : ℝ)*
          ((Real.exp (-T i/2)*(T i+h)^N/N.factorial)*(max 0 (-Real.cos (y*T i))+|y| * h)*h) := by
    have hai := periodAngle_bounds hm (Finset.mem_range.mp hi).le
    have hVi := hV (periodAngle m i) hai
    have htilo : (39/20 : ℝ)*N ≤ T i := by
      have hr := div_le_div_of_nonneg_right hai.1 hy0.le
      rw [neg_div] at hr
      dsimp [T]
      linarith
    have hti : 0 < T i := by nlinarith
    have hNt : (N : ℝ) ≤ T i := by nlinarith
    have hVm : (99/100 : ℝ)*V₀ ≤ Real.exp (-(T i+h)/2)*(T i)^N/N.factorial :=
      (mul_le_mul_of_nonneg_left hVi.1 (by norm_num)).trans (lower_radial hti.le hhu)
    have hVp : Real.exp (-T i/2)*(T i+h)^N/N.factorial ≤
        (501/500 : ℝ)*(1001/1000)*V₀ := by
      have he := (upper_radial hti hNt hh.le hhu).trans
        (mul_le_mul_of_nonneg_left hVi.2 (by norm_num : (0 : ℝ) ≤ 1001/1000))
      nlinarith only [he]
    have hphase : -Real.cos (y*T i) = c i :=
      ZetaRieszPhaseBudget.phase_at_negative_peak hyne hpeak (periodAngle m i)
    rw [hphase]
    have hm' := mul_le_mul_of_nonneg_right hVm
      (show 0 ≤ (8529739/62500000 : ℝ)*max 0 (c i-ε)*h by positivity)
    have hp' := mul_le_mul_of_nonneg_right hVp
      (show 0 ≤ (133421/1000000 : ℝ)*(max 0 (c i)+ε)*h by dsimp [ε]; positivity)
    dsimp only [ε] at hm' hp' ⊢
    nlinarith only [hm',hp']
  have hsum := Finset.sum_le_sum hrow
  simp only [← Finset.sum_mul] at hsum
  have hscalar := finite_phase_budget (show 0 ≤ ε by dsimp [ε]; positivity) hε
    (sum_positive_cos_lower hm)
  have hscaled := mul_le_mul_of_nonneg_right hscalar (show 0 ≤ V₀*h by positivity)
  refine ⟨V₀,hV₀,?_⟩
  nlinarith only [hscaled,hsum]

/-- The calibrated four-prime debit is paid across the entire original
period by five-prime credit on positive phase. The radial weights are
compared on that period before summation, not at a frozen saddle. -/
theorem original_finite_upper_period_budget {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    {b y h : ℝ} (hy : 54 ≤ |y|) (hpeak : Real.cos (y*b) = -1)
    (hlo : (39/20 : ℝ)*N ≤ b-Real.pi/|y|)
    (hhi : b+Real.pi/|y| ≤ (203/100 : ℝ)*N)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hε : |y| * h ≤ 1/10000) :
    ∃ V₀ : ℝ, 0 < V₀ ∧
      (∑ i ∈ Finset.range (8*m),
        let t := b+periodAngle m i/|y|
        (133555/1000000 : ℝ)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*(max 0 (Real.cos (y*t))+|y| * h)*h)-
        (6823/50000 : ℝ)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*max 0 (Real.cos (y*t)-|y| * h)*h)) ≤
        -(m : ℝ)/2000*V₀*h := by
  obtain ⟨V₀,hV₀,hV⟩ := ZetaRieszPhaseBudget.radial_period_comparable hN hy hlo hhi
  have hy0 : 0 < |y| := by linarith
  have hyne : y ≠ 0 := by intro he; simp only [he,abs_zero] at hy; linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let T : ℕ → ℝ := fun i => b+periodAngle m i/|y|
  let c : ℕ → ℝ := fun i => -Real.cos (periodAngle m i)
  let ε := |y| * h
  have hrow (i : ℕ) (hi : i ∈ Finset.range (8*m)) :
      (133555/1000000 : ℝ)*
          ((Real.exp (-T i/2)*(T i+h)^N/N.factorial)*(max 0 (Real.cos (y*T i))+|y| * h)*h)-
        (6823/50000 : ℝ)*
          ((Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*max 0 (Real.cos (y*T i)-|y| * h)*h) ≤
      (((501/500 : ℝ)*(1001/1000)*(133555/1000000)*(max 0 (c i)+ε)-
        (99/100 : ℝ)*(6823/50000)*max 0 (c i-ε))*V₀*h) := by
    have hai := periodAngle_bounds hm (Finset.mem_range.mp hi).le
    have hVi := hV (periodAngle m i) hai
    have htilo : (39/20 : ℝ)*N ≤ T i := by
      have hr := div_le_div_of_nonneg_right hai.1 hy0.le
      rw [neg_div] at hr
      dsimp [T]
      linarith
    have hti : 0 < T i := by nlinarith
    have hNt : (N : ℝ) ≤ T i := by nlinarith
    have hVm : (99/100 : ℝ)*V₀ ≤ Real.exp (-(T i+h)/2)*(T i)^N/N.factorial :=
      (mul_le_mul_of_nonneg_left hVi.1 (by norm_num)).trans (lower_radial hti.le hhu)
    have hVp : Real.exp (-T i/2)*(T i+h)^N/N.factorial ≤
        (501/500 : ℝ)*(1001/1000)*V₀ := by
      have he := (upper_radial hti hNt hh.le hhu).trans
        (mul_le_mul_of_nonneg_left hVi.2 (by norm_num : (0 : ℝ) ≤ 1001/1000))
      nlinarith only [he]
    have hp := ZetaRieszPhaseBudget.phase_at_negative_peak hyne hpeak (periodAngle m i)
    have hphase : Real.cos (y*T i) = c i := by dsimp only [c,T]; linarith only [hp]
    rw [hphase]
    have hm' := mul_le_mul_of_nonneg_right hVm
      (show 0 ≤ (6823/50000 : ℝ)*max 0 (c i-ε)*h by positivity)
    have hp' := mul_le_mul_of_nonneg_right hVp
      (show 0 ≤ (133555/1000000 : ℝ)*(max 0 (c i)+ε)*h by dsimp [ε]; positivity)
    dsimp only [ε] at hm' hp' ⊢
    nlinarith only [hm',hp']
  have hsum := Finset.sum_le_sum hrow
  simp only [← Finset.sum_mul] at hsum
  have hscalar := finite_upper_phase_budget (show 0 ≤ ε by dsimp [ε]; positivity) hε
    (sum_negative_cos_lower hm)
  have hscaled := mul_le_mul_of_nonneg_right hscalar (show 0 ≤ V₀*h by positivity)
  refine ⟨V₀,hV₀,?_⟩
  nlinarith only [hscaled,hsum]

/-- One five-prime credit also pays the balanced-triple debit throughout every phase cell. -/
theorem finite_phase_budget_with_triples {m : ℕ} {c : ℕ → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hεu : ε ≤ 1/10000)
    (hc : (m : ℝ) ≤ ∑ i ∈ Finset.range (8*m), max 0 (c i)) :
    (m : ℝ)/2000 ≤ ∑ i ∈ Finset.range (8*m),
      ((99/100 : ℝ)*(8529739/62500000)*max 0 (c i-ε)-
        (501/500 : ℝ)*(1001/1000)*(133521/1000000)*(max 0 (c i)+ε)) := by
  have hp (i : ℕ) : max 0 (c i)-ε ≤ max 0 (c i-ε) := by
    by_cases hi : 0 ≤ c i
    · rw [max_eq_right hi]
      exact le_max_right _ _
    · rw [max_eq_left (le_of_not_ge hi)]
      exact (by linarith : (0 : ℝ)-ε ≤ 0).trans (le_max_left _ _)
  have hs := Finset.sum_le_sum (s := Finset.range (8*m)) (fun i _ => hp i)
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  have heps : (m : ℝ)*ε ≤ (m : ℝ)/10000 := by
    have hn : (0 : ℝ) ≤ m := by positivity
    nlinarith
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  push_cast at hs ⊢
  have hn : (0 : ℝ) ≤ m := by positivity
  nlinarith

/-- The calibrated upper credit pays the same triple debit, including phase boundaries. -/
theorem finite_upper_phase_budget_with_triples {m : ℕ} {c : ℕ → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hεu : ε ≤ 1/10000)
    (hc : (m : ℝ) ≤ ∑ i ∈ Finset.range (8*m), max 0 (c i)) :
    (∑ i ∈ Finset.range (8*m),
      ((501/500 : ℝ)*(1001/1000)*(133655/1000000)*(max 0 (c i)+ε)-
        (99/100 : ℝ)*(6823/50000)*max 0 (c i-ε))) ≤ -(m : ℝ)/2000 := by
  have hp (i : ℕ) : max 0 (c i)-ε ≤ max 0 (c i-ε) := by
    by_cases hi : 0 ≤ c i
    · rw [max_eq_right hi]
      exact le_max_right _ _
    · rw [max_eq_left (le_of_not_ge hi)]
      exact (by linarith : (0 : ℝ)-ε ≤ 0).trans (le_max_left _ _)
  have hs := Finset.sum_le_sum (s := Finset.range (8*m)) (fun i _ => hp i)
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  have heps : (m : ℝ)*ε ≤ (m : ℝ)/10000 := by
    have hn : (0 : ℝ) ≤ m := by positivity
    nlinarith
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  push_cast at hs ⊢
  have hn : (0 : ℝ) ≤ m := by positivity
  nlinarith

/-- Whole-period lower payment including the literal balanced-triple budget. -/
theorem original_finite_period_budget_with_triples {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    {b y h : ℝ} (hy : 54 ≤ |y|) (hpeak : Real.cos (y*b) = -1)
    (hlo : (39/20 : ℝ)*N ≤ b-Real.pi/|y|)
    (hhi : b+Real.pi/|y| ≤ (203/100 : ℝ)*N)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hε : |y| * h ≤ 1/10000) :
    ∃ V₀ : ℝ, 0 < V₀ ∧ (m : ℝ)/2000*V₀*h ≤
      ∑ i ∈ Finset.range (8*m),
        let t := b+periodAngle m i/|y|
        (8529739/62500000 : ℝ)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*max 0 (-Real.cos (y*t)-|y| * h)*h)-
        (133521/1000000 : ℝ)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*(max 0 (-Real.cos (y*t))+|y| * h)*h) := by
  obtain ⟨V₀,hV₀,hV⟩ := ZetaRieszPhaseBudget.radial_period_comparable hN hy hlo hhi
  have hy0 : 0 < |y| := by linarith
  have hyne : y ≠ 0 := by intro he; simp only [he,abs_zero] at hy; linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let T : ℕ → ℝ := fun i => b+periodAngle m i/|y|
  let c : ℕ → ℝ := fun i => Real.cos (periodAngle m i)
  let ε := |y| * h
  have hrow (i : ℕ) (hi : i ∈ Finset.range (8*m)) :
      (((99/100 : ℝ)*(8529739/62500000)*max 0 (c i-ε)-
        (501/500 : ℝ)*(1001/1000)*(133521/1000000)*(max 0 (c i)+ε))*V₀*h) ≤
        (8529739/62500000 : ℝ)*
          ((Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*max 0 (-Real.cos (y*T i)-|y| * h)*h)-
        (133521/1000000 : ℝ)*
          ((Real.exp (-T i/2)*(T i+h)^N/N.factorial)*(max 0 (-Real.cos (y*T i))+|y| * h)*h) := by
    have hai := periodAngle_bounds hm (Finset.mem_range.mp hi).le
    have hVi := hV (periodAngle m i) hai
    have htilo : (39/20 : ℝ)*N ≤ T i := by
      have hr := div_le_div_of_nonneg_right hai.1 hy0.le
      rw [neg_div] at hr
      dsimp [T]
      linarith
    have hti : 0 < T i := by nlinarith
    have hNt : (N : ℝ) ≤ T i := by nlinarith
    have hVm : (99/100 : ℝ)*V₀ ≤ Real.exp (-(T i+h)/2)*(T i)^N/N.factorial :=
      (mul_le_mul_of_nonneg_left hVi.1 (by norm_num)).trans (lower_radial hti.le hhu)
    have hVp : Real.exp (-T i/2)*(T i+h)^N/N.factorial ≤
        (501/500 : ℝ)*(1001/1000)*V₀ := by
      have he := (upper_radial hti hNt hh.le hhu).trans
        (mul_le_mul_of_nonneg_left hVi.2 (by norm_num : (0 : ℝ) ≤ 1001/1000))
      nlinarith only [he]
    have hphase : -Real.cos (y*T i) = c i :=
      ZetaRieszPhaseBudget.phase_at_negative_peak hyne hpeak (periodAngle m i)
    rw [hphase]
    have hm' := mul_le_mul_of_nonneg_right hVm
      (show 0 ≤ (8529739/62500000 : ℝ)*max 0 (c i-ε)*h by positivity)
    have hp' := mul_le_mul_of_nonneg_right hVp
      (show 0 ≤ (133521/1000000 : ℝ)*(max 0 (c i)+ε)*h by dsimp [ε]; positivity)
    dsimp only [ε] at hm' hp' ⊢
    nlinarith only [hm',hp']
  have hsum := Finset.sum_le_sum hrow
  simp only [← Finset.sum_mul] at hsum
  have hscalar := finite_phase_budget_with_triples (show 0 ≤ ε by dsimp [ε]; positivity) hε
    (sum_positive_cos_lower hm)
  have hscaled := mul_le_mul_of_nonneg_right hscalar (show 0 ≤ V₀*h by positivity)
  refine ⟨V₀,hV₀,?_⟩
  nlinarith only [hscaled,hsum]

/-- Whole-period upper payment including the literal balanced-triple budget. -/
theorem original_finite_upper_period_budget_with_triples {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    {b y h : ℝ} (hy : 54 ≤ |y|) (hpeak : Real.cos (y*b) = -1)
    (hlo : (39/20 : ℝ)*N ≤ b-Real.pi/|y|)
    (hhi : b+Real.pi/|y| ≤ (203/100 : ℝ)*N)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hε : |y| * h ≤ 1/10000) :
    ∃ V₀ : ℝ, 0 < V₀ ∧
      (∑ i ∈ Finset.range (8*m),
        let t := b+periodAngle m i/|y|
        (133655/1000000 : ℝ)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*(max 0 (Real.cos (y*t))+|y| * h)*h)-
        (6823/50000 : ℝ)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*max 0 (Real.cos (y*t)-|y| * h)*h)) ≤
        -(m : ℝ)/2000*V₀*h := by
  obtain ⟨V₀,hV₀,hV⟩ := ZetaRieszPhaseBudget.radial_period_comparable hN hy hlo hhi
  have hy0 : 0 < |y| := by linarith
  have hyne : y ≠ 0 := by intro he; simp only [he,abs_zero] at hy; linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let T : ℕ → ℝ := fun i => b+periodAngle m i/|y|
  let c : ℕ → ℝ := fun i => -Real.cos (periodAngle m i)
  let ε := |y| * h
  have hrow (i : ℕ) (hi : i ∈ Finset.range (8*m)) :
      (133655/1000000 : ℝ)*
          ((Real.exp (-T i/2)*(T i+h)^N/N.factorial)*(max 0 (Real.cos (y*T i))+|y| * h)*h)-
        (6823/50000 : ℝ)*
          ((Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*max 0 (Real.cos (y*T i)-|y| * h)*h) ≤
      (((501/500 : ℝ)*(1001/1000)*(133655/1000000)*(max 0 (c i)+ε)-
        (99/100 : ℝ)*(6823/50000)*max 0 (c i-ε))*V₀*h) := by
    have hai := periodAngle_bounds hm (Finset.mem_range.mp hi).le
    have hVi := hV (periodAngle m i) hai
    have htilo : (39/20 : ℝ)*N ≤ T i := by
      have hr := div_le_div_of_nonneg_right hai.1 hy0.le
      rw [neg_div] at hr
      dsimp [T]
      linarith
    have hti : 0 < T i := by nlinarith
    have hNt : (N : ℝ) ≤ T i := by nlinarith
    have hVm : (99/100 : ℝ)*V₀ ≤ Real.exp (-(T i+h)/2)*(T i)^N/N.factorial :=
      (mul_le_mul_of_nonneg_left hVi.1 (by norm_num)).trans (lower_radial hti.le hhu)
    have hVp : Real.exp (-T i/2)*(T i+h)^N/N.factorial ≤
        (501/500 : ℝ)*(1001/1000)*V₀ := by
      have he := (upper_radial hti hNt hh.le hhu).trans
        (mul_le_mul_of_nonneg_left hVi.2 (by norm_num : (0 : ℝ) ≤ 1001/1000))
      nlinarith only [he]
    have hp := ZetaRieszPhaseBudget.phase_at_negative_peak hyne hpeak (periodAngle m i)
    have hphase : Real.cos (y*T i) = c i := by dsimp only [c,T]; linarith only [hp]
    rw [hphase]
    have hm' := mul_le_mul_of_nonneg_right hVm
      (show 0 ≤ (6823/50000 : ℝ)*max 0 (c i-ε)*h by positivity)
    have hp' := mul_le_mul_of_nonneg_right hVp
      (show 0 ≤ (133655/1000000 : ℝ)*(max 0 (c i)+ε)*h by dsimp [ε]; positivity)
    dsimp only [ε] at hm' hp' ⊢
    nlinarith only [hm',hp']
  have hsum := Finset.sum_le_sum hrow
  simp only [← Finset.sum_mul] at hsum
  have hscalar := finite_upper_phase_budget_with_triples (show 0 ≤ ε by dsimp [ε]; positivity) hε
    (sum_negative_cos_lower hm)
  have hscaled := mul_le_mul_of_nonneg_right hscalar (show 0 ≤ V₀*h by positivity)
  refine ⟨V₀,hV₀,?_⟩
  nlinarith only [hscaled,hsum]


/-- A central-bin phase budget pays the broadened triple and four-prime
costs with the owner-enhanced five-prime credit. Constants are numerical
budgets only; the optional certificate transfer supplies their arithmetic
premises without rerunning the exhaustive covers. -/
theorem finite_central_budget {m : ℕ} {c : ℕ → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hεu : ε ≤ 1/10000)
    (hc : (m : ℝ) ≤ ∑ i ∈ Finset.range (8*m), max 0 (c i)) :
    (m : ℝ)/500 ≤ ∑ i ∈ Finset.range (8*m),
      ((99/100 : ℝ)*(1309/10000)*max 0 (c i-ε)-
        (501/500 : ℝ)*(1001/1000)*(1261/10000)*(max 0 (c i)+ε)) := by
  have hp (i : ℕ) : max 0 (c i)-ε ≤ max 0 (c i-ε) := by
    by_cases hi : 0 ≤ c i
    · rw [max_eq_right hi]
      exact le_max_right _ _
    · rw [max_eq_left (le_of_not_ge hi)]
      exact (by linarith : (0 : ℝ)-ε ≤ 0).trans (le_max_left _ _)
  have hs := Finset.sum_le_sum (s := Finset.range (8*m)) (fun i _ => hp i)
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  have heps : (m : ℝ)*ε ≤ (m : ℝ)/10000 := by
    have hn : (0 : ℝ) ≤ m := by positivity
    nlinarith
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  push_cast at hs ⊢
  have hn : (0 : ℝ) ≤ m := by positivity
  nlinarith

/-- The central upper phase budget retains every phase-boundary debit. -/
theorem finite_upper_central_budget {m : ℕ} {c : ℕ → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hεu : ε ≤ 1/10000)
    (hc : (m : ℝ) ≤ ∑ i ∈ Finset.range (8*m), max 0 (c i)) :
    (∑ i ∈ Finset.range (8*m),
      ((501/500 : ℝ)*(1001/1000)*(1261/10000)*(max 0 (c i)+ε)-
        (99/100 : ℝ)*(1309/10000)*max 0 (c i-ε))) ≤ -(m : ℝ)/500 := by
  have hp (i : ℕ) : max 0 (c i)-ε ≤ max 0 (c i-ε) := by
    by_cases hi : 0 ≤ c i
    · rw [max_eq_right hi]
      exact le_max_right _ _
    · rw [max_eq_left (le_of_not_ge hi)]
      exact (by linarith : (0 : ℝ)-ε ≤ 0).trans (le_max_left _ _)
  have hs := Finset.sum_le_sum (s := Finset.range (8*m)) (fun i _ => hp i)
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  have heps : (m : ℝ)*ε ≤ (m : ℝ)/10000 := by
    have hn : (0 : ℝ) ≤ m := by positivity
    nlinarith
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  push_cast at hs ⊢
  have hn : (0 : ℝ) ≤ m := by positivity
  nlinarith

/-- The central constants survive a full original phase period, with a 1/500 radial margin. -/
theorem original_central_period_budget_with_radial {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    {b y h : ℝ} (hy : 54 ≤ |y|) (hpeak : Real.cos (y*b) = -1)
    (hlo : (39/20 : ℝ)*N ≤ b-Real.pi/|y|)
    (hhi : b+Real.pi/|y| ≤ (203/100 : ℝ)*N)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hε : |y| * h ≤ 1/10000) :
    ∃ V₀ : ℝ, 0 < V₀ ∧
      Real.exp (-b/2)*b^N/N.factorial ≤ (501/500 : ℝ)*V₀ ∧ (m : ℝ)/500*V₀*h ≤
      ∑ i ∈ Finset.range (8*m),
        let t := b+periodAngle m i/|y|
        (1309/10000 : ℝ)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*max 0 (-Real.cos (y*t)-|y| * h)*h)-
        (1261/10000 : ℝ)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*(max 0 (-Real.cos (y*t))+|y| * h)*h) := by
  obtain ⟨V₀,hV₀,hV⟩ := ZetaRieszPhaseBudget.radial_period_comparable hN hy hlo hhi
  have hy0 : 0 < |y| := by linarith
  have hyne : y ≠ 0 := by intro he; simp only [he,abs_zero] at hy; linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let T : ℕ → ℝ := fun i => b+periodAngle m i/|y|
  let c : ℕ → ℝ := fun i => Real.cos (periodAngle m i)
  let ε := |y| * h
  have hrow (i : ℕ) (hi : i ∈ Finset.range (8*m)) :
      (((99/100 : ℝ)*(1309/10000)*max 0 (c i-ε)-
        (501/500 : ℝ)*(1001/1000)*(1261/10000)*(max 0 (c i)+ε))*V₀*h) ≤
        (1309/10000 : ℝ)*
          ((Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*max 0 (-Real.cos (y*T i)-|y| * h)*h)-
        (1261/10000 : ℝ)*
          ((Real.exp (-T i/2)*(T i+h)^N/N.factorial)*(max 0 (-Real.cos (y*T i))+|y| * h)*h) := by
    have hai := periodAngle_bounds hm (Finset.mem_range.mp hi).le
    have hVi := hV (periodAngle m i) hai
    have htilo : (39/20 : ℝ)*N ≤ T i := by
      have hr := div_le_div_of_nonneg_right hai.1 hy0.le
      rw [neg_div] at hr
      dsimp [T]
      linarith
    have hti : 0 < T i := by nlinarith
    have hNt : (N : ℝ) ≤ T i := by nlinarith
    have hVm : (99/100 : ℝ)*V₀ ≤ Real.exp (-(T i+h)/2)*(T i)^N/N.factorial :=
      (mul_le_mul_of_nonneg_left hVi.1 (by norm_num)).trans (lower_radial hti.le hhu)
    have hVp : Real.exp (-T i/2)*(T i+h)^N/N.factorial ≤
        (501/500 : ℝ)*(1001/1000)*V₀ := by
      have he := (upper_radial hti hNt hh.le hhu).trans
        (mul_le_mul_of_nonneg_left hVi.2 (by norm_num : (0 : ℝ) ≤ 1001/1000))
      nlinarith only [he]
    have hphase : -Real.cos (y*T i) = c i :=
      ZetaRieszPhaseBudget.phase_at_negative_peak hyne hpeak (periodAngle m i)
    rw [hphase]
    have hm' := mul_le_mul_of_nonneg_right hVm
      (show 0 ≤ (1309/10000 : ℝ)*max 0 (c i-ε)*h by positivity)
    have hp' := mul_le_mul_of_nonneg_right hVp
      (show 0 ≤ (1261/10000 : ℝ)*(max 0 (c i)+ε)*h by dsimp [ε]; positivity)
    dsimp only [ε] at hm' hp' ⊢
    nlinarith only [hm',hp']
  have hsum := Finset.sum_le_sum hrow
  simp only [← Finset.sum_mul] at hsum
  have hscalar := finite_central_budget (show 0 ≤ ε by dsimp [ε]; positivity) hε
    (sum_positive_cos_lower hm)
  have hscaled := mul_le_mul_of_nonneg_right hscalar (show 0 ≤ V₀*h by positivity)
  refine ⟨V₀,hV₀,?_,?_⟩
  · simpa only [zero_div,add_zero] using (hV 0 (by
      constructor <;> linarith [Real.pi_pos])).2
  · nlinarith only [hscaled,hsum]

/-- The prior period budget follows without weakening it; the strengthened
version additionally retains the scale of its radial witness. -/
theorem original_central_period_budget {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    {b y h : ℝ} (hy : 54 ≤ |y|) (hpeak : Real.cos (y*b) = -1)
    (hlo : (39/20 : ℝ)*N ≤ b-Real.pi/|y|)
    (hhi : b+Real.pi/|y| ≤ (203/100 : ℝ)*N)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hε : |y| * h ≤ 1/10000) :
    ∃ V₀ : ℝ, 0 < V₀ ∧ (m : ℝ)/500*V₀*h ≤
      ∑ i ∈ Finset.range (8*m),
        let t := b+periodAngle m i/|y|
        (1309/10000 : ℝ)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*max 0 (-Real.cos (y*t)-|y| * h)*h)-
        (1261/10000 : ℝ)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*(max 0 (-Real.cos (y*t))+|y| * h)*h) := by
  obtain ⟨V₀,hV₀,_,hpay⟩ := original_central_period_budget_with_radial hN hm hy hpeak hlo hhi hh hhu hε
  exact ⟨V₀,hV₀,hpay⟩

/-- The central upper constants survive a full original phase period with the same margin. -/
theorem original_central_upper_period_budget_with_radial {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    {b y h : ℝ} (hy : 54 ≤ |y|) (hpeak : Real.cos (y*b) = -1)
    (hlo : (39/20 : ℝ)*N ≤ b-Real.pi/|y|)
    (hhi : b+Real.pi/|y| ≤ (203/100 : ℝ)*N)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hε : |y| * h ≤ 1/10000) :
    ∃ V₀ : ℝ, 0 < V₀ ∧
      Real.exp (-b/2)*b^N/N.factorial ≤ (501/500 : ℝ)*V₀ ∧
      (∑ i ∈ Finset.range (8*m),
        let t := b+periodAngle m i/|y|
        (1261/10000 : ℝ)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*(max 0 (Real.cos (y*t))+|y| * h)*h)-
        (1309/10000 : ℝ)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*max 0 (Real.cos (y*t)-|y| * h)*h)) ≤
        -(m : ℝ)/500*V₀*h := by
  obtain ⟨V₀,hV₀,hV⟩ := ZetaRieszPhaseBudget.radial_period_comparable hN hy hlo hhi
  have hy0 : 0 < |y| := by linarith
  have hyne : y ≠ 0 := by intro he; simp only [he,abs_zero] at hy; linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let T : ℕ → ℝ := fun i => b+periodAngle m i/|y|
  let c : ℕ → ℝ := fun i => -Real.cos (periodAngle m i)
  let ε := |y| * h
  have hrow (i : ℕ) (hi : i ∈ Finset.range (8*m)) :
      (1261/10000 : ℝ)*
          ((Real.exp (-T i/2)*(T i+h)^N/N.factorial)*(max 0 (Real.cos (y*T i))+|y| * h)*h)-
        (1309/10000 : ℝ)*
          ((Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*max 0 (Real.cos (y*T i)-|y| * h)*h) ≤
      (((501/500 : ℝ)*(1001/1000)*(1261/10000)*(max 0 (c i)+ε)-
        (99/100 : ℝ)*(1309/10000)*max 0 (c i-ε))*V₀*h) := by
    have hai := periodAngle_bounds hm (Finset.mem_range.mp hi).le
    have hVi := hV (periodAngle m i) hai
    have htilo : (39/20 : ℝ)*N ≤ T i := by
      have hr := div_le_div_of_nonneg_right hai.1 hy0.le
      rw [neg_div] at hr
      dsimp [T]
      linarith
    have hti : 0 < T i := by nlinarith
    have hNt : (N : ℝ) ≤ T i := by nlinarith
    have hVm : (99/100 : ℝ)*V₀ ≤ Real.exp (-(T i+h)/2)*(T i)^N/N.factorial :=
      (mul_le_mul_of_nonneg_left hVi.1 (by norm_num)).trans (lower_radial hti.le hhu)
    have hVp : Real.exp (-T i/2)*(T i+h)^N/N.factorial ≤
        (501/500 : ℝ)*(1001/1000)*V₀ := by
      have he := (upper_radial hti hNt hh.le hhu).trans
        (mul_le_mul_of_nonneg_left hVi.2 (by norm_num : (0 : ℝ) ≤ 1001/1000))
      nlinarith only [he]
    have hp := ZetaRieszPhaseBudget.phase_at_negative_peak hyne hpeak (periodAngle m i)
    have hphase : Real.cos (y*T i) = c i := by dsimp only [c,T]; linarith only [hp]
    rw [hphase]
    have hm' := mul_le_mul_of_nonneg_right hVm
      (show 0 ≤ (1309/10000 : ℝ)*max 0 (c i-ε)*h by positivity)
    have hp' := mul_le_mul_of_nonneg_right hVp
      (show 0 ≤ (1261/10000 : ℝ)*(max 0 (c i)+ε)*h by dsimp [ε]; positivity)
    dsimp only [ε] at hm' hp' ⊢
    nlinarith only [hm',hp']
  have hsum := Finset.sum_le_sum hrow
  simp only [← Finset.sum_mul] at hsum
  have hscalar := finite_upper_central_budget (show 0 ≤ ε by dsimp [ε]; positivity) hε
    (sum_negative_cos_lower hm)
  have hscaled := mul_le_mul_of_nonneg_right hscalar (show 0 ≤ V₀*h by positivity)
  refine ⟨V₀,hV₀,?_,?_⟩
  · simpa only [zero_div,add_zero] using (hV 0 (by
      constructor <;> linarith [Real.pi_pos])).2
  · nlinarith only [hscaled,hsum]

/-- The prior period budget follows without weakening it; the strengthened
version additionally retains the scale of its radial witness. -/
theorem original_central_upper_period_budget {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    {b y h : ℝ} (hy : 54 ≤ |y|) (hpeak : Real.cos (y*b) = -1)
    (hlo : (39/20 : ℝ)*N ≤ b-Real.pi/|y|)
    (hhi : b+Real.pi/|y| ≤ (203/100 : ℝ)*N)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hε : |y| * h ≤ 1/10000) :
    ∃ V₀ : ℝ, 0 < V₀ ∧
      (∑ i ∈ Finset.range (8*m),
        let t := b+periodAngle m i/|y|
        (1261/10000 : ℝ)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*(max 0 (Real.cos (y*t))+|y| * h)*h)-
        (1309/10000 : ℝ)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*max 0 (Real.cos (y*t)-|y| * h)*h)) ≤
        -(m : ℝ)/500*V₀*h := by
  obtain ⟨V₀,hV₀,_,hpay⟩ := original_central_upper_period_budget_with_radial hN hm hy hpeak hlo hhi hh hhu hε
  exact ⟨V₀,hV₀,hpay⟩

end
end RiemannGaussian.ZetaRieszCapacityPhaseBudget
