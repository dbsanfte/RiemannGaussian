/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorSchurJetAudit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Growing projection budgets do not repair the actual Schur PSD premise

This audit counts disjoint actual semiprime rows in one native phase band.
Qualitative PNT is used ONLY to locate counterexample rows, not to pay a
signed prime sum. The full phased Mobius divisor kernel, diagonal credit,
physical cutoff, squarefreeness and exact complex constraints are retained.

The final obstruction concerns arbitrary positive unit-diagonal Schur
factors and a growing number of jet constraints. It is not a source
asymptotic, an arithmetic floor, or a zero-free theorem.
-/

namespace RiemannGaussian.ArithmeticOperatorGrowingSchurAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorMoebiusCoprimeAudit ArithmeticOperatorGcdAudit
open ArithmeticOperatorCoprimeDiagonalAudit ArithmeticOperatorSchurProjectionAudit
open ArithmeticOperatorSchurJetAudit
open scoped BigOperators Classical Topology ComplexConjugate

/-- The entire prime band has residual phase between 1/4 and 1/2. -/
def bandWidth (y : ℝ) : ℝ := Real.exp (1/(4*|y|))

/-- The literal ordinary primes in the native multiplicative phase band. -/
def phasePrimes (y : ℝ) (J : ℕ) : Finset ℕ :=
  PrimeWindow.primesInWindow (smallPhaseScale y J) (bandWidth y)

/-- A native integer cutoff containing every pair from this band. -/
def phaseCutoff (y : ℝ) (J : ℕ) : ℕ :=
  (Nat.ceil (bandWidth y*smallPhaseScale y J))^2

theorem bandWidth_gt_one {y : ℝ} (hy : y≠0) : 1<bandWidth y := by
  exact Real.one_lt_exp_iff.mpr (div_pos (by norm_num)
    (mul_pos (by norm_num) (abs_pos.mpr hy)))

theorem phaseScale_tendsto {y : ℝ} (hy : y≠0) :
    Tendsto (smallPhaseScale y) atTop atTop := by
  have ht : Tendsto (fun J : ℕ => (J : ℝ)*(2*Real.pi)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const
      (by positivity : 0<2*Real.pi)
  have ht' : Tendsto (fun J : ℕ => ((J : ℝ)*(2*Real.pi)+1/4)/|y|) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (1/4 : ℝ) ht).atTop_div_const (abs_pos.mpr hy)
  exact Real.tendsto_exp_atTop.comp ht'

theorem phase_prime_bounds {y : ℝ} (hy : y≠0) {J p : ℕ}
    (hp : p∈phasePrimes y J) :
    p.Prime ∧ smallPhaseScale y J<(p : ℝ) ∧
      (p : ℝ)≤bandWidth y*smallPhaseScale y J := by
  obtain ⟨hl,hu,hr⟩ := PrimeWindow.mem_primesInWindow_bounds
    (Real.exp_pos _).le (zero_lt_one.trans (bandWidth_gt_one hy)).le hp
  exact ⟨hr,hl,hu⟩

theorem phase_angle_bounds {y : ℝ} (hy : y≠0) {J p : ℕ}
    (hp : p∈phasePrimes y J) :
    1/4≤|y| *Real.log p-(J : ℝ)*(2*Real.pi) ∧
      |y| *Real.log p-(J : ℝ)*(2*Real.pi)≤1/2 := by
  obtain ⟨hr,hl,hu⟩ := phase_prime_bounds hy hp
  have ha := abs_pos.mpr hy
  have hlo : ((J : ℝ)*(2*Real.pi)+1/4)/|y|<Real.log p := by
    simpa [smallPhaseScale] using Real.log_lt_log (Real.exp_pos _) hl
  have hhi : Real.log p≤1/(4*|y|)+((J : ℝ)*(2*Real.pi)+1/4)/|y| := by
    have hh := Real.log_le_log (by exact_mod_cast hr.pos) hu
    dsimp [bandWidth,smallPhaseScale] at hh
    rw [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne'] at hh
    simpa only [Real.log_exp] using hh
  constructor
  · have hh := (div_lt_iff₀ ha).mp hlo
    linarith
  · have hh := mul_le_mul_of_nonneg_left hhi ha.le
    field_simp at hh
    nlinarith

/-- BOTH actual prime phases are joined before the sign is read. -/
theorem phase_pair_negative {y : ℝ} (hy : y≠0) {J p q : ℕ}
    (hp : p∈phasePrimes y J) (hq : q∈phasePrimes y J) (hpq : p≠q) :
    (augmentedKernel y (p*q) (p*q)).re≤-(1/25 : ℝ) := by
  obtain ⟨ha0,ha1⟩ := phase_angle_bounds hy hp
  obtain ⟨hb0,hb1⟩ := phase_angle_bounds hy hq
  rw [semiprime_diagonal_real (phase_prime_bounds hy hp).1
    (phase_prime_bounds hy hq).1 hpq]
  have hpa : |y| *Real.log p=
      (|y| *Real.log p-(J : ℝ)*(2*Real.pi))+(J : ℝ)*(2*Real.pi) := by ring
  have hqa : |y| *Real.log q=
      (|y| *Real.log q-(J : ℝ)*(2*Real.pi))+(J : ℝ)*(2*Real.pi) := by ring
  rw [hpa,hqa,Real.cos_add_nat_mul_two_pi,Real.cos_add_nat_mul_two_pi,
    Real.sin_add_nat_mul_two_pi,Real.sin_add_nat_mul_two_pi]
  exact small_angles_negative ha0 ha1 hb0 hb1

theorem phase_pair_mem_cutoff {y : ℝ} (hy : y≠0) {J p q : ℕ}
    (hp : p∈phasePrimes y J) (hq : q∈phasePrimes y J) :
    p*q∈Finset.Icc 1 (phaseCutoff y J) := by
  obtain ⟨hrp,_,hpu⟩ := phase_prime_bounds hy hp
  obtain ⟨hrq,_,hqu⟩ := phase_prime_bounds hy hq
  have hpU : p≤Nat.ceil (bandWidth y*smallPhaseScale y J) := by
    exact_mod_cast hpu.trans (Nat.le_ceil _)
  have hqU : q≤Nat.ceil (bandWidth y*smallPhaseScale y J) := by
    exact_mod_cast hqu.trans (Nat.le_ceil _)
  exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hrp.ne_zero hrq.ne_zero),
    by simpa [phaseCutoff,pow_two] using Nat.mul_le_mul hpU hqU⟩

/-- Every finite prime population produces half as many pairwise
coprime physical rows. No arbitrary-array or density model is used. -/
theorem negative_rows_of_prime_count {y : ℝ} (hy : y≠0) {J L H : ℕ}
    (hH : (H : ℝ)<smallPhaseScale y J) (hcard : 2*L≤(phasePrimes y J).card) :
    ∃ n : Fin L → ℕ,
      (∀ i,n i∈Finset.Icc 1 (phaseCutoff y J) ∧ H<n i ∧ 1<n i ∧
        Squarefree (n i) ∧ (augmentedKernel y (n i) (n i)).re≤-(1/25 : ℝ)) ∧
      Pairwise (fun i j => (n i).Coprime (n j)) := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin (2*L)) (β := ↥(phasePrimes y J)) (by simpa using hcard)
  let even : Fin L → Fin (2*L) := fun i => ⟨2*i,by omega⟩
  let odd : Fin L → Fin (2*L) := fun i => ⟨2*i+1,by omega⟩
  let p : Fin L → ℕ := fun i => e (even i)
  let q : Fin L → ℕ := fun i => e (odd i)
  have hpm (i : Fin L) : p i∈phasePrimes y J := (e (even i)).property
  have hqm (i : Fin L) : q i∈phasePrimes y J := (e (odd i)).property
  have hev (i : Fin L) : even i≠odd i := by
    intro hh
    have hh' := congrArg Fin.val hh
    dsimp [even,odd] at hh'
    omega
  have hneq {i j : Fin (2*L)} (hh : i≠j) : (e i : ℕ)≠(e j : ℕ) := by
    intro he
    exact hh (e.injective (Subtype.ext he))
  have hpq (i : Fin L) : p i≠q i := hneq (hev i)
  refine ⟨fun i => p i*q i,?_,?_⟩
  · intro i
    have hp := (phase_prime_bounds hy (hpm i)).1
    have hq := (phase_prime_bounds hy (hqm i)).1
    have hbig : H<p i := by
      exact_mod_cast hH.trans (phase_prime_bounds hy (hpm i)).2.1
    refine ⟨phase_pair_mem_cutoff hy (hpm i) (hqm i),
      hbig.trans_le (Nat.le_mul_of_pos_right _ hq.pos),?_,?_,
      phase_pair_negative hy (hpm i) (hqm i) (hpq i)⟩
    · exact hp.one_lt.trans_le (Nat.le_mul_of_pos_right _ hq.pos)
    · exact (Nat.squarefree_mul ((Nat.coprime_primes hp hq).mpr (hpq i))).mpr
        ⟨hp.squarefree,hq.squarefree⟩
  · intro i j hij
    have cpp (a b : Fin (2*L)) (hh : a≠b) : (e a : ℕ).Coprime (e b : ℕ) :=
      (Nat.coprime_primes (phase_prime_bounds hy (e a).property).1
        (phase_prime_bounds hy (e b).property).1).mpr (hneq hh)
    have ee : even i≠even j := by
      intro hh
      have hv := congrArg Fin.val hh
      exact hij (Fin.ext (by dsimp [even] at hv; omega))
    have oo : odd i≠odd j := by
      intro hh
      have hv := congrArg Fin.val hh
      exact hij (Fin.ext (by dsimp [odd] at hv; omega))
    have eo : even i≠odd j := by
      intro hh
      have hv := congrArg Fin.val hh
      dsimp [even,odd] at hv
      omega
    have oe : odd i≠even j := by
      intro hh
      have hv := congrArg Fin.val hh
      dsimp [even,odd] at hv
      omega
    exact ((cpp (even i) (even j) ee).mul_right (cpp (even i) (odd j) eo)).mul_left
      ((cpp (odd i) (even j) oe).mul_right (cpp (odd i) (odd j) oo))

/-- Native prime mass in this one phase band, with a fixed height-dependent
positive density. This is a qualitative PNT LOCATION theorem only. -/
theorem eventually_phase_prime_mass {y : ℝ} (hy : y≠0) :
    ∀ᶠ J in atTop,
      (bandWidth y-1)/2*smallPhaseScale y J≤
        ∑ p∈phasePrimes y J,Real.log p := by
  have ht := (PrimeWindow.theta_interval_div_tendsto
    (zero_lt_one.trans (bandWidth_gt_one hy))).comp (phaseScale_tendsto hy)
  have he := ht.eventually
    (eventually_gt_nhds (by linarith [bandWidth_gt_one hy] :
      (bandWidth y-1)/2<bandWidth y-1))
  filter_upwards [he] with J hJ
  have hh := (lt_div_iff₀ (show 0<smallPhaseScale y J from Real.exp_pos _)).mp hJ
  rw [←PrimeWindow.sum_log_primesInWindow (x := smallPhaseScale y J) (Real.exp_pos _).le
    (bandWidth_gt_one hy).le] at hh
  exact hh.le

/-- The number of actual available primes is at least their logarithmic
mass divided by the band's maximum prime logarithm. -/
theorem phase_prime_mass_le_card {y : ℝ} (hy : y≠0) (J : ℕ) :
    (∑ p∈phasePrimes y J,Real.log p)≤
      ((phasePrimes y J).card : ℝ)*Real.log (bandWidth y*smallPhaseScale y J) := by
  calc
    _ ≤ ∑ _p∈phasePrimes y J,Real.log (bandWidth y*smallPhaseScale y J) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hr,_,hu⟩ := phase_prime_bounds hy hp
      exact Real.log_le_log (by exact_mod_cast hr.pos) hu
    _ = _ := by simp

theorem phaseCutoff_tendsto {y : ℝ} (hy : y≠0) :
    Tendsto (phaseCutoff y) atTop atTop := by
  have ht : Tendsto (fun J => bandWidth y*smallPhaseScale y J) atTop atTop :=
    (phaseScale_tendsto hy).const_mul_atTop (zero_lt_one.trans (bandWidth_gt_one hy))
  exact (tendsto_pow_atTop (by decide : (2 : ℕ)≠0)).comp
    (tendsto_nat_ceil_atTop.comp ht)

/-- Physical size accounting for integer ceiling. -/
theorem cutoff_size_bound {y : ℝ} (hy : y≠0) {J : ℕ}
    (hx : 1≤smallPhaseScale y J) :
    Real.sqrt ((phaseCutoff y J : ℝ)+1)≤
      (bandWidth y+2)*smallPhaseScale y J := by
  let x := smallPhaseScale y J
  let U := Nat.ceil (bandWidth y*x)
  have hU : (U : ℝ)<bandWidth y*x+1 :=
    Nat.ceil_lt_add_one (mul_nonneg (zero_lt_one.trans (bandWidth_gt_one hy)).le
      (Real.exp_pos _).le)
  have hs : Real.sqrt ((phaseCutoff y J : ℝ)+1)≤(U : ℝ)+1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · simp only [phaseCutoff,Nat.cast_pow]
      change (U : ℝ)^2+1≤((U : ℝ)+1)^2
      nlinarith [Nat.cast_nonneg (α := ℝ) U]
  have hx' : 1≤x := hx
  calc
    _ ≤ (U : ℝ)+1 := hs
    _ ≤ bandWidth y*x+2 := by linarith
    _ ≤ (bandWidth y+2)*x := by nlinarith

theorem cutoff_log_bound {y : ℝ} (hy : y≠0) {J : ℕ}
    (hx : 1≤smallPhaseScale y J) :
    Real.log (bandWidth y*smallPhaseScale y J)≤Real.log ((phaseCutoff y J : ℝ)+1) := by
  let U := Nat.ceil (bandWidth y*smallPhaseScale y J)
  have hU : 1≤U := by
    have hge : (1 : ℝ)≤(U : ℝ) :=
      (by nlinarith [bandWidth_gt_one hy] : (1 : ℝ)≤bandWidth y*smallPhaseScale y J).trans
        (Nat.le_ceil _)
    exact_mod_cast hge
  have hUU : (U : ℝ)≤(phaseCutoff y J : ℝ)+1 := by
    have hge : (1 : ℝ)≤(U : ℝ) := by exact_mod_cast hU
    simp only [phaseCutoff,Nat.cast_pow]
    change (U : ℝ)≤(U : ℝ)^2+1
    nlinarith
  exact Real.log_le_log (mul_pos (zero_lt_one.trans (bandWidth_gt_one hy)) (Real.exp_pos _))
    ((Nat.le_ceil _).trans hUU)

/-- A growing codimension genuinely smaller than sqrt(X)/log(X) is
also smaller than the actual prime-row population along native cutoffs. -/
theorem phase_budget_tendsto {y : ℝ} (hy : y≠0) (r : ℕ → ℕ)
    (hr : Tendsto (fun X : ℕ => ((r X+1 : ℕ) : ℝ)*Real.log ((X : ℝ)+1)/
      Real.sqrt ((X : ℝ)+1)) atTop (nhds 0)) :
    Tendsto (fun J => ((r (phaseCutoff y J)+1 : ℕ) : ℝ)*
      Real.log (bandWidth y*smallPhaseScale y J)/smallPhaseScale y J) atTop (nhds 0) := by
  have ht := ((tendsto_const_nhds (x := bandWidth y+2)).mul
    (hr.comp (phaseCutoff_tendsto hy)))
  have hxb := (phaseScale_tendsto hy).eventually (eventually_ge_atTop (1 : ℝ))
  apply squeeze_zero' _ _ (by simpa using ht)
  · filter_upwards [hxb] with J hx
    have hlog : 0≤Real.log (bandWidth y*smallPhaseScale y J) := by
      apply Real.log_nonneg
      nlinarith [bandWidth_gt_one hy]
    exact div_nonneg (mul_nonneg (by positivity) hlog) (Real.exp_pos _).le
  · filter_upwards [hxb] with J hx
    have hx0 : 0<smallPhaseScale y J := Real.exp_pos _
    have hs0 : 0<Real.sqrt ((phaseCutoff y J : ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
    rw [div_le_iff₀ hx0]
    have hlogs := cutoff_log_bound hy hx
    have hsize := cutoff_size_bound hy hx
    have hnum : ((r (phaseCutoff y J)+1 : ℕ) : ℝ)*
        Real.log (bandWidth y*smallPhaseScale y J)≤
      ((r (phaseCutoff y J)+1 : ℕ) : ℝ)*Real.log ((phaseCutoff y J : ℝ)+1) :=
      mul_le_mul_of_nonneg_left hlogs (by positivity)
    have hn0 : 0≤((r (phaseCutoff y J)+1 : ℕ) : ℝ)*
        Real.log ((phaseCutoff y J : ℝ)+1) :=
      mul_nonneg (by positivity) (Real.log_nonneg (by
        have hh := Nat.cast_nonneg (α := ℝ) (phaseCutoff y J)
        linarith))
    have hh := mul_le_mul_of_nonneg_left hsize (div_nonneg hn0 hs0.le)
    have he : (((r (phaseCutoff y J)+1 : ℕ) : ℝ)*
        Real.log ((phaseCutoff y J : ℝ)+1)/Real.sqrt ((phaseCutoff y J : ℝ)+1))*
        Real.sqrt ((phaseCutoff y J : ℝ)+1)=
      ((r (phaseCutoff y J)+1 : ℕ) : ℝ)*Real.log ((phaseCutoff y J : ℝ)+1) :=
      div_mul_cancel₀ _ hs0.ne'
    rw [he] at hh
    exact hnum.trans (by convert hh using 1; push_cast; ring)

/-- The exact budget 54(r+1) supplies 27(r+1) disjoint rows. The extra
constraint is constant-density centering; r may grow with the cutoff. -/
theorem eventually_prime_count_budget {y : ℝ} (hy : y≠0) (r : ℕ → ℕ)
    (hr : Tendsto (fun X : ℕ => ((r X+1 : ℕ) : ℝ)*Real.log ((X : ℝ)+1)/
      Real.sqrt ((X : ℝ)+1)) atTop (nhds 0)) :
    ∀ᶠ J in atTop,54*(r (phaseCutoff y J)+1)≤(phasePrimes y J).card := by
  have ht := phase_budget_tendsto hy r hr
  have hsmall := ht.eventually (eventually_lt_nhds
    (by linarith [bandWidth_gt_one hy] : (0 : ℝ)<(bandWidth y-1)/108))
  filter_upwards [hsmall,eventually_phase_prime_mass hy,
    (phaseScale_tendsto hy).eventually (eventually_ge_atTop (1 : ℝ))] with J hs hm hx
  have hx0 : 0<smallPhaseScale y J := Real.exp_pos _
  have hl0 : 0<Real.log (bandWidth y*smallPhaseScale y J) := by
    apply Real.log_pos
    nlinarith [bandWidth_gt_one hy]
  have hs' := (div_lt_iff₀ hx0).mp hs
  have hm' := hm.trans (phase_prime_mass_le_card hy J)
  have hc : 54*((r (phaseCutoff y J)+1 : ℕ) : ℝ)<((phasePrimes y J).card : ℝ) := by
    by_contra hh
    have hh' := mul_le_mul_of_nonneg_right (le_of_not_gt hh) hl0.le
    nlinarith
  exact (by exact_mod_cast hc : 54*(r (phaseCutoff y J)+1)<(phasePrimes y J).card).le

/-- No finite source or whole-matrix norm is used: the exact native
quadratic already has a negative constrained vector on actual rows. -/
theorem negative_native_of_rows {y : ℝ} {X H m L : ℕ} (n : Fin L → ℕ)
    (hn : ∀ i,n i∈Finset.Icc 1 X ∧ H<n i ∧ 1<n i ∧ Squarefree (n i) ∧
      (augmentedKernel y (n i) (n i)).re≤-(1/25 : ℝ))
    (hc : Pairwise (fun i j => (n i).Coprime (n j))) (hL : 26*(m+1)<L)
    (K : ℕ → ℕ → ℂ) (hd : ∀ n∈Finset.Icc 1 X,K n n=1) (hK : PositiveSchur K)
    (profiles : Fin m → ℕ → ℂ) :
    ∃ (S : Finset ℕ) (a : ℕ → ℂ),S⊆Finset.Icc 1 X ∧
      (∀ n∈S,H<n ∧ Squarefree n) ∧ (∑ n∈S,a n)=0 ∧
      (∀ j,∑ n∈S,a n*profiles j n=0) ∧
      (∑ n∈S,∑ k∈S,a n*conj (a k)*schurEntry y K n k).re<0 := by
  have hinj : Function.Injective n := by
    intro i j he
    by_contra hij
    have hh := hc hij
    change (n i).Coprime (n j) at hh
    rw [he,Nat.coprime_self] at hh
    have hp := (hn j).2.2.1
    omega
  let b : Fin (m+1) → Fin L → ℂ :=
    fun j i => Fin.cases 1 (fun k => profiles k (n i)) j
  obtain ⟨a,ha,hneg⟩ := exists_negative_damped_constrained
    (fun i j => K (n i) (n j)) (fun i => augmentedKernel y (n i) (n i))
    (fun i => hd (n i) (hn i).1) (fun i => (hn i).2.2.2.2)
    (positiveSchur_indexed K hK n hinj) hL b
  have hzero : (∑ i,a i)=0 := by simpa [b] using ha 0
  have hprofiles (j : Fin m) : (∑ i,a i*profiles j (n i))=0 := by
    simpa [b] using ha j.succ
  have hnative : (quadratic (fun i j => schurEntry y K (n i) (n j)) a).re<0 := by
    simpa only [quadratic,schur_matrix_eq y K n hinj hc
      (fun i => hd (n i) (hn i).1),dampedMatrix] using hneg
  refine ⟨Finset.univ.image n,Function.extend n a 0,?_,?_,?_,?_,?_⟩
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact (hn i).1
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨(hn i).2.1,(hn i).2.2.2.1⟩
  · simpa only [Finset.sum_image (fun _ _ _ _ hh => hinj hh),hinj.extend_apply] using hzero
  · intro j
    simpa only [Finset.sum_image (fun _ _ _ _ hh => hinj hh),hinj.extend_apply] using hprofiles j
  · rwa [quadratic_eq_native (schurEntry y K) n hinj a] at hnative

/-- A GROWING collection of exact pole/jet profiles with
r(X)=o(sqrt(X)/log(X+1)) cannot rescue whole-space native PSD, even
after constant-density centering and any positive unit-diagonal damping. -/
theorem eventually_negative_growing_projection {y : ℝ} (hy : y≠0) (H : ℕ) (r : ℕ → ℕ)
    (hr : Tendsto (fun X : ℕ => ((r X+1 : ℕ) : ℝ)*Real.log ((X : ℝ)+1)/
      Real.sqrt ((X : ℝ)+1)) atTop (nhds 0)) :
    ∀ᶠ J in atTop,∀ K : ℕ → ℕ → ℂ,
      (∀ n∈Finset.Icc 1 (phaseCutoff y J),K n n=1) → PositiveSchur K →
      ∀ profiles : Fin (r (phaseCutoff y J)) → ℕ → ℂ,
      ∃ (S : Finset ℕ) (a : ℕ → ℂ),S⊆Finset.Icc 1 (phaseCutoff y J) ∧
        (∀ n∈S,H<n ∧ Squarefree n) ∧ (∑ n∈S,a n)=0 ∧
        (∀ j,∑ n∈S,a n*profiles j n=0) ∧
        (∑ n∈S,∑ k∈S,a n*conj (a k)*schurEntry y K n k).re<0 := by
  filter_upwards [eventually_prime_count_budget hy r hr,
    (phaseScale_tendsto hy).eventually (eventually_gt_atTop (H : ℝ))] with J hcard hH
  intro K hd hK profiles
  obtain ⟨n,hn,hc⟩ := negative_rows_of_prime_count hy hH
    (L := 27*(r (phaseCutoff y J)+1))
      (by simpa only [←mul_assoc,show 2*27=54 from rfl] using hcard)
  exact negative_native_of_rows n hn hc (by omega) K hd hK profiles

/-- This refutes eventual PSD at the ORIGINAL integer cutoff, not
merely at an auxiliary real scale. Profiles and damping may vary with X. -/
theorem not_eventually_growing_projected_psd {y : ℝ} (hy : y≠0) (H : ℕ) (r : ℕ → ℕ)
    (hr : Tendsto (fun X : ℕ => ((r X+1 : ℕ) : ℝ)*Real.log ((X : ℝ)+1)/
      Real.sqrt ((X : ℝ)+1)) atTop (nhds 0))
    (K : ℕ → ℕ → ℕ → ℂ) (profiles : (X : ℕ) → Fin (r X) → ℕ → ℂ)
    (hd : ∀ X,∀ n∈Finset.Icc 1 X,K X n n=1)
    (hK : ∀ X,PositiveSchur (K X)) :
    ¬∀ᶠ X : ℕ in atTop,∀ (S : Finset ℕ) (a : ℕ → ℂ),
      S⊆Finset.Icc 1 X → (∀ n∈S,H<n) → (∑ n∈S,a n)=0 →
      (∀ j,∑ n∈S,a n*profiles X j n=0) →
      0≤(∑ n∈S,∑ k∈S,a n*conj (a k)*schurEntry y (K X) n k).re := by
  intro hPSD
  have he := (phaseCutoff_tendsto hy).eventually hPSD
  obtain ⟨J,hJ,hbound⟩ := ((eventually_negative_growing_projection hy H r hr).and he).exists
  obtain ⟨S,a,hsub,hrows,hzero,hprofiles,hneg⟩ :=
    hJ (K (phaseCutoff y J)) (hd _) (hK _) (profiles _)
  exact not_lt_of_ge (hbound S a hsub (fun n hn => (hrows n hn).1) hzero hprofiles) hneg

/-- Every actual zero ordinate has this obstruction, with all analytic
multiplicities untouched and no exposure/rightmost hypothesis. -/
theorem not_eventually_growing_projected_psd_at_zero (rho : NontrivialZetaZero)
    (H : ℕ) (r : ℕ → ℕ)
    (hr : Tendsto (fun X : ℕ => ((r X+1 : ℕ) : ℝ)*Real.log ((X : ℝ)+1)/
      Real.sqrt ((X : ℝ)+1)) atTop (nhds 0))
    (K : ℕ → ℕ → ℕ → ℂ) (profiles : (X : ℕ) → Fin (r X) → ℕ → ℂ)
    (hd : ∀ X,∀ n∈Finset.Icc 1 X,K X n n=1)
    (hK : ∀ X,PositiveSchur (K X)) :
    ¬∀ᶠ X : ℕ in atTop,∀ (S : Finset ℕ) (a : ℕ → ℂ),
      S⊆Finset.Icc 1 X → (∀ n∈S,H<n) → (∑ n∈S,a n)=0 →
      (∀ j,∑ n∈S,a n*profiles X j n=0) →
      0≤(∑ n∈S,∑ k∈S,a n*conj (a k)*schurEntry rho.1.im (K X) n k).re :=
  not_eventually_growing_projected_psd rho.im_ne_zero_of_eta_mass H r hr K profiles hd hK

/-- Every polylogarithmic growing jet schedule satisfies the quantitative
row-budget hypothesis. This is not restricted to a fixed codimension. -/
theorem polylog_projection_budget (r : ℕ → ℕ) (d : ℕ) {C : ℝ}
    (hr : ∀ᶠ X : ℕ in atTop,((r X+1 : ℕ) : ℝ)≤C*(Real.log ((X : ℝ)+1))^d) :
    Tendsto (fun X : ℕ => ((r X+1 : ℕ) : ℝ)*Real.log ((X : ℝ)+1)/
      Real.sqrt ((X : ℝ)+1)) atTop (nhds 0) := by
  have ht : Tendsto (fun x : ℝ => (Real.log x)^(d+1)/Real.sqrt x) atTop (nhds 0) := by
    simpa only [Real.rpow_natCast,←Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop ((d+1 : ℕ) : ℝ)
        (by norm_num : (0 : ℝ)<1/2)).tendsto_div_nhds_zero
  have hx : Tendsto (fun X : ℕ => (X : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have htc := (tendsto_const_nhds (x := C)).mul (ht.comp hx)
  apply squeeze_zero' _ _ (by simpa using htc)
  · exact Eventually.of_forall (fun X => by
      apply div_nonneg
      · apply mul_nonneg (by positivity) (Real.log_nonneg _)
        have hh := Nat.cast_nonneg (α := ℝ) X
        linarith
      · positivity)
  · filter_upwards [hr] with X hX
    have hlog : 0≤Real.log ((X : ℝ)+1) := Real.log_nonneg (by
      have hh := Nat.cast_nonneg (α := ℝ) X
      linarith)
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hX hlog)
      (Real.sqrt_nonneg ((X : ℝ)+1))
    convert hh using 1; ring

theorem not_eventually_polylog_projected_psd {y : ℝ} (hy : y≠0) (H : ℕ) (r : ℕ → ℕ)
    (d : ℕ) {C : ℝ}
    (hr : ∀ᶠ X : ℕ in atTop,((r X+1 : ℕ) : ℝ)≤C*(Real.log ((X : ℝ)+1))^d)
    (K : ℕ → ℕ → ℕ → ℂ) (profiles : (X : ℕ) → Fin (r X) → ℕ → ℂ)
    (hd : ∀ X,∀ n∈Finset.Icc 1 X,K X n n=1)
    (hK : ∀ X,PositiveSchur (K X)) :
    ¬∀ᶠ X : ℕ in atTop,∀ (S : Finset ℕ) (a : ℕ → ℂ),
      S⊆Finset.Icc 1 X → (∀ n∈S,H<n) → (∑ n∈S,a n)=0 →
      (∀ j,∑ n∈S,a n*profiles X j n=0) →
      0≤(∑ n∈S,∑ k∈S,a n*conj (a k)*schurEntry y (K X) n k).re :=
  not_eventually_growing_projected_psd hy H r (polylog_projection_budget r d hr)
    K profiles hd hK

end
end RiemannGaussian.ArithmeticOperatorGrowingSchurAudit

#lint+ in RiemannGaussian.ArithmeticOperatorGrowingSchurAudit

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
  unless declarations>0 do throwError "Empty growing Schur audit."
  logInfo m!"Growing-Schur audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-growing-schur"
  IO.FS.writeFile ".lake/arithmetic-operator-growing-schur/axioms.json"
    (Json.mkObj [("scope",toJson "actual native negative semiprime row population defeats unit-diagonal Schur PSD and growing sub-sqrt/log jet projections; no signed RH estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
