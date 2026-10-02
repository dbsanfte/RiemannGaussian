/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointCreditFloor

/-!
# Complex divisor-log nulls in the whole signed floor

Keep every count, cutoff and both phases. The first and second divisor-log
moments vanish label by label, so COMPLEX coefficients of these nulls are
free in the exact pairing. Choose one bounded vector for the entire joined
population, after summing each complete cutoff period. This reduces the
actual one-sided cost, not merely the energy of a corrected profile.

The early cutoffs are included. No adverse imaginary null, orthogonality,
source decay or independent numerical floor is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszComplexNullFloor
open ZetaRieszCofactorPhaseEnergy ZetaRieszCutoffPeriodFloor
open ZetaRieszComplexProjection ZetaRieszJointAllocation ZetaRieszJointPrimeEnergy
open ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint ZetaRieszParityPacket

/-- Centered log and log-square profiles, with EXACT finite endpoints.
The second profile is scaled by N+1 only for coefficient conditioning. -/
def nullProfile (X N : ℕ) (L : ℝ) (quadratic : Bool) (d : ℕ) : ℝ :=
  if quadratic then
    (correctedProfile X L 1 1 d-correctedProfile X L 1 0 d)/(N+1 : ℝ)
  else correctedProfile X L 2 0 d-correctedProfile X L 1 0 d

private theorem nullProfile_end (X N : ℕ) (L : ℝ) (q : Bool) :
    nullProfile X N L q (X+1)=0 := by
  cases q <;> simp [nullProfile,correctedProfile,ZetaRieszCenteredPrimeEnergy.centeredProfile]

/-- Both nulls vanish on each original squarefree count-three label.
No phase, roughness, physical mask or allocation assumption is needed. -/
theorem nullProfile_pairing_zero {n X : ℕ} (hs : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) (hX : n ≤ X) (N : ℕ) (L : ℝ) (q : Bool) :
    (∑ d ∈ Finset.Icc 1 X,nullProfile X N L q d*
      (if d ∣ n then (μ d : ℝ) else 0))=0 := by
  cases q
  · simp only [nullProfile,Bool.false_eq_true,if_false,sub_mul,Finset.sum_sub_distrib]
    rw [corrected_prefix_eq hs hc hX,corrected_prefix_eq hs hc hX,sub_self]
  · simp only [nullProfile,if_true,div_mul_eq_mul_div,sub_mul]
    rw [← Finset.sum_div,Finset.sum_sub_distrib]
    rw [corrected_prefix_eq hs hc hX,corrected_prefix_eq hs hc hX,sub_self,zero_div]

/-- Arbitrary complex weights retain BOTH exact zero moments. In
particular, moving complex coefficients do not change the carrier. -/
theorem complex_null_zero (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (hs : ∀ n ∈ S,Squarefree n) (hc : ∀ n ∈ S,3 ≤ n.primeFactors.card)
    (hX : ∀ n ∈ S,n ≤ X) (q : Bool) :
    complexPrefix X S W (nullProfile X N L q)=0 := by
  unfold complexPrefix
  apply Finset.sum_eq_zero
  intro n hn
  rw [nullProfile_pairing_zero (hs n hn) (hc n hn) (hX n hn)]
  simp only [Complex.ofReal_zero,mul_zero]

private theorem correlation_delta_eq (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    (hend : f (X+1)=0) :
    (∑ k ∈ Finset.Icc 1 X,correlation S w k*(f k-f (k+1)))=
      ∑ n ∈ S,w n*(∑ d ∈ Finset.Icc 1 X,
        f d*(if d ∣ n then (μ d : ℝ) else 0)) := by
  symm
  simp_rw [ZetaRieszSignedCutoffEnergy.abel_profile X f _ hend,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [correlation,sharp,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem complexPrefix_re (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (f : ℕ → ℝ) :
    (complexPrefix X S W f).re=
      ∑ n ∈ S,(W n).re*(∑ d ∈ Finset.Icc 1 X,
        f d*(if d ∣ n then (μ d : ℝ) else 0)) := by
  simp only [complexPrefix,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero]

private theorem complexPrefix_im (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (f : ℕ → ℝ) :
    (complexPrefix X S W f).im=
      ∑ n ∈ S,(W n).im*(∑ d ∈ Finset.Icc 1 X,
        f d*(if d ∣ n then (μ d : ℝ) else 0)) := by
  simp only [complexPrefix,Complex.im_sum,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,zero_add]

/-- One global vector: imaginary tilt, then real/imaginary coefficients
of log and log-square. No count or period chooses its own vector. -/
def increment (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (p : Fin 5 → ℝ) (k : ℕ) : ℝ :=
  let R := correlation S (fun n => (W n).re) k
  let I := correlation S (fun n => (W n).im) k
  let f := correctedProfile X L 1 0
  (R-p 0*I)*(f k-f (k+1))+
    (p 1*R-p 2*I)*(nullProfile X N L false k-nullProfile X N L false (k+1))+
      (p 3*R-p 4*I)*(nullProfile X N L true k-nullProfile X N L true (k+1))

/-- Every early and late cutoff is retained before clipping complete
periods. Complex null coefficients carry NO coherent-moment norm price. -/
theorem sum_increment_eq (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (hs : ∀ n ∈ S,Squarefree n) (hc : ∀ n ∈ S,3 ≤ n.primeFactors.card)
    (hX : ∀ n ∈ S,n ≤ X) (p : Fin 5 → ℝ) :
    (∑ k ∈ Finset.Icc 1 X,increment X N S W L p k)=
      (complexPrefix X S W (correctedProfile X L 1 0)).re-
        p 0*(complexPrefix X S W (correctedProfile X L 1 0)).im := by
  have hend : correctedProfile X L 1 0 (X+1)=0 := by
    simp [correctedProfile,ZetaRieszCenteredPrimeEnergy.centeredProfile]
  have hr f hf : (∑ k ∈ Finset.Icc 1 X,
      correlation S (fun n => (W n).re) k*(f k-f (k+1)))=
        (complexPrefix X S W f).re :=
    (correlation_delta_eq X S (fun n => (W n).re) f hf).trans (complexPrefix_re X S W f).symm
  have hi f hf : (∑ k ∈ Finset.Icc 1 X,
      correlation S (fun n => (W n).im) k*(f k-f (k+1)))=
        (complexPrefix X S W f).im :=
    (correlation_delta_eq X S (fun n => (W n).im) f hf).trans (complexPrefix_im X S W f).symm
  have hn₁ := complex_null_zero X N S W L hs hc hX false
  have hn₂ := complex_null_zero X N S W L hs hc hX true
  simp only [increment,sub_mul,mul_assoc,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,← Finset.mul_sum]
  rw [hr _ hend,hi _ hend,hr _ (nullProfile_end X N L false),
    hi _ (nullProfile_end X N L false),hr _ (nullProfile_end X N L true),
      hi _ (nullProfile_end X N L true),hn₁,hn₂]
  simp only [Complex.zero_re,Complex.zero_im,mul_zero,sub_zero,add_zero]

/-- The ACTUAL joined one-sided price after both exact complex nulls. -/
def cost (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (p : Fin 5 → ℝ) : ℝ :=
  blockCost (Finset.Icc 1 X) g (increment X N S W L p)

/-- This is a direct signed inequality, before any source hypothesis. -/
theorem cost_floor (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (hs : ∀ n ∈ S,Squarefree n)
    (hc : ∀ n ∈ S,3 ≤ n.primeFactors.card) (hX : ∀ n ∈ S,n ≤ X)
    (p : Fin 5 → ℝ) :
    -cost X N S W L g p+p 0*(complexPrefix X S W (correctedProfile X L 1 0)).im ≤
      (complexPrefix X S W (correctedProfile X L 1 0)).re := by
  have hh := block_floor (Finset.Icc 1 X) g (increment X N S W L p)
  rw [sum_increment_eq X N S W L hs hc hX p] at hh
  change -cost X N S W L g p ≤ _ at hh
  linarith only [hh]

theorem continuous_cost (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) : Continuous (cost X N S W L g) := by
  unfold cost blockCost blockTotal increment
  fun_prop

/-- Compactness gives a single optimum over all counts/cutoffs. -/
theorem exists_best (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) :
    ∃ p ∈ Set.Icc (fun _ : Fin 5 => -|B|) (fun _ => |B|),
      ∀ q ∈ Set.Icc (fun _ : Fin 5 => -|B|) (fun _ => |B|),
        cost X N S W L g p ≤ cost X N S W L g q := by
  exact isCompact_Icc.exists_isMinOn
    ⟨fun _ => 0,by constructor <;> intro _ <;> linarith only [abs_nonneg B]⟩
    (continuous_cost X N S W L g).continuousOn

/-- One compact optimum for the entire literal population. -/
def bestParameters (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) : Fin 5 → ℝ :=
  Classical.choose (exists_best X N S W L g B)

/-- The least whole-period one-sided price, including every early cutoff. -/
def bestCost (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) : ℝ :=
  cost X N S W L g (bestParameters X N S W L g B)

theorem bestParameters_bound (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) (i : Fin 5) :
    |bestParameters X N S W L g B i| ≤ |B| := by
  have hh := (Classical.choose_spec (exists_best X N S W L g B)).1
  exact abs_le.mpr ⟨hh.1 i,hh.2 i⟩

theorem bestCost_nonneg (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) : 0 ≤ bestCost X N S W L g B := by
  unfold bestCost cost blockCost
  exact Finset.sum_nonneg (fun _ _ => le_max_right _ _)

private theorem blockCost_support (T K : Finset ℕ) (g : ℕ → ℕ) (t : ℕ → ℝ)
    (hK : K ⊆ T) (hz : ∀ k ∈ T,k ∉ K → t k=0) :
    blockCost T g t=blockCost K g t := by
  have hb b : blockTotal T g t b=blockTotal K g t b := by
    symm
    apply Finset.sum_subset
    · intro k hk
      obtain ⟨hk,he⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨hK hk,he⟩
    · intro k hk hout
      obtain ⟨hk,he⟩ := Finset.mem_filter.mp hk
      exact hz k hk (fun hin => hout (Finset.mem_filter.mpr ⟨hin,he⟩))
  unfold blockCost
  simp_rw [hb]
  symm
  apply Finset.sum_subset
  · intro b hb
    obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨k,hK hk,he⟩
  · intro b _ hout
    have he : K.filter (fun k => g k=b)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      obtain ⟨hk,hb⟩ := Finset.mem_filter.mp hk
      exact hout (Finset.mem_image.mpr ⟨k,hk,hb⟩)
    simp only [blockTotal,he,Finset.sum_empty,neg_zero,max_self]

/-- The old bounded imaginary tilt is included without changing any
cutoff group. Inactive base cutoffs contribute exactly zero. -/
def tiltParameters (v : ℝ) (i : Fin 5) : ℝ := if i=0 then v else 0

theorem cost_tilt_eq (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (v : ℝ) :
    cost X N S W L g (tiltParameters v)=
      directionalCost X S W (correctedProfile X L 1 0) g v := by
  let f := correctedProfile X L 1 0
  have hi : increment X N S W L (tiltParameters v)=
      (fun k => correlation S (tilt W v) k*(f k-f (k+1))) := by
    funext k
    simp only [increment,tiltParameters,ite_true,if_neg (by decide : (1 : Fin 5) ≠ 0),
      if_neg (by decide : (2 : Fin 5) ≠ 0),if_neg (by decide : (3 : Fin 5) ≠ 0),
        if_neg (by decide : (4 : Fin 5) ≠ 0),zero_mul,sub_zero,add_zero]
    simp only [correlation,tilt,sub_mul,mul_assoc,Finset.sum_sub_distrib,← Finset.mul_sum,f]
  rw [cost,hi]
  exact blockCost_support (Finset.Icc 1 X) (activeCutoffs X f) g _
    (Finset.filter_subset _ _) (fun k hk hout => by
      have he : f k=f (k+1) := by
        by_contra hn
        exact hout (Finset.mem_filter.mpr ⟨hk,hn⟩)
      simp only [he,sub_self,mul_zero])

/-- The enlarged signed optimization is NEVER worse than the former
best whole-period phase cost. This is a cost inequality, not an energy fit. -/
theorem bestCost_le_old (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) :
    bestCost X N S W L g B ≤
      ZetaRieszComplexProjection.bestCost X S W (correctedProfile X L 1 0) g B := by
  let v := bestTilt X S W (correctedProfile X L 1 0) g B
  have hv := abs_le.mp (bestTilt_bound X S W (correctedProfile X L 1 0) g B)
  have hp : tiltParameters v ∈ Set.Icc (fun _ : Fin 5 => -|B|) (fun _ => |B|) := by
    constructor
    · intro i
      by_cases hi : i=0
      · simpa only [tiltParameters,hi,ite_true] using hv.1
      · simp only [tiltParameters,if_neg hi]
        linarith only [abs_nonneg B]
    · intro i
      by_cases hi : i=0
      · simpa only [tiltParameters,hi,ite_true] using hv.2
      · simp only [tiltParameters,if_neg hi]
        exact abs_nonneg B
  have hh := (Classical.choose_spec (exists_best X N S W L g B)).2 (tiltParameters v) hp
  rw [cost_tilt_eq] at hh
  exact hh

/-- Null coefficients perpendicular to one common complex prefix.
The zero common moment is harmless: all four null coefficients are zero. -/
def orthogonalParameters (M : ℂ) (v a b : ℝ) : Fin 5 → ℝ :=
  ![v,a*M.im/‖M‖,a*M.re/‖M‖,b*M.im/‖M‖,b*M.re/‖M‖]

/-- Exact cross-phase cancellation replaces a coherent-moment norm
price. Every count/label is still in BOTH prefix correlations. -/
theorem increment_orthogonal_eq (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (L : ℝ) (M : ℂ) (v a b : ℝ) (k : ℕ) :
    increment X N S W L (orthogonalParameters M v a b) k=
      (correlation S (fun n => (W n).re) k-v*correlation S (fun n => (W n).im) k)*
        (correctedProfile X L 1 0 k-correctedProfile X L 1 0 (k+1))+
      (M.im*correlation S (fun n => (W n).re) k-
        M.re*correlation S (fun n => (W n).im) k)/‖M‖*
        (a*(nullProfile X N L false k-nullProfile X N L false (k+1))+
          b*(nullProfile X N L true k-nullProfile X N L true (k+1))) := by
  simp [increment,orthogonalParameters]
  ring

/-- ALL flat coherent prefix cutoffs vanish, not just a single count
or sector. This includes any common real multiple of M. -/
theorem increment_coherent_zero (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (L : ℝ) (M : ℂ) (v a b : ℝ) (k : ℕ)
    (hf : correctedProfile X L 1 0 k=correctedProfile X L 1 0 (k+1))
    (hc : M.im*correlation S (fun n => (W n).re) k=
      M.re*correlation S (fun n => (W n).im) k) :
    increment X N S W L (orthogonalParameters M v a b) k=0 := by
  rw [increment_orthogonal_eq,hf,hc]
  simp only [sub_self,mul_zero,zero_div,zero_mul,add_zero]

/-- The formerly unpaid cutoff-one common moment is now killed
EXACTLY by complex null coefficients. Its real/imaginary size is arbitrary. -/
theorem first_cutoff_zero {X : ℕ} (hX : 2 ≤ X) (N : ℕ) (S : Finset ℕ)
    (W : ℕ → ℂ) {L : ℝ} (hL : log (2 : ℕ) ≤ L) (v a b : ℝ) :
    increment X N S W L (orthogonalParameters (∑ n ∈ S,W n) v a b) 1=0 := by
  have hr : correlation S (fun n => (W n).re) 1=(∑ n ∈ S,W n).re := by
    simp [correlation,sharp,Complex.re_sum]
  have hi : correlation S (fun n => (W n).im) 1=(∑ n ∈ S,W n).im := by
    simp [correlation,sharp,Complex.im_sum]
  apply increment_coherent_zero
  · have hL1 : log (1 : ℕ) ≤ L := by
      have h2 : 0 ≤ log (2 : ℕ) := log_nonneg (by norm_num)
      simpa only [Nat.cast_one,log_one] using h2.trans hL
    exact (correctedProfile_flat (by omega : 1 ≤ X) hL1).trans
      (correctedProfile_flat hX hL).symm
  · rw [hr,hi,mul_comm]

/-- A direct whole signed floor omitting ONLY proven zero coherent
increments. This avoids the old absolute coherent-moment penalty.
All noncoherent early cutoffs remain explicitly in the price. -/
theorem orthogonal_floor (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (hs : ∀ n ∈ S,Squarefree n)
    (hc : ∀ n ∈ S,3 ≤ n.primeFactors.card) (hX : ∀ n ∈ S,n ≤ X)
    (M : ℂ) (v a b : ℝ) :
    -blockCost ((Finset.Icc 1 X).filter (fun k =>
        correctedProfile X L 1 0 k ≠ correctedProfile X L 1 0 (k+1) ∨
        M.im*correlation S (fun n => (W n).re) k ≠
          M.re*correlation S (fun n => (W n).im) k)) g
      (increment X N S W L (orthogonalParameters M v a b))+
      v*(complexPrefix X S W (correctedProfile X L 1 0)).im ≤
        (complexPrefix X S W (correctedProfile X L 1 0)).re := by
  have hf := cost_floor X N S W L g hs hc hX (orthogonalParameters M v a b)
  have he := blockCost_support (Finset.Icc 1 X)
    ((Finset.Icc 1 X).filter (fun k =>
      correctedProfile X L 1 0 k ≠ correctedProfile X L 1 0 (k+1) ∨
      M.im*correlation S (fun n => (W n).re) k ≠
        M.re*correlation S (fun n => (W n).im) k)) g
    (increment X N S W L (orthogonalParameters M v a b)) (Finset.filter_subset _ _) (by
      intro k hk hout
      have hh : ¬(correctedProfile X L 1 0 k ≠ correctedProfile X L 1 0 (k+1) ∨
        M.im*correlation S (fun n => (W n).re) k ≠
          M.re*correlation S (fun n => (W n).im) k) :=
        fun hn => hout (Finset.mem_filter.mpr ⟨hk,hn⟩)
      push Not at hh
      exact increment_coherent_zero X N S W L M v a b k hh.1 hh.2)
  rw [cost,he] at hf
  simpa only [orthogonalParameters,Matrix.cons_val_zero] using hf

/-- Only the bounded WHOLE imaginary correction remains. Null moment
coefficients, including imaginary ones, are exact and require no error. -/
theorem best_floor (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) (hs : ∀ n ∈ S,Squarefree n)
    (hc : ∀ n ∈ S,3 ≤ n.primeFactors.card) (hX : ∀ n ∈ S,n ≤ X) :
    -bestCost X N S W L g B-|B| * |(complexPrefix X S W (correctedProfile X L 1 0)).im| ≤
      (complexPrefix X S W (correctedProfile X L 1 0)).re := by
  have hf := cost_floor X N S W L g hs hc hX (bestParameters X N S W L g B)
  have hm := mul_le_mul_of_nonneg_right
    (bestParameters_bound X N S W L g B 0)
    (abs_nonneg (complexPrefix X S W (correctedProfile X L 1 0)).im)
  rw [← abs_mul] at hm
  have hl := neg_abs_le (bestParameters X N S W L g B 0*
    (complexPrefix X S W (correctedProfile X L 1 0)).im)
  change -bestCost X N S W L g B+_ ≤ _ at hf
  linarith only [hf,hm,hl]

/-- The exact cost saved by JOINED complex null profiles, beyond the
previous whole-carrier imaginary tilt. It is never spent twice. -/
def gain (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) : ℝ :=
  ZetaRieszComplexProjection.bestCost X S W (correctedProfile X L 1 0) g B-
    bestCost X N S W L g B

theorem gain_nonneg (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) : 0 ≤ gain X N S W L g B :=
  sub_nonneg.mpr (bestCost_le_old X N S W L g B)

/-- Both credits and the new cost are bounded by the SAME old price.
This COST ledger is needed before improving a paid signed-energy floor. -/
theorem bestCost_add_credits_le_original (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (L : ℝ) (g : ℕ → ℕ) (B : ℝ) :
    bestCost X N S W L g B+gain X N S W L g B+
      ZetaRieszComplexProjection.credit X S W (correctedProfile X L 1 0) g B ≤
        ZetaRieszRejoinedPhaseFloor.negativeCost X S (fun n => (W n).re)
          (correctedProfile X L 1 0) := by
  have hh := bestCost_add_credit_le_negativeCost X S W (correctedProfile X L 1 0) g B
  unfold gain
  linarith only [hh]

/-- The original literal count-cropped core and source normalization. -/
def nativeCost (u y : ℝ) (j : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  let X := max 1 (S.sup id)
  bestCost X N (S.filter Squarefree) (sourceWeight A L u y N) L (cutoffPeriod y) 4

/-- Actual signed native cost reduction, beyond the earlier phase tilt. -/
def nativeGain (u y : ℝ) (j : ℕ) : ℝ :=
  ZetaRieszComplexProjection.nativeCost u y j-nativeCost u y j

theorem nativeCost_le_old (u y : ℝ) (j : ℕ) :
    nativeCost u y j ≤ ZetaRieszComplexProjection.nativeCost u y j := by
  unfold nativeCost ZetaRieszComplexProjection.nativeCost
  exact bestCost_le_old _ _ _ _ _ _ _

theorem nativeGain_nonneg (u y : ℝ) (j : ℕ) : 0 ≤ nativeGain u y j :=
  sub_nonneg.mpr (nativeCost_le_old u y j)

/-- A stronger DIRECT floor on ORIGINAL joinedPhysical. All early/null
cutoffs and both phases are charged, and the SAME paid error is reused.
The size of this actual signed cost is not assumed or proved here. -/
theorem native_floor (u y : ℝ) (j : ℕ) :
    -nativeCost u y j-ZetaRieszComplexProjection.nativeError u y j ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
        (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  let X := max 1 (S.sup id)
  let P := (u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)
  let Q := (u : ℂ)^(N+1)*coreResponse u y N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  have hs : ∀ n ∈ S.filter Squarefree,Squarefree n := fun _ hn => (Finset.mem_filter.mp hn).2
  have hc : ∀ n ∈ S.filter Squarefree,3 ≤ n.primeFactors.card :=
    fun _ hn => core_count (Finset.mem_filter.mp hn).1
  have hX : ∀ n ∈ S.filter Squarefree,n ≤ X :=
    fun _ hn => (Finset.le_sup (f := id) (Finset.mem_filter.mp hn).1).trans (le_max_right _ _)
  have hf := best_floor X N (S.filter Squarefree) (sourceWeight A L u y N) L
    (cutoffPeriod y) 4 hs hc hX
  have he := native_prefix_eq A S L u y N (fun _ hn => core_count hn)
  dsimp only at he
  change complexPrefix X (S.filter Squarefree) (sourceWeight A L u y N)
    (correctedProfile X L 1 0)=Q at he
  rw [he] at hf
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at hf
  have hr : Q.re-P.re ≤ ‖Q-P‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (Q-P)
  have hi : |Q.im| ≤ |P.im|+‖Q-P‖ := by
    have hh := abs_sub_le Q.im P.im 0
    simp only [sub_zero] at hh
    have hd : |Q.im-P.im| ≤ ‖Q-P‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (Q-P)
    linarith only [hh,hd]
  change -nativeCost u y j-4*|Q.im| ≤ Q.re at hf
  change -nativeCost u y j-(4*|P.im|+5*‖Q-P‖) ≤ P.re
  linarith only [hf,hr,hi]

/-- All paid pair prices and BOTH actual whole-population credits enter
the SAME original carrier inequality. Neither credit has a size premise. -/
theorem eventually_joined_floor_with_credits {u y : ℝ} (hu : 0 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∀ᶠ j : ℕ in atTop,
      let N := dyadicMomentOrder j
      let A := intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
      let X := max 1 (S.sup id)
      let f := correctedProfile X L 1 0
      let w := fun n => u^(N+1)*primeWeight A L y N n 1;
      ZetaRieszComplexProjection.nativeCredit u y j+nativeGain u y j-
        sqrt (max (ZetaRieszFinitePhasePayment.remainingEnergy X N (S.filter Squarefree) w f y) 0*
          ((129/200 : ℝ)*N))-ZetaRieszJointCreditFloor.joinedError u y j ≤
            ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
  filter_upwards [tendsto_dyadicMomentOrder.eventually
    (eventually_ge_atTop (65536 : ℕ))] with j hN
  have hf := native_floor u y j
  have hc := ZetaRieszComplexProjection.nativeCost_add_credit_le_original u y j
  have hp := ZetaRieszJointCreditFloor.core_negativeCost_bound hu hU
    (by linarith only [hy,le_abs_self y] : 3 ≤ |y|) hN
    (ZetaRieszNearCriticalCountPayment.countCeiling j)
  dsimp only at hc hp ⊢
  unfold nativeGain ZetaRieszJointCreditFloor.joinedError
  linarith only [hf,hc,hp]

/-- The imaginary channel cannot erase a genuinely negative WHOLE
source, even after exact complex nulls. This is a regression safeguard. -/
theorem negative_real_le_bestCost_of_im_zero (X N : ℕ) (S : Finset ℕ)
    (W : ℕ → ℂ) (L : ℝ) (g : ℕ → ℕ) (B : ℝ)
    (hs : ∀ n ∈ S,Squarefree n) (hc : ∀ n ∈ S,3 ≤ n.primeFactors.card)
    (hX : ∀ n ∈ S,n ≤ X)
    (him : (complexPrefix X S W (correctedProfile X L 1 0)).im=0) :
    max (-(complexPrefix X S W (correctedProfile X L 1 0)).re) 0 ≤
      bestCost X N S W L g B := by
  have hf := best_floor X N S W L g B hs hc hX
  rw [him,abs_zero,mul_zero,sub_zero] at hf
  exact max_le (by linarith only [hf]) (bestCost_nonneg X N S W L g B)

/-- The cofinal numerical budget is explicit and STILL OPEN. The
stronger joined cost supplies no RH or zero-free claim by itself. -/
theorem false_of_cofinal_nativeCost (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hsimple : analyticZetaZeroMultiplicity rho=1)
    (hcost : ∃ᶠ j in atTop,nativeCost (3/2-rho.1.re) rho.1.im j ≤ 399/5000) : False := by
  apply ZetaRieszEndgameSlack.false_of_relaxed_floor rho hrho hexposed hU hsimple
    (ZetaRieszComplexProjection.nativeError (3/2-rho.1.re) rho.1.im)
    (tendsto_nativeError rho hrho hexposed hU)
  exact hcost.mono fun j hj => by
    have hf := native_floor (3/2-rho.1.re) rho.1.im j
    linarith only [hj,hf]

end RiemannGaussian.ZetaRieszComplexNullFloor
