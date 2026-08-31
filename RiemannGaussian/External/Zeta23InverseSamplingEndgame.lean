import RiemannGaussian.External.Zeta23InverseSamplingPacking
import RiemannGaussian.External.Zeta23Benchmark
import Zeta23.ThmD.Mult

/-!
# Literal inverse-sampling certification endgame

This file retains the checked packed simple-zero energy through the Zeta23
zero-side seam and the endpoint trace asymptotics.  Its terminal theorem is
the first unconditional project improvement of the literal simple-critical-
zero constant beyond the imported `HD(1)` benchmark.
-/

noncomputable section

open Asymptotics Complex Filter Real Topology
open scoped BigOperators

namespace RiemannGaussian
namespace Zeta23InverseSampling

open RHLinalg

/-- The multiplicity-two Zeta23 seam with the literal packed three-correlation
energy retained.  This is the exact finite-`T` inequality used by the improved
certificate; `κ` consists only of the zero padding columns. -/
theorem seamA_mult2_tripleCertificate
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T : ℝ}
    {κ β : Type*} [Fintype κ] [Fintype β] [DecidableEq β]
    (hT : 0 ≤ T) (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (hreal : Zeta23.ZeroSide.PhiHatReal T P)
    (hPois : Zeta23.ZeroSide.PoissonSq T P)
    {θ₀ : ℝ} (hTl : Zeta23.Assembly.TailInputs Z P T θ₀)
    (ha : 0 < P.a T) (hL : 0 < P.L T)
    (e : Fin 3 × β ≃ Sum
      (Zeta23.ZeroSide.blockData Z T P hconj).S₁ κ) :
    4 * rtrace (P.hat T (Z.Gz P T)) -
        frobSq (P.hat T (Z.Gz P T)) -
        2 * (Z.N T (2 * T) : ℝ) - 3 * (Zeta23.Assembly.NII Z T : ℝ) -
        θ₀ / (P.a T * P.L T) *
          (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) +
            θ₀ / (P.a T * P.L T)) +
        (∑ b, min
          (ZeroBlockData.tripleOffDiagEnergy
            ((zetaSimplePackedGram Z T P hconj e).submatrix
              (fun j : Fin 3 => (j, b))
              (fun j : Fin 3 => (j, b)))) 1) ≤
      (Z.N0s T (2 * T) : ℝ) + Fintype.card κ := by
  obtain ⟨Bc, hBc0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) =
      P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← Zeta23.Assembly.hat_add]
    congr 1
    simp [Zeta23.ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) :=
    div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := hatAz_mult2_tripleCertificate
    (Z := Z) (T := T) (P := P) hconj hreal hPois
    (by positivity) e
  have hpert := Zeta23.Assembly.ctr_sub_frobSq_perturb
    4 (by norm_num) hGAE hB₀ (htrE.trans hBle)
      (hfrE.trans (pow_le_pow_left₀ hBc0 hBle 2))
  have hs1 : (Z.s1 T : ℝ) ≤
      (Z.N0s T (2 * T) : ℝ) + (Zeta23.Assembly.NII Z T : ℝ) := by
    exact_mod_cast Zeta23.Assembly.s1_le Z hT
  have hNI : (Z.NIprime T : ℝ) =
      (Z.N T (2 * T) : ℝ) + (Zeta23.Assembly.NII Z T : ℝ) := by
    exact_mod_cast Zeta23.Assembly.NIprime_eq Z hT
  rw [hNI] at hcore
  linarith

/-! ## The four endpoint collars are negligible -/

/-- Forgetting the block-data proofs embeds a literal simple-zero column into
the underlying zero configuration. -/
def simpleZeroCarrierEmbedding
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T : ℝ}
    {hconj : Zeta23.ZeroSide.PhiHatConj T P} :
    (Zeta23.ZeroSide.blockData Z T P hconj).S₁ ↪ Z.carrier where
  toFun z := ⟨(z.1 : ℂ),
    ((Zeta23.ZeroSide.mem_ZIprime_iff (Z := Z) (T := T)).mp
      ((Zeta23.ZeroSide.mem_ZI (Z := Z) (T := T)).mp z.1.2)).1⟩
  inj' := by
    intro z z' h
    have hc : (z.1 : ℂ) = (z'.1 : ℂ) :=
      congrArg (fun x : Z.carrier => (x : ℂ)) h
    exact Subtype.ext (Subtype.ext hc)

/-- Literal simple-zero columns inherit the unconditional unit-window local
count, with weight one because their proved multiplicity is exactly one. -/
theorem simpleZeroLocalCount
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T A₀ : ℝ}
    {hconj : Zeta23.ZeroSide.PhiHatConj T P}
    (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ,
      (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    Zeta23.Tail.LocalCount
      (simpleZeroOrdinate (Z := Z) (P := P) (T := T)
        (hconj := hconj)) (fun _ => 1) A₀ := by
  let emb := simpleZeroCarrierEmbedding
    (Z := Z) (P := P) (T := T) (hconj := hconj)
  have hbase := Zeta23.Tail.LocalCount.ofWindowCount Z hA₀ hloc
  refine ⟨hA₀, ?_⟩
  intro t s hs
  have hwindow := hbase.window t (s.map emb) (by
    intro z hz
    rw [Finset.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    change t < simpleZeroOrdinate x ∧
      simpleZeroOrdinate x ≤ t + 1
    exact hs x hx)
  rw [Finset.sum_map] at hwindow
  have hmult : ∀ z :
      (Zeta23.ZeroSide.blockData Z T P hconj).S₁,
      Z.mult (emb z : ℂ) = 1 := by
    intro z
    have hz' :
        (Zeta23.ZeroSide.blockData Z T P hconj).σ z.1 = z.1 ∧
          (Zeta23.ZeroSide.blockData Z T P hconj).m z.1 = 1 := by
      simpa [Zeta23.ZeroSide.ZeroBlockData.S₁] using z.2
    have hz := hz'.2
    change Z.mult (z.1 : ℂ) = 1
    simpa [Zeta23.ZeroSide.blockData,
      Zeta23.ZeroSide.mkData] using hz
  simpa only [hmult, Nat.cast_one] using hwindow

/-- Simple columns not covered by the uniform interior sampler estimate. -/
def nonInteriorSimpleZeros
    (Z : Zeta23.ZeroConfig) (P : Zeta23.Params) (T : ℝ)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    Finset (Zeta23.ZeroSide.blockData Z T P hconj).S₁ :=
  Finset.univ \ interiorSimpleZeros Z P T hconj

/-- The part of the discarded set lying outside the original `(T,2T]`
window. -/
def outerSimpleCollar
    (Z : Zeta23.ZeroConfig) (P : Zeta23.Params) (T : ℝ)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    Finset (Zeta23.ZeroSide.blockData Z T P hconj).S₁ :=
  (nonInteriorSimpleZeros Z P T hconj).filter (fun z =>
    simpleZeroOrdinate z ≤ T ∨ 2 * T < simpleZeroOrdinate z)

/-- The discarded collar immediately to the right of `T`. -/
def lowerInnerSimpleCollar
    (Z : Zeta23.ZeroConfig) (P : Zeta23.Params) (T : ℝ)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    Finset (Zeta23.ZeroSide.blockData Z T P hconj).S₁ :=
  (nonInteriorSimpleZeros Z P T hconj).filter (fun z =>
    T < simpleZeroOrdinate z ∧
      simpleZeroOrdinate z < T + Real.sqrt T)

/-- The discarded collar immediately to the left of `2T`. -/
def upperInnerSimpleCollar
    (Z : Zeta23.ZeroConfig) (P : Zeta23.Params) (T : ℝ)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    Finset (Zeta23.ZeroSide.blockData Z T P hconj).S₁ :=
  (nonInteriorSimpleZeros Z P T hconj).filter (fun z =>
    2 * T - Real.sqrt T < simpleZeroOrdinate z ∧
      simpleZeroOrdinate z ≤ 2 * T)

/-- Every discarded literal simple-zero column lies in one of the four
`sqrt T` endpoint collars, and the proved local count gives an explicit
bound.  The three terms correspond to the outer pair, the lower inner
collar, and the upper inner collar. -/
theorem nonInteriorSimpleZeros_card_le_endpointCollars
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T A₀ : ℝ}
    {hconj : Zeta23.ZeroSide.PhiHatConj T P}
    (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ,
      (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hT : Zeta23.Tail.T₀ ≤ T) :
    ((nonInteriorSimpleZeros Z P T hconj).card : ℝ) ≤
      3 * A₀ * Real.sqrt T * Real.log (4 * T) +
      3 * A₀ * Real.sqrt (T + Real.sqrt T) *
        Real.log (4 * (T + Real.sqrt T)) +
      3 * A₀ * Real.sqrt (2 * T) * Real.log (4 * (2 * T)) := by
  classical
  let bad := nonInteriorSimpleZeros Z P T hconj
  let outer := outerSimpleCollar Z P T hconj
  let lower := lowerInnerSimpleCollar Z P T hconj
  let upper := upperInnerSimpleCollar Z P T hconj
  have hT0 : 0 ≤ T := by
    have := Zeta23.Tail.T₀_pos
    linarith
  have hLC := simpleZeroLocalCount
    (Z := Z) (P := P) (T := T) (hconj := hconj) hA₀ hloc
  have hcover : bad ⊆ outer ∪ lower ∪ upper := by
    intro z hz
    have hzBad : z ∈ nonInteriorSimpleZeros Z P T hconj := by
      simpa only [bad] using hz
    have hzNotInterior := (Finset.mem_sdiff.mp hzBad).2
    have hzNot : ¬ (T + Real.sqrt T ≤ simpleZeroOrdinate z ∧
        simpleZeroOrdinate z ≤ 2 * T - Real.sqrt T) := by
      intro hzInt
      exact hzNotInterior (mem_interiorSimpleZeros_iff.mpr hzInt)
    have hzI := (Zeta23.ZeroSide.mem_ZIprime_iff
      (Z := Z) (T := T)).mp
        ((Zeta23.ZeroSide.mem_ZI (Z := Z) (T := T)).mp z.1.2)
    have hzWindow : T - Real.sqrt T < simpleZeroOrdinate z ∧
        simpleZeroOrdinate z ≤ 2 * T + Real.sqrt T := by
      simpa only [simpleZeroOrdinate, Zeta23.D0] using hzI.2
    by_cases hlo : simpleZeroOrdinate z ≤ T
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      simp only [outer, outerSimpleCollar, Finset.mem_filter]
      exact ⟨hzBad, Or.inl hlo⟩
    · by_cases hhi : 2 * T < simpleZeroOrdinate z
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        simp only [outer, outerSimpleCollar, Finset.mem_filter]
        exact ⟨hzBad, Or.inr hhi⟩
      · have hlo' : T < simpleZeroOrdinate z := lt_of_not_ge hlo
        have hhi' : simpleZeroOrdinate z ≤ 2 * T := le_of_not_gt hhi
        by_cases hlowCollar :
            simpleZeroOrdinate z < T + Real.sqrt T
        · apply Finset.mem_union_left
          apply Finset.mem_union_right
          simp only [lower, lowerInnerSimpleCollar, Finset.mem_filter]
          exact ⟨hzBad, hlo', hlowCollar⟩
        · apply Finset.mem_union_right
          simp only [upper, upperInnerSimpleCollar, Finset.mem_filter]
          have hu : 2 * T - Real.sqrt T < simpleZeroOrdinate z := by
            by_contra hnu
            apply hzNot
            exact ⟨le_of_not_gt hlowCollar, le_of_not_gt hnu⟩
          exact ⟨hzBad, hu, hhi'⟩
  have houter : (outer.card : ℝ) ≤
      3 * A₀ * Real.sqrt T * Real.log (4 * T) := by
    have h := Zeta23.Tail.boundary_count_le hLC hT outer (by
      intro z hz
      have hz' := (Finset.mem_filter.mp (show
        z ∈ outerSimpleCollar Z P T hconj by simpa only [outer] using hz)).2
      have hzI := (Zeta23.ZeroSide.mem_ZIprime_iff
        (Z := Z) (T := T)).mp
          ((Zeta23.ZeroSide.mem_ZI (Z := Z) (T := T)).mp z.1.2)
      have hzWindow : T - Real.sqrt T < simpleZeroOrdinate z ∧
          simpleZeroOrdinate z ≤ 2 * T + Real.sqrt T := by
        simpa only [simpleZeroOrdinate, Zeta23.D0] using hzI.2
      rcases hz' with hlo | hhi
      · exact Or.inl ⟨hzWindow.1, hlo⟩
      · exact Or.inr ⟨hhi, hzWindow.2⟩)
    simpa only [Finset.sum_const_zero, Finset.sum_const,
      nsmul_eq_mul, Nat.cast_one, mul_one] using h
  have hlower : (lower.card : ℝ) ≤
      3 * A₀ * Real.sqrt (T + Real.sqrt T) *
        Real.log (4 * (T + Real.sqrt T)) := by
    have hcenter : Zeta23.Tail.T₀ ≤ T + Real.sqrt T := by
      linarith [Real.sqrt_nonneg T]
    have hsqrtMono : Real.sqrt T ≤ Real.sqrt (T + Real.sqrt T) :=
      Real.sqrt_le_sqrt (by linarith [Real.sqrt_nonneg T])
    have h := Zeta23.Tail.boundary_count_le hLC hcenter lower (by
      intro z hz
      have hz' := (Finset.mem_filter.mp (show
        z ∈ lowerInnerSimpleCollar Z P T hconj by
          simpa only [lower] using hz)).2
      apply Or.inl
      constructor
      · linarith
      · exact hz'.2.le)
    simpa only [Finset.sum_const_zero, Finset.sum_const,
      nsmul_eq_mul, Nat.cast_one, mul_one] using h
  have hupper : (upper.card : ℝ) ≤
      3 * A₀ * Real.sqrt (2 * T) * Real.log (4 * (2 * T)) := by
    have hcenter : Zeta23.Tail.T₀ ≤ 2 * T := by
      have hTlarge : 0 ≤ Zeta23.Tail.T₀ := Zeta23.Tail.T₀_pos.le
      linarith
    have hsqrtMono : Real.sqrt T ≤ Real.sqrt (2 * T) :=
      Real.sqrt_le_sqrt (by linarith)
    have h := Zeta23.Tail.boundary_count_le hLC hcenter upper (by
      intro z hz
      have hz' := (Finset.mem_filter.mp (show
        z ∈ upperInnerSimpleCollar Z P T hconj by
          simpa only [upper] using hz)).2
      apply Or.inl
      constructor
      · linarith
      · exact hz'.2)
    simpa only [Finset.sum_const_zero, Finset.sum_const,
      nsmul_eq_mul, Nat.cast_one, mul_one] using h
  have hcardNat : bad.card ≤ outer.card + lower.card + upper.card := by
    have hsub := Finset.card_le_card hcover
    have houl := Finset.card_union_le outer lower
    have houlu := Finset.card_union_le (outer ∪ lower) upper
    omega
  have hcard : (bad.card : ℝ) ≤
      (outer.card : ℝ) + lower.card + upper.card := by
    exact_mod_cast hcardNat
  dsimp only [bad] at hcard
  linarith

/-- A single classical-size bound for all four endpoint collars.  The loose
constant `42` is immaterial; the decisive fact is the `sqrt T * l T` scale. -/
theorem nonInteriorSimpleZeros_card_le_sqrt_mul_l
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T A₀ : ℝ}
    {hconj : Zeta23.ZeroSide.PhiHatConj T P}
    (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ,
      (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hT : Zeta23.Tail.T₀ ≤ T) :
    ((nonInteriorSimpleZeros Z P T hconj).card : ℝ) ≤
      42 * A₀ * Real.sqrt T * Zeta23.l T := by
  have hTpos : 0 < T := lt_of_lt_of_le Zeta23.Tail.T₀_pos hT
  have hT300 : (300 : ℝ) ≤ T := by
    simpa only [Zeta23.Tail.T₀] using hT
  have hT0 : 0 ≤ T := hTpos.le
  have hA0 : 0 ≤ A₀ := hA₀.trans' zero_le_one
  have hs0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hsSq : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT0
  have hs_le_T : Real.sqrt T ≤ T := by
    have hTone : 1 ≤ T := by
      have : (1 : ℝ) < Zeta23.Tail.T₀ := by norm_num [Zeta23.Tail.T₀]
      linarith
    nlinarith
  have hU : T + Real.sqrt T ≤ 2 * T := by linarith
  have hsU : Real.sqrt (T + Real.sqrt T) ≤ 2 * Real.sqrt T := by
    have h1 : Real.sqrt (T + Real.sqrt T) ≤ Real.sqrt (2 * T) :=
      Real.sqrt_le_sqrt hU
    have h2sq : Real.sqrt (2 * T) ^ 2 = 2 * T :=
      Real.sq_sqrt (by positivity)
    have h2nonneg := Real.sqrt_nonneg (2 * T)
    have h2 : Real.sqrt (2 * T) ≤ 2 * Real.sqrt T := by
      nlinarith
    exact h1.trans h2
  have hs2 : Real.sqrt (2 * T) ≤ 2 * Real.sqrt T := by
    have h2sq : Real.sqrt (2 * T) ^ 2 = 2 * T :=
      Real.sq_sqrt (by positivity)
    have h2nonneg := Real.sqrt_nonneg (2 * T)
    nlinarith
  have hl1 : 1 ≤ Zeta23.l T := by
    unfold Zeta23.l
    rw [Real.le_log_iff_exp_le (by positivity)]
    calc
      Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
      _ ≤ T / (2 * Real.pi) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [Real.pi_le_four]
  have hlog4 : Real.log (4 * T) ≤ 2 * Zeta23.l T :=
    Zeta23.Tail.log_four_mul_le_two_mul_l hT
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog8 : Real.log (8 * T) ≤ 3 * Zeta23.l T := by
    rw [show 8 * T = 2 * (4 * T) by ring,
      Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hlogU : Real.log (4 * (T + Real.sqrt T)) ≤
      3 * Zeta23.l T := by
    have harg : 4 * (T + Real.sqrt T) ≤ 8 * T := by nlinarith
    exact (Real.log_le_log (by positivity) harg).trans hlog8
  have hbase := nonInteriorSimpleZeros_card_le_endpointCollars
    (Z := Z) (P := P) (T := T) (hconj := hconj) hA₀ hloc hT
  have hterm1 :
      3 * A₀ * Real.sqrt T * Real.log (4 * T) ≤
        6 * A₀ * Real.sqrt T * Zeta23.l T := by
    have hcoef : 0 ≤ 3 * A₀ * Real.sqrt T := by positivity
    have hm := mul_le_mul_of_nonneg_left hlog4 hcoef
    nlinarith
  have htermU :
      3 * A₀ * Real.sqrt (T + Real.sqrt T) *
          Real.log (4 * (T + Real.sqrt T)) ≤
        18 * A₀ * Real.sqrt T * Zeta23.l T := by
    have hcoef : 0 ≤ 3 * A₀ * Real.sqrt (T + Real.sqrt T) := by
      positivity
    have hm := mul_le_mul_of_nonneg_left hlogU hcoef
    have hsMul := mul_le_mul_of_nonneg_right hsU (zero_le_one.trans hl1)
    have hsScaled := mul_le_mul_of_nonneg_left hsMul
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) hA0)
    nlinarith
  have hterm2 :
      3 * A₀ * Real.sqrt (2 * T) * Real.log (4 * (2 * T)) ≤
        18 * A₀ * Real.sqrt T * Zeta23.l T := by
    have hlog : Real.log (4 * (2 * T)) ≤ 3 * Zeta23.l T := by
      rw [show 4 * (2 * T) = 8 * T by ring]
      exact hlog8
    have hcoef : 0 ≤ 3 * A₀ * Real.sqrt (2 * T) := by positivity
    have hm := mul_le_mul_of_nonneg_left hlog hcoef
    have hsMul := mul_le_mul_of_nonneg_right hs2 (zero_le_one.trans hl1)
    have hsScaled := mul_le_mul_of_nonneg_left hsMul
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) hA0)
    nlinarith
  linarith

/-- The concrete block-data simple columns are exactly the `s₁` simple
critical zeros in the enlarged Zeta23 window. -/
lemma card_blockData_S₁_eq_s1
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T : ℝ}
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    Fintype.card (Zeta23.ZeroSide.blockData Z T P hconj).S₁ =
      Z.s1 T := by
  have hs := Zeta23.ZeroSide.s1_eq_mk Z T
    (Zeta23.ZeroSide.evalVec Z T P)
    (Zeta23.ZeroSide.evalVec_reflect hconj)
  rw [Fintype.card_coe]
  simpa [Zeta23.ZeroSide.blockData,
    Zeta23.ZeroSide.ZeroBlockData.s₁] using hs.symm

/-- Every simple critical zero in `(T,2T]` occurs among the block-data simple
columns in the enlarged window. -/
lemma N0s_le_s1
    {Z : Zeta23.ZeroConfig} {T : ℝ} :
    Z.N0s T (2 * T) ≤ Z.s1 T := by
  unfold Zeta23.ZeroConfig.N0s Zeta23.ZeroConfig.s1
    Zeta23.ZeroConfig.S1 Zeta23.ZeroConfig.ZIprime
  apply Set.ncard_le_ncard
  · rintro z ⟨⟨⟨hz, hlo, hhi⟩, hline⟩, hsimple⟩
    exact ⟨⟨⟨hz,
      (show T - Zeta23.D0 T < z.im by
        rw [Zeta23.D0]; linarith [Real.sqrt_nonneg T]),
      (show z.im ≤ 2 * T + Zeta23.D0 T by
        rw [Zeta23.D0]; linarith [Real.sqrt_nonneg T])⟩,
      hline⟩, hsimple⟩
  · apply (Z.finite_window (T - Zeta23.D0 T)
      (2 * T + Zeta23.D0 T)).subset
    intro z hz
    exact hz.1.1

/-- Exact bookkeeping connecting the literal count to the uniformly sampled
interior and the proved endpoint-collar remainder. -/
theorem N0s_le_interior_add_nonInterior
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T : ℝ}
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    Z.N0s T (2 * T) ≤
      (interiorSimpleZeros Z P T hconj).card +
        (nonInteriorSimpleZeros Z P T hconj).card := by
  classical
  let interior := interiorSimpleZeros Z P T hconj
  let bad := nonInteriorSimpleZeros Z P T hconj
  have hdisj : Disjoint interior bad := by
    simp only [interior, bad, nonInteriorSimpleZeros]
    exact Finset.disjoint_sdiff
  have hunion : interior ∪ bad = Finset.univ := by
    simp only [interior, bad, nonInteriorSimpleZeros]
    exact Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hcard : Fintype.card
      (Zeta23.ZeroSide.blockData Z T P hconj).S₁ =
        interior.card + bad.card := by
    rw [← Finset.card_univ, ← hunion, Finset.card_union_of_disjoint hdisj]
  calc
    Z.N0s T (2 * T) ≤ Z.s1 T := N0s_le_s1
    _ = Fintype.card
        (Zeta23.ZeroSide.blockData Z T P hconj).S₁ :=
      (card_blockData_S₁_eq_s1 hconj).symm
    _ = interior.card + bad.card := hcard
    _ = (interiorSimpleZeros Z P T hconj).card +
        (nonInteriorSimpleZeros Z P T hconj).card := rfl

/-! ## Finite-height elimination of the retained energy -/

/-- The central certificate algebra.  A retained-energy seam, a positive
affine triple certificate, literal triple coverage, and a linear upper bound
on the number of selected triples force an improved coefficient on the
literal simple-zero count. -/
lemma affinePacked_seam_elimination
    {A cinv N NII E R S pad q span eta bad : ℝ}
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (heta0 : 0 ≤ eta)
    (hbad0 : 0 ≤ bad)
    (hseam : (2 - cinv) * N + E - R ≤ S + pad)
    (hpack : A * q ≤ E + span + 36 * eta * q)
    (hcount : S ≤ 3 * q + 4 + bad)
    (hq : 3 * q ≤ N + NII + 2)
    (hpad : pad ≤ 2) :
    3 * (2 - cinv) * N -
        (3 * R + 3 * span + 36 * eta * (N + NII + 2) +
          10 + bad) ≤
      (3 - A) * S := by
  have hAS := mul_le_mul_of_nonneg_left hcount hA0
  have hpack3 := mul_le_mul_of_nonneg_left hpack
    (show (0 : ℝ) ≤ 3 by norm_num)
  have hqerr := mul_le_mul_of_nonneg_left hq
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 36) heta0)
  have hpad3 := mul_le_mul_of_nonneg_left hpad
    (show (0 : ℝ) ≤ 3 by norm_num)
  have hAbad := mul_le_mul_of_nonneg_right hA1 hbad0
  have hA4 := mul_le_mul_of_nonneg_right hA1
    (show (0 : ℝ) ≤ 4 by norm_num)
  nlinarith

/-- The complete finite-height certification inequality for the actual Zeta23
objects.  It constructs the consecutive packing, applies the literal Gram
certificate, carries that energy through the zero-side seam, and eliminates
it.  Every remaining term is explicit and is proved negligible below. -/
theorem endpointAffine_finite
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} (hP : P.Valid)
    (hlam : P.lam = 1) {T : ℝ}
    (hT4 : 4 ≤ T)
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (hgrid : 2 * Real.pi / P.L T ≤ Real.sqrt T / 2)
    (hconj : Zeta23.ZeroSide.PhiHatConj T (P.atD T))
    (hreal : Zeta23.ZeroSide.PhiHatReal T (P.atD T))
    (hPois : Zeta23.ZeroSide.PoissonSq T (P.atD T))
    {θ₀ : ℝ} (hTl : Zeta23.Assembly.TailInputs Z (P.atD T) T θ₀)
    {R₁ R₂ cinv : ℝ}
    (htr : |rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
        (Z.N T (2 * T) : ℝ)| ≤ R₁)
    (hfr : frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) ≤
      cinv * (Z.N T (2 * T) : ℝ) + R₂)
    {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 < B) (hA1 : A ≤ 1)
    (hcert : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      A ≤ montgomeryTaylorTripleEnergy a b + B * (a + b))
    (herr1 : endpointSamplerError P T ≤ 1) :
    3 * (2 - cinv) * (Z.N T (2 * T) : ℝ) -
        (3 * (4 * R₁ + R₂ +
            3 * (Zeta23.Assembly.NII Z T : ℝ) +
            θ₀ / ((P.atD T).a T * P.L T) *
              (4 + 2 * Real.sqrt
                (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))) +
                θ₀ / ((P.atD T).a T * P.L T))) +
          2 * B * P.L T * T +
          36 * endpointSamplerError P T *
            ((Z.N T (2 * T) : ℝ) +
              (Zeta23.Assembly.NII Z T : ℝ) + 2) +
          10 +
          ((nonInteriorSimpleZeros Z (P.atD T) T hconj).card : ℝ)) ≤
      (3 - A) * (Z.N0s T (2 * T) : ℝ) := by
  classical
  have hT0 : 0 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have ha : 0 < (P.atD T).a T := by
    linarith [(Zeta23.ThmD.aD_range_of hP h8 h4pi).1]
  have heta0 : 0 ≤ endpointSamplerError P T :=
    endpointSamplerError_nonneg hP h8 h4pi hTpos
  let α := (Zeta23.ZeroSide.blockData Z T (P.atD T) hconj).S₁
  let Q : ℕ := (Fintype.card α + 2) / 3
  let pad : ℕ := 3 * Q - Fintype.card α
  obtain ⟨q, e, hqQ, hcard, hpad, henergy⟩ :=
    exists_literalPackedEnergy_affine_lower
      hP hlam hT4 h8 h4pi hgrid hconj hB0 hA1 hcert herr1
  have hqQLocal : q ≤ Q := by
    simpa only [Q, α] using hqQ
  have hpadLocal : pad ≤ 2 := by
    simpa only [pad, Q, α] using hpad
  let E : ℝ := ∑ b : Fin Q, min
    (ZeroBlockData.tripleOffDiagEnergy
      ((zetaSimplePackedGram Z T (P.atD T) hconj e).submatrix
        (fun j : Fin 3 => (j, b))
        (fun j : Fin 3 => (j, b)))) 1
  let tailLoss : ℝ :=
    θ₀ / ((P.atD T).a T * P.L T) *
      (4 + 2 * Real.sqrt
        (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))) +
        θ₀ / ((P.atD T).a T * P.L T))
  let R : ℝ := 4 * R₁ + R₂ +
    3 * (Zeta23.Assembly.NII Z T : ℝ) + tailLoss
  let span : ℝ := (2 * B * P.L T * T) / 3
  let bad : ℝ :=
    ((nonInteriorSimpleZeros Z (P.atD T) T hconj).card : ℝ)
  have hseamRaw := seamA_mult2_tripleCertificate
    (Z := Z) (P := P.atD T) hT0 hconj hreal hPois hTl ha hL e
  simp only [Zeta23.Params.atD_L, Fintype.card_fin] at hseamRaw
  have hseam :
      (2 - cinv) * (Z.N T (2 * T) : ℝ) + E - R ≤
        (Z.N0s T (2 * T) : ℝ) + (pad : ℝ) := by
    have htrlo : (Z.N T (2 * T) : ℝ) - R₁ ≤
        rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) := by
      linarith [(abs_le.mp htr).1]
    dsimp only [E, R, tailLoss, pad, Q, α] at hseamRaw ⊢
    linarith [hfr]
  have hpack : A * (q : ℝ) ≤
      E + span + 36 * endpointSamplerError P T * (q : ℝ) := by
    simpa only [E, span, Q, α] using henergy
  have hcountNat : Z.N0s T (2 * T) ≤
      3 * q + 4 + (nonInteriorSimpleZeros Z (P.atD T) T hconj).card := by
    have hwhole := N0s_le_interior_add_nonInterior
      (Z := Z) (P := P.atD T) hconj
    omega
  have hcount : (Z.N0s T (2 * T) : ℝ) ≤
      3 * (q : ℝ) + 4 + bad := by
    dsimp only [bad]
    exact_mod_cast hcountNat
  have hqNat : 3 * q ≤ Z.N T (2 * T) +
      Zeta23.Assembly.NII Z T + 2 := by
    have hα : Fintype.card α = Z.s1 T := by
      dsimp only [α]
      exact card_blockData_S₁_eq_s1 hconj
    have hs1 := Zeta23.Assembly.s1_le Z hT0
    have hSN : Z.N0s T (2 * T) ≤ Z.N T (2 * T) :=
      (Z.trivial_chain T (2 * T)).1.trans
        ((Z.trivial_chain T (2 * T)).2.1.trans
          (Z.trivial_chain T (2 * T)).2.2.1)
    have hαQ : Fintype.card α ≤ 3 * Q := by
      dsimp only [Q]
      exact card_le_three_mul_ceilThird _
    have hQpad : 3 * Q = Fintype.card α + pad := by
      dsimp only [pad]
      omega
    omega
  have hq : 3 * (q : ℝ) ≤
      (Z.N T (2 * T) : ℝ) +
        (Zeta23.Assembly.NII Z T : ℝ) + 2 := by
    exact_mod_cast hqNat
  have hpadR : (pad : ℝ) ≤ 2 := by exact_mod_cast hpadLocal
  have hbad0 : 0 ≤ bad := by
    dsimp only [bad]
    positivity
  have hfinal := affinePacked_seam_elimination
    hA0 hA1 heta0 hbad0 hseam hpack hcount hq hpadR
  dsimp only [R, span, tailLoss, bad] at hfinal ⊢
  convert hfinal using 1
  all_goals ring

/-! ## Endpoint asymptotics -/

/-- At `λ = 1`, the sampling span `L(T)T` differs from the Riemann--von
Mangoldt main scale `2π N(T,2T)` by `o(N)`. -/
lemma endpoint_L_mul_T_sub_two_pi_N_isLittleO
    (Z : Zeta23.ZeroConfig) (hRvM : Zeta23.RiemannVonMangoldt Z)
    (P : Zeta23.Params) (hlam : P.lam = 1) :
    (fun T : ℝ => P.L T * T -
      2 * Real.pi * (Z.N T (2 * T) : ℝ)) =o[atTop]
        (fun T => (Z.N T (2 * T) : ℝ)) := by
  let N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ)
  let rvmErr : ℝ → ℝ := fun T =>
    N T - T / (2 * Real.pi) * Zeta23.ell1 T
  obtain ⟨C, T₀, hmain⟩ := hRvM.main
  have hErrO : rvmErr =O[atTop] Real.log := by
    refine IsBigO.of_bound |C| ?_
    filter_upwards [eventually_ge_atTop T₀,
      Zeta23.Assembly.eventually_log_nonneg] with T hT hlog
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog]
    have h := hmain T hT
    dsimp only [rvmErr, N]
    calc
      |(Z.N T (2 * T) : ℝ) -
          T / (2 * Real.pi) * Zeta23.ell1 T| ≤
          C * Real.log T := h
      _ ≤ |C| * Real.log T :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hlog
  have hErrO_N : rvmErr =o[atTop] N :=
    hErrO.trans_isLittleO
      (Zeta23.Assembly.isLittleO_N_of_isLittleO_Tl Z hRvM
        Zeta23.Assembly.isLittleO_log_Tl)
  have hT_Tl : (fun T : ℝ => T) =o[atTop]
      (fun T => T * Zeta23.l T) := by
    refine (isLittleO_iff).2 fun c hc => ?_
    filter_upwards [Zeta23.Assembly.tendsto_l_atTop.eventually_ge_atTop c⁻¹,
      eventually_gt_atTop (0 : ℝ)] with T hl hT
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hT,
      abs_of_pos (mul_pos hT (lt_of_lt_of_le (inv_pos.mpr hc) hl))]
    have hone : 1 ≤ c * Zeta23.l T := by
      have hm := mul_le_mul_of_nonneg_left hl hc.le
      rwa [mul_inv_cancel₀ hc.ne'] at hm
    nlinarith
  have hT_N : (fun T : ℝ => T) =o[atTop] N :=
    Zeta23.Assembly.isLittleO_N_of_isLittleO_Tl Z hRvM hT_Tl
  have hdecomp : (fun T : ℝ => P.L T * T -
        2 * Real.pi * N T) =
      (fun T => (-2 * Real.pi) * rvmErr T - Zeta23.Assembly.c₀ * T) := by
    funext T
    dsimp only [rvmErr, N]
    rw [Zeta23.Params.L, hlam, one_mul, Zeta23.Assembly.ell1_eq]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hdecomp]
  exact (hErrO_N.const_mul_left (-2 * Real.pi)).sub
    (hT_N.const_mul_left Zeta23.Assembly.c₀)

/-- The literal simple-zero columns sacrificed at the finite sampler
endpoints form an `o(N)` family. -/
lemma nonInteriorSimpleZeros_isLittleO_N
    (Z : Zeta23.ZeroConfig) (hRvM : Zeta23.RiemannVonMangoldt Z)
    (P : Zeta23.Params)
    (hconj : ∀ T : ℝ, Zeta23.ZeroSide.PhiHatConj T (P.atD T)) :
    (fun T : ℝ =>
      ((nonInteriorSimpleZeros Z (P.atD T) T (hconj T)).card : ℝ))
      =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := hRvM.local_count
  have hO : (fun T : ℝ =>
      ((nonInteriorSimpleZeros Z (P.atD T) T (hconj T)).card : ℝ))
      =O[atTop] (fun T => Real.sqrt T * Zeta23.l T) := by
    refine IsBigO.of_bound (42 * A₀) ?_
    filter_upwards [eventually_ge_atTop Zeta23.Tail.T₀,
      Zeta23.Assembly.eventually_l_pos] with T hT hl
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg T) hl.le)]
    have h := nonInteriorSimpleZeros_card_le_sqrt_mul_l
      (Z := Z) (P := P.atD T) (hconj := hconj T) hA₀ hloc hT
    simpa only [mul_assoc] using h
  exact hO.trans_isLittleO
    (Zeta23.Assembly.isLittleO_N_of_isLittleO_Tl Z hRvM
      Zeta23.Assembly.isLittleO_sqrt_mul_l_Tl)

lemma constant_isLittleO_of_tendsto_atTop
    {N : ℝ → ℝ} (hN : Tendsto N atTop atTop) (k : ℝ) :
    (fun _ : ℝ => k) =o[atTop] N := by
  have h := (isLittleO_const_id_atTop k).comp_tendsto hN
  change (fun _ : ℝ => k) =o[atTop] N at h
  exact h

lemma abs_sub_mul_isLittleO
    {f N : ℝ → ℝ} {a : ℝ}
    (hf : Tendsto f atTop (nhds a)) :
    (fun T => |f T - a| * N T) =o[atTop] N := by
  apply Zeta23.Assembly.isLittleO_of_tendsto_zero_mul
  have hsub : Tendsto (fun T => f T - a) atTop (nhds 0) := by
    simpa only [sub_self] using hf.sub_const a
  simpa only [abs_zero] using hsub.abs

lemma const_mul_abs_sub_mul_isLittleO
    {f N : ℝ → ℝ} {a k : ℝ}
    (hf : Tendsto f atTop (nhds a)) :
    (fun T => k * |f T - a| * N T) =o[atTop] N := by
  have h := abs_sub_mul_isLittleO (N := N) hf
  simpa only [mul_assoc] using h.const_mul_left k

lemma const_mul_abs_isLittleO
    {f N : ℝ → ℝ} {k : ℝ} (h : f =o[atTop] N) :
    (fun T => k * |f T|) =o[atTop] N := by
  have hn := h.norm_left
  have ha : (fun T => |f T|) =o[atTop] N := by
    simpa only [Real.norm_eq_abs] using hn
  exact ha.const_mul_left k

lemma endpoint_span_abs_isLittleO
    (Z : Zeta23.ZeroConfig) (hRvM : Zeta23.RiemannVonMangoldt Z)
    (P : Zeta23.Params) (hlam : P.lam = 1) (k : ℝ) :
    (fun T => k * |P.L T * T -
      2 * Real.pi * (Z.N T (2 * T) : ℝ)|) =o[atTop]
        (fun T => (Z.N T (2 * T) : ℝ)) :=
  const_mul_abs_isLittleO
    (endpoint_L_mul_T_sub_two_pi_N_isLittleO Z hRvM P hlam)

set_option maxHeartbeats 800000 in
/-- Endpoint Zeta23 with a literal affine triple certificate.  Unlike the
baseline theorem, this retains and spends the finite simple-zero Gram energy.
The resulting unconditional constant is the displayed quotient. -/
theorem thmD_endpoint_affine_abstract
    (Z : Zeta23.ZeroConfig) (H : Zeta23.PaperInputs Z)
    (P : Zeta23.Params) (hP : P.Valid) (hlam : P.lam = 1)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : Zeta23.ThmD.TracesBoundsD P aT bT JT trG trG2
      (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => Zeta23.ThmD.cRatio
      (P.lam1 T) (aT T) (bT T) (JT T)) atTop (nhds c))
    (haRange : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (θ₀ : ℝ → ℝ)
    (hTail : ∀ᶠ T in atTop,
      Zeta23.Assembly.TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop,
      θ₀ T ≤ C * Zeta23.l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop,
      (Zeta23.Assembly.NII Z T : ℝ) ≤
        C * Real.sqrt T * Zeta23.l T)
    (hGzGp : ∀ᶠ T in atTop,
      Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = trG T ∧
      (P.atD T).trGtildeSq T = trG2 T ∧
      (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (nhds 0))
    {A B : ℝ} (hA0 : 0 < A) (hB0 : 0 < B) (hA1 : A ≤ 1)
    (hcert : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      A ≤ montgomeryTaylorTripleEnergy a b + B * (a + b)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((3 * (2 - c⁻¹) - 4 * Real.pi * B) / (3 - A) - ε) *
          (Z.N T (2 * T) : ℝ) ≤
        Z.N0s T (2 * T) := by
  have hlam0 : 0 < P.lam := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hP.lam_le_one
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  let hconjD : ∀ T : ℝ,
      Zeta23.ZeroSide.PhiHatConj T (P.atD T) := fun T =>
    Zeta23.ZeroSide.phiHatConj
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ := fun T =>
    (Zeta23.ThmD.cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹
      with hcinv
  set R₁ : ℝ → ℝ := fun T =>
    C₁ * Real.sqrt (P.X T) / aT T with hR₁
  set R₂ : ℝ → ℝ := fun T =>
    C₂ * P.calE T * (cinv T * N T) with hR₂
  set Bt : ℝ → ℝ := fun T =>
    θ₀ T / (aT T * P.L T) with hBt
  set eta : ℝ → ℝ := endpointSamplerError P with heta
  set bad : ℝ → ℝ := fun T =>
    ((nonInteriorSimpleZeros Z (P.atD T) T (hconjD T)).card : ℝ)
      with hbad
  set baseR : ℝ → ℝ := fun T =>
    4 * R₁ T + R₂ T + 3 * (Zeta23.Assembly.NII Z T : ℝ) +
      Bt T * (4 + 2 * Real.sqrt (cinv T * N T + R₂ T) + Bt T)
      with hbaseR
  set Cnum : ℝ := 3 * (2 - c⁻¹) - 4 * Real.pi * B with hCnum
  set err : ℝ → ℝ := fun T =>
    3 * baseR T +
      36 * eta T * (N T + (Zeta23.Assembly.NII Z T : ℝ) + 2) +
      10 + bad T +
      3 * |cinv T - c⁻¹| * N T +
      2 * B * |P.L T * T - 2 * Real.pi * N T| with herr
  have hLtop := Zeta23.ThmD.tendsto_L hP
  have hcinvTo : Tendsto cinv atTop (nhds c⁻¹) := hc.inv₀ hc0.ne'
  have h4pi : ∀ᶠ T in atTop, 4 * Real.pi * P.w ≤ P.L T :=
    hLtop.eventually_ge_atTop (4 * Real.pi * P.w)
  have hgrid : ∀ᶠ T in atTop,
      2 * Real.pi / P.L T ≤ Real.sqrt T / 2 := by
    filter_upwards [h4pi, eventually_ge_atTop (1 : ℝ)] with T hL hT
    have hLpos : 0 < P.L T := by
      nlinarith [hP.one_le_w, Real.pi_pos]
    have hs : 1 ≤ Real.sqrt T := Real.one_le_sqrt.mpr hT
    rw [div_le_iff₀ hLpos]
    have hhalf : (1 / 2 : ℝ) ≤ Real.sqrt T / 2 := by linarith
    have hw0 : 0 ≤ 4 * Real.pi * P.w :=
      mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
        (zero_le_one.trans hP.one_le_w)
    have hs0 : 0 ≤ Real.sqrt T / 2 := by positivity
    have hm := mul_le_mul hhalf hL hw0 hs0
    have hbase : 2 * Real.pi ≤ (1 / 2 : ℝ) *
        (4 * Real.pi * P.w) := by
      have hw := mul_le_mul_of_nonneg_left hP.one_le_w
        (show 0 ≤ 2 * Real.pi by positivity)
      nlinarith
    exact hbase.trans hm
  have hetaTo : Tendsto eta atTop (nhds 0) := by
    simpa only [eta] using tendsto_endpointSamplerError_zero hP
  have heta1 : ∀ᶠ T in atTop, eta T ≤ 1 :=
    hetaTo.eventually (eventually_le_nhds (by norm_num))
  have hmain : ∀ᶠ T in atTop,
      Cnum * N T - err T ≤ (3 - A) * (Z.N0s T (2 * T) : ℝ) := by
    filter_upwards [hTail, hGzGp, hId, haRange,
      eventually_ge_atTop T₁, eventually_ge_atTop T₂,
      eventually_ge_atTop Zeta23.Tail.T₀, eventually_ge_atTop (4 : ℝ),
      Zeta23.Assembly.eventually_l_pos,
      Zeta23.Assembly.eventually_calE_nonneg P hlam0
        (zero_le_one.trans hP.one_le_w),
      Zeta23.ThmD.eventually_w8 hP, h4pi, hgrid, heta1]
      with T hTl hGG hid haT hT₁ hT₂ hTailT hT4 hl hE0 h8 h4 hgr he1
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hapos : 0 < aT T := by linarith [haT.1]
    have hLpos : 0 < P.L T := by
      simp only [Zeta23.Params.L]
      exact mul_pos hlam0 hl
    have hrt : rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) =
        (aT T * P.L T)⁻¹ * trG T := by
      rw [Zeta23.Assembly.rtrace_hat, hGG,
        Zeta23.Assembly.rtrace_tilde_Gp, hidtr, hida]
      rfl
    have hfrEq : frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) =
        ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [Zeta23.Assembly.frobSq_hat, hGG,
        Zeta23.Assembly.frobSq_tilde_Gp, hidfr, hida]
      rfl
    have htrBound : |rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
        N T| ≤ R₁ T := by
      rw [hrt]
      exact Zeta23.Assembly.trGhat_sub_N_le hapos hLpos
        (by simpa only [N, R₁] using htr1 T hT₁)
    have hfrBound : frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) ≤
        cinv T * N T + R₂ T := by
      rw [hfrEq]
      have h := hfr2 T hT₂
      simp only at h
      have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T ≤
          C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
      have heq : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T =
          trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]
      rw [heq]
      simp only [R₂]
      linarith
    have hfinite := endpointAffine_finite hP hlam hT4 h8 h4 hgr
      (hconjD T) Zeta23.ZeroSide.phiHatReal
      (Zeta23.ThmD.poissonSqD hP h8) hTl htrBound hfrBound
      hA0.le hB0 hA1 hcert he1
    have hBt0 : 0 ≤ Bt T := by
      simp only [Bt]
      exact div_nonneg hTl.theta_nonneg (mul_pos hapos hLpos).le
    have hsqrt := Real.sqrt_le_sqrt hfrBound
    have htailLe :
        θ₀ T / ((P.atD T).a T * P.L T) *
            (4 + 2 * Real.sqrt
              (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))) +
              θ₀ T / ((P.atD T).a T * P.L T)) ≤
          Bt T * (4 + 2 * Real.sqrt (cinv T * N T + R₂ T) + Bt T) := by
      rw [hida]
      simp only [Bt]
      exact mul_le_mul_of_nonneg_left (by linarith) hBt0
    have hDynamic :
        3 * (2 - cinv T) * N T - 2 * B * P.L T * T -
            (3 * baseR T +
              36 * eta T *
                (N T + (Zeta23.Assembly.NII Z T : ℝ) + 2) +
              10 + bad T) ≤
          (3 - A) * (Z.N0s T (2 * T) : ℝ) := by
      simp only [N, cinv, R₁, R₂] at hfinite
      simp only [baseR, N, cinv, R₁, R₂, Bt, eta, bad]
      linarith
    have hN0 : 0 ≤ N T := by
      simp only [N]
      positivity
    have hcinvDrift := mul_le_mul_of_nonneg_right
      (le_abs_self (cinv T - c⁻¹)) hN0
    have hspanDrift := mul_le_mul_of_nonneg_left
      (le_abs_self (P.L T * T - 2 * Real.pi * N T))
      (show 0 ≤ 2 * B by positivity)
    simp only [Cnum, err]
    nlinarith
  have hNtop : Tendsto N atTop atTop :=
    Zeta23.Assembly.tendsto_N_atTop Z H.RvM
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1 : ℝ)) := by
      refine Zeta23.Assembly.isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [haRange] with T haT
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [haT.1]))]
      rw [div_le_iff₀ (by linarith [haT.1])]
      nlinarith [haT.1]
    have ho := Zeta23.Assembly.isLittleO_of_bdd_mul hbd
      (Zeta23.Assembly.isLittleO_N_of_isLittleO_Tl Z H.RvM
        (Zeta23.Assembly.isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact ho.congr_left fun T => by simp only [R₁]; ring
  have hcinvBd : ∀ᶠ T in atTop,
      0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
    have hcpos : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc0
    filter_upwards [hcinvTo.eventually (eventually_ge_nhds hcpos),
      hcinvTo.eventually
        (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))]
      with T h1 h2
    exact ⟨h1, h2⟩
  have hcinvO : cinv =O[atTop] (fun _ => (1 : ℝ)) := by
    refine Zeta23.Assembly.isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
    filter_upwards [hcinvBd] with T h
    rw [abs_of_nonneg h.1]
    exact h.2
  have o2 : R₂ =o[atTop] N := by
    have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (nhds 0) := by
      simpa using hcalE.const_mul C₂
    have hi : (fun T => cinv T * N T) =O[atTop] N := by
      simpa using hcinvO.mul (isBigO_refl N atTop)
    have ho := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO hi
    refine (ho.congr_left fun T => ?_).congr_right fun T => by simp
    simp only [R₂]
  have o3 : (fun T => (Zeta23.Assembly.NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (Zeta23.Assembly.NII Z T : ℝ))
        =O[atTop] (fun T => Real.sqrt T * Zeta23.l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, Zeta23.Assembly.eventually_l_pos]
        with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO
      (Zeta23.Assembly.isLittleO_N_of_isLittleO_Tl Z H.RvM
        Zeta23.Assembly.isLittleO_sqrt_mul_l_Tl)
  have oBt : Tendsto Bt atTop (nhds 0) := by
    have hup : Tendsto (fun T =>
        2 * |Cθ| *
          (Zeta23.l T * T ^ (P.lam / 2 - 1) / P.L T))
        atTop (nhds 0) := by
      simpa using
        (Zeta23.Assembly.tendsto_theta_over_L P hlam0 hlam1).const_mul
          (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, haRange, Zeta23.Assembly.eventually_l_pos]
        with T hTl haT hl
      have hLpos : 0 < P.L T := by
        simp only [Zeta23.Params.L]
        exact mul_pos hlam0 hl
      simp only [Bt]
      exact div_nonneg hTl.theta_nonneg (by nlinarith [haT.1])
    · filter_upwards [hTail, haRange, Zeta23.Assembly.eventually_l_pos,
        hθ, eventually_gt_atTop (0 : ℝ)]
        with T hTl haT hl hθT hT0
      have hLpos : 0 < P.L T := by
        simp only [Zeta23.Params.L]
        exact mul_pos hlam0 hl
      have hapos : 0 < aT T := by linarith [haT.1]
      have hq0 : 0 ≤ Zeta23.l T * T ^ (P.lam / 2 - 1) / P.L T := by
        positivity
      simp only [Bt]
      rw [div_le_iff₀ (mul_pos hapos hLpos)]
      calc
        θ₀ T ≤ Cθ * Zeta23.l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * Zeta23.l T * T ^ (P.lam / 2 - 1) := by
          gcongr
          exact le_abs_self _
        _ = |Cθ| *
            (Zeta23.l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by
          field_simp
        _ ≤ (2 * |Cθ| *
            (Zeta23.l T * T ^ (P.lam / 2 - 1) / P.L T)) *
              (aT T * P.L T) := by
          have heq : |Cθ| *
              (Zeta23.l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T =
            (2 * |Cθ| *
              (Zeta23.l T * T ^ (P.lam / 2 - 1) / P.L T)) *
                (1 / 2 * P.L T) := by ring
          rw [heq]
          have hinner : 1 / 2 * P.L T ≤ aT T * P.L T :=
            mul_le_mul_of_nonneg_right haT.1 hLpos.le
          exact mul_le_mul_of_nonneg_left hinner
            (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg Cθ)) hq0)
  have obase : baseR =o[atTop] N := by
    have h := Zeta23.Assembly.err_isLittleO hNtop o1 o2 o3 oBt hcinvBd
    simpa only [baseR] using h
  have hsumO : (fun T =>
      N T + (Zeta23.Assembly.NII Z T : ℝ) + 2) =O[atTop] N := by
    have hconst : (fun _ : ℝ => (2 : ℝ)) =O[atTop] N := by
      refine IsBigO.of_bound 2 ?_
      filter_upwards [hNtop.eventually_ge_atTop 1] with T hN
      rw [norm_of_nonneg (by norm_num), Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      nlinarith
    exact ((isBigO_refl N atTop).add o3.isBigO).add hconst
  have oeta : (fun T =>
      36 * eta T *
        (N T + (Zeta23.Assembly.NII Z T : ℝ) + 2)) =o[atTop] N := by
    have hetaOne : eta =o[atTop] (fun _ => (1 : ℝ)) :=
      (isLittleO_one_iff ℝ).2 hetaTo
    have h := hetaOne.mul_isBigO hsumO
    have h' : (fun T => eta T *
        (N T + (Zeta23.Assembly.NII Z T : ℝ) + 2)) =o[atTop] N := by
      simpa using h
    simpa only [mul_assoc] using h'.const_mul_left 36
  have obad : bad =o[atTop] N := by
    have h := nonInteriorSimpleZeros_isLittleO_N Z H.RvM P hconjD
    simpa only [bad, N] using h
  have oconst : (fun _ : ℝ => (10 : ℝ)) =o[atTop] N := by
    exact constant_isLittleO_of_tendsto_atTop hNtop 10
  have ocinv : (fun T => 3 * |cinv T - c⁻¹| * N T) =o[atTop] N := by
    exact const_mul_abs_sub_mul_isLittleO (N := N) (k := 3) hcinvTo
  have ospan : (fun T =>
      2 * B * |P.L T * T - 2 * Real.pi * N T|) =o[atTop] N := by
    rw [hNdef]
    exact endpoint_span_abs_isLittleO Z H.RvM P hlam (2 * B)
  have herrO : err =o[atTop] N := by
    have hsum := (((((obase.const_mul_left 3).add oeta).add oconst).add obad).add
      ocinv).add ospan
    simpa only [err] using hsum
  have hnum := Zeta23.Assembly.eps_form_of_isLittleO hmain
    (Eventually.of_forall fun T => by simp only [N]; positivity) herrO
  intro ε hε
  have hd : 0 < 3 - A := by linarith
  obtain ⟨T₀, hT₀⟩ := hnum ((3 - A) * ε) (mul_pos hd hε)
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have heq : Cnum - (3 - A) * ε =
      (3 - A) * (Cnum / (3 - A) - ε) := by
    field_simp
  rw [heq] at h
  have hmul : (3 - A) *
      ((Cnum / (3 - A) - ε) * N T) ≤
        (3 - A) * (Z.N0s T (2 * T) : ℝ) := by
    simpa only [mul_assoc] using h
  have hout : (Cnum / (3 - A) - ε) * N T ≤
      (Z.N0s T (2 * T) : ℝ) := le_of_mul_le_mul_left hmul hd
  simpa only [Cnum] using hout

/-- All analytic hypotheses of the endpoint affine theorem are supplied by
the existing concrete Zeta23 construction. -/
theorem thmD_endpoint_affine_concrete
    (Z : Zeta23.ZeroConfig) (H : Zeta23.PaperInputs Z)
    (P : Zeta23.Params) (hP : P.Valid) (hlam : P.lam = 1)
    {A B : ℝ} (hA0 : 0 < A) (hB0 : 0 < B) (hA1 : A ≤ 1)
    (hcert : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      A ≤ montgomeryTaylorTripleEnergy a b + B * (a + b)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((3 * Zeta23.ThmD.HD 1 - 4 * Real.pi * B) / (3 - A) - ε) *
          (Z.N T (2 * T) : ℝ) ≤
        Z.N0s T (2 * T) := by
  have hLoc : Zeta23.ThmD.LocalHypsCoreDEventually P :=
    Zeta23.ThmD.localHypsCoreD_eventually hP
  have hTr := Zeta23.ThmD.tracesBoundsD_concrete (Z := Z) hP H hLoc
  have hc := Zeta23.ThmD.tendsto_cRatio_concrete hP Z
  have hc0 := Zeta23.ThmD.cStar_pos hP.lam_pos hP.lam_le_one
  have haRange : ∀ᶠ T in atTop,
      1 / 2 ≤ (Zeta23.ThmD.concreteDataD P Z).aT T ∧
        (Zeta23.ThmD.concreteDataD P Z).aT T ≤ 1 :=
    (Zeta23.ThmD.concreteFactsD hP H hLoc).ab_range.mono fun T h =>
      ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨θ₀, hTail, hθ₀⟩ :=
    Zeta23.ThmD.eventually_tailPackageD Z H hP
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hNII := Zeta23.Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := Zeta23.ThmD.eventually_GzGpD Z H hP
  have hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = (Zeta23.ThmD.concreteDataD P Z).trG T ∧
      (P.atD T).trGtildeSq T = (Zeta23.ThmD.concreteDataD P Z).trG2 T ∧
      (P.atD T).a T = (Zeta23.ThmD.concreteDataD P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Zeta23.Params.atD_trGtilde T hP,
        Zeta23.Params.atD_trGtildeSq T hP,
        Zeta23.Params.atD_a T hP⟩
  have hcalE := Zeta23.Assembly.calE_tendsto_zero P hP.lam_pos
    hP.lam_le_one (zero_le_one.trans hP.one_le_w)
  have h := thmD_endpoint_affine_abstract Z H P hP hlam
    _ _ _ _ _ hTr hc0 hc haRange θ₀ hTail hθ₀ hNII hGzGp hId
      hcalE hA0 hB0 hA1 hcert
  simpa only [Zeta23.ThmD.HD, hlam, one_div] using h

/-- The affine slope `B=A/(6π)` makes the endpoint quotient strictly larger
than the imported `HD(1)` constant. -/
lemma montgomeryTaylor_affine_constant_gt_HD_one
    {A B : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1)
    (hB : B = A / (6 * Real.pi)) :
    Zeta23.ThmD.HD 1 <
      (3 * Zeta23.ThmD.HD 1 - 4 * Real.pi * B) / (3 - A) := by
  have hden : 0 < 3 - A := by linarith
  have hgap : 0 < A * (Zeta23.ThmD.HD 1 - (2 : ℝ) / 3) /
      (3 - A) := by
    exact div_pos (mul_pos hA0
      (sub_pos.mpr externalZeta23_HD_one_gt_two_thirds)) hden
  have hid :
      (3 * Zeta23.ThmD.HD 1 - 4 * Real.pi * B) / (3 - A) -
          Zeta23.ThmD.HD 1 =
        A * (Zeta23.ThmD.HD 1 - (2 : ℝ) / 3) / (3 - A) := by
    rw [hB]
    field_simp [Real.pi_ne_zero, hden.ne']
    ring
  linarith

/-- **Unconditional literal improvement over Zeta23.**  There exists a
constant strictly larger than `HD(1)` for which the asymptotic lower bound
holds for the actual number of simple Riemann-zeta zeros on the critical
line.  The witness is generated by the proved compact affine certificate;
there are no hypotheses and no numerical oracle. -/
theorem externalZeta23_montgomeryTaylor_simple_strict_improvement :
    ∃ C : ℝ, Zeta23.ThmD.HD 1 < C ∧
      ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
        (C - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
          Zeta23.N0simple T (2 * T) := by
  obtain ⟨A, B, hA0, hB0, hA1, hB, hcert⟩ :=
    exists_montgomeryTaylorTripleAffineCertificate
  let P : Zeta23.Params := Zeta23.paramsOf Zeta23.stdProfile 1
  have hP : P.Valid := by
    dsimp only [P]
    exact Zeta23.paramsOf_valid Zeta23.taperProfile_stdProfile one_pos le_rfl
  have hlam : P.lam = 1 := by rfl
  let C : ℝ :=
    (3 * Zeta23.ThmD.HD 1 - 4 * Real.pi * B) / (3 - A)
  have hC : Zeta23.ThmD.HD 1 < C := by
    dsimp only [C]
    exact montgomeryTaylor_affine_constant_gt_HD_one hA0 hA1 hB
  have hmain := thmD_endpoint_affine_concrete
    Zeta23.zetaZeroConfig Zeta23.paperInputs_zeta P hP hlam
      hA0 hB0 hA1 hcert
  refine ⟨C, hC, ?_⟩
  simpa only [C, P, Zeta23.paramsOf, Zeta23.zetaZeroConfig_N,
    Zeta23.zetaZeroConfig_N0s] using hmain

end Zeta23InverseSampling
end RiemannGaussian
