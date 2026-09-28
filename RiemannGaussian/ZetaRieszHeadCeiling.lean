/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFivePositiveHead

/-!
# Upper payments for the same exponential prime heads

The lower endgame does not exclude multiple zeros. This module retains
its literal signed carrier and uses a positive-cosine supply window to
pay the same small-prime heads from above. The complementary carrier is
not replaced by an unsigned allowance.
-/

namespace RiemannGaussian.ZetaRieszHeadCeiling
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic ZetaRieszRadialCompensation
open ZetaRieszBandCompensation ZetaRieszSmallPrimeCompensation ZetaRieszFourPrimeHead
open ZetaRieszFivePositiveHead ZetaRieszPrimeCountFrequency ZetaRieszParityPacket

/-- At every sufficiently large fixed height, each radial slab contains
an actual short window where the original cosine is at least one half. -/
theorem exists_short_positive_window {y : ℝ} (hy : 16 ≤ |y|) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1/20 ∧ ∀ b : ℝ, ∃ v : ℝ,
      0 ≤ v ∧ v ≤ 1/2 ∧ ∀ t : ℝ, b+v ≤ t → t ≤ b+v+4*h →
        (1/2 : ℝ) ≤ Real.cos (y*t) := by
  let z := |y|
  have hz : 0 < z := by dsimp [z]; linarith
  let h := 1/(10*(z+1))
  have hh : 0 < h := by dsimp [h]; positivity
  have hhhi : h ≤ 1/20 := by
    dsimp [h]
    apply (div_le_iff₀ (by positivity)).mpr
    dsimp [z]
    linarith
  refine ⟨h,hh,hhhi,?_⟩
  intro b
  let k : ℤ := ⌈(z*b)/(2*Real.pi)⌉
  let v := ((k : ℝ)*(2*Real.pi))/z-b
  have hklo : z*b ≤ (k : ℝ)*(2*Real.pi) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 2*Real.pi)).mp (Int.le_ceil _)
  have hkhi : (k : ℝ)*(2*Real.pi) < z*b+2*Real.pi := by
    have h := mul_lt_mul_of_pos_right (Int.ceil_lt_add_one ((z*b)/(2*Real.pi)))
      (by positivity : (0 : ℝ) < 2*Real.pi)
    simpa only [add_mul,div_mul_cancel₀ _ (by positivity : 2*Real.pi ≠ 0),one_mul] using h
  have hvEq : z*(b+v) = (k : ℝ)*(2*Real.pi) := by dsimp [v]; field_simp; ring
  have hv : 0 ≤ v := by nlinarith
  have hvhi : v ≤ 1/2 := by
    have hpi := Real.pi_lt_four
    have hzy : (16 : ℝ) ≤ z := hy
    nlinarith
  refine ⟨v,hv,hvhi,?_⟩
  intro t ht htu
  have he : Real.cos (z*(b+v)) = 1 := by rw [hvEq,Real.cos_int_mul_two_pi]
  have hhphase : 4*z*h ≤ 1/2 := by
    dsimp [h]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hd : |z*t-z*(b+v)| ≤ 1/2 := by
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  have hc := Real.abs_cos_sub_cos_le (z*t) (z*(b+v))
  rw [he] at hc
  have hc' := (abs_le.mp (hc.trans hd)).1
  have hcos : (1/2 : ℝ) ≤ Real.cos (z*t) := by linarith
  have hec : Real.cos (z*t) = Real.cos (y*t) := by
    dsimp [z]
    rcases le_total 0 y with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,neg_mul,Real.cos_neg]
  rwa [hec] at hcos


/-- The same original four-prime atom supplies a negative credit on a
positive-cosine window. Calibration is used only to reuse its proved
amplitude lower bound; the conclusion keeps the original height. -/
theorem supply_atom_upper (A : Finset ℕ) {N M i j k : ℕ} {h v L y : ℝ}
    (hh : 0 < h) (hhhi : h ≤ 1/20)
    (hi : i ∈ grid M h) (hj : j ∈ grid M h) (hk : k ∈ grid M h)
    (hv : 0 ≤ v) (hvhi : v ≤ 1/2) (hw : h+v ≤ (M : ℝ)/1000)
    (hL0 : 0 < L) (hL : (271/200 : ℝ)*M ≤ L) (hLu : L ≤ (143/100 : ℝ)*M)
    (hshare : (1/2 : ℝ) ≤ 1-4*Real.exp (-(N : ℝ)/64))
    {p : Fin 4 → ℕ} (hp : p ∈ tuples M h v i j k)
    (hcos : (1/2 : ℝ) ≤ Real.cos (y*Real.log (∏ a, p a : ℕ))) :
    (M : ℝ)/160*Real.exp (-3/2 : ℝ)*radialEnvelope N M ≤
      -(residualCoefficient A L N (∏ a, p a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (∏ a, p a)).re := by
  have hs := tuple_squarefree hh hi hj hk hv hw hp
  have hn1 : 1 < ∏ a, p a := by
    apply (tuple_bounds hp 0).1.one_lt.trans_le
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) (Finset.dvd_prod_of_mem p (Finset.mem_univ 0))
  have ht : 0 < Real.log (∏ a, p a : ℕ) := Real.log_pos (by exact_mod_cast hn1)
  have hcal := supply_atom_lower A hh hhhi hi hj hk hv hvhi hw hL0 hL hLu hshare hp
    (y := Real.pi/Real.log (∏ a, p a : ℕ)) (by
      rw [div_mul_cancel₀ _ ht.ne',Real.cos_pi]
      norm_num)
  have hc := tuple_coefficient_le_wide hh hi hj hk hv hw hL0 hL hLu hp
  have hnonpos : weight A N (∏ a, p a)*(SquarefreeVaughanLogSource.coefficient L (∏ a, p a)).re ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (weight_nonneg A N _)
      (by linarith [Nat.cast_nonneg (α := ℝ) M])
  have hhcos := mul_le_mul_of_nonpos_left hcos hnonpos
  rw [re_residual_atom,div_mul_cancel₀ _ ht.ne',Real.cos_pi] at hcal
  rw [re_residual_atom]
  nlinarith only [hcal,hhcos]

/-- An actual negative supply at the original moving order and height. -/
theorem eventually_supply_upper {h : ℝ} (hh : 0 < h) (hhhi : h ≤ 1/20) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (A : Finset ℕ) (v L y : ℝ),
      N ≤ 2*M → 0 ≤ v → v ≤ 1/2 → 0 < L →
      (271/200 : ℝ)*M ≤ L → L ≤ (143/100 : ℝ)*M →
      (∀ t : ℝ, 2*M+v ≤ t → t ≤ 2*M+v+4*h → (1/2 : ℝ) ≤ Real.cos (y*t)) →
      c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
        -(∑ n ∈ supply M h v, residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨c,hc,hcards⟩ := eventually_supply_card_lower hh (by norm_num : (0 : ℝ) ≤ 1/2)
  obtain ⟨M0,hM0⟩ := eventually_atTop.mp hcards
  refine ⟨c/160*Real.exp (-3/2 : ℝ),by positivity,?_⟩
  have ht : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ)/64)) atTop (𝓝 0) := by
    simpa only [neg_div,Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (by norm_num : (0 : ℝ) < 64))
  filter_upwards [eventually_ge_atTop (2*M0),eventually_ge_atTop (2000 : ℕ),
    ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1/8)]
    with N hN0 hN hsmall M A v L y hNM hv hvhi hL0 hL hLu hphase
  have hcM := hM0 M (by omega) v hv hvhi
  have hMR : (1000 : ℝ) ≤ M := by exact_mod_cast (show 1000 ≤ M by omega)
  have hw : h+v ≤ (M : ℝ)/1000 := by linarith
  have ha (n : ℕ) (hn : n ∈ supply M h v) :
      (M : ℝ)/160*Real.exp (-3/2 : ℝ)*radialEnvelope N M ≤
        -(residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
    obtain ⟨ijk,hijk,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨hi,hjk⟩ := Finset.mem_product.mp hijk
    obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    have hb := tuple_log_bounds hp
    exact supply_atom_upper A hh hhhi hi hj hk hv hvhi hw hL0 hL hLu (by linarith) hp
      (hphase _ hb.1.le hb.2)
  have hsum := Finset.sum_le_sum ha
  rw [Finset.sum_const,nsmul_eq_mul,Finset.sum_neg_distrib,← Complex.re_sum] at hsum
  have hscale := mul_le_mul_of_nonneg_right hcM
    (show 0 ≤ (M : ℝ)/160*Real.exp (-3/2 : ℝ)*radialEnvelope N M by
      positivity [radialEnvelope_nonneg N M])
  exact (le_of_eq (by ring)).trans (hscale.trans hsum)

/-- A fixed exponential small-prime range, together with the balanced
triple band, is paid from above by ONE negative four-prime supply. The fractions remain
one half plus three eighths. The width and phase window are chosen once. -/
theorem eventually_joint_slabs_upper_log_head_with_scale {y : ℝ} (hy : 16 ≤ |y|) :
    ∃ η h δ c : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < c ∧
      ∀ᶠ N : ℕ in atTop, ∀ (M Q : ℕ) (D S H F A : Finset ℕ) (L : ℝ),
        N ≤ 2*M → Real.log Q ≤ δ*N → 0 < L → (271/200 : ℝ)*M ≤ L → L ≤ (143/100 : ℝ)*M →
        (∀ n ∈ H, Squarefree n ∧ n.primeFactors.card = 4 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ ∃ r ∈ n.primeFactors, r ≤ Q) →
        (∀ n ∈ F, Squarefree n ∧ n.primeFactors.card = 5 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ (∃ r ∈ n.primeFactors, r ≤ Q) ∧
          0 < (SquarefreeVaughanLogSource.coefficient L n).re) →
        ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1/2 ∧
          let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
          let Y := -(∑ n ∈ supply M h v, f n).re
          c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤ Y ∧
          0 < Y ∧
            ‖∑ n ∈ slabTriples D M η, f n‖ ≤ (1/2 : ℝ)*Y ∧
            ‖∑ n ∈ smallTriples S M Q, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ H, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ F, f n‖ ≤ (1/8 : ℝ)*Y := by
  obtain ⟨h,hh,hhhi,hphase⟩ := exists_short_positive_window hy
  obtain ⟨c,hc,hsupply⟩ := eventually_supply_upper hh hhhi
  let B : ℝ := 27*(6*Real.log 4)^3*Real.exp 8
  have hB : 0 < B := by dsimp [B]; positivity
  let η := min (1/1000 : ℝ) (Real.sqrt (c/(2*B)))
  have hη : 0 < η := lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity))
  have hηu : η ≤ 1/1000 := min_le_left _ _
  have hηcost : B*η^2 ≤ c/2 := by
    have hs := pow_le_pow_left₀ hη.le (min_le_right (1/1000 : ℝ) (Real.sqrt (c/(2*B)))) 2
    rw [Real.sq_sqrt (by positivity)] at hs
    have ht := (le_div_iff₀ (by positivity : 0 < 2*B)).mp hs
    nlinarith
  obtain ⟨δ₄,hδ₄,hδ₄u,hbudget⟩ := exists_log_head_budget (show 0 < c/8 by positivity)
  obtain ⟨δ₅,hδ₅,_,hcost5⟩ := eventually_small_five_positive_log_cost (show 0 < c/8 by positivity)
  let δ := min δ₄ δ₅
  have hδ : 0 < δ := lt_min hδ₄ hδ₅
  have hδu : δ ≤ 1/128 := (min_le_left _ _).trans hδ₄u
  refine ⟨η,h,δ,c,hη,hηu,hh,hhhi,hδ,hδu,hc,?_⟩
  filter_upwards [hsupply,hbudget,hcost5,eventually_ge_atTop (200 : ℕ),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2/η)]
    with N hs hbudget hcost5 hN hsize M Q D S H F A L hNM hQ hL0 hL hLu hH hF
  have hM : 20 ≤ M := by omega
  have hηM : 1 ≤ η*M := by
    have ht := (div_le_iff₀ hη).mp hsize
    have hnr : (N : ℝ) ≤ 2*M := by exact_mod_cast hNM
    nlinarith
  obtain ⟨v,hv,hvhi,hcos⟩ := hphase (2*(M : ℝ))
  have hpos := hs M A v L y hNM hv hvhi hL0 hL hLu hcos
  have hLM : (M : ℝ) ≤ L := by nlinarith [Nat.cast_nonneg (α := ℝ) M]
  have hneg := slab_norm_upper D A hη hηu hM hηM hNM hL0 hLM y
  have hQ₄ : Real.log Q ≤ δ₄*N := hQ.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg (α := ℝ) N))
  have hQ₅ : Real.log Q ≤ δ₅*N := hQ.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg (α := ℝ) N))
  obtain ⟨hQ32,hbudget3,hbudget4⟩ := hbudget M Q hNM hQ₄
  have hsm5 := hcost5 M Q F A L y hNM hQ₅ hL0 hL hLu hF
  have hsm3 := small_triples_norm_upper S A (by omega : 1 ≤ M) hNM
    (by linarith [Nat.cast_nonneg (α := ℝ) M] : Real.log Q ≤ (M : ℝ)/8) hL0 hLM y
  have hsm4 := small_four_norm_upper H A (by omega : 100 ≤ M) hNM hQ32 hL0 hL hLu y hH
  have hb3 := mul_le_mul_of_nonneg_right hbudget3
    (show 0 ≤ Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M by
      positivity [radialEnvelope_nonneg N M])
  have hb4 := mul_le_mul_of_nonneg_right hbudget4
    (show 0 ≤ Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M by
      positivity [radialEnvelope_nonneg N M])
  refine ⟨v,hv,hvhi,?_⟩
  dsimp only
  refine ⟨hpos,lt_of_lt_of_le (by positivity [radialEnvelope_pos N (show 0 < M by omega)]) hpos,?_,?_,?_,?_⟩
  · have hbudget := mul_le_mul_of_nonneg_right hηcost
      (show 0 ≤ (M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M by
        positivity [radialEnvelope_nonneg N M])
    have hh := mul_le_mul_of_nonneg_left hpos (by norm_num : (0 : ℝ) ≤ 1/2)
    change ‖_‖ ≤ B*η^2*_*_/_*_ at hneg
    have hmid : B*η^2*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
        (1/2 : ℝ)*(c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) := by
      calc
        _ = B*η^2*((M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) := by ring
        _ ≤ c/2*((M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) := hbudget
        _ = _ := by ring
    exact hneg.trans (hmid.trans hh)
  · have hh := mul_le_mul_of_nonneg_left hpos (by norm_num : (0 : ℝ) ≤ 1/8)
    apply hsm3.trans
    calc
      _ ≤ (c/8*M)*(Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) := by
        simpa only [div_eq_mul_inv,mul_assoc] using hb3
      _ ≤ _ := by convert hh using 1 <;> first | rfl | ring
  · have hh := mul_le_mul_of_nonneg_left hpos (by norm_num : (0 : ℝ) ≤ 1/8)
    apply hsm4.trans
    calc
      _ ≤ (c/8*M)*(Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) := by
        simpa only [div_eq_mul_inv,mul_assoc] using hb4
      _ ≤ _ := by convert hh using 1 <;> first | rfl | ring

  · have hh := mul_le_mul_of_nonneg_left hpos (by norm_num : (0 : ℝ) ≤ 1/8)
    apply hsm5.trans
    convert hh using 1
    ring


/-- The same signed spending theorem with its supply calibration forgotten.
The calibrated version remains available for additional disjoint payments. -/
theorem eventually_joint_slabs_upper_log_head {y : ℝ} (hy : 16 ≤ |y|) :
    ∃ η h δ : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (M Q : ℕ) (D S H F A : Finset ℕ) (L : ℝ),
        N ≤ 2*M → Real.log Q ≤ δ*N → 0 < L → (271/200 : ℝ)*M ≤ L → L ≤ (143/100 : ℝ)*M →
        (∀ n ∈ H, Squarefree n ∧ n.primeFactors.card = 4 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ ∃ r ∈ n.primeFactors, r ≤ Q) →
        (∀ n ∈ F, Squarefree n ∧ n.primeFactors.card = 5 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ (∃ r ∈ n.primeFactors, r ≤ Q) ∧
          0 < (SquarefreeVaughanLogSource.coefficient L n).re) →
        ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1/2 ∧
          let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
          let Y := -(∑ n ∈ supply M h v, f n).re
          0 < Y ∧
            ‖∑ n ∈ slabTriples D M η, f n‖ ≤ (1/2 : ℝ)*Y ∧
            ‖∑ n ∈ smallTriples S M Q, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ H, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ F, f n‖ ≤ (1/8 : ℝ)*Y := by
  obtain ⟨η,h,δ,c,hη,hηu,hh,hhu,hδ,hδu,hc,hpay⟩ := eventually_joint_slabs_upper_log_head_with_scale hy
  refine ⟨η,h,δ,hη,hηu,hh,hhu,hδ,hδu,?_⟩
  filter_upwards [hpay] with N hpay M Q D S H F A L hNM hQ hL0 hL hLu hH hF
  obtain ⟨v,hv,hvu,_,hY,hX,hZ,hHpay,hFpay⟩ :=
    hpay M Q D S H F A L hNM hQ hL0 hL hLu hH hF
  exact ⟨v,hv,hvu,hY,hX,hZ,hHpay,hFpay⟩


/-- The upper spending ledger for the unchanged finite sum. This is
the lower ledger applied algebraically to its negative, retaining all
favorable negative observations and the exact signed complement. -/
theorem re_sum_le_joint_spending {D X Z H F Y : Finset ℕ} (f : ℕ → ℂ)
    (hsub : X ∪ Z ∪ H ∪ Y ∪ F ⊆ D) (hXZ : Disjoint X Z)
    (hXH : Disjoint X H) (hZH : Disjoint Z H)
    (hXY : Disjoint X Y) (hZY : Disjoint Z Y) (hHY : Disjoint H Y)
    (hF : Disjoint F (X ∪ Z ∪ H ∪ Y))
    (hXcost : ‖∑ n ∈ X, f n‖ ≤ (1/2 : ℝ)*(-(∑ n ∈ Y, f n).re))
    (hZcost : ‖∑ n ∈ Z, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ Y, f n).re))
    (hHcost : ‖∑ n ∈ H, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ Y, f n).re))
    (hFcost : ‖∑ n ∈ F, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ Y, f n).re)) :
    (∑ n ∈ D, f n).re ≤
      (∑ n ∈ D\(X ∪ Z ∪ H ∪ Y ∪ F), f n).re+
      min (∑ n ∈ X, f n).re 0+min (∑ n ∈ Z, f n).re 0+
      min (∑ n ∈ H, f n).re 0+min (∑ n ∈ F, f n).re 0+
      (∑ n ∈ Y, f n).re/8 := by
  have h := ZetaRieszFivePositiveHead.re_sum_ge_joint_spending (fun n => -f n)
    hsub hXZ hXH hZH hXY hZY hHY hF
    (by simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using hXcost)
    (by simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using hZcost)
    (by simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using hHcost)
    (by simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using hFcost)
  have hm (a : ℝ) : max (-a) 0 = -min a 0 := by
    simp only [min_def,max_def]
    split_ifs <;> linarith
  simp only [Finset.sum_neg_distrib,Complex.neg_re,hm] at h
  linarith only [h]

private theorem log_floor_exp_le {x : ℝ} (hx : 0 ≤ x) :
    Real.log (⌊Real.exp x⌋₊ : ℕ) ≤ x := by
  by_cases hz : ⌊Real.exp x⌋₊ = 0
  · simpa only [hz,Nat.cast_zero,Real.log_zero] using hx
  have hp : (0 : ℝ) < (⌊Real.exp x⌋₊ : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hz
  have h := Real.log_le_log hp (Nat.floor_le (Real.exp_nonneg x))
  simpa only [Real.log_exp] using h

/-- A fixed exponential prime head is paid throughout the original
radial union from above. This enlarges the two paid head selections; it does not add
another copy of the supply. All unselected labels remain signed, and all
four negative credits and one eighth of the same supply remain. -/
theorem eventually_core_exponential_ceiling {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h δ : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
        let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q (SquarefreeVaughanLogSource.length u N))
        let Ys := radialSupply N h v
        let W := ∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs), f n
        0 < -(∑ n ∈ Ys, f n).re ∧
          ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re ≤
            u^(N+1)*(W.re+min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
              min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+(∑ n ∈ Ys, f n).re/8) := by
  obtain ⟨η,h,δ,hη,hηu,hh,hhu,hδ,hδu,hpay⟩ := eventually_joint_slabs_upper_log_head hy
  refine ⟨η,h,δ,hη,hηu,hh,hhu,hδ,hδu,?_⟩
  filter_upwards [tendsto_dyadicMomentOrder.eventually hpay,
    tendsto_dyadicMomentOrder.eventually (eventually_length_on_slabs hu hU),
    eventually_radial_supply_in_core hu hU hh hhu,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (2000 : ℕ))]
    with j hpay hL hsub hN
  let N := dyadicMomentOrder j
  let Q := ⌊Real.exp (δ*N)⌋₊
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := coreBand u N (dyadicPrimeCount j)
  let Xs := radialTriples S N η
  let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
  let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hQ : Real.log Q ≤ δ*N := log_floor_exp_le
    (mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) N))
  have hex : ∀ M : ℕ, ∃ v : ℝ, M ∈ radialIndices N →
      0 ≤ v ∧ v ≤ 1/2 ∧ 0 < -(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ slabTriples S M η, f n‖ ≤ (1/2 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) ∧
      ‖∑ n ∈ smallTriples (S\Xs) M Q, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) ∧
      ‖∑ n ∈ smallFours S M Q, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) ∧
      ‖∑ n ∈ smallPositiveFives S M Q L, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) := by
    intro M
    by_cases hM : M ∈ radialIndices N
    · obtain ⟨v,hv,hvu,hY,hX,hZ,hH,hF⟩ := hpay M Q S (S\Xs) (smallFours S M Q) (smallPositiveFives S M Q L) A L
        (hL M hM).1 hQ (SquarefreeVaughanLogSource.length_pos _ _) (hL M hM).2.1 (hL M hM).2.2
        (by
          intro n hn
          obtain ⟨_,hs,hc,hlo,hhi,hmax,hsmall⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hc,hlo,hhi.le,hmax,hsmall⟩)
        (by
          intro n hn
          obtain ⟨_,hs,hc,hlo,hhi,hmax,hsmall,hpos⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hc,hlo,hhi.le,hmax,hsmall,hpos⟩)
      exact ⟨v,fun _ => ⟨hv,hvu,hY,hX,hZ,hH,hF⟩⟩
    · exact ⟨0,fun h => False.elim (hM h)⟩
  choose v hv using hex
  have hvb : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2 :=
    fun M hM => ⟨(hv M hM).1,(hv M hM).2.1⟩
  let Ys := radialSupply N h v
  have hY : 0 < -(∑ n ∈ Ys, f n).re := by
    change 0 < -(∑ n ∈ radialSupply N h v, f n).re
    rw [radialSupply,Finset.sum_biUnion (supply_disjoint hhu hvb),Complex.re_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_pos'
    · intro M hM
      exact (hv M hM).2.2.1.le
    · exact ⟨N,self_mem_radialIndices (by omega),(hv N (self_mem_radialIndices (by omega))).2.2.1⟩
  have hXpay := union_spending (f := fun n => -f n) hhu hvb (fun M hM => by
    simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using (hv M hM).2.2.2.1)
  have hZpay := norm_radial_payment (f := fun n => -f n)
    (fun _ _ _ _ hne => smallTriples_disjoint (S\Xs) Q hne) hhu hvb (fun M hM => by
      simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using (hv M hM).2.2.2.2.1)
  have hHpay := norm_radial_payment (f := fun n => -f n)
    (fun _ _ _ _ hne => smallFours_disjoint S Q hne) hhu hvb (fun M hM => by
      simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using (hv M hM).2.2.2.2.2.1)
  have hFpay := norm_radial_payment (f := fun n => -f n)
    (fun _ _ _ _ hne => smallPositiveFives_disjoint S Q L hne) hhu hvb (fun M hM => by
      simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using (hv M hM).2.2.2.2.2.2)
  simp only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] at hXpay hZpay hHpay hFpay
  have hXsub : Xs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hZsub : Zs ⊆ S\Xs := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hHsub : Hs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hFsub : Fs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hF5 : ∀ n ∈ Fs, n.primeFactors.card = 5 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hX3 : ∀ n ∈ Xs, n.primeFactors.card = 3 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hZ3 : ∀ n ∈ Zs, n.primeFactors.card = 3 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hH4 : ∀ n ∈ Hs, n.primeFactors.card = 4 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hY4 : ∀ n ∈ Ys, n.primeFactors.card = 4 :=
    fun _ hn => (radial_supply_geometry hN hh hhu hvb hn).1
  have hdisj (B C : Finset ℕ) (hB : ∀ n ∈ B, n.primeFactors.card = 3)
      (hC : ∀ n ∈ C, n.primeFactors.card = 4) : Disjoint B C :=
    Finset.disjoint_left.mpr (fun n hb hc => by have := hB n hb; have := hC n hc; omega)
  have hXZ : Disjoint Xs Zs := Finset.disjoint_left.mpr
    (fun _ hx hz => (Finset.mem_sdiff.mp (hZsub hz)).2 hx)
  have hHY : Disjoint Hs Ys := by
    apply Finset.disjoint_left.mpr
    intro n hn hnY
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨_,_,_,_,_,_,r,hr,hrsmall⟩ := Finset.mem_filter.mp hn
    have hrlog := Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).pos)
      (show (r : ℝ) ≤ Q by exact_mod_cast hrsmall)
    have hh := (radial_supply_geometry hN hh hhu hvb hnY).2 r hr
    have hδN := mul_le_mul_of_nonneg_right hδu (Nat.cast_nonneg (α := ℝ) N)
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hsuball : Xs ∪ Zs ∪ Hs ∪ Ys ⊆ S := by
    apply Finset.union_subset
    · exact Finset.union_subset (Finset.union_subset hXsub
        (fun _ hn => (Finset.mem_sdiff.mp (hZsub hn)).1)) hHsub
    · intro n hn
      obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
      exact hsub M hM (v M) (hvb M hM).1 (hvb M hM).2 hn
  have hFdisj : Disjoint Fs (Xs ∪ Zs ∪ Hs ∪ Ys) := by
    apply Finset.disjoint_left.mpr
    intro n hnF hn
    have hf := hF5 n hnF
    rcases Finset.mem_union.mp hn with hn | hnY
    · rcases Finset.mem_union.mp hn with hn | hnH
      · rcases Finset.mem_union.mp hn with hnX | hnZ
        · have := hX3 n hnX; omega
        · have := hZ3 n hnZ; omega
      · have := hH4 n hnH; omega
    · have := hY4 n hnY; omega
  have hfloor := re_sum_le_joint_spending f (Finset.union_subset hsuball hFsub) hXZ
    (hdisj Xs Hs hX3 hH4) (hdisj Zs Hs hZ3 hH4)
    (hdisj Xs Ys hX3 hY4) (hdisj Zs Ys hZ3 hY4) hHY hFdisj hXpay hZpay hHpay hFpay
  refine ⟨v,hvb,hY,?_⟩
  have hnorm := mul_le_mul_of_nonneg_left hfloor (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  change ((u : ℂ)^(N+1)*(∑ n ∈ S, f n)).re ≤ _
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact hnorm



/-- The whole exponential head of the actual three- and four-prime
classes, the positive five-prime class and the original balanced triple band are paid simultaneously.
One supply retains one eighth, all negative selected observations remain,
and every other label remains signed. Only previously controlled radial
and dominant-prime errors are added. The numerical whole-sum ceiling is open. -/
theorem eventually_core_full_exponential_ceiling {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h δ r C : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
        let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let Ys := radialSupply N h v
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q (SquarefreeVaughanLogSource.length u N))
        let B := balancedTriples S N η ∪ S.filter (fun n => Squarefree n ∧
          (n.primeFactors.card = 3 ∨ n.primeFactors.card = 4 ∨
          (n.primeFactors.card = 5 ∧ 0 < (SquarefreeVaughanLogSource.coefficient
            (SquarefreeVaughanLogSource.length u N) n).re)) ∧ ∃ p ∈ n.primeFactors, p ≤ Q)
        let W := ∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ B), f n
        0 < -(∑ n ∈ Ys, f n).re ∧
          ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re ≤
            u^(N+1)*(W.re+min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
              min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+(∑ n ∈ Ys, f n).re/8)+
                (r^N*C+2*zetaMoebiusLogMajorantMass (1+1/262144)*Real.exp (-(N : ℝ)/1000000)) := by
  obtain ⟨η,h,δ,hη,hηu,hh,hhu,hδ,hδu,hspend⟩ := eventually_core_exponential_ceiling hu hU hy
  obtain ⟨r,C,hr,hr1,hC,hmissed⟩ := ZetaRieszFivePositiveHead.exists_exponential_head_missed_bound
  refine ⟨η,h,δ,r,C,hη,hηu,hh,hhu,hδ,hδu,hr,hr1,hC,?_⟩
  have hord : Tendsto (fun j => (dyadicMomentOrder j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_dyadicMomentOrder
  filter_upwards [hspend,eventually_ge_atTop (32 : ℕ),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ)),
    hord.eventually_ge_atTop (4/η)] with j hj hj32 hN hsize
  obtain ⟨v,hvb,hY,hfloor⟩ := hj
  let N := dyadicMomentOrder j
  let Q := ⌊Real.exp (δ*N)⌋₊
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let Xs := radialTriples S N η
  let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
  let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let Ys := radialSupply N h v
  let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let B := balancedTriples S N η ∪ S.filter (fun n => Squarefree n ∧
    (n.primeFactors.card = 3 ∨ n.primeFactors.card = 4 ∨
          (n.primeFactors.card = 5 ∧ 0 < (SquarefreeVaughanLogSource.coefficient
            (SquarefreeVaughanLogSource.length u N) n).re)) ∧ ∃ p ∈ n.primeFactors, p ≤ Q)
  let D := B\(Xs ∪ Zs ∪ Hs ∪ Fs)
  have hηN : 4 ≤ η*N := by
    have ht := (div_le_iff₀ hη).mp hsize
    dsimp [N]
    nlinarith
  have hnorm := hmissed j η δ y u hj32 hN hη hηN hδ.le hu.le hU
  change ‖(u : ℂ)^(N+1)*∑ n ∈ D, f n‖ ≤ _ at hnorm
  have hreal : u^(N+1)*(∑ n ∈ D, f n).re ≤ r^N*C+2*zetaMoebiusLogMajorantMass (1+1/262144)*
      Real.exp (-(N : ℝ)/1000000) := by
    have ht := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).2
    simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] using ht
  have hBY : Disjoint B Ys := by
    apply Finset.disjoint_left.mpr
    intro n hnB hnY
    have hsupply := radial_supply_geometry (by omega : 2000 ≤ N) hh hhu hvb hnY
    rcases Finset.mem_union.mp hnB with hbal | hhead
    · have hc := (Finset.mem_filter.mp hbal).2.2.1
      omega
    obtain ⟨_,_,_,p,hp,hpQ⟩ := Finset.mem_filter.mp hhead
    have hplog : Real.log p ≤ δ*N := by
      have ht := Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
        (show (p : ℝ) ≤ Q by exact_mod_cast hpQ)
      exact ht.trans (log_floor_exp_le (mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) N)))
    have hδN := mul_le_mul_of_nonneg_right hδu (Nat.cast_nonneg (α := ℝ) N)
    linarith [(hsupply.2 p hp),Nat.cast_nonneg (α := ℝ) N]
  have hDsub : D ⊆ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs) := by
    intro n hn
    obtain ⟨hnB,hnnot⟩ := Finset.mem_sdiff.mp hn
    have hnS : n ∈ S := by
      rcases Finset.mem_union.mp hnB with hn | hn <;> exact (Finset.mem_filter.mp hn).1
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro h
    rcases Finset.mem_union.mp h with h | hF
    · rcases Finset.mem_union.mp h with h | hY
      · exact hnnot (Finset.mem_union_left _ h)
      · exact Finset.disjoint_left.mp hBY hnB hY
    · exact hnnot (Finset.mem_union_right _ hF)
  have hset_aux (S X Z H Y F B : Finset ℕ) :
      (S\(X ∪ Z ∪ H ∪ Y ∪ F))\(B\(X ∪ Z ∪ H ∪ F)) =
        S\(X ∪ Z ∪ H ∪ Y ∪ F ∪ B) := by
    ext n
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  have hset : (S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs))\D = S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ B) :=
    hset_aux S Xs Zs Hs Ys Fs B
  have hsum := Finset.sum_sdiff (f := f) hDsub
  rw [hset] at hsum
  have hre := congrArg Complex.re hsum
  rw [Complex.add_re] at hre
  refine ⟨v,hvb,hY,?_⟩
  change _ ≤ u^(N+1)*((∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ B), f n).re+
    min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
    min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+(∑ n ∈ Ys, f n).re/8)+_
  change _ ≤ u^(N+1)*((∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs), f n).re+
    min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
    min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+(∑ n ∈ Ys, f n).re/8) at hfloor
  rw [← hre] at hfloor
  nlinarith only [hfloor,hreal]



end
end RiemannGaussian.ZetaRieszHeadCeiling
