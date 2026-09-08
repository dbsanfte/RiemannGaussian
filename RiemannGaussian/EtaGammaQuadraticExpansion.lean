import RiemannGaussian.EtaGammaFactorTail

/-!
# Exact complete-row and gcd expansions of the gamma quadratic

The finite divisor indicator is proved first. Absolute convergence then
justifies the complete positive-multiple rows, and the finite square is
partitioned by its exact gcd. Both divided cutoffs and every original
Moebius coefficient are retained before any estimate is applied.
-/

open Complex Filter MeasureTheory Set RiemannGaussian RiemannGaussian.EtaGammaSmoothing
open RiemannGaussian.EtaGammaQuadratic
open scoped Classical Topology ArithmeticFunction.Moebius

namespace RiemannGaussian.EtaGammaGcd

noncomputable section

private theorem short_ne_zero_cutoff {U n : ℕ} (h : shortMoebius U n ≠ 0) : n ≤ U := by
  by_contra hn
  exact h (if_neg hn)

/-- The original short cofactor is exactly the finite double divisor indicator, including every coefficient. -/
theorem cofactor_short_eq_sum_dvd (U : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    cofactor (shortMoebius U) n =
      ∑ a ∈ Finset.Icc 1 U, ∑ b ∈ Finset.Icc 1 U,
        if a * b ∣ n then (μ a : ℂ) * (μ b : ℂ) else 0 := by
  rw [cofactor, ArithmeticFunction.coe_zeta_mul_apply, pow_two]
  simp_rw [ArithmeticFunction.mul_apply]
  rw [Finset.sum_sigma', ← Finset.sum_product']
  refine Finset.sum_bij_ne_zero (fun x _ _ ↦ x.2) ?_ ?_ ?_ ?_
  · intro x hx hx0
    obtain ⟨hxd, hxp⟩ := Finset.mem_sigma.mp hx
    obtain ⟨ha, hb⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hxp
    have haU := short_ne_zero_cutoff (left_ne_zero_of_mul hx0)
    have hbU := short_ne_zero_cutoff (right_ne_zero_of_mul hx0)
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero ha, haU⟩,
      Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hb, hbU⟩⟩
  · intro x hx hx0 y hy hy0 hxy
    have hxprod := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
    have hyprod := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hy).2).1
    have he : x.1 = y.1 := by rw [← hxprod, ← hyprod, hxy]
    exact Sigma.ext he (heq_of_eq hxy)
  · intro p hp hp0
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    have hdiv : p.1 * p.2 ∣ n := by
      by_contra h
      exact hp0 (if_neg h)
    have hmul : 0 < p.1 * p.2 := Nat.mul_pos (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1
    have hx : (⟨p.1 * p.2, p⟩ : Σ m : ℕ, ℕ × ℕ) ∈
        n.divisors.sigma (fun m ↦ m.divisorsAntidiagonal) :=
      Finset.mem_sigma.mpr ⟨Nat.mem_divisors.mpr ⟨hdiv, by omega⟩,
        Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hmul.ne'⟩⟩
    refine ⟨⟨p.1 * p.2, p⟩, hx, ?_, rfl⟩
    simpa only [shortMoebius, ArithmeticFunction.coe_mk, if_pos (Finset.mem_Icc.mp ha).2,
      if_pos (Finset.mem_Icc.mp hb).2, if_pos hdiv] using hp0
  · intro x hx hx0
    have hprod := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
    have hdiv : x.2.1 * x.2.2 ∣ n := by
      rw [hprod]
      exact (Nat.mem_divisors.mp (Finset.mem_sigma.mp hx).1).1
    have ha := short_ne_zero_cutoff (left_ne_zero_of_mul hx0)
    have hb := short_ne_zero_cutoff (right_ne_zero_of_mul hx0)
    simp only [shortMoebius, ArithmeticFunction.coe_mk, if_pos ha, if_pos hb, if_pos hdiv]

/-- The complete infinite zeta cofactor of one positive product. -/
def gammaRow (rho : NontrivialZetaZero) (A : ℝ) (m : ℕ) : ℂ :=
  ∑' k : ℕ, gammaCarrier rho A (m * (k + 1))

/-- The full smooth carrier is absolutely summable before any arithmetic reindexing. -/
theorem summable_norm_gammaCarrier (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A) :
    Summable (fun n : ℕ ↦ ‖gammaCarrier rho A n‖) := by
  have h1 (n : ℕ) : ‖(1 : ArithmeticFunction ℂ) n‖ ≤ 1 := by
    rw [ArithmeticFunction.one_apply]
    split_ifs <;> simp
  have hs := summable_norm_cofactor_gamma rho hA 1 h1
  apply (summable_nat_add_iff 1).mp
  simpa [cofactor] using hs

/-- Every positive-product cofactor row is absolutely summable. -/
theorem summable_norm_gammaRow (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    {m : ℕ} (hm : 1 ≤ m) :
    Summable (fun k : ℕ ↦ ‖gammaCarrier rho A (m * (k + 1))‖) := by
  apply (summable_norm_gammaCarrier rho hA).comp_injective
  intro a b hab
  dsimp only at hab
  have h := Nat.eq_of_mul_eq_mul_left hm hab
  omega

/-- Divisibility selects exactly the complete positive-multiple row, with the rearrangement justified. -/
theorem hasSum_dvd_gammaRow (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    {m : ℕ} (hm : 1 ≤ m) :
    HasSum (fun n : ℕ ↦ if m ∣ n + 1 then gammaCarrier rho A (n + 1) else 0)
      (gammaRow rho A m) := by
  let f : ℕ → ℂ := fun n ↦ if m ∣ n + 1 then gammaCarrier rho A (n + 1) else 0
  have hi : Function.Injective (fun k : ℕ ↦ m * (k + 1) - 1) := by
    intro a b hab
    have ha : 1 ≤ m * (a + 1) := Nat.mul_pos hm (by omega)
    have hb : 1 ≤ m * (b + 1) := Nat.mul_pos hm (by omega)
    have he : m * (a + 1) = m * (b + 1) := by dsimp only at hab; omega
    have h := Nat.eq_of_mul_eq_mul_left hm he
    omega
  have hz (n : ℕ) (hn : n ∉ Set.range (fun k : ℕ ↦ m * (k + 1) - 1)) : f n = 0 := by
    apply if_neg
    rintro ⟨k, hk⟩
    have hkpos : 1 ≤ k := by
      by_contra h
      have he : k = 0 := by omega
      simp [he] at hk
    apply hn
    refine ⟨k - 1, ?_⟩
    dsimp only
    rw [Nat.sub_add_cancel hkpos, ← hk]
    omega
  apply (hi.hasSum_iff hz).mp
  convert! (summable_norm_gammaRow rho hA hm).of_norm.hasSum using 1
  ext k
  have hk : 1 ≤ m * (k + 1) := Nat.mul_pos hm (by omega)
  simp only [Function.comp_apply, f, Nat.sub_add_cancel hk, dvd_mul_right, if_true]

/-- The full original quadratic is the exact finite Moebius square of complete infinite cofactor rows. -/
theorem smoothQuadratic_eq_sum_gammaRow (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (U : ℕ) :
    smoothQuadratic rho A U =
      -(∑ a ∈ Finset.Icc 1 U, ∑ b ∈ Finset.Icc 1 U,
        (μ a : ℂ) * (μ b : ℂ) * gammaRow rho A (a * b)) := by
  have hs := hasSum_sum (s := Finset.Icc 1 U) (fun a ha ↦
    hasSum_sum (s := Finset.Icc 1 U) (fun b hb ↦
      (hasSum_dvd_gammaRow rho hA (Nat.mul_pos (Finset.mem_Icc.mp ha).1
        (Finset.mem_Icc.mp hb).1)).mul_left ((μ a : ℂ) * (μ b : ℂ))))
  have he (n : ℕ) : cofactor (shortMoebius U) (n + 1) * gammaCarrier rho A (n + 1) =
      ∑ a ∈ Finset.Icc 1 U, ∑ b ∈ Finset.Icc 1 U,
        ((μ a : ℂ) * (μ b : ℂ)) *
          (if a * b ∣ n + 1 then gammaCarrier rho A (n + 1) else 0) := by
    rw [cofactor_short_eq_sum_dvd U (by omega)]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    split_ifs <;> simp
  simp_rw [← he] at hs
  exact congrArg Neg.neg hs.tsum_eq

/-- The complete finite square is partitioned by its exact gcd, with both divided cutoffs and coprimality retained. -/
theorem sum_square_eq_sum_gcd (U : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ a ∈ Finset.Icc 1 U, ∑ b ∈ Finset.Icc 1 U, F a b) =
      ∑ g ∈ Finset.Icc 1 U, ∑ r ∈ Finset.Icc 1 (U / g), ∑ s ∈ Finset.Icc 1 (U / g),
        if r.Coprime s then F (g * r) (g * s) else 0 := by
  let S := (Finset.Icc 1 U).product (Finset.Icc 1 U)
  have hmap (p : ℕ × ℕ) (hp : p ∈ S) : p.1.gcd p.2 ∈ Finset.Icc 1 U := by
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    have ha1 := (Finset.mem_Icc.mp ha).1
    exact Finset.mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left _ ha1,
      (Nat.le_of_dvd ha1 (Nat.gcd_dvd_left _ _)).trans (Finset.mem_Icc.mp ha).2⟩
  calc
    _ = ∑ p ∈ S, F p.1 p.2 := (Finset.sum_product' _ _ F).symm
    _ = ∑ g ∈ Finset.Icc 1 U, ∑ p ∈ S with p.1.gcd p.2 = g, F p.1 p.2 :=
      (Finset.sum_fiberwise_of_maps_to hmap (fun p ↦ F p.1 p.2)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g hg
      have hgp : 0 < g := (Finset.mem_Icc.mp hg).1
      symm
      rw [← Finset.sum_product', ← Finset.sum_filter]
      refine Finset.sum_bij (fun p _ ↦ (g * p.1, g * p.2)) ?_ ?_ ?_ ?_
      · intro p hp
        obtain ⟨hp, hc⟩ := Finset.mem_filter.mp hp
        obtain ⟨hr, hs⟩ := Finset.mem_product.mp hp
        have hr1 := (Finset.mem_Icc.mp hr).1
        have hs1 := (Finset.mem_Icc.mp hs).1
        have hrU := (Nat.le_div_iff_mul_le hgp).mp (Finset.mem_Icc.mp hr).2
        have hsU := (Nat.le_div_iff_mul_le hgp).mp (Finset.mem_Icc.mp hs).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hgp hr1, by simpa [mul_comm] using hrU⟩,
           Finset.mem_Icc.mpr ⟨Nat.mul_pos hgp hs1, by simpa [mul_comm] using hsU⟩⟩,
          by simp only [Nat.gcd_mul_left, hc.gcd_eq_one, mul_one]⟩
      · intro p hp q hq he
        exact Prod.ext (Nat.eq_of_mul_eq_mul_left hgp (congrArg Prod.fst he))
          (Nat.eq_of_mul_eq_mul_left hgp (congrArg Prod.snd he))
      · intro p hp
        obtain ⟨hp, hc⟩ := Finset.mem_filter.mp hp
        obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
        have hga : g ∣ p.1 := hc ▸ Nat.gcd_dvd_left p.1 p.2
        have hgb : g ∣ p.2 := hc ▸ Nat.gcd_dvd_right p.1 p.2
        have ha1 := (Finset.mem_Icc.mp ha).1
        have hb1 := (Finset.mem_Icc.mp hb).1
        refine ⟨(p.1 / g, p.2 / g), Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
        · exact Finset.mem_product.mpr
            ⟨Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd ha1 hga) hgp,
              Nat.div_le_div_right (Finset.mem_Icc.mp ha).2⟩,
             Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hb1 hgb) hgp,
              Nat.div_le_div_right (Finset.mem_Icc.mp hb).2⟩⟩
        · simpa only [hc] using Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left p.2 ha1)
        · exact Prod.ext (Nat.mul_div_cancel' hga) (Nat.mul_div_cancel' hgb)
      · intro p hp
        rfl


/-- The exact common-factor coefficient keeps its squarefree weight and both coprimality exclusions. -/
theorem moebius_common_factor (g r s : ℕ) :
    (μ (g * r) : ℂ) * (μ (g * s) : ℂ) =
      if g.Coprime r ∧ g.Coprime s then (μ g : ℂ) ^ 2 * ((μ r : ℂ) * (μ s : ℂ)) else 0 := by
  by_cases hgr : g.Coprime r
  · by_cases hgs : g.Coprime s
    · rw [if_pos ⟨hgr, hgs⟩, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hgr,
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hgs]
      push_cast
      ring
    · have hs : ¬ Squarefree (g * s) := fun h ↦ hgs (Nat.coprime_of_squarefree_mul h)
      rw [if_neg (by tauto), ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
      simp
  · have hr : ¬ Squarefree (g * r) := fun h ↦ hgr (Nat.coprime_of_squarefree_mul h)
    rw [if_neg (by tauto), ArithmeticFunction.moebius_eq_zero_of_not_squarefree hr]
    simp

/-- At a supported squarefree common factor, only the two reduced Moebius signs remain. -/
theorem moebius_common_factor_of_squarefree {g r s : ℕ} (hg : Squarefree g)
    (hgr : g.Coprime r) (hgs : g.Coprime s) :
    (μ (g * r) : ℂ) * (μ (g * s) : ℂ) = (μ r : ℂ) * (μ s : ℂ) := by
  rw [moebius_common_factor, if_pos ⟨hgr, hgs⟩]
  have hm : (μ g : ℂ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hg
  rw [hm, one_mul]

/-- Scaling the product by a positive square preserves its full complex phase and rescales the physical kernel exactly. -/
theorem gammaCarrier_square_scale (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    {g : ℕ} (hg : 1 ≤ g) (n : ℕ) :
    gammaCarrier rho A (g ^ 2 * n) =
      (g : ℂ) ^ (-2 * rho.1) * gammaCarrier rho (A / (g : ℝ) ^ 2) n := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have he : ((g ^ 2 * n : ℕ) : ℝ) / A = (n : ℝ) / (A / (g : ℝ) ^ 2) := by
    push_cast
    field_simp
  unfold gammaCarrier
  rw [he, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul]
  rw [show (2 : ℕ) * (-rho.1) = -2 * rho.1 by push_cast; ring]
  ring

/-- The entire infinite row has the exact common-square complex factor; no reduced row is replaced by a norm. -/
theorem gammaRow_square_scale (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    {g : ℕ} (hg : 1 ≤ g) (m : ℕ) :
    gammaRow rho A (g ^ 2 * m) =
      (g : ℂ) ^ (-2 * rho.1) * gammaRow rho (A / (g : ℝ) ^ 2) m := by
  unfold gammaRow
  simp_rw [mul_assoc (g ^ 2), gammaCarrier_square_scale rho hA hg]
  exact tsum_mul_left


end

end RiemannGaussian.EtaGammaGcd
