import RiemannGaussian.EtaMoebiusOriginalQuadraticFamily
import RiemannGaussian.EtaLogColourPrimitive

/-!
# The actual moving center and physical divisor endpoint

The center is the logarithm of the original next integer cutoff. Its
translated divisor coordinate stays within a controlled displacement of
the literal odd endpoint. Both complex normalization powers are retained,
and their ratio is bounded on the full physical divisor range.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- Two positive logarithmic endpoints have an explicit displacement
bound in their common positive lower scale. -/
theorem abs_log_sub_log_le_above {a x y : ℝ} (ha : 0 < a) (hax : a ≤ x) (hay : a ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / a := by
  have hx : 0 < x := ha.trans_le hax
  have hy : 0 < y := ha.trans_le hay
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hx hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    have h := log_add_sub_log_le_div hx (sub_nonneg.mpr hxy)
    rw [add_sub_cancel] at h
    calc
      _ = Real.log y - Real.log x := by ring
      _ ≤ (y - x) / x := h
      _ ≤ (y - x) / a := div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) ha hax
      _ = _ := by ring
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    have h := log_add_sub_log_le_div hy (sub_nonneg.mpr hyx)
    rw [add_sub_cancel] at h
    exact h.trans (div_le_div_of_nonneg_left (sub_nonneg.mpr hyx) ha hay)

/-- The actual moment center displacement at its literal divided odd endpoint. -/
def pairedEtaMomentDivisorCenterDisplacement (M d : ℕ) : ℝ :=
  Real.log (pairedEtaUnpairedOddEndpoint (M / d) : ℝ) -
    (Real.log (M + 1 : ℝ) - Real.log d)

/-- The translated divisor center is exactly the logarithmic displacement
of the full physical endpoint from the next original cutoff. -/
theorem pairedEtaMomentDivisorCenterDisplacement_eq {d : ℕ} (hd : 0 < d) (M : ℕ) :
    pairedEtaMomentDivisorCenterDisplacement M d =
      Real.log (d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) - Real.log (M + 1 : ℝ) := by
  have hq := (pairedEtaUnpairedOddEndpoint_bounds (M / d)).1
  unfold pairedEtaMomentDivisorCenterDisplacement
  rw [Nat.cast_mul, Real.log_mul (by positivity : (d : ℝ) ≠ 0)
    (by positivity : (pairedEtaUnpairedOddEndpoint (M / d) : ℝ) ≠ 0)]
  ring

/-- The original moving center has displacement at most `4d/M` for
every physical divisor, including the largest divided cutoffs. -/
theorem abs_pairedEtaMomentDivisorCenterDisplacement_le {M d : ℕ}
    (hd : d ∈ Finset.Icc 1 M) :
    |pairedEtaMomentDivisorCenterDisplacement M d| ≤ 4 * (d : ℝ) / M := by
  have hdp : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hM : 1 ≤ M := hdp.trans (Finset.mem_Icc.mp hd).2
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hdp
  have hb := pairedEtaDivisorOddEndpoint_physical_bounds hd
  have he : |(d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) - (M + 1 : ℝ)| ≤ 2 * d := by
    calc
      _ = |((d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) - (M : ℝ)) - 1| := by congr 1; ring
      _ ≤ |(d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) - (M : ℝ)| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ (d : ℝ) + 1 := by
        rw [abs_sub_comm, abs_one]
        exact add_le_add hb.2 le_rfl
      _ ≤ 2 * d := by linarith
  rw [pairedEtaMomentDivisorCenterDisplacement_eq hdp]
  apply (abs_log_sub_log_le_above (by positivity : (0 : ℝ) < (M : ℝ) / 2)
    hb.1 (by linarith : (M : ℝ) / 2 ≤ M + 1)).trans
  calc
    _ ≤ (2 * (d : ℝ)) / ((M : ℝ) / 2) :=
      div_le_div_of_nonneg_right he (by positivity)
    _ = _ := by field_simp; ring

/-- All actual divisor center displacements lie in one fixed radius. -/
theorem abs_pairedEtaMomentDivisorCenterDisplacement_le_four {M d : ℕ}
    (hd : d ∈ Finset.Icc 1 M) : |pairedEtaMomentDivisorCenterDisplacement M d| ≤ 4 := by
  have hM : (0 : ℝ) < M := by
    exact_mod_cast (Finset.mem_Icc.mp hd).1.trans (Finset.mem_Icc.mp hd).2
  apply (abs_pairedEtaMomentDivisorCenterDisplacement_le hd).trans
  apply (div_le_iff₀ hM).mpr
  have hh : (d : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hd).2
  nlinarith

/-- Every center between the two original logarithmic endpoints has
the same explicit divisor displacement bound. -/
theorem abs_log_divisor_endpoint_sub_center_le {M d : ℕ} (hd : d ∈ Finset.Icc 1 M)
    {a : ℝ} (ha : Real.log (M : ℝ) ≤ a ∧ a ≤ Real.log (M + 1 : ℝ)) :
    |Real.log (pairedEtaUnpairedOddEndpoint (M / d) : ℝ) - (a - Real.log d)| ≤
      4 * (d : ℝ) / M := by
  have hdp := (Finset.mem_Icc.mp hd).1
  have hMR : (0 : ℝ) < M := by exact_mod_cast hdp.trans (Finset.mem_Icc.mp hd).2
  have hb := pairedEtaDivisorOddEndpoint_physical_bounds hd
  have hl : |Real.log (d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) - Real.log (M : ℝ)| ≤
      2 * (d : ℝ) / M := by
    apply (abs_log_sub_log_le_above (by positivity : (0 : ℝ) < (M : ℝ) / 2)
      hb.1 (by linarith : (M : ℝ) / 2 ≤ M)).trans
    have hh : |(d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) - (M : ℝ)| ≤ d := by
      rw [abs_sub_comm]
      exact hb.2
    apply (div_le_div_of_nonneg_right hh (by positivity : (0 : ℝ) ≤ (M : ℝ) / 2)).trans_eq
    field_simp
  have hu := abs_pairedEtaMomentDivisorCenterDisplacement_le hd
  rw [pairedEtaMomentDivisorCenterDisplacement_eq hdp] at hu
  have heq : Real.log (pairedEtaUnpairedOddEndpoint (M / d) : ℝ) - (a - Real.log d) =
      Real.log (d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) - a := by
    have hq := (pairedEtaUnpairedOddEndpoint_bounds (M / d)).1
    rw [Nat.cast_mul, Real.log_mul (by positivity : (d : ℝ) ≠ 0)
      (by positivity : (pairedEtaUnpairedOddEndpoint (M / d) : ℝ) ≠ 0)]
    ring
  rw [heq]
  obtain ⟨hlo, hhi⟩ := abs_le.mp hl
  obtain ⟨huo, hui⟩ := abs_le.mp hu
  apply abs_le.mpr
  constructor
  · linarith [ha.2]
  · apply (show Real.log (d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) - a ≤
      2 * (d : ℝ) / M by linarith [ha.1]).trans
    exact div_le_div_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α := ℝ) d]) hMR.le

/-- Every translated center in the original inverse formula lies between
the logarithms of its divided cutoff and the next integer. -/
theorem pairedEtaMomentInverseCenter_mem_interval {M d : ℕ} (hd : d ∈ Finset.Icc 1 M) :
    Real.log (M / d : ℕ) ≤ Real.log (M + 1 : ℝ) - Real.log d ∧
      Real.log (M + 1 : ℝ) - Real.log d ≤ Real.log ((M / d : ℕ) + 1 : ℝ) := by
  have hdp := (Finset.mem_Icc.mp hd).1
  have hdM := (Finset.mem_Icc.mp hd).2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdp
  have hq : 1 ≤ M / d := (Nat.le_div_iff_mul_le hdp).mpr (by simpa only [one_mul] using hdM)
  have hqR : (0 : ℝ) < (M / d : ℕ) := by exact_mod_cast hq
  have hrem := Nat.mod_lt M hdp
  have hsplit := Nat.div_add_mod M d
  have hlo : ((M / d : ℕ) : ℝ) ≤ (M + 1 : ℝ) / d := by
    apply (le_div_iff₀ hdR).mpr
    have h := Nat.mul_div_le M d
    have hc : ((d * (M / d) : ℕ) : ℝ) ≤ M := by exact_mod_cast h
    push_cast at hc
    nlinarith
  have hhi : (M + 1 : ℝ) / d ≤ ((M / d : ℕ) : ℝ) + 1 := by
    apply (div_le_iff₀ hdR).mpr
    have hnat : M + 1 ≤ d * (M / d + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hc : ((M + 1 : ℕ) : ℝ) ≤ (d * (M / d + 1) : ℕ) := by exact_mod_cast hnat
    push_cast at hc
    nlinarith
  rw [← Real.log_div (by positivity : (M + 1 : ℝ) ≠ 0) hdR.ne']
  exact ⟨Real.log_le_log hqR hlo, Real.log_le_log (by positivity) hhi⟩

/-- The exact ratio between the common and individual complex powers. -/
def pairedEtaMomentPhysicalRatio (rho : NontrivialZetaZero) (M d : ℕ) : ℂ :=
  (M : ℂ) ^ rho.1 * (((d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) : ℂ) ^ rho.1)⁻¹

/-- The physical ratio cancels only the matching individual complex
endpoint power, retaining every other coefficient of the actual carrier. -/
theorem pairedEtaMomentPhysicalRatio_cancel (rho : NontrivialZetaZero) {M d : ℕ}
    (hd : d ∈ Finset.Icc 1 M) (z : ℂ) :
    pairedEtaMomentPhysicalRatio rho M d *
      (((d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) : ℂ) ^ rho.1 * z) = (M : ℂ) ^ rho.1 * z := by
  have hdp := (Finset.mem_Icc.mp hd).1
  have hq := (pairedEtaUnpairedOddEndpoint_bounds (M / d)).1
  have hp : (((d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) : ℂ) ^ rho.1) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (Nat.mul_pos hdp hq).ne'))
  unfold pairedEtaMomentPhysicalRatio
  field_simp

/-- The full physical divisor range bounds the normalization ratio by
two, using the actual zero coordinate in the open critical strip. -/
theorem norm_pairedEtaMomentPhysicalRatio_le (rho : NontrivialZetaZero) {M d : ℕ}
    (hd : d ∈ Finset.Icc 1 M) : ‖pairedEtaMomentPhysicalRatio rho M d‖ ≤ 2 := by
  have hMR : (0 : ℝ) < M := by
    exact_mod_cast (Finset.mem_Icc.mp hd).1.trans (Finset.mem_Icc.mp hd).2
  have hb := (pairedEtaDivisorOddEndpoint_physical_bounds hd).1
  have hpR : (0 : ℝ) < (d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) := by linarith
  have hn (n : ℕ) (hnp : (0 : ℝ) < n) : ‖(n : ℂ) ^ rho.1‖ = (n : ℝ) ^ rho.1.re := by
    simpa only [Complex.ofReal_natCast] using Complex.norm_cpow_eq_rpow_re_of_pos hnp rho.1
  unfold pairedEtaMomentPhysicalRatio
  rw [norm_mul, norm_inv, hn M hMR, hn _ hpR, ← div_eq_mul_inv,
    ← Real.div_rpow hMR.le hpR.le]
  have hratio : (M : ℝ) / (d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) ≤ 2 :=
    (div_le_iff₀ hpR).mpr (by linarith)
  apply (Real.rpow_le_rpow (by positivity) hratio (NontrivialZetaZero.zero_lt_re rho).le).trans
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 2) (NontrivialZetaZero.re_lt_one rho).le

end

end RiemannGaussian
