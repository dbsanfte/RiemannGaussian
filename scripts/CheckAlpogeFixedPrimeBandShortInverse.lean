import CheckAlpogeFixedPrimeBandCorner
import CheckAlpogeFixedPrimeBandMoments

/-! # The fourth-power sample from Möbius values through its fourth root -/

namespace RiemannGaussian.AlpogeMined
open Finset Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- One Newton step for the inverse of the constant-one arithmetic function.
Products here are Dirichlet convolutions. -/
def fixedBandInverseStep {R : Type*} [CommRing R] (f : ArithmeticFunction R) : ArithmeticFunction R :=
  f+f-f*f*ζ

/-- An inverse correct through U becomes correct through U². -/
theorem fixedBandInverseStep_exact {R : Type*} [CommRing R] {f : ArithmeticFunction R} {U : ℕ}
    (hf : ∀ j ≤ U, f j = (μ j : R)) {j : ℕ} (hj : j ≤ U^2) :
    fixedBandInverseStep f j = (μ j : R) := by
  let m : ArithmeticFunction R := μ
  have he : m-fixedBandInverseStep f=(m-f)*(m-f)*(ζ : ArithmeticFunction R) := by
    have hm : m*(ζ : ArithmeticFunction R)=1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
    calc
      _ = m*(m*ζ)-f*(m*ζ)-f*(m*ζ)+f*f*ζ := by rw [hm]; dsimp only [fixedBandInverseStep]; ring
      _ = _ := by ring
  have hs {q : ℕ} (hq : q ≤ U^2) : ((m-f)*(m-f)) q = 0 := by
    rw [ArithmeticFunction.mul_apply]
    apply sum_eq_zero
    intro p hp
    obtain ⟨hab,_⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    simp only [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply]
    by_cases ha : p.1 ≤ U
    · rw [hf _ ha]; simp [m]
    · have hb : p.2 ≤ U := by
        by_contra! h
        have hh := Nat.mul_lt_mul_of_lt_of_lt (lt_of_not_ge ha) h
        rw [hab,← pow_two] at hh
        omega
      rw [hf _ hb]; simp [m]
  have hz : (m-fixedBandInverseStep f) j=0 := by
    rw [he,ArithmeticFunction.mul_apply]
    apply sum_eq_zero
    intro p hp
    obtain ⟨hab,hn⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hdiv : p.1 ∣ j := ⟨p.2,hab.symm⟩
    rw [hs ((Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv).trans hj),zero_mul]
  simp only [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply] at hz
  rw [← sub_eq_add_neg] at hz
  exact (sub_eq_zero.mp hz).symm

private def inverseHead {R : Type*} [Zero R] (s : ℕ) (f : ArithmeticFunction R) :
    ArithmeticFunction R where
  toFun k := if k ≤ s then f k else 0
  map_zero' := by simp

/-- A quartic expression for a quadratic form truncated at any square s². -/
noncomputable def fixedBandQuarticAt (N s : ℕ) : ℝ :=
  let f := fixedBandInverseStep (inverseHead s (μ : ArithmeticFunction ℝ))
  ∑ a ∈ Ioc 0 (s^2), ∑ b ∈ Ioc 0 (s^2), f a*f b*fixedBandProductEntry N a b

theorem fixedBandQuarticAt_eq (N s : ℕ) :
    fixedBandQuarticAt N s = fixedBandQuadratic N (s^2) := by
  have hf {j : ℕ} (hj : j ≤ s^2) :
      fixedBandInverseStep (inverseHead s (μ : ArithmeticFunction ℝ)) j = (μ j : ℝ) :=
    fixedBandInverseStep_exact (U := s) (fun d hd => by simp [inverseHead,hd]) hj
  exact sum_congr rfl fun a ha => sum_congr rfl fun b hb => by rw [hf (mem_Ioc.mp ha).2,hf (mem_Ioc.mp hb).2]

/-- Both factors are evaluated from the same finite list through n. -/
noncomputable def fixedBandShortQuadratic (n : ℕ) : ℝ := fixedBandQuarticAt (n^4) n

theorem fixedBandShortQuadratic_eq (n : ℕ) :
    fixedBandShortQuadratic n = fixedBandQuadratic (n^4) (n^2) := fixedBandQuarticAt_eq _ _

/-- Only the inputs through the shorter root occur in the trimmed window. -/
theorem fixedBandQuarticAt_trimmed_mass (m b : ℕ) :
    (∑ n ∈ Icc m b, max (-fixedBandQuarticAt (n^4) (fixedBandShortRoot n)) 0/(n:ℝ)^3) =
      fixedBandTrimmedMass m b := by
  simp only [fixedBandQuarticAt_eq,fixedBandTrimmedMass]

/-- The negative-part mass is unchanged even on individual finite windows. -/
theorem fixedBandShortQuadratic_mass (m b : ℕ) :
    (∑ n ∈ Icc m b, max (-fixedBandShortQuadratic n) 0/(n:ℝ)^3) = fixedBandQuadraticMass m b := by
  simp only [fixedBandShortQuadratic_eq,fixedBandQuadraticMass]

/-- The quartic calculation supplies the window criterion with no error. -/
theorem rh_of_fixedBandShortQuadratic_powerWindows
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ A : ℕ, ∃ m ≥ A,
      (∑ n ∈ Icc m ⌈(m:ℝ)^(1+δ)⌉₊, max (-fixedBandShortQuadratic n) 0/(n:ℝ)^3) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply rh_of_fixedBandQuadraticMass_powerWindows
  simpa only [fixedBandShortQuadratic_mass] using h

/-- Each entry uses the multiples of ab with their exact rational weights. -/
def fixedBandRationalProductEntry (n a b : ℕ) : ℚ :=
  ∑ j ∈ Ioc 0 (n^4/(a*b)), fixedBandRationalWeight n (a*b*j)

private theorem rationalProductEntry_eq {n a b : ℕ} (hpos : 0 < a*b) :
    fixedBandRationalProductEntry n a b =
      ∑ k ∈ Ioc 0 (n^4), if a*b ∣ k then fixedBandRationalWeight n k else 0 := by
  rw [← sum_filter]
  unfold fixedBandRationalProductEntry
  apply sum_bij (fun j _ => a*b*j)
  · intro j hj
    obtain ⟨h₁,h₂⟩ := mem_Ioc.mp hj
    have htop : a*b*j ≤ n^4 := by
      simpa only [Nat.mul_comm j] using (Nat.le_div_iff_mul_le hpos).mp h₂
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.mul_pos hpos h₁,htop⟩,dvd_mul_right _ _⟩
  · exact fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hpos h
  · intro k hk
    obtain ⟨hk,hd⟩ := mem_filter.mp hk
    obtain ⟨j,rfl⟩ := hd
    have hj : 0 < j := by
      by_contra! h
      have he : j=0 := by omega
      simp [he] at hk
    exact ⟨j,mem_Ioc.mpr ⟨hj,(Nat.le_div_iff_mul_le hpos).mpr (by
      simpa only [Nat.mul_comm j] using (mem_Ioc.mp hk).2)⟩,rfl⟩
  · exact fun _ _ => rfl

/-- Rational quadratic form on a specified arithmetic input vector. -/
def fixedBandRationalQuadraticAt (n V : ℕ) (f : ArithmeticFunction ℚ) : ℚ :=
  ∑ a ∈ Ioc 0 V, ∑ b ∈ Ioc 0 V, f a*f b*fixedBandRationalProductEntry n a b

/-- Double inversion pays for the rational weights with a square-root error,
even though each multiple can occur in many entries. -/
theorem fixedBandRationalQuadratic_error {n V : ℕ} (hn : 2 ≤ n)
    (hV : V^2 ≤ n^4) (hN : n^4 ≤ 2*V^2) :
    |fixedBandQuadratic (n^4) V-(fixedBandRationalQuadraticAt n V μ:ℝ)| ≤ 48*(n:ℝ)^2 := by
  let e (k : ℕ) :=
    fixedBandCenteredKernel (((n^4:ℕ):ℝ)/k)-(fixedBandRationalWeight n k:ℝ)
  have he : fixedBandQuadratic (n^4) V-(fixedBandRationalQuadraticAt n V μ:ℝ) =
      ∑ a ∈ Ioc 0 V, ∑ b ∈ Ioc 0 V, ((μ a:ℝ)*(μ b:ℝ))*
        (∑ k ∈ Ioc 0 (n^4), if a*b ∣ k then e k else 0) := by
    simp only [fixedBandQuadratic,fixedBandRationalQuadraticAt,Rat.cast_sum,Rat.cast_mul,
      ← sum_sub_distrib]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    have hab := Nat.mul_pos (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1
    rw [rationalProductEntry_eq hab,fixedBandProductEntry,Rat.cast_sum]
    simp only [ArithmeticFunction.intCoe_apply,Rat.cast_intCast,← mul_sub,← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro k _
    split_ifs <;> simp [e]
  rw [he]
  have hh := fixedBand_weighted_quadratic_abs_le hV hN (by positivity : 0 ≤ 12/(n:ℝ)^2)
    (fun _ hk => fixedBandRationalWeight_error hn hk)
  refine hh.trans_eq ?_
  have hn₀ : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  rw [Nat.cast_pow]
  field_simp [hn₀.ne']
  ring

/-- A single inverse step supplies both quadratic factors using the input
values through s. -/
def fixedBandRationalQuarticAt (n s : ℕ) (f : ArithmeticFunction ℚ) : ℚ :=
  fixedBandRationalQuadraticAt n (s^2) (fixedBandInverseStep (inverseHead s f))

theorem fixedBandRationalQuarticAt_eq (n s : ℕ) :
    fixedBandRationalQuarticAt n s μ = fixedBandRationalQuadraticAt n (s^2) μ := by
  have he {k : ℕ} (hk : k ≤ s^2) :
      fixedBandInverseStep (inverseHead s (μ : ArithmeticFunction ℚ)) k = (μ k:ℚ) :=
    fixedBandInverseStep_exact (U := s) (fun j hj => by simp [inverseHead,hj]) hk
  unfold fixedBandRationalQuarticAt fixedBandRationalQuadraticAt
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  rw [he (mem_Ioc.mp ha).2,he (mem_Ioc.mp hb).2]
  rfl

theorem fixedBandRationalQuarticAt_congr {n s : ℕ} {f g : ArithmeticFunction ℚ}
    (h : ∀ k ≤ s, f k = g k) : fixedBandRationalQuarticAt n s f = fixedBandRationalQuarticAt n s g := by
  have he : inverseHead s f = inverseHead s g := by
    ext k
    change (if k ≤ s then f k else 0) = if k ≤ s then g k else 0
    split_ifs with hk
    · exact h k hk
    · rfl
  rw [fixedBandRationalQuarticAt,fixedBandRationalQuarticAt,he]

/-- Negative-part window mass using the shortened rational quartic. -/
def fixedBandShortRationalMass (m b : ℕ) : ℚ :=
  ∑ n ∈ Icc m b, max (-fixedBandRationalQuarticAt n (fixedBandShortRoot n) μ) 0/(n:ℚ)^3

theorem fixedBandShortRationalMass_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m b : ℕ}, 2 ≤ m →
      |fixedBandMass m b-(fixedBandShortRationalMass m b:ℝ)| ≤ C*(1+log b) := by
  obtain ⟨C,hC,h⟩ := fixedBand_prime_shortRoot_error
  refine ⟨C+48,by positivity,fun {m b} hm => ?_⟩
  have he {n : ℕ} (hn : 2 ≤ n) :
      |dyadicPrimeDeficit ((n:ℝ)^4)-(-(fixedBandRationalQuarticAt n (fixedBandShortRoot n) μ:ℝ))| ≤
        (C+48)*(n:ℝ)^2 := by
    let V := (fixedBandShortRoot n)^2
    obtain ⟨hV,hN⟩ := fixedBandShortRoot_square_bounds n
    have hd := fixedBandRationalQuadratic_error hn hV hN
    rw [fixedBandRationalQuarticAt_eq,sub_neg_eq_add]
    have hsplit : dyadicPrimeDeficit ((n:ℝ)^4)+(fixedBandRationalQuadraticAt n V μ:ℝ) =
        (dyadicPrimeDeficit ((n:ℝ)^4)+fixedBandQuadratic (n^4) V)+
          ((fixedBandRationalQuadraticAt n V μ:ℝ)-fixedBandQuadratic (n^4) V) := by ring
    rw [hsplit]
    apply (abs_add_le _ _).trans
    rw [abs_sub_comm (fixedBandRationalQuadraticAt n V μ:ℝ)]
    exact (add_le_add (h hn) hd).trans_eq (by ring)
  simpa only [fixedBandMass,fixedBandSample,fixedBandShortRationalMass,Rat.cast_sum,Rat.cast_div,
    Rat.cast_max,Rat.cast_neg,Rat.cast_zero,Rat.cast_pow,Rat.cast_natCast] using
      (fixedBand_mass_sqrt_error (C := C+48) (by positivity) he (b := b) hm)

/-- The short-input rational condition is equivalent to the existing rational test. -/
theorem fixedBandShortRationalWindowBound_iff :
    fixedBandIntegerWindowBound fixedBandShortRationalMass ↔ fixedBandRationalWindowBound :=
  (fixedBandIntegerWindowBound_iff_prime _ fixedBandShortRationalMass_error).trans
    (fixedBandIntegerWindowBound_iff_prime _ fixedBandRationalMass_error).symm

theorem rh_of_fixedBandShortRationalWindowBound
    (h : fixedBandIntegerWindowBound fixedBandShortRationalMass) : RiemannHypothesis :=
  rh_of_fixedBandMass_log_squareWindows
    ((fixedBandIntegerWindowBound_iff_prime _ fixedBandShortRationalMass_error).mp h)

end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.fixedBandInverseStep_exact,
      ``RiemannGaussian.AlpogeMined.fixedBandShortQuadratic_eq,
      ``RiemannGaussian.AlpogeMined.fixedBandQuarticAt_trimmed_mass,
      ``RiemannGaussian.AlpogeMined.fixedBandRationalQuadratic_error,
      ``RiemannGaussian.AlpogeMined.fixedBandRationalQuarticAt_congr,
      ``RiemannGaussian.AlpogeMined.fixedBandShortRationalWindowBound_iff,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandShortRationalWindowBound,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandShortQuadratic_powerWindows] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
  let imports := (← getEnv).header.moduleNames
  logInfo m!"Short-input rational implication uses {imports.size + 1} Lean modules including this module."
