import RiemannGaussian.FirstDerivativeTest
import RiemannGaussian.FiniteAbelVariation
import RiemannGaussian.PhaseConjugation
import RiemannGaussian.ZetaVaughanReduction
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Reciprocal exponential sums in the ordinary-prime cofactor range

The frequency is in radians. Every column may have its own interval of
integers, allowing both ends of the product window to be retained. -/

namespace RiemannGaussian.SuzukiReciprocal
noncomputable section
open PhaseIncrementInverse
open scoped ComplexConjugate

/-- First-derivative cancellation for a reciprocal phase on an arbitrary
subinterval of a dyadic interval. -/
theorem block {M A a : ℝ} {L : ℕ} (hM : 0 < M) (hA : 0 < A) (hsmall : A ≤ M^2)
    (ha : M ≤ a) (hb : a + L ≤ 2*M) :
    ‖∑ j ∈ Finset.range L, rotation (-A / (a+j))‖ ≤ 8*Real.pi*M^2/A := by
  let η := A / (2*M)^2
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (2*M)^2)).mpr
    nlinarith [sq_nonneg M]
  have hh := FirstDerivativeTest.bound (fun x => -A/x) (fun x => A/x^2) a L hη
  have hd (x : ℝ) (hx : x ∈ Set.Icc a (a+L)) : HasDerivAt (fun y : ℝ => -A/y) (A/x^2) x := by
    have hx0 := hM.trans_le (ha.trans hx.1)
    simpa only [Pi.div_def, id_eq, zero_mul, mul_one, zero_sub, neg_neg] using
      (hasDerivAt_const x (-A)).div (hasDerivAt_id x) hx0.ne'
  have hm : AntitoneOn (fun x : ℝ => A/x^2) (Set.Icc M (2*M)) := by
    intro x hx y _ hxy
    exact div_le_div_of_nonneg_left hA.le (sq_pos_of_pos (hM.trans_le hx.1))
      (by nlinarith [sq_le_sq' (by linarith [hx.1]) hxy])
  have hsub : Set.Icc a (a+L) ⊆ Set.Icc M (2*M) := fun x hx => ⟨ha.trans hx.1,hx.2.trans hb⟩
  have hends : M ∈ Set.Icc M (2*M) ∧ 2*M ∈ Set.Icc M (2*M) := by
    constructor <;> constructor <;> linarith
  have hr (x : ℝ) (hx : x ∈ Set.Icc a (a+L)) : A/x^2 ∈ Set.Icc η (2*Real.pi-η) := by
    have hx' := hsub hx
    refine ⟨hm hx' hends.2 hx'.2, (hm hends.1 hx' hx'.1).trans ?_⟩
    have hlo := (div_le_one (sq_pos_of_pos hM)).mpr hsmall
    linarith [Real.pi_gt_three]
  apply (hh hd hr (.inr (hm.mono hsub))).trans_eq
  dsimp [η]
  field_simp
  ring

private theorem block_Ico {M : ℕ} {A : ℝ} (hM : 0 < M) (hA : 0 < A)
    (hsmall : A ≤ (M:ℝ)^2) (l u : ℕ) (hl : M ≤ l) (hu : u ≤ 2*M) :
    ‖∑ m ∈ Finset.Ico l u, rotation (-A / m)‖ ≤ 8*Real.pi*(M:ℝ)^2/A := by
  by_cases hlu : l ≤ u
  · rw [Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.cast_add, add_comm] using
      block (M := M) (a := l) (L := u-l) (by exact_mod_cast hM) hA hsmall
        (by exact_mod_cast hl) (by
          rw [Nat.cast_sub hlu]
          have hh : (u:ℝ) ≤ 2*(M:ℝ) := by exact_mod_cast hu
          linarith)
  · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty, norm_zero]
    positivity

/-- A reciprocal wave evaluated at an actual product. -/
def wave (A : ℝ) (m n : ℕ) : ℂ := rotation (-A / ((m:ℝ) * n))

/-- The rectangular phase with arbitrary lower and upper cuts on each column. -/
def entry (A : ℝ) (l u : ℕ → ℕ) (m n : ℕ) : ℂ :=
  if l n ≤ m ∧ m < u n then wave A m n else 0

private theorem norm_entry_le (A : ℝ) (l u : ℕ → ℕ) (m n : ℕ) :
    ‖entry A l u m n‖ ≤ 1 := by
  unfold entry wave
  split_ifs <;> simp [norm_rotation]

private theorem wave_pair {A : ℝ} {m i j : ℕ} (hm : 0 < m) (hi : 0 < i) (hij : i < j) :
    wave A m i * conj (wave A m j) = rotation (-(A * (j-i : ℝ) / (i*j)) / m) := by
  rw [wave, wave, ← PhaseConjugation.rotation_neg, ← rotation_add]
  congr 1
  have hj := hi.trans hij
  have hm' : (m:ℝ) ≠ 0 := by positivity
  have hi' : (i:ℝ) ≠ 0 := by positivity
  have hj' : (j:ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Distinct column correlations decay as the reciprocal separation even when
the two product cuts leave a short or empty intersection. -/
theorem pair_bound {A : ℝ} {M N i j : ℕ} (hM : 0 < M) (hN : 0 < N) (hA : 0 < A)
    (hsmall : A ≤ (M:ℝ)^2 * N) (hi : i ∈ Finset.Ico N (2*N))
    (hj : j ∈ Finset.Ico N (2*N)) (hij : i < j) (l u : ℕ → ℕ) :
    ‖∑ m ∈ Finset.Ico M (2*M), entry A l u m i * conj (entry A l u m j)‖ ≤
      32*Real.pi*(M:ℝ)^2*(N:ℝ)^2 / (A*((j:ℝ)-i)) := by
  let L := max M (max (l i) (l j))
  let U := min (2*M) (min (u i) (u j))
  let B := A * ((j:ℝ)-i) / (i*j)
  obtain ⟨hiN,hi2⟩ := Finset.mem_Ico.mp hi
  obtain ⟨hjN,hj2⟩ := Finset.mem_Ico.mp hj
  have hni := hN.trans_le hiN
  have hnj := hni.trans hij
  have hi0 : (0:ℝ) < i := by exact_mod_cast hni
  have hj0 : (0:ℝ) < j := by exact_mod_cast hnj
  have hd : (0:ℝ) < (j:ℝ)-i := sub_pos.mpr (by exact_mod_cast hij)
  have hB : 0 < B := by dsimp [B]; positivity
  have hBsmall : B ≤ (M:ℝ)^2 := by
    apply (div_le_iff₀ (mul_pos hi0 hj0)).mpr
    calc
      _ ≤ A * j := mul_le_mul_of_nonneg_left (by linarith) hA.le
      _ ≤ ((M:ℝ)^2 * i) * j := by
        apply mul_le_mul_of_nonneg_right _ hj0.le
        exact hsmall.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hiN) (sq_nonneg _))
      _ = _ := by ring
  have hclip : (Finset.Ico M (2*M)).filter
      (fun m => (l i ≤ m ∧ m < u i) ∧ (l j ≤ m ∧ m < u j)) = Finset.Ico L U := by
    ext m
    simp [L,U, Finset.mem_Ico, and_assoc, and_left_comm, and_comm]
  have he : (∑ m ∈ Finset.Ico M (2*M), entry A l u m i * conj (entry A l u m j)) =
      ∑ m ∈ Finset.Ico L U, rotation (-B/m) := by
    rw [← hclip, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    have hm0 := hM.trans_le (Finset.mem_Ico.mp hm).1
    by_cases he1 : l i ≤ m ∧ m < u i <;> by_cases he2 : l j ≤ m ∧ m < u j <;>
      simp [entry, he1, he2, wave_pair hm0 hni hij, B]
  rw [he]
  apply (block_Ico hM hB hBsmall L U (le_max_left ..) (min_le_left ..)).trans
  have hi' : (i:ℝ) ≤ 2*N := by exact_mod_cast hi2.le
  have hj' : (j:ℝ) ≤ 2*N := by exact_mod_cast hj2.le
  have hp := mul_le_mul hi' hj' hj0.le (by positivity : (0:ℝ) ≤ 2*N)
  calc
    _ = 8*Real.pi*(M:ℝ)^2*((i:ℝ)*j) / (A*((j:ℝ)-i)) := by dsimp [B]; field
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (mul_pos hA hd).le
      nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 8*Real.pi*(M:ℝ)^2)]

private theorem harmonic_row {N i : ℕ} (hi : i ∈ Finset.Ico N (2*N)) :
    (∑ j ∈ Finset.Ico N (2*N), if i < j then ((j:ℝ)-i)⁻¹ else 0) ≤
      1 + Real.log N := by
  let T := (Finset.Ico N (2*N)).filter (i < ·)
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (fun j : ℕ => j-i) (T : Set ℕ) := by
    intro x hx y hy h
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    dsimp at h
    omega
  calc
    _ = ∑ r ∈ T.image (·-i), (r:ℝ)⁻¹ := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.cast_sub (Finset.mem_filter.mp hj).2.le]
    _ ≤ ∑ r ∈ Finset.Icc 1 N, (r:ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
      intro r hr
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨hjN,hij⟩ := Finset.mem_filter.mp hj
      have hi' := Finset.mem_Ico.mp hi
      have hj' := Finset.mem_Ico.mp hjN
      exact Finset.mem_Icc.mpr (by omega)
    _ ≤ _ := by
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        using harmonic_le_one_add_log N

private theorem gram_norm_sum {A : ℝ} {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (hA : 0 < A)
    (hsmall : A ≤ (M:ℝ)^2 * N) (l u : ℕ → ℕ) :
    (∑ i ∈ Finset.Ico N (2*N), ∑ j ∈ Finset.Ico N (2*N),
      ‖∑ m ∈ Finset.Ico M (2*M), entry A l u m i * conj (entry A l u m j)‖) ≤
      N * (M:ℝ) + 2 * N * (32*Real.pi*(M:ℝ)^2*(N:ℝ)^2/A) * (1+Real.log N) := by
  let I := Finset.Ico M (2*M)
  let J := Finset.Ico N (2*N)
  let g i j := ‖∑ m ∈ I, entry A l u m i * conj (entry A l u m j)‖
  let C := 32*Real.pi*(M:ℝ)^2*(N:ℝ)^2/A
  let f (i j : ℕ) := if i < j then ((j:ℝ)-i)⁻¹ else 0
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcI : I.card = M := by simp [I,two_mul]
  have hcJ : J.card = N := by simp [J,two_mul]
  have hdiag (i : ℕ) : g i i ≤ M := by
    apply (norm_sum_le ..).trans
    calc
      _ ≤ ∑ _m ∈ I, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro m _
        rw [norm_mul, Complex.norm_conj]
        simpa only [one_mul] using
          mul_le_mul (norm_entry_le A l u m i) (norm_entry_le A l u m i) (norm_nonneg _) zero_le_one
      _ = _ := by simp [hcI]
  have hsym (i j : ℕ) : g i j = g j i := by
    dsimp [g]
    rw [← Complex.norm_conj (∑ m ∈ I, entry A l u m j * conj (entry A l u m i))]
    simp only [map_sum, map_mul, Complex.conj_conj, mul_comm]
  have hp {i j : ℕ} (hi : i ∈ J) (hj : j ∈ J) (hij : i < j) : g i j ≤ C * f i j := by
    simpa [g,I,C,f,hij, div_eq_mul_inv,mul_left_comm,mul_comm,mul_assoc] using pair_bound hM hN hA hsmall hi hj hij l u
  have hmajor {i j : ℕ} (hi : i ∈ J) (hj : j ∈ J) :
      g i j ≤ (if i = j then (M:ℝ) else 0) + C*f i j + C*f j i := by
    rcases lt_trichotomy i j with h|rfl|h
    · simpa [h.ne, f, h, h.asymm] using hp hi hj h
    · simpa [f] using hdiag i
    · rw [hsym]
      simpa [h.ne', f, h, h.asymm] using hp hj hi h
  have hrow : (∑ i ∈ J, ∑ j ∈ J, C*f i j) ≤ (N:ℝ)*C*(1+Real.log N) := by
    calc
      _ ≤ ∑ i ∈ J, C*(1+Real.log N) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (harmonic_row hi) hC
      _ = _ := by simp [hcJ]; ring
  change (∑ i ∈ J, ∑ j ∈ J, g i j) ≤ _
  apply (Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hmajor hi hj).trans
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => C*f j i)]
  have hd : (∑ i ∈ J, ∑ j ∈ J, if i = j then (M:ℝ) else 0) = N * (M:ℝ) := by
    simp [hcJ]
  rw [hd]
  change _ ≤ (N:ℝ)*M + 2*N*C*(1+Real.log N)
  linarith

/-- Dyadic Type II estimate with arbitrary bounded coefficients and a literal
interval cut on the long variable in each short-variable column. -/
theorem bilinear_bound {A R S : ℝ} {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (hA : 0 < A)
    (hsmall : A ≤ (M:ℝ)^2*N) (a b : ℕ → ℂ) (l u : ℕ → ℕ)
    (ha : ∀ m ∈ Finset.Ico M (2*M), ‖a m‖ ≤ R) (hb : ∀ n ∈ Finset.Ico N (2*N), ‖b n‖ ≤ S) :
    ‖∑ m ∈ Finset.Ico M (2*M), a m * ∑ n ∈ Finset.Ico N (2*N), b n * entry A l u m n‖^2 ≤
      M * R^2 * S^2 * (N*(M:ℝ) + 2*N*(32*Real.pi*(M:ℝ)^2*(N:ℝ)^2/A)*(1+Real.log N)) := by
  let I := Finset.Ico M (2*M)
  let J := Finset.Ico N (2*N)
  let z := entry A l u
  let row m := ∑ n ∈ J, b n * z m n
  let gram i j := ∑ m ∈ I, z m i * conj (z m j)
  have hS : 0 ≤ S := (norm_nonneg _).trans (hb N (Finset.mem_Ico.mpr ⟨le_rfl,by omega⟩))
  have hId : (↑(∑ m ∈ I, ‖row m‖^2 : ℝ) : ℂ) =
      ∑ i ∈ J, ∑ j ∈ J, (b i * conj (b j)) * gram i j := by
    simp only [Complex.ofReal_sum, Complex.ofReal_pow, ← Complex.mul_conj', row, map_sum, map_mul,
      Finset.sum_mul, Finset.mul_sum, gram]
    conv_rhs => rw [Finset.sum_comm]
    rw [Finset.sum_comm (s := I) (t := J)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm (s := I) (t := J)]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hn := congrArg norm hId
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hn
  have henergy : (∑ m ∈ I, ‖row m‖^2) ≤ S^2 * ∑ i ∈ J, ∑ j ∈ J, ‖gram i j‖ := by
    rw [hn, Finset.mul_sum]
    apply (norm_sum_le ..).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum]
    apply (norm_sum_le ..).trans
    apply Finset.sum_le_sum
    intro j hj
    rw [norm_mul, norm_mul, Complex.norm_conj, sq]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hb i hi) (hb j hj) (norm_nonneg _) hS) (norm_nonneg _)
  have ham : (∑ m ∈ I, ‖a m‖^2) ≤ (M:ℝ)*R^2 := by
    calc
      _ ≤ ∑ _m ∈ I, R^2 := Finset.sum_le_sum (fun m hm => pow_le_pow_left₀ (norm_nonneg _) (ha m hm) 2)
      _ = _ := by simp [I,two_mul]
  have hh : ‖∑ m ∈ I, a m * row m‖ ≤ ∑ m ∈ I, ‖a m‖ * ‖row m‖ := by
    simpa only [norm_mul] using norm_sum_le I (fun m => a m * row m)
  calc
    _ ≤ _ := pow_le_pow_left₀ (norm_nonneg _) hh 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq I (fun m => ‖a m‖) (fun m => ‖row m‖)
    _ ≤ ((M:ℝ)*R^2) * (S^2 * ∑ i ∈ J, ∑ j ∈ J, ‖gram i j‖) :=
      mul_le_mul ham henergy (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (gram_norm_sum hM hN hA hsmall l u) (by positivity)

/-- The logarithmic Type I weight on every clipped reciprocal row. -/
theorem log_block {M A a : ℝ} {L : ℕ} (hM : 1 ≤ M) (hA : 0 < A) (hsmall : A ≤ M^2)
    (ha : M ≤ a) (hb : a + L ≤ 2*M) :
    ‖∑ j ∈ Finset.range L, (Real.log (a+j) : ℂ) * rotation (-A / (a+j))‖ ≤
      (8*Real.pi*M^2/A) * (2*Real.log (2*M)) := by
  have hM0 := zero_lt_one.trans_le hM
  have ha0 := hM0.trans_le ha
  have hb' : 0 ≤ Real.log (2*M) := Real.log_nonneg (by linarith)
  cases L with
  | zero => simp; positivity
  | succ K =>
    let w (n : ℕ) := Real.log (a+n)
    have hw (n : ℕ) : 0 ≤ w n := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hwm (n : ℕ) : w n ≤ w (n+1) := by
      apply Real.log_le_log (by positivity)
      push_cast
      linarith
    have hz (n : ℕ) (hn : n ≤ K) : a + (↑(n+1 : ℕ) : ℝ) ≤ 2*M :=
      (add_le_add_right (by exact_mod_cast Nat.succ_le_succ hn) a).trans hb
    have hh := FiniteAbelVariation.weighted_bound (fun n => (w n : ℂ))
      (fun n => rotation (-A/(a+n))) K (fun n hn => block hM0 hA hsmall ha (hz n hn))
    have hd (n : ℕ) : ‖(w n : ℂ)-(w (n+1) : ℂ)‖ = w (n+1)-w n := by
      rw [← Complex.ofReal_sub,Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr (hwm n))]
      ring
    simp only [hd, Finset.sum_range_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hw K)] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hlog : w K ≤ Real.log (2*M) := by
      apply Real.log_le_log (by positivity)
      push_cast at hb
      linarith
    linarith [hw 0]

open scoped ArithmeticFunction.Moebius

/-- The two cutoff functions encode the exact half-open product interval. -/
theorem entry_product (A : ℝ) (P Q m n : ℕ) (hn : 0 < n) :
    entry A (fun j => P/j+1) (fun j => Q/j+1) m n =
      if P < m*n ∧ m*n ≤ Q then wave A m n else 0 := by
  unfold entry
  simp only [Nat.add_one_le_iff,Nat.lt_succ_iff,Nat.div_lt_iff_lt_mul hn,Nat.le_div_iff_mul_le hn]

/-- Möbius coefficients with the strict cutoff used in Vaughan's identity. -/
def muTail (U m : ℕ) : ℂ := if U < m then (ArithmeticFunction.moebius m : ℂ) else 0

private theorem norm_muTail_le (U m : ℕ) : ‖muTail U m‖ ≤ 1 := by
  unfold muTail
  split_ifs
  · rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m)
  · simp

private theorem cofactor_size (V : ℕ) {N n : ℕ} (hN : 0 < N) (hn : n ∈ Finset.Ico N (2*N)) :
    ‖(ZetaVaughanReduction.cofactor V n : ℂ)‖ ≤ Real.log (2*(N:ℝ)) := by
  have hpos := hN.trans_le (Finset.mem_Ico.mp hn).1
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ZetaVaughanReduction.cofactor_nonneg ..)]
  exact (ZetaVaughanReduction.cofactor_le_log ..).trans (Real.log_le_log
    (by exact_mod_cast hpos) (by exact_mod_cast (Finset.mem_Ico.mp hn).2.le))

/-- The Type II estimate with the actual Vaughan coefficients in either
orientation. The outer variable is the one on which the first-derivative
test acts. Both endpoints of the product window are included in the formula. -/
theorem vaughan_box {A : ℝ} {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (hA : 0 < A)
    (hsmall : A ≤ (M:ℝ)^2*N) (P Q U V : ℕ) (swap : Bool) :
    ‖∑ m ∈ Finset.Ico M (2*M), ∑ n ∈ Finset.Ico N (2*N),
        (if swap then (ZetaVaughanReduction.cofactor V m : ℂ) * muTail U n
         else muTail U m * (ZetaVaughanReduction.cofactor V n : ℂ)) *
        (if P < m*n ∧ m*n ≤ Q then wave A m n else 0)‖^2 ≤
      (M:ℝ) * (if swap then Real.log (2*(M:ℝ)) else Real.log (2*(N:ℝ)))^2 *
      (N*(M:ℝ) + 2*N*(32*Real.pi*(M:ℝ)^2*(N:ℝ)^2/A)*(1+Real.log N)) := by
  have he (a b : ℕ → ℂ) :
      (∑ m ∈ Finset.Ico M (2*M), a m * ∑ n ∈ Finset.Ico N (2*N), b n *
        entry A (fun j => P/j+1) (fun j => Q/j+1) m n) =
      ∑ m ∈ Finset.Ico M (2*M), ∑ n ∈ Finset.Ico N (2*N),
        (a m * b n) * (if P < m*n ∧ m*n ≤ Q then wave A m n else 0) := by
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [entry_product _ _ _ _ _ (hN.trans_le (Finset.mem_Ico.mp hn).1), mul_assoc]
  cases swap
  · have hh := bilinear_bound hM hN hA hsmall (muTail U)
      (fun n => (ZetaVaughanReduction.cofactor V n : ℂ)) (fun j => P/j+1) (fun j => Q/j+1)
      (fun n _ => norm_muTail_le U n) (fun _ hn => cofactor_size V hN hn)
    rw [he] at hh
    simpa using hh
  · have hh := bilinear_bound hM hN hA hsmall
      (fun m => (ZetaVaughanReduction.cofactor V m : ℂ)) (muTail U) (fun j => P/j+1) (fun j => Q/j+1)
      (fun _ hm => cofactor_size V hM hm) (fun n _ => norm_muTail_le U n)
    rw [he] at hh
    simpa using hh

private theorem twist_angle {t δ F : ℝ} (ht : 1 ≤ t) (ht' : t ≤ 1+δ)
    (hF : 0 ≤ F) (hδ : F*δ^2 ≤ 1) :
    |F*(1/t-1+Real.log t)| ≤ 1 := by
  have ht0 := zero_lt_one.trans_le ht
  have hlow := Real.log_le_sub_one_of_pos (inv_pos.mpr ht0)
  rw [Real.log_inv, ← one_div] at hlow
  have ha : 0 ≤ 1/t-1+Real.log t := by linarith
  have hb := Real.log_le_sub_one_of_pos ht0
  have he : 1/t-1+(t-1) = (t-1)^2/t := by field_simp; ring
  have hsq : (t-1)^2 ≤ δ^2 := sq_le_sq' (by linarith) (by linarith)
  rw [abs_of_nonneg (mul_nonneg hF ha)]
  apply le_trans (mul_le_mul_of_nonneg_left _ hF) hδ
  calc
    _ ≤ 1/t-1+(t-1) := by linarith
    _ = _ := he
    _ ≤ (t-1)^2 := div_le_self (sq_nonneg _) ht
    _ ≤ _ := hsq

/-- Unit-modulus logarithmic twists produce a large reciprocal sum on a short
product interval. This tests what a bilinear estimate uniform in the coefficients
can prove. The actual arithmetic coefficients are specified in `vaughan_box`. -/
theorem log_twist_lower {F D δ : ℝ} (hF : 0 ≤ F) (hD : 0 < D) (hδ : F*δ^2 ≤ 1)
    (S : Finset (ℕ × ℕ)) (hs : ∀ z ∈ S,
      (z.1:ℝ)*z.2 ∈ Set.Icc D (D*(1+δ))) :
    (S.card:ℝ)/2 ≤ ‖∑ z ∈ S, rotation (-F*Real.log z.1) * rotation (-F*Real.log z.2) *
      wave (F*D) z.1 z.2‖ := by
  let c := F*(1+Real.log D)
  let f (z : ℕ × ℕ) := rotation (-F*Real.log z.1) * rotation (-F*Real.log z.2) *
    wave (F*D) z.1 z.2
  have hpoint (z : ℕ × ℕ) (hz : z ∈ S) : 1/2 ≤ (rotation c*f z).re := by
    let u := (z.1:ℝ)*z.2
    have hu : 0 < u := hD.trans_le (hs z hz).1
    have hm : (z.1:ℝ) ≠ 0 := fun h => by simp [u, h] at hu
    have hn : (z.2:ℝ) ≠ 0 := fun h => by simp [u, h] at hu
    have ht := twist_angle ((one_le_div hD).mpr (hs z hz).1)
      ((div_le_iff₀ hD).mpr (by simpa only [mul_comm] using (hs z hz).2)) hF hδ
    let b := F*(1/(u/D)-1+Real.log (u/D))
    have hb : |b| ≤ 1 := ht
    have he : rotation c*f z = rotation (-b) := by
      simp only [f, wave, ← rotation_add]
      congr 1
      dsimp only [c,b,u]
      rw [Real.log_div hu.ne' hD.ne', Real.log_mul hm hn]
      field_simp
      ring
    rw [he, PhaseIncrementInverse.rotation, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    have hl := Real.one_sub_sq_div_two_le_cos (x := b)
    have hb2 := sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
    nlinarith
  change _ ≤ ‖∑ z ∈ S, f z‖
  calc
    _ = ∑ _z ∈ S, (1/2:ℝ) := by simp [div_eq_mul_inv]
    _ ≤ ∑ z ∈ S, (rotation c*f z).re := Finset.sum_le_sum hpoint
    _ = (rotation c*∑ z ∈ S, f z).re := by rw [Finset.mul_sum, Complex.re_sum]
    _ ≤ _ := Complex.re_le_norm _
    _ = _ := by rw [norm_mul, norm_rotation, one_mul]

/-- An explicit clipped dyadic square, centered at product `144*r^2`. -/
def twistBand (r k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ico (8*r) (16*r)) ×ˢ (Finset.Ico (8*r) (16*r))).filter
    (fun z => 144*r^2 < z.1*z.2 ∧ z.1*z.2 ≤ 144*r^2+12*r*k)

private theorem twistBand_card {r k : ℕ} (hk : 0 < k) (hkr : k ≤ r) :
    2*r*k ≤ (twistBand r k).card := by
  let D := 144*r^2
  let T := Finset.Ico (10*r) (12*r) ×ˢ Finset.range k
  let f (z : ℕ × ℕ) := (D/z.1+1+z.2,z.1)
  have hc : T.card ≤ (twistBand r k).card := by
    apply Finset.card_le_card_of_injOn f
    · rintro ⟨n,j⟩ hz
      obtain ⟨hn,hj⟩ := Finset.mem_product.mp hz
      obtain ⟨hn1,hn2⟩ := Finset.mem_Ico.mp hn
      have hjk := Finset.mem_range.mp hj
      have hn0 : 0 < n := by omega
      have hlo : 12*r ≤ D/n := (Nat.le_div_iff_mul_le hn0).mpr (by
        dsimp [D]
        nlinarith [Nat.mul_le_mul_left (12*r) hn2.le])
      have hhi : D/n < 15*r := (Nat.div_lt_iff_lt_mul hn0).mpr (by
        dsimp [D]
        nlinarith [Nat.mul_le_mul_left (15*r) hn1, Nat.mul_pos (hk.trans_le hkr) (hk.trans_le hkr)])
      have hd : D < (D/n+1)*n := (Nat.div_lt_iff_lt_mul hn0).mp (Nat.lt_succ_self _)
      have hu : (D/n+1+j)*n ≤ D+12*r*k := by
        calc
          _ = D/n*n+(j+1)*n := by ring
          _ ≤ D+k*(12*r) := Nat.add_le_add (Nat.div_mul_le_self D n)
            (Nat.mul_le_mul (by omega) hn2.le)
          _ = _ := by ring
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨?_,?_⟩, Finset.mem_Ico.mpr ⟨?_,?_⟩⟩, ?_⟩
      · change 8*r ≤ D/n+1+j
        omega
      · change D/n+1+j < 16*r
        omega
      · change 8*r ≤ n
        omega
      · change n < 16*r
        omega
      · change D < (D/n+1+j)*n ∧ (D/n+1+j)*n ≤ D+12*r*k
        exact ⟨hd.trans_le (Nat.mul_le_mul_right n (by omega)), hu⟩
    · rintro ⟨n,j⟩ _ ⟨n',j'⟩ _ he
      have h := Prod.mk.inj he
      dsimp only [f] at h
      obtain ⟨h1,rfl⟩ := h
      congr 1
      omega
  simpa [T, Nat.card_Ico, show 12*r-10*r = 2*r by omega] using hc

/-- With frequency `F = (r/k)^2` and product scale `D = 144*r^2`, the
unit twists attain at least `D/(144*sqrt F)` on the entire clipped box. -/
theorem log_twist_box_lower {r k : ℕ} (hk : 0 < k) (hkr : k ≤ r) :
    let F := ((r:ℝ)/k)^2
    let D := 144*(r:ℝ)^2
    (r:ℝ)*k ≤ ‖∑ z ∈ twistBand r k, rotation (-F*Real.log z.1) *
      rotation (-F*Real.log z.2)*wave (F*D) z.1 z.2‖ := by
  dsimp only
  have hr : (0:ℝ) < r := by exact_mod_cast hk.trans_le hkr
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hl := log_twist_lower (F := ((r:ℝ)/k)^2) (D := 144*(r:ℝ)^2) (δ := (k:ℝ)/r)
    (sq_nonneg _) (by positivity) (by apply le_of_eq; field) (twistBand r k) (fun z hz => by
      have hz' := (Finset.mem_filter.mp hz).2
      have hlo : 144*(r:ℝ)^2 < (z.1:ℝ)*z.2 := by exact_mod_cast hz'.1
      have hhi : (z.1:ℝ)*z.2 ≤ 144*(r:ℝ)^2+12*r*k := by exact_mod_cast hz'.2
      refine ⟨hlo.le, hhi.trans ?_⟩
      field_simp
      nlinarith [mul_nonneg (sq_nonneg (r:ℝ)) hk'.le])
  have hc : 2*(r:ℝ)*k ≤ (twistBand r k).card := by exact_mod_cast twistBand_card hk hkr
  linarith

end
end RiemannGaussian.SuzukiReciprocal
