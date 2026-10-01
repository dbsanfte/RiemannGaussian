/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCanonicalOwnerRows
import RiemannGaussian.ZetaRieszSelectedGamma
import RiemannGaussian.ZetaRieszSignedDensityMain
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Signed cancellation on canonical rows with the full radial window

The unsigned leg on these rows spans the entire original core window.
Its factorial Fourier integral is evaluated before any norm is taken.
The original owner allocation is retained as an exact finite sum of
shifted factorial integrals. Neither the owner prime nor a prime cofactor
is completed. Rows cut by a moving boundary remain signed and unpaid.
-/

noncomputable section
open Filter Topology Real MeasureTheory Set
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszFreeRadialRows
open ZetaRieszCanonicalOwnerRows ZetaRieszUnsignedDivisorError
open ZetaRieszSaturatedRowFloor ZetaRieszOwnerMaximal
open ZetaRieszJointAllocation ZetaRieszWingHighOrders

/-- Precisely the original canonical rows whose three moving thresholds
do not shorten their total-log window. -/
def freeRows (u : ℝ) (N : ℕ) : Finset (ℕ×ℕ) :=
  (rows u N).filter (fun pb =>
    log (pb.1*pb.2 : ℕ) ≤ (37/20 : ℝ)*N ∧
    log pb.1 ≤ (507/400 : ℝ)*N ∧
    (203/100 : ℝ)*N ≤ log pb.1+SquarefreeVaughanLogSource.length u N)

theorem free_lowerLog {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (h : pb ∈ freeRows u N) :
    lowerLog N pb.1 pb.2 = (39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ) := by
  obtain ⟨_,hb,hp,_⟩ := Finset.mem_filter.mp h
  unfold lowerLog
  have hi : max ((39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ))
      ((20/13 : ℝ)*log pb.1-log (pb.1*pb.2 : ℕ)) =
        (39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ) := max_eq_left (by linarith)
  rw [hi,max_eq_right (by linarith)]

theorem free_upperLog {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (h : pb ∈ freeRows u N) :
    upperLog N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2 =
      (203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ) := by
  obtain ⟨hr,_,_,hp⟩ := Finset.mem_filter.mp h
  have hg := rows_geometry hr
  have hb0 : pb.2 ≠ 0 := by have := hg.2.1; omega
  have hl : log (pb.1*pb.2 : ℕ)=log pb.1+log pb.2 := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hg.1.ne_zero) (by exact_mod_cast hb0)]
  unfold upperLog
  rw [min_eq_left (by rw [hl]; linarith)]

/-- The damping of the actual fixed-height unsigned-leg Fourier phase. -/
def damping (y : ℝ) : ℂ := ((1/2 : ℝ) : ℂ)+Complex.I*y

private theorem damping_re (y : ℝ) : (damping y).re=1/2 := by simp [damping]

private theorem damping_norm (y : ℝ) (hy : 54 ≤ |y|) : 16 ≤ ‖damping y‖ := by
  have hi := Complex.abs_im_le_norm (damping y)
  have hi' : |y| ≤ ‖damping y‖ := by simpa [damping] using hi
  linarith

/-- One exact complementary factorial channel. The variable is the
unsigned cofactor logarithm after subtracting the fixed owner logarithm. -/
def allocatedChannel (N k : ℕ) (P y x : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)*((P : ℂ)^(N+1-k)/((N+1-k).factorial : ℂ))*
    ((x : ℂ)^k/(k.factorial : ℂ))*Complex.exp (-damping y*(x+P))

/-- The exact complete integral of the SAME factorial channel. -/
def allocatedIntegral (N k : ℕ) (P y : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)*Complex.exp (-damping y*P)*
    ((P : ℂ)^(N+1-k)/((N+1-k).factorial : ℂ))*((damping y)⁻¹)^(k+1)

theorem allocatedChannel_laplace (N k : ℕ) (P y : ℝ) :
    IntegrableOn (allocatedChannel N k P y) (Ioi 0) ∧
    (∫ x : ℝ in Ioi 0, allocatedChannel N k P y x)=allocatedIntegral N k P y := by
  have h := ZetaRieszSelectedGamma.complex_factorial_laplace
    (z := damping y) (by rw [damping_re]; norm_num) k
  have he x : allocatedChannel N k P y x =
      (((N+1 : ℕ) : ℂ)*Complex.exp (-damping y*P)*
        ((P : ℂ)^(N+1-k)/((N+1-k).factorial : ℂ)))*
        ((x : ℂ)^k/(k.factorial : ℂ)*Complex.exp (-damping y*x)) := by
    unfold allocatedChannel
    rw [show -damping y*(x+P) = -damping y*x+(-damping y*P) by ring,
      Complex.exp_add]
    ring
  rw [funext he]
  exact ⟨h.1.const_mul _,by rw [integral_const_mul,h.2]; rfl⟩

/-- Summing the allocated factorial orders BEFORE estimating keeps the
full owner weight. This is a complete unsigned-log integral only. -/
def completeOwnerIntegral (N : ℕ) (P y : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)*((damping y)⁻¹)^(N+2)-
    ∑ k ∈ unpaidOrders N, allocatedIntegral N k P y

private theorem factorial_envelope (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    exp (-P/2)*P^m/(m.factorial : ℝ) ≤ (2 : ℝ)^m := by
  have hh := logMoment_exp_envelope m hP (by norm_num : (0 : ℝ)<1/2) (1/2)
  norm_num only [sub_self,zero_mul,exp_zero,mul_one,inv_div,one_div] at hh
  convert hh using 1
  ring_nf

private theorem allocated_order {N k : ℕ} (hk : k ∈ unpaidOrders N) :
    k ≤ N+1 ∧ N+1 ≤ 5*k := by
  rw [unpaidOrders_eq] at hk
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hk
  omega

/-- No absolute source envelope is charged to the allocated orders.
Their exact Fourier denominator pays the whole channel geometrically. -/
theorem allocatedIntegral_bound {u P y : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ (3/4 : ℝ)) (hP : 0 ≤ P) (hy : 54 ≤ |y|)
    {N k : ℕ} (hk : k ∈ unpaidOrders N) :
    ‖(u : ℂ)^(N+1)*allocatedIntegral N k P y‖ ≤
      ((N : ℝ)+1)*(3/4 : ℝ)^N := by
  have hk' := allocated_order hk
  have hd := damping_norm y hy
  have hd0 : 0 < ‖damping y‖ := by linarith
  have hpow : N+1-k ≤ 4*k := by omega
  have h16 : (2 : ℝ)^(N+1-k) ≤ ‖damping y‖^(k+1) := by
    calc
      _ ≤ (2 : ℝ)^(4*k) := pow_le_pow_right₀ (by norm_num) hpow
      _ = (16 : ℝ)^k := by rw [pow_mul]; norm_num
      _ ≤ ‖damping y‖^k := pow_le_pow_left₀ (by norm_num) hd k
      _ ≤ ‖damping y‖^(k+1) := pow_le_pow_right₀ (by linarith) (by omega)
  have he := factorial_envelope (N+1-k) hP
  have hex : ‖Complex.exp (-damping y*P)‖=exp (-P/2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re,damping]
    ring
  have hratio : exp (-P/2)*P^(N+1-k)/(N+1-k).factorial*
      (‖damping y‖⁻¹)^(k+1) ≤ 1 := by
    rw [inv_pow]
    exact (mul_le_mul_of_nonneg_right he (by positivity)).trans
      ((mul_inv_le_iff₀ (by positivity : 0 < ‖damping y‖^(k+1))).mpr (by simpa using h16))
  have huN : u^(N+1) ≤ (3/4 : ℝ)^N := by
    calc
      _ ≤ (3/4 : ℝ)^(N+1) := pow_le_pow_left₀ hu hU _
      _ ≤ (3/4 : ℝ)^N := by
        rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) (by norm_num)
  simp only [allocatedIntegral,norm_mul,norm_pow,norm_div,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hu,Complex.norm_natCast,hex,norm_inv,
    abs_of_nonneg hP]
  calc
    _ = (((N : ℝ)+1)*u^(N+1))*
        (exp (-P/2)*P^(N+1-k)/(N+1-k).factorial*(‖damping y‖⁻¹)^(k+1)) := by
      push_cast; ring
    _ ≤ ((N : ℝ)+1)*u^(N+1) := mul_le_of_le_one_right (by positivity) hratio
    _ ≤ _ := mul_le_mul_of_nonneg_left huN (by positivity)

/-- Explicit geometric saving for the complete signed unsigned-leg
response, including EVERY original owner-allocation order. -/
theorem completeOwnerIntegral_bound {u P y : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ (3/4 : ℝ)) (hP : 0 ≤ P) (hy : 54 ≤ |y|) (N : ℕ) :
    ‖(u : ℂ)^(N+1)*completeOwnerIntegral N P y‖ ≤
      ((N : ℝ)+1)*((N : ℝ)+3)*(3/4 : ℝ)^N := by
  have hd := damping_norm y hy
  have hi : ‖(damping y)⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have huN : u^(N+1) ≤ (3/4 : ℝ)^N := by
    exact (pow_le_pow_left₀ hu hU _).trans
      (by rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) (by norm_num))
  have hbase : ‖(u : ℂ)^(N+1)*(((N+1 : ℕ) : ℂ)*((damping y)⁻¹)^(N+2))‖ ≤
      ((N : ℝ)+1)*(3/4 : ℝ)^N := by
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hu,Complex.norm_natCast]
    have hp : ‖(damping y)⁻¹‖^(N+2) ≤ 1 := pow_le_one₀ (norm_nonneg _) hi
    calc
      _ = (u^(N+1)*(N+1 : ℕ))*‖(damping y)⁻¹‖^(N+2) := by ring
      _ ≤ u^(N+1)*(N+1 : ℕ) := mul_le_of_le_one_right (by positivity) hp
      _ ≤ _ := by
        push_cast
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left huN (by positivity : 0 ≤ (N : ℝ)+1)
  have hs : ‖∑ k ∈ unpaidOrders N, (u : ℂ)^(N+1)*allocatedIntegral N k P y‖ ≤
      ((N : ℝ)+2)*(((N : ℝ)+1)*(3/4 : ℝ)^N) := by
    apply (norm_sum_le _ _).trans
    have hb := Finset.sum_le_sum (s := unpaidOrders N)
      (fun k hk => allocatedIntegral_bound hu hU hP hy hk)
    simp only [Finset.sum_const,nsmul_eq_mul] at hb
    have hc : (unpaidOrders N).card ≤ N+2 := by
      apply le_trans (Finset.card_le_card ?_) (Finset.card_range (N+2)).le
      intro k hk
      exact Finset.mem_range.mpr (by have := (allocated_order hk).1; omega)
    exact hb.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity))
  unfold completeOwnerIntegral
  rw [mul_sub,Finset.mul_sum]
  exact (norm_sub_le _ _).trans (by nlinarith [hbase,hs])

/-- The full factorial phase on the positive radial half-line. -/
def radialFourier (N : ℕ) (y T : ℝ) : ℂ :=
  (radialMoment N T : ℂ)*Complex.exp (-(Complex.I*y)*(T : ℂ))

private theorem radialFourier_laplace (N : ℕ) (y : ℝ) :
    IntegrableOn (radialFourier N y) (Ioi 0) ∧
    (∫ T : ℝ in Ioi 0, radialFourier N y T) =
      ((N+1 : ℕ) : ℂ)*((damping y)⁻¹)^(N+2) := by
  have h := ZetaRieszSelectedGamma.complex_factorial_laplace
    (z := damping y) (by rw [damping_re]; norm_num) (N+1)
  have he T : radialFourier N y T = ((N+1 : ℕ) : ℂ)*
      ((T : ℂ)^(N+1)/((N+1).factorial : ℂ)*Complex.exp (-damping y*T)) := by
    unfold radialFourier radialMoment damping
    simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
      Complex.ofReal_exp,Complex.ofReal_neg,Complex.ofReal_natCast]
    norm_num only [Complex.ofReal_ofNat,Complex.ofReal_one]
    rw [show -((1/2 : ℂ)+Complex.I*y)*T =
      (-(T : ℂ)/2)+(-(Complex.I*y)*(T : ℂ)) by ring,Complex.exp_add]
    rw [Nat.factorial_succ,Nat.cast_mul]
    have hn : ((N+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : N+1 ≠ 0)
    have hf : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
    field_simp
  rw [funext he]
  exact ⟨h.1.const_mul _,by rw [integral_const_mul,h.2]⟩

/-- Zero extension is only in the unsigned radial integration variable.
It does not extend any prime support or count mask. -/
def ownerFourier (N : ℕ) (P y T : ℝ) : ℂ :=
  (Ioi (0 : ℝ)).indicator (radialFourier N y) T-
    ∑ k ∈ unpaidOrders N,
      (Ioi (0 : ℝ)).indicator (allocatedChannel N k P y) (T-P)

theorem ownerFourier_integral (N : ℕ) (P y : ℝ) :
    Integrable (ownerFourier N P y) ∧
    (∫ T : ℝ, ownerFourier N P y T)=completeOwnerIntegral N P y := by
  have hb := (radialFourier_laplace N y).1.integrable_indicator measurableSet_Ioi
  have ha k : Integrable (fun T : ℝ =>
      (Ioi (0 : ℝ)).indicator (allocatedChannel N k P y) (T-P)) :=
    ((allocatedChannel_laplace N k P y).1.integrable_indicator measurableSet_Ioi).comp_sub_right P
  refine ⟨hb.sub (integrable_finsetSum _ (fun k _ => ha k)),?_⟩
  simp only [ownerFourier]
  rw [integral_sub hb (integrable_finsetSum _ (fun k _ => ha k)),
    integral_indicator measurableSet_Ioi,integral_finsetSum _ (fun k _ => ha k),
    (radialFourier_laplace N y).2]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_sub_right_eq_self,integral_indicator measurableSet_Ioi,
    (allocatedChannel_laplace N k P y).2]

private theorem mass_radial {N k : ℕ} (hk : k ≤ N+1)
    {P T : ℝ} (hT : T ≠ 0) :
    mass (N+1) k (1-P/T)*radialMoment N T =
      ((N : ℝ)+1)*P^(N+1-k)/(N+1-k).factorial*
        ((T-P)^k/k.factorial)*exp (-T/2) := by
  have hchoose : ((N+1).choose k : ℝ)/(N.factorial : ℝ) =
      ((N : ℝ)+1)/((k.factorial : ℝ)*((N+1-k).factorial : ℝ)) := by
    have hc := Nat.choose_mul_factorial_mul_factorial hk
    rw [Nat.factorial_succ] at hc
    have hc' : ((N+1).choose k : ℝ)*k.factorial*(N+1-k).factorial =
        ((N : ℝ)+1)*N.factorial := by exact_mod_cast hc
    field_simp
    nlinarith only [hc']
  have hn : k+(N+1-k)=N+1 := by omega
  have he : (1-P/T)^k*(1-(1-P/T))^(N+1-k)*T^(N+1) =
      (T-P)^k*P^(N+1-k) := by
    rw [show 1-(1-P/T)=P/T by ring,
      show 1-P/T=(T-P)/T by field_simp,div_pow,div_pow,
      div_mul_div_comm,← pow_add,hn]
    exact div_mul_cancel₀ _ (pow_ne_zero _ hT)
  unfold mass radialMoment
  calc
    _ = ((1-P/T)^k*(1-(1-P/T))^(N+1-k)*T^(N+1))*
      (((N+1).choose k : ℝ)/(N.factorial : ℝ))*exp (-T/2) := by ring
    _ = _ := by rw [he,hchoose]; ring

private theorem allocatedChannel_mass {N k : ℕ} (hk : k ≤ N+1)
    {P T : ℝ} (hT : T ≠ 0) (y : ℝ) :
    allocatedChannel N k P y (T-P) =
      (mass (N+1) k (1-P/T) : ℂ)*radialFourier N y T := by
  unfold allocatedChannel
  simp only [Complex.ofReal_sub]
  rw [sub_add_cancel]
  rw [show -damping y*T = (-(T : ℂ)/2)+(-(Complex.I*y)*(T : ℂ)) by
    simp only [damping]; push_cast; ring,Complex.exp_add]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) (mass_radial (P := P) hk hT)
  rw [Complex.ofReal_mul] at hc
  rw [radialFourier]
  conv_rhs => rw [← mul_assoc,hc]
  push_cast
  ring

/-- On the actual positive owner region this is exactly its original
allocation and phase, without dropping any factorial order. -/
theorem ownerFourier_eq_literal (N : ℕ) {P T : ℝ} (hP : 0 ≤ P)
    (hPT : P < T) (y : ℝ) :
    ownerFourier N P y T =
      (ownerWeight N (1-P/T) : ℂ)*radialFourier N y T := by
  have ht : 0 < T := hP.trans_lt hPT
  simp only [ownerFourier,Set.indicator_of_mem (show T ∈ Ioi (0 : ℝ) from ht),
    Set.indicator_of_mem (show T-P ∈ Ioi (0 : ℝ) from sub_pos.mpr hPT)]
  have he : (∑ k ∈ unpaidOrders N, allocatedChannel N k P y (T-P)) =
      ∑ k ∈ unpaidOrders N, (mass (N+1) k (1-P/T) : ℂ)*radialFourier N y T := by
    exact Finset.sum_congr rfl (fun k hk => allocatedChannel_mass (allocated_order hk).1 ht.ne' y)
  rw [he]
  rw [ownerWeight,Complex.ofReal_sub,Complex.ofReal_sum,Complex.ofReal_one,
    sub_mul,Finset.sum_mul,one_mul]

theorem ownerFourier_norm (N : ℕ) {P T : ℝ} (hP : 0 ≤ P) (hT : 0 < T) (y : ℝ) :
    ‖ownerFourier N P y T‖ ≤ radialMoment N T := by
  have hr := radialMoment_nonneg N hT.le
  have hf : ‖radialFourier N y T‖=radialMoment N T := by
    simp [radialFourier,Complex.norm_exp,abs_of_nonneg hr]
  by_cases hPT : P < T
  · rw [ownerFourier_eq_literal N hP hPT y,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,hf]
    have hx : 0 ≤ 1-P/T ∧ 1-P/T ≤ 1 := by
      constructor
      · have := (div_le_one hT).mpr hPT.le; linarith
      · have := div_nonneg hP hT.le; linarith
    have ho := ownerWeight_bounds N hx.1 hx.2
    rw [abs_of_nonneg ho.1]
    exact mul_le_of_le_one_left hr ho.2
  · have hz k : (Ioi (0 : ℝ)).indicator (allocatedChannel N k P y) (T-P)=0 :=
      indicator_of_notMem (by simp only [mem_Ioi]; linarith) _
    simp only [ownerFourier,Set.indicator_of_mem (show T ∈ Ioi (0 : ℝ) from hT),
      hz,Finset.sum_const_zero,sub_zero,hf,le_refl]

private def scaledRadial (N : ℕ) (a T : ℝ) : ℝ :=
  exp (-T/a)*T^(N+1)/(N.factorial : ℝ)

private theorem scaledRadial_integral (N : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (scaledRadial N a) (Ioi 0) ∧
    (∫ T : ℝ in Ioi 0, scaledRadial N a T)=((N : ℝ)+1)*a^(N+2) := by
  have he T : scaledRadial N a T = (((N : ℝ)+1)*a^(N+2))*
      ZetaRieszSelectedGamma.gammaKernel a⁻¹ (N+2) T := by
    unfold scaledRadial ZetaRieszSelectedGamma.gammaKernel
    simp only [show N+2-1=N+1 by omega,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    rw [show -a⁻¹*T = -T/a by ring,inv_pow]
    field_simp
  have hi := ZetaRieszSelectedGamma.gammaKernel_integrable (inv_pos.mpr ha) (N+2)
  rw [funext he]
  exact ⟨hi.const_mul _,by
    rw [integral_const_mul,ZetaRieszSelectedGamma.integral_gammaKernel
      (inv_pos.mpr ha) (by omega),mul_one]⟩

private theorem radialMoment_integrable (N : ℕ) :
    IntegrableOn (radialMoment N) (Ioi 0) := by
  have he : scaledRadial N 2=radialMoment N := by ext T; rfl
  rw [← he]
  exact (scaledRadial_integral N (by norm_num : (0 : ℝ)<2)).1

private theorem lower_radial_tail (N : ℕ) {a : ℝ} (ha : 0 < a) (ha2 : a < 2) :
    (∫ T : ℝ in (0 : ℝ)..a*N, radialMoment N T) ≤
      exp ((1-a/2)*N)*(((N : ℝ)+1)*a^(N+2)) := by
  have hab : (0 : ℝ) ≤ a*N := by positivity
  have hp T (ht : T ∈ Ioc (0 : ℝ) (a*N)) :
      radialMoment N T ≤ exp ((1-a/2)*N)*scaledRadial N a T := by
    have ht0 : 0 ≤ T := ht.1.le
    have htilt : 0 ≤ a⁻¹-1/2 := by
      rw [sub_nonneg,inv_eq_one_div]
      exact (le_div_iff₀ ha).mpr (by linarith)
    have he : exp (-T/2) ≤ exp ((1-a/2)*N)*exp (-T/a) := by
      rw [← exp_add]
      apply exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left ht.2 htilt
      field_simp at hh ⊢
      nlinarith
    unfold radialMoment scaledRadial
    calc
      _ ≤ (exp ((1-a/2)*N)*exp (-T/a))*T^(N+1)/N.factorial :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he (by positivity)) (by positivity)
      _ = _ := by ring
  rw [intervalIntegral.integral_of_le hab]
  have hi : IntegrableOn (fun T => exp ((1-a/2)*N)*scaledRadial N a T) (Ioi 0) :=
    (scaledRadial_integral N ha).1.const_mul (exp ((1-a/2)*N))
  calc
    _ ≤ ∫ T : ℝ in Ioc 0 (a*N), exp ((1-a/2)*N)*scaledRadial N a T :=
      setIntegral_mono_on ((radialMoment_integrable N).mono_set Ioc_subset_Ioi_self)
        (hi.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc hp
    _ ≤ ∫ T : ℝ in Ioi 0, exp ((1-a/2)*N)*scaledRadial N a T :=
      setIntegral_mono_set hi (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with T ht
        have ht0 : 0 ≤ T := ht.le
        unfold scaledRadial; positivity)
        (Eventually.of_forall (fun _ ht => ht.1))
    _ = _ := by rw [integral_const_mul,(scaledRadial_integral N ha).2]

private theorem upper_radial_tail (N : ℕ) {a : ℝ} (ha : 2 < a) :
    (∫ T : ℝ in Ioi (a*N), radialMoment N T) ≤
      exp ((1-a/2)*N)*(((N : ℝ)+1)*a^(N+2)) := by
  have ha0 : 0 < a := by linarith
  have hs : Ioi (a*(N : ℝ)) ⊆ Ioi (0 : ℝ) := by
    intro T ht
    exact lt_of_le_of_lt (show (0 : ℝ) ≤ a*N by positivity) ht
  have hp T (ht : T ∈ Ioi (a*N)) :
      radialMoment N T ≤ exp ((1-a/2)*N)*scaledRadial N a T := by
    have htilt : a⁻¹-1/2 ≤ 0 := by
      rw [sub_nonpos,inv_eq_one_div]
      exact (div_le_iff₀ ha0).mpr (by linarith)
    have he : exp (-T/2) ≤ exp ((1-a/2)*N)*exp (-T/a) := by
      rw [← exp_add]
      apply exp_le_exp.mpr
      have hh := mul_le_mul_of_nonpos_left ht.le htilt
      field_simp at hh ⊢
      nlinarith
    unfold radialMoment scaledRadial
    calc
      _ ≤ (exp ((1-a/2)*N)*exp (-T/a))*T^(N+1)/N.factorial :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right he (by have : 0 ≤ T := (by positivity : 0 ≤ a*N).trans ht.le; positivity))
          (by positivity)
      _ = _ := by ring
  have hi : IntegrableOn (fun T => exp ((1-a/2)*N)*scaledRadial N a T) (Ioi 0) :=
    (scaledRadial_integral N ha0).1.const_mul (exp ((1-a/2)*N))
  calc
    _ ≤ ∫ T : ℝ in Ioi (a*N), exp ((1-a/2)*N)*scaledRadial N a T :=
      setIntegral_mono_on ((radialMoment_integrable N).mono_set hs)
        (hi.mono_set hs) measurableSet_Ioi hp
    _ ≤ ∫ T : ℝ in Ioi 0, exp ((1-a/2)*N)*scaledRadial N a T :=
      setIntegral_mono_set hi (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with T ht
        have ht0 : 0 ≤ T := ht.le
        unfold scaledRadial; positivity)
        (Eventually.of_forall (fun _ ht => hs ht))
    _ = _ := by rw [integral_const_mul,(scaledRadial_integral N ha0).2]

/-- The already certified core endpoints have a strict exponential
margin AFTER source normalization. -/
def radialRate : ℝ := max (3/4 : ℝ)
  (max (ZetaRieszWideOwnerAudit.radiusCeiling*(39/20)*exp (1-(39/20)/2))
    (ZetaRieszWideOwnerAudit.radiusCeiling*(203/100)*exp (1-(203/100)/2)))

theorem radialRate_bounds : 0 < radialRate ∧ radialRate < 1 := by
  have hlo := ZetaRieszParityPacket.core_window_costs.1
  have hhi := ZetaRieszParityPacket.core_window_costs.2
  have hU : 0 < ZetaRieszWideOwnerAudit.radiusCeiling := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
  have hr (a : ℝ) (ha : 0 < a)
      (hc : log (2*ZetaRieszWideOwnerAudit.radiusCeiling)<LogarithmicDeviation.deviationCost a) :
      ZetaRieszWideOwnerAudit.radiusCeiling*a*exp (1-a/2)<1 := by
    rw [← exp_log (mul_pos hU ha),← exp_add]
    apply exp_lt_one_iff.mpr
    have he := LogarithmicDeviation.log_rate_eq_deviation hU ha
    linarith
  constructor
  · unfold radialRate; exact (by norm_num : (0 : ℝ)<3/4).trans_le (le_max_left _ _)
  · unfold radialRate
    exact max_lt (by norm_num) (max_lt (hr _ (by norm_num) hlo) (hr _ (by norm_num) hhi))

private theorem normalized_radial_tail {u a : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (ha : 0 ≤ a)
    (hcoef : ZetaRieszWideOwnerAudit.radiusCeiling*a^2 ≤ 3)
    (hr : ZetaRieszWideOwnerAudit.radiusCeiling*a*exp (1-a/2) ≤ radialRate) (N : ℕ) :
    u^(N+1)*(exp ((1-a/2)*N)*(((N : ℝ)+1)*a^(N+2))) ≤
      3*((N : ℝ)+1)*radialRate^N := by
  have he : ZetaRieszWideOwnerAudit.radiusCeiling^(N+1)*
      (exp ((1-a/2)*N)*(((N : ℝ)+1)*a^(N+2))) =
      ((N : ℝ)+1)*(ZetaRieszWideOwnerAudit.radiusCeiling*a^2)*
        (ZetaRieszWideOwnerAudit.radiusCeiling*a*exp (1-a/2))^N := by
    rw [mul_comm (1-a/2),exp_nat_mul]
    simp only [pow_add,pow_one]
    ring
  calc
    _ ≤ ZetaRieszWideOwnerAudit.radiusCeiling^(N+1)*
      (exp ((1-a/2)*N)*(((N : ℝ)+1)*a^(N+2))) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu hU _) (by positivity)
    _ = _ := he
    _ ≤ ((N : ℝ)+1)*3*radialRate^N := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hcoef (by positivity)
      · apply pow_le_pow_left₀ _ hr N
        have hU0 : 0 ≤ ZetaRieszWideOwnerAudit.radiusCeiling := by
          norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
        positivity
      · exact pow_nonneg (mul_nonneg
          (mul_nonneg (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]) ha) (exp_pos _).le) N
      · positivity
    _ = _ := by ring

private theorem owner_integral_norm {N : ℕ} {P y : ℝ} (hP : 0 ≤ P)
    {S : Set ℝ} (hS : MeasurableSet S) (hsub : S ⊆ Ioi (0 : ℝ)) :
    ‖∫ T : ℝ in S, ownerFourier N P y T‖ ≤ ∫ T : ℝ in S, radialMoment N T := by
  apply (norm_integral_le_integral_norm _).trans
  exact setIntegral_mono_on (ownerFourier_integral N P y).1.norm.integrableOn
    ((radialMoment_integrable N).mono_set hsub) hS
    (fun T ht => ownerFourier_norm N hP (hsub ht) y)

private theorem owner_integral_Ioi {N : ℕ} {P y : ℝ} (hP : 0 ≤ P) :
    (∫ T : ℝ in Ioi 0, ownerFourier N P y T)=completeOwnerIntegral N P y := by
  have he : (Ioi (0 : ℝ)).indicator (ownerFourier N P y)=ownerFourier N P y := by
    ext T
    by_cases ht : 0 < T
    · exact Set.indicator_of_mem ht _
    · rw [Set.indicator_of_notMem (show T ∉ Ioi (0 : ℝ) from ht)]
      symm
      have hx : T-P ∉ Ioi (0 : ℝ) := by simp only [mem_Ioi]; linarith
      simp only [ownerFourier,Set.indicator_of_notMem (show T ∉ Ioi (0 : ℝ) from ht),
        Set.indicator_of_notMem hx,Finset.sum_const_zero,sub_zero]
  rw [← integral_indicator measurableSet_Ioi,he,(ownerFourier_integral N P y).2]

/-- The entire ORIGINAL radial window, with its full owner allocation
and phase, has a strict source-normalized geometric bound. -/
theorem owner_window_bound {u P y : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hP : 0 ≤ P)
    (hy : 54 ≤ |y|) (N : ℕ) :
    ‖(u : ℂ)^(N+1)*(∫ T : ℝ in (39/20 : ℝ)*N..(203/100 : ℝ)*N,
      ownerFourier N P y T)‖ ≤ ((N : ℝ)+1)*((N : ℝ)+9)*radialRate^N := by
  let a : ℝ := (39/20)*N
  let b : ℝ := (203/100)*N
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hab : a ≤ b := by dsimp [a,b]; nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hi := (ownerFourier_integral N P y).1.integrableOn (s := Ioi (0 : ℝ))
  have hiA : IntegrableOn (ownerFourier N P y) (Ioi a) :=
    hi.mono_set (fun _ h => lt_of_le_of_lt ha0 h)
  have h0 := intervalIntegral.integral_Ioi_sub_Ioi hi ha0
  have h1 := intervalIntegral.integral_Ioi_sub_Ioi hiA hab
  rw [owner_integral_Ioi hP] at h0
  have he : (∫ T : ℝ in a..b, ownerFourier N P y T) =
      completeOwnerIntegral N P y-(∫ T : ℝ in (0 : ℝ)..a, ownerFourier N P y T)-
        (∫ T : ℝ in Ioi b, ownerFourier N P y T) := by
    rw [← h0,← h1]
    abel
  have hlo : ‖(u : ℂ)^(N+1)*(∫ T : ℝ in (0 : ℝ)..a, ownerFourier N P y T)‖ ≤
      3*((N : ℝ)+1)*radialRate^N := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu]
    have hn : ‖∫ T : ℝ in (0 : ℝ)..a, ownerFourier N P y T‖ ≤
        exp ((1-(39/20)/2)*N)*(((N : ℝ)+1)*(39/20)^(N+2)) := by
      rw [intervalIntegral.integral_of_le ha0]
      have hh := (owner_integral_norm (y := y) hP measurableSet_Ioc Ioc_subset_Ioi_self).trans
        (by simpa only [a,intervalIntegral.integral_of_le ha0] using
          lower_radial_tail N (by norm_num : (0 : ℝ)<39/20) (by norm_num))
      exact hh
    exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans
      (normalized_radial_tail hu hU (by norm_num : (0 : ℝ)≤39/20)
        (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
        ((le_max_left _ _).trans (le_max_right _ _)) N)
  have hhi : ‖(u : ℂ)^(N+1)*(∫ T : ℝ in Ioi b, ownerFourier N P y T)‖ ≤
      3*((N : ℝ)+1)*radialRate^N := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu]
    have hn := (owner_integral_norm (y := y) hP measurableSet_Ioi
      (fun _ h => lt_of_le_of_lt hb0 h)).trans
        (upper_radial_tail N (by norm_num : (2 : ℝ)<203/100))
    exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans
      (normalized_radial_tail hu hU (by norm_num : (0 : ℝ)≤203/100)
        (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
        ((le_max_right _ _).trans (le_max_right _ _)) N)
  have hbase := completeOwnerIntegral_bound hu
    (hU.trans (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])) hP hy N
  have hb : ‖(u : ℂ)^(N+1)*completeOwnerIntegral N P y‖ ≤
      ((N : ℝ)+1)*((N : ℝ)+3)*radialRate^N :=
    hbase.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) (le_max_left _ _) N) (by positivity))
  change ‖(u : ℂ)^(N+1)*(∫ T : ℝ in a..b, ownerFourier N P y T)‖ ≤ _
  rw [he,mul_sub,mul_sub]
  exact (norm_sub_le _ _).trans (by
    have hh := norm_sub_le ((u : ℂ)^(N+1)*completeOwnerIntegral N P y)
      ((u : ℂ)^(N+1)*(∫ T : ℝ in (0 : ℝ)..a, ownerFourier N P y T))
    nlinarith [hb,hlo,hhi])

private theorem mass_le_one (n k : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    mass n k x ≤ 1 := by
  by_cases hk : k ≤ n
  · have hh := Finset.single_le_sum (s := Finset.range (n+1))
      (f := fun j => mass n j x) (fun j _ => mass_nonneg n j hx hx1)
      (Finset.mem_range.mpr (by omega : k<n+1))
    exact hh.trans_eq (mass_total n x)
  · simp [mass,Nat.choose_eq_zero_of_lt (lt_of_not_ge hk)]

private theorem lowerMass_lipschitz (n k : ℕ) {x z : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    |lowerMass n k x-lowerMass n k z| ≤ (n : ℝ)*|x-z| := by
  have hb t (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖-(n : ℝ)*mass (n-1) k t‖ ≤ n := by
    rw [Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
      abs_of_nonneg (mass_nonneg _ _ ht.1 ht.2)]
    exact mul_le_of_le_one_right (Nat.cast_nonneg n) (mass_le_one _ _ ht.1 ht.2)
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (hasDerivAt_lowerMass n k t).hasDerivWithinAt) hb
      (convex_Icc (0 : ℝ) 1) hz hx

private theorem ownerWeight_lipschitz {N : ℕ} (hN : 32 ≤ N) {x z : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    |ownerWeight N x-ownerWeight N z| ≤ 2*((N : ℝ)+1)*|x-z| := by
  have he t : ownerWeight N t =
      1-lowerMass (N+1) (13*N/32) t+lowerMass (N+1) (N/5+1) t := by
    rw [ownerWeight,ownerMass_eq_difference hN]; ring
  rw [he,he]
  have hh := lowerMass_lipschitz (N+1) (13*N/32) hx hz
  have hl := lowerMass_lipschitz (N+1) (N/5+1) hx hz
  have he' : (1-lowerMass (N+1) (13*N/32) x+lowerMass (N+1) (N/5+1) x)-
      (1-lowerMass (N+1) (13*N/32) z+lowerMass (N+1) (N/5+1) z) =
      -(lowerMass (N+1) (13*N/32) x-lowerMass (N+1) (13*N/32) z)+
        (lowerMass (N+1) (N/5+1) x-lowerMass (N+1) (N/5+1) z) := by ring
  rw [he']
  exact (abs_add_le _ _).trans (by rw [abs_neg]; push_cast at hh hl; linarith)

/-- The real integrand of the unchanged density row. -/
def physicalWeight (N : ℕ) (P y T : ℝ) : ℝ :=
  ownerWeight N (1-P/T)*radialMoment N T*cos (y*T)

private theorem physicalWeight_bound (N : ℕ) {P T : ℝ} (hP : 0 ≤ P)
    (hT : 1 ≤ T) (hPT : P ≤ T) (y : ℝ) :
    |physicalWeight N P y T| ≤ radialEnvelope N := by
  have ht0 : 0 < T := by linarith
  have hx : 0 ≤ 1-P/T ∧ 1-P/T ≤ 1 := by
    constructor
    · have := (div_le_one ht0).mpr hPT; linarith
    · have := div_nonneg hP ht0.le; linarith
  have ho := ownerWeight_bounds N hx.1 hx.2
  rw [physicalWeight,abs_mul,abs_mul,abs_of_nonneg ho.1,
    abs_of_nonneg (radialMoment_nonneg N ht0.le)]
  calc
    _ ≤ radialMoment N T := mul_le_of_le_one_right
      (mul_nonneg ho.1 (radialMoment_nonneg N ht0.le)) (abs_cos_le_one _)
        |>.trans (mul_le_of_le_one_left (radialMoment_nonneg N ht0.le) ho.2)
    _ ≤ _ := radialMoment_le N ht0.le

private theorem ownerPhysical_eq_re (N : ℕ) {P T : ℝ} (hP : 0 ≤ P)
    (hPT : P < T) (y : ℝ) :
    physicalWeight N P y T=(ownerFourier N P y T).re := by
  rw [ownerFourier_eq_literal N hP hPT y]
  simp [physicalWeight,radialFourier,Complex.mul_re,Complex.exp_re,cos_neg]
  ring

private theorem physicalWeight_lipschitz {N : ℕ} (hN : 32 ≤ N) {P T U : ℝ}
    (hP : 0 ≤ P) (hT : 1 ≤ T) (hU : 1 ≤ U) (hPT : P ≤ T) (hPU : P ≤ U) (y : ℝ) :
    |physicalWeight N P y T-physicalWeight N P y U| ≤
      ((3*(N : ℝ)+4+|y|)*radialEnvelope N)*|T-U| := by
  have ht0 : 0 < T := by linarith
  have hu0 : 0 < U := by linarith
  have hx (V : ℝ) (hV : 0 < V) (hp : P ≤ V) : 1-P/V ∈ Icc (0 : ℝ) 1 := by
    constructor
    · have := (div_le_one hV).mpr hp; linarith
    · have := div_nonneg hP hV.le; linarith
  have hs : |(1-P/T)-(1-P/U)| ≤ |T-U| := by
    have he : |(1-P/T)-(1-P/U)|=(P/(T*U))*|T-U| := by
      rw [show (1-P/T)-(1-P/U)=(P/(T*U))*(T-U) by field_simp; ring,
        abs_mul,abs_of_nonneg (div_nonneg hP (mul_pos ht0 hu0).le)]
    rw [he]
    apply mul_le_of_le_one_left (abs_nonneg _)
    exact (div_le_one (mul_pos ht0 hu0)).mpr (by nlinarith)
  have hw := (ownerWeight_lipschitz hN (hx T ht0 hPT) (hx U hu0 hPU)).trans
    (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*((N : ℝ)+1)))
  have hr := radialMoment_lipschitz N hT hU
  have ht := (ownerWeight_bounds N (hx T ht0 hPT).1 (hx T ht0 hPT).2)
  have hu := (ownerWeight_bounds N (hx U hu0 hPU).1 (hx U hu0 hPU).2)
  have ham : |ownerWeight N (1-P/T)*radialMoment N T-
      ownerWeight N (1-P/U)*radialMoment N U| ≤
        ((3*(N : ℝ)+4)*radialEnvelope N)*|T-U| := by
    have he : ownerWeight N (1-P/T)*radialMoment N T-ownerWeight N (1-P/U)*radialMoment N U =
        (ownerWeight N (1-P/T)-ownerWeight N (1-P/U))*radialMoment N T+
          ownerWeight N (1-P/U)*(radialMoment N T-radialMoment N U) := by ring
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_of_nonneg (radialMoment_nonneg N ht0.le),abs_of_nonneg hu.1]
    have hfirst := mul_le_mul hw (radialMoment_le N ht0.le)
      (radialMoment_nonneg N ht0.le) (by positivity : 0 ≤ 2*((N : ℝ)+1)*|T-U|)
    have hsecond := mul_le_mul hu.2 hr (abs_nonneg _) zero_le_one
    nlinarith [hfirst,hsecond]
  have hc : |cos (y*T)-cos (y*U)| ≤ |y| * |T-U| := by
    have hh := abs_cos_sub_cos_le (y*T) (y*U)
    simpa only [← mul_sub,abs_mul] using hh
  have hAU : |ownerWeight N (1-P/U)*radialMoment N U| ≤ radialEnvelope N := by
    rw [abs_mul,abs_of_nonneg hu.1,abs_of_nonneg (radialMoment_nonneg N hu0.le)]
    exact (mul_le_of_le_one_left (radialMoment_nonneg N hu0.le) hu.2).trans (radialMoment_le N hu0.le)
  unfold physicalWeight
  have he : ownerWeight N (1-P/T)*radialMoment N T*cos (y*T)-
      ownerWeight N (1-P/U)*radialMoment N U*cos (y*U) =
      (ownerWeight N (1-P/T)*radialMoment N T-ownerWeight N (1-P/U)*radialMoment N U)*cos (y*T)+
        (ownerWeight N (1-P/U)*radialMoment N U)*(cos (y*T)-cos (y*U)) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul]
  have hfirst := mul_le_mul ham (abs_cos_le_one (y*T)) (abs_nonneg _)
    (mul_nonneg (mul_nonneg (by positivity) (radialEnvelope_pos N).le) (abs_nonneg _))
  have hsecond := mul_le_mul hAU hc (abs_nonneg _) (radialEnvelope_pos N).le
  nlinarith [hfirst,hsecond]

private theorem log_lipschitz {M x z : ℝ} (hM : 0 < M) (hx : M ≤ x) (hz : M ≤ z) :
    |log x-log z| ≤ M⁻¹*|x-z| := by
  have hb t (ht : t ∈ Ici M) : ‖t⁻¹‖ ≤ M⁻¹ := by
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hM.trans_le ht))]
    exact inv_anti₀ hM ht
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hasDerivAt_log (hM.trans_le ht).ne').hasDerivWithinAt) hb
      (convex_Ici M) hz hx

private theorem inv_lipschitz {M x z : ℝ} (hM : 0 < M) (hx : M ≤ x) (hz : M ≤ z) :
    |x⁻¹-z⁻¹| ≤ |x-z|/M^2 := by
  have hx0 := hM.trans_le hx
  have hz0 := hM.trans_le hz
  have he : x⁻¹-z⁻¹=-(x-z)/(x*z) := by field_simp; ring
  rw [he,abs_div,abs_neg,abs_of_pos (mul_pos hx0 hz0)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hM) (by nlinarith)

private theorem physicalWeight_continuousAt (N : ℕ) (P y : ℝ) {T : ℝ} (hT : T ≠ 0) :
    ContinuousAt (physicalWeight N P y) T := by
  unfold physicalWeight ownerWeight mass radialMoment
  fun_prop

private theorem log_kernel_lipschitz {N : ℕ} (hN : 32 ≤ N) {P c M x z : ℝ}
    (hP : 0 ≤ P) (hM : 0 < M) (hT : 1 ≤ c+log M) (hPT : P ≤ c+log M)
    (hx : M ≤ x) (hz : M ≤ z) (y : ℝ) :
    |physicalWeight N P y (c+log x)/x-physicalWeight N P y (c+log z)/z| ≤
      ((3*(N : ℝ)+5+|y|)*radialEnvelope N)/M^2*|x-z| := by
  have hx0 := hM.trans_le hx
  have hz0 := hM.trans_le hz
  have htx : c+log M ≤ c+log x := add_le_add_right (log_le_log hM hx) c
  have htz : c+log M ≤ c+log z := add_le_add_right (log_le_log hM hz) c
  let B := (3*(N : ℝ)+4+|y|)*radialEnvelope N
  let A := radialEnvelope N
  have hB : 0 ≤ B := mul_nonneg (by positivity) (radialEnvelope_pos N).le
  have hA : 0 ≤ A := (radialEnvelope_pos N).le
  have hf := physicalWeight_lipschitz hN hP (hT.trans htx) (hT.trans htz)
    (hPT.trans htx) (hPT.trans htz) y
  have hl := log_lipschitz hM hx hz
  have hf' : |physicalWeight N P y (c+log x)-physicalWeight N P y (c+log z)| ≤
      B*(M⁻¹*|x-z|) := by
    have hf'' : |physicalWeight N P y (c+log x)-physicalWeight N P y (c+log z)| ≤
        B*|log x-log z| := by simpa only [add_sub_add_left_eq_sub] using hf
    exact hf''.trans (mul_le_mul_of_nonneg_left hl hB)
  have ha : |physicalWeight N P y (c+log z)| ≤ A :=
    physicalWeight_bound N hP (hT.trans htz) (hPT.trans htz) y
  have he : physicalWeight N P y (c+log x)/x-physicalWeight N P y (c+log z)/z =
      (physicalWeight N P y (c+log x)-physicalWeight N P y (c+log z))*x⁻¹+
        physicalWeight N P y (c+log z)*(x⁻¹-z⁻¹) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_of_pos (inv_pos.mpr hx0)]
  have hfirst := mul_le_mul hf' (inv_anti₀ hM hx) (inv_nonneg.mpr hx0.le)
    (mul_nonneg hB (mul_nonneg (inv_nonneg.mpr hM.le) (abs_nonneg _)))
  have hsecond := mul_le_mul ha (inv_lipschitz hM hx hz) (abs_nonneg _) hA
  calc
    _ ≤ B*(M⁻¹*|x-z|)*M⁻¹+A*(|x-z|/M^2) := add_le_add hfirst hsecond
    _ = _ := by dsimp [A,B]; field_simp; ring

private theorem interval_lattice_error {M X : ℕ} (hMX : M ≤ X) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc (M : ℝ) X)) (K : ℕ → ℝ)
    (hK : ∀ k ∈ Finset.Ico M X, 0 ≤ K k)
    (hlip : ∀ k ∈ Finset.Ico M X, ∀ x ∈ Icc (k : ℝ) (k+1 : ℕ),
      ∀ z ∈ Icc (k : ℝ) (k+1 : ℕ), |g x-g z| ≤ K k*|x-z|) :
    |(∑ d ∈ Finset.Ioc M X, g d)-(∫ x : ℝ in (M : ℝ)..X, g x)| ≤
      ∑ k ∈ Finset.Ico M X, K k := by
  have hh k (hk : k ∈ Finset.Ico M X) :
      |g (k+1 : ℕ)-(∫ x : ℝ in (k : ℝ)..(k+1 : ℕ), g x)| ≤ K k := by
    have hk' := Finset.mem_Ico.mp hk
    have hc : ContinuousOn g (uIcc (k : ℝ) (k+1 : ℕ)) := by
      apply hg.mono
      rw [uIcc_of_le (by exact_mod_cast Nat.le_succ k)]
      intro x hx
      exact ⟨(by exact_mod_cast hk'.1 : (M : ℝ) ≤ k).trans hx.1,
        hx.2.trans (by exact_mod_cast (by omega : k+1 ≤ X))⟩
    have hp := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (k : ℝ)) (b := ((k+1 : ℕ) : ℝ)) (f := fun x => g (k+1 : ℕ)-g x)
      (C := K k) (fun x hx => by
        rw [uIoc_of_le (by exact_mod_cast Nat.le_succ k)] at hx
        have hxe : x ∈ Icc (k : ℝ) (k+1 : ℕ) := ⟨hx.1.le,hx.2⟩
        have hke : ((k+1 : ℕ) : ℝ) ∈ Icc (k : ℝ) (k+1 : ℕ) :=
          ⟨by exact_mod_cast Nat.le_succ k,le_rfl⟩
        rw [Real.norm_eq_abs]
        apply (hlip k hk _ hke _ hxe).trans
        apply mul_le_of_le_one_right (hK k hk)
        rw [abs_of_nonneg (sub_nonneg.mpr hx.2)]
        norm_num only [Nat.cast_add,Nat.cast_one] at hx ⊢
        linarith [hx.1])
    rw [intervalIntegral.integral_sub intervalIntegrable_const hc.intervalIntegrable] at hp
    simpa only [intervalIntegral.integral_const,Nat.cast_add,Nat.cast_one,
      add_sub_cancel_left,one_smul,Real.norm_eq_abs,abs_one,mul_one] using hp
  have he : (∑ d ∈ Finset.Ioc M X, g d) =
      ∑ k ∈ Finset.Ico M X, g (k+1 : ℕ) := by
    symm
    apply Finset.sum_bij (fun k _ => k+1)
    · intro k hk; have := Finset.mem_Ico.mp hk; exact Finset.mem_Ioc.mpr (by omega)
    · intro k _ l _ h; omega
    · intro d hd; have := Finset.mem_Ioc.mp hd
      exact ⟨d-1,Finset.mem_Ico.mpr (by omega),by omega⟩
    · intro _ _; rfl
  have hi : (∑ k ∈ Finset.Ico M X, ∫ x : ℝ in (k : ℝ)..(k+1 : ℕ), g x) =
      ∫ x : ℝ in (M : ℝ)..X, g x := by
    apply intervalIntegral.sum_integral_adjacent_intervals_Ico hMX
    intro k hk
    have hk' : M ≤ k ∧ k < X := hk
    apply (hg.mono ?_).intervalIntegrable
    rw [uIcc_of_le (by exact_mod_cast Nat.le_succ k)]
    intro x hx
    exact ⟨(by exact_mod_cast hk'.1 : (M : ℝ) ≤ k).trans hx.1,
      hx.2.trans (by exact_mod_cast (by omega : k+1 ≤ X))⟩
  rw [he,← hi,← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hh)

private theorem reciprocal_square_sum {M X : ℕ} (hM : 0 < M) (hMX : M ≤ X) :
    (∑ k ∈ Finset.Ico M X, (1 : ℝ)/(k : ℝ)^2) ≤ 2/(M : ℝ) := by
  have hb k (hk : k ∈ Finset.Ico M X) :
      (1 : ℝ)/(k : ℝ)^2 ≤ 2*((k : ℝ)⁻¹-((k+1 : ℕ) : ℝ)⁻¹) := by
    have hk0 : (0 : ℝ)<k := by exact_mod_cast hM.trans_le (Finset.mem_Ico.mp hk).1
    have hk1 : (1 : ℝ)≤k := by
      exact_mod_cast Nat.succ_le_of_lt (hM.trans_le (Finset.mem_Ico.mp hk).1)
    norm_num only [Nat.cast_add,Nat.cast_one]
    field_simp
    nlinarith
  have ht : (∑ k ∈ Finset.Ico M X, ((k : ℝ)⁻¹-((k+1 : ℕ) : ℝ)⁻¹)) =
      (M : ℝ)⁻¹-(X : ℝ)⁻¹ := by
    calc
      _ = -(∑ k ∈ Finset.Ico M X, (((k+1 : ℕ) : ℝ)⁻¹-(k : ℝ)⁻¹)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = _ := by rw [Finset.sum_Ico_sub (fun k : ℕ => (k : ℝ)⁻¹) hMX]; ring
  calc
    _ ≤ ∑ k ∈ Finset.Ico M X, 2*((k : ℝ)⁻¹-((k+1 : ℕ) : ℝ)⁻¹) :=
      Finset.sum_le_sum hb
    _ = 2*((M : ℝ)⁻¹-(X : ℝ)⁻¹) := by rw [← Finset.mul_sum,ht]
    _ ≤ _ := by rw [div_eq_mul_inv]; nlinarith [inv_nonneg.mpr (Nat.cast_nonneg X : (0 : ℝ)≤X)]

/-- Integer quadrature is paid only on the unsigned divisor leg. The
square-summable local variation avoids any prime-density approximation
and is uniform in the original upper endpoint. -/
theorem integer_weight_error {N M X : ℕ} (hN : 32 ≤ N) (hM : 0 < M) (hMX : M ≤ X)
    {P c : ℝ} (hP : 0 ≤ P) (hT : 1 ≤ c+log M) (hPT : P ≤ c+log M) (y : ℝ) :
    |(∑ d ∈ Finset.Ioc M X, physicalWeight N P y (c+log d)/(d : ℝ))-
        ∫ T : ℝ in (c+log M)..(c+log X), physicalWeight N P y T| ≤
      2*(3*(N : ℝ)+5+|y|)*radialEnvelope N/(M : ℝ) := by
  have hM0 : (0 : ℝ)<M := by exact_mod_cast hM
  have hx0 (x : ℝ) (hx : x ∈ Icc (M : ℝ) X) : 0 < x := hM0.trans_le hx.1
  have htx (x : ℝ) (hx : x ∈ Icc (M : ℝ) X) : c+log M ≤ c+log x :=
    add_le_add_right (log_le_log hM0 hx.1) c
  let g : ℝ → ℝ := fun x => physicalWeight N P y (c+log x)/x
  have hg : ContinuousOn g (Icc (M : ℝ) X) := by
    intro x hx
    have hx' := (hx0 x hx).ne'
    have ht' : c+log x ≠ 0 := by linarith [htx x hx]
    apply ContinuousAt.continuousWithinAt
    exact ((physicalWeight_continuousAt N P y ht').comp (f := fun x : ℝ => c+log x)
      (continuousAt_const.add (continuousAt_log hx'))).div continuousAt_id hx'
  let B := (3*(N : ℝ)+5+|y|)*radialEnvelope N
  have hB : 0 ≤ B := mul_nonneg (by positivity) (radialEnvelope_pos N).le
  have hl := interval_lattice_error hMX g hg (fun k => B/(k : ℝ)^2)
    (fun _ _ => div_nonneg hB (sq_nonneg _)) (by
      intro k hk x hx z hz
      have hk' := Finset.mem_Ico.mp hk
      have hk0 : (0 : ℝ)<k := by exact_mod_cast hM.trans_le hk'.1
      have hmk : (M : ℝ)≤k := by exact_mod_cast hk'.1
      have htk : c+log M ≤ c+log k := add_le_add_right (log_le_log hM0 hmk) c
      exact log_kernel_lipschitz hN hP hk0 (hT.trans htk) (hPT.trans htk) hx.1 hz.1 y)
  have hs : (∑ k ∈ Finset.Ico M X, B/(k : ℝ)^2) ≤ 2*B/(M : ℝ) := by
    rw [show (∑ k ∈ Finset.Ico M X, B/(k : ℝ)^2) =
      B*(∑ k ∈ Finset.Ico M X, (1 : ℝ)/(k : ℝ)^2) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)]
    exact (mul_le_mul_of_nonneg_left (reciprocal_square_sum hM hMX) hB).trans_eq (by ring)
  have hi : (∫ x : ℝ in (M : ℝ)..X, g x) =
      ∫ T : ℝ in (c+log M)..(c+log X), physicalWeight N P y T := by
    have hu : uIcc (M : ℝ) X=Icc (M : ℝ) X := uIcc_of_le (by exact_mod_cast hMX)
    have hf : ∀ x ∈ uIcc (M : ℝ) X,
        HasDerivAt (fun x => c+log x) x⁻¹ x := by
      intro x hx
      rw [hu] at hx
      exact HasDerivAt.const_add c (hasDerivAt_log (hx0 x hx).ne')
    have hd : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc (M : ℝ) X) := by
      rw [hu]
      intro x hx
      exact (continuousAt_inv₀ (hx0 x hx).ne').continuousWithinAt
    have hc : ContinuousOn (physicalWeight N P y)
        ((fun x => c+log x) '' uIcc (M : ℝ) X) := by
      rintro T ⟨x,hx,rfl⟩
      rw [hu] at hx
      exact (physicalWeight_continuousAt N P y (by linarith [htx x hx])).continuousWithinAt
    simpa only [g,Function.comp_def,div_eq_mul_inv] using
      intervalIntegral.integral_comp_mul_deriv' hf hd hc
  rw [hi] at hl
  exact (hl.trans hs).trans_eq (by dsimp [B]; ring)

private theorem log_ceil_gap (v : ℝ) :
    0 ≤ log (⌈exp v⌉₊ : ℝ)-v ∧ log (⌈exp v⌉₊ : ℝ)-v ≤ exp (-v) := by
  have hm : (0 : ℝ)<⌈exp v⌉₊ := by exact_mod_cast Nat.ceil_pos.mpr (exp_pos v)
  have hlo := log_le_log (exp_pos v) (Nat.le_ceil (exp v))
  have hhi := (Nat.ceil_lt_add_one (exp_pos v).le).le
  have hl := log_le_sub_one_of_pos (div_pos hm (exp_pos v))
  rw [log_div hm.ne' (exp_pos v).ne',log_exp] at hl
  refine ⟨by simpa using sub_nonneg.mpr hlo,hl.trans ?_⟩
  rw [show (⌈exp v⌉₊ : ℝ)/exp v-1=((⌈exp v⌉₊ : ℝ)-exp v)/exp v by field_simp,
    exp_neg,← one_div]
  exact div_le_div_of_nonneg_right (by linarith) (exp_pos v).le

private theorem log_floor_gap {v : ℝ} (h : 0 < ⌊exp v⌋₊) :
    0 ≤ v-log (⌊exp v⌋₊ : ℝ) ∧ v-log (⌊exp v⌋₊ : ℝ) ≤ (⌊exp v⌋₊ : ℝ)⁻¹ := by
  have hx : (0 : ℝ)<⌊exp v⌋₊ := by exact_mod_cast h
  have hlo := log_le_log hx (Nat.floor_le (exp_pos v).le)
  have hhi := (Nat.lt_floor_add_one (exp v)).le
  have hl := log_le_sub_one_of_pos (div_pos (exp_pos v) hx)
  rw [log_div (exp_pos v).ne' hx.ne',log_exp] at hl
  refine ⟨by simpa using sub_nonneg.mpr hlo,hl.trans ?_⟩
  rw [show exp v/(⌊exp v⌋₊ : ℝ)-1=(exp v-(⌊exp v⌋₊ : ℝ))/(⌊exp v⌋₊ : ℝ) by
      field_simp,← one_div]
  exact div_le_div_of_nonneg_right (by linarith) hx.le

private theorem physical_window_bound {N : ℕ} (hN : 32 ≤ N) {P : ℝ}
    (hP : 0 ≤ P) (hPl : P ≤ (39/20 : ℝ)*N) (y : ℝ) :
    ∀ T ∈ Icc ((39/20 : ℝ)*N) ((203/100 : ℝ)*N),
      |physicalWeight N P y T| ≤ radialEnvelope N := by
  intro T hT
  have hn : (32 : ℝ)≤N := by exact_mod_cast hN
  exact physicalWeight_bound N hP (by linarith [hT.1]) (hPl.trans hT.1) y

/-- The original integer endpoints are compared with the full original
radial window. Only their rounding slivers are norm-bounded. -/
theorem free_integer_window_error {u : ℝ} {N : ℕ} (hN : 32 ≤ N) {pb : ℕ×ℕ}
    (hpb : pb ∈ freeRows u N) (y : ℝ) :
    |(∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
        (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2),
      physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))-
        ∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
          physicalWeight N (log pb.1) y T| ≤
      (6*(N : ℝ)+12+2*|y|)*radialEnvelope N*exp (-(N : ℝ)/10) := by
  obtain ⟨hr,_,hP,_⟩ := Finset.mem_filter.mp hpb
  obtain ⟨hp,hb,hs,hpd,hmax,hH,hM,hlo,hhi,hsat,hshare⟩ := rows_geometry hr
  have hMX := (Finset.mem_filter.mp hr).2.2.2.2.2
  have hX : 0 < upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2 := hM.trans_le hMX
  let P := log pb.1
  let c := log (pb.1*pb.2 : ℕ)
  let a := (39/20 : ℝ)*N
  let b := (203/100 : ℝ)*N
  let M := lower N pb.1 pb.2
  let X := upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2
  have hPl : P ≤ a := by dsimp [P,a]; linarith
  have hP0 : 0 ≤ P := log_natCast_nonneg pb.1
  have ha1 : 1 ≤ a := by
    have hn : (32 : ℝ)≤N := by exact_mod_cast hN
    dsimp [a]
    linarith
  have hl : a ≤ c+log M := hlo
  have hh : c+log X ≤ b := hhi
  have hlog : c+log M ≤ c+log X :=
    add_le_add_right (log_le_log (by exact_mod_cast hM) (by exact_mod_cast hMX)) c
  have heM : (M : ℝ)⁻¹ ≤ exp (-(N : ℝ)/10) := by
    rw [neg_div,exp_neg]
    exact inv_anti₀ (exp_pos _) (rows_large N pb.1 pb.2)
  have hleft : c+log M-a ≤ exp (-(N : ℝ)/10) := by
    have hv := (log_ceil_gap (lowerLog N pb.1 pb.2)).2
    change log (M : ℝ)-lowerLog N pb.1 pb.2 ≤ _ at hv
    rw [free_lowerLog hpb] at hv
    have hrlo : (N : ℝ)/10 ≤ lowerLog N pb.1 pb.2 := le_max_left _ _
    rw [free_lowerLog hpb] at hrlo
    exact (by dsimp [a,c]; linarith [hv] : c+log M-a ≤ exp (-(a-c))).trans
      (exp_le_exp.mpr (by dsimp [a,c]; linarith))
  have hright : b-(c+log X) ≤ exp (-(N : ℝ)/10) := by
    have hv := (log_floor_gap (v := upperLog N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2) hX).2
    change upperLog N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2-log X ≤ (X : ℝ)⁻¹ at hv
    rw [free_upperLog hpb] at hv
    have hi : (X : ℝ)⁻¹ ≤ (M : ℝ)⁻¹ := inv_anti₀ (by exact_mod_cast hM) (by exact_mod_cast hMX)
    exact (by dsimp [b,c]; linarith [hv] : b-(c+log X) ≤ (X : ℝ)⁻¹).trans (hi.trans heM)
  have hc : ContinuousOn (physicalWeight N P y) (Icc a b) := by
    intro T hT
    exact (physicalWeight_continuousAt N P y (by linarith [hT.1])).continuousWithinAt
  have hI (v w : ℝ) (hv : a ≤ v) (hw : w ≤ b) (hvw : v ≤ w) :
      IntervalIntegrable (physicalWeight N P y) volume v w := by
    apply (hc.mono ?_).intervalIntegrable
    rw [uIcc_of_le hvw]
    exact Icc_subset_Icc hv hw
  have hwb := physical_window_bound hN hP0 hPl y
  have hli : |∫ T : ℝ in a..(c+log M), physicalWeight N P y T| ≤
      radialEnvelope N*exp (-(N : ℝ)/10) := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := c+log M) (C := radialEnvelope N) (f := physicalWeight N P y) (by
        rw [uIoc_of_le hl]
        intro T hT
        exact hwb T ⟨hT.1.le,hT.2.trans (hlog.trans hh)⟩)
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hl)] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left hleft (radialEnvelope_pos N).le)
  have hri : |∫ T : ℝ in (c+log X)..b, physicalWeight N P y T| ≤
      radialEnvelope N*exp (-(N : ℝ)/10) := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := c+log X) (b := b) (C := radialEnvelope N) (f := physicalWeight N P y) (by
        rw [uIoc_of_le hh]
        intro T hT
        exact hwb T ⟨(hl.trans hlog).trans hT.1.le,hT.2⟩)
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hh)] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left hright (radialEnvelope_pos N).le)
  have he : (∫ T : ℝ in a..b, physicalWeight N P y T)=
      (∫ T : ℝ in a..(c+log M), physicalWeight N P y T)+
      (∫ T : ℝ in (c+log M)..(c+log X), physicalWeight N P y T)+
      (∫ T : ℝ in (c+log X)..b, physicalWeight N P y T) := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hI a _ le_rfl (hlog.trans hh) hl) (hI _ _ hl hh hlog),
      intervalIntegral.integral_add_adjacent_intervals
        (hI a _ le_rfl hh (hl.trans hlog)) (hI _ b (hl.trans hlog) le_rfl hh)]
  have hq := integer_weight_error hN hM hMX hP0 (ha1.trans hl) (hPl.trans hl) y
  have hq' := (mul_le_mul_of_nonneg_left heM
    (by positivity [radialEnvelope_pos N] : 0 ≤ 2*(3*(N : ℝ)+5+|y|)*radialEnvelope N))
  rw [← div_eq_mul_inv] at hq'
  have hq'' := hq.trans hq'
  change |_-∫ T : ℝ in a..b, physicalWeight N P y T| ≤ _
  rw [he]
  calc
    _ = |((∑ d ∈ Finset.Ioc M X, physicalWeight N P y (c+log d)/(d : ℝ))-
        ∫ T : ℝ in (c+log M)..(c+log X), physicalWeight N P y T)-
      ((∫ T : ℝ in a..(c+log M), physicalWeight N P y T)+
        ∫ T : ℝ in (c+log X)..b, physicalWeight N P y T)| := by congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans (add_le_add hq'' ((abs_add_le _ _).trans (add_le_add hli hri)))
    _ = _ := by ring

/-- The exact all-intersection coprimality density is a probability. -/
theorem density_bounds (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    0 ≤ density S ∧ density S ≤ 1 := by
  have he : density S=SquarefreeCounting.density ∅*
      ∏ p ∈ S, (1-((p : ℝ)+1)⁻¹) := by
    unfold density
    simp_rw [sub_eq_add_neg]
    rw [Finset.prod_one_add,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro W hW
    rw [ZetaRieszSignedDensityMain.density_marks W
      (fun p hp => hS p ((Finset.mem_powerset.mp hW) hp)),Finset.prod_neg]
    ring
  have hn p (_ : p ∈ S) : 0 ≤ 1-((p : ℝ)+1)⁻¹ := by
    have hi : ((p : ℝ)+1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀
      (by linarith [Nat.cast_nonneg (α := ℝ) p])
    linarith
  have hu p (_ : p ∈ S) : 1-((p : ℝ)+1)⁻¹ ≤ 1 := by
    linarith [inv_nonneg.mpr (show (0 : ℝ)≤(p : ℝ)+1 by positivity)]
  rw [he]
  exact ⟨mul_nonneg ZetaRieszSignedDensityMain.base_density_bounds.1
      (Finset.prod_nonneg hn),
    (mul_le_of_le_one_right ZetaRieszSignedDensityMain.base_density_bounds.1
      (Finset.prod_le_one hn hu)).trans ZetaRieszSignedDensityMain.base_density_bounds.2⟩

private theorem physical_window_source_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 32 ≤ N)
    {pb : ℕ×ℕ} (hpb : pb ∈ freeRows u N) {y : ℝ} (hy : 54 ≤ |y|) :
    |u^(N+1)*(∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
      physicalWeight N (log pb.1) y T)| ≤ ((N : ℝ)+1)*((N : ℝ)+9)*radialRate^N := by
  have hp0 := log_natCast_nonneg pb.1
  have hp := (Finset.mem_filter.mp hpb).2.2.1
  have hab : (39/20 : ℝ)*N ≤ (203/100 : ℝ)*N := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have he : (∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
      physicalWeight N (log pb.1) y T) =
      (∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
        ownerFourier N (log pb.1) y T).re := by
    change _=Complex.reCLM (∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
      ownerFourier N (log pb.1) y T)
    rw [← Complex.reCLM.intervalIntegral_comp_comm
      (ownerFourier_integral N (log pb.1) y).1.intervalIntegrable]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab]
    intro T hT
    have hn : (32 : ℝ)≤N := by exact_mod_cast hN
    exact ownerPhysical_eq_re N hp0 (by linarith [hT.1]) y
  rw [he]
  have hn := Complex.abs_re_le_norm
    ((u : ℂ)^(N+1)*(∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
      ownerFourier N (log pb.1) y T))
  have he' : ((u : ℂ)^(N+1)*(∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
      ownerFourier N (log pb.1) y T)).re =
      u^(N+1)*(∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
        ownerFourier N (log pb.1) y T).re := by
    rw [← Complex.ofReal_pow,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [he'] at hn
  exact hn.trans (owner_window_bound hu hU hp0 hy N)

private theorem normalized_lattice_envelope {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ) :
    u^(N+1)*radialEnvelope N*exp (-(N : ℝ)/10) ≤
      2*((N : ℝ)+1)*(23/25 : ℝ)^N := by
  have hr : 0 ≤ 2*u*exp (-(1/10 : ℝ)) := by positivity
  have hrate : 2*u*exp (-(1/10 : ℝ)) ≤ 23/25 := by
    rw [exp_neg,mul_inv_le_iff₀ (exp_pos _)]
    have he := add_one_le_exp (1/10 : ℝ)
    have huU : u ≤ (10001/20000 : ℝ) := hU
    nlinarith
  have he : u^(N+1)*radialEnvelope N*exp (-(N : ℝ)/10) =
      2*u*((N : ℝ)+1)*(2*u*exp (-(1/10 : ℝ)))^N := by
    unfold radialEnvelope
    rw [mul_pow,mul_pow,← exp_nat_mul,pow_succ,pow_succ]
    rw [show -(N : ℝ)/10=(N : ℝ)*(-(1/10 : ℝ)) by ring]
    ring
  rw [he]
  have hfac : 2*u*((N : ℝ)+1) ≤ 2*((N : ℝ)+1) := by
    have huU : u ≤ (10001/20000 : ℝ) := hU
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  exact mul_le_mul hfac (pow_le_pow_left₀ hr hrate N) (pow_nonneg hr N) (by positivity)

/-- A fixed rate for the actual integer-row payment, including radial
tails, lattice quadrature and both rounding slivers. -/
def freeRate : ℝ := max radialRate (23/25)

theorem freeRate_bounds : 0 < freeRate ∧ freeRate < 1 := by
  exact ⟨radialRate_bounds.1.trans_le (le_max_left _ _),
    max_lt radialRate_bounds.2 (by norm_num)⟩

/-- This bound is for the signed integer row itself, not merely for its
comparison error. All owner factorial orders have been summed first. -/
theorem free_weight_sum_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 32 ≤ N)
    {pb : ℕ×ℕ} (hpb : pb ∈ freeRows u N) {y : ℝ} (hy : 54 ≤ |y|) :
    |u^(N+1)*(∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
        (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2),
      physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))| ≤
      ((N : ℝ)+1)*(13*(N : ℝ)+33+4*|y|)*freeRate^N := by
  have hq := free_integer_window_error hN hpb y
  have hi := physical_window_source_bound hu hU hN hpb hy
  have hnorm := (mul_le_mul_of_nonneg_left hq (pow_nonneg hu (N+1))).trans
    (by
      calc
        _ = (6*(N : ℝ)+12+2*|y|)*
            (u^(N+1)*radialEnvelope N*exp (-(N : ℝ)/10)) := by ring
        _ ≤ (6*(N : ℝ)+12+2*|y|)*(2*((N : ℝ)+1)*(23/25 : ℝ)^N) :=
          mul_le_mul_of_nonneg_left (normalized_lattice_envelope hu hU N) (by positivity))
  rw [← abs_of_nonneg (pow_nonneg hu (N+1)),← abs_mul] at hnorm
  have h1 := pow_le_pow_left₀ radialRate_bounds.1.le (le_max_left radialRate (23/25)) N
  have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤23/25) (le_max_right radialRate (23/25)) N
  have hi' := hi.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
  have hq' := hnorm.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2*((N : ℝ)+1)))
    (by positivity : 0 ≤ 6*(N : ℝ)+12+2*|y|))
  have ha := abs_add_le
    (u^(N+1)*((∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
        (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2),
      physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))-
        ∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
          physicalWeight N (log pb.1) y T))
    (u^(N+1)*(∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
      physicalWeight N (log pb.1) y T))
  calc
    _ = |u^(N+1)*((∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
        (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2),
      physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))-
        ∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
          physicalWeight N (log pb.1) y T)+
        u^(N+1)*(∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
          physicalWeight N (log pb.1) y T)| := by congr 1; ring
    _ ≤ (6*(N : ℝ)+12+2*|y|)*(2*((N : ℝ)+1)*max radialRate (23/25)^N)+
        ((N : ℝ)+1)*((N : ℝ)+9)*max radialRate (23/25)^N :=
      ha.trans (add_le_add hq' hi')
    _ = _ := by unfold freeRate; ring

/-- The unchanged signed row, with its full owner factorial allocation
and phase inside one unsigned-divisor sum. -/
theorem densityRow_physical (N : ℕ) (L y : ℝ) (p b M X : ℕ) :
    densityRow N L y p b M X =
      ((μ b : ℝ)*ZetaRieszSignedConvolution.pairHinge L p b/(L*(p*b : ℕ)))*
        density (p*b).primeFactors*
          ∑ d ∈ Finset.Ioc M X, physicalWeight N (log p) y (log (p*b : ℕ)+log d)/(d : ℝ) := by
  unfold densityRow
  congr 1
  simp only [ZetaRieszCofactorDiscrepancy.shellWeight]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  · intro d _
    rfl

/-- Every canonical row has only its harmonic outer coefficient. This
does not bound the signed inner main. -/
theorem row_density_coefficient {u : ℝ} {N : ℕ} (hN : 32 ≤ N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    {pb : ℕ×ℕ} (hpb : pb ∈ rows u N) :
    |((μ pb.2 : ℝ)*ZetaRieszSignedConvolution.pairHinge
      (SquarefreeVaughanLogSource.length u N) pb.1 pb.2/
        (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)))*
        density (pb.1*pb.2).primeFactors| ≤ (1 : ℝ)/(pb.1*pb.2 : ℕ) := by
  have hg := rows_geometry hpb
  have hMX := (Finset.mem_filter.mp hpb).2.2.2.2.2
  have hl : log (lower N pb.1 pb.2) ≤
      log (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2) :=
    log_le_log (by exact_mod_cast hg.2.2.2.2.2.2.1) (by exact_mod_cast hMX)
  have hP : log pb.1 ≤ (13/20 : ℝ)*((203/100 : ℝ)*N) := by
    have hshare := hg.2.2.2.2.2.2.2.2.2.2
    have hhi := hg.2.2.2.2.2.2.2.2.1
    nlinarith
  have hn : (32 : ℝ)≤N := by exact_mod_cast hN
  have hL0 : 0 < SquarefreeVaughanLogSource.length u N := by linarith
  have hpb0 : (0 : ℝ)<(pb.1*pb.2 : ℕ) := by
    exact_mod_cast Nat.mul_pos hg.1.pos (by have := hg.2.1; omega)
  have hH := pairHinge_bounds
    (SquarefreeVaughanLogSource.length u N) pb.1 pb.2
  have hHL : ZetaRieszSignedConvolution.pairHinge
      (SquarefreeVaughanLogSource.length u N) pb.1 pb.2 ≤ SquarefreeVaughanLogSource.length u N := by
    linarith [hH.2]
  have hd := density_bounds (pb.1*pb.2).primeFactors
    (fun _ hq => Nat.prime_of_mem_primeFactors hq)
  have hm : |(μ pb.2 : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := pb.2)
  rw [abs_mul,abs_div,abs_mul,abs_of_nonneg hH.1,abs_of_nonneg hd.1,
    abs_of_pos (mul_pos hL0 hpb0)]
  have hnum : |(μ pb.2 : ℝ)| * ZetaRieszSignedConvolution.pairHinge
      (SquarefreeVaughanLogSource.length u N) pb.1 pb.2*density (pb.1*pb.2).primeFactors ≤
      SquarefreeVaughanLogSource.length u N :=
    (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) hH.1) hd.2).trans
      ((mul_le_of_le_one_left hH.1 hm).trans hHL)
  calc
    _ = (|(μ pb.2 : ℝ)| * ZetaRieszSignedConvolution.pairHinge
      (SquarefreeVaughanLogSource.length u N) pb.1 pb.2*density (pb.1*pb.2).primeFactors)/
        (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)) := by ring
    _ ≤ SquarefreeVaughanLogSource.length u N/
        (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)) :=
      div_le_div_of_nonneg_right hnum (mul_pos hL0 hpb0).le
    _ = _ := by field_simp

set_option backward.isDefEq.respectTransparency false in
/-- All outer counts have only harmonic mass after the unsigned leg is
joined and cancelled. No exponential count majorant is charged here. -/
theorem rows_outer_harmonic_bound (u : ℝ) (N : ℕ) :
    (∑ pb ∈ rows u N, (1 : ℝ)/(pb.1*pb.2 : ℕ)) ≤
      (1+(203/100 : ℝ)*N)^2 := by
  let B := ⌊exp ((203/100 : ℝ)*N)⌋₊
  have hBn : 0 < B := Nat.floor_pos.mpr (one_le_exp (by positivity))
  have hB : (0 : ℝ)<B := by exact_mod_cast hBn
  have hlogB : log B ≤ (203/100 : ℝ)*N := by
    have hh := log_le_log hB (Nat.floor_le (exp_pos ((203/100 : ℝ)*N)).le)
    simpa only [log_exp] using hh
  have hsub : rows u N ⊆ (Finset.Icc 1 B).product (Finset.Icc 1 B) := by
    intro pb hpb
    have hg := rows_geometry hpb
    have hb := (Finset.mem_product.mp (Finset.mem_filter.mp hpb).1).2
    have hMX := (Finset.mem_filter.mp hpb).2.2.2.2.2
    have hl : log (lower N pb.1 pb.2) ≤
        log (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2) :=
      log_le_log (by exact_mod_cast hg.2.2.2.2.2.2.1) (by exact_mod_cast hMX)
    have hp : log pb.1 ≤ (13/20 : ℝ)*((203/100 : ℝ)*N) := by
      have hshare := hg.2.2.2.2.2.2.2.2.2.2
      have hhi := hg.2.2.2.2.2.2.2.2.1
      nlinarith
    have hpB : pb.1 ≤ B := by
      apply Nat.le_floor
      rw [← exp_log (by exact_mod_cast hg.1.pos : (0 : ℝ)<pb.1)]
      apply exp_le_exp.mpr
      linarith [Nat.cast_nonneg (α := ℝ) N]
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hg.1.pos,hpB⟩,
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hb).1; omega,(Finset.mem_Icc.mp hb).2⟩⟩
  have hhar : (∑ d ∈ Finset.Icc 1 B, (d : ℝ)⁻¹) ≤ 1+(203/100 : ℝ)*N := by
    have hh := harmonic_le_one_add_log B
    rw [harmonic_eq_sum_Icc,Rat.cast_sum] at hh
    push_cast at hh
    exact hh.trans (add_le_add_right hlogB 1)
  have he : (∑ pb ∈ (Finset.Icc 1 B).product (Finset.Icc 1 B), (1 : ℝ)/(pb.1*pb.2 : ℕ)) =
      (∑ d ∈ Finset.Icc 1 B, (d : ℝ)⁻¹)^2 := by
    calc
      _ = ∑ p ∈ Finset.Icc 1 B, ∑ b ∈ Finset.Icc 1 B, (1 : ℝ)/(p*b : ℕ) :=
        Finset.sum_product (Finset.Icc 1 B) (Finset.Icc 1 B)
          (fun pb : ℕ×ℕ => (1 : ℝ)/(pb.1*pb.2 : ℕ))
      _ = _ := by
        simp only [Nat.cast_mul,one_div,mul_inv]
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul,pow_two]
  calc
    _ ≤ ∑ pb ∈ (Finset.Icc 1 B).product (Finset.Icc 1 B), (1 : ℝ)/(pb.1*pb.2 : ℕ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = _ := he
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity)) hhar 2

/-- Restricting the harmonic outer mass adds no count cost. -/
theorem free_outer_harmonic_bound (u : ℝ) (N : ℕ) :
    (∑ pb ∈ freeRows u N, (1 : ℝ)/(pb.1*pb.2 : ℕ)) ≤
      (1+(203/100 : ℝ)*N)^2 := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => by positivity)).trans (rows_outer_harmonic_bound u N)

/-- The exact signed sum of the full-window canonical density rows. -/
def freeDensityMain (u y : ℝ) (N : ℕ) : ℝ :=
  ∑ pb ∈ freeRows u N,
    densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
      (lower N pb.1 pb.2) (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)

/-- A main-sector budget with a strict geometric rate. It includes
integer quadrature and literal endpoint rounding, not an unpaid main. -/
def freeErrorBudget (y : ℝ) (N : ℕ) : ℝ :=
  9*(33+4*|y|)*((N : ℝ)+1)^4*freeRate^N

theorem tendsto_freeErrorBudget (y : ℝ) : Tendsto (freeErrorBudget y) atTop (𝓝 0) := by
  change Tendsto (fun N => freeErrorBudget y N) atTop (𝓝 0)
  have hh := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 4
    freeRate_bounds.1 freeRate_bounds.2).const_mul (9*(33+4*|y|))
  simpa only [freeErrorBudget,mul_assoc,mul_zero] using hh

/-- A genuine signed arithmetic main payment, across every count and
every radial phase period on the selected original rows. -/
theorem source_scaled_freeDensityMain_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 32 ≤ N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) {y : ℝ} (hy : 54 ≤ |y|) :
    |u^(N+1)*freeDensityMain u y N| ≤ freeErrorBudget y N := by
  let Q := ((N : ℝ)+1)*(13*(N : ℝ)+33+4*|y|)*freeRate^N
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity [freeRate_bounds.1]
  have hb pb (hpb : pb ∈ freeRows u N) :
      |u^(N+1)*densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
        (lower N pb.1 pb.2) (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)| ≤
          (1 : ℝ)/(pb.1*pb.2 : ℕ)*Q := by
    rw [densityRow_physical]
    have he : u^(N+1)*
        (((μ pb.2 : ℝ)*ZetaRieszSignedConvolution.pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2/
          (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)))*density (pb.1*pb.2).primeFactors*
            (∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
              (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2),
                physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))) =
        (((μ pb.2 : ℝ)*ZetaRieszSignedConvolution.pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2/
          (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)))*density (pb.1*pb.2).primeFactors)*
            (u^(N+1)*(∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
              (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2),
                physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))) := by ring
    rw [he,abs_mul]
    exact mul_le_mul (row_density_coefficient hN hL (Finset.mem_filter.mp hpb).1)
      (free_weight_sum_bound hu hU hN hpb hy) (abs_nonneg _) (by positivity)
  unfold freeDensityMain
  rw [Finset.mul_sum]
  have hs := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hb)
  rw [← Finset.sum_mul] at hs
  have hs' := hs.trans (mul_le_mul_of_nonneg_right (free_outer_harmonic_bound u N) hQ)
  have hn : (0 : ℝ)≤N := Nat.cast_nonneg N
  have h1 : 1+(203/100 : ℝ)*N ≤ 3*((N : ℝ)+1) := by linarith
  have h2 : 13*(N : ℝ)+33+4*|y| ≤ (33+4*|y|)*((N : ℝ)+1) := by nlinarith [abs_nonneg y]
  apply hs'.trans
  dsimp [Q,freeErrorBudget]
  have hp := mul_le_mul (pow_le_pow_left₀ (by positivity) h1 2) h2
    (by positivity : 0 ≤ 13*(N : ℝ)+33+4*|y|) (by positivity : 0 ≤ (3*((N : ℝ)+1))^2)
  calc
    _ = ((1+(203/100 : ℝ)*N)^2*(13*(N : ℝ)+33+4*|y|))*
        (((N : ℝ)+1)*freeRate^N) := by ring
    _ ≤ ((3*((N : ℝ)+1))^2*((33+4*|y|)*((N : ℝ)+1)))*
        (((N : ℝ)+1)*freeRate^N) := mul_le_mul_of_nonneg_right hp
      (mul_nonneg (by positivity : 0 ≤ (N : ℝ)+1) (pow_nonneg freeRate_bounds.1.le N))
    _ = _ := by ring

/-- The selected arithmetic density main is independently source-small;
no zero hypothesis or numerical phase data enters this cancellation. -/
theorem tendsto_source_scaled_freeDensityMain {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    Tendsto (fun N => u^(N+1)*freeDensityMain u y N) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := freeErrorBudget y) ?_ (tendsto_freeErrorBudget y)
  have hl := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [hl,eventually_ge_atTop (32 : ℕ)] with N hL hN
  rw [Real.norm_eq_abs]
  exact source_scaled_freeDensityMain_bound (by linarith) hU hN (by nlinarith only [hL]) hy

/-- Precisely the original canonical rows shortened by at least one
moving threshold. They remain SIGNED in the floor, across all counts. -/
def clippedRows (u : ℝ) (N : ℕ) : Finset (ℕ×ℕ) := rows u N \ freeRows u N

/-- The unchanged signed density main on the shortened rows. -/
def clippedDensityMain (u y : ℝ) (N : ℕ) : ℝ :=
  ∑ pb ∈ clippedRows u N,
    densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
      (lower N pb.1 pb.2) (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)

/-- Exact splitting of the current carrier's canonical density main.
The paid sector is removed once, without changing any literal mask. -/
theorem canonicalSignedMain_eq_free_clipped (u y : ℝ) (j : ℕ) :
    canonicalSignedMain u y j = canonicalRemaining u y j+
      freeDensityMain u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)+
      clippedDensityMain u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) := by
  have hs : freeRows u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) ⊆
      rows u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) := Finset.filter_subset _ _
  unfold canonicalSignedMain freeDensityMain clippedDensityMain clippedRows
  rw [← Finset.sum_sdiff hs]
  ring

/-- All old canonical errors plus the independently paid full-window
signed main. No second nonowner or count-boundary charge is introduced. -/
def clippedErrorBudget (y : ℝ) (N : ℕ) : ℝ := canonicalErrorBudget y N+freeErrorBudget y N

theorem tendsto_clippedErrorBudget (y : ℝ) : Tendsto (clippedErrorBudget y) atTop (𝓝 0) := by
  change Tendsto (fun N => clippedErrorBudget y N) atTop (𝓝 0)
  simpa only [clippedErrorBudget,zero_add] using
    (tendsto_canonicalErrorBudget y).add (tendsto_freeErrorBudget y)

/-- A concrete whole-carrier floor advance: the full-window signed rows
are paid geometrically and disappear from the unpaid main. The original
unselected incidences and clipped rows must still be bounded jointly. -/
theorem eventually_joined_floor_with_clipped_rows {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop,
      u^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        (canonicalRemaining u y j-endpointRows u y j+
          clippedDensityMain u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))-
        clippedErrorBudget y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) ≤
      ((u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re := by
  have hf := eventually_joined_floor_without_endpoints hu hU y
  have hl := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [hf,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hl,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (32 : ℕ))] with j hj hL hN
  have hb := (abs_le.mp (source_scaled_freeDensityMain_bound (by linarith) hU hN
    (by nlinarith only [hL]) hy)).1
  rw [canonicalSignedMain_eq_free_clipped] at hj
  unfold clippedErrorBudget
  nlinarith only [hj,hb]

end RiemannGaussian.ZetaRieszFreeRadialRows
