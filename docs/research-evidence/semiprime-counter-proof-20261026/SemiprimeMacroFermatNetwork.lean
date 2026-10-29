/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitFermatInterpolation
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Arithmetic bridge for the actual macro-Fermat multiplication network

The compiler uses root four at length `n` over `ZMod (2^n+1)`.  This file
proves its principal characters and its two-axis macro identity directly.
Finite convolution and integer carry statements are arithmetic specifications;
no tensor-contraction oracle, complexity claim, or graph validity premise is
substituted for those identities.
-/

namespace RiemannGaussian.SemiprimeMacroFermatNetwork

open scoped BigOperators
open SemiprimeBitFermatArithmetic SemiprimeBitFermatInterpolation

/-- The compiler's dyadic transform length, at least two. -/
def macroLength (d : ℕ) : ℕ := 2^(d+1)

/-- The literal ring used by the compiler, with no primality assumption. -/
abbrev MacroRing (d : ℕ) := ZMod (2^(macroLength d)+1)

/-- The cheap root four has negative half-period in the actual ring. -/
theorem root_four_half_period (d : ℕ) :
    (4 : MacroRing d)^(2^d)= -1 := by
  calc
    (4 : MacroRing d)^(2^d) = (2 : MacroRing d)^(2^(d+1)) := by
      rw [show (4 : MacroRing d)=(2 : MacroRing d)^2 by norm_num, ←pow_mul]
      congr 1
      rw [pow_succ]
      omega
    _ = -1 := by
      have h := fermat_radix (macroLength d)
      rw [Nat.cast_pow, Nat.cast_two] at h
      simpa [MacroRing,macroLength] using h

/-- Every nonconstant compiler character cancels over the composite ring. -/
theorem root_four_cancellation (d : ℕ) {k : ℕ}
    (hk : 0<k ∧ k<macroLength d) :
    (∑ j∈Finset.range (macroLength d),(4 : MacroRing d)^(j*k))=0 :=
  dyadic_character_cancel _ d (root_four_half_period d) hk

/-- The compiler root has the complete transform period. -/
theorem root_four_period (d : ℕ) :
    (4 : MacroRing d)^(macroLength d)=1 := by
  change (4 : MacroRing d)^(2^(d+1))=1
  rw [pow_succ,pow_mul,root_four_half_period]
  norm_num

/-- Length inversion is licensed by the existing physical inverse-two proof. -/
theorem macro_length_unit (d : ℕ) :
    IsUnit (((macroLength d : ℕ) : MacroRing d)) := by
  apply (ZMod.isUnit_iff_coprime _ _).mpr
  apply Nat.Coprime.pow_left
  apply Nat.coprime_two_left.mpr
  refine ⟨2^(macroLength d-1), ?_⟩
  have hp : 0<macroLength d := by unfold macroLength; positivity
  have he := fermat_modulus_odd hp
  omega

/-- Principal root-four delta identity, including the reflected zero slot. -/
theorem root_four_delta (d : ℕ) {i j : ℕ}
    (hi : i<macroLength d) (hj : j<macroLength d) :
    (∑ r∈Finset.range (macroLength d),
      (4 : MacroRing d)^(r*(i+(if j=0 then 0 else macroLength d-j))))=
        if i=j then ((macroLength d : ℕ) : MacroRing d) else 0 := by
  by_cases hj0 : j=0
  · subst j
    simp only [ite_true,Nat.add_zero]
    by_cases hi0 : i=0
    · subst i
      simp only [ite_true,Nat.mul_zero,pow_zero,Finset.sum_const,Finset.card_range,
        nsmul_eq_mul,mul_one]
    · rw [ite_eq_right hi0]
      exact root_four_cancellation d ⟨by omega,hi⟩
  · rw [ite_eq_right hj0]
    by_cases hij : i=j
    · subst i
      rw [ite_eq_left rfl]
      have he : j+(macroLength d-j)=macroLength d := by omega
      rw [he]
      simp only [Nat.mul_comm _ (macroLength d),pow_mul,root_four_period,
        one_pow,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
    · rw [ite_eq_right hij]
      by_cases hlt : i<j
      · exact root_four_cancellation d ⟨by omega,by omega⟩
      · have he : i+(macroLength d-j)=(i-j)+macroLength d := by omega
        rw [he,character_sum_period _ _ _ (root_four_period d)]
        exact root_four_cancellation d ⟨by omega,by omega⟩


/-- Literal rectangle reindexing with the compiler's first digit fastest. -/
theorem sum_range_rectangle {R : Type*} [AddCommMonoid R]
    (f : ℕ→R) (r t : ℕ) :
    (∑ j∈Finset.range (r*t),f j)=
      ∑ j₂∈Finset.range t,∑ j₁∈Finset.range r,f (j₁+r*j₂) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ,Finset.sum_range_add,ih,Finset.sum_range_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    omega

/-- One Fourier value at the actual coefficient positions. -/
def fourier {R : Type*} [CommSemiring R] (w : R) (n : ℕ)
    (a : ℕ→R) (k : ℕ) : R :=
  ∑ j∈Finset.range n,a j*w^(j*k)

/-- The finite two-axis network, including its actual twiddle phase. -/
def macroFourier {R : Type*} [CommSemiring R] (w : R) (r t : ℕ)
    (a : ℕ→R) (k₁ k₂ : ℕ) : R :=
  ∑ j₁∈Finset.range r,
    w^(j₁*k₂)*(w^t)^(j₁*k₁)*
      (∑ j₂∈Finset.range t,a (j₁+r*j₂)*(w^r)^(j₂*k₂))

/-- Actual macro phases differ from the flat phase by a complete period. -/
theorem macro_phase {R : Type*} [CommSemiring R] (w : R) (r t j₁ j₂ k₁ k₂ : ℕ)
    (hw : w^(r*t)=1) :
    w^((j₁+r*j₂)*(k₂+t*k₁))=
      w^(j₁*k₂)*(w^t)^(j₁*k₁)*(w^r)^(j₂*k₂) := by
  have he : (j₁+r*j₂)*(k₂+t*k₁)=
      j₁*k₂+t*(j₁*k₁)+r*(j₂*k₂)+(r*t)*(j₂*k₁) := by ring
  rw [he,pow_add,pow_mul,hw,one_pow,mul_one,pow_add,pow_add]
  simp only [pow_mul]

/-- The two Cooley--Tukey stages in the compiler equal the full DFT.
No macro identity is assumed as input. -/
theorem macroFourier_eq_fourier {R : Type*} [CommSemiring R]
    (w : R) (r t : ℕ) (a : ℕ→R) (k₁ k₂ : ℕ)
    (hw : w^(r*t)=1) :
    macroFourier w r t a k₁ k₂=fourier w (r*t) a (k₂+t*k₁) := by
  unfold macroFourier fourier
  rw [sum_range_rectangle,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j₁ hj₁
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j₂ hj₂
  rw [macro_phase w r t j₁ j₂ k₁ k₂ hw]
  ring

/-- Ordinary finite convolution, before any ring reduction. -/
def convolution {R : Type*} [CommSemiring R] (a b : ℕ→R) (d k : ℕ) : R :=
  ∑ i∈Finset.range d,∑ j∈Finset.range d,if i+j=k then a i*b j else 0

/-- A no-wrap convolution represents the product of the actual digit sums. -/
theorem convolution_evaluation {R : Type*} [CommSemiring R]
    (a b : ℕ→R) (d n : ℕ) (hsize : 2*d≤n) (x : R) :
    (∑ k∈Finset.range n,convolution a b d k*x^k)=
      (∑ i∈Finset.range d,a i*x^i)*(∑ j∈Finset.range d,b j*x^j) := by
  simp only [convolution,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl (fun i hi => by rw [Finset.sum_comm]))
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i+j<n := by
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    omega
  simp only [ite_mul,zero_mul]
  rw [Finset.sum_eq_single (i+j)]
  · rw [ite_eq_left rfl,pow_add]
    ring
  · intro k hk hne
    simp only [ite_eq_right (Ne.symm hne)]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr hij))

/-- Convolution is derived from polynomial evaluation, not supplied as a
pointwise multiplication premise. -/
theorem fourier_convolution {R : Type*} [CommSemiring R]
    (a b : ℕ→R) (d n : ℕ) (hsize : 2*d≤n) (w : R) (k : ℕ) :
    fourier w n (convolution a b d) k=fourier w d a k*fourier w d b k := by
  have hpow (i : ℕ) : (w^k)^i=w^(i*k) := by rw [←pow_mul,Nat.mul_comm]
  simpa only [fourier,hpow] using convolution_evaluation a b d n hsize (w^k)

/-- The actual reflected Fourier sum recovers every coefficient with the
invertible compiler length, without a prime-modulus assumption. -/
theorem fourier_reflection (d : ℕ) (a : ℕ→MacroRing d) {j : ℕ}
    (hj : j<macroLength d) :
    fourier 4 (macroLength d) (fourier 4 (macroLength d) a)
      (if j=0 then 0 else macroLength d-j)=
        (macroLength d : MacroRing d)*a j := by
  unfold fourier
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i∈Finset.range (macroLength d), a i *
        (∑ r∈Finset.range (macroLength d),
          (4 : MacroRing d)^(r*(i+(if j=0 then 0 else macroLength d-j)))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [mul_assoc,←pow_add]
      congr 2
      ring
    _ = ∑ i∈Finset.range (macroLength d),
        if i=j then a i*(macroLength d : MacroRing d) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [root_four_delta d (Finset.mem_range.mp hi) hj]
      simp only [mul_ite,mul_zero]
    _ = _ := by
      simp only [Finset.sum_ite_eq',Finset.mem_range,hj,ite_true]
      exact mul_comm _ _

/-- The normalized inverse is unique: a valid pointwise multiplication
and reflected inverse stage has exactly the ordinary convolution output. -/
theorem inverse_convolution_unique (d : ℕ) (a b output : ℕ→MacroRing d)
    (digits : ℕ) (hsize : 2*digits≤macroLength d)
    (hinverse : ∀ j, j<macroLength d →
      (macroLength d : MacroRing d)*output j=
        fourier 4 (macroLength d)
          (fun k => fourier 4 digits a k*fourier 4 digits b k)
          (if j=0 then 0 else macroLength d-j)) :
    ∀ j, j<macroLength d → output j=convolution a b digits j := by
  intro j hj
  apply (macro_length_unit d).mul_left_cancel
  rw [hinverse j hj]
  have he : (fun k => fourier (4 : MacroRing d) digits a k*
      fourier 4 digits b k)=fourier 4 (macroLength d) (convolution a b digits) := by
    funext k
    exact (fourier_convolution a b digits (macroLength d) hsize 4 k).symm
  rw [he,fourier_reflection d _ hj]

/-- Every ordinary convolution coefficient is bounded by one product per
source digit, rather than by the square of the source length. -/
theorem convolution_bound (a b : ℕ→ℕ) (digits radix k : ℕ)
    (ha : ∀ i, i<digits → a i<radix)
    (hb : ∀ i, i<digits → b i<radix) :
    convolution a b digits k≤digits*radix^2 := by
  unfold convolution
  calc
    _ ≤ ∑ i∈Finset.range digits,radix^2 := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ ∑ j∈Finset.range digits,if j=k-i then radix^2 else 0 := by
          apply Finset.sum_le_sum
          intro j hj
          by_cases he : i+j=k
          · have he' : j=k-i := by omega
            rw [ite_eq_left he,ite_eq_left he']
            have hai := ha i (Finset.mem_range.mp hi)
            have hbj := hb j (Finset.mem_range.mp hj)
            nlinarith
          · rw [ite_eq_right he]
            exact Nat.zero_le _
        _ ≤ radix^2 := by
          simp only [Finset.sum_ite_eq',Finset.mem_range]
          split_ifs <;> omega
    _ = _ := by simp [pow_two]

/-- Casting an ordinary coefficient into the composite Fermat ring does
not change the convolution expression. -/
theorem cast_convolution (a b : ℕ→ℕ) (digits k modulus : ℕ) :
    ((convolution a b digits k : ℕ) : ZMod modulus)=
      convolution (fun i => (a i : ZMod modulus)) (fun i => (b i : ZMod modulus))
        digits k := by
  simp only [convolution,Nat.cast_sum,Nat.cast_ite,Nat.cast_mul,Nat.cast_zero]

/-- Canonical representatives turn modular equality into actual integer
equality; the modulus is not assumed prime. -/
theorem canonical_nat_unique (modulus x y : ℕ) (hx : x<modulus) (hy : y<modulus)
    (he : (x : ZMod modulus)=(y : ZMod modulus)) : x=y := by
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast_of_lt hx,ZMod.val_natCast_of_lt hy] using hv

/-- No-wrap is checked at its actual coefficient bound, then the literal
normalized inverse fixes every canonical integer output coefficient. -/
theorem canonical_inverse_convolution (d : ℕ) (a b output : ℕ→ℕ)
    (digits radix : ℕ) (hsize : 2*digits≤macroLength d)
    (ha : ∀ i, i<digits → a i<radix)
    (hb : ∀ i, i<digits → b i<radix)
    (hbound : digits*radix^2<2^(macroLength d)+1)
    (hcanonical : ∀ j, j<macroLength d → output j<2^(macroLength d)+1)
    (hinverse : ∀ j, j<macroLength d →
      (macroLength d : MacroRing d)*(output j : MacroRing d)=
        fourier 4 (macroLength d)
          (fun k => fourier 4 digits (fun i => (a i : MacroRing d)) k*
            fourier 4 digits (fun i => (b i : MacroRing d)) k)
          (if j=0 then 0 else macroLength d-j)) :
    ∀ j, j<macroLength d → output j=convolution a b digits j := by
  intro j hj
  apply canonical_nat_unique (2^(macroLength d)+1) _ _ (hcanonical j hj)
    (lt_of_le_of_lt (convolution_bound a b digits radix j ha hb) hbound)
  rw [cast_convolution]
  exact inverse_convolution_unique d _ _ (fun i => (output i : MacroRing d))
    digits hsize hinverse j hj

/-- The INTEGER carry equations telescope with their actual end carries.
This prevents interpreting the compiler's carry checks modulo the ring. -/
theorem carry_telescope (coefficient digit carry : ℕ→ℕ) (radix n : ℕ)
    (hcarry : ∀ k, k<n → coefficient k+carry k=digit k+radix*carry (k+1)) :
    (∑ k∈Finset.range n,coefficient k*radix^k)+carry 0=
      (∑ k∈Finset.range n,digit k*radix^k)+carry n*radix^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := ih (fun k hk => hcarry k (by omega))
    have hn := congrArg (fun x : ℕ => x*radix^n) (hcarry n (by omega))
    rw [Finset.sum_range_succ,Finset.sum_range_succ,pow_succ]
    nlinarith

/-- A fully specified arithmetic-stage network implies actual integer
multiplication, including zero end carries. The inverse-convolution bridge
above supplies `hcoefficient` from the actual Fourier-stage equations. -/
theorem integer_network_sound (a b coefficient target carry : ℕ→ℕ)
    (digits n radix : ℕ) (hsize : 2*digits≤n)
    (hcoefficient : ∀ k, k<n → coefficient k=convolution a b digits k)
    (hcarry : ∀ k, k<n → coefficient k+carry k=target k+radix*carry (k+1))
    (hfirst : carry 0=0) (hlast : carry n=0) :
    (∑ i∈Finset.range digits,a i*radix^i)*
      (∑ j∈Finset.range digits,b j*radix^j)=
        ∑ k∈Finset.range n,target k*radix^k := by
  have hc := carry_telescope coefficient target carry radix n hcarry
  rw [hfirst,hlast,Nat.zero_mul,Nat.add_zero,Nat.add_zero] at hc
  rw [←convolution_evaluation a b digits n hsize radix]
  rw [←hc]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hcoefficient k (Finset.mem_range.mp hk)]

/-- The compiler's quarter-length radix gives a genuine integer no-wrap
bound, even using the weaker `3*bits≤n` sufficient condition. -/
theorem compiler_no_wrap (digits bits n : ℕ) (hdigits : digits≤bits)
    (hbits : 3*bits≤n) : digits*(2^bits)^2<2^n+1 := by
  have hall : ∀ bits : ℕ, bits≤2^bits := by
    intro bits
    induction bits with
    | zero => norm_num
    | succ bits ih => rw [pow_succ]; nlinarith [Nat.one_le_pow bits 2 (by omega)]
  have hp := hall bits
  have he : (2^bits : ℕ)*(2^bits)^2=2^(3*bits) := by
    rw [←pow_mul,←pow_add]
    congr 1
    omega
  have hm := Nat.mul_le_mul_right ((2^bits)^2) (le_trans hdigits hp)
  rw [he] at hm
  have hh : (2 : ℕ)^(3*bits)≤2^n := Nat.pow_le_pow_right (by omega) hbits
  omega

/-- Splitting off the constant digit exposes the exact radix-tail relation. -/
theorem radix_sum_succ (a : ℕ→ℕ) (radix n : ℕ) :
    (∑ k∈Finset.range (n+1),a k*radix^k)=
      a 0+radix*(∑ k∈Finset.range n,a (k+1)*radix^k) := by
  rw [Finset.sum_range_succ']
  simp only [pow_zero,Nat.mul_one,pow_succ,Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Equal integer digit evaluations admit actual nonnegative integer
carries with zero terminal carry. Thus carry soundness has a converse,
without requiring a modular or pre-supplied carry witness. -/
theorem integer_carries_exist (coefficient target : ℕ→ℕ) (radix n start : ℕ)
    (hbase : 0<radix) (hdigit : ∀ k, k<n → target k<radix)
    (heval : (∑ k∈Finset.range n,coefficient k*radix^k)+start=
      ∑ k∈Finset.range n,target k*radix^k) :
    ∃ carry : ℕ→ℕ, carry 0=start ∧ carry n=0 ∧
      ∀ k, k<n → coefficient k+carry k=target k+radix*carry (k+1) := by
  induction n generalizing coefficient target start with
  | zero =>
    have hs : start=0 := by simpa using heval
    exact ⟨fun _ => 0,hs.symm,rfl,by omega⟩
  | succ n ih =>
    rw [radix_sum_succ,radix_sum_succ] at heval
    let next := (coefficient 0+start)/radix
    have ht := hdigit 0 (by omega)
    have hmod : (coefficient 0+start)%radix=target 0 := by
      have hh := congrArg (fun x : ℕ => x%radix) heval
      simpa [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt ht] using hh
    have hstep : coefficient 0+start=target 0+radix*next := by
      have hh := Nat.mod_add_div (coefficient 0+start) radix
      rw [hmod] at hh
      exact hh.symm
    have htail : (∑ k∈Finset.range n,coefficient (k+1)*radix^k)+next=
        ∑ k∈Finset.range n,target (k+1)*radix^k := by
      nlinarith
    obtain ⟨tail,hfirst,hlast,hrest⟩ := ih
      (fun k => coefficient (k+1)) (fun k => target (k+1)) next
      (fun k hk => hdigit (k+1) (by omega)) htail
    refine ⟨fun k => if k=0 then start else tail (k-1),by simp,?_,?_⟩
    · simpa using hlast
    · intro k hk
      cases k with
      | zero => simpa [hfirst] using hstep
      | succ k => simpa using hrest k (by omega)

/-- With fixed digit data and initial carry, all internal carries are
unique on the network's finite range. -/
theorem integer_carries_unique (coefficient target c₁ c₂ : ℕ→ℕ)
    (radix n : ℕ) (hbase : 0<radix) (hfirst : c₁ 0=c₂ 0)
    (h₁ : ∀ k, k<n → coefficient k+c₁ k=target k+radix*c₁ (k+1))
    (h₂ : ∀ k, k<n → coefficient k+c₂ k=target k+radix*c₂ (k+1)) :
    ∀ k, k≤n → c₁ k=c₂ k := by
  intro k hk
  induction k with
  | zero => exact hfirst
  | succ k ih =>
    have he := ih (by omega)
    have ha := h₁ k (by omega)
    have hb := h₂ k (by omega)
    nlinarith

/-- Exact arithmetic interface of the compiler's canonical inverse and
INTEGER carry vertices. Forward macro vertices are the defined `macroFourier`
and are proved equal to their flat values above, rather than postulated. -/
def ArithmeticNetworkValid (d : ℕ) (a b target output carry : ℕ→ℕ)
    (digits radix : ℕ) : Prop :=
  (∀ j, j<macroLength d → output j<2^(macroLength d)+1) ∧
  (∀ j, j<macroLength d →
    (macroLength d : MacroRing d)*(output j : MacroRing d)=
      fourier 4 (macroLength d)
        (fun k => fourier 4 digits (fun i => (a i : MacroRing d)) k*
          fourier 4 digits (fun i => (b i : MacroRing d)) k)
        (if j=0 then 0 else macroLength d-j)) ∧
  carry 0=0 ∧ carry (macroLength d)=0 ∧
  (∀ k, k<macroLength d → output k+carry k=target k+radix*carry (k+1))

/-- Complete arithmetic soundness AND existence: valid canonical Fourier,
point-product, inverse, and integer carry stages exist exactly for a true
integer digit multiplication. This does not assert a Boolean-graph compiler
correctness theorem: bit-port wiring/representation is a separate interface. -/
theorem arithmetic_network_iff (d : ℕ) (a b target : ℕ→ℕ)
    (digits radix : ℕ) (hbase : 0<radix) (hsize : 2*digits≤macroLength d)
    (ha : ∀ i, i<digits → a i<radix)
    (hb : ∀ i, i<digits → b i<radix)
    (ht : ∀ i, i<macroLength d → target i<radix)
    (hbound : digits*radix^2<2^(macroLength d)+1) :
    (∃ output carry,ArithmeticNetworkValid d a b target output carry digits radix) ↔
      (∑ i∈Finset.range digits,a i*radix^i)*
        (∑ j∈Finset.range digits,b j*radix^j)=
          ∑ k∈Finset.range (macroLength d),target k*radix^k := by
  constructor
  · rintro ⟨output,carry,hcanon,hinverse,hfirst,hlast,hcarry⟩
    exact integer_network_sound a b output target carry digits (macroLength d) radix hsize
      (canonical_inverse_convolution d a b output digits radix hsize ha hb hbound
        hcanon hinverse) hcarry hfirst hlast
  · intro heval
    let output := convolution a b digits
    have heval' : (∑ k∈Finset.range (macroLength d),output k*radix^k)+0=
        ∑ k∈Finset.range (macroLength d),target k*radix^k := by
      rw [Nat.add_zero,convolution_evaluation a b digits (macroLength d) hsize radix]
      exact heval
    obtain ⟨carry,hfirst,hlast,hcarry⟩ := integer_carries_exist output target radix
      (macroLength d) 0 hbase ht heval'
    refine ⟨output,carry,?_,?_,hfirst,hlast,hcarry⟩
    · intro j hj
      exact lt_of_le_of_lt (convolution_bound a b digits radix j ha hb) hbound
    · intro j hj
      have he : (fun k => fourier (4 : MacroRing d) digits (fun i => (a i : MacroRing d)) k*
          fourier 4 digits (fun i => (b i : MacroRing d)) k)=
            fourier 4 (macroLength d) (fun i => (output i : MacroRing d)) := by
        funext k
        simp only [output,cast_convolution]
        exact (fourier_convolution _ _ digits (macroLength d) hsize 4 k).symm
      rw [he,fourier_reflection d _ hj]

/-- The carry witnesses just constructed fit below the same coefficient
bound when the digit radix is at least two, licensing finite physical words. -/
theorem integer_carry_bound (coefficient target carry : ℕ→ℕ)
    (radix n bound : ℕ) (hbase : 2≤radix) (hfirst : carry 0=0)
    (hcoeff : ∀ k, k<n → coefficient k≤bound)
    (hcarry : ∀ k, k<n → coefficient k+carry k=target k+radix*carry (k+1)) :
    ∀ k, k≤n → carry k≤bound := by
  intro k hk
  induction k with
  | zero => rw [hfirst]; omega
  | succ k ih =>
    have hp := ih (by omega)
    have hc := hcoeff k (by omega)
    have he := hcarry k (by omega)
    nlinarith

/-- All canonical inverse coefficients and all internal carries are
unique on the finite arithmetic network, not only its terminal product. -/
theorem arithmetic_network_unique (d : ℕ) (a b target output₁ output₂ carry₁ carry₂ : ℕ→ℕ)
    (digits radix : ℕ) (hbase : 0<radix) (hsize : 2*digits≤macroLength d)
    (ha : ∀ i, i<digits → a i<radix)
    (hb : ∀ i, i<digits → b i<radix)
    (hbound : digits*radix^2<2^(macroLength d)+1)
    (h₁ : ArithmeticNetworkValid d a b target output₁ carry₁ digits radix)
    (h₂ : ArithmeticNetworkValid d a b target output₂ carry₂ digits radix) :
    (∀ j, j<macroLength d → output₁ j=output₂ j) ∧
      (∀ j, j≤macroLength d → carry₁ j=carry₂ j) := by
  have ho₁ := canonical_inverse_convolution d a b output₁ digits radix hsize ha hb hbound
    h₁.1 h₁.2.1
  have ho₂ := canonical_inverse_convolution d a b output₂ digits radix hsize ha hb hbound
    h₂.1 h₂.2.1
  have ho : ∀ j, j<macroLength d → output₁ j=output₂ j := by
    intro j hj
    rw [ho₁ j hj,ho₂ j hj]
  refine ⟨ho,integer_carries_unique output₁ target carry₁ carry₂ radix (macroLength d)
    hbase (h₁.2.2.1.trans h₂.2.2.1.symm) h₁.2.2.2.2 ?_⟩
  intro k hk
  rw [ho k hk]
  exact h₂.2.2.2.2 k hk

/-- The literal quarter-radix parameters give the stricter physical-word
bound below `2^n`, not merely below the Fermat modulus `2^n+1`. -/
theorem compiler_quarter_strict_bound (digits bits n : ℕ) (hdigits : digits≤bits)
    (hbits : 0<bits) (hn : n=4*bits) : digits*(2^bits)^2<2^n := by
  have hall : ∀ k : ℕ, k≤2^k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; nlinarith [Nat.one_le_pow k 2 (by omega)]
  calc
    digits*(2^bits)^2 ≤ 2^bits*(2^bits)^2 :=
      Nat.mul_le_mul_right _ (le_trans hdigits (hall bits))
    _ = 2^(3*bits) := by rw [←pow_mul,←pow_add]; congr 1; omega
    _ < 2^n := Nat.pow_lt_pow_right (by omega) (by omega)

/-- Every actual carry fits the compiler's strict `n`-bit carry capacity
under its quarter-length radix choice. -/
theorem compiler_carry_capacity (coefficient target carry : ℕ→ℕ)
    (digits bits n : ℕ) (hdigits : digits≤bits) (hbits : 0<bits) (hn : n=4*bits)
    (hfirst : carry 0=0)
    (hcoeff : ∀ k, k<n → coefficient k≤digits*(2^bits)^2)
    (hcarry : ∀ k, k<n → coefficient k+carry k=target k+2^bits*carry (k+1)) :
    ∀ k, k≤n → carry k<2^n := by
  intro k hk
  have hb : 2≤2^bits := by
    calc
      2 = (2 : ℕ)^1 := by norm_num
      _ ≤ 2^bits := Nat.pow_le_pow_right (by omega) hbits
  exact lt_of_le_of_lt
    (integer_carry_bound coefficient target carry (2^bits) n (digits*(2^bits)^2)
      hb hfirst hcoeff hcarry k hk)
    (compiler_quarter_strict_bound digits bits n hdigits hbits hn)

end RiemannGaussian.SemiprimeMacroFermatNetwork
