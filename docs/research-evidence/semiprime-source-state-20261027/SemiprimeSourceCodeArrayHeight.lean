/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceExpressionBound
import RiemannGaussian.SemiprimeHermiteArrayHeight
import RiemannGaussian.SemiprimeLocalExecutionHeight

/-! # All-subtree heights of the actual source array interpreter
Leaf bounds are original constant bounds. Each compiled subtree and its cached
convolution prefixes share a power of that original denominator. The actual
source-constant specialization is supplied by SourceInterpolationHeight.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeSourceCodeArrayHeight
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation
open SemiprimeSourceCodeArrays SemiprimeJetArray SemiprimeJetArrayHeight SemiprimeArrayOps
open SemiprimeHermiteArrayHeight SemiprimeLocalExecutionHeight

/-- Common ORIGINAL representations of every constant leaf, not intermediate advice. -/
def Leaves (d B : ℕ) : PolynomialCode ℚ → Prop
  | .constant c => Representation c d B
  | .indeterminate => True
  | .add p q => Leaves d B p ∧ Leaves d B q
  | .mul p q => Leaves d B p ∧ Leaves d B q

/-- Original-parameter base covering binary addition and finite convolution. -/
def base (J d B : ℕ) : ℕ := (J+2)*(2*d+2*B+4)

/-- The common denominator is positive and dominated by the numeric base. -/
theorem base_guards (J d B : ℕ) :
    d ≤ base J d B ∧ B ≤ base J d B ∧ 2*d ≤ base J d B ∧ J*d ≤ base J d B := by
  unfold base
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Every syntax tree has at least its root node. -/
theorem nodes_positive (p : PolynomialCode ℚ) : 0<nodes p := by
  cases p <;> simp only [nodes] <;> omega

/-- Promote one computed binary-stage representation to its actual parent node. -/
theorem promote_binary {q : ℚ} (J d B u v K : ℕ) (hd : 0<d)
    (hK : K*d ≤ base J d B)
    (hq : Representation q (d^(u+v)) (K*base J d B^(u+v))) :
    Representation q (d^(u+v+1)) (base J d B^(u+v+1)) := by
  have hh := representation_mul hq (representation_one d hd)
  simp only [mul_one] at hh
  apply representation_mono (by simpa only [pow_succ] using hh)
  rw [pow_succ]
  calc
    K*base J d B^(u+v)*d = base J d B^(u+v)*(K*d) := by ring
    _ ≤ base J d B^(u+v)*base J d B := Nat.mul_le_mul_left _ hK

/-- The actual cached coefficient arrays at EVERY syntax node have derived common bounds. -/
theorem compile_representation (J d B : ℕ) (hd : 0<d) (p : PolynomialCode ℚ)
    (hp : Leaves d B p) :
    ArrayBound (compile J p).coefficients J (d^nodes p) (base J d B^nodes p) := by
  have hg := base_guards J d B
  induction p with
  | constant c =>
    intro i hi
    simp only [compile,ofFn_coefficient _ i hi,nodes]
    split_ifs
    · simpa only [pow_one] using representation_mono hp hg.2.1
    · exact representation_mono (representation_zero _) (Nat.zero_le _)
  | indeterminate =>
    intro i hi
    simp only [compile,ofFn_coefficient _ i hi,nodes]
    split_ifs
    · simpa only [pow_one] using representation_mono (representation_one d hd) hg.1
    · exact representation_mono (representation_zero _) (Nat.zero_le _)
  | add p q ihp ihq =>
    have hpa := ihp hp.1
    have hqa := ihq hp.2
    intro i hi
    have hp' := representation_power_extend d (base J d B) (nodes p) (nodes p+nodes q)
      hd hg.1 (by omega) (hpa i hi)
    have hq' := representation_power_extend d (base J d B) (nodes q) (nodes p+nodes q)
      hd hg.1 (by omega) (hqa i hi)
    have hs := representation_add hp' hq'
    have hs' : Representation
        (coefficient (compile J p).coefficients i+coefficient (compile J q).coefficients i)
        (d^(nodes p+nodes q)) (2*base J d B^(nodes p+nodes q)) := by
      simpa only [two_mul] using hs
    have h := promote_binary J d B (nodes p) (nodes q) 2 hd hg.2.2.1 hs'
    simpa only [compile,nodes,SemiprimeArrayOps.addJet_coefficient _ _ J i hi] using h
  | mul p q ihp ihq =>
    have hpa := ihp hp.1
    have hqa := ihq hp.2
    intro i hi
    have hh := multiply_representation (compile J p).coefficients (compile J q).coefficients
      (d^nodes p) (d^nodes q) (base J d B^nodes p) (base J d B^nodes q) J hpa hqa i hi
    have hh' : Representation
        (coefficient (multiply (compile J p).coefficients (compile J q).coefficients J).coefficients i)
        (d^(nodes p+nodes q)) (J*base J d B^(nodes p+nodes q)) := by
      simpa only [pow_add,Nat.mul_assoc] using hh
    have h := promote_binary J d B (nodes p) (nodes q) J hd hg.2.2.2 hh'
    exact h

/-- Literal subexpression relation for the executed syntax tree. -/
inductive Subcode : PolynomialCode ℚ → PolynomialCode ℚ → Prop
  | refl (p) : Subcode p p
  | addLeft {p q a} : Subcode a p → Subcode a (.add p q)
  | addRight {p q a} : Subcode a q → Subcode a (.add p q)
  | mulLeft {p q a} : Subcode a p → Subcode a (.mul p q)
  | mulRight {p q a} : Subcode a q → Subcode a (.mul p q)

/-- A genuine subtree has no more nodes than its parent. -/
theorem subcode_nodes {p q : PolynomialCode ℚ} (h : Subcode p q) : nodes p ≤ nodes q := by
  induction h with
  | refl => exact le_rfl
  | addLeft h ih => change _ ≤ _+_+1;omega
  | addRight h ih => change _ ≤ _+_+1;omega
  | mulLeft h ih => change _ ≤ _+_+1;omega
  | mulRight h ih => change _ ≤ _+_+1;omega

/-- Original constant bounds restrict to all actual subtrees. -/
theorem subcode_leaves {p q : PolynomialCode ℚ} (d B : ℕ)
    (h : Subcode p q) (hq : Leaves d B q) : Leaves d B p := by
  induction h with
  | refl => exact hq
  | addLeft h ih => exact ih hq.1
  | addRight h ih => exact ih hq.2
  | mulLeft h ih => exact ih hq.1
  | mulRight h ih => exact ih hq.2

/-- One ORIGINAL full-tree node cap bounds all recursively cached arrays. -/
theorem subtree_representation (J d B N : ℕ) (hd : 0<d) (p q : PolynomialCode ℚ)
    (hp : Leaves d B p) (hN : nodes p ≤ N) (hq : Subcode q p) :
    ArrayBound (compile J q).coefficients J (d^N) (base J d B^N) := by
  have h := compile_representation J d B hd q (subcode_leaves d B hq hp)
  intro i hi
  exact representation_power_extend d (base J d B) (nodes q) N hd (base_guards J d B).1
    ((subcode_nodes hq).trans hN) (h i hi)

/-- Every convolution slice, including all prefixes and suffixes, has the parent-node cap. -/
theorem convolution_slice_representation (J d B : ℕ) (hd : 0<d) (p q : PolynomialCode ℚ)
    (hp : Leaves d B p) (hq : Leaves d B q) (n start len : ℕ)
    (hn : n<J) (hlen : start+len ≤ n+1) :
    Representation (∑ i∈Finset.range len,
      coefficient (compile J p).coefficients (start+i)*
        coefficient (compile J q).coefficients (n-(start+i)))
      (d^nodes (.mul p q)) (base J d B^nodes (.mul p q)) := by
  have hpa := compile_representation J d B hd p hp
  have hqa := compile_representation J d B hd q hq
  have hs := representation_sum (Finset.range len)
    (fun i => coefficient (compile J p).coefficients (start+i)*
      coefficient (compile J q).coefficients (n-(start+i)))
    (d^nodes p*d^nodes q) (base J d B^nodes p*base J d B^nodes q) (by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact representation_mul (hpa _ (by omega)) (hqa _ (by omega)))
  have hs' : Representation (∑ i∈Finset.range len,
      coefficient (compile J p).coefficients (start+i)*
        coefficient (compile J q).coefficients (n-(start+i)))
      (d^(nodes p+nodes q)) (J*base J d B^(nodes p+nodes q)) := by
    apply representation_mono (by simpa only [Finset.card_range,pow_add,Nat.mul_assoc] using hs)
    have hlenJ : len ≤ J := by omega
    simpa only [pow_add,Nat.mul_assoc] using
      Nat.mul_le_mul_right (base J d B^nodes p*base J d B^nodes q) hlenJ
  exact promote_binary J d B (nodes p) (nodes q) J hd (base_guards J d B).2.2.2 hs'

/-- Every actually cached ascending dot-prefix in multiplication has the parent cap. -/
theorem compile_dotPrefix_representation (J d B : ℕ) (hd : 0<d) (p q : PolynomialCode ℚ)
    (hp : Leaves d B p) (hq : Leaves d B q) (n len : ℕ) (hn : n<J) (hlen : len ≤ n) :
    Representation (dotPrefix (compile J p).coefficients (compile J q).coefficients (n-1) len).value
      (d^nodes (.mul p q)) (base J d B^nodes (.mul p q)) := by
  have h := convolution_slice_representation J d B hd p q hp hq n 1 len hn (by omega)
  rw [dotPrefix_value]
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  congr 2 <;> omega

/-- The original full-tree cap controls every convolution slice at every multiplication subtree. -/
theorem subtree_convolution_slice (J d B N : ℕ) (hd : 0<d)
    (root p q : PolynomialCode ℚ) (hroot : Leaves d B root) (hN : nodes root ≤ N)
    (hsub : Subcode (.mul p q) root) (n start len : ℕ) (hn : n<J) (hlen : start+len ≤ n+1) :
    Representation (∑ i∈Finset.range len,
      coefficient (compile J p).coefficients (start+i)*
        coefficient (compile J q).coefficients (n-(start+i))) (d^N) (base J d B^N) := by
  have hpq := subcode_leaves d B hsub hroot
  exact representation_power_extend d (base J d B) (nodes (.mul p q)) N hd
    (base_guards J d B).1 ((subcode_nodes hsub).trans hN)
    (convolution_slice_representation J d B hd p q hpq.1 hpq.2 n start len hn hlen)

/-- Every actual ascending multiplication prefix array has the parent-node cap. -/
theorem multiply_prefix_representation (J d B : ℕ) (hd : 0<d) (p q : PolynomialCode ℚ)
    (hp : Leaves d B p) (hq : Leaves d B q) (k : ℕ) (hk : k ≤ J) :
    ArrayBound (multiply (compile J p).coefficients (compile J q).coefficients k).coefficients
      k (d^nodes (.mul p q)) (base J d B^nodes (.mul p q)) := by
  intro i hi
  have h := convolution_slice_representation J d B hd p q hp hq i 0 (i+1) (by omega) (by omega)
  rw [multiply_coefficient _ _ k i hi]
  simpa only [Nat.zero_add] using h

/-- Every cached prefix product at every genuine subtree shares the ORIGINAL root cap. -/
theorem subtree_multiply_prefix (J d B N : ℕ) (hd : 0<d)
    (root p q : PolynomialCode ℚ) (hroot : Leaves d B root) (hN : nodes root ≤ N)
    (hsub : Subcode (.mul p q) root) (k : ℕ) (hk : k ≤ J) :
    ArrayBound (multiply (compile J p).coefficients (compile J q).coefficients k).coefficients
      k (d^N) (base J d B^N) := by
  have hpq := subcode_leaves d B hsub hroot
  have h := multiply_prefix_representation J d B hd p q hpq.1 hpq.2 k hk
  intro i hi
  exact representation_power_extend d (base J d B) (nodes (.mul p q)) N hd
    (base_guards J d B).1 ((subcode_nodes hsub).trans hN) (h i hi)

end RiemannGaussian.SemiprimeSourceCodeArrayHeight
