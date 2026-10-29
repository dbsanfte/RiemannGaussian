/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildBudgetMono

/-! # Exact retained original source/fresh report multiplicity
The source-mode report occurs once outside and once per right packet header.
The fresh report similarly occurs once outside and once per eager right table.
Original sparse replay/pullback/routing work remains separately retained.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1ChildSourceLinear
open SemiprimeD1JetAxes SemiprimeD1ChildNetworkClock SemiprimeD1ChildClockFactor

/-- Exact algebraic multiplicity of cached source and fresh reports after the
actual original header supplier `H <= S+H0` is substituted. -/
theorem prefactor_source_linear (old : Context) (extra : List ℕ)
    (p a D A K P T B L E NF Fchild links S W G Z O H0 : ℕ) :
    prefactor old extra p a D A K P T B L E NF Fchild links S W G Z O (S+H0) =
      (Fchild+1)*(S+Z)+
        prefactor old extra p a D A K P T B L E NF Fchild links 0 W G 0 O H0 := by
  unfold prefactor rightPolynomial rightControls
  ring

/-- Complete eager table scale keeps the computed per-packet producer multiplicity. -/
theorem budget_source_linear (old : Context) (extra : List ℕ)
    (p a D A K P T B L E NF Fchild links S W G Z O H0 : ℕ) :
    budget old extra p a D A K P T B L E NF Fchild links S W G Z O (S+H0) =
      ((Fchild+1)*(S+Z)+
        prefactor old extra p a D A K P T B L E NF Fchild links 0 W G 0 O H0)*2^D := by
  unfold budget
  rw [prefactor_source_linear]

end RiemannGaussian.SemiprimeD1ChildSourceLinear
