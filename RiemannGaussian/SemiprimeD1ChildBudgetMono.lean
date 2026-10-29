/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildNetworkClock

/-! # Monotone original metadata substitution in the actual child report
Only explicit scalar/report dimensions are enlarged. This does not identify
clock reports by value equality or omit repeated producer reports.
-/
set_option autoImplicit false
set_option maxHeartbeats 120000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ChildBudgetMono
open SemiprimeD1JetAxes SemiprimeD1ChildNetworkClock SemiprimeD1ChildClockFactor

/-- Original graph/data/header report suppliers may be substituted at all their
actual occurrences in the fixed arithmetic prefactor. -/
theorem prefactor_mono (old : Context) (extra : List ℕ)
    (p a D A K P T B L E NF Fchild links S W G Z O H Fchild' links' S' W' G' Z' O' H' : ℕ)
    (hF : Fchild ≤ Fchild') (hl : links ≤ links') (hS : S ≤ S') (hW : W ≤ W')
    (hG : G ≤ G') (hZ : Z ≤ Z') (hO : O ≤ O') (hH : H ≤ H') :
    prefactor old extra p a D A K P T B L E NF Fchild links S W G Z O H ≤
      prefactor old extra p a D A K P T B L E NF Fchild' links' S' W' G' Z' O' H' := by
  unfold prefactor leftPolynomial rightPolynomial rightControls
  gcongr

/-- Whole actual child-network clock envelope preserves the explicit common eager scale. -/
theorem budget_mono (old : Context) (extra : List ℕ)
    (p a D A K P T B L E NF Fchild links S W G Z O H Fchild' links' S' W' G' Z' O' H' : ℕ)
    (hF : Fchild ≤ Fchild') (hl : links ≤ links') (hS : S ≤ S') (hW : W ≤ W')
    (hG : G ≤ G') (hZ : Z ≤ Z') (hO : O ≤ O') (hH : H ≤ H') :
    budget old extra p a D A K P T B L E NF Fchild links S W G Z O H ≤
      budget old extra p a D A K P T B L E NF Fchild' links' S' W' G' Z' O' H' :=
  Nat.mul_le_mul_right _ (prefactor_mono old extra p a D A K P T B L E NF Fchild links S W G Z O H
    Fchild' links' S' W' G' Z' O' H' hF hl hS hW hG hZ hO hH)

end RiemannGaussian.SemiprimeD1ChildBudgetMono
