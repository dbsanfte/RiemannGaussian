/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszContinuumCascade

/-! # Signed cancellation in the six-small-prime hinge sum

The finite case split retains the negative triple hinges while bounding
the positive pair hinges. Every leaf is a real linear inequality checked
by Lean; numerical optimization is only a guide to the split order. -/

namespace RiemannGaussian.ZetaRieszSixSmallHinges
noncomputable section
open scoped BigOperators Classical

set_option maxHeartbeats 16000000 in
/-- All six ordered logarithms below the cutoff share one least-logarithm
upper budget once their total is at least three cutoffs. -/
theorem pair_triple_bound {a b c d e f D : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hde : d ≤ e) (hef : e ≤ f) (hf : f ≤ D)
    (ht : 3*D ≤ a+b+c+d+e+f) :
    a+b+c+d+e+f-5*D+
      (max 0 (D-(a+b))+
       max 0 (D-(a+c))+
       max 0 (D-(a+d))+
       max 0 (D-(a+e))+
       max 0 (D-(a+f))+
       max 0 (D-(b+c))+
       max 0 (D-(b+d))+
       max 0 (D-(b+e))+
       max 0 (D-(b+f))+
       max 0 (D-(c+d))+
       max 0 (D-(c+e))+
       max 0 (D-(c+f))+
       max 0 (D-(d+e))+
       max 0 (D-(d+f))+
       max 0 (D-(e+f)))-
      (max 0 (D-(a+b+c))+
       max 0 (D-(a+b+d))+
       max 0 (D-(a+b+e))+
       max 0 (D-(a+b+f))+
       max 0 (D-(a+c+d))+
       max 0 (D-(a+c+e))+
       max 0 (D-(a+c+f))+
       max 0 (D-(a+d+e))+
       max 0 (D-(a+d+f))+
       max 0 (D-(a+e+f))+
       max 0 (D-(b+c+d))+
       max 0 (D-(b+c+e))+
       max 0 (D-(b+c+f))+
       max 0 (D-(b+d+e))+
       max 0 (D-(b+d+f))+
       max 0 (D-(b+e+f))+
       max 0 (D-(c+d+e))+
       max 0 (D-(c+d+f))+
       max 0 (D-(c+e+f))+
       max 0 (D-(d+e+f))) ≤ a := by
  have h11 : D-(c+f) ≤ 0 := by linarith
  have h13 : D-(d+f) ≤ 0 := by linarith
  have h14 : D-(e+f) ≤ 0 := by linarith
  have h20 : D-(a+c+e) ≤ 0 := by linarith
  have h21 : D-(a+c+f) ≤ 0 := by linarith
  have h22 : D-(a+d+e) ≤ 0 := by linarith
  have h23 : D-(a+d+f) ≤ 0 := by linarith
  have h24 : D-(a+e+f) ≤ 0 := by linarith
  have h26 : D-(b+c+e) ≤ 0 := by linarith
  have h27 : D-(b+c+f) ≤ 0 := by linarith
  have h28 : D-(b+d+e) ≤ 0 := by linarith
  have h29 : D-(b+d+f) ≤ 0 := by linarith
  have h30 : D-(b+e+f) ≤ 0 := by linarith
  have h31 : D-(c+d+e) ≤ 0 := by linarith
  have h32 : D-(c+d+f) ≤ 0 := by linarith
  have h33 : D-(c+e+f) ≤ 0 := by linarith
  have h34 : D-(d+e+f) ≤ 0 := by linarith
  rw [max_eq_left h11, max_eq_left h13, max_eq_left h14, max_eq_left h20, max_eq_left h21, max_eq_left h22, max_eq_left h23, max_eq_left h24, max_eq_left h26, max_eq_left h27, max_eq_left h28, max_eq_left h29, max_eq_left h30, max_eq_left h31, max_eq_left h32, max_eq_left h33, max_eq_left h34]
  rcases le_total (D-(a+b)) 0 with h0 | h0
  · rw [max_eq_left h0]
    have h1 : D-(a+c) ≤ 0 := by linarith
    have h2 : D-(a+d) ≤ 0 := by linarith
    have h3 : D-(a+e) ≤ 0 := by linarith
    have h4 : D-(a+f) ≤ 0 := by linarith
    have h5 : D-(b+c) ≤ 0 := by linarith
    have h6 : D-(b+d) ≤ 0 := by linarith
    have h7 : D-(b+e) ≤ 0 := by linarith
    have h8 : D-(b+f) ≤ 0 := by linarith
    have h9 : D-(c+d) ≤ 0 := by linarith
    have h10 : D-(c+e) ≤ 0 := by linarith
    have h12 : D-(d+e) ≤ 0 := by linarith
    have h15 : D-(a+b+c) ≤ 0 := by linarith
    have h16 : D-(a+b+d) ≤ 0 := by linarith
    have h17 : D-(a+b+e) ≤ 0 := by linarith
    have h18 : D-(a+b+f) ≤ 0 := by linarith
    have h19 : D-(a+c+d) ≤ 0 := by linarith
    have h25 : D-(b+c+d) ≤ 0 := by linarith
    rw [max_eq_left h1, max_eq_left h2, max_eq_left h3, max_eq_left h4, max_eq_left h5, max_eq_left h6, max_eq_left h7, max_eq_left h8, max_eq_left h9, max_eq_left h10, max_eq_left h12, max_eq_left h15, max_eq_left h16, max_eq_left h17, max_eq_left h18, max_eq_left h19, max_eq_left h25]
    linarith
  · rw [max_eq_right h0]
    rcases le_total (D-(a+c)) 0 with h1 | h1
    · rw [max_eq_left h1]
      have h2 : D-(a+d) ≤ 0 := by linarith
      have h3 : D-(a+e) ≤ 0 := by linarith
      have h4 : D-(a+f) ≤ 0 := by linarith
      have h5 : D-(b+c) ≤ 0 := by linarith
      have h6 : D-(b+d) ≤ 0 := by linarith
      have h7 : D-(b+e) ≤ 0 := by linarith
      have h8 : D-(b+f) ≤ 0 := by linarith
      have h9 : D-(c+d) ≤ 0 := by linarith
      have h10 : D-(c+e) ≤ 0 := by linarith
      have h12 : D-(d+e) ≤ 0 := by linarith
      have h15 : D-(a+b+c) ≤ 0 := by linarith
      have h16 : D-(a+b+d) ≤ 0 := by linarith
      have h17 : D-(a+b+e) ≤ 0 := by linarith
      have h18 : D-(a+b+f) ≤ 0 := by linarith
      have h19 : D-(a+c+d) ≤ 0 := by linarith
      have h25 : D-(b+c+d) ≤ 0 := by linarith
      rw [max_eq_left h2, max_eq_left h3, max_eq_left h4, max_eq_left h5, max_eq_left h6, max_eq_left h7, max_eq_left h8, max_eq_left h9, max_eq_left h10, max_eq_left h12, max_eq_left h15, max_eq_left h16, max_eq_left h17, max_eq_left h18, max_eq_left h19, max_eq_left h25]
      linarith
    · rw [max_eq_right h1]
      rcases le_total (D-(a+d)) 0 with h2 | h2
      · rw [max_eq_left h2]
        have h3 : D-(a+e) ≤ 0 := by linarith
        have h4 : D-(a+f) ≤ 0 := by linarith
        have h6 : D-(b+d) ≤ 0 := by linarith
        have h7 : D-(b+e) ≤ 0 := by linarith
        have h8 : D-(b+f) ≤ 0 := by linarith
        have h9 : D-(c+d) ≤ 0 := by linarith
        have h10 : D-(c+e) ≤ 0 := by linarith
        have h12 : D-(d+e) ≤ 0 := by linarith
        have h16 : D-(a+b+d) ≤ 0 := by linarith
        have h17 : D-(a+b+e) ≤ 0 := by linarith
        have h18 : D-(a+b+f) ≤ 0 := by linarith
        have h19 : D-(a+c+d) ≤ 0 := by linarith
        have h25 : D-(b+c+d) ≤ 0 := by linarith
        rw [max_eq_left h3, max_eq_left h4, max_eq_left h6, max_eq_left h7, max_eq_left h8, max_eq_left h9, max_eq_left h10, max_eq_left h12, max_eq_left h16, max_eq_left h17, max_eq_left h18, max_eq_left h19, max_eq_left h25]
        rcases le_total (D-(b+c)) 0 with h5 | h5
        · rw [max_eq_left h5]
          have h15 : D-(a+b+c) ≤ 0 := by linarith
          rw [max_eq_left h15]
          linarith
        · rw [max_eq_right h5]
          rcases le_total (D-(a+b+c)) 0 with h15 | h15
          · rw [max_eq_left h15]
            linarith
          · rw [max_eq_right h15]
            linarith
      · rw [max_eq_right h2]
        rcases le_total (D-(a+e)) 0 with h3 | h3
        · rw [max_eq_left h3]
          have h4 : D-(a+f) ≤ 0 := by linarith
          have h7 : D-(b+e) ≤ 0 := by linarith
          have h8 : D-(b+f) ≤ 0 := by linarith
          have h10 : D-(c+e) ≤ 0 := by linarith
          have h12 : D-(d+e) ≤ 0 := by linarith
          have h17 : D-(a+b+e) ≤ 0 := by linarith
          have h18 : D-(a+b+f) ≤ 0 := by linarith
          rw [max_eq_left h4, max_eq_left h7, max_eq_left h8, max_eq_left h10, max_eq_left h12, max_eq_left h17, max_eq_left h18]
          rcases le_total (D-(b+c)) 0 with h5 | h5
          · rw [max_eq_left h5]
            have h6 : D-(b+d) ≤ 0 := by linarith
            have h9 : D-(c+d) ≤ 0 := by linarith
            have h15 : D-(a+b+c) ≤ 0 := by linarith
            have h16 : D-(a+b+d) ≤ 0 := by linarith
            have h19 : D-(a+c+d) ≤ 0 := by linarith
            have h25 : D-(b+c+d) ≤ 0 := by linarith
            rw [max_eq_left h6, max_eq_left h9, max_eq_left h15, max_eq_left h16, max_eq_left h19, max_eq_left h25]
            linarith
          · rw [max_eq_right h5]
            rcases le_total (D-(b+d)) 0 with h6 | h6
            · rw [max_eq_left h6]
              have h9 : D-(c+d) ≤ 0 := by linarith
              have h16 : D-(a+b+d) ≤ 0 := by linarith
              have h19 : D-(a+c+d) ≤ 0 := by linarith
              have h25 : D-(b+c+d) ≤ 0 := by linarith
              rw [max_eq_left h9, max_eq_left h16, max_eq_left h19, max_eq_left h25]
              rcases le_total (D-(a+b+c)) 0 with h15 | h15
              · rw [max_eq_left h15]
                linarith
              · rw [max_eq_right h15]
                linarith
            · rw [max_eq_right h6]
              rcases le_total (D-(c+d)) 0 with h9 | h9
              · rw [max_eq_left h9]
                have h19 : D-(a+c+d) ≤ 0 := by linarith
                have h25 : D-(b+c+d) ≤ 0 := by linarith
                rw [max_eq_left h19, max_eq_left h25]
                rcases le_total (D-(a+b+c)) 0 with h15 | h15
                · rw [max_eq_left h15]
                  have h16 : D-(a+b+d) ≤ 0 := by linarith
                  rw [max_eq_left h16]
                  linarith
                · rw [max_eq_right h15]
                  rcases le_total (D-(a+b+d)) 0 with h16 | h16
                  · rw [max_eq_left h16]
                    linarith
                  · rw [max_eq_right h16]
                    linarith
              · rw [max_eq_right h9]
                rcases le_total (D-(a+b+c)) 0 with h15 | h15
                · rw [max_eq_left h15]
                  have h16 : D-(a+b+d) ≤ 0 := by linarith
                  have h19 : D-(a+c+d) ≤ 0 := by linarith
                  have h25 : D-(b+c+d) ≤ 0 := by linarith
                  rw [max_eq_left h16, max_eq_left h19, max_eq_left h25]
                  linarith
                · rw [max_eq_right h15]
                  rcases le_total (D-(a+b+d)) 0 with h16 | h16
                  · rw [max_eq_left h16]
                    have h19 : D-(a+c+d) ≤ 0 := by linarith
                    have h25 : D-(b+c+d) ≤ 0 := by linarith
                    rw [max_eq_left h19, max_eq_left h25]
                    linarith
                  · rw [max_eq_right h16]
                    rcases le_total (D-(a+c+d)) 0 with h19 | h19
                    · rw [max_eq_left h19]
                      have h25 : D-(b+c+d) ≤ 0 := by linarith
                      rw [max_eq_left h25]
                      linarith
                    · rw [max_eq_right h19]
                      rcases le_total (D-(b+c+d)) 0 with h25 | h25
                      · rw [max_eq_left h25]
                        linarith
                      · rw [max_eq_right h25]
                        linarith
        · rw [max_eq_right h3]
          have h25 : D-(b+c+d) ≤ 0 := by linarith
          rw [max_eq_left h25]
          rcases le_total (D-(a+f)) 0 with h4 | h4
          · rw [max_eq_left h4]
            have h8 : D-(b+f) ≤ 0 := by linarith
            have h18 : D-(a+b+f) ≤ 0 := by linarith
            rw [max_eq_left h8, max_eq_left h18]
            rcases le_total (D-(b+c)) 0 with h5 | h5
            · rw [max_eq_left h5]
              have h6 : D-(b+d) ≤ 0 := by linarith
              have h7 : D-(b+e) ≤ 0 := by linarith
              have h9 : D-(c+d) ≤ 0 := by linarith
              have h10 : D-(c+e) ≤ 0 := by linarith
              have h12 : D-(d+e) ≤ 0 := by linarith
              have h15 : D-(a+b+c) ≤ 0 := by linarith
              have h16 : D-(a+b+d) ≤ 0 := by linarith
              have h17 : D-(a+b+e) ≤ 0 := by linarith
              have h19 : D-(a+c+d) ≤ 0 := by linarith
              rw [max_eq_left h6, max_eq_left h7, max_eq_left h9, max_eq_left h10, max_eq_left h12, max_eq_left h15, max_eq_left h16, max_eq_left h17, max_eq_left h19]
              linarith
            · rw [max_eq_right h5]
              rcases le_total (D-(b+d)) 0 with h6 | h6
              · rw [max_eq_left h6]
                have h7 : D-(b+e) ≤ 0 := by linarith
                have h9 : D-(c+d) ≤ 0 := by linarith
                have h10 : D-(c+e) ≤ 0 := by linarith
                have h12 : D-(d+e) ≤ 0 := by linarith
                have h16 : D-(a+b+d) ≤ 0 := by linarith
                have h17 : D-(a+b+e) ≤ 0 := by linarith
                have h19 : D-(a+c+d) ≤ 0 := by linarith
                rw [max_eq_left h7, max_eq_left h9, max_eq_left h10, max_eq_left h12, max_eq_left h16, max_eq_left h17, max_eq_left h19]
                rcases le_total (D-(a+b+c)) 0 with h15 | h15
                · rw [max_eq_left h15]
                  linarith
                · rw [max_eq_right h15]
                  linarith
              · rw [max_eq_right h6]
                rcases le_total (D-(b+e)) 0 with h7 | h7
                · rw [max_eq_left h7]
                  have h10 : D-(c+e) ≤ 0 := by linarith
                  have h12 : D-(d+e) ≤ 0 := by linarith
                  have h17 : D-(a+b+e) ≤ 0 := by linarith
                  rw [max_eq_left h10, max_eq_left h12, max_eq_left h17]
                  rcases le_total (D-(c+d)) 0 with h9 | h9
                  · rw [max_eq_left h9]
                    have h19 : D-(a+c+d) ≤ 0 := by linarith
                    rw [max_eq_left h19]
                    rcases le_total (D-(a+b+c)) 0 with h15 | h15
                    · rw [max_eq_left h15]
                      have h16 : D-(a+b+d) ≤ 0 := by linarith
                      rw [max_eq_left h16]
                      linarith
                    · rw [max_eq_right h15]
                      rcases le_total (D-(a+b+d)) 0 with h16 | h16
                      · rw [max_eq_left h16]
                        linarith
                      · rw [max_eq_right h16]
                        linarith
                  · rw [max_eq_right h9]
                    rcases le_total (D-(a+b+c)) 0 with h15 | h15
                    · rw [max_eq_left h15]
                      have h16 : D-(a+b+d) ≤ 0 := by linarith
                      have h19 : D-(a+c+d) ≤ 0 := by linarith
                      rw [max_eq_left h16, max_eq_left h19]
                      linarith
                    · rw [max_eq_right h15]
                      rcases le_total (D-(a+b+d)) 0 with h16 | h16
                      · rw [max_eq_left h16]
                        have h19 : D-(a+c+d) ≤ 0 := by linarith
                        rw [max_eq_left h19]
                        linarith
                      · rw [max_eq_right h16]
                        rcases le_total (D-(a+c+d)) 0 with h19 | h19
                        · rw [max_eq_left h19]
                          linarith
                        · rw [max_eq_right h19]
                          linarith
                · rw [max_eq_right h7]
                  have h19 : D-(a+c+d) ≤ 0 := by linarith
                  rw [max_eq_left h19]
                  rcases le_total (D-(c+d)) 0 with h9 | h9
                  · rw [max_eq_left h9]
                    have h10 : D-(c+e) ≤ 0 := by linarith
                    have h12 : D-(d+e) ≤ 0 := by linarith
                    rw [max_eq_left h10, max_eq_left h12]
                    rcases le_total (D-(a+b+c)) 0 with h15 | h15
                    · rw [max_eq_left h15]
                      have h16 : D-(a+b+d) ≤ 0 := by linarith
                      have h17 : D-(a+b+e) ≤ 0 := by linarith
                      rw [max_eq_left h16, max_eq_left h17]
                      linarith
                    · rw [max_eq_right h15]
                      rcases le_total (D-(a+b+d)) 0 with h16 | h16
                      · rw [max_eq_left h16]
                        have h17 : D-(a+b+e) ≤ 0 := by linarith
                        rw [max_eq_left h17]
                        linarith
                      · rw [max_eq_right h16]
                        rcases le_total (D-(a+b+e)) 0 with h17 | h17
                        · rw [max_eq_left h17]
                          linarith
                        · rw [max_eq_right h17]
                          linarith
                  · rw [max_eq_right h9]
                    have h17 : D-(a+b+e) ≤ 0 := by linarith
                    rw [max_eq_left h17]
                    rcases le_total (D-(c+e)) 0 with h10 | h10
                    · rw [max_eq_left h10]
                      have h12 : D-(d+e) ≤ 0 := by linarith
                      rw [max_eq_left h12]
                      rcases le_total (D-(a+b+c)) 0 with h15 | h15
                      · rw [max_eq_left h15]
                        have h16 : D-(a+b+d) ≤ 0 := by linarith
                        rw [max_eq_left h16]
                        linarith
                      · rw [max_eq_right h15]
                        rcases le_total (D-(a+b+d)) 0 with h16 | h16
                        · rw [max_eq_left h16]
                          linarith
                        · rw [max_eq_right h16]
                          linarith
                    · rw [max_eq_right h10]
                      have h16 : D-(a+b+d) ≤ 0 := by linarith
                      rw [max_eq_left h16]
                      rcases le_total (D-(d+e)) 0 with h12 | h12
                      · rw [max_eq_left h12]
                        rcases le_total (D-(a+b+c)) 0 with h15 | h15
                        · rw [max_eq_left h15]
                          linarith
                        · rw [max_eq_right h15]
                          linarith
                      · rw [max_eq_right h12]
                        have h15 : D-(a+b+c) ≤ 0 := by linarith
                        rw [max_eq_left h15]
                        linarith
          · rw [max_eq_right h4]
            have h10 : D-(c+e) ≤ 0 := by linarith
            have h12 : D-(d+e) ≤ 0 := by linarith
            rw [max_eq_left h10, max_eq_left h12]
            rcases le_total (D-(b+c)) 0 with h5 | h5
            · rw [max_eq_left h5]
              have h6 : D-(b+d) ≤ 0 := by linarith
              have h7 : D-(b+e) ≤ 0 := by linarith
              have h8 : D-(b+f) ≤ 0 := by linarith
              have h9 : D-(c+d) ≤ 0 := by linarith
              have h15 : D-(a+b+c) ≤ 0 := by linarith
              have h16 : D-(a+b+d) ≤ 0 := by linarith
              have h17 : D-(a+b+e) ≤ 0 := by linarith
              have h18 : D-(a+b+f) ≤ 0 := by linarith
              have h19 : D-(a+c+d) ≤ 0 := by linarith
              rw [max_eq_left h6, max_eq_left h7, max_eq_left h8, max_eq_left h9, max_eq_left h15, max_eq_left h16, max_eq_left h17, max_eq_left h18, max_eq_left h19]
              linarith
            · rw [max_eq_right h5]
              rcases le_total (D-(b+d)) 0 with h6 | h6
              · rw [max_eq_left h6]
                have h7 : D-(b+e) ≤ 0 := by linarith
                have h8 : D-(b+f) ≤ 0 := by linarith
                have h9 : D-(c+d) ≤ 0 := by linarith
                have h16 : D-(a+b+d) ≤ 0 := by linarith
                have h17 : D-(a+b+e) ≤ 0 := by linarith
                have h18 : D-(a+b+f) ≤ 0 := by linarith
                have h19 : D-(a+c+d) ≤ 0 := by linarith
                rw [max_eq_left h7, max_eq_left h8, max_eq_left h9, max_eq_left h16, max_eq_left h17, max_eq_left h18, max_eq_left h19]
                rcases le_total (D-(a+b+c)) 0 with h15 | h15
                · rw [max_eq_left h15]
                  linarith
                · rw [max_eq_right h15]
                  linarith
              · rw [max_eq_right h6]
                rcases le_total (D-(b+e)) 0 with h7 | h7
                · rw [max_eq_left h7]
                  have h8 : D-(b+f) ≤ 0 := by linarith
                  have h17 : D-(a+b+e) ≤ 0 := by linarith
                  have h18 : D-(a+b+f) ≤ 0 := by linarith
                  rw [max_eq_left h8, max_eq_left h17, max_eq_left h18]
                  rcases le_total (D-(c+d)) 0 with h9 | h9
                  · rw [max_eq_left h9]
                    have h19 : D-(a+c+d) ≤ 0 := by linarith
                    rw [max_eq_left h19]
                    rcases le_total (D-(a+b+c)) 0 with h15 | h15
                    · rw [max_eq_left h15]
                      have h16 : D-(a+b+d) ≤ 0 := by linarith
                      rw [max_eq_left h16]
                      linarith
                    · rw [max_eq_right h15]
                      rcases le_total (D-(a+b+d)) 0 with h16 | h16
                      · rw [max_eq_left h16]
                        linarith
                      · rw [max_eq_right h16]
                        linarith
                  · rw [max_eq_right h9]
                    rcases le_total (D-(a+b+c)) 0 with h15 | h15
                    · rw [max_eq_left h15]
                      have h16 : D-(a+b+d) ≤ 0 := by linarith
                      have h19 : D-(a+c+d) ≤ 0 := by linarith
                      rw [max_eq_left h16, max_eq_left h19]
                      linarith
                    · rw [max_eq_right h15]
                      rcases le_total (D-(a+b+d)) 0 with h16 | h16
                      · rw [max_eq_left h16]
                        have h19 : D-(a+c+d) ≤ 0 := by linarith
                        rw [max_eq_left h19]
                        linarith
                      · rw [max_eq_right h16]
                        rcases le_total (D-(a+c+d)) 0 with h19 | h19
                        · rw [max_eq_left h19]
                          linarith
                        · rw [max_eq_right h19]
                          linarith
                · rw [max_eq_right h7]
                  have h9 : D-(c+d) ≤ 0 := by linarith
                  have h19 : D-(a+c+d) ≤ 0 := by linarith
                  rw [max_eq_left h9, max_eq_left h19]
                  rcases le_total (D-(b+f)) 0 with h8 | h8
                  · rw [max_eq_left h8]
                    have h18 : D-(a+b+f) ≤ 0 := by linarith
                    rw [max_eq_left h18]
                    rcases le_total (D-(a+b+c)) 0 with h15 | h15
                    · rw [max_eq_left h15]
                      have h16 : D-(a+b+d) ≤ 0 := by linarith
                      have h17 : D-(a+b+e) ≤ 0 := by linarith
                      rw [max_eq_left h16, max_eq_left h17]
                      linarith
                    · rw [max_eq_right h15]
                      rcases le_total (D-(a+b+d)) 0 with h16 | h16
                      · rw [max_eq_left h16]
                        have h17 : D-(a+b+e) ≤ 0 := by linarith
                        rw [max_eq_left h17]
                        linarith
                      · rw [max_eq_right h16]
                        rcases le_total (D-(a+b+e)) 0 with h17 | h17
                        · rw [max_eq_left h17]
                          linarith
                        · rw [max_eq_right h17]
                          linarith
                  · rw [max_eq_right h8]
                    rcases le_total (D-(a+b+c)) 0 with h15 | h15
                    · rw [max_eq_left h15]
                      have h16 : D-(a+b+d) ≤ 0 := by linarith
                      have h17 : D-(a+b+e) ≤ 0 := by linarith
                      have h18 : D-(a+b+f) ≤ 0 := by linarith
                      rw [max_eq_left h16, max_eq_left h17, max_eq_left h18]
                      linarith
                    · rw [max_eq_right h15]
                      rcases le_total (D-(a+b+d)) 0 with h16 | h16
                      · rw [max_eq_left h16]
                        have h17 : D-(a+b+e) ≤ 0 := by linarith
                        have h18 : D-(a+b+f) ≤ 0 := by linarith
                        rw [max_eq_left h17, max_eq_left h18]
                        linarith
                      · rw [max_eq_right h16]
                        rcases le_total (D-(a+b+e)) 0 with h17 | h17
                        · rw [max_eq_left h17]
                          have h18 : D-(a+b+f) ≤ 0 := by linarith
                          rw [max_eq_left h18]
                          linarith
                        · rw [max_eq_right h17]
                          rcases le_total (D-(a+b+f)) 0 with h18 | h18
                          · rw [max_eq_left h18]
                            linarith
                          · rw [max_eq_right h18]
                            linarith

/-- The exact six-coordinate finite difference, including every subset,
satisfies the one-least-log bound in the ordered small-log chamber. -/
theorem kernel_six_le_first {a b c d e f D : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hde : d ≤ e) (hef : e ≤ f) (hf : f ≤ D)
    (ht : 3*D ≤ a+b+c+d+e+f) :
    ZetaRieszContinuumCascade.kernel (Finset.univ : Finset (Fin 6))
      ![a,b,c,d,e,f] D ≤ a := by
  have hu : (Finset.univ : Finset (Fin 6)) =
      insert 0 (insert 1 (insert 2 (insert 3 (insert 4 (insert 5 ∅))))) := by decide
  convert pair_triple_bound ha hab hbc hcd hde hef hf ht using 1
  rw [hu]
  repeat' rw [ZetaRieszContinuumCascade.kernel_insert _ _ _ (by decide)]
  simp only [show (![a,b,c,d,e,f] : Fin 6 → ℝ) 0 = a from rfl,
    show (![a,b,c,d,e,f] : Fin 6 → ℝ) 1 = b from rfl,
    show (![a,b,c,d,e,f] : Fin 6 → ℝ) 2 = c from rfl,
    show (![a,b,c,d,e,f] : Fin 6 → ℝ) 3 = d from rfl,
    show (![a,b,c,d,e,f] : Fin 6 → ℝ) 4 = e from rfl,
    show (![a,b,c,d,e,f] : Fin 6 → ℝ) 5 = f from rfl]
  norm_num [ZetaRieszContinuumCascade.kernel]
  simp only [sub_sub,← add_assoc]
  have hz0 : 0 ≤ D := by linarith
  rw [max_eq_right hz0]
  have hz1 : 0 ≤ D-(a) := by linarith
  rw [max_eq_right hz1]
  have hz2 : 0 ≤ D-(b) := by linarith
  rw [max_eq_right hz2]
  have hz3 : 0 ≤ D-(c) := by linarith
  rw [max_eq_right hz3]
  have hz4 : 0 ≤ D-(d) := by linarith
  rw [max_eq_right hz4]
  have hz5 : 0 ≤ D-(e) := by linarith
  rw [max_eq_right hz5]
  have hz6 : 0 ≤ D-(f) := by linarith
  rw [max_eq_right hz6]
  have hz7 : D-(a+b+c+d) ≤ 0 := by linarith
  rw [max_eq_left hz7]
  have hz8 : D-(a+b+c+e) ≤ 0 := by linarith
  rw [max_eq_left hz8]
  have hz9 : D-(a+b+c+f) ≤ 0 := by linarith
  rw [max_eq_left hz9]
  have hz10 : D-(a+b+d+e) ≤ 0 := by linarith
  rw [max_eq_left hz10]
  have hz11 : D-(a+b+d+f) ≤ 0 := by linarith
  rw [max_eq_left hz11]
  have hz12 : D-(a+b+e+f) ≤ 0 := by linarith
  rw [max_eq_left hz12]
  have hz13 : D-(a+c+d+e) ≤ 0 := by linarith
  rw [max_eq_left hz13]
  have hz14 : D-(a+c+d+f) ≤ 0 := by linarith
  rw [max_eq_left hz14]
  have hz15 : D-(a+c+e+f) ≤ 0 := by linarith
  rw [max_eq_left hz15]
  have hz16 : D-(a+d+e+f) ≤ 0 := by linarith
  rw [max_eq_left hz16]
  have hz17 : D-(b+c+d+e) ≤ 0 := by linarith
  rw [max_eq_left hz17]
  have hz18 : D-(b+c+d+f) ≤ 0 := by linarith
  rw [max_eq_left hz18]
  have hz19 : D-(b+c+e+f) ≤ 0 := by linarith
  rw [max_eq_left hz19]
  have hz20 : D-(b+d+e+f) ≤ 0 := by linarith
  rw [max_eq_left hz20]
  have hz21 : D-(c+d+e+f) ≤ 0 := by linarith
  rw [max_eq_left hz21]
  have hz22 : D-(a+b+c+d+e) ≤ 0 := by linarith
  rw [max_eq_left hz22]
  have hz23 : D-(a+b+c+d+f) ≤ 0 := by linarith
  rw [max_eq_left hz23]
  have hz24 : D-(a+b+c+e+f) ≤ 0 := by linarith
  rw [max_eq_left hz24]
  have hz25 : D-(a+b+d+e+f) ≤ 0 := by linarith
  rw [max_eq_left hz25]
  have hz26 : D-(a+c+d+e+f) ≤ 0 := by linarith
  rw [max_eq_left hz26]
  have hz27 : D-(b+c+d+e+f) ≤ 0 := by linarith
  rw [max_eq_left hz27]
  have hz28 : D-(a+b+c+d+e+f) ≤ 0 := by linarith
  rw [max_eq_left hz28]
  ring

end
end RiemannGaussian.ZetaRieszSixSmallHinges
