# Original scalar pair differences: acquired Lucas data, unresolved contraction

22 October 2026. Focused construction attempt using original prepared gamma and its original q/H source. No repository edits, examples, implementation, new agents, or improved rate claim.

Write M=m^3, Q=gamma^M, c_a=gamma^(N+a), t_j=gamma^v_j. Native antipodal points satisfy

    y_j=c_a t_j, y_-j=c_a t_j^-1 Q^-u_j,
    u_j in {0,1,2}.

The already paid bounded-block corrections move the second H argument from y_-j to c_a/t_j. These corrections retain original scalar leaf ledgers and are NOT silently unit-cancelled. All following paired formulas refer to that corrected interval.

## Actual difference norm, including its acquired coefficients

For a single common seed s, the ORIGINAL scalar pair has the exact quadratic

    (c_a t_j-s)(c_a/t_j-s)
      =s^2-c_a L_j s+c_a^2,
    L_j=gamma^v_j+gamma^-v_j.                  (1)

Both c_a and L_j are genuinely acquired for the entire family in soft O(m): each is formed by O(log N)-bit public modular powering of known units, without expanding a degree-|v_j| polynomial. Negative v_j use gamma inverse. The values L_j are Lucas/Chebyshev values at w=gamma+gamma^-1, with C_0=2,C_1=w,C_(n+1)=w C_n-C_(n-1). Binary powering, rather than expansion through the largest n, pays the claimed data acquisition.

For epsilon=Legendre(-1,m)=+1, both antipodal rows have the SAME palette, so for a supplied complete pair group G the paired query is exactly

    product_(s a root of H_e) product_(j in G_e)
       (s^2-c_(a_j)L_j s+c_(a_j)^2),           (2)

up to the previously paid endpoint factors and public scales. The inner monic polynomial P_G(s) has degree 2|G_e| and is acquired in soft O(|G_e|) by a product tree of quadratics. Equivalently it is the actual target polynomial for the corrected two-row points, without needing their separate expansions. This is a true difference product, unlike the acquired product of the targets alone.

For epsilon=-1 the two rows have opposite palettes. Directly (2) cannot be used with one H: its two linear factors belong to different seed sets. The paid palette reflection first gives the previously reviewed same-palette nodes y_j,w_j with w_j/y_j=B gamma^-2a_j. Their quadratic has acquired sum y_j+w_j and product y_j w_j. It also yields a degree-2|G_e| polynomial, but these coefficients are not a shared Lucas polynomial with one constant center. No opposite-palette seed is silently identified with the same s in (1).

## Where the contraction still costs more than soft m

Equation (2) reduces the group query to Res(P_G,H_e), with P_G acquired. It DOES NOT acquire the resultant. Its degree stays proportional to the number of original rows, and H still has K blocks of about m/2 roots. Scalar evaluation of P_G over those blocks remains the direct norm-only contraction from the earlier packet. Generic geometric-query evaluation pays the existing soft O(J+sqrt(JL)) scale. No new bound follows from writing the degree-two factors before multiplying them.

The cubic congruence v_j^2=4a_jN modulo M is a congruence of INTEGER INDICES. Lucas identities such as C_(r+s)+C_(r-s)=C_r C_s use actual sums of indices. Replacing an index by a congruent one modulo M changes its value through the nontrivial scalar Q and cannot be dropped. Since gamma is not assumed to have order M, the congruence does not identify L_j with a fixed short Chebyshev evaluation indexed only by a_j. All retained Q carries would have to be included by a proposed transform. The exact native no-wrap multiplier map supplies some powered point relations; it does not close this whole pair-polynomial family under the seed step.

No Christoffel--Darboux formula was obtained whose required recurrence coefficients and boundary data determine the resultant (2). Acquiring the Lucas values is already paid, so an unavailable trace oracle is not being blamed; the missing operation is their joint multiplicative contraction against the long original scalar seed grid. Likewise the exact seed reciprocity/reflection and finite multiplier identities retain their paid endpoint corrections but have not removed that contraction.

## Outcome and sufficient next theorem

The original pair DIFFERENCE quadratics and their complete group polynomial are actually acquired in soft O(m), with all centers and Lucas values charged. A restriction-stable algorithm evaluating their resultant with H_e in soft O(|G|+m) would solve the sufficient pair-group query and permit binary pair localization followed by original two-row scalar descent. This pass found no such algorithm. It supplies no zero-support substitute, no Gauss-base order assumption, and no claim that a compact quadratic or theta identity itself acquires the query.
