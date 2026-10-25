# Independent normalized-formula review

22 October2026. Reviewed gamma-normalization-review.md against gamma-normalized-gauss.md, composite-gauss-supply.md and the prior whole-unit implementation. Verdict: PASS. The new normalized formulas, explicit inverses, own-tag whole-local-algebra coverage and same-leaf ideal equality are correct for odd composite m, unit tags and the stated primewise screens. This does not validate recovery from a lone component hit or acquire a difference aggregate.

## Quotients and explicit inverses

Let bar=rho_−1 fix additive roots and scalars. Put E0=m^(−1)sum X^r, D=E0+ell(1−E0), and D_E=E_E+ell(1−E_E), where E_E projects onto characters trivialized by exponent E. On the screened branch ell,m are units. For every component, including trivial and proper-divisor characters,

    g_1 bar(g_1)=D, g_E bar(g_E)=D_E.

Thus C_E bar(C_E)=D^E D_E^(−1), and the explicit inverse bar(C_E)D_E D^(−E) is correct. E=0 has C_0=−1,E_E=1,D_E=1, so this gives−1 as required. Intermediate nonunit E modm creates the larger projector E_E and is already handled. Only nonnegative supplied E is needed for the reviewed C_E acquisition; signed powers of the resulting units are acquired from the explicit inverse, not an undefined negative-index C.

The normalized h_a=t g_a/g_−a has h_a bar(h_a)=gamma=t². Its packed quotient A_E=t^(E−1)C_E/bar(C_E) satisfies h_1^E=A_E h_E and A_E bar(A_E)=gamma^(E−1). E=0,1 agree exactly. This removes the prior need for a guarded generic polynomial inverse in THIS operation.

## V, seed, pair and whole aggregates

U=g_1^m=−C_m and U bar(U)=D^m. Therefore

    V=h_1^m=t^m U/bar(U)=t^m U²D^(−m),
    q_h=h_1^(m²)=V^m.

All are acquired from constant-many rank-m operations. V bar(V)=gamma^m and q_h bar(q_h)=gamma^(m²), so explicit inverses are bar(V)gamma^(−m) and bar(q_h)gamma^(−m²), if desired. No additive-root joint carrier is required for these particular grade-zero quantities.

For the old target G_j, T_j=t^E_j G_j/bar(G_j). The old unit antipodal identity G_jG_−j=q_G^(−s)D^(N+a) and E_j+E_−j=2(N+a)−m²s give exactly

    T_jT_−j=gamma^(N+a)q_h^(−s).

The scalar D amplitudes cancel because bar(D)=D. Also T_jbar(T_j)=gamma^E_j gives

    bar(T_j)=gamma^(ellrow_j)q_h^s T_−j.

Over h=phi(m)/2 pairs, A=sum a and S=sum s, the whole product is gamma^(A+Nh)q_h^(−S). Pair quotient weights satisfy A_j A_(m−j)=V/gamma because j+(m−j)=m as INTEGERS; weighting by equal integer a yields product_units A_j^a_j=(V/gamma)^A. The integer representative convention is essential and is respected.

At X=1, U=−1,D=1,h_a=t,V=t^m and q_h=t^(m²). Every pair and whole formula becomes its literal t-exponent identity, including delta signs implicit in negative powers. At every nontrivial proper-order component, unit tags preserve nontriviality and odd order gives chi(−1)=1, so D=ell exactly. There is no omitted exceptional character case.

## Full source phase and same-leaf recovery

At a hidden P, true Frobenius acts on both root systems. With j=Pmodm,b=Pmodell, direct substitution gives h_1^P=chi(P)^(−2P)h_P because t^P=t modulo P. The inverse Frobenius phase in the N arm is chi(b)^(2N/j); the a arm has chi(b)^(−2aj). Native a j²=Nmodm cancels their product. Thus the corrected public T_j equals h_1^(ellrow+aP+Q)=h_1^(m²I) in the WHOLE local algebra at its true tag. Since gamma is scalar and the actual integer source identity applies, no scalar-order hypothesis is assigned to h_1 or ell.

The grade2(ellrow+aj+N/j) vanishes modm, as does the seed grade. The automorphism group orderell−1=2m is invertible modulo odd screened N, so averaging/descent to the character algebra is justified. This only pays requested grade-zero expressions, not an expanded family of m independent rank-m row vectors.

For z=q_h^i, f=T_j−z, G=gamma^E_j−gamma^(m²i), direct expansion gives

    G=bar(T_j)f+z bar(f).

Therefore G lies in(f,bar(f)), and since z is a unit,

    bar(f)=z^(−1)[G−bar(T_j)f].

Both ideal inclusions hold, proving(f,bar(f))=(f,G) over the WHOLE packed ring, not just field components. The argument does not need bar(T_j) to be inverted. At a common same-leaf component zero, G vanishes at the underlying hidden prime, so the ORIGINAL scalar gamma exponent ledger/decoder gives valid recovery. Norm(f)=f bar(f) instead records a union of two zero supports, so its zero alone cannot be promoted to this intersection. Different-leaf products retain the same unresolved pairing issue.

## Paid scalar root and original decoder contract

Given prepared gamma0 of odd local orders, choose any d>=1 of logarithmic size and compute gamma=gamma0^(2^d), t=gamma0^(2^(d−1)). These are public powers and t²=gamma exactly. Raising to2^d preserves each local order and global lcm, including coprimality and the required q0-order promises. Native row/Fermat coverage is valid for arbitrary bases satisfying that contract. Integer gaps are unchanged. A certified gamma^K=1 implies gamma0^K=1 at both factors, because each odd local order divides2^dK iff it divides K. Thus the same nonzero K works for the original decoder with no bit expansion. No unknown-order root extraction is needed.

All requested vectors/inverses/powers have the reviewed soft O(ell+m) native cost, with polynomial-size exponent logarithms. Primewise screens, ell-first supply and the composite row catalog remain separately paid. No all-row difference product or paired-component localizer is supplied by these formulas. In particular the full-algebra source and same-leaf recovery theorem repair the old source/order issue, while the acquisition/localization problem remains open.

Only this new scratch review was written. No source report, implementation, repository, examples, or backend was changed.
