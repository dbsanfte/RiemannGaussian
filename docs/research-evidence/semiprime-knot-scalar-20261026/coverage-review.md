# Independent review of primitive-coverage.md

26 October 2026. Scratch only; no tests needed. Verdict: Section 3's alternate-source construction and its cost tradeoff are correct with the phase-lift and deletion details below made explicit. It does not yield a new factoring record or the requested soft-k prefix algorithm.

## Source and orientation

Checked Harvey–Hittmeir, arXiv:2105.11105, Proposition 3.3 (printed p.5), proof (p.6), and Algorithm 4.3 Steps 8–10 (pp.7–8): https://arxiv.org/pdf/2105.11105 . The substitution is m=k, m_0=r, sigma_0=B. Its physical sum is T=aQ+bP for the factor P in the chosen residue/bin. Its stationary lattice condition is b sigma²=aN mod k. This is consistent with Section 1's different orientation T=aP+bQ, provided coefficients are explicitly swapped. These are not the same labeled row.

For the project's descriptor E_(u,v)=u+vN+lambda, the exact identities for Section 3 are

    E_(b,a) − (T+lambda) = (P−1)(aQ−b),
    E_(a,b) − (T+lambda) = (Q−1)(bP−a).

Thus the report correctly assigns the P-hit to (b,a) and Q-hit to (a,b). The physical value and stationary phase are shared. No independent unknown bin for Q is needed.

## The modulo-k² phase must use a genuine lift

Compute tau=aN sigma^{-1}+b sigma modulo H=k² using the canonical integer sigma in [1,k] and its inverse **modulo H**; then lambda=[−tau]_H. Computing an inverse only modulo k and reusing its integer representative modulo H is insufficient. This is the same precision used in the source's Algorithm 4.3 Step 9.

No enumeration of k lifts of sigma is required. If sigma is replaced by sigma+kt, the change of tau modulo H is

    kt (b−aN sigma^{-2}) = 0 mod H,

because stationary congruence gives the parenthesized expression zero mod k. Also tau²−4abN=(aN/sigma−b sigma)²=0 mod H. The source congruence therefore supplies exactly one lawful conic root lambda for this alternate descriptor, without acquiring all conic roots. This is a positive source-specific fact, not a general omission of phase lifts in an arbitrary approximation construction.

## Coefficient bounds and zero-row deletion

The proof inequalities (3.7), with B≤sqrt N, imply

    |a| ≤ 2B sqrt(kr)/sqrt N ≤ 2sqrt(kr),
    |b| ≤ 2sqrt(Nk/r)/B + 2sqrt(Nkr)/B
         ≤ 4sqrt(Nkr)/B.

These are stronger than the proposition's general polynomial-size output assertion and apply to every acquired bin in the stated range. For B≥16k², r≤k^(1/3), N≤k^6, they give |a|=O(k^(2/3)), |b|=O(k^(5/3)); both are below P,Q>16k²+1 asymptotically. The nonzero pair assertion then proves **both** aQ−b≠0 and bP−a≠0, including axes. Consequently both displayed Fermat integers are nonzero, and all labels/exponents have O(log N) bits. The finite initial k range requires the stated finite fallback.

For precision, the deletion-survival argument is: let I=(T+lambda)/H, and choose the common public center c from (aN/B+bB+lambda)/H. The source error gives |I−c|≤O(1+sqrt N/(kr)^(3/2)). If E_(u,v)=H(c+i_0) for an index in this same searched interval, the appropriate local hit gives q^(i_0−(I−c))=1. The entire interval diameter is below the certified local q order for the stated asymptotic range, so i_0=I−c. That would force the corresponding nonzero Fermat integer above to vanish, a contradiction. Both witness rows survive. Deletion must use each row's actual centered interval, as the report says.

Checked the existing public setup contract in `uniform-setup-and-query-interface.md` §§1–3 and the actual composition in `scalar-catalogue.md` §§1–2,5, together with `swap-erratum.md` §1. The relevant licensed consumer accepts arbitrary nonzero polynomial-bit global annihilators with the prepared odd local-order bounds; it does not require the old |a|,|b|≤k label bound. Hence these larger alternate labels are allowed after the preceding nonzero proof. The controller's separate later prime-modulus query specialization must not be imported here.

## Common center and full zero

Both swapped rows use the same lambda, the same physical T, and the same center c. At the single global centered index i=I−c, one scalar factor vanishes modulo P and another modulo Q. The product over the two retained rows is therefore zero modulo N. Centering the two swapped rows independently using their own coefficient-oriented approximations would lose this proof; retain descriptor provenance and transport the chosen common center instead.

This establishes the full-zero endpoint needed by the existing zero-only consumer. It does not by itself certify distinct known root values or unit pair differences. Those would require additional paid preprocessing if a particular later paired-root selector demands them. The generic saturated-leaf/annihilator consumer does not need that stronger promise. Opposite rows can be centered compatibly as described in Section 1 and are not necessary just to obtain this full zero.

## Exact cost and credit

There are O(r log N) rounded multiplicative bins and phi(k)=Theta(k) permitted residues, hence R=soft(kr) acquired descriptors, with only constant overhead for swaps. The source width is

    W=O(1+sqrt N/(kr)^(3/2)).

The stated monic variable-window evaluation bound soft(R+sqrt(RW)) consequently becomes

    soft(kr + sqrt(kr) + N^(1/4)/(kr)^(1/4))
      = soft(kr + k^(5/4)/r^(1/4))

when N=Theta(k^6). All hidden arithmetic bit factors are polylog N; the cost is not the source's original linear-babystep implementation but the already paid project window evaluator applied to its acquired rows. Ceilings contribute sqrt(R), absorbed by R.

At r=k^(1/5), both principal terms equal k^(6/5)=Theta(N^(1/5)). At r=k^(1/3), the width is O(k) but acquisition is k^(4/3), which dominates. Soft-k acquisition permits only polylogarithmic r and retains the old soft(k^(3/2)) width. These calculations are correct. The one-fifth endpoint is a reconstruction of known factoring scale, not a new record or a sixth-rate solution.

The coalescence proposal remains genuinely unproved: reducing distinct vectors alone does not bound the union of their shifted integer windows. The requested soft-k descriptor count and soft-k² total support must both be acquired with the shared-index provenance intact.
