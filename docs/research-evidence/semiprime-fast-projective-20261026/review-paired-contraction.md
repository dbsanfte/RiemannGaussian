# Independent review: paired-contraction.md

26 October 2026. Scoped symbolic review against the frozen paired-monic inputs and the actual guarded-gcd source. No tests, new investigation or repository edits.

**PASS on the cross gates, arithmetic nonalignment and state/trace scope; one unconditional-proof correction requested for the sibling determinant.**

## Whole-list gate and its actual cost

The pair resultant (2) has the correct leading-coefficient normalization and sign. Its point norm exponents 2[L+/-2ell],2L are nonzero on the stated regular range. Whole-list cross differences have beta norm exponent 2E_uv, where E_uv=ell_u-ell_v+a_u-1-(a_v-1)N. Since a_v>=3 and the phase width is H, |E_uv|>=2N-H-K>0. Hence the saturated whole-point branch has a legal explicit short annihilator. The nonsplit-field argument correctly handles norm saturation with a nonglobal-zero coordinate vector by a proper coordinate gcd.

Evaluate FB at all A roots once by monic MPE; that costs soft K even if the A roots repeat. Products/norms and binary selection locate ONE nonunit evaluation. Scanning its O(K) B differences is paid only on that terminating nonunit branch, not separately at every A root. If its product norm vanishes at different primes in different B entries, the individual scan finds a proper gcd; it does not mistake the mixed product for a global point equality. Thus total soft K plus once-only T_ext is valid, not K². Continuation certifies every individual A/B cross difference a unit.

## Bezout/CRT justification

A unit resultant alone does NOT certify arbitrary Euclidean intermediate coefficients. The report does, however, cite an actual stronger interface: norm-sharing/implicit-evaluation.md section 2 explicitly tests every quadratic-algebra pivot by norm and coordinates, allowing a degree drop only for a globally zero coefficient.

The needed continuation argument is sound: a nonzero B coefficient either has unit norm, a proper norm gcd, or saturated norm with zero at the nonsplit field. In the last case a nonglobal-zero coefficient gives a proper coordinate gcd. Thus on no-factor continuation every nonzero pivot is a certified unit and degrees agree componentwise. Running the standard FAST half-GCD/extended-gcd algorithm with this classifier gives the stated soft K bound. No within-list root-separation inverse is required. Suggested wording: explicitly say “guarded fast half-GCD/extended gcd,” rather than letting “extended Euclid” suggest a quadratic-time implementation. The existing cited interface already states its soft bound; the important point is its pivot guards, not the input resultant alone.

The resulting RA FA+RB FB=1 and EA=RB FB, EB=RA FA modulo FA FB have correct orientation. The geometric sums of these O(K)-degree coefficients require only short q^d-1 inverses, all certified; long numerator values are not inverted. The text correctly avoids treating an arbitrary nonhit clock node as a root projector value 0, and avoids inferring a whole wrong-family norm is a unit merely from cross separation.

## Physical nonalignment

At a good A tag, aR=S modulo K. For a!=1 choose p^e||K with t=v_p(a-1)<e. Since R is a unit, S-R=(a-1)R modulo p^e has EXACT valuation t. The product (a-1)(S-R) therefore has valuation 2t<2e, so it is not divisible by H. This proves absence of a paired INTEGER physical clock index at the same field, while leaving unknown-order modular aliases open. The reversed good-B statement follows identically. No coefficient-as-field-factor or two-factor-ratio assumption is used.

## Required correction: public sibling integrality without an actual factor lift

Formula (6) checks by inverse expansion modulo H, using (K/3)^3 divisible by H for e>=3. Formula (7) checks under its explicitly conditional factor lift. But the unconditional integrality of (8) should NOT be proved by assuming such a lift exists for an arbitrary sibling triple.

Here is the direct public proof. Put delta0=K/3 and let m index the middle coefficient a_m. Since sum_s a_s=3a_m and a_s=a+delta0*k_s,

    sum_s k_s-3k_m=0.

Sum (6) over s=0,1,2 and subtract three times its m instance. Its linear term becomes

    delta0*(sum_s s-3m)*(N*j^-2-a),

because the k_s*j term cancels EXACTLY. The remaining parenthesis is divisible by K=3delta0. All other terms already carry delta0². Therefore sum_s ell_s-3ell_m is divisible by delta0²=H/9, since H is also a multiple of delta0². This is unconditional and uses only acquired public data, not existence of any actual factor with that coarse colour.

Once that direct argument replaces the sentence relying on summing (7), the global product identity is valid: the barpi exponent cancels because the coefficient is the exact middle sibling, and the remaining pi exponent is the defined integer L times H/9. Centering shifts L by multiples of 9. The stated |L|<=27 is safe. This determinant does not determine the first/second symmetric coefficients or imply a cubic root-of-unity orbit.

If a=1 pruning cuts a triple, retain its acquired auxiliary root when stating the algebraic triple identity or account for that constant-size partial-triple boundary; no long value is thereby supplied. The separately paid original unit query permits zero-safe bookkeeping, not arbitrary numerical division at a collision.

After the explicit integrality correction, no substantive claim or cost problem remains. The new gates/projectors are actually acquired; the one-defect readout and correction clock norm remain unacquired at target rate, exactly as stated.

Integration note: paired-contraction.md now includes the direct proof
from (6), explicitly names guarded fast half-GCD, and retains auxiliary
entries for the constant number of exception-cut triples. These address
the review's requested corrections without changing the claimed rate.
