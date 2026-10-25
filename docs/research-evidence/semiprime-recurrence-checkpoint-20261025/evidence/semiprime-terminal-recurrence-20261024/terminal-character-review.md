# Independent terminal character/block review

24 October 2026. Reviewed final exact bytes of /tmp/semiprime-terminal-recurrence-20261024/terminal-character.md.

SHA-256: `75cf6cbaa4a15bd5d334440a93fafad90a57b6d3286228e5d4e016a911c0e9ae`.

Verdict: **PASS. No required fixes remain.** Earlier head-coefficient and doubled-block denominator precisions were corrected before this pin. Read-only audit; no source/repository edits, examples or backend work.

## Entire pivot polynomials and auxiliary zero supports are acquired

The principal coefficient minor's rows/columns give p_1=a_(n-1)-f_(n-1)Z and, at Z=0, the stated Toeplitz Delta_k with the consistent convention. Each pivot depends only on the indicated head coefficients. Its degree bound k² is the already proved public bound, not an assertion that a truncation evaluated at a unit is exact without proof.

The trace/Newton algorithm over R[Z]/Z^(k²+1) genuinely computes the full determinant polynomial. For a 2k matrix, sequential powers through 2k cost O(k^4) coefficient-ring operations; each coefficient-ring multiplication costs soft k². The sum through K is soft K^7. Newton divisions are only by certified integer units: <=2K in the prefix and <=4K in the next doubled block, always <=2n<P,Q under the chosen caps/preparation. No determinant or target pivot is inverted during this polynomial construction.

Reversal with the public k² bound and Delta_k inverse makes h_k monic of exact degree k² even if its low Y coefficients vanish. The aggregate H_K is acquired, with degree O(K³), and its MPE values on all actual outer nodes are paid. Individual gcds, rather than only a product gcd, correctly distinguish a proper factor from a global zero node. A global aggregate zero need not have the same individual pivot zero at both primes; the report explicitly does not assume it does.

Absent a proper gcd, the bad nodes are exact public global zeros of H_K, at most its degree because the node differences and leading coefficient remain units locally. At each such node the ORIGINAL n-point slice is acquired and tested. Nonunit original leaves have the retained original decoder; unit slices are stored and removed by monic exact division. Thus all removed factors really are known units, and the retained algebra has all processed pivots unit. No auxiliary zero is passed directly to a beta decoder.

The combined helper cost soft(n+t+K^7+n*K³)=soft(n+t) for logarithmic K is sound, including all original-slice exceptions, polynomial coefficients, individual gcds and known-node removal. This does not prove those supports contain a hit, and the source makes no such coverage claim.

## A full next elimination block is actually initialized

The character mask on a retained-algebra element is correctly U_outer(a)=Jacobi(Norm(a),N)^2. After cleanup, unit-pivot resultant transport can omit its unit multipliers for this BOOLEAN output, even at a zero terminal resultant. It does not compute the tail mask.

The final head convention is precise: degree-D heads use the TOP D+1 coefficients, so discarded tails have degree <n-D. Applying the degree-<=K cofactor matrix leaves error degree <n-D+K, below the leading and next coefficients used by the first K steps. Therefore the specialized head Euclidean quotients agree with the full ones. Their pivots are certified unit by the acquired principal support cleanup, not by a generic profile assumption.

A head computation at one node costs O(K²) elementary scalar operations, and its 2-by-2 cofactor matrix contains O(K) coefficients. Across t nodes, O(tK) actual residue coordinates and optional soft(tK) interpolation are paid. This supplies a genuine transformation matrix with exact residual representation, not a named but uninitialized state.

The next block obtains the head through degree 4K+2 and pivots through 2K, clears their actual aggregate support, and recomputes the corresponding cofactor state. If the requested head degree exceeds n, the full original polynomial is used and has degree O(K), so the stated cost still applies. Matrix construction and auxiliary cleanup remain soft(n+t) at logarithmic K.

This is a real extension beyond two-pivot cleanup. Its tail degrees n-K+1,n-K remain Theta(n), however. The report does not count an arbitrary number of doublings as free: pivot aggregate degree, explicit determinant work and O(kt) endpoint state all grow with k. It leaves the next mixed leading coefficients and absorbing masks unacquired at the target scale. Those are implementation ledgers rather than lower bounds on other scalar algorithms.

## Scalar q-shift identity is zero-safe but supplies no starting amplitude

F(Y)R_n(qY)=F(q^nY)R_n(Y) is exact. The report correctly returns to the ORIGINAL unremoved outer grid for the separate norm experiment; a cleaned holed grid need not have one seam and is not assigned the same boundary formula.

The resulting E1*F(1)=E0*F(q^(nt)) follows directly from the two full index multisets. It does not divide a possibly nonunit intermediate norm. When F(1) is unit, the acquired coefficient c=F(q^(nt))/F(1) gives the lawful equality E1=c*E0 even if E0 is zero or a zero divisor. The source now explicitly says that the numerical quotient E1/E0 would require E0 unit and is not used otherwise. With both endpoints unit, equality of the absorbing masks is valid without dividing a zero mask; it initializes neither mask.

The endpoint indices are explicitly checked: nt<=L<=2H+2<4H, and shifted restrictions retain the same bounded original decoder horizon. Endpoint nonunits therefore have original-source recovery. Repeated shifts beyond that horizon have only the algebraic identity, with no unproved decoder transfer. The formal constant Y=0 is not on this unit q orbit and is correctly not used as its start.

## Transport, restrictions and completed fallback

The transverse q connection remains a linear scaling map, not an algebra homomorphism. Its exact quotient carry d_q*S_q(h) is retained, and d_q is a unit rather than a negligible scalar seam. The within-grid one-boundary identity is used only on the original full grid. No auxiliary transport inverse failure is interpreted as an original collision.

The helper's soft(n+t) bound is restricted to its actual balanced input; it is not claimed to be a uniform soft-m oracle when n is tiny and t may be large. Restricted calls acquire their own actual coefficients and index shifts or use the original evaluator. Empty/small cases retain direct products.

The defined completion reacquires the whole original rectangle if the helper has not produced a witness. It therefore needs neither an uncomputed removed product inverse nor a false geometric claim for the holed grid. Original row/seed labels survive; proper gcds factor and saturated ORIGINAL leaves use their original beta decoder. The final complete bound remains soft(J+sqrt(JL)). No collision value or covered terminal resultant is inverted.

## Assessment

The reviewed source supplies a paid logarithmic clean prefix, its actual cofactor/head state, and another initialized block. Its scalar norm shift is a valid relative transport with an unknown initial mask/amplitude. These are supporting operations, not a whole-query exponent advance, and no generic scalar-algorithm lower bound is asserted. The final exact bytes pass.
