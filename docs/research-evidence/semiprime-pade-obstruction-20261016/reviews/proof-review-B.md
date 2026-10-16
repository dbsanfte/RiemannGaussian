# Independent exact proof review B

Verdict: PASS for the immutable main theorem and rational-approximation supplement. No correction requested. All five prerequisite source pins match their exact files. No native build or new formal certification is claimed.

Reviewed final files:
- `pade-constant-recurrence.md`: 7291 bytes; SHA256 `d749385717bca05f1cdb1bbe3e432b3571200b07e79902b64491a796739d6937`.
- `rational-approximation-barrier.md`: 3450 bytes; SHA256 `40da69ad305c1446c032132ef38643e43681eb8180fad569ab1d3f36a2324741`.
- `source-pins.json`: 1313 bytes; SHA256 `e94471eab58bd43ad292e3bcbe41d62181966d9ddb4cef2cb49f316226fd86a5`.

The exact functional equation and endpoint cancellation check coefficient by coefficient. Its proof works in any field and does not require prime order or distinct g-powers. The finite recurrence is reversed with Q(0)=a_r!=0, allowing a_0=0 and lower actual denominator degree. It supplies P/Q=C modulo X^(L+1) with degP<r,degQ<=r. Clearing FOUR shifted denominators gives numerator degree at most4r; 4r<=L forces exact rational equality. Each denominator product has nonzero constant coefficient, so vanishing precision is retained.

The exact rational equation uniquely propagates coefficients through L+r when ord(q)>L+r. In particular its zero numerator at k=L forces the first tail coefficient to zero and then the next r-1. P-QC therefore vanishes beyond its full degree, impossible because C has exact degreeL and P has degree belowr. A_0=1 excludes the zero solution. Reducing to maximal nonzero recurrence order handles ineffective highest shifts. No characteristic, derivative, factorial or separability gap occurs.

For the supplement, four-denominator residual degree is u+3v+1. If that is at mostL, exact equality follows; uniqueness through L+v then forces P=QC, contradicting u<L. Hence u+3v>=L. The v=0 case is valid and may also be checked directly from full coefficient agreement. Nonreduced P,Q cause no issue. The stated q-order cutoff for the new setup and its nearlinear u,v consequence are correct.

Both actual ORIGINAL prime-order fields and the paid all-semiprime beta/q setup satisfy local q-order>16m²; for L=2m²+2 this exceeds L+floor(L/4). Thus the main quadratic recurrence-order conclusion applies in both fields with no new family deletion. The supplement likewise applies in its explicit v range. The latest unbalanced setup dependency is now pinned, rather than silently substituting an older balance contract.

This closes constant order2m and O(m polylog m) FULL finite-stream recurrence compression for this sequence. It does not exclude agreement at selected values/coefficients, another stream, q-dependent or multivariate state, succinct high-degree circuits, selected convolution, or direct scalar norm algorithms. The proofs explicitly distinguish a degree/order representation statement from an operation lower bound and do not use an upper-bound algorithm theorem as a lower bound. Whole-query acquisition and the full Lean bit/controller proof remain unpaid. The historical Padé audits concerned other objects; standard Padé and denominator clearing are correctly credited, with only a limited repository novelty claim.
