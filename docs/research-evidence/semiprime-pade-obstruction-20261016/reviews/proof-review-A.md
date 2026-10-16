# Independent exact mathematical review A

2026-10-16. Verdict: PASS for the exact finite-segment theorem, its applications and stated limitations. No operation lower bound or acquisition algorithm follows.

Target: `pade-constant-recurrence.md`, 7291 bytes, SHA256 `d749385717bca05f1cdb1bbe3e432b3571200b07e79902b64491a796739d6937`.

## Coefficients and functional equation

The finite q-binomial coefficient relation has the correct sign. Multiplication by the chirp contributes g^k on the A_(k+1) side, giving equation(2). Multiplying by g and summing yields precisely C(gX)-C(gqX)=gX(q^L C(X)-C(qX)). Its constant term vanishes and its potential degree-L+1 right boundary vanishes because q^L-q^L=0. All intermediate coefficients are nonzero in the canonical construction under ord(q)>L, and A_L is a nonzero product of units. The general theorem correctly assumes exact degree and coefficient relation rather than a hidden relation q=g^d.

## Recurrence-to-Pade and exact identity

The reversal Q_j=a_(r-j) makes [X^n]QC equal the assumed recurrence at k=n-r for n=r,...,L. Thus Q0=a_r!=0, degQ<=r and the truncated P has degree<r; missing a_0 and lower actual denominator degree cause no problem. The result is G=P/Q=C+O(X^(L+1)), as formal series over the field.

All four denominator shifts have nonzero constant terms, including if some shifts coincide. Residual substitution preserves order at least L+1; multiplication by X can only increase that order. The first two cleared terms have degree<=4r-1, and the X-multiplied terms degree<=4r. Thus when4r<=L the residual numerator must vanish identically. This is an exact rational identity, not finite-grid interpolation.

## Finite uniqueness and contradiction

Coefficient comparison gives g^k(1-q^(k+1))b_(k+1)=(q^L-q^k)b_k. For indices through L+r the leading factors are nonzero, so b0=1 uniquely determines all those coefficients. In particular b_(L+1)=0 from the terminating numerator, followed by r-1 further zeros. Infinite formal-series uniqueness is neither needed nor claimed: q may have finite order, and only the stated finite interval is used. Therefore P-QC has degree<=L+r and vanishes through that degree. Its exact vanishing contradicts deg(QC)>=L>degP. This proof works in every characteristic, without differentiation or separability.

The recurrence order is the maximal nonzero forward coefficient r, and the equations cover its entire natural finite range. The order-zero case is ruled out by A0=1. The statement does not falsely infer the same conclusion for a shorter arbitrary collection of equations or for a larger declared order with a zero leading coefficient.

## Actual applications and scope

For L=2m²+2, both the original qualified source and the new certified setup provide local q orders>16m²>L+floor(L/4), including m>=1. The argument applies independently in both hidden fields, with fully advised field coefficients. No numerical order, frequency nonalias certificate, prime-order assumption or extra majority-family deletion is required. This genuinely strengthens the old order<=m obstruction and excludes O(m polylog m) constant recurrences asymptotically for the FULL chirped coefficient segment.

The theorem is about constant recurrences of this sequence on that full segment. It does not exclude interpolation matching only selected values, another stream/transform, q-dependent coefficients, multivariate/two-clock state, sparse high-degree formulas, nonlinear methods, selected convolution or direct scalar norms. It gives no arithmetic-circuit lower bound. Pade approximation and rational denominator clearing are standard methods; the novel finite-segment application is not asserted to be the first recurrence obstruction or an exhaustive literature-priority result. Original collision coverage is not silently transferred to another base.

No original report/repository file was changed; no native build or numerical test was used. All five raw source pins in final `source-pins.json` (1313 bytes, SHA256 `e94471eab58bd43ad292e3bcbe41d62181966d9ddb4cef2cb49f316226fd86a5`) independently match their declared byte lengths and hashes. These include the latest all-semiprime setup, prior paid coprime refinement, earlier chirped/constant-recurrence proofs and block-transform source. No external primary theorem is needed for the new self-contained algebra.
