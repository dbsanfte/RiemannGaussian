# One certified surviving counterexample to the N-quadratic cover

24 October 2026. **The specific quadratic lists do not give guaranteed coverage.** This is one requested exact route-adjudication certificate, not a success campaign, timing claim or counterexample to other compact covers. No frozen report or repository file was modified.

Frozen candidate report: `cover-literature.md`, SHA256 `28b9b5e14ac5e94a101213d17f4ca387ad959efb708160f90af66b2eb21970d1`.

Executable certificate: `tinyreplay.py`, SHA256 `5f09e0c77ea9e02e25181176928b5c29c419452ec0a157038ba6dc00268cc805`. Run `python3 /tmp/semiprime-compact-cover-20261024/tinyreplay.py`. It contains fixed constants only, no search or factor/order oracle, and uses exact integer arithmetic.

## Actual semiprime and preparation promises

Take

    r=450071, s=454931,
    P=900143=2r+1, Q=909863=2s+1,
    N=819006810409=P*Q,
    m=97, H=m²=9409, beta=4.

The replay certifies that r,s,P,Q,m are prime by trial division through their integer square roots, all below 1000. It checks 96^6<N<=97^6. Thus ceil(N^(1/6))=97, already prime, so this is also the first-prime canonical m. It equals ceil((ceil(sqrt N))^(1/3)).

Direct modular powering gives beta^r=1 modulo P and beta^s=1 modulo Q, and beta is not 1 in either field. Since r,s are prime, beta has EXACT local orders r,s. These are distinct, odd and coprime. Moreover

    min(r,s)=450071 > 16H=150544,
    ord_N(beta)=r*s=204751250101
       > 256H²=22663495936.

The replay also checks gcd(H,r*s)=1, so q=beta^H retains these local orders. It checks gcd(N-1,r*s)=1: the point is compatible with an N-1-projected preparation as well, since powering by N-1 is invertible on this cyclic subgroup. No false order-transfer premise is used.

## The actual smooth projection survives with the same orders

Use exactly the report's multiplier

    M=product_(prime ell<=97) ell^floor(log_ell N).

The replay constructs it by sieving/trial primality and exact prime-power comparisons. Its binary length is 931. Because every prime factor is <=97<r,s, gcd(M,r*s)=1. Hence

    gamma'=beta^M mod N=654114417787

still has exact local orders r,s. The replay additionally verifies its powers and nonidentity directly and checks gcd(gamma'-1,N)=1. Therefore the M-kernel branch does not return a factor, and the ordered cap-16H screen returns NoHit: both actual orders exceed that cap. The counterexample reaches the intended surviving quadratic branch with all stated local/global margins.

## All cross-differences are units: interval proof for the entire lists

For the report's exact lists

    S={ f_N(97b):1<=b<=97 },
    T={ f_N(a):0<=a<97 }, f_N(x)=x(N-x),

write u=97b-a and v=97b+a. Then every positive integer exponent gap is

    Delta=u*(N-v),
    1<=u<=9409,
    97<=v<=9505.

Both r,s exceed 9409 and are prime, so neither divides u. The actual residues are

    N mod r=9721,
    N mod s=445212.

Both lie STRICTLY above 9505 and below their respective prime moduli. The whole v interval lies below both moduli. Consequently neither r nor s divides N-v for ANY allowed v. Neither divides Delta at ANY pair.

Since gamma' has exact local orders r,s, gamma'^s_b-gamma'^t_a is nonzero modulo BOTH P and Q for every pair, and is therefore a unit modulo N. This proves failure for the entire 97-by-97 Cartesian product using two interval bounds and two residues; no empirical coverage scan is needed. Monic cross-evaluation returns only unit row products, so its honest outcome is “no covered pair.”

The two-list candidate is still a paid construction with the conditional coverage criterion proved in the frozen report. This certificate decisively refutes universal coverage by that SPECIFIC construction, including after its smooth projection and NoHit preparation. It supplies no general lower bound and says nothing negative about a different N-dependent compact-cover design.
