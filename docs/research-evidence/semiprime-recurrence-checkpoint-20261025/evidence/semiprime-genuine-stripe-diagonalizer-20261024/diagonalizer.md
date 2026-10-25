# Genuine Toeplitz diagonalization of the acquired stripe pencil

24 October 2026. Scratch only. This proves an actual change of basis and native contraction, not a faster paired-query algorithm.

Use the acquired inputs of `/tmp/semiprime-hierarchy-contraction-20261024/shared-resolvent.md`: b=k, T=3k, ell=bT-1, a=q^ell, lower shift S, V=diag(q^j), U_rho=q^(b rho), and C[rho,s]=c_(b rho+s), where P_ell(Y)=sum c_n Y^n. The proved pencil is C(S-aI)-U C B=g e_(b-1)^t, with B=(qS-I)V. The supplied local orders exceed16H. All exponents of screened differences below have absolute value below16H.

## Actual diagonalizer and acquisition

Put A=(S-aI)B^-1. Since B=V(S-I),

    A=(aI+(a-1) sum_(r=1)^(b-1) S^r) V^-1.

Define the unit lower triangular Toeplitz matrix L by L[i,j]=t_(i-j), with

    t_r=(q/a)^r (a;q)_r/(q;q)_r, 0<=r<b,
    (x;q)_r=prod_(0<=i<r)(1-x q^i).

Then

    A L=L Lambda, Lambda[j,j]=lambda_j=a q^-j.

Proof: in column j, the row j+r equation is

    a(q^r-1)t_r=(a-1)sum_(u=0)^(r-1) q^(r-u)t_u.

Subtract q times the r-1 equation to obtain

    t_r=(q/a)(1-a q^(r-1))/(1-q^r) t_(r-1),

which is the displayed formula, starting at t_0=1. All 1-q^r, r<b, are global units. Acquire t by a power walk and scalar recurrence in soft b. The inverse L^-1 is also Toeplitz, with coefficients

    u_r=q^r(a^-1;q)_r/(q;q)_r.

For example this follows formally from the finite-precision q-binomial identities

    sum t_r z^r=(qz;q)_infinity/(qz/a;q)_infinity,
    sum u_r z^r=(qz/a;q)_infinity/(qz;q)_infinity.

Only precision b is used, so these are formal identities with licensed denominators, not convergent infinite products. Alternatively invert the acquired unit series sum t_r z^r modulo z^b in soft b, requiring no q-binomial citation or additional divisions. Application of L or L^-1 to one supplied vector is one truncated convolution, costing soft b.

## True Cauchy reduction, including its exceptional cell

Set M=C L and h^t=e_(b-1)^t B^-1 L. The actual pencil gives

    M Lambda-U M=g h^t.

For m=b-1-j,

    h_j=-q^-j sum_(r=0)^m q^-r t_r
       =-q^-j a^-m (a q;q)_m/(q;q)_m.

The second equality follows by telescoping the successive partial sums; its increment is a^-m(a;q)_m/(q;q)_m. Thus all h_j are acquired in soft b. They are global units: all numerator exponent differences lie between ell+1 and ell+b-1, within the local-order screen.

The denominator lambda_j-U_rho vanishes as a literal exponent difference exactly when ell-j=b rho. With 0<=j<b, 0<=rho<T, the unique such pair is (rho,j)=(T-1,b-1). Every other difference is a global unit, since its nonzero exponent difference has magnitude at most ell<16H. Also g_(T-1)=0. Consequently

    M[rho,j]=g_rho h_j/(lambda_j-U_rho), rho<T-1,
    M[T-1,j]=0, j<b-1,
    M[T-1,b-1]=c_ell.

The last value follows directly from M=C L: the last column of L is e_(b-1), so that entry is the original c_ell. No division by the resonant zero occurs. All g_rho for rho<T-1 are units too, though the contraction does not need their inverses.

The Cauchy rectangle with the resonant last row removed has b column nodes lambda_j and T-1 row nodes U_rho. Its action on one supplied vector costs soft(b+T), by rational numerator construction and monic multipoint evaluation. Every denominator polynomial evaluated at a column node is a product of the certified unit differences. Thus any inverse used by this action is justified over Z/N; no field-only target separation assumption is hidden.

## Exact native paired contraction

For any acquired native y, put z=y^b and

    w_j(y)=(L^-1 v(y))_j=sum_(r=0)^j u_r y^(j-r),
    v(y)=(1,y,...,y^(b-1))^t.

Equivalently w_0=1, w_j=y w_(j-1)+u_j. The ORIGINAL polynomial is exactly

    P_ell(y)
      =sum_(j=0)^(b-1) h_j w_j(y)
           sum_(rho=0)^(T-2) g_rho y^(b rho)/(lambda_j-U_rho)
       +c_ell y^(b(T-1)) w_(b-1)(y).                 (*)

This follows from P_ell(y)=(1,z,...,z^(T-1)) C v(y), inserting C=M L^-1 and the preceding complete description of M. It is genuinely derived from the native pencil, unlike the separate unproved resolvent ansatz in the shared-resolvent scratch.

For ONE y, acquire y^b, its T powers, all w_j(y), and perform one Cauchy action: soft(b+T). For J native points, doing these operations separately costs soft(J(b+T)), approximately k^2. A single Cauchy matvec is therefore insufficient. Formula (*) asks for Cauchy-weighted contractions in which both the weights y^(b rho) and the test vector w_j(y) vary with the SAME native point.

All u,h,g and both node lists have soft(b+T) acquisition and representation. The displayed b(T-1) Cauchy entries are NOT acquired individually. There is no output-count lower bound here: an implicit paired-curve contraction might bypass that rectangle. No such fast contraction has been supplied. The existing soft sqrt(J ell) (or shorter-horizon scalar) evaluator remains necessary for a proved completion.

## Independent audit of the varying-quotient Ore report

The formulas in `/tmp/semiprime-varying-quotient-recurrence-20261024/ore-recurrence.md` check: scaled quotient transport, the ordering in D^m=z^-m prod_(r<m)(1-q^-r S), the unit highest-shift coefficient, and the reversed-convolution recurrence-row oracle. The full horizon h<16H also makes (q;q)_n units through n=h, but acquiring all h factorials exceeds the intended soft-k budget.

For the normalized generating function W_(q,X)(t)=sum P_n(X)t^n/(q;q)_n, the exact formal identities are

    W_(q,X)(t)=E_q(t)/E_q(Xt), E_q(t)=sum t^n/(q;q)_n,
    W_(q,X)(t)W_(q,X)(-t)=W_(q^2,X^2)(t^2).

This resembles Graeffe but does not furnish a bounded-degree rational denominator for Bostan-Mori. For example its even coefficient sequence is

    [t^(2n)]W=(X;q^2)_n(Xq;q^2)_n /
                    ((q;q^2)_n(q^2;q^2)_n),

so parity decimation doubles the hypergeometric parameter lists; further iterations keep increasing them. No soft-k advancement of F(D) follows from this identity alone.

## Extension to the actual shorter horizon, with a partial last stripe

The same derivation works for arbitrary ell and stripe width b, with T=ceil((ell+1)/b) and r*=ell mod b. Set c_n=0 for n>ell, so the last row is genuinely partial; no extra factors are introduced. The coefficient recurrence continues to prove the exact original pencil, with g_(T-1)=0. The unique resonant cell is now (rho,j)=(T-1,r*), since ell-j=b rho. The homogeneous last row of M has only that cell nonzero, and M[T-1,r*]=c_ell: in C L, all entries of C to its right are zero. Consequently (*) becomes exactly

    P_ell(y)
      =sum_(j=0)^(b-1) h_j w_j(y)
           sum_(rho=0)^(T-2) g_rho y^(b rho)/(lambda_j-U_rho)
       +c_ell y^(b(T-1)) w_(r*)(y).                 (**)

All previous Toeplitz formulas remain valid. Off-resonance exponent differences have absolute value at most ell+b. Require ell+b<16H for the simple global-unit certificate, including all h and u numerators. For the actual ell=h=O(k^(3/2)) and b approximately sqrt ell, the explicit source bound h<=8k^(3/2)+7+8/H, k>16, supplies this margin; the asymptotic big-O description alone is not used as a finite-input guard.

Choosing b approximately sqrt(ell+1), T approximately sqrt(ell+1), acquires both nodes, both Toeplitz kernels, h and the source's selected coefficient/boundary lists in soft sqrt ell. One native evaluation by Cauchy action costs soft sqrt ell. J separate native evaluations therefore cost soft(J sqrt ell), which is about k^(7/4) at ell about k^(3/2). The earlier k^2 cost refers specifically to the original ell=3k^2-1, b=k, T=3k setup. Neither bound improves the already available soft sqrt(J ell) aggregate query. The unresolved paired contraction (**) now applies directly to the actual shorter horizon, without padding, extra factors or a tail guard.

No shared/frozen file or numerical campaign was changed or run.
