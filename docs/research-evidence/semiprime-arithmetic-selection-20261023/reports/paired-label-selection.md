# N-dependent paired labels: exact convolution and the remaining arithmetic query

23 October 2026. Scratch only; no repository changes. This studies the actual P/Q coupling and does not invoke the earlier residue-wise universal ratio-menu limitation. No soft-r factor detector was obtained. The positive acquired operation is a soft-r convolution over all paired AP labels, and the new exact arithmetic organization includes a finite coefficient carry in the monic case and an all-input short linear partner clock.

## 1. The exact paired-label map and its carries

Let N=P Q<=r^6, H=r^2, M=H^2, P<Q and P,Q>16H. For proof-only true multipliers set

    c=P^(-1) modr, d=Q^(-1) modr, 1<=c,d<r,
    s=cP modH=1+ru, t=dQ modH=1+rv,
    0<=u,v<r.

Put nu=N^(-1) modr in [1,r-1]. For each public c, the candidate d is

    d_c=nu*c^(-1) modr.

All r-1 candidate pairs are acquired in soft O(r) bit work. Set

    k_c=c*d_c=nu+r*z_c, 0<=z_c<r,
    kappa_c=((N*nu-1)/r+N*z_c) modr.                    (1)

The quotients are exact integers, with O(log N) bits. Since st=cdN modulo H,

    v=kappa_c-u modr.                                  (2)

If kappa_c and u are canonical, write

    v=kappa_c-u+r*epsilon,
    epsilon=1 if u>kappa_c, otherwise 0.

Thus u+v is kappa_c or kappa_c+r. This is the canonical reflection carry. The full product carry is a different, generally large integer:

    R_(c,u)=(k_c*N-s*t)/H.

Writing cP=s+Hh and dQ=t+Hj gives

    R_(c,u)=s*j+t*h+H*h*j.                              (3)

Do not replace this exact integer by its residue or by the binary reflection carry. For balanced inputs h,j can both be order r^2; for unbalanced inputs j can be still larger.

The map is simply the modular-hyperbola involution x->N/x expressed in these labels. It is N-dependent, not an independent choice of two residue classes. It has r(r-1) labeled pairs (s,c), with the partner fully determined. This cardinality is bookkeeping, not an algorithmic lower bound.

## 2. An actually acquired coupled convolution

Let A_u and B_v be ANY supplied ring weights indexed by the AP labels. One cyclic convolution gives

    Z_kappa=sum_(u=0)^(r-1) A_u*B_(kappa-u modr)

for every kappa. All reflected paired sums Z_(kappa_c) are then r table lookups. This costs soft O(r) ring/bit work for O(log N)-bit coefficients. It needs no roots of unity modulo N: use ordinary polynomial multiplication and folding modulo X^r-1.

If the two exact reflection carries must remain separate, compute the ordinary length-2r-1 convolution first and retain coefficients at kappa and kappa+r. This keeps their distinction at the same asymptotic cost. Grouping multiple source descriptors by their AP label also costs softly their total descriptor volume. Any supplied subset of candidate c values can be retained or summed by a mask on the r lookups without rebuilding r separate convolutions; this remains only access to the same additive data.

This is useful only for a supplied separable witness predicate/weight. The catalog has at least one descriptor over every AP label, so pairing unweighted support cannot distinguish the two true labels. The zero/nonzero collision indicator is not among the supplied weights. An additive convolution of available phases is not silently promoted to a norm or to an integer-root selector.

## 3. Paired quadratic coefficients have a stronger linear relation

Suppose two actual descriptors over s and t have coefficients

    CN=a*s^2 modH, C'N=a'*t^2 modH,
    a,a' units modr.

Since s,t are 1 modulo r, (s-t)^2=0 modulo H. Consequently

    a'*C+a*C' = 2*a*a'*k_c modH,                       (4)
    C*C' = a*a'*k_c^2 modH.                            (5)

The linear relation (4) is often a cleaner pairing key than (5). Its exact integer carry must still be retained.

For two monic rows a=a'=1 with centered |C|,|C'|<=floor(H/2),

    C+C'=2k_c-eH, e in {0,1,2}.                        (6)

Thus there are only three coefficient-sum carries. In the balanced A=1 catalog, write C=nu+r*i and C'=nu+r*i' with consecutive signed index intervals. Equation (6) becomes

    i+i'=2*z_c-e*r.

All separably weighted coefficient pairs, with each of these exact carries retained, are again ordinary convolution coefficients. This is a genuine source organization and paid additive contraction, not a source norm evaluation.

It does not force equal or square-related discriminants. On the already retained prepared instance r=43, P=59447, Q=59747, the actual monic pairs have

    c=41, d=28, k=1148,
    C=331, C'=116, B=1082824, B'=-453996,
    e=1,
    D0=(B^2-4CN)/M=-1032540,
    D0'=(B'^2-4C'N)/M=-421760.

They are unequal and their product 435484070400 is nonsquare. The paired coefficient determinant k^2-CC'=1279508=H*692 has nonsquare quotient 692. These are direct computations on the same prepared instance, not an extra example search. Thus those proposed forced equality/square shortcuts are false even on a prepared branch.

## 4. The exact two-quadratic elimination, and its cost

If both true quadratic seeds are short, write

    U=M*sigma-B*c=a*c^2*P+C*Q,
    V=M*tau-B'*d=C'*P+a'*d^2*Q.

The determinant is

    Delta_pair=a*a'*k_c^2-C*C', H divides Delta_pair.

When it is nonzero,

    P=(a'*d^2*U-C*V)/Delta_pair,
    Q=(a*c^2*V-C'*U)/Delta_pair.                        (7)

The numerator/divisibility and PQ=N conditions give a conic in the two seeds. Equation (7) is an exact recovery/elimination relation. It does not supply sigma,tau. If Delta_pair=0, one gets a rank-one relation, not permission to divide by zero or an automatic factor.

For balanced factors the two monic catalogs each have r descriptors, and their matching pairs are grouped by the convolution above. But explicitly reporting all compatible labeled row/c pairs still has an O(r^2) cost in this construction. Applying an integer small-root algorithm separately to each candidate pair therefore has not met the soft-r target even if its individual cost is polylogarithmic. No generic lower bound is intended.

There is an additional all-input scope issue: the original quadratic catalog is windowed on the SMALLER factor. For an unbalanced Q>sqrtN, putting Q0 near Q would give floor(sqrtN/Q0)=0, so one cannot claim a second short quadratic clock from the same theorem. The next section supplies a correct inherited linear partner instead.

## 5. A whole-input short linear clock for the partner

For every t=1+rv acquire

    b_t=center(-N*t^(-1) modH),
    G_t(Z)=H*b_t*Z+H*N.

Here b_t is a unit modulo r and |b_t|<=H/2. The polynomial satisfies G_t(t)=0 modulo M and G_t'(t)=0 modulo H. At the true dQ=t modH it gives

    H*tau=b_t*d+P, |tau|<r/2+sqrtN/H<=1.5r.            (8)

Thus the Q partner has a short integer seed for EVERY size window. This is the inherited normalized cofactor-GP/linear source, not a new sixth-rate detector.

The label coupling yields

    b_t*k_c+s=H*ell_(c,u),
    h=c*tau-ell_(c,u),                                 (9)

with an exact publicly computable integer ell for each candidate (s,c). The first congruence follows from t=k_c*N/s modulo H and b_t=-N/t modulo H. Substituting (9) into the P-row relation gives a bivariate integer equation in TWO short seeds:

    g(c*tau-ell)=sigma*(H*tau-b_t*d).                   (10)

Both |sigma|<3.5r and |tau|<1.5r are valid all-input bounds. The candidate factor is simply

    P_candidate=H*tau-b_t*d.

At any integer solution of (10) in the genuine factor window, a proper gcd with N recovers a factor. Indeed (1) from the preceding arithmetic-detector report gives P_candidate|CN, since P_candidate divides both g(h) and Hh+s=c*P_candidate and H is a unit modulo P_candidate. If gcd(P_candidate,N)=1, then P_candidate|C, impossible when P_candidate>=P0>=16H>|C|. P_candidate<N excludes a saturated gcd. Thus no prepared-base collision is needed after such a bounded arithmetic solution has actually been acquired.

Equation (10) is the concrete paired arithmetic target. Its coefficients and ell have O(log N) bits and all candidate metadata are public. The remaining issue is **total** acquisition across the still two-indexed (s,c) candidates. Recomputing its coefficients or performing a separate bivariate root search for every one costs O(r^2) times a polylogarithm. Pairing alone does not supply the required contraction.

For a fixed candidate, the factor window restricts tau to an interval of length P0/H, often much shorter than r. Exploiting this without expanding all residue/multiplier labels is necessary; enumerating these candidate factors globally merely recovers the inherited direct interval/divisor search.

## 6. What remains in a paired convolution of phases

The favorable coefficient sum in (6) makes the product W(C)W(C') depend only on k and e for monic rows. The actual exponential phase still contains

    B(C)*c+B(C')*d.

For each c the needed convolution would use coefficients V(C)^c and V(C')^d, with d=nu/c modr, and extract its c-dependent sum index. Canonical centered cubic phases and their integer carries are part of these values. One convolution with fixed input weights does not provide all these changing convolutions. Performing r ordinary convolutions costs soft O(r^2); deleting the phase or its carries changes the query.

Thus an actual positive continuation could contract this diagonal family of coupled convolutions with a proved detection link, or solve (10) jointly across the O(r) acquired row descriptors without expanding the c dimension. An additional fast additive statistic without such a link would not close acquisition.

## 7. Primary-literature check and scope

Hittmeir, *Integer factorization as subset-sum problem*, arXiv:2205.10074, Sections3-6, explicitly uses the modular hyperbola and its projection to factor sums. The rigorous sieve improves a divisor-difference-dependent Fermat bound; its further isolation claim after increasing the modulus is explicitly heuristic (equation5.1). The inspected result does not supply a guaranteed soft-r selector for the paired carry/phase problem above. Primary PDF: https://arxiv.org/pdf/2205.10074 . This is a relevant existing use of the same factor coupling, not a newly discovered reduction.

The previous residue-universal menu count does NOT decide this N-dependent problem. The positive results here are the exact reflected-label and coefficient-carry convolution, the correct all-input partner clock, and the exact short-seed arithmetic equation (10) with direct gcd recovery. A whole-family algorithm acquiring a solution/nonunit in soft O(r) is still missing. No repo edits, frozen-packet edits, or backend claims were made.
