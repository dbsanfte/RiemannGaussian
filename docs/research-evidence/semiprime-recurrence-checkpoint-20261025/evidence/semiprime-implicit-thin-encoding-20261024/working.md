# Direct implicit tensor encodings: paid digit/box primitives and the retained output problem

24 October 2026. Separate substantive followup. Neither frozen block-literature.md nor the integrating packet was edited. There ARE sub-b acquisition primitives for actual non-parity tensor masks; one must not infer that every encoding needs all b coefficients. The exact whole shared encoding and a terminal-product reduction are nevertheless not acquired below. No endpoint speedup is claimed.

## 1. Actual native cut and the exact tensor forms to supply

Use the acquired rough torus/native quadratic input and restriction consumer pinned in `/tmp/semiprime-rough-block-composition-20261024/block-literature.md`, SHA256 `86fd66adb32e7b18cdfaf787d2bde4971c93c0a14941f1ef9df0debaf54b2ee3`. Write q=z, C=16k^2, L=2k^2+2. q is a unit with every 1-q^r, 1<=r<=C, actually certified unit in the constant-rank quadratic algebra B. Its local component orders are odd. For the proposed large-b cut take 1<=b<=L and

    P_b(X)=prod_(i=0)^(b-1)(1-q^i X)=sum_(n=0)^b c_n X^n.

The exact convention for the covered block is

    prod_(r=0)^(b-1)(V_j-q^(ab+r))
       =V_j^b P_b(q^(ab)/V_j).

Write L=A b+d, 0<=d<b. Thus the full B-valued product is the acquired unit prod_j V_j^L times prod_(j,a<A) P_b(x_(j,a)) and the exact tail prod_j P_d(q^(Ab)/V_j), where x_(j,a)=q^(ab)/V_j. Every V_j is a certified unit; acquire its inverse as bar(V_j)/Norm(V_j). The K=J A actual full-block arguments cost soft K, with all original row/block labels retained. Each factor 1-q^r x_(j,a) equals (V_j-q^(ab+r))/V_j, so its zero is precisely an ORIGINAL bounded leaf, not an alias. For b=k^alpha with fixed alpha>3/2, K=O(k^(3-alpha)); avoiding the degree-b coefficient acquisition could therefore matter. The task is to retain this exact product/restriction convention. The negative pure giant clock of Section 6 is a separate auxiliary primitive, not this full target list.

Primary source: [Alman–Vassilevska Williams, arXiv:2610.06783v1](https://arxiv.org/abs/2610.06783), Sections 2.2--2.4. The tensor is Schoenhage's simultaneous inner/outer-product identity; the paper's new pruning shares whole leaf encodings across tiles. Its encoded leaf numbers are

    Phi_tau(a)=sum_u a[u] prod_(ell=1)^h phi_(tau_ell)(u_ell),
    Psi_tau(b)=sum_v b[v] prod_(ell=1)^h psi_(tau_ell)(v_ell).

These are exact linear forms, not arbitrary black-box matrix inputs. Arrays have seven letters per tensor position. Only strings with an inner set Q of cardinality m are active; D=4^m is the matrix inner dimension and N0=3^(h-m) its block outer dimension. The actual shared array includes MANY active Q, with Q-dependent row/column blocks. This cardinality and block assignment matters below.

## 2. Exact digit masks and a cheap pure-power side

Flatten the four inner letters p11,p12,p21,p22 to radix-four digits 0,1,2,3, and similarly q11,q12,q21,q22. At one inner position the NONZERO left masks are

    P11:e0, P12:e1, P21:e2, P22:e3,
    P31:-(e0+e2), P32:-(e1+e3).

P13,P23,P33 and P0 have zero left inner mask. Right masks are

    P11:e0, P12:e1, P21:e2, P22:e3,
    P13:-(e0+e1), P23:-(e2+e3),

and P31,P32,P33,P0 are zero on the inner right variables. On an OUTER position Pij selects x_i on the left and y_j on the right; P0 selects minus the sum of all three x letters and the sum of all three y letters.

Fix Q and one outer row/column entry. If the inner input is the pure-power vector (x^n)_(0<=n<D), then any tensor digit mask w gives

    sum_(0<=n<D) x^n prod_(s=0)^(m-1) w_(s,digit_s n)
       =prod_(s=0)^(m-1) [sum_(d=0)^3 w_(s,d) x^(d*4^s)]. (1)

This is an executable O(m) ring-operation encoding after the actual power table x^(4^s), built by repeated fourth powering. Singleton factors are monomials; the left pair factors are signed monomials times 1+x^(2*4^s), and right pairs use 1+x^(4^s). No nonunit value is inverted. x can even be nonunit. A fixed actual target therefore supplies this pure-power inner encoding in soft log D, rather than D entries.

The qualifications in (1) are essential. Outer digit masks may sum MANY actual targets, and distinct Q use different block assignments. Equation (1) is not a claim that the whole Psi_tau of a row/column band is one product of m binomials.

Also, if ONLY one Q is active, then at each inner position the left column-pair cases P3j have zero right mask, and the right row-pair cases Pi3 have zero left mask. P0 has zero inner masks on both sides. Only the FOUR matching singleton products remain. The identity restricted to that lone inner product therefore returns its ordinary four terms per digit. The paper's batching savings require the other active-Q/outer-variable interactions; a cheap isolated mask does not itself establish those savings.

## 3. Coefficient-side sparse masks: exact sub-b acquisition

Let f(n)=prod_(r=1)^n(1-q^r), f(0)=1. All these products through b are units, and the actual q-binomial identity gives

    c_n=(-1)^n q^[n(n-1)/2] f(b)/(f(n) f(b-n)).       (2)

For T explicitly requested prefix indices in [0,b], all f(n) are acquired in soft(sqrt b+T): build/store dyadic block polynomials prod_(r=1)^d(1-q^rY) through d of order sqrt b; acquire every full coarse-block prefix by monic MPE and multiplication; refine the requested residual intervals with the stored dyadic polynomials, one MPE per size. At each size there are at most T real starting points, so their total refinement cost is soft(sqrt b+T). This is a ring-safe initialized algorithm, not a free arbitrary-prefix oracle. Only the later coefficient use divides its certified unit outputs.

Consequently any t explicitly supported coefficient positions c_n, including q phases and unit denominator inversions, cost soft(sqrt b+t). A fixed inner-mask subcube has at most 2^m=sqrt D positions. If the digit dimension D is of order b, ONE such coefficient form is acquired in soft sqrt b. A concrete non-global-parity mask fixes the low digit to 0, restricts the next digit by -(e0+e2), and fixes higher digits to 0: its exact supported positions are 0 and 8 and its value at x is

    -1-c_8 x^8,
    c_8=q^28 prod_(r=0)^7(1-q^(b-r)) / prod_(r=1)^8(1-q^r)

for b>=8, and -1 otherwise. It costs O(log b), not b. This is a literal tensor-mask formula, not an extrapolation from parity.

The companion `digit-mask-attempt.md` proves this sparse-mask primitive and a useful clock extension: after acquiring the t supported coefficients, ONE fixed mask on x_g=x0 Q^g has a generating function sum_n d_n/(1-Q^n T), with constant-one denominator and all numerator/denominator coefficients acquired by weighted product trees. ALL R consecutive clock values cost soft(sqrt b+t+R); spectral collisions are harmless. It does not acquire all different masks or arbitrary outer-row sums. The prefix construction and its proof do not import a field theorem into B.

## 4. Additional positive primitive: selected AP coefficient-box sums

Outer masks are not necessarily sparse coefficients, but their box structure can also be used without enumerating all covered coefficients. Here is a complete initialized version.

For ONE supplied scalar x, put w_n=c_n x^n. Fix a stride D>=1 and residue 0<=a<D, with a<=b. Let n=a+D rho. The exact transition ratio, used as a cleared identity even if x is nonunit, is

    B(q^n) w_(n+D)=A(q^n) w_n,
    A(X)=(-1)^D x^D q^[D(D-1)/2]
                         prod_(v=0)^(D-1)(X-q^(b-v)),
    B(X)=prod_(v=1)^D(1-q^v X).                    (3)

It follows directly by dividing (2) at n+D and n, then clearing denominators; no algorithm divides w_n or x. These degree-D coefficient arrays are acquired by geometric product trees ONLY in the branch D<=sqrt b below, where soft D fits the budget. The D>sqrt b branch skips both arrays and directly samples its fewer than sqrt b+1 coefficients. For a legitimate transition to a next selected coefficient n+D<=b, every denominator factor has exponent n+v<=b and is a certified unit.

Write Q=q^D. For state (w_rho,S_rho), S_rho=sum_(t<rho)w_(a+Dt), use the polynomial numerator matrix

    M(X)=[[A(X),0],[B(X),B(X)]],
    (w_(rho+1),S_(rho+1))^t
       =B(q^(a+D rho))^(-1) M(q^(a+D rho))
                                      (w_rho,S_rho)^t.             (4)

The initial w_a is acquired by (2), S_0=0. For a prefix ending at coefficient a+D rho, perform rho transitions and return S_rho+w_rho. In particular a sum of ell terms needs ell-1 transitions, then its final term is added. No extra denominator beyond the last selected coefficient is introduced. The scalar denominator of the rho-transition product is exactly

    f(a+D rho)/f(a),                              (5)

an actually certified unit ratio, acquired from the prefix lemma. Inverting it after acquisition is lawful even when the final sum is zero.

### Pay all requested box endpoints for one residue

If D<=sqrt b, take a dyadic block length s of order sqrt b/D (or 1 near the boundary). Its numerator matrix polynomial has degree O(Ds)=O(sqrt b). Acquire all dyadic matrix blocks through s by the exact recurrence B_(2s)(X)=B_s(Q^s X) B_s(X); the order of multiplication is as displayed. The entire polynomial table costs soft sqrt b.

There are O(sqrt b) full blocks along rho<=floor((b-a)/D). Monic MPE acquires every full-block matrix at its real starting q power, then literal matrix prefix products give all coarse prefix states. Refine T requested residual prefixes by dyadic blocks. Each size uses one MPE at at most T actual starts; the polynomial degree is at most O(sqrt b). Total numerator-matrix acquisition is soft(sqrt b+T). Acquire all (5), starting coefficients and required q powers in that same budget, then apply the matrices and add the last term. This gives every requested inclusive coefficient-prefix sum, with all starts and outputs paid.

If D>sqrt b, the residue has fewer than sqrt b+1 coefficient indices. Acquire them all by the sparse coefficient-prefix lemma, accumulate their sums, and answer the T requested endpoints. This also costs soft(sqrt b+T). Thus for ANY stride D, ONE fixed residue and ONE supplied x admit

    soft(sqrt b+T)

for T explicitly requested coefficient-prefix sums. Interval sums are differences of two inclusive prefixes (with prefix -1 equal zero), never ratios of sums. For K distinct residues sharing x, the direct proved bound is soft(K sqrt b+T_total), plus enumeration of the requested residue/endpoints; no sharing across different x is assumed.

This is a real coefficient-box acquisition shortcut. It handles arbitrary zero sums and nonunit x, uses only the stated q-prefix unit denominators, and does not need to form the degree-b Pochhammer coefficient vector.

## 5. Exact fixed-Q and whole-band forms, including outer boxes

Here is the form the paper actually requires on a coefficient reshaping, rather than a promise that all encoders are parity filters. Let a scalar coefficient matrix be

    C[r,d]=c_(D r+d), 0<=d<D,

with coefficients outside [0,b] set to zero. In one row band, active inner sets Q of size m select row blocks r_Q (the public grid assignment of Section 2.3.4). Let R0 be the band's real starting row and rho the base-three index of its h-m outer digits. Then its exact leaf encoding is

    Phi_tau(C)=sum_(Q active) sum_(rho<N0) sum_(d<D)
       c_[D(R0+r_Q N0+rho)+d]
       *prod_(ell notin Q) phi_(tau_ell)(x_(digit_ell rho))
       *prod_(ell in Q) phi_(tau_ell)(p_(digit_ell d)).   (6)

Zero/padded matrix entries are omitted exactly; repeated r_Q assignments are not silently treated as different coefficients. Formula (6) is the required family of linear forms with actual block offsets.

For a fixed Q, any P0 on Q makes its summand zero. Otherwise at the s positions where tau=P0, the OUTER digits are free ternary choices; other outer digits are singletons. This row set is a radix-three box, decomposable into at most 3^s contiguous row intervals (possibly fewer by merging its trailing free digits). The inner mask selects at most sqrt D radix-four residues. Therefore one fixed-Q summand of (6) is a known signed sum of AP coefficient intervals with stride D, shifted by the actual row-block offset. Section 4 acquires it at the proved bound

    soft(sqrt(D b)+T_Q),
    T_Q <= O(sqrt D * 3^s),                         (7)

using one AP-prefix computation per selected residue and the actual interval endpoints. At boundaries, intersect intervals with [0,b]; do not include a nonexistent final coefficient. Constant signs from pair/P0 digits are known and kept. This bound is not b, although it can still be too large after many Q/leaves.

A corresponding Vandermonde right band has exact form

    Psi_tau=sum_(Q active) sum_(eta<N0) outer_weight_(tau,Q)(eta)
                 *prod_(inner positions s in Q)
                    [sum_(d=0)^3 inner_weight_(tau,Q,s,d)
                          x_[J0+c_Q N0+eta]^(d*4^s)],              (8)

where c_Q is its actual column-block assignment and J0 its band start. Powers in the product use the radix positions after restricting to Q. Equation (1) pays each FIXED actual target's inner product. The outer weighted target sum in (8) and the active-Q summation must still be enumerated, shared by an acquired identity, or otherwise charged.

For the whole encoding family, write K_tau for the number of distinct residue sequences actually required in its AP decomposition, T_tau for all requested interval endpoints, and A_tau for the cost to enumerate the active-Q/box descriptions. A direct established bound is

    soft(K_tau sqrt b+T_tau+A_tau)

per coefficient encoding, with possible actual reuse when the same residue/endpoints occur in several summands. One must count their UNION across all wanted leaf encodings, not separately assume every scalar form costs soft sqrt b. That union can include many row-singleton requests or many distinct weighted x parameters. No soft-k bound for that actual union, nor a proof of enough vanishing full encodings to skip it, has been obtained here.

### Counts for the actual paper layout, with native b and K explicit

For the Section 2 layout take h=19m, D=4^m, A_Q=binom(19m,m), N0=3^(18m), and K0=floor(sqrt(A_Q)). One band has K0*N0 outer rows; its grid assigns K0^2 active Q (or zero-padded omissions). At a leaf that contributes to a wanted output, s=#P0<=m. A nonzero left input Q must avoid all P0 positions and any position with a zero left inner mask; there are at most binom(h-s,m)<=A_Q possibilities before the actual grid restriction.

For one scalar coefficient band, the direct nonshared bound from (7) is

    soft(A_Q*sqrt(D*b) + A_Q*sqrt(D)*3^s + A_Q*h).     (9a)

This includes descriptions of actual row boxes and their offsets. Sharing SAME residue sequences across Q can replace the first term by D*sqrt(b); the number of distinct requested prefix endpoints is at most min(O(A_Q*sqrt(D)*3^s),O(b+D)). But enumerating the original active-Q/box incidences must still be paid unless a separate compressed sharing algorithm supplies them. Endpoint deduplication alone does not make that description cost disappear.

The paper's UNMODIFIED encoding phase writes ALL 10^h leaf numbers for every band, independently of the wanted set. On the coefficient reshape there are Rb=ceil((b+1)/D) real rows. Even counting only ceil(Rb/(K0*N0)) nonzero row bands, the number of written encoding slots is

    ceil(Rb/(K0*N0))*10^h.

It exceeds the b+1 coefficient slots: 10^h>K0*N0*D for h=19m. For example the purely symbolic bound K0<=2^(h/2) gives

    10^h/(K0*N0*D)
      >= [10^19/(2^(23/2)*3^18)]^m >1.

This is a count of that full encoding algorithm's outputs, not a lower bound on direct implicit encodings or on distinct functional values. A sub-b implementation MUST therefore deviate from the full preencoding phase: acquire only the wanted-leaf union, prove enough shared/repeated/zero forms, or provide another compressed transform. The current paper does not assert that implicit q-Pochhammer arrays make those forms vanish.

For native b<=L=O(k^2) and K=J floor(L/b), the matrix reshape's natural square padding is S=max(Rb,K), with D<=S^(1/18) for the quoted thin theorem (the tiling can further zero-pad). Substituting this small D into (9a) can make individual encoders inexpensive; it does NOT count the number of different encoders requested by an exact product reduction. That latter union is the still-unacquired quantity, particularly when wanting all Rb*K partial values of (10), or the target-weighted left inputs of (11).

## 6. Global parity on the auxiliary pure giant clock is also cheap, but does not cover (6)

For x_a=q^(-ab), 1<=a<=floor(L/b), with a=0 handled separately, put S=a b^2-b(b-1)/2. Directly reversing its negative exponents gives

    P_b(x_a)=(-1)^b q^(-S) f(ab)/f(ab-b),
    P_b(-x_a)=q^(-S)
        [f_(q^2)(ab)/f_(q^2)(ab-b)]/[f(ab)/f(ab-b)].    (9)

At a=0 use P_b(1)=0 and P_b(-1)=2 f_(q^2)(b-1)/f(b-1). All prefix indices are <=L, and q^2 prefixes need only q differences through 2L<C. Batch-prefix construction therefore acquires ALL these clock values in soft sqrt L=soft k in the proposed b>k^(3/2) regime, including their actual phases and denominator inverses. The even/odd coefficient forms are (P_b(x_a)+/-P_b(-x_a))/2.

These are valid initialized filters; an auxiliary zero at x_0=1 is not an original factoring witness. Higher-digit conditions are not all two-character parity filters. For example a condition on bit 2s has period 2*4^s and generally growing root-of-unity Fourier support. Sparse-mask and AP-prefix methods above work without claiming constant Fourier support. Equation (9) does not replace the block-dependent boxes and active-Q sums in (6), nor does it supply arbitrary target-weighted versions for free.

## 7. Execute a terminal-output reduction attempt and expose the remaining operation

Consider the direct matrix evaluation of P_b at the K original scaled targets x_j. With Rb=ceil((b+1)/D), reshape c_n as C[r,d] and multiply by Y[d,j]=x_j^d. Requested entries are

    A[r,j]=sum_(d<D)c_(Dr+d) x_j^d,
    P_b(x_j)=sum_(r<Rb) (x_j^D)^r A[r,j].          (10)

The positive implicit encoders above can support individual left forms, and pure powers support individual right inner forms. Nevertheless the thin-product theorem delivers INDIVIDUAL entries A[r,j], not the final weighted column contractions in (10) or their product. Executing (10) literally asks for Rb*K partial values. Since K is of order JL/b, this count is of order JL/D. In the natural square padding S=max(Rb,K), D<=S^(1/18) is very thin. More explicitly, for b>=k^(3/2), b<=L=Theta(k^2), and the full J=Theta(k) family, S=O(k^2), so D=O(k^(1/9)); the partial-output count is Theta(JL/D), at least of order k^(26/9). This is a count in this literal reduction with explicit partial outputs, not a generic query lower bound. No sub-k^(3/2) completion follows from asking for all those partial values, even if their input encodings were free. This is a failure of this explicit reduction, not a lower bound on an implicit weighted-output algorithm.

Alternatively force only K wanted diagonal outputs by first folding the coefficient rows:

    X[j,d]=sum_r c_(Dr+d) x_j^(Dr),
    Y[d,j']=x_(j')^d,
    (XY)[j,j]=P_b(x_j).                            (11)

This DOES identify the correct wanted outputs, but its left input is now the residue-class polynomial evaluated at a native x_j, not a scalar coefficient mask at 1. Its leaf encodings require the corresponding NATIVE target-weighted box forms in (6), with x=x_j and row exponents included. Section 4 pays them for ONE x, not simultaneously for all K native parameters. The giant-clock identities (9) do not apply to general q^(ab)/V_j. Treating those entries or their encoded combinations as already acquired would simply hide the original Pochhammer evaluation problem. Moreover a K-by-K square invocation has preprocessing of order K^2/D^0.063, already near k^2 when K=Omega(k) and D is thin. Packing K values into a smaller outer square would need a new native factorization across its row/column labels; none has been acquired from the bounded norm fibers or tag congruence.

The product of the correct P_b(x_j) values still needs its original restriction interface. Individual mask zeros, partial-output zeros, spectral aliases or arbitrary decoded box zeros are not substitute leaves. A completed route could use (11) or a different exact reduction, but must pay its whole encoding union and preserve original row/interval labels through the final product. No such faster complete reduction has been obtained here.

## 8. Outcome and attribution

This followup proves usable implicit input primitives rather than insisting on dense input: pure-power digit encodings cost soft log D; sparse q-binomial leaf forms cost soft sqrt b; a fixed residue's requested AP partial sums cost soft(sqrt b+T); actual coefficient row boxes follow (7); actual unmasked/parity giant-clock values follow (9). Their proofs retain all starts, true unit denominators and zeros. The companion digit-mask report adds a paid consecutive-clock batch for one sparse mask.

The unacquired object is precisely the UNION of the active-Q, row-band and leaf forms (6)--(8) needed by an exact restricted terminal-output reduction, including any native target weights in (11). It is not enough to know that a single digit mask factors or that a small number of coefficient samples is cheap. The source tensor's single-active-Q restriction collapses to ordinary singleton inner products, so that restriction cannot claim the paper's batching gain. No exponent saving or full factoring-query acquisition is claimed on the current evidence.

Primary tensor PDF cached in the preceding block packet: `sources/thin-products-2610.06783.pdf`, SHA256 `d91a79c5dbf1fc662f0c5c1bb2b690ac3d83d9ef5bf872bde4cdaf7cc9e76005`. The prefix/refinement arguments are explicit ring-safe instances of the standard q-block approach, consistent with Bostan--Yurkevich's multi-index refinement; no fixed-degree field theorem is applied to an unpaid growing coefficient algebra. Companion proof: `digit-mask-attempt.md` in this directory, frozen SHA256 `300952af3de79e56b9c90d4fe02c756e640273a3e2db444010c0c79d7cb07400`, with independent review recorded separately. This report makes no absolute novelty or generic lower-bound claim.
