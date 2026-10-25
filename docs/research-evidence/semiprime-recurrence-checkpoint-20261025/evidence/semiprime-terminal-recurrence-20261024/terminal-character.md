# Terminal character attempt: cleaned blocks, actual tail state, and q-shift initialization

2026-10-24. Scratch only; no repository edits, examples or backend work. This executes a longer unit-support prefix, the ensuing block-elimination state, and the scalar q-shift update. The positive helper extends complete auxiliary cleanup from two pivots to a logarithmic prefix at soft m on the balanced native rectangle. It is NOT the endpoint advance: the actual tail still has degree n-O(log n), and neither block doubling nor phase cancellation acquires its absorbing zero mask in soft m. The complete original query retains soft(J+sqrt(JL)).

## Read inputs and duplicate boundary

Read character-endpoint/character-resultant.md (87c7b82b0bcc516f63d8ff4f1f81f2214f1e8c4e3e23083072470d7c2a672fb1), half-norm-cancellation.md (b0185cb2ab94f4224ebe3133dabe0a1cb5179f87ecfe22907f72160b93118889), tensor-norm/sylvester-elimination.md (f3375df02a067a43230d1f4accddc476bbbe020a64c9145b90757ba5404720c2) and geometric-generator.md (8ff92a623b50d8698b34260ab01216f3d17ad89c26c5a88831561d3602aa581a). Their exact original-leaf, auxiliary-pivot and unit-argument distinctions remain in force.

The scalar target is E_L=product_(i<L)F(q^i), F monic of degree J~m, L~m^2. The sufficient output is its absorbing unit mask U(E)=Jacobi(E,N)^2, with values 1 on units and 0 otherwise, uniformly under original row/interval restrictions. The old character interface, reciprocal-square identity and the fact that a known unrestricted zero does not identify a child are not new results here.

Use the balanced tensor trial n=J, s=n, t=floor(L/n), inner A(X)=product_(a<n)(X-q^a) and outer P(Y)=product_(b<t)(Y-q^(nb)). Their inputs and short tail are acquired. R=Z/N has the original prepared beta/q guard, and all required small integers and short q-differences are certified units. n,t~m for the main trial. A multiplication in the outer quotient retains its rank-t cost.

## 1. An actual logarithmic prefix-support constructor

Write A(X)=sum a_i X^i and B_Z(X)=sum f_i Z^(n-i)X^i. Define the principal polynomial p_k(Z) by the 2k-by-2k coefficient minor with columns

    A,XA,...,X^(k-1)A, B_Z,XB_Z,...,X^(k-1)B_Z

and coefficient rows n-k,...,n+k-1. This consistent sign convention has p_1=a_(n-1)-f_(n-1)Z. It agrees with the tensor principal pivots up to only the fixed standard subresultant convention sign, irrelevant to unit support.

The minor depends ONLY on the top 2k coefficients. The already proved public bound is deg_Z p_k<=k^2; at Z=0 its B columns are monomial shifts, leaving

    p_k(0)=Delta_k=det(a_(n-k+i-j))_(1<=i,j<=k).

The q-hook formula proves every Delta_k a scalar UNIT and acquires all of them in soft n. It does not certify endpoint p_k(Y^-1) values.

Choose K=floor(log2 n), capped so 2K+2<=n; bounded small n uses the existing direct query. The following completely explicit determinant algorithm acquires the ENTIRE p_k for each 3<=k<=K, without a generic pivot or a supplied polynomial oracle:

1. Form the actual 2k minor over S_k=R[Z]/Z^(k^2+1), from the acquired top coefficient lists.
2. Compute its powers through exponent 2k by ordinary matrix multiplication, acquire their traces T_r, and apply Newton identities e_0=1,

       e_h=(1/h) sum_(r=1)^h (-1)^(r-1)e_(h-r)T_r,
       det=e_(2k).

   Each integer h<=2k<n<P,Q is a certified scalar unit. There is no division by a determinant or endpoint pivot, even when the target minor is singular after specialization.
3. The determinant modulo Z^(k^2+1) is the FULL polynomial because of its proved degree bound. Thus evaluation at a unit argument is legal AFTER reversal; no unknown tail is discarded.

Naive matrix powers use O(k^4) operations in S_k, each costing soft k^2. Summing over k costs soft K^7; input/output coefficient volume is O(K^3). These are explicit, albeit deliberately elementary, bounds. For K=O(log n) this is polylogarithmic. Fast partial half-GCD may improve that local polynomial bound but is not needed for the claimed soft-m helper.

Reverse and normalize by acquired scalar units:

    h_k(Y)=Delta_k^-1 Y^(k^2)p_k(Y^-1),
    H_K(Y)=product_(k=3)^K h_k(Y).

Each h_k is monic of exact public degree k^2, even if its low Y coefficients vanish. H_K is actually acquired by a product tree, with degree D_K=sum_(k=3)^K k^2=O(K^3). Its values on the known outer nodes cost soft(D_K+t) by monic MPE. First remove the already processed first-two-pivot nodes as in the prior report, so this is a genuine extension beyond those stages.

Compute EACH gcd(H_K(y_b),N). A proper gcd factors. Otherwise every value is unit or zero modulo N, hence the bad-node set is PUBLIC and has size at most D_K. Global zero of the PRODUCT need not mean the same individual pivot vanishes at both primes; that inference is not used. Removing the entire original outer node clears every auxiliary support there, and a unit H_K value proves every included pivot a unit on that component.

At each bad node acquire the ORIGINAL n-point slice product and recover from any actual nonunit original leaf. If it is unit, record its acquired scalar and remove the node by monic exact outer division. All remaining node differences stay units. If no nodes remain, those acquired slice factors are the complete product. Every branch is defined, with no auxiliary zero assigned an original decoder.

Total helper cost is

    soft(n+t+K^7+n*D_K)=soft(n+t)

for K=O(log n). It completely clears a growing logarithmic prefix, not only two pivots, with every original-slice exception actually checked. There is NO theorem that these auxiliary supports must contain an original hit.

## 2. Actual state AFTER that prefix and the next blocked step

The helper alone is not the main goal. On the retained outer algebra all principal endpoint pivots through K are now units. For an element a of that retained outer algebra, write U_outer(a)=Jacobi(Norm(a),N)^2; removed original slice factors are acquired units and do not change this scalar mask. Unit-pivot Euclidean resultant transport therefore gives

    U_outer(Res(A,B))=U_outer(Res(R_(K-1),R_K)),                (1)

where the true remainder degrees are n-K+1,n-K. Its omitted multiplier is a certified UNIT (signs and powers of already cleared leading coefficients). For the BOOLEAN output its numeric norm/phase need not be acquired. This is a legitimate cancellation; it does not compute the tail mask on the right.

We now actually initialize its transformation state. At every retained outer node y, form the two degree-D HEAD polynomials with D=2K+2 from the top D+1 coefficients (including the monic leading coefficient) of A and B_(1/y), and run the first K ordinary degree drops. Every scalar pivot inverse is certified by the cleanup. Those quotient polynomials agree with the first K steps for the original degree-n pair: applying a cofactor matrix of X-degree <=K to the discarded low tails leaves error degree <n-D+K, below the leading/next coefficients used in these steps. This is the usual head truncation proof, supplied here rather than treating a partial gcd state as an input.

Each node needs O(K^2) scalar operations by the elementary Euclidean algorithm. Its actual 2-by-2 cofactor matrix M_K(X;y) has X-degree O(K). Across all t retained nodes the complete state costs O(tK) residues; optional monic interpolation of each coefficient into the outer quotient costs soft(tK). At logarithmic K this is soft t. The original A and diagonal B_Z input remain acquired.

The tail can therefore be retained EXACTLY as

    (R_(K-1),R_K)^t=M_K(X;Y)*(A,B_(1/Y))^t.

This is actual acquired matrix data, not just a state name. Expanding the long remainder coefficients would contain n outer-algebra vectors and cost rank t; we do not expand them for free. The cofactor representation supports next-leading coefficient convolutions at their actual cost.

For the NEXT doubled block, acquire the degree-(4K+2) head including its leading coefficient (top 4K+3 coefficients); if that degree exceeds n use the full original polynomial instead, whose degree is then O(K) and the exact pivot polynomials K+1,...,2K by the same coefficient-minor computation. Clear their aggregate support through original slices, then compute M_(2K) by the corresponding head Euclidean computation. At logarithmic K this next block is also fully initialized in soft(n+t). Thus the attempt really performs a block beyond the cleaned prefix; it does not stop at a collection of normalization constants.

Arbitrary doubling is not a free skip of the remaining n steps. At scale k the explicit pivot aggregate has degree Theta(k^3); the elementary determinant route costs soft k^7, and the endpoint cofactor state has O(kt) acquired scalar coordinates. A fast unit-pivot half-GCD on t separate specialized heads could lower arithmetic to soft kt, but that retains the factor t. Original slice exceptions can grow with the acquired support, rather than stay constantly many. These are ledgers of the displayed two representations, not a claim that another compact determinant algorithm must materialize them.

In particular equation (1) removes only K degrees. At K=O(log n) the actual tail degree remains Theta(n). Reaching a half-size tail requires a block with k=Theta(n), whose endpoint support/state is NOT acquired by the logarithmic helper. Keeping a straight-line matrix circuit instead of O(kt) coordinates is allowed, but its next mixed leading coefficient and zero mask still require an actual evaluation algorithm. A mask of an additive Schur sum is not obtained by multiplying the unit masks of its summands.

## 3. Try the q-shift scalar route instead: execute its norm update

The other concrete way around that cofactor state is to use the geometric seed transport. Let

    R_n(Y)=product_(a=0)^(n-1)F(q^aY).

It obeys the exact, division-free q-difference identity

    F(Y)R_n(qY)=F(q^nY)R_n(Y).                    (2)

Its constant R_n(0)=F(0)^n is a cheap known unit. But its actual degree is n*J, so a short formal prefix is not its value at Y=1 or an outer grid point. The cleaned principal pivots do not change this degree or provide the missing boundary value.

For this separate transport test return to the ORIGINAL full outer grid y_b=q^(nb), whose nodes were acquired initially. Do not silently apply a one-boundary identity to the holed quotient left by cleanup. Take the scalar norm over that full grid. Multiplying (2) over b telescopes the F boundaries. With E0=product_(i<nt)F(q^i) and E1=product_(i<nt)F(q^(i+1)), the EXACT aggregate update is

    E1*F(1)=E0*F(q^(nt)).                           (3)

The identity follows directly from equality of the two full index multisets; it does NOT divide away a possibly nonunit intermediate norm of F. Both endpoint F-values are acquired in soft J. If F(1) is a unit, the coefficient c=F(q^(nt))*F(1)^-1 is actually acquired and E1=c*E0 without any division by E0. Writing E1/E0 as an ordinary quotient would additionally require E0 a unit; no such condition is assumed. On the original native scale nt<=L<=2H+2<4H, so both first-shift endpoint indices are within the bounded original decoder horizon. For a restriction starting at u, u+nt is at most the original horizon endpoint and has the same guard. An actual endpoint nonunit can therefore be localized and decoded through the original scalar source. If both endpoints are units, character phase cancels lawfully, but (3) only says U(E1)=U(E0). It has not initialized either mask.

Indeed every original collision in the shared interior occurs on BOTH sides of the window update. Its absorbing zero cancels from the transport information. Dividing a zero mask would be invalid; deleting the common interior would discard the very witness. The cheap formal point Y=0 is fixed by multiplicative q shifts and is not a start on the unit q orbit. No finite q transport from that known constant to E0 is provided.

This is the previously known adjacent-window boundary phenomenon, now actually reached from the scalar tensor recurrence after the prefix test. It is not credited as a new identity or an acquisition advance. Repeated known boundary updates do not supply a unit starting window within budget; a far shift also needs a new original-leaf ledger if it leaves the bounded horizon.

## 4. Why the two geometric moduli do not repair this block

The attempted cheap operator transport has an initialized Cauchy connection, but its transverse scaling is linear, not multiplicative in the finite quotient. The reviewed geometric-generator identity is

    S_q(fg mod P)=S_q(f)S_q(g)-d_q*S_q(h),
    fg=(fg modP)+P h, d_q=P(qY)modP.

Here d_q is a UNIT because the q-shifted and unshifted outer geometric grids are disjoint. The actual degree-J multiplier produces a rank-at-most-J commutator, not a one-scalar boundary that could be ignored by unit phase. Exact quotient carries are needed, and a nonunit of an auxiliary transport inverse is not automatically an original hit.

Conversely scaling within the ORIGINAL unremoved shared grid has a real one-boundary update, but its scalar norm is exactly the relative window identity (3), with the unacquired initial product. Removing nodes can introduce additional seams; no one-boundary claim is made for that holed grid. The present prefix cleanup does not modify those identities. Thus this tested route does not combine its cheap Cauchy actions and unit-pivot character cancellations into an absolute scalar endpoint.

## 5. Restrictions, bit cost and completed fallback

For every supplied native row subset/seed interval the constructions can be initialized with its ACTUAL degree n, length and index shift. The helper cost is soft(n+t), t=floor(length/n), plus the short tail. It is soft m in the balanced n,t~m trial; it is NOT claimed to be a uniform soft-m oracle for arbitrary tiny row subsets. On any restriction where that helper is unhelpful, use the existing original scalar evaluator directly. Empty/small dimensions have their direct product conventions.

Original bad slices and endpoint leaves retain their original row and index. Proper gcds factor; saturated original bounded leaves use the original beta decoder. Intermediate principal pivots, cofactor matrices and transport inverse failures never receive that decoder merely for being nonunit. Only acquired UNIT slices are removed, and all their actual scalar factors remain available for exact-value reconstruction if needed.

All residue coordinates and indices have O(log N) bits. The trace/Newton determinant for pivot k divides only by integers <=2k (hence <=4K in the next doubled block, and always <=2n<P,Q), q-hook reversal normalizes only by certified scalar units, MPE/division is monic, and endpoint pivot inversions occur only after support cleanup. No collision value is inverted. Every polynomial evaluated at a unit has its ENTIRE coefficients acquired using a proved degree bound; formal truncation is not used as unit evaluation.

The fully defined completion is: execute whichever logarithmic clean blocks are desired within the displayed budget; if they find no original witness, run the existing restriction-stable scalar blocking on the original rectangle. This costs

    soft(J+sqrt(JL)),

including original-leaf localization/recovery. It may reacquire the whole original rectangle rather than assuming a holed outer grid remains geometric. The supporting helper does not alter that exponent.

## Result

The actual new helper is complete logarithmic-prefix pivot-support cleanup and its acquired cofactor/head state, with a subsequent clean block executed at the same balanced soft-m scale. The determinant-only character step legally ignores the resulting UNIT normalization phase, but the tail retains degree Theta(m). The executed q-shift norm update yields only relative boundary transport with no absolute zero-mask initialization. Neither mechanism skips the remaining growing mixed pivots or acquires the original covered endpoint at soft m.

This is a concrete terminal attempt with its real remaining state and costs, not a generic lower bound or a rebranding of the old square observation. A faster whole-family acquisition algorithm remains required.
