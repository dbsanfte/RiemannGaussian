# Explicit common-character basis and its finite scalar readout

26 October 2026. Parent's constructive normal form independently validated and executed on the actual finite domains. Scratch only; no tests or repository edits. **Positive:** acquired unimodular character normalization and exact shared-coordinate domains. **Not a complete-query gain:** the paid readout below still costs soft k²; a genuinely cheaper collective slice algorithm remains missing.

## 1. Validate the integral normalization

Write G=gcd(j-1,k)², L=H/G. Let B_j have columns (k,0),(a0,1), with a0=[N*j^-2]_k. Acquire their CANONICAL integer labels e1,e2. The exact phase-image theorem says gcd(H,e1,e2)=G, so e1/G,e2/G are integers. For L>1 set

    a=[e1/G]_L, b=[e2/G]_L, d=gcd(a,b).

They are not both zero; gcd(d,L)=1. Choose Bezout u,v with au+bv=d, and put

    C0=[[u,-b/d],[v,a/d]], det C0=1.

Choose r=[d]_L, s=d^-1 mod L, t=(r*s-1)/L. Then

    D=[[s,L],[t,r]], det D=1,
    (a,b)C0=(d,0), (d,0)D=(d*s,d*L)=(1,0) mod L.

Consequently C_j=C0*D is integral unimodular and

    (e1,e2)C_j=(G+H*f,H*c)                         (1)

for acquired integers f,c. The normalized lattice basis is V_j=B_j*C_j. Its generator nodes are beta^G*q^f and q^c. All matrix entries, Bezout coefficients, and exponents have O(log N) bits: C0 and D have polynomially bounded entries in L, and original basis labels have short height. Entire-family acquisition remains soft k. The common beta^G direction itself is inherited phase-index credit; the new concrete refinement is this explicit unimodular basis and its transported finite domains.

For L=1 (j=1,G=H), use C_j=I. Both labels are multiples of H; write the first as G+H*f and the second as H*c. No gcd(0,0), residue inverse modulo1, or artificial unit is needed.

For equal G, the lattice map FROM j TO j' is

    M_(j->j')=B_j'*C_j'*C_j^-1*B_j^-1.             (2)

The reverse product B_j*C_j*C_j'^-1*B_j'^-1 maps j' to j. These rational ambient determinant-one matrices map the supplied source lattice integrally and bijectively to the target lattice, and preserve character modulo H. They need not be ambient SL2(Z) operators. This is a genuine extension of the pointwise ambient shear interface.

## 2. Transport the ACTUAL Gauss-box labels, not only residues

Let U_j be the acquired Gauss basis with columns u,w, and let e_G=(E_u,E_w) be its CANONICAL generator label row. Retain its supplied orientation and exact generator labels. The integer unimodular coordinate matrix (determinant plus or minus1) is

    P_j=V_j^-1*U_j.

Original signed coefficient differences z satisfy |z1|<A,|z2|<B and z!=0. Their common coordinates are n=P_j*z. The exact source label is

    e_G*z = (e_G*P_j^-1)*n
          =G*n1+H*(F_j*n1+C_j^clock*n2).           (3)

Here F_j,C_j^clock are acquired integers, obtained from the ACTUAL e_G*P_j^-1. For an explicit height bound, each weighted reduced basis length is O(k*sqrt N), because ell1>=sqrt(2N) and ell1*ell2<=2kN/sqrt3. Since p0 and N/p0 are both>=8H, the Gauss basis coefficients are O(k²). One may bound C_j entries by O(L²)<=O(k^4), V_j by O(k^5), and integer P_j and P_j^-1 by O(k^6). Thus e_G=O(k²*N) and e_G*P_j^-1=O(k^8*N). All are polynomial in N (N>256k^4), so their coordinates, labels, and exact quotient carries have O(log N) bits. They can differ from f,c in (1): canonical phases chosen independently on B_j and U_j can differ by H-lifts. Ignoring that lift would change the finite physical clock. The lattice-normalization matrix C_j and scalar C_j^clock have distinct meanings.

Thus the exact normalized leaf, up to a monomial unit, is

    q^[h-F_j*n1-C_j^clock*n2]-(beta^G)^n1,
    n in P_j{z:|z1|<A,|z2|<B,z!=0}, h=0,...,4k.  (4)

This is the promised common beta^G direction and common q direction, with an acquired sheared finite parallelogram and linear clock boundaries. The origin line is still OMITTED by n=0, before any specialization. The public source-cell filter and its nonzero exponent labels are transported, not silently replaced by a rectangular completion in n.

## 3. Execute q-direction slicing and exact interval merging

For a fixed attained n1=r, the allowed n2 are an integer interval: intersect the two linear inequalities |(P_j^-1 n)_i|<A_i. At r=0 omit n2=0, splitting into at most two intervals. Empty slices are skipped. For an interval b0<=n2<=b1 the exact clock set in (4) is

    union_(b=b0..b1)[-F_j*r-C_j^clock*b,
                     4k-F_j*r-C_j^clock*b].       (5)

When |C_j^clock|<=4k+1 these intervals overlap or touch, so the UNION is one fully acquired interval, of length 4k+1+|C_j^clock|*(b1-b0). Dropping multiplicities is valid for local-zero predicates. Every merged index has an original b,h source; retain that source map for the nonzero exponent decoder.

When |C_j^clock|>4k+1 the intervals are disjoint. They form a known arithmetic progression of finite blocks; filling the gaps is not justified and may introduce unlicensed zeros. Different cells with the same G,r may likewise be merged only by their ACTUAL clock-set union, not their common envelope. Large F_j or C_j^clock, IF they occur, merely have short BIT size; their magnitude is not a short interval length. No claim that large C is necessary, or that another basis cannot yield better overlaps, is made.

A complete paid algorithm enumerates each cell's O(AB)=O(k) original differences, computes n and the exact interval starts, groups by (G,r), and merges the represented intervals with their source maps. It enumerates only the O(k) ACTUAL supplied points per cell, never scans the possibly huge n1 range or a dense bounding box of the sheared parallelogram. Its total acquisition is soft k² across the cells. The raw clock mass is soft k³, and exact merging cannot increase it. The inherited variable-window/block evaluator therefore costs at most soft(k²+sqrt(k³))=soft k², or one may simply evaluate the old degree-O(k) source polynomial per cell in soft k. Prefix/localization queries keep the same rate. A terminating saturated leaf adds T_ext once; it fits these whole-family bounds.

Thus the common q direction is operationally usable, and the overlap condition (5) is explicit. No theorem bounds the NUMBER of acquired slices/blocks or their union mass at the desired soft-k acquisition scale. No such concentration is inferred from the character normal form.

## 4. Exact-kernel option and what it changes

One may instead Smith-normalize the INTEGER row (e1,e2) to (delta,0), delta=gcd(e1,e2). This makes the second exponent exactly zero, rather than just a multiple of H. But delta/G can be a nontrivial unit only modulo L, not necessarily modulo the hidden beta orders, and the first phase is beta^delta rather than a universally equal beta^G. The finite projected n1 set also changes and can be a sparse support over a huge integer range. This option therefore does not by itself acquire a common small clock or its support. It can be tested when delta=G, but even then the remaining projected support must be initialized; no generic short interval is supplied.

The normal form's exact monomial units do not need numerical acquisition solely for zero predicates. Nor is obtaining a numerical unit-correction product an added necessary bottleneck. The unresolved input is the actual collective slice/clock union or norm value, including its nonliteral-leaf source map.

## Outcome

The parent's construction is valid and supplies a real common-character intertwiner beyond ambient Dehn shears. The exact query is (4), and the tested readout is the slice/interval algorithm (5), completed at soft k². Sharing beta^G and q does not presently reduce acquired support enough to meet soft k. Any new bound on these particular transported slices, or a scalar algorithm avoiding their expansion, would be a substantive continuation. No general lower bound, root-of-unity completion, or full-query gain is claimed.
