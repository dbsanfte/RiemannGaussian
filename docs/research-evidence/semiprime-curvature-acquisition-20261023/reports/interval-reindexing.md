# Exact interval reindexing of the Fermat multiplier query

Date: 2026-10-22. Independent proof check requested by the root agent. No repository edits. This is an algebraic scope result for the frozen Fermat-multiplier packet, not a general lower bound on modular product algorithms.

**Conclusion.** The selected (s,c) labels are a bijective coordinate system for all unit residue classes modulo H=r^2. Once sigma is restricted by T=H sigma-bc lying in an integer interval I, the leaves enumerate precisely the integers T in I with r not dividing T, once each. Their product is a known unit multiple of an ordinary single-base geometric product. For intervals consisting of whole H-blocks, including the sufficient positive interval 1<=T<=2r^3, that unit exponent cancels exactly. Thus the Fermat cover alone adds no sparsity to this interval query. Existing geometric-product routines pay soft-O(r^(3/2))=soft-O(N^(1/4)), not soft-O(r), at this length.

## 1. Inputs inherited from the cover

Let r be an odd prime, H=r^2, r not dividing N. Let a range over the selected quotient layers. For each layer,

    S_a={s mod H : s is a unit and q_r(s)=a}, |S_a|=r-1,
    C_a subset {1,...,r-1}.

The selected quotient witnesses give a partition of F_r and make

    (s,c), s in S_a, c in C_a  ->  s/c mod H

a bijection onto (Z/HZ)^*. In particular sum_a |C_a|=r and there are exactly r(r-1) selected pairs. This is a fact about the explicit witness partition, not just a union-cover estimate.

Set

    b=b_s=center(-N/s mod H),   |b|<= (H-1)/2.

Multiplication by the fixed unit -N sends the preceding bijection to

    (s,c) -> bc mod H = -N/(s/c) mod H.

Therefore the selected bc residues modulo H are bijective onto all r(r-1) unit residue classes. Write e(s,c)=bc as an integer, so

    |e| <= (r-1)(H-1)/2 < r^3/2.

All exponentiations below are defined for signed integers because beta is a unit modulo N.

## 2. The interval bijection, with inverse

Let I=[A,B] intersect Z, A<=B. Define the aligned triple set

    X_I={(s,c,sigma) : (s,c) selected, sigma integer,
                       T=H sigma-b_s c lies in I}.

The map X_I -> {T in I : r does not divide T} given by this formula is bijective.

Proof of injectivity: if two triples give the same T, their e=bc residues agree modulo H because e=-T modulo H. The selected-pair bijection forces the same (s,c). Their sigma values then agree because H sigma=T+e.

Proof of surjectivity: given T in I with r not dividing T, the residue -T is a unit modulo H. Exactly one selected pair has e=-T modulo H. Then

    sigma=(T+e)/H

is an integer, giving the required triple.

The inverse is also explicit and cheap per T. Put u=N/T modulo H; look up the selected quotient witness (a,c) for q_r(u). Then s=c u modulo H lies in S_a, and b=center(-N/s modulo H). This yields bc=-T modulo H and the unique sigma above. Fermat-quotient evaluation and modular inversion take polylogarithmic bit time here. This does not make enumeration of a length-r^3 interval cheap; it only confirms that the coordinates themselves are explicit.

The number of leaves is exactly

    M_I=(B-A+1) - (floor(B/r)-floor((A-1)/r)).

No target multiplicity is discarded.

## 3. Exact modular product and unit exponent

Use the forward-oriented leaf

    L_(s,c,sigma)=beta^(N+bc)-beta^(H sigma).

For T=H sigma-bc,

    L_(s,c,sigma)=beta^(bc) (beta^N-beta^T).

Consequently, as an exact identity in Z/NZ,

    product_(X_I) L_(s,c,sigma)
      = beta^(U_I) product_(T in I, r not dividing T) (beta^N-beta^T),

where

    U_I=sum_(X_I) bc
       =sum_selected_(s,c) bc *
          ( floor((B+bc)/H)-floor((A-1+bc)/H) ).

This formula also holds when b, A, or sigma is negative. The exponent beta^(U_I) is a unit, so the two products have exactly the same gcd with N. Its numerical value need not be acquired for a gcd decision or factor search. Computing U_I by enumerating the selected pairs would cost soft-O(r^2); no soft-O(r) acquisition for arbitrary endpoints is asserted here.

If using the opposite leaf q^sigma-theta*x_b^c from the query statement, multiply the displayed expression by (-1)^M_I. This is also a unit.

## 4. Unit-exponent cancellation on whole H-blocks

For odd r, q_r(-1)=0. Hence every quotient fiber S_a is closed under s -> -s modulo H. The centered representative satisfies

    b_(-s)=-b_s.

Since H is odd and b_s is a unit, this involution has no fixed point. Therefore

    sum_(s in S_a) b_s=0,
    sum_selected_(s,c) bc
       =sum_a (sum_(s in S_a) b_s)(sum_(c in C_a) c)=0.

In any integer interval of length K H, each residue class modulo H occurs exactly K times. Each selected pair consequently occurs with K sigma values, and U_I=K sum_selected bc=0. The forward product equals the ordinary geometric product exactly.

In particular:

* I=[1,2r^3] has length 2r H, so U_I=0 and M_I=2r^3-2r^2.
* I=[-2r^3,2r^3] has one extra endpoint relative to a whole-block interval, but the extra endpoint is a multiple of r and is excluded. Each unit residue still occurs exactly 4r times, so U_I=0 and M_I=4r^3-4r^2.
* For a common sigma set of size L, U=L sum_selected bc=0, regardless of whether the reindexed T set is an interval.

The opposite-leaf sign is harmless. In the two specific intervals above M_I is even, so it also equals +1.

## 5. Relation to the original common sigma cap

For every selected pair, |bc|<r^3/2. If |T|<=2r^3, then

    |sigma|=|T+bc|/H < 2.5r < 3r.

Thus all triples for I=[-2r^3,2r^3] occur inside the original common cap |sigma|<=3r. The sufficient positive interval I=[1,2r^3] also lies inside it.

Conversely, every triple in that cap has

    |T|=|H sigma-bc|<3.5r^3.

The full cap is therefore a residue-dependent-endpoint subset of this longer interval that contains the entire central interval with multiples of r removed. It is not claimed to be exactly one interval. Its cardinality is exactly

    r(r-1)(6r+1),

because reduction modulo H first determines the selected pair and then T determines sigma. Its total forward-leaf unit exponent is zero by Section 4.

The length-r^3 central portion already shows the absence of query sparsity from the cover alone. This is not a proof that every possible ring algorithm must spend at least its square root.

## 6. Local witnesses and global recovery

Suppose N=PQ, beta is a unit modulo N, and Q<=2r^3. As r does not divide N, r does not divide Q. Fermat's theorem gives

    beta^N = beta^(PQ) = beta^Q modulo P,

because N-Q=(P-1)Q. Thus T=Q is a guaranteed nonunit leaf in the positive aligned interval. This argument uses no Fermat-quotient catalog: the catalog coordinates simply name that T once.

A true local witness from the original row identity indeed has H sigma=Q+bc, so its interval label is T=Q. A global collision has a different interpretation. Under the inherited strong setup

    D=ord_N(beta)>256r^4, D | phi(N),

a global leaf beta^N=beta^T implies

    D | (N-T)-phi(N) = P+Q-1-T.

For P,Q<=2r^3 and |T|<3.5r^3, the absolute value on the right is <7.5r^3+1<D for r>=3. It is therefore zero, giving

    P+Q=T+1.

The integer quadratic X^2-(T+1)X+N yields the factors. This is precisely the inherited bounded-global-order decoder in different coordinates, not a new recovery theorem. It applies even to T divisible by r, which is useful in safely removing excluded multiples below.

## 7. Paid ordinary-GP consumer and bit cost

Let ell=B-A+1=O(r^3), with endpoints O(r^3). The full interval product

    A_I=product_(T=A..B)(beta^N-beta^T)

is a unit multiple of the evaluation at alpha=beta^(N-A) of a polynomial whose roots are 1,beta,...,beta^(ell-1). Pollard's geometric-product baby/giant splitting computes it in soft-O(sqrt ell) ring operations, using product/remainder trees; the only necessary base inversions are powers of the known unit beta. This is Section 3.2 of Bernstein--De Feo--Leroux--Smith, *Faster computation of isogenies of large prime degree*. [Primary preprint, pp.3-5](https://arxiv.org/pdf/2003.10118).

Over Z/NZ a degree-d polynomial multiplication/remainder costs soft-O(d log N) bit operations. Therefore the resulting modular GP evaluation costs soft-O(sqrt ell log N), plus polylogarithmic powering. At ell=Theta(r^3) this is soft-O(r^(3/2)), or soft-O(N^(1/4)) when N~r^6.

To omit T divisible by r, first handle

    B_I=product_(k: rk in I)(beta^N-beta^(rk)),

a GP with ratio beta^r and O(ell/r+1) terms. Its cost is soft-O(sqrt(ell/r+1)) ring operations, at most soft-O(r) in the relevant regime. If gcd(B_I,N)=1, invert B_I modulo N and recover the product over r not dividing T as A_I/B_I. If its gcd is nontrivial, localize B_I to a leaf: a proper leaf gcd factors N; a global leaf uses the same bounded decoder of Section 6. Thus this procedure is a rigorous factor-or-product consumer and never divides by an unchecked nonunit.

Saturation localization of a GP interval uses interval halves. At each level only a positive-gcd branch needs continued search. Recomputing square-root products along one branch has total square-root work bounded by a geometric series; even a conservative logarithmic overhead remains hidden by soft-O. No pairwise-unit-difference promise for target points is used.

This consumer is not a new quarter-rate factoring result. The frozen packet already pays an unconditional positive-integer quarter-rate product. The purpose here is to identify the present collision query exactly and account for its parameters.

## 8. Restriction ledger

An interval split in T gives another aligned query and another single-GP product with the same proof. This is sufficient for the paid GP consumer's factor localization. The endpoint may be carried as O(log r) bits, without enumerating selected pairs.

An arbitrary restriction to rows b, labels c, or original sigma boxes maps instead to a filtered subset of T. Membership is explicit via the inverse map in Section 2, but the resulting T set need not be an interval or a fixed small union of intervals. No cheap arbitrary-filter GP product is claimed.

Conversely an algorithm that handles only axis-aligned boxes in (b,c,sigma) does not automatically handle the condition H sigma-bc in I. The identity establishes a sufficient aligned subquery and its exact scope; it does not silently grant a proposed oracle stronger restriction support.

Any eventual soft-O(r) modular acceleration of this ordinary long-GP factor query would still be a substantive result and is not ruled out here. The precise conclusion is that the Fermat multiplier cover, its witness partition, and the linear row identity alone merely relabel the whole candidate interval rather than acquire a sparse query.


## 9. Finite algebra checks

An independent inline Python check constructed the greedy quotient cover and all actual quotient fibers for r=3,5,7,11,13. For beta=2 modulo the composite 1009*1013 it verified the selected-pair bijection, signed-endpoint interval bijection, exact modular product with the displayed unit exponent, zero exponent on both whole-block examples, and the positive-interval cap bound. These are algebra sanity checks only. They do not test the asymptotic acquisition cost, the inherited large-order setup, or any new native factor-coverage theorem.
