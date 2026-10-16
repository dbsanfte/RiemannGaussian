# Arbitrary geometric clocks cannot give small-parameter nonvacuous recurrences

2026-10-16. Classical finite-segment statement proposed by root and independently derived here. It extends the four-block first-order graph argument to polynomial-coefficient recurrences in ANY geometric clock, including finite-order clocks with repeated nodes. Initial coefficient singularities may be skipped at a loss of at most D samples. No arbitrary-operation lower bound, full-query acquisition algorithm, or new Lean theorem is claimed.

## 1. Field interface and result

Let K be a field, g,q nonzero elements, and L>=1. Define nonzero A_0,...,A_L by A_0=1 and

 g^k(1−q^(k+1))A_(k+1)=(q^L−q^k)A_k, 0<=k<L.                     (1)

Assume ord(q)>L+r. In the canonical application q=g^(m²), L=2m²+2, and A_k is the Bluestein-chirped finite q-binomial coefficient c_k g^(−binom(k,2)). The stated order condition ensures all numerator/denominator factors in (1) are nonzero.

Suppose an integer m>=1 supplies this short-relation exclusion:

 g^a q^b!=1 whenever (a,b)!=(0,0) and |a|,|b|<=m.                    (2)

This includes the two axes. No order, genericity or independence assumption is made on an arbitrary supplied unit h in K.

Let r>=1,D>=0 satisfy

 r<=m,       2rD<=m,
 (r+1)²(D+1)<=L−r−D+1.                                            (3)

Then no NONVACUOUS recurrence

 sum_(t=0)^r P_t(h^k)A_(k+t)=0, 0<=k<=L−r,                         (4)

can hold, with deg P_t<=D. Here nonvacuous means at least one coefficient FUNCTION k->P_t(h^k) is not identically zero on the entire orbit <h>. Merely asking that a formal P_t be nonzero is insufficient: for finite-order h, a nonzero polynomial can vanish on every orbit point and produce a vacuous zero relation.

All P_t and h may depend arbitrarily on the full input or hidden field. The proof first establishes the regular-leading case P_r(1)!=0 with the weaker sample condition (r+1)²(D+1)<=L−r+1, then removes that regularity requirement by a short shift. Cases with a lower effective maximal shift are included by dropping identically-zero coefficient functions WITHOUT enlarging the original equation range. All sample bounds continue to use the nominal input r. The order-zero effective case is also handled below.

## 2. Clear denominators at an arbitrary initial position

Consider equations starting at j>=0, with leading P_r(1)!=0 after replacing the coefficient polynomials by their shifted versions. Set X=q^k. Iterating (1) gives

 A_(j+k+t)/A_(j+k)
 =g^(−jt−binom(t,2)) (g^k)^(−t)
  *product_(ell=0)^(t−1)(q^L−q^(j+ell)X)
  /product_(ell=1)^t(1−q^(j+ell)X).                                (5)

On k=0,...,L−r−j every denominator is nonzero: j+k+ell<=L. Clearing the common product for ell=1,...,r converts (4) to

 sum_(t=0)^r (g^k)^(−t) B_t(q^k)P_t(h^k)=0,                       (6)

where B_t is a nonzero polynomial of degree at most r, equal to g^(−jt−binom(t,2)) times the first numerator product in (5) and the missing factors with ell=t+1,...,r. Expanding exposes frequencies

 g^(−t) q^u h^v,       0<=t,u<=r, 0<=v<=D.                          (7)

There are at most n=(r+1)²(D+1) such frequencies. If at least n consecutive equations are available, group equal numerical frequencies and apply a square Vandermonde system to the first number-of-groups equations. The coefficient sum of EVERY actual frequency group is zero. Individual expanded coefficients may vanish; that only decreases the number of groups.

This is fieldwise finite Vandermonde algebra. No exponential sum heuristic, distinctness assumption on h-nodes, or finite group-algebra division is being used.

## 3. All actual short alias differences lie on one rational line

An alias between two frequencies in (7) gives

 g^a q^b h^c=1,       |a|,|b|<=r, |c|<=D.                          (8)

A nonzero alias vector cannot have c=0, by (2). Given two alias vectors v_i=(a_i,b_i,c_i), eliminate h by opposite integer powers. This gives

 g^(a_1c_2−a_2c_1) q^(b_1c_2−b_2c_1)=1.

Both displayed exponents have absolute value at most2rD<=m. Thus (2) forces both to vanish. As c_i!=0, the vectors are rationally collinear. No assertion that a primitive direction itself is an actual relation is needed.

If there are no nonzero aliases, (6) already forces every coefficient in every product B_tP_t to vanish, contradicting the nonzero leading polynomial. Otherwise choose ANY nonzero alias vector (a,b,c), reversing signs so c>0. Introduce formal variables G,Q,H and substitute

 G=x^c,       Q=y^c,       H=x^(−a)y^(−b).                         (9)

Every actual numerical frequency group maps to one formal Laurent monomial: each difference is parallel to (a,b,c), so both resulting exponents cancel. Some different actual groups may merge; this is harmless because each of their coefficient sums is already zero. Consequently the formal version of (6) vanishes identically after (9).

This coarsening is valid with torsion and composite orders. It does not identify the numerical frequency group quotient with a torsion-free lattice or invert a zero divisor in a group algebra.

## 4. The highest-shift pole or x-degree separates the leading term

Divide the formal identity by the nonzero common denominator-clearing polynomial. In K(x,y) this yields

 sum_(t=0)^r x^(−ct) R_t(y^c)P_t(x^(−a)y^(−b))=0,                   (10)

where

 R_t(Y)=g^(−jt−binom(t,2))
        *product_(ell=0)^(t−1)(q^L−q^(j+ell)Y)
        /product_(ell=1)^t(1−q^(j+ell)Y).

Here g,q in the coefficients remain the original FIELD CONSTANTS; G,Q in (9) represented the numerical frequency clocks g^k,q^k. Confusing these roles would change the identity.

If a!=0, choose in an algebraic closure a nonzero y_0 with y_0^c=q^(−j−r). Terms t<r are regular at y_0. The term R_r has a genuine pole: its numerator factors could vanish only if q^(L+r−ell)=1 for some0<=ell<r, with L+1<=L+r−ell<=L+r<ord(q). Its other denominator factors are nonzero there. Moreover P_r(x^(−a)y_0^(−b)) is a NONZERO Laurent polynomial in the independent variable x because a!=0 and P_r is nonzero. Thus the top pole cannot cancel with any lower term, contradicting (10). If the characteristic divides c, the pole has higher multiplicity but remains genuine; no separability assumption is needed.

If a=0, the factors R_t(y^c)P_t(y^(−b)) do not involve x, and the powers x^(−ct) are distinct. Each coefficient must vanish. For b!=0, P_r(y^(−b)) is nonzero since P_r is a nonzero polynomial. For b=0 it is P_r(1), nonzero by the regular-leading hypothesis. In either case R_r is nonzero, a contradiction.

This proves the regular-leading theorem at any start j with enough remaining equations, provided ord(q)>L+r and the short-relation box (2) covers the frequencies in question. Formal identities and Laurent valuations avoid all finite-characteristic or torsion pitfalls.

## 5. Remove initial singularities and formal-vacuity cases

Start from a nonvacuous recurrence (4). Choose its largest index r_eff whose coefficient function is not identically zero on <h>, and drop larger identically-zero functions; these terms contribute nothing on any evaluated node. Necessarily r_eff<=r and its polynomial degree<=D. The numerical conditions (3) also bound all frequencies with this smaller effective shift. Dropping terms does NOT supply equations beyond the original k<=L−r range.

There is a j with0<=j<=D and P_(r_eff)(h^j)!=0. If ord(h)>D (including infinite order), the first D+1 nodes are distinct, so a degree-D polynomial cannot vanish on them all unless zero. If ord(h)<=D, the first D+1 nodes cover the entire orbit; the nonzero coefficient-function premise guarantees one nonzero evaluation there. This reasoning uses no algorithm for the order of h.

Replace k by j+k and replace each P_t(Z) by P_t(h^j Z). The leading polynomial is now nonzero at1. The remaining equation count is at least

 L−r−j+1>=L−r−D+1>=(r+1)²(D+1),

so sections2–4 apply when r_eff>=1. They give a contradiction with no additional q-order requirement: the pole numerator exclusion is L+r_eff−ell, independent of the initial shift j.

If r_eff=0, the shifted equation at k=0 is P_0(h^j)A_j=0, contradicting both factors being nonzero. Thus the theorem also excludes a recurrence whose only effective coefficient is order zero, despite its formally higher zero-on-orbit polynomials.

The first D+1 nodes argument also shows why merely patching finitely many initially singular coefficients cannot evade the result under the sample bound. The explicit D-sample loss is retained; it must not be silently omitted.

## 6. Paid actual-source application and quantitative limits

The paid square-alias screen, after the all-semiprime strong-order setup, either factors N or certifies the required box (2) in BOTH hidden fields for g=beta,q=beta^(m²). The axes follow from the certified local g/q orders>16m²; mixed exponents follow by sign reversal from its units beta^(m²s)−beta^t,1<=s<=m,0<|t|<=m. The screen is a classical soft O(m) product/multipoint/gcd composition, not a new generic primitive. Its arithmetic depends only on the strong-order interface, which the latest all-semiprime setup supplies without balance.

With L=2m²+2, ord(q)>16m² gives ord(q)>L+r whenever r<=m. Thus, on the no-factor certified branch, every arbitrary-h nonvacuous recurrence is excluded whenever (3) holds. In particular all fixed or polylogarithmic r,D satisfy the inequalities eventually. Field coefficients and h may be privately advised. No original prime-order counterfamily or new exception deletion is required.

This does not exclude every nearlinear-order recurrence: for example2rD<=m and the frequency count impose explicit parameter limits. It does not treat arbitrary multivariate coefficient clocks, sparse high-degree recurrences, another transformed sequence, selected convolution or scalar norm algorithms. No source collision/controller theorem is automatically transferred to beta, and no whole-query clock is improved. An upper bound for a q-holonomic algorithm is not a lower bound; the result only excludes invoking that specified bounded-parameter recurrence representation on this stream.

The first-order arbitrary-base cancellation graph and earlier fixed g/q-clock obstructions are credited as predecessors. The new step is the three-clock alias-line coarsening, the highest-shift pole with an independent x clock, and the D-sample shift removing initial singularity for every nonvacuous coefficient function. This is a limited repository-level novelty distinction, not a literature-priority claim. Exact prerequisites are pinned in recurrence-source-pins.json. No native source, frozen earlier report, Lean declaration, numerical example or broad build is modified.
