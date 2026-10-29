# Acquired sparse Alexander realization of the complete native trace family

25 October 2026. Positive representation result; no fast partial-orbit norm theorem is claimed.

## 1. Input normalization and two valid integer lifts

Work over R=Z/NZ with the acquired native rows x_j, j=1,...,J. The paid tests have made x_j and x_j-1 units, or already returned a factor. Set

    z_j=x_j+x_j^-1, G(Z)=prod_j(Z-z_j),
    S(T)=T^J G(T+T^-1)=prod_j(T²-z_j T+1),
    S(1)=G(2)=prod_j(2-z_j).

Since 2-z_j=-(x_j-1)²/x_j, S(1) is a unit. Therefore

    Delta_R(T)=T^-J S(T)/S(1)=G(T+T^-1)/G(2)

is a well-defined reciprocal Laurent polynomial with Delta_R(1)=1. This uses every retained original row; it does not require that the uncentered catalogue be closed under inversion or select special semiprimes.

The direct symmetric lift suggested in the task is valid. Lift paired coefficients c_r=c_-r for r>=1 to representatives of magnitude<N. Put c_0=1-2*sum_(r>=1)c_r. Its residue is the required central coefficient because Delta_R(1)=1. Then Delta_lift(T)=c_0+sum_(r>=1)c_r(T^r+T^-r) is integral, symmetric, equals1 at1, reduces to Delta_R, and has coefficient magnitude O(JN), hence O(log N+log J)=O(log N) bits in this regime.

For the **sparse small-entry Seifert realization**, a different equally legitimate lift is preferable. Let

    w=T+T^-1-2=(1-T)²/T,
    f_R(w)=G(w+2)/G(2)=1+sum_(i=1)^J f_i w^i.

Lift f_i individually to integers of magnitude<N and keep f_0=1 exactly. Define f_Z and Delta_Z(T)=f_Z(T+T^-1-2). Then Delta_Z is an actual integer Alexander polynomial normalized at1 and reduces to Delta_R. Its expanded Laurent coefficients can have O(J+log N) bits; **they need not be expanded**. The Seifert entries below are the small f_i, so this coefficient growth is not charged as nonexistent output. Delta_Z need not equal the preceding direct Laurent lift as an integer polynomial; their reductions modulo N coincide.

## 2. Explicit sparse, constant-bandwidth Seifert matrix

Let n=J, let Q be the n-by-n upper shift, Q_(i,i+1)=1, and put

    E=diag(f_1,-f_2,f_3,...,(-1)^(n-1) f_n),
    F=e_1 e_1^T,
    V=[[E,Q],[Q^T-I,F]].

This is an explicitly acquired integer 2n-by-2n matrix with at most

    n+(n-1)+(2n-1)+1 = 4n-1

nonzero entries. Each entry is 0, +/-1, or a signed lift of f_i and has O(log N) bits. Its skew part is exactly

    V-V^T=[[0,I],[-I,0]].

Interleave the basis as (e_1,f_1,e_2,f_2,...,e_n,f_n). The only off-diagonal nonzeros are

    V_(f_i,e_i)=-1,
    V_(e_i,f_(i+1))=V_(f_(i+1),e_i)=1.

Thus the interleaved V has bandwidth3. This is an actual O(J)-entry matrix, not a dense matrix with an uncharged O(J²) expansion or merely a black-box determinant.

### Exact determinant proof over the Laurent ring

Use an indeterminate T and the integer Laurent ring Z[T,T^-1]. Put

    A=(1-T)E,
    B=T I+(1-T)Q,
    C=(1-T)Q^T-I.

First replace F by0. The determinant of [[A,B],[C,0]] is T^n: swap the two n-column blocks and use det(B)=T^n, det(C)=(-1)^n. B,C are invertible in this Laurent ring because Q^n=0, with explicit finite inverses

    B^-1=T^-1 sum_(r=0)^(n-1) [-(1-T)/T]^r Q^r,
    C^-1=-sum_(r=0)^(n-1) (1-T)^r (Q^T)^r.

Restoring the lower-right block (1-T)e_1e_1^T is a rank-one update. The determinant lemma gives

    T^-n det(V-T V^T)
      =1-(1-T)² e_1^T B^-1 E C^-1 e_1
      =1+sum_(i=1)^n f_i [(1-T)²/T]^i
      =Delta_Z(T).

All signs follow from E_ii=(-1)^(i-1)f_i. This is a formal polynomial identity; it does not divide by 1-T or by an unknown coefficient. Specialization to any unit T, including T=q^i, is valid over the composite ring.

Independent exact arithmetic check: evaluated the determinant identity for n=1,...,7, ten random signed integer coefficient lists at each n, and T=2,3,-1,-2 (280 determinant comparisons using exact rational Gaussian elimination). All passed. These checks guard the displayed signs; the formal proof supplies uniform coverage.

## 3. Primary constructive realization source

H. Seifert, *Über das Geschlecht von Knoten*, Math. Ann.110,571–592, original scan https://webhomes.maths.ed.ac.uk/~v1ranick/papers/seifert.pdf ; digitization https://digizeitschriften.de/download/pdf/235181684_0110/log34.pdf . The volume is commonly cited1934; digitization metadata also gives1935. The relevant primary pages were inspected as images.

Pages586–587 construct surfaces by assigning band crossing/linking and self-twist numbers. Satz5, p.587, states the converse realization for integer matrices satisfying the prescribed intersection conditions. The proof of Satz6, pp.588–589, itself makes only a linear-size set of crossing parameters nonzero and derives a sparse determinant recurrence (27). It then realizes every integral reciprocal polynomial with value +/-1 at1.

Applying this matrix-realization theorem to the displayed V produces a genuine knot with Seifert matrix V and normalized Alexander polynomial Delta_Z. The determinant calculation above is our explicit modern block-matrix form; it is not claimed as a new topological realization theorem.

The acquired object is the sparse Seifert matrix, together with the classical disk-with-bands realization instructions. Its encoding is O(J log N) bits, or O(J(log N+log J)) if row/column indices are written explicitly. No geometric diagram is needed for the finite-ring determinant identity or partial torsion interpretation.

An expanded knot projection has a different cost. A twist parameter of magnitude A can require Theta(A) crossings in the standard band construction. Even though its binary encoding has O(log A) bits, expanding all integer twists can cost Omega(sum_i |f_i|), as large as O(JN) for this representative choice, plus routing crossings. No O(J)-crossing ordinary knot diagram is claimed. Likewise a generic dense-matrix realization routine must not be charged as linear without using the sparse instruction list.

## 4. Acquisition is soft-O(J), including coefficients

Acquire G with its ordinary product tree in soft-O(J) ring operations. Invert G(2) after the paid unit check. To acquire f_R=G(w+2)/G(2), use a division-free balanced Taylor-shift recursion:

    G(Z)=G_0(Z)+Z^m G_1(Z),
    G(w+2)=G_0(w+2)+(w+2)^m G_1(w+2).

Pad to a power of two, choose balanced m, and precompute (w+2)^(2^r) by repeated squaring. Then the recursion satisfies T(n)=2T(n/2)+O(M(n)); including all levels costs soft-O(J) ring operations with fast polynomial multiplication. It requires no factorial inverses or characteristic assumption. Each ring operation has soft-O(log N) bit cost. Lifting the J output coefficients and writing the 4J-1 entries costs soft-O(J log N) bits. The matrix representation is therefore genuinely acquired inside the soft-k budget.

If the direct symmetric lift is used instead, conversion to integer Conway coefficients can grow exponentially in J, so its sparse matrix need not have O(log N)-bit entries. This is why the alternative lift in Section1 matters. Both lifts describe the same modular polynomial, which is all the native prefix-norm computation uses.

## 5. Unknotting-one alternative and what the skein move computes

Primary: H. Kondo, *Knots of unknotting number1 and their Alexander polynomials*, Osaka J. Math.16(1979),551–559, https://ir.library.osaka-u.ac.jp/repo/ouka/all/6492/ojm16_02_19.pdf , Theorem3 and equation(8), pp.558–559.

Kondo constructs a knot normal form using only the linking parameters lambda_(1j)=lambda_(j1), all others zero. For the symmetric degree2n polynomial with paired coefficients a_i, the parameters alpha_i are obtained from second differences. In particular alpha_0=a_0, the interior recurrence is alpha_i=a_i-alpha_(i-2)+2alpha_(i-1), and the final step adds n-1. The star parameters are lambda_11=alpha_(n-1),...,lambda_1n=alpha_0. This realizes the prescribed polynomial with unknotting number1.

Our cost deduction: from the direct Laurent lift with max|a_i|=O(JN), cumulative second differences give |alpha_i|=O(J³N+J), still O(log N)-bit integers. There are only O(J) star parameters and their computation takes O(J) integer additions. This is a second, weighted-band realization of the entire family; it is not a claim that Kondo's ordinary projection has O(J) crossings or that its Seifert matrix was explicitly written in that paper.

The block construction gives an even more direct algebraic version of a single crossing-change phenomenon: setting the one entry F_11 from1 to0 changes the normalized Alexander polynomial to1. Thus the whole nontrivial determinant is a rank-one update of a unit-determinant presentation. This is an algebraic unknotting-one representation; by itself it does not prove that our particular geometric realization becomes the unknot under that move. Kondo independently supplies the genuine unknotting-one knot realization.

## 6. Rank-one update does not yet compute the partial torsion product

At a chosen t=q^i, the update formula computes

    Delta_R(t)=1+w_i R(w_i),
    w_i=q^i+q^-i-2,
    R(w)=(f_R(w)-1)/w.

One value can be acquired in O(J) ring operations by Horner/triangular elimination. For many i, the input coefficient list is shared and fast multipoint evaluation can help only after the points are acquired. The binary-powered q-clock gives any single w_i cheaply; it does not acquire the entire interval's norm cheaply.

For the product over i=1,...,m, the evident determinant presentation is a block sum of m copies of the base matrix evaluated at different q^i, with m independent rank-one updates. The determinant lemma now gives an m-by-m diagonal correction matrix with diagonal entries Delta_R(q^i). Its rank is m in general, not1. Eliminating the star or using the unknotting skein relation therefore returns

    prod_(i=1)^m [1+w_i R(w_i)],

which is exactly the remaining partial-orbit norm. No cancellation across different i follows from the one-crossing relation. Treating its m updates as one shared rank-one update would be incorrect. This is not an impossibility theorem against a new cross-index identity.

## 7. Exact native norm and torsion boundary

With u_i=q^i+q^-i and H_m(Z)=prod_(i=1)^m (Z-u_i)/(2-u_i), direct rearrangement gives the task's normalization:

    R_m=prod_j H_m(z_j)
       = q^(J*m*(m+1)/2) * S(1)^m
          * prod_(i=1)^m Delta_R(q^i) / (q;q)_m^(2J),
    (q;q)_m=prod_(i=1)^m(1-q^i).

Here S(q^i)=q^(Ji)S(1)Delta_R(q^i). The bound m<ord_P(q),ord_Q(q) makes every 1-q^i and therefore (q;q)_m a unit. S(1) and q are already units. Consequently nonunit/zero detection for the scalar partial torsion product is exactly equivalent to that for R_m; these normalizations do not hide a collision denominator.

The root's prefix consumer can therefore ask only for prod_(i=1)^m Delta_R(q^i), or its zero/nonunit decision, at chosen prefixes. It does not need the full degree-m H_m polynomial. The sparse knot realization preserves that reduction, but is not yet an algorithm for the prefix oracle.

For comparison, Hillar–Levine, *Polynomial recurrences and cyclic resultants*, https://arxiv.org/abs/math/0411414 and author PDF https://lionellevine.github.io/hillarlevineAMSrevised.pdf , studies Res(f,T^m-1), with roots raised to the m-th power and known full root-of-unity cycles. Its short polynomial recurrences do not identify the partial geometric product above with a cyclic resultant. A complete-cycle torsion formula and a partial orbit of an unknown-order unit have different supplied boundary data. No cyclic-order specialization is made here.

## Conclusion

The whole native family has an acquired, genuine Alexander realization with a 2J-by-2J Seifert matrix of bandwidth3, at most4J-1 nonzeros, and O(log N)-bit entries, obtained in soft-k bit complexity. This is a positive representation result with all coefficients paid. It gives an exact knot/torsion interpretation of the scalar prefix norm. The remaining unresolved operation is its partial geometric-orbit product; neither sparse representation, a single rank-one update, nor unknotting number1 alone supplies that product in soft-k time.
