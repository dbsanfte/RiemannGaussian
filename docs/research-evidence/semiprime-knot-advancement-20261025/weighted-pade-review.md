# Independent review: weighted descendant Padé and exceptional pole chains

2026-10-25. **PASS for the scoped classification below.** The normalized figure-eight q-factorial weighting changes the rational-solution problem: its exceptional solution at Z=2 must be retained. Nevertheless the actual native axis nodes exclude that exceptional value, so the same small-degree Padé strategy cannot initialize the full native quotient. This does not exclude other representations or a residual-only algorithm.

## 1. Operator and formal coefficients

Over a field K, let q have order r>2, or infinite order, and put

    L=(1-z)+(Z*q*z-2)T+(1-q²*z)T²,     (TA)(z)=A(qz).

For a scalar t replacing Z, a normalized series Psi(z)=sum H_n z^n satisfying L Psi=0 has coefficient recurrence

    (1-q^n)² H_n=(1-t*q^n+q^(2n))*H_(n-1),    H_0=1.       (1)

This determines H_n uniquely while 1<=n<r, or for every n when r is infinite. In the finite-order setting only that nonsingular initial range is used here. The truncated series Psi_M=sum_(n=0..M-1) H_n z^n, for M<r, has exact residual

    L Psi_M=-(1-q^M)² H_M z^M.                            (2)

The numerator factors in (1) vanish exactly at t=q^n+q^-n. Their product through n=d differs from C_d(t) by a known unit. Hence termination is equivalent to C_d(t)=0.

## 2. Exact small-denominator rational classification

**Derived proposition.** Suppose A(z) in K(z), regular at zero, satisfies L A=0. In finite order assume its reduced denominator degree b<r/2. In infinite order assume simply that A is rational. Then every finite pole of A, if one exists, is a simple pole at z=1.

Proof: extend K algebraically. Zero is not a pole by assumption. Consider any nonzero pole orbit under multiplication by q. In finite order each orbit has length r. Since the denominator degree is less than r/2, its pole support has fewer than half the orbit positions, hence there exist two consecutive missing positions. Cut the cyclic orbit through such a gap, yielding a linearly ordered segment containing all poles and with at least two empty positions separating its endpoints. In infinite order use the ordinary finite minimum/maximum pole support, with no cut needed.

For an orbit not containing 1, let alpha*q^m be its first pole and alpha*q^n its last, using the cut ordering. At z=alpha*q^(m-2), only T²A can have a pole; its coefficient 1-q²z equals 1-alpha*q^m, which is nonzero. This is impossible. Thus poles lie only on the orbit containing 1.

On that exceptional orbit, the same first-pole test forces q^m=1. Moreover its pole must be simple, since 1-q²z has only a simple zero and no other term has a pole there. At the last pole z=q^n only A(z) can have a pole, forcing q^n=1, again simple. Both first and last indices therefore represent the unique position 0 modulo r. They belong to a segment of length less than r (the cut omitted at least two holes), so they coincide. The only possible pole is z=1, simple. This explicitly handles cyclic wrap rather than assuming an infinite-order argument applies unchanged.

Consequently A=P+c/(1-z), with P polynomial. Direct calculation gives

    L(c/(1-z))=c*q*z*(t-2)/(1-q*z).                       (3)

Since L(P) is polynomial, t!=2 forces c=0. Thus at every scalar t!=2, all such rational solutions are polynomial. For a nonzero polynomial of degree d, the coefficient of z^(d+1) is

    -(1-t*q^(d+1)+q^(2d+2))*leading_coefficient(P).

Therefore t=q^(d+1)+q^(-d-1), and in particular C_(d+1)(t)=0. If d+1<r, the lower recurrence also identifies the normalized terminating series uniquely.

At t=2, the solution 1/(1-z) is exact. If additionally deg P<r-1 in finite order, no nonzero polynomial P can solve L P=0: the displayed top coefficient becomes -(1-q^(d+1))², nonzero in that range. In infinite order the same holds at every degree. Hence normalized A(0)=1 then gives A=1/(1-z). Larger-degree polynomial solutions in finite order are not excluded; the bound is essential.

## 3. Finite Padé residual criterion

Let A=P/Q with Q(0)=1, deg P<=a, deg Q<=b, approximate the nonsingular normalized solution through O(z^M), with M<r in finite order. Use denominator

    W=Q(z)Q(qz)Q(q²z).

The numerator of L A over W is

    (1-z)P(z)Q(qz)Q(q²z)
    +(t*q*z-2)P(qz)Q(z)Q(q²z)
    +(1-q²*z)P(q²z)Q(z)Q(qz).

Its degree is at most a+2b+1. Since the approximation implies L A=O(z^M), and W(0)=1, **M>a+2b+1 forces L A=0 identically**. The earlier bound max(a+2b+1,3b) is also safe, though the 3b term is unnecessary for this homogeneous weighted equation.

Assume b<r/2, t!=2 and C_(a+1)(t)!=0. The exact classification forces A polynomial after cancellation, of degree d<=a; its top coefficient forces C_(d+1)(t)=0, hence C_(a+1)(t)=0. This contradiction rules out the proposed Padé approximant. Infinite-order q has the same conclusion without the finite-order denominator restriction.

## 4. Actual-family implication

The independently reviewed native axes provide x_s=beta^(ks), z_s=x_s+x_s^-1 for at least k-2 retained s in [1,k-1]. At either local prime, ell=ord(beta^k)>=ord(q)>16k². Thus x_s!=1, and

    z_s-2=(x_s-1)²/x_s !=0

in that field. All these axis components avoid the exceptional t=2 solution.

For d=a+1, at most

    2*floor((k*d+k-1)/ell) < (d+1)/(8k)

of the retained axis trace nodes satisfy C_d(z_s)=0. With a,b=soft O(J), J=soft O(k), M=Theta(k^(3/2)), all sufficiently large native instances satisfy M>a+2b+1, M<r, b<r/2, and have many retained axis nodes with C_(a+1)!=0. Therefore a quotient-wide weighted rational Padé approximation of these degrees cannot exist on the full acquired G. This is an actual-family statement for the specified full-quotient rational approximation ansatz; no generic-component assumption remains.

The conclusion is unchanged if Q has cancellable factors, since reduction only decreases its degree. Q(0)=1 guarantees formal expansion at zero, and specialization to a local axis component preserves that condition. No inversion of unknown prime-field quantities is performed by this proof.

## 5. Scope and algorithmic relevance

This tests whether q-factorial normalization followed by a short rational Padé initializer avoids the earlier raw-Green obstruction. It does not: exceptional coefficient zeros do permit the simple pole at 1, but only at t=2, which the retained native axes avoid. Thus this particular route needs larger-degree rational data or a different compact state.

The proof does not exclude a Pfaff/Heine transformation that changes the requested output or parameters in a way not represented by this operator/Padé ansatz, an algebraic or nonrational generator, or a direct residual-only algorithm. It does not establish an algorithmic lower bound, factorization exponent improvement, or inexpensive label recovery. A positive method must still provide restricted-window calls or labels and handle local inverse signs with the existing consumer.
