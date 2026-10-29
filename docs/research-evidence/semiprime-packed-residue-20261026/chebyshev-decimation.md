# Guarded Chebyshev binary decimation on the actual torus query

26 October 2026. Bounded paper execution; no repository edits or tests. **The negative algebraic branch is genuinely unit-safe, but the two clock parity branches remain. A shared target polynomial can be acquired cheaply at every level; the complete clock still has h positions. No improved full-query bound is obtained.**

## 1. Actual roots, traces and a fully paid root convention

Use the complete raw torus branch and scalar Cayley/trace query of `cone-reciprocity.md`, with its own nonzero-label decoder. Do NOT import singleton or tag promises from the original beta-coupled bank. Use the UNSHIFTED canonical roots x_j=W^r_j and the original symmetric physical clock [-M0,M0], not a shifted target together with a trace clock that would add unintended inverse indices. After the paid i=0 row gates, put m=M0, ell=1 and theta=q0^ell. The trace query has clock Tr(theta*q0^u), 0<=u<m, corresponding exactly to physical indices +/- (ell+u). Its targets are v_j=x_j+x_j^-1 and F(V)=product_j(V-v_j). Trace equality is equivalent to x_j=q0^i OR x_j=q0^-i. Both are original physical indices; the original nonzero-label exclusions therefore apply without an extra literal-zero overcover.

To permit binary target/clock roots to depth s without an unknown-order extraction, start from the already supplied large rough coprime U and PREPOWER W=U^(2^s), choosing 2^s>=h. This preserves norm one and every local order because those orders are odd. Actually rerun the q0 short screen at the changed W and rebuild all row powers and labels in soft K. The original scalar beta is unchanged. The new torus-annihilator transfer applies to this W exactly as before. All 2^s exponents have O(log N) bits. Thus W^(1/2^t)=U^(2^(s-t)) for 0<=t<=s is a SUPPLIED integer power, not a modular square-root oracle.

Let z_j be the acquired square root x_j^(1/2) in the odd subgroup and define

    F_half(V)=product_j(V-(z_j+z_j^-1)), C2(V)=V²-2.

Product trees acquire F_half in soft J. For all finite arguments,

    F(C2(V))=(-1)^J F_half(V)*F_half(-V).        (1)

This follows from C2(Tr z_j)=Tr(z_j²) and ordinary factorization. It is an exact polynomial identity, including repeated roots.

## 2. Discard the negative algebraic branch, with a genuine unit proof

At V=Tr(y), where y and every z_j lie in the same generated odd-order local subgroup, each factor in F_half(-V) is a unit. Indeed Tr(z_j)=-Tr(y) implies

    (z_j+y)*(z_j+y^-1)=0

in the local field, hence z_j=-y or -y^-1, impossible in an odd-order subgroup. The same statement holds at EVERY split coordinate. Norm/gcd certification is legitimate if desired, but evaluating the aggregate unit product is unnecessary for a zero/nonunit equivalence: the proof certifies every factor.

Therefore F(Tr(y²)) is nonunit iff F_half(Tr(y)) is nonunit, componentwise. This is a genuine safe algebraic-branch elimination. It does not authorize rejecting a whole parity class of the geometric clock, since both parity classes below still consist of odd-subgroup elements.

## 3. Execute parity decimation with exact endpoints

For the actual scalar interval write u=2k+a, a=0,1, and put qhalf=q0^(1/2), supplied by §1. Then

    Tr(theta*q0^(2k+a))
       =C2(Tr(theta^(1/2)*qhalf^a*q0^k)).

Both children use the SAME F_half. Their exact lengths are ceil(m/2) and floor(m/2), and starts theta^(1/2) and theta^(1/2)*qhalf. Empty children are omitted. Each child remembers its original physical index ell+2k+a and both inverse orientations. Thus none of the parent's finite endpoints or nonzero labels is silently reset.

After t levels the common target has roots Tr(x_j^(1/2^t)) and degree J. It costs soft J per level, not J*2^t, to acquire it from the paid root list. The clock has at most 2^t children, starts theta^(1/2^t)*q0^(a/2^t), and lengths floor((m-1-a)/2^t)+1 for a<m. Their union is EXACTLY

    {Tr(theta^(1/2^t)*q0^(u/2^t)):0<=u<m}.

Thus this shared-polynomial implementation reacquires a finer clock of the SAME length m=Theta(h), retaining the original offset ell. No clock positions or their unknown useful parity have disappeared. Every child belongs to the admissible odd subgroup; the negative-phase proof in §2 does not certify either clock child unit. At a native hit the useful parity is its normalized u modulo 2 (or 2^t), which is not supplied.

The fully initialized completion can evaluate that same F_t against the fine length-m clock using the inherited shared engine at soft(J+sqrt(Jm))=soft(J+sqrt(Jh)). Alternatively process all child strings independently: the square-root terms add to soft(sqrt(Jh*2^t)), worse. These are costs of the specified algorithms, not a lower bound on an unknown joint contraction. Reading all child starts costs at least their explicit array length in that implementation, but this does not force a J*2^t degree growth because the target really is shared.

## 4. The oriented-root implementation and its different startup cost

For comparison, take any actual oriented interval after its known offset has been absorbed into a row root X_j. Its equation X_j=q0^u, 0<=u<m, permits parity splitting:

    even child root sqrt(X_j),
    odd child root sqrt(X_j/q0),

both tested against q0^k, with exact parity lengths. At depth t its explicit starts are X_j^(1/2^t)*q0^(-a/2^t), 0<=a<2^t, a<m. This implementation emits J*2^t row starts and retains total mass Jm. The negative square-root branch is unit-safe, but both displayed roots lie in the odd subgroup and neither can be dropped without a hit-parity theorem or a computed branch predicate.

The scalar trace implementation of §3 avoids this start expansion by shifting the CLOCK instead. One must not combine the shared degree from that implementation with a single unshifted half-clock from this one: it would silently delete one allowed parity. Also an odd trace clock cannot be shifted into a single oriented row root without tracking both inverse orientations; keeping the coset clocks in §3 handles this exactly.

## Result

The experiment pays root acquisition, target acquisition, unit branches, starts and finite boundaries. It proves an exact negative-branch elimination with no unit-product evaluation and no hidden group order. Its surviving binary clock cosets reassemble into a length-m=Theta(h) clock, so the executed completion retains soft K^(5/4). A useful future bridge would need a genuine joint evaluation of these shared-polynomial cosets or a paid coverage-preserving parity selector. Neither follows from Dickson composition, odd order or the small degree alone.
