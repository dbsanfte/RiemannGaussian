# Paid coherent root preparation by an initial power-of-two rebase

22 October2026. Verdict: PASS. The all-input prepared-base pipeline may publicly rebase gamma0 to gamma=gamma0^(2^D) before constructing the native targets. This pays coherent2^d roots of every ORIGINAL native input through d<=D, without extracting roots at an unknown order. It does not pay the exponentially branching recursive target family or supply a common-H evaluator.

## Input and rebase

Suppose the paid preparation either already factors N or supplies a PUBLIC unit gamma0 with the required odd local orders R_P,R_Q, including their coprimality and retained lower bounds. Where required, q0=gamma0^(m²) has the original promised local orders as well. Let

    D=ceil(log_2(8m)), c=2^D, gamma=gamma0^c.

Since R_P,R_Q are odd, gcd(c,R_P)=gcd(c,R_Q)=1. Therefore

    ord_P(gamma)=R_P, ord_Q(gamma)=R_Q,
    ord_N(gamma)=lcm(R_P,R_Q)=ord_N(gamma0).

No order is supplied to or computed by the algorithm. The equality is a proof using the retained odd-order contract. Coprimality, any prime-order property, lower bounds and global-order bounds are all unchanged.

The redefined scalar step is q=gamma^(m²)=q0^c. Local orders of q are unchanged from q0 for the same reason, because those orders divide the odd R_P,R_Q. Thus all original q-order and unit-difference screens remain valid. The cost is D repeated modular squarings, soft O(logm) native operations. c lies in[8m,16m), so its bit length is O(logm).

## Explicit coherent roots of the actual native inputs

Write A_j=E_j−m²kappa_j, so the rebased native target is y_j=gamma^A_j. For0<=d<=D define PUBLIC units

    y_(j,d)=gamma0^(2^(D−d) A_j),
    Q_d=gamma0^(2^(D−d) m³),
    q_d=gamma0^(2^(D−d) m²).

Then y_(j,0)=y_j, Q_0=q^m, q_0=q, and

    y_(j,d+1)²=y_(j,d),
    Q_(d+1)²=Q_d, q_(d+1)²=q_d.

Every prescribed2^d power returns the rebased input exactly modulo N. These are coherent choices globally, not independent square-root selections in hidden fields. Since gamma0 has odd local orders, all these choices belong to the prepared odd subgroups. They do not require choosing among hidden local signs or knowing their orders.

All A_j have O(log N) bits in the retained polynomial-size native regime. Multiplication by2^(D−d)=O(m) adds only O(logm) bits, so every displayed exponent remains O(log N) bits. The same holds for m²,m³. At a chosen level the J roots are acquired by J public modular exponentiations, soft O(J); the common q,Q roots add logarithmic work. Even acquiring ALL D+1 native-input levels costs soft O(J logm)=soft O(m) for J=soft O(m), with logarithmic modular bit costs included. Storage may keep one level or all levels with the same soft bound. Signed A_j, if permitted by a more general contract, use the supplied unit inverse; the retained positive-ledger setting in fact has A_j>0.

## Original Fermat coverage and scalar recovery are preserved

The native integer row identity and its local Fermat collision hold for ANY base satisfying the period/odd-order preparation hypotheses; they do not prescribe a particular numerical value of gamma. Replacing the prepared base by a public power coprime to all its local orders preserves every local period statement. Consequently the own-tag coverage proof and the quadratic index mask still apply to the targets constructed from the rebased gamma. The integer exponents E_j, m²i and their nonzero gaps are unaffected.

A proper leaf gcd is a factor as before. A saturated leaf gives gamma^K=1 with the SAME public nonzero integer K=E_j−m²i. It can be consumed by the inherited decoder instantiated at gamma, whose unit/order contract is unchanged. If an interface insists on gamma0, local oddness proves the stronger equivalence

    gamma^K=1 mod P iff gamma0^K=1 mod P,

and likewise at Q: R_P divides cK iff R_P divides K. Thus the same K is also a global gamma0 annihilator, with no increased bit length. Merely multiplying K by c would also be valid but is unnecessary. A nonunit local collision support is preserved under this equivalence, so no useful factor is lost by rebasing.

There is no fixed-base restriction in the stated all-input pipeline that forbids this initial choice. The prepared base is acquired for its order contract, and native rows/consumer accept arbitrary bases with that contract. This does NOT assert that every exploratory theorem with a literally fixed numerical base, or every density statement about a separately chosen gamma, can silently be changed; those contracts must be checked individually. The present all-input source/recovery interface permits the rebase explicitly.

## Exact limit of the repair

This repairs the statement that coherent roots of the ORIGINAL native targets and q^m must remain unpaid. They can be publicly prepared in advance at the cost above. In particular a recursion using those chains for only polynomially/logarithmically many operations should not be rejected for lack of an unknown-order square-root oracle.

It does not acquire all newly generated recursive arguments. A depth-d branching construction may ask for J*2^d DISTINCT shifted or twisted targets, not merely the J values y_(j,d). Giving a short expression for every descendant is not evaluation of every descendant, and their explicit output size can already exceed soft m. Their multiplicative correction products, character masks, or subtree values still need an actually batched algorithm. No terminal base case or reduction of the common-H degree is established by this preparation alone.

Only this allocated scratch report was written. No archived report, repository file, backend, subagent or finite example was changed. All assertions are direct cyclic-order and modular-exponent arithmetic under the previously retained preparation/row/decoder contracts.
