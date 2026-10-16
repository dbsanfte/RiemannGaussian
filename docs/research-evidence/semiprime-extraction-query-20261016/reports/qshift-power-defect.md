# The interpolation q-shift has a linearly ranked powered-node defect on the actual source

2026-10-16. Exact actual-source obstruction to one proposed generator conversion. This is NOT a rank theorem for the mixed matrix commutator YS-SY, and is not a general query lower bound. No new asymptotic deletion or generic-to-actual specialization is used.

## 1. The precise proposed conversion

The paid mixed matrix S has diag S=(P_L(z_i;q)) and fast actions. The available block-kernel pencil instead involves the interpolation q-shift. That shift has a rank-one q-commutation defect with multiplication by z. A tempting conversion to the ordinary powered-node commutator uses Y=diag(z_i^B), and treats the resulting power defect as still small. The theorem below shows its rank is actually Omega(m) for a valid balanced dyadic B on the literal source.

Publicly deduplicate equal integer source offsets, retaining multiplicities for the final query. Write J for the resulting distinct-node count; (m-1)/2<=J<=m-1 by the old low-digit two-fiber bound. Let

    H(t)=product_(i=1)^J(t-z_i),
    Z=diag(z_i),  V_(i,s)=z_i^s, 0<=s<J,
    Q=V diag(1,q,...,q^(J-1)) V^(-1).

Thus Q takes the values of a degree<J polynomial at z_i to its values at qz_i. It is a genuine fast interpolation/evaluation operator on the actual unit-difference promise; no closure of the target set under q is required. This assertion concerns degree<J polynomials, not the full degree-L F.

## 2. Exact rank formula

For any field with distinct nonzero z_i, q!=0, and integer 1<=B<=J, put

    r = #{i:H(qz_i)!=0}.

Then

    rank(Q Z^B-q^B Z^B Q)=min(B,r).                (1)

Proof. Let H_j(t)=H(t)/(t-z_j), an exact polynomial quotient. Lagrange interpolation gives Q_(i,j)=H_j(qz_i)/H'(z_j). Therefore, with no numerical division by qz_i-z_j,

 (QZ^B-q^B Z^B Q)_(i,j)
   = -H(qz_i)/H'(z_j) sum_(s=0)^(B-1)(qz_i)^s z_j^(B-1-s).  (2)

Indeed t^B-z_j^B=(t-z_j)sum_s t^s z_j^(B-1-s), so (2) also holds exactly when qz_i=z_j. These apparent collision denominators are never inverted.

Factor the right side into diagonal H(qz_i), the J-by-B Vandermonde at qz_i, the reversed B-by-J Vandermonde at z_j, and the invertible derivative diagonal. The right rectangular Vandermonde is surjective because B<=J. After discarding its zero rows, the left factor has rank min(r,B) because the retained qz_i are distinct. Composition with a surjection preserves that rank. This proves (1). In particular B=1 gives the familiar rank-one q-defect; it does not remain rank one after taking a balanced power.

## 3. Exact actual-source transfer

Use the literal source z_i=gamma^(-N-delta_i), q=gamma^d, d=m^2, with -3d<=delta_i<=d. At both hidden primes the order of gamma exceeds 16d. Distinct deduplicated offsets therefore give unit node differences.

A local equality qz_i=z_j is equivalent to the local order dividing delta_i-delta_j-d. The absolute value of this integer is at most 5d, strictly below that order. Hence

    qz_i=z_j in either hidden field
        iff delta_i-delta_j=d as an integer.      (3)

In particular the same adjacency graph occurs in both fields. Its edges join two distinct offsets in the same residue class modulo m. The old native identity delta_j=N(t_j^2-2t_j) modulo m, with N a unit modulo m, gives at most two original tags per class. Deduplication only decreases this number. Thus each class contributes at most one directed edge satisfying (3), and there are at most floor(J/2) such edges. No class can contain a chain of three offsets. Consequently

    r=#{i:H(qz_i)!=0}>=ceil(J/2)                  (4)

simultaneously in both hidden fields. Nonzero values H(qz_i) are units modulo N, rather than zeros in only one field, by the same integer test (3).

Choose B to be the largest power of two not exceeding J. Then B>J/2 (with B=1 for J=1), and B=Theta(m). Also L/B=Theta(m) for the native long length L=Theta(m^2). Equations (1) and (4) give

    rank(QY-q^B YQ)>=ceil(J/2)=Omega(m),  Y=Z^B,   (5)

in EACH actual hidden field. The choice is dyadic and remains within the balanced paid block-action regime. On the retained prime-order source, dyadic powering preserves node differences as units, as required by the mixed diagonal/Trummer interface.

For the ROW-value convention of the block-pencil report, W=V^T and Q_row=W^(-1)diag(q^s)W=Q^T. Its corresponding defect Q_row Y-q^(-B)Y Q_row is the transpose of -q^(-B)(QY-q^B YQ), so it has exactly the same rank. This explicitly matches the two orientation conventions; neither q factor is substituted silently.

## 4. Exact obstruction and remaining possibility

Any explicit factorization QY-q^B YQ=UV^T over R must have at least ceil(J/2) columns after reduction to either hidden field. Its dense J-by-r generator arrays therefore have quadratic-size output. Thus the proposed step that upgrades the rank-one QZ-qZQ relation to a polylog-rank powered-node compatibility correction fails on the actual source, without an additional counterfamily or counting assumption.

The matrix Q itself still has fast actions, and its powered-node defect does too. A high-rank defect does not imply a high arithmetic cost for every use of that defect. More importantly, multiplication by other matrices or cancellation between terms could give a different low-rank ordinary commutator for S. This report does NOT prove rank(YS-SY)=Omega(m), exclude a different compatible generator, or rule out matrix-free diagonal/norm acquisition. The full query remains open. It identifies exactly why the natural rank-one q-compatibility conversion cannot be used as the missing generator theorem.

## Provenance

The adjacent source-pins.json pins the native offset bounds and low-digit two-fiber machinery, the already paid mixed-matrix interface, and the historical exact local-order premise. The low-fiber, source-span, and long-branch hypotheses are inherited; only the explicit interpolation defect factorization/rank computation is used to transfer them here. No generic polynomial nonvanishing claim, numeric examples, new Lean theorem, repository edit or broad build is involved.
