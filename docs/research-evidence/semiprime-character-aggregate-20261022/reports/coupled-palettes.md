# Coupled quadratic palettes: a paid finite Casoratian coefficient

22 October 2026. Focused symbolic investigation, preserving the prepared scalar q=gamma^(m^2). No implementation, examples, Lean changes, or repository edits. Read the current two-common-product and native antipodal/lifted-root reports and the paid coefficient-block/mixed-diagonal journal entry at 30250--30410.

Write Q=q^m, R_e={0} union the nonzero residues of Legendre sign e modulo m, d0=(m+1)/2, D=K*d0, and

    H_e(X)=prod_(r in R_e,n<K)(X-q^r Q^n),
    B_(e,n)(X)=prod_(r in R_e)(X-q^r Q^n).

The four endpoint block polynomials B_(e,-1), B_(e,K-1), for e=+,-, have O(m) total degree. Their coefficients and all values at the O(m) native normalized nodes are genuinely acquired in soft O(m), via product trees and monic MPE. This construction uses original q scalars, not cyclotomic mask roots.

## Exact coupled q-difference identity

The finite products give the fraction-free first-order equations

    B_(e,K-1)(X) H_e(QX)
      =Q^D B_(e,-1)(X) H_e(X).                 (1)

Define the finite Casoratian

    W(X)=H_+(QX)H_-(X)-H_-(QX)H_+(X),
    Z(X)=H_+(X)H_-(X),
    A(X)=B_(+,-1)(X)B_(-,K-1)(X)
         -B_(-,-1)(X)B_(+,K-1)(X).

Then exactly, WITHOUT any division,

    B_(+,K-1) B_(-,K-1) W=Q^D Z A.            (2)

A is acquired in soft O(m) arithmetic and has degree at most m (the degree m+1 leading terms cancel). Thus the normalized Casoratian coefficient in (2) is an actual paid endpoint object. It does not require a full degree-L polynomial, and it gives a precise finite coupled operator rather than substituting a fixed-node interpolated q-shift for a full-polynomial endomorphism.

The degree can be reduced further by factoring the common residue-zero endpoint factors: write B_(e,n)=(X-Q^n) C_(e,n). Then A contains (X-Q^-1)(X-Q^(K-1)), and the remaining difference of two degree m-1 products has leading cancellation. This is another paid endpoint simplification, not acquisition of W.

## What this operator still asks to acquire

The exact common multiplier is

    Z(X)=P_(mK)(X;q) P_K(X;Q).

P_K has degree K=O(m) in the native regime and is paid at every node. P_(mK) is the original scalar long product. Consequently (2) exposes a cheaply acquired rational coefficient of the Casoratian, while W itself still contains that long-product multiplier. Dividing (2) by Z at a native hit would be invalid: zero is exactly the required signal. At nonunit endpoint values, the already proved boundary trees localize to a scalar leaf and retain the explicit nonzero annihilator ledger. The identity is not used to cancel an interior zero or a 0/0.

Likewise the ratio H_+/H_- obeys a first-order q-difference equation with acquired rational coefficient, obtained from (1), but its initial/native values are not supplied by this coefficient. The quotient is only an identity after unit checks and cannot stand in for collision detection. A finite Christoffel--Darboux-style kernel at Q-related arguments is therefore acquired only after normalization by the same unacquired Z.

The native antipodal reduction instead asks for SAME-palette values at (y_j,w_j), with

    w_j/y_j=Q^K gamma^(-2N) gamma^(-2a_j).

This is a public geometric dependence on the explicit quadratic-residue coset of a_j, but it is not the common Q shift in (1). Iterating (1) does not transport these exact nodes without acquiring their actual intermediate/origin data. The lifted equation v_j^2=4a_jN modulo m^3 supplies their carried exponents; it does not replace their integer gamma exponents by residues in a genuine additive-character group. No source-preserving character transform completing that transport was found.

## Endpoint of this pass

A concrete coupled finite operator and its full O(m)-degree coefficient are acquired above. Its unnormalized output contains exactly the original long-query multiplier Z; the available native point relation does not currently remove that multiplier. No paid soft-O(m) evaluator for all H values, collision locator, or improved exponent follows. A useful next theorem would acquire the unnormalized Casoratian at the native coupled points (or another coupled invariant retaining its zeros) directly, without first computing Z and without treating the normalized coefficient as that observable.
