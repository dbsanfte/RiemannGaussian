# Independent review: constant-power core and joint forcing

23 October 2026. **PASS; no correction required.**

Complete reviewed inputs:

* `constant-power-correction.md` SHA256
  `e4481d2a6a3eb536fc13108ba7903bb4e61cac38134a805044aaa36afc3fbdb5`.
* `joint-forcing-attempt.md` SHA256
  `34ebb3bcc289c03a0d825a9bc37cbefd1f949a610354e062641fa22a0728a5a7`.

## Constant-power construction

The companion convention is multiplication by X modulo the actual
monic F, distinct from the earlier first-row companion convention.
For all nonterminal monomial columns DC=qCD, and the last column gives
`w_i=f_i(q^J-q^i)` with the displayed positive sign. Multiplying by
I-C therefore gives `MC-qCM=u v^t` exactly.

The Krylov identity `M^k e0=P_k(C)e0` is valid through k=J: before
the last multiplication the representative has degree below J, so
coefficient scaling really is substitution by q. Only the final
degree-J product is reduced. The source correctly does not extend this
argument past J.

The q-binomial coefficient formula (3a) has the correct kappa factors.
Reversing its upper-triangular index gives convolution with `1/Q_n`;
the proposed inverse satisfies

    sum_(i=0)^n kappa_i/(Q_i Q_(n-i))=P_n(1)/Q_n.

This is one for n=0 and zero for every 1<=n<=J. Thus both finite
basis conversions are acquired in soft J. All Q_i and kappa_i are
certified units, and no infinite q-series or order advice is used.
The first J Krylov columns have unit triangular diagonal. The actual
cyclic companion similarity consequently proves the characteristic
polynomial, including over this composite ring. Monic modular powering
and the two conversions pay soft(J log L) for the constant core, even
if M is singular; no inverse of M or of the characteristic polynomial's
constant coefficient appears.

The quotient invariant is retained correctly. Reduction gives
`F(qC)e0=-w`, so the first correction has sign `-s_n`. Multiplication
by `1-q^n X` contributes exactly the scalar quotient `-q^n t_n`.
Evaluation at qC then yields the stated second recurrence, including
its q^(n+1) coefficient. R0=e0 and s0=0 genuinely initialize the 2J
algorithm; Q_n is only a proof invariant, not a supplied vector.
Each step costs soft J, hence direct total soft JL with O(J) residues.

For the shear, `A_(n+1)M-MA_n=q^n u v^t` follows directly from the
same boundary. Also `(M-A0)e0=(I-C)(D-I)e0=0`, so eta0 really is zero.
Expanding the two updates proves `eta_(n+1)=M eta_n` and
`R_(n+1)=A_n R_n-eta_n`. Thus the zero auxiliary channel leaves the
original variable-coefficient product in the other channel. Neither
the shear nor the fast constant core computes the forcing sum for free.

The q-Calogero observation uses a legitimate C inverse, because the
native roots are units. It gives the finite nilpotent Jackson derivative.
The source properly limits its use of Iliev's rational wave formula;
the repeated-zero spectrum fails the two-spectrum hypothesis for J>1.
The weaker proposition's second-spectrum condition is not silently
asserted for every native input, nor is a complex q-exponential supplied
as a modular scalar. The cached primary text at the cited definitions
and proposition/theorem was checked for this scope; this is not a review
of the entire geometric theory.

## Joint companion-algebra execution

The reversal is exact:
`X^L P_L(1/X;q)=(-1)^L q^(L(L-1)/2) P_L(X;q^(-1))`.
It turns the initialized whole forcing vector into the displayed
polynomial evaluated on the constant companion, with all J coordinates
recovered by the paid Krylov conversion.

The scalar C-transpose circuit is formally linear with acquired
base-ring constants, so extending its evaluation to R[X]/f is valid.
The complete-block and ragged expressions include every coefficient
exactly once. Scalar preprocessing is reused once, but the K quotient
weights and B quotient outputs each retain their rank-J cost. The
stated soft `(sqrt L+J(B+K)+J)` work and corresponding dense-quotient
storage ledger are therefore sound. Empty J and zero L branches are
separated. No scalar transform call is substituted for an algebra-valued
call, and the outer sum of (6) is correctly retained as a possible
future joint contraction rather than a necessary output array.

Both reports preserve original coverage and all-output recovery. Their
executed algorithms and fast constant operation do not establish a
better whole-query exponent; neither asserts an operation lower bound.

Read-only review. No report/repository edits, examples, numerical tests,
downloaded code execution, new backend or extra theorem transfer.
