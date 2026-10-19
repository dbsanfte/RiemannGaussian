# Common-integer depth transport and the remaining physical source

Local research checkpoint, 2026-10-19. This continues the
[Siegel interpolation review](siegel-interpolation-review.md) and
[native source/coupling audit](arithmetic-operator-native-source-coupling.md).
Four isolated Lean leaves pass. The new finite inequalities retain actual
integer integrality and prime-power depths. They do not yet give an
independent bound for an RH endpoint. The imported strict `Re(s)>7/8`
result is unchanged.

## 1. What survives from the interpolation idea

The useful feature of [Banks's argument](https://arxiv.org/html/2610.15483v1)
is that divisibility at different primes constrains the **same nonzero
integer** whose Archimedean size is bounded. Our next test therefore kept
one actual cyclotomic product

\[
P=\prod_{2\le e\le M}\Phi_e(b)^{\beta_e}\in\mathbb Z,
\qquad b\ge2.
\]

[ArithmeticOperatorPrimitiveTransportAudit](../scripts/ArithmeticOperatorPrimitiveTransportAudit.lean)
proves that, given an actual primitive root of order `d` modulo prime `q`,

\[
q\mid\Phi_e(b)\quad\Longleftrightarrow\quad e=dq^j
\quad\text{for some }j\ge0.
\]

It proves the exact signed valuation ledger on that chain, including
characteristic-divisible indices, order one and the two-adic head. A child
index can have only one nonprimitive prime. The actual descendant
valuations remain explicit in Lean; replacing them by one uses a separate
paper-level LTE calculation.

Write each value as its primitive part `R_e` times its nonprimitive part
`L_e`, and form `R_+, R_-, L_+, L_-` using the positive and negative
exponents. The independently checked paper argument gives the collective
restriction

\[
R_-\mid L_+.
\]

Every negative primitive factor must be paid by the actual positive
nonprimitive factors; the same budget cannot be spent independently on
each parent. An elementary order split gives

\[
\sum_{e\le M}\log L_e=O_b(M^{2/3}\log M).
\]

With only the positive exponents bounded by `B`, Zsigmondy's theorem and
explicit fixed heads then give a direct comparison of the **literal phased
integer packets** of `P` and `R_+`, uniformly in physical cutoff and height:

\[
|\Psi(P;X,y)-\Psi(R_+;X,y)|
 =O_b(BM^{2/3}\log M).
\]

The common initial prime-power depths cancel before this error is bounded.
No phase is reset. These collective and asymptotic statements are paper-level;
the incidence and valuation statements above are compiled.

This only preserves an already-established continuous row-Mellin source
above exponent `a+2/3` when `B=O(M^a)`. It supplies neither that source nor
a bound on the remaining positive primitive product. Constants depend on
fixed `b` and cannot be reused uniformly over growing bases.

## 2. A checked quantitative repair of the old depth mismatch

The exact phase-linearization counterexample remains valid. Nevertheless,
for the restricted exponents `beta_e in {-1,0,1}`, its error has a sharply
identified support.

For a prime `q`, let `v_e=v_q(Phi_e(b))`, `V=sum v_e`, and let `O_e` be the
sum of the **unsigned original** depths preceding row `e`. For any bounded
complex depth weight `f`, put `D_f(v)=sum_(1<=r<=v) f(r)`. Define the exact
cumulative-row ledger

\[
\mathcal L_f=\sum_e\beta_e
 \bigl(D_f(O_e+v_e)-D_f(O_e)\bigr).
\]

[ArithmeticOperatorSignedDepthTransportAudit](../scripts/ArithmeticOperatorSignedDepthTransportAudit.lean)
proves

\[
\left|D_f(v_q(P))-\mathcal L_f\right|
 \le4\,(V-1)_+.
\]

When `V<=1`, equality of the two packets is exact. Thus the whole discrepancy
is paid by repeated prime-power depths, retaining arbitrary bounded masks.
The leaf also proves the summed physical version with
`f(r)=1_(q^r<=X)*exp(-iy log(q^r))` and weight `log q`.

The earlier proper-power mean extends by monotone convergence to all depths,
giving `O_eta(M^(1/2+eta) log M)` for the **unconditional compatible complete-base
mean**. That paper-level mean is below every fixed `M^beta`, `beta>1/2`.
It is not a bound at an arbitrary fixed integer base, or on a normalized
population selected by integrality.

The exact warning is small:

\[
\frac{\Phi_6(b)}{\Phi_2(b)}=b-2+\frac3{b+1}
\]

is integral for integers `b>=2` only at `b=2`. Integrality can therefore
select a density-zero population. Its averaging cost cannot be discarded.
Finite-base transfer also needs its own boundary and height estimate: the
new error uses untruncated repeated depths, not merely those below `X`.
The old example `C_6(2)/(C_2(2)C_3(2))=155` remains a nonzero error at prime
three and lies exactly in the repeated-depth sector. Exponent two is also
checked to break the single-depth identity, so the coefficient restriction
is essential.

## 3. The actual central error can be paid in a small larger range

The parallel audit checks the **same native central rows**, including grid-zero
floors, selected marks, spectral cubes, calibration and moving height. It finds
that the moment producer permits an independent positive auxiliary parameter
`Delta`; it need not equal `betaStar-7/8` as in the final imported wrapper.

The actual terminal certificate needs
`kappa>=3/4` and `2*betaStar-1<=kappa`. For `betaStar<=7/8`, choosing
`kappa=3/4+2*Delta` preserves the native four-field moment input. The fixed
fine slots, exclusions and height parameter must be chosen in their original
order before the scale grows. This is a paper-level application of imported
theorems, independently reviewed against their exact statements.

[QuasiRHCentralRateFrontierAudit](../scripts/QuasiRHCentralRateFrontierAudit.lean)
proves a `1/5000` margin for the actual balanced exponent and its complete
scalar cost ledger. Composing the native estimates then pays all central
rows at source scale for

\[
\beta_\star>\frac{2187}{2500}=0.8748.
\]

The full new composition is paper-level, not a newly compiled zero-free theorem.
Even the old certified margin already supports a slightly smaller extension.
The exact ideal limit of this unchanged norm envelope is approximately
`0.874771852691`; that number is an algebraic envelope frontier, not a bound
for any actual zero or an assertion that an extremal bin occurs.

Crucially, the protected source belongs to `normalizedProbe-F_all`.
Making `F_all` small still leaves the physical probe unpaid. It does not
create a new zero exclusion or pay the theta covariance.

## 4. A fixed-row theta-residue shortcut fails at the actual coordinate

The physical Mellin exponent is `u_raw=w+z`. Thus the theta pole has locus
`w+z=7/6`. On the actual central line `Re z=17/50`, its coordinate is
`w=62/75-i Im z`. An earlier scratch inference `w=2/3` omitted a second
physical square-root factor; it was corrected before a successful theorem
or frozen claim.

[QuasiRHThetaCentralJoinAudit](../scripts/QuasiRHThetaCentralJoinAudit.lean)
proves the actual fixed nonprincipal central kernel, and finite sums with
the actual tuple weights, analytic at that locus. Consequently `F_all`
cannot simply be identified with a sum of those fixed-row theta residues.
This does **not** exclude an external-scale source or collective cancellation
as its number of rows and contour heights grow.

The exact joined accounting still gives

\[
\Theta-F_{\rm all}
 =R_{\rm principal}+R_{\rm small}+R_{\rm large}
   +E_{\rm cube}-E_{\rm physical}.
\]

The principal term retains the reciprocal-L source. The available absolute
majorant for the growing free-row dyads is `U^(63/50+delta)`, so it does not
justify exchanging the infinite row expansion with the physical residue.
This is a failure of the available majorant, not a lower bound on the signed sum.

## Validation and remaining decision

The [checkpoint manifest](arithmetic-operator-primitive-depth-frontier-gates.json)
records four strict leaves: **55 local declarations / 48 theorem declarations**
including helpers, 15 namespace linters each, and only standard axioms.
All 657 previous pins and 118 new manifest entries matched before shared
notes changed. Exact probes retain the old counterexamples and all explicit
nonintegrality exclusions. Local research only: no broad build, public
registration, commit or push.

The common-integer route now has genuine additional arithmetic restrictions
and a finite phased transport estimate. Its remaining tests are source
identification and an independent bound for the actual positive primitive
packet, without an unproved averaging change. The native analytic route
still needs an independent signed physical theta estimate or a controlled
joint residue/free-row passage. Neither is supplied by more valuation
bookkeeping or another optimization of the same norm exponent.

The active goal remains eight Tier-1 families visited and none exhausted.
