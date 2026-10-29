# Techniques from the Euclidean wave local-smoothing paper

26 October 2026. Requested study of OpenAI's 59-page draft dated
25 October 2026, [Local smoothing for the Euclidean wave equation](https://github.com/openai/math/blob/main/preprints%2FLocal-smoothing-for-the-Euclidean-wave-equation-October-25-2026%2Fpaper.pdf).
Three parallel readings covered its proof, applications and appendices;
the central identities and proposed finite transfers received additional
checks. This is an applicability study, not a certification of every PDE
claim in the draft. The existing factoring goal remains paused.

**The most useful ideas are compatible determinant corrections, rank-one
linearization, invariant-preserving currents, and choosing one aggregate
across several scales.** We executed finite analogues rather than treating
the smoothing estimates themselves as computational savings. No faster
whole-family collision query follows from this study.

The paper's N is a frequency scale, h its reciprocal, and K a fixed
analytic constant. Below, native N is the semiprime, K its sixth-root
budget, J the number of rows, and h the clock length.

## 1. Cancel the determinant with a compatible correction

The core is Proposition 4.2, equations (4.10)–(4.13), printed pp.16–17.
A current and a Hessian cofactor have separate conservation laws. The
paper constructs a potential and an energy correction whose Laplacian
produces exactly the unwanted full determinant. The two determinant terms
then cancel; boundary geometry makes the correction's own boundary flux
zero. Lemma 4.3 shows that useful energy remains.

For us, the valuable feature is that the cofactor identities are
polynomial: they can hold at a singular matrix, without taking its inverse.
The critical qualification is compatibility. An arbitrary matrix is not
a Hessian field, and a formal potential is not an acquired potential.

An exact ordinary-matrix version of the rank-one segment calculation is

\[
\int_0^1\det\bigl(tD+(1-t)uv^T\bigr)\,dt
=\frac{\det D}{J+1}
+\frac{v^T\operatorname{adj}(D)u}{J(J+1)}.
\]

This is coefficient integration of a two-term polynomial, with native
J and J+1 certified units. It preserves a selected cofactor without a
division by det D. We evaluated it on our acquired Macdonald/shift
operators in soft J. On the singular operator I-M it returns the known
evaluation-at-zero projector. On D=diag(W_h(T_j)) it gives the desired
physical cofactor pair, but those entries are precisely the unpaid long
products. Thus the identity is usable, while the correct inexpensive
singular operator remains to be found.

See [determinant-cancellation.md](determinant-cancellation.md), §§1–3.

## 2. The planar appendix suggests a linear boundary formulation

Appendix D, pp.48–49, uses the coefficient of a rank-one background to
replace the nonlinear auxiliary determinant equation by a linear
Dirichlet equation. We tested a finite version with an entirely explicit
operator. For the useful native source

\[
f_i(\delta)=\frac{p(q^{i-1})}{F(q^{i-1})+\delta},\qquad
2u_i-u_{i-1}-u_{i+1}=f_i,\quad u_0=u_{h+1}=0,
\]

the exact boundary identities are

\[
u_1+u_h=\sum_{i=1}^h f_i,\qquad
u_h=\frac1{h+1}\sum_{i=1}^h i f_i.
\]

At a unique collision q^I, if A=p(q^I), the two boundary residues are
(h-I)A/(h+1) and (I+1)A/(h+1). Their sum retains the useful amplitude;
their ratio also encodes the clock index. Taking p=F' and p=H_w retains
the established row-mark interface.

A four-state polynomial transfer computes these boundary numerators
without inverting a colliding source. Its evaluated cost is still
soft(J+sqrt(Jh)). The Green function is explicit, but its application to
the singular source is not free. For a regular polynomial source the same
boundary values cost soft J and carry no collision residue.

There is also an exact discrete cofactor-divergence identity in two
directions. Its boundary flux requires shifted products: applying the
ordinary differential product rule to forward differences gives the wrong
minor. The correct finite identity is supplied in the report, §4.

## 3. The paper's passive invariant is our discriminant in coordinates

Equations (2.10)–(2.13), p.9, give the passive invariant and a factored
angular-mismatch identity. In its scalar version, the substitution

\[
(Y,P,S_1)=(2a,\ell,-cN)
\quad\Longrightarrow\quad
\Phi=\frac{\ell^2-4acN}{4a}
\]

identifies it with a native row's discriminant. This is an exact rational
identity, with the nonzero-a and unit conditions checked; axis rows retain
their existing handling.

We tested the apparent shortcut of shifting the clock while preserving
this invariant. Replacing ell by ell-HI at fixed a requires

\[
c_I=c+\frac{HI(HI-2\ell)}{4aN}.
\]

Under the native short-window bounds, integrality forces HI=2ell. This
gives only a possible centered-endpoint reflection. The corresponding
short integral unipotent flow likewise yields the known reflection.
This rules out that particular transport, not other transformations that
change more coordinates. It also explains why reducing the discriminant
modulo N too early loses the relevant integer condition.

The coherent-current construction supplies another exact analogy:
if U_0 and U_w are the long unmarked and marked resolvents, then
Res(delta U_w conjugate(U_0)) and Res(delta U_0 conjugate(U_0)) preserve
the unique-hit mark ratio. Both resolvents remain unacquired. Details and
the original multi-hit-output distinction are in
[current-localization.md](current-localization.md).

## 4. Aggregate once at a cutoff determined by two scales

Appendix B, especially (B.7)–(B.8), pp.44–45, is the most useful
organization principle. It chooses the largest admissible angular
low-pass from both output radius and radial frequency, treats that entire
aggregate once, and estimates the exceptional bands separately. It
reassembles the pieces before using a theorem that requires their original
frequency support.

A precise native candidate is to split the initialized rational-Newton
section/quotient operator into one jointly acquired coarse contribution
and explicit exceptional carry operators. The cutoff should depend on
both actual row support and physical clock span. The test is whether the
same-root contraction can be shared across all admitted depths, with a
proved total cost for the exceptions. Merely applying each old query once
per band would retain the old bill.

This is a proposed next experiment, not one executed in this study. It
needs exact residue preservation or a remainder proved to have no useful
pole; a small analytic norm is insufficient.

## 5. Further techniques and their precise limits

| Technique and location | Useful requirement for our hybrid |
| --- | --- |
| Symbol-adapted Gaussian and two coherent flows, §2 pp.6–10; §5 pp.18–21 | Build cancellation around the actual phase law and retain interference before squaring. Any modular filter still needs an exact character/zero-detection bridge. |
| Cofactor polarization and boundary compression, §3 pp.11–13 | Prove conservation from a compatible potential, and prove the boundary coefficient vanishes. A low-rank matrix description alone does neither. |
| Two-circle propagation, §6 pp.21–23 | Track both outward and return costs. The two logarithmic losses are sharp for the scalar comparison used there; this is not a bound on arithmetic operations. |
| Three-way scale splitting, Lemma 11.3 pp.35–36 | Seek acquired simple correction operators at far scales and only a narrow expensive middle range. Norm orthogonality does not itself reduce the number of calls. |
| Random signs, §9.2 and Appendix C | Algebraic cross-term cancellation transfers, but requires acquired signed amplitudes. Positive real squares cannot be treated as noncancelling field sums. |
| General symmetric pencils, Appendix E pp.49–53 | The current construction can follow nonquadratic phase surfaces. Its isolated real eigenvalue, curvature and spectral-gap conditions must be supplied in any new representation. |

The [multiscale study](multiscale-propagation.md) records the exact
interfaces and the remaining sections' radius-selection, endpoint and
surface-transfer arguments. Appendix A provides existence and regularity
for the auxiliary PDE, not an arithmetic algorithm or a bit-cost bound.

## Assessment

The strongest algebraic lead is a compatible cofactor correction whose
potential is acquired from our short inputs and whose boundary retains
the physical pole. The strongest way to organize such a calculation is
the single aggregate chosen from two scales. We have exact finite tests
for both the determinant and boundary mechanisms, and a concrete failed
invariant-preserving clock move. None yet reduces the guaranteed query
cost below the retained soft K^(5/4).

Reviews: [determinant and boundary](review-determinant.md),
[current and native invariant](review-current.md), and
[multiscale/source scope](review-multiscale.md). No new factoring examples,
implementation, Lean changes, commit or push were made. The broader goal
was not resumed.
