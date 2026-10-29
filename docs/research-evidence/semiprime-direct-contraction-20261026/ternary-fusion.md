# Execute ternary fusion: all cubic coefficients and a native parent/GP recursion

26 October 2026. Finite arithmetic continuation of the frozen sibling
identity. No tests, numerics, code, Lean or repository changes.

**Positive:** there is a complete exact parent-child recursion, not just
a determinant. Each child root equals its parent root times a small
public q-phase and a power0,1,2 of an acquired GP character. Both first
and second symmetric coefficients are initialized by constant-degree
formulas. The auxiliary GP character has the same smaller-factor
quotient interpretation in whichever monic orientation is good.
The executed SL3/Adams and coarse-marker contractions retain the long
clock: no target-soft-K scalar/cofactor readout was obtained.

## 1. Exact parent and child inputs

Work at pure K=2*3^e, e>=3, H=K^2, and put delta=K/3,
H0=delta^2, q0=pi^H0, so q=q0^9. The current preparation, not a
new smaller-scale setup, supplies all bases and large rough orders.
The smaller modulus delta is used to DEFINE acquired arithmetic rows;
we do not pretend N<=delta^6 or rerun an uncharged torus supplier.

For A take a parent colour j in[1,delta), unit modulo delta, and

    a0=[N*j^(-2)]_delta,
    ell0=[-a0*j-N*j^(-1)]_(H0), centered,
    p=pi^ell0*barpi^(a0+N).

Its three child colours are j+s*delta, s=0,1,2. Their coefficients
are exactly a0+delta*r for r=0,1,2, in a publicly computable
permutation: inverse-square lifting has derivative -2N/j^3, a
3-unit. Reorder by coefficient r and keep the ACTUAL centered
child phases ell_r and original tags. Define

    c_r=(ell_r-ell0+delta*r*j)/H0,
    U_j=pi^(-delta*j)*barpi^delta.                 (1)

These c_r are INTEGERS unconditionally. Modulo H0, the parent phase
is invariant under changing its colour lift by delta, while changing
a0 to a0+delta*r subtracts delta*r*j from the phase. This proves
the divisibility before any hidden factor is considered.
Because |ell_r|<=9H0/2, |ell0|<=H0/2 and j<delta,
|c_r|<=7. All carry integers are supplied, not discarded.

The FULL GLOBAL root recursion is now exactly

    y_r=p*U_j^r*q0^(c_r), r=0,1,2.                (2)

It is verified by substituting (1) into both pi/barpi exponents.
No equality modulo an unknown order is used. The acquired character
is one GP in its parent colour:

    U_(j+1)=pi^(-delta)*U_j.

Only unit-colour indices are retained, with their public gaps. The
map (2), its tags, carries, roots and coefficients cost soft K for
all parents.

For B the same statement holds with b0=[j^2/N]_delta,
p=pi^ell0*barpi^(1+b0N), and c=[N/j]_delta:

    U_j^B=pi^(-delta*c)*barpi^(delta*N),
    c_r^B=(ell_r-ell0+delta*r*c)/H0,
    y_r^B=p*(U_j^B)^r*q0^(c_r^B).                 (3)

The B characters form a GP under the public permutation j->N/j.
Thus the full formulas do not presume the smaller nonsplit orientation.

## 2. Acquire MORE than the cubic determinant

Set A_r=q0^(c_r), U=U_j. With child root p*U^r*A_r,
its three elementary symmetric coefficients are exactly

    S1=p*(A0+A1*U+A2*U^2),
    S2=p^2*(A0*A1*U+A0*A2*U^2+A1*A2*U^3),
    S3=p^3*A0*A1*A2*U^3.                         (4)

Consequently the entire child cubic

    f(z)=1-S1*z+S2*z^2-S3*z^3

is acquired in O(1) arithmetic per parent. These are actual initialized
numeric coefficients, including the small phases and all carries.
They need neither the hidden quotient nor a three-dimensional
root-of-unity representation. The product relation from the previous
packet is the middle-reference consequence

    product_r y_r=y_1^3*q0^(c0+c2-2c1).

Equations (2)-(4) refine that determinant by identifying both missing
trace characters explicitly in a parent root and acquired GP character.
They do not say those characters can be ignored.

At the true parent colour, A's character has the local interpretation

    U_j=q0^u, u=(R-j)/delta.

For B it is q0^v with v=(N/R-c)/delta. Therefore in the GOOD monic
orientation the latent quotient is always a quotient of the SMALLER
factor: R=P for good A, N/R=P for good B. This uniform bound is
stronger than using a possibly large nonsplit factor blindly.
It does not acquire the quotient digit; U_j itself was already acquired
by the explicit powers in (1)/(3).

In the GOOD family and original bounded clock, the previously proved
small-gap versus ord(pi) theorem makes every local child hit an exact
integer physical event. If the parent row has stationary integer index
I0, that child hit therefore has the exact index relation

    I0+r*u+c_r=9i

(or v and c_r^B for B). This is the finite clock handoff, not a free
replacement i by I0/9. In particular the small coefficient carries do
not remove the term containing the unknown factor quotient.

## 3. Execute the classical SL3/Adams contraction

The known sibling determinant permits an explicit determinant-one
normalization: divide by the acquired unit

    d=y_1*pi^[H*(c0+c2-2c1)/27].

Since e>=3, H/27 is an integer, and d^3=product y_r. No fractional
power or unknown root is requested. For the normalized 3-by-3 diagonal
matrix, its fundamental and dual traces are S1/d and S2/d^2.
Cayley--Hamilton gives the usual SL3 cubic/Adams identities. In the
unnormalized coefficients the fully explicit cubing operation is

    S1new=S1^3-3S1*S2+3S3,
    S2new=S2^3-3S1*S2*S3+3S3^2,
    S3new=S3^3.                                  (5)

These acquire the cubic with roots y_r^3 in O(1) per parent.
They are polynomial identities over the actual ring, not a semisimple
representation or quantum-group genericity assumption.

The native pi/barpi/q orders are 3-rough. Thus cubing is injective
on all relevant local subgroups: y_r^3=q^(3i) iff y_r=q^i.
Equivalently, the other two factors in the auxiliary cubic norm
f(z)f(omega*z)f(omega^2*z) are units at native z=q^(-i).
An auxiliary omega needs only a rank-two extension and 3 is a unit;
its existence is NOT confused with the arithmetic q. This verifies
zero/nonunit and tag preservation for this legitimate cubing operation.

But (5) changes the base to q^3 and roots to y_r^3 while leaving
EVERY clock index i=0,...,h-1. It does not turn q=q0^9 into a
shorter q0 clock. The trace terms in (4) survive, with U cubed and
phases multiplied by3. A character/Adams operation alone therefore
supplies no missing scalar or boundary initialization. This is the
actual finite cubic analogue of the old safe Graeffe norm, not a
claimed new query algorithm.

Primary context checked: Kuperberg, *Spiders for rank2 Lie algebras*,
[arXiv:q-alg/9712003](https://arxiv.org/abs/q-alg/9712003), describes
A2/SL3 representation-theoretic contraction. No spider theorem is
asserted to compute these arithmetic clock norms. The determinant,
trace and Adams identities actually used here are directly proved
by the three acquired eigenvalues and their characteristic polynomial;
there is no quantum skein parameter substitution or unpaid clasp.

## 4. Coarse factor tags survive fusion, but the old advancement cost remains

All three child colours have the SAME tag modulo delta. Thus one may
mark the whole cubic with that coarse residue w without identifying
a branch. In the first-jet algebra, the exact formula is

    product_r(1-y_r*z+epsilon*(1-Y*w))
      =(1+epsilon*c)^3*f(z/(1+epsilon*c)),
    c=1-Y*w,
    first epsilon coefficient=c*(3f(z)-z*f'(z)).   (6)

Only inverses with constant term1 are used. At a unique hit, (6)
retains its cofactor amplitude and returns the correct coarse tag.
The new HH consumer accepts that tag once the modulus is large enough;
no unobserved child digit is part of its required OUTPUT.

This is a lawful reduction of the marker specification, but not yet
its scalar acquisition. The existing block engine acting on the
parent cubic has one-third as many rows but degree3 per row; the
actual clock coefficient polynomial still has total degreeK. Its
initialized first-jet cost remains soft(K+sqrt(Kh)). Retaining the
cubic coefficients avoids any dense inverse or forbidden collision
normalization, but does not improve that explicit implementation.
This statement is a charge for that engine, not a lower bound against
another scalar algorithm on (2).

Attempted interval overcover has the complementary problem. Replacing
child clocks by a q0-parent clock must cover 9i-r*u-c_r. Even with a
public correct factor-size bin for the smaller factor, the envelope
has length O(9h+P/delta+1). Reducing row count by3 while multiplying
clock length by about9 increases the old row-clock mass by a constant
factor, rather than creating a power saving. This is ONLY the literal displayed overcover, not a sharp universal
parent-window cost or lower bound. Rebuilding the parent physical bound
in a tight balanced factor bin can make the clock grow by about 3
when the row modulus shrinks by 3, maintaining the row-clock mass
rather than worsening it by 9/3. No power saving is proved by either
accounting, and that sharper reconstruction needs its actual starts,
coverage and decoder charged. Across deeper levels the literal
overcover expands as the modulus squares shrink. Neither the endpoint
masks nor the unknown quotient term may be
silently omitted. Added leaves need their own correct-bin integer
quadratic decoder before this overcover is used.

## 5. Exact cross-level GP-character recursion

There is useful closure beyond one triple. Let delta=3epsilon and
parent colours j=j0+s*epsilon. A's characters obey

    U_delta(j)=U_epsilon(j0)^3*q_epsilon^(-3s),
    q_epsilon=pi^(epsilon^2), q_delta=q_epsilon^9. (7)

It follows just by substituting U_m(j)=pi^(-m*j)*barpi^m.
For B retain the public inverse-colour digit t, defined by

    c_delta=[N/j]_delta=c_epsilon+epsilon*t,
    c_epsilon=[N/j0]_epsilon, t in {0,1,2}.

Then the exact companion law is

    U_delta^B(j)=U_epsilon^B(j0)^3*q_epsilon^(-3t). (8)

The inverse-colour digit need not equal the original colour digit s;
it is acquired from the actual representatives and is not discarded.
Combining (7) with the next instance of (2) expresses all nine
children using a single next-parent root, powers0,...,8 of its GP
character and explicit finite q_epsilon carries. This is a real
finite hierarchical data closure; no new numeric root value is a
hidden input.

The carries and the coefficient-digit/colour permutation still enter
the clock product. The full descendant expression has the form
p*U^d*q_parent^(c_d), not a complete auxiliary root orbit. Cancelling
the determinant of a block fixes only its top symmetric coefficient.
A useful further theorem would jointly contract that known GP index
and its acquired carry function in the LONG clock, without generating
all descendant coefficient blocks or dividing their zero norms.
The present calculation does not supply that theorem. Both monic
orientations and the a=1 partial triples must be retained; if exceptional
roots were previously paid/removed, restore no missing branch silently
when applying a complete-triple identity.

## Outcome

The complete elementary-symmetric recursion (4), its explicit parent
GP characters, and cross-level relation (7) are stronger initialized
structure than the old determinant-only sibling identity. They give
a particularly concrete joint scalar target (2),(6), with small public
carries and factor-tag provenance intact. The executed SL3/cubic-Adams
norm and the literal parent-overcover implementations do not solve it.
No soft-K norm/cofactor readout or new factoring exponent is proved.
