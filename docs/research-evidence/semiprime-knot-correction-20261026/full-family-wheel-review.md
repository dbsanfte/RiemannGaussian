# Independent derivation: complete signed-family masks

26 October 2026. This derives the proposed axis-wheel completion directly
from the original row labels. It complements the nonaxis character proof.
The outcome is a complete coverage-preserving mask algorithm, with only
the familiar logarithmic wheel saving in the dominating axis term.

## Axis masks and coverage

For a horizontal axis `(a,b)=(epsilon*k,0)`, epsilon in {+1,-1}, write
`lambda=t*k`, 0<=t<k. Its physical candidate is the integer

    p_star(I)=(H*I-lambda)/a=epsilon*(k*I-t).

At the actual horizontal witness this equals the actual factor P. Give
the vertical swapped row `(0,epsilon*k,lambda)` exactly the same mask,
using this horizontal expression. It must not independently use Q or
re-derive an unrelated physical sum. The swap collision at the other
prime occurs at the same original I and survives this inherited mask.

Choose a squarefree B composed of auxiliary primes greater than 3 and
less than 16H, all coprime to N. Retain precisely the axis indices with
`gcd(p_star(I),B)=1`. Since both actual factors exceed 16H on the prepared
branch, the true axis witness always passes. The affine slope epsilon*k
is a unit modulo B, so every axis row has exactly phi(B) allowed residue
classes modulo B. Negative or otherwise false factor candidates cause
no issue: retaining extra leaves is harmless.

For t>0 the opposite row has epsilon'=-epsilon, t'=k-t and I'=1-I.
Direct substitution gives `p_star'(I')=p_star(I)`. At t=0 use I'=-I,
with the same equality. Thus the opposite transport is consistent too.
The simplest implementation uses the complete signed catalogue before
the optional half-center knot fold. If a harmless horizontal row has
already been pruned, its label can still define its retained vertical
partner's mask; it is not reintroduced as a collision leaf.

Every genuine covered shortest vector is either nonaxis, and passes the
quadratic-square mask, or horizontal axis, and passes this prime wheel.
A vertical axis need not be a separate coverage source when P<=Q; the
swapped rows are nevertheless retained as required for the global-zero
witness. The initial unfiltered coverage theorem and its original-leaf
consumer therefore extend to these fixed masks. This need not preserve
every accidental zero of the old query; coverage and valid recovery,
not equality of all old/new prefix values, are the requirements.

## Exact counts and costs

Take all primes 3<ell<=y, with `y=c*log k` and any fixed 0<c<1/4.
Let B be their product and t their number. Elementary prime sieving
acquires these data. PNT and Mertens' product estimate give

    B=k^(c+o(1)),
    t=(c+o(1))*log k/loglog k,
    phi(B)/B=Theta(1/log y).

The nonaxis proof still applies: its previously bounded Euler product
is now `O((log y)^3)` instead of a constant. With the explicit catalogue
bound `O(k*log k*tau(D)/D)`, the nonaxis density sum is at most

    O(k*log k*2^(-t)*(log y)^3)=o(k/log y).

There are at most 4k axis phase rows, so the total density over the
complete family is `O(k/log y)`. Hence the explicitly acquired CRT/AP
count and retained original-factor count satisfy

    A_total=O(k*B/log y),
    S_total=O(k*(M+B)/log y).

All APs have common base q^B. The existing paid variable-window evaluator
therefore gives

    soft(k + k*B/log y + sqrt(k*(M+B)/log y)).

At M=Theta(k^(3/2)) and c<1/4, the mask/start term is smaller than the
square-root term. The displayed query bound becomes

    soft(k + sqrt(k*M/loglog k)).

The underlying candidate counts exhibit a wheel reduction. Soft-O
notation already suppresses logarithmic factors, so this is **not** a
new soft exponent or a new deterministic factoring record. In particular
it is not the requested soft(k) acquisition theorem. The mask expansion
is paid and is not falsely declared soft(k).

## Provenance and limits

This is a native-label integration of a classical prime wheel, combined
with the newly costed quadratic masks. Sutherland's
[*Order Computations in Generic Groups*](https://math.mit.edu/~drew/sutherland-phd.pdf),
Algorithms 4.1–4.2, is prior literature for primorial-step savings; the
root review does not claim novelty for that effect. The native algorithm
here filters a candidate prime factor, rather than assuming the order
of beta is itself prime. That distinction must be retained.

Fixed masks may be clipped to any original prefix. A first aggregate
zero forces a newly included original leaf to be nonunit; its row/AP
metadata reconstructs the original nonzero exponent. No rejected factor
is asserted to be a unit or used as a denominator. A prospective fusion
of these masks must preserve that limitation: sieve rejection alone is
not a certificate that an accidental scalar collision cannot occur.
