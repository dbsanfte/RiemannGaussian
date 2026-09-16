# Signed mass transport of the original carrier

Lean now lets an original amplitude participate in several cancellation
pairs using only its unsent mass. Every step preserves its complex
direction, removes equal mass from both endpoints, and keeps the complete
sent pair as a complex vector. This avoids spending a whole integer merely
because one smaller partner has been exhausted.

After a fully charged fallback visits every distinct original pair, the
final unsent mass has an independently proved source-normalized bound
tending to zero for every fixed 0 < u < 1. This is **not free coverage**:
all fallback chord costs remain in the whole upper bound. Their sufficient
source-scale control, or a signed bound for the combined sent sum, remains
open. No new zero-free region or RH proof follows.

## Equal mass, original directions

For a complex amplitude z, define its ray z/|z|, with zero kept at zero.
Given z and w, let m be the smaller of their norms. One step sends

```math
m\left(\frac z{|z|}+\frac w{|w|}\right)
```

and leaves the two remainders on their original rays. Their norms are
|z|-m and |w|-m. At least one endpoint is exhausted; neither can grow or
reappear later. `sum_eq_sent_add_remaining` proves the exact complex
partition for every supported list of distinct pairs, even when vertices
occur more than once. The list may include pairs from different prime
counts. No coefficient family or cancellation hypothesis is assumed.

`transportCost` charges each sent chord norm and the entire final unsent
mass. It bounds the full original sum and never exceeds the initial
triangle allowance. The richer `sentAfter` sum retains interactions among
all sent pairs before that relaxation.

## Arithmetic sign remains in the phase cost

The full polynomial carrier retains its zero-height complex direction
times the exact multiplicative phase. In particular, for P=1 each original
atom is its real signed Riesz coefficient times the nonnegative factorial
envelope and exp(-it log n). This is a complex identity, not a real-part
projection.

For signed real amplitudes a and b at phases x and y,
`pairCost_real_phases` and `pairCost_bandWeight_one` give

```math
\operatorname{cost}=2\min(|a|,|b|)
\begin{cases}
|\cos((x-y)/2)|,&ab\ge0,\\
|\sin((x-y)/2)|,&ab<0.
\end{cases}
```

Zero mass makes the boundary convention harmless. Equal signs favor
opposite phases; opposite signs favor nearby phases. Splitting removes
the amplitude-mismatch charge from the sent portion, while keeping every
unsent portion available for later pairs. The original full-polynomial
direction identity remains available when P is not one.

## The final unsent mass is controlled

`remainingAfter_edge_zero` proves that the final nonzero support is
independent of every edge already processed. After all distinct pairs
have been visited, at most one nonzero original amplitude survives.
Consequently its entire unsent mass M obeys

```math
M^2\le\sum_{n\in\mathcal B_N}|B(n)|^2.
```

`actual_remaining_mass_sq_le` connects this directly to the existing
independent diagonal-energy estimate, including the complete polynomial,
original support and Riesz normalization:

```math
M_N^2\le E(P,r)\,r^{-2N},\qquad 0\lt r\lt1.
```

The finite constant E is `zetaArithmeticEnergyConstant`; its definition
uses a genuinely summable divisor-square Dirichlet mass. It is not a
numerically evaluated threshold. Choosing u < r < 1 proves
`tendsto_actual_remaining_mass`:

```math
u^{N+1}M_N\longrightarrow0,\qquad 0\lt u\lt1.
```

This holds for every fixed full polynomial, arbitrary preceding pair
lists, and even arbitrary height sequences. The source scale u is fixed;
no uniform rate as u approaches one is asserted. The cutoffs are the
actual moving lengths, not a trial replacement.

## The original source stays in one signed sum

`actual_band_le_completed_prime_transport` uses the actual gcd-based
prime-pair list followed by the complete fallback. Every term and every
fallback chord is included in this specified whole-carrier bound.
`tendsto_actual_band_sub_sent` proves that the normalized difference
between the original carrier and `sentAfter` tends to zero.

The terminal
[`tendsto_actual_sent_source`](../RiemannGaussian/ZetaRieszTransportSource.lean)
therefore retains the full conditional source

```math
u^{N+1}\operatorname{sentAfter}_N\longrightarrow -m(\rho),
\qquad u=\frac32-\Re\rho,
```

for every hypothetical right-half zero, using its full pole-jet polynomial
and unrestricted multiplicity. No exposure or simplicity premise is added.
The original source theorem supplies these analytic obligations; the
independent remainder estimate is valid without a zero hypothesis.

What remains is an independent sufficiently strong bound for the **whole
signed sent sum**, or for its fully charged accumulated chord allowance.
The decay of the final unsent mass does not bound those charges. Taking
separate pair norms loses their common phases; the exact complex sum is
retained so further work can use those interactions.

The four focused modules belong to the arithmetic family and ordinary
root. Their strict Lean, declaration-lint and transitive-axiom gates use
only the permitted standard axioms. Default RH, zero-free and certificate
endpoints and both top-ten lists remain unchanged. Small floating-point
transport probes are neither certificates nor asymptotic evidence and do
not run in ordinary CI. No historical novelty claim is made here.
