# Finite signed budgets for the actual carrier poles

The complete xi expansion now gives a finite local upper bound for its
imaginary logarithmic derivative. Its omitted terms have a proved favorable
sign. Every genuine upper carrier pole must pay a unit threshold in this
local signed sum and must lie inside a reflected-zero disk. The bound does
not establish the upper ceiling for the joint residue and strip correction
in the [reflection comparison](suzuki-carrier-reflection-contrast.md).
No new zeta zeros have been excluded.

## Exact paired sign

Write `A(z)=xi(1/2+i*z)`, `q=A'/A`, and `alpha=a+i*d` for a spectral
zero of analytic multiplicity `m`. The critical-line reflection has
spectral coordinate `conj(alpha)` and the same multiplicity. At a nonzero
A point, the complete pair satisfies

```
Im(m/(z-alpha) + m/(z-conj(alpha)))
  = 2*m*Im(z)*(d^2-(Re(z)-a)^2-Im(z)^2)
      / (normSq(z-alpha)*normSq(z-conj(alpha))).
```

For `Im(z)>0`, this is positive exactly inside

```
(Re(z)-a)^2 + Im(z)^2 < d^2.
```

These are the classical Jensen disks, whose diameters join reflected
zeros. The geometry is established in the literature; see
[Level sets of real entire functions](https://www.math.kent.edu/~varga/pub/paper_192.pdf).
The project contribution here is its checked application to the complete
actual xi expansion and Suzuki carrier, with finite windows and all
multiplicities retained. No mathematical-priority claim is made.

The exact complex pair and its signed formula are retained in
[RiemannXiJensenDiskBound.lean](../RiemannGaussian/RiemannXiJensenDiskBound.lean).
At xi nodes the displayed rational formula is not used: both genuine
denominator exclusions are discharged from `A(z) != 0`.

## The complete infinite tail now has a sign

Every nontrivial zero has `abs(d)<1/2`. Consequently every positive pair
lies within ordinate distance `1/2` of `Re(z)`. Critical-line zeros have
nonpositive imaginary contribution throughout the upper half-plane.

Let `q_T(z)` be the original full symmetric Cauchy sum over genuine zeros
with `abs(Re(alpha))<=T`. For

```
T >= abs(Re(z)) + 1/2,  Im(z)>=0,  A(z)!=0,
```

Lean proves that `Im(q_T(z))` is nonincreasing as T grows and that

```
Im(q(z)) <= Im(q_T(z)).
```

The existing complete expansion identifies the limit with the actual q.
There is no assumed infinite remainder estimate. The complete complex
head remains available, so this bound has not replaced the signed identity.

The stronger local version retains only the actual zeros in the ordinate
band `abs(Re(alpha)-Re(z))<=L`, for any `L>=1/2`. Its complex sum H_L
keeps every critical zero and both members of each reflected pair in the
band. The enclosing finite symmetric window is `abs(Re(z))+L`, which
contains every zero in that band. Lean proves

```
Im(q(z)) <= Im(H_L(z)).
```

The local negative terms remain in H_L. A separate, weaker upper bound
retains only positive pairs whose Jensen disks contain z. Their complete
set is proved finite and has no hidden cutoff restriction.

The terminal signed local bound is
`im_logDeriv_riemannXiSpectral_le_local_paired_window`.

## Consequences for genuine Suzuki poles

At a genuine pole of `C=i*A/(A+i*A')`, the complete complex equation is
`q(z)=i`. The pole is genuine when `A(z)!=0`; shared xi/denominator zeros
remain handled by the earlier local cancellation theory.

For every local radius `L>=1/2`, Lean therefore proves

```
1 <= Im(H_L(z))  at a genuine upper carrier pole.
```

Conversely, a proved finite budget `Im(H_L(z))<1` excludes the pole and
gives the quantitative estimate

```
norm(C(z)) <= 1/(1-Im(H_L(z))).
```

That strict budget is not presumed globally. The theorem makes the
required input a finite signed local sum, including its negative terms.
The original wider symmetric-head version is also available.

Every genuine upper carrier pole lies in at least one actual Jensen disk.
In zeta coordinates, it forces a right-half zero rho satisfying

```
1/2 < Re(rho),
(Re(z)-Im(rho))^2 + Im(z)^2 < (Re(rho)-1/2)^2.
```

Outside all Jensen disks the actual carrier has `norm(C(z))<=1`, including
inside the original zero strip. This norm statement also covers literal
totalized values at xi nodes; no pointwise analytic extension is inferred
from those values.

These actual pole and carrier theorems are in
[SuzukiCarrierLocalPoleBudget.lean](../RiemannGaussian/SuzukiCarrierLocalPoleBudget.lean).

## Remaining obstruction

The active goal still requires an independent upper ceiling for

```
J_R = 2*pi*Re(Q_rho(K_R)) - Re(Q_rho(S_R)),
```

where K_R contains every genuine carrier-pole residue and S_R the two
oriented strip segments. Its limit under a hypothetical right-half zero
is `2*pi/m_rho + E_rho` with `E_rho>0`.

The new estimates control q and locate carrier poles. They do not control
the sign or size of the full mixed residue matrix. At a simple pole this
matrix still involves the complex slope `q'(c)` and both reflected test
values. Multiple poles require the existing complete Taylor-jet formula.
No simplicity, slope lower bound, separate residue sign, or cancellation
of the strip segments follows merely from the local unit budget.

Use the finite signed bounds together with the actual arithmetic and the
full coupled residues. Replacing those residues by independent absolute
values would lose the information still needed for the source ceiling.

The [signed tail and finite residue enclosures](suzuki-carrier-finite-residue-enclosures.md)
now extend this bound to actual slopes and signed weighted residues at
simple poles. The fixed-window analytic tail controls its own derivative;
inverting that slope disk retains the residue phase. The estimates above
alone still do not imply simplicity, a uniform margin, or a source ceiling.
