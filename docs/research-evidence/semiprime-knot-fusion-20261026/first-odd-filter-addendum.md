# Timeboxed follow-up: an exact discriminant filter for odd menus

26 October 2026. This tests one concrete PQ=N shortening of the Euclidean cover. It gives a safe arithmetic filter but only a constant-factor worst-case width saving for the literal first-odd family. The remaining task is a simultaneous square-discriminant filter, explicitly identified below. No general obstruction or new representation is claimed.

## A paid safe shortening

At an odd Euclidean stage, A,B are positive. For a candidate c in its acquired residue class c_i mod k, the physical sum is

    T=k c+A j+B s,

and actual factors necessarily satisfy

    T²-4ABN=(AP-BQ)²>=0,
    T>0.

Therefore replace the lower menu endpoint by the additional public bound

    c >= ceil[(ceil sqrt(4ABN)-A j-B s)/k].              (1)

Intersect this with the original open interval and the residue class; integer square root and exact floor/ceiling implement it in polynomial(log N) time per descriptor. It does not enumerate candidates. Total acquisition is still soft(k), and every true odd-stage factor point survives. Even-stage menus remain present. Swapped rows inherit the same physical-sum interval, so the shared-index/full-zero endpoint is unchanged. This is an actual safe shortening based on PQ=N, not a probable-square heuristic.

## Exact first-odd width after filtering

For the first odd stage A=g,B=1, write

    mu0=sqrt(N/k³), mu=ceil(mu0), theta=g/k.

Before filtering its c interval is (2mu*g, mu*(k+g)), sampled every k. Away from theta=1 by a fixed constant, (1) dominates the old lower endpoint for large k. The filtered number of candidates is

    mu0*(1-sqrt(theta))²+O(1).                         (2)

The bounded error includes rounding, mu-mu0<1, and (g j+s)/k²=O(1). This follows directly by subtracting the new lower bound 2sqrt(gN)/k-(g j+s)/k from the old upper bound and dividing by k.

Thus near g=k the filter can be strong, but for g in [k/4,k/2] its leading factor remains between (1-1/sqrt(2))² and 1/4. There are Theta(k) actual unit tags in that range because g=N j^-2 runs twice through one residue class modulo 6. Consequently this safely shortened literal first-odd family still has total width Omega(k*mu0)=Omega(k^(5/2)). The constant-multiplicity exponent-deduplication argument in factor-correlated-cover.md remains applicable.

This disproves only the hope that nonnegative discriminant by itself reduces these exact menus to total width soft(k²). It does not show that another subset/filter cannot do so.

## What exact squareness adds

Let the public residue/phase data for one stage be

    tau=k c_i+A j+B s,
    c=c_i+kz,
    T=tau+H z, H=k².

The native stationary congruence makes tau²-4ABN divisible by H. Put

    D0=(tau²-4ABN)/H.

The perfect-square condition is equivalent to the integer conic

    w²=D0+2tau*z+H z²,                                (3)

because T²-4ABN=H w². Actual factor recovery also checks the original divisibility and positivity conditions, so a conic root is only a candidate until those checks succeed. Every true factor supplies such a root. All coefficients and z intervals in (3) are already acquired with O(log N)-bit integers.

Thus the explicit unpaid problem is: across the softly linear list of these conics and their length-Theta(k^(3/2)) z intervals, either find a valid square point, or acquire in soft(k) time a coverage-preserving shortened union of total z width soft(k²). Testing nonnegativity was (1). Testing integer squareness for every listed z separately restores the long candidate support. The small total number of valid divisor points does not itself give an output-sensitive algorithm for locating them.

Adjacent Euclidean-stage coverage gives a possible stronger filter: an odd stage is needed only where the neighboring even-stage forms at the sign crossing are outside their short menus. For the first odd stage this gives the weaker safe bounds x>=mu and y>=mu*g from the sign-change proof. Substituting x=mu+u,y=mu*g+v with u,v>=0 into the exact quotient product yields a positive residual hyperbola. Its elementary product bound is the old upper width mu(k-g), up to the already retained residue offsets, and its AM–GM bound gives (2); no further power saving follows from those inequalities alone. To improve this route, the simultaneous conic/squareness constraint must be exploited beyond these real bounds, or a new adjacent-stage selection theorem must replace the long odd menus.

No tests were needed: the shortening and its surviving width follow from exact inequalities and the known tag distribution.
