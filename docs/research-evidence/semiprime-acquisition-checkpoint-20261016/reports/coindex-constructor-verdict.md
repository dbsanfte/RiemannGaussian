# Public continued-fraction coindex construction: unresolved

No separated exponent GAPs meeting the requested soft O(m) actual-volume and descriptor budget were constructed. In particular the safe branch a=b=2 remains uncovered by a proved construction. This note records one explicit candidate calculation, not a new obstruction theorem or a conditional result promoted to a solution.

## Concrete public candidate

For a public rational/integer center x>0, choose positive integers u,v by continued fractions so that

    1 <= u <= H,     |v-uN/x^2| <= 1/H.

The elementary rational-approximation guarantee also follows by pigeonholing H+1 fractional multiples of N/x^2. Form the entirely public integer

    c_x = uN+v-floor(uN/x+vx).

If the hidden smaller factor P is within W of x and P>=x/2, set

    i = uQ+vP-floor(uN/x+vx).

Then the exact identities are

    c_x-i = (P-1)(uQ-v) = a d (uQ-v),

    uN/P+vP-(uN/x+vx)
      = (P-x)(v-uN/x^2) + uN(P-x)^2/(P x^2).

Consequently d divides an individual crossdifference, and

    -W/H <= i <= W/H + 2HN W^2/x^3 + 1.

Thus a public mesh of centers provides an unconditional arithmetic cover using one common short integer interval and the public c_x anchors. This calculation does not require a,b,d,e or the witness P as algorithm inputs. The anchors are large positive integers in the present asymptotic regime; hull separation can also be checked directly before using them.

On the balanced scale x~m^3, N~m^6, the explicit choices H~m^(2/3), W~m^(5/3) give an O(m)-length common interval and O(m^(4/3)) public anchors per bounded-ratio window. They improve on enumerating m^2 Lehman starts but still exceed the requested O~(m) budget, and the varying c_x have not been embedded into a GAP of the required actual box volume. This is not claimed as a new factoring exponent or as an improvement over the known Harvey construction.

## What the actual coindex equation contributes

The identity N=abde+ad+be+1 leaves the same approximation target uQ+vP in the displayed witness. If a were known, the equality c_x=i modulo a would allow dividing both integers by a using floors:

    floor(c_x/a)-floor(i/a) = d(uQ-v).

This shrinks the common interval by a, but produces no power saving in the mandatory a=b=2 branch. Neither the coindex equation nor gcd(d,e)=1 supplied a public approximation to P/Q or recoverable Bezout coefficients for d,e in this attempt. Quadratic reciprocity gives character information in the safe-prime branch; I obtained no short integer divisibility witness from it.

The precise unresolved step for this candidate is to select or represent enough of these public varying anchors in separated GAPs of total actual box volume and descriptor bits O~(m), while preserving an anchor belonging to the hidden P-window and an individual d- or e-divisible difference. No such selection, GAP representation, or coverage proof was found. The earlier secondary-order orbit and smooth projection were not used.

Scratch only; no repository edits, builds, backend lemma changes, broad searches, or subagents.
