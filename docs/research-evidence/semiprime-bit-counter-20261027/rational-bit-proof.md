# Actual rational word operations and dot products

`SemiprimeRationalBits.lean` represents a rational by actual signed numerator
bits and unsigned denominator bits. Its value in Q is a specification. Reduction
runs denominator scanning, the existing binary GCD and exact division routines;
theorems identify the reduced fields with the canonical numerator and positive
denominator. A zero denominator is explicitly totalized to the zero rational.

Raw addition and multiplication use signed integer cross-products and ordinary
denominator products. Negation changes the sign; inversion swaps numerator and
denominator data before reduction. The total inverse at zero agrees with Q's
totalized inverse and is not a nonzero-unit certificate. Each operation reduces
and copies into a physical template. The output-height premise needed for that
copy is derived by `fits_of_representation` from an unreduced common denominator
and numerator bound. It is not a computed rational-value oracle.

For input widths and template length at most W, `executeOperation_cost` bounds
the report clock by `20000*(W+1)^3`, including larger unreduced temporaries,
normalization and copying. The clock measures the documented Boolean/list-cell
backend model. It does not claim a complete finite Turing-machine compilation.

`SemiprimeDotBits.lean` recursively computes one suffix once, then one product
and one addition. From valid input representations over common denominators d
and e, it derives each product and partial-sum representation over the SAME de.
No desired intermediate Fits predicate is assumed. The result numerator bound
is `length*B*C`; clock is at most `length*(40000*(W+1)^3+4)+4`.

These routines accept actual input words. Acquiring pair lists from the counter,
matching cached-array/controller states, and charging whole-program data
movement are separate. The independent review records those limits explicitly.
