# Independent review of physical local interpolation

Disposition: PASS for the stated component refinement and clock. Root read the
three frozen local-bit modules and their complete audit/build reports. This is
independent of their author's proof construction. Source hashes are recorded
in `review-local-physical-hashes.json`.

The runtime contains the intended multilinear recursion: it evaluates both
restricted Boolean branches on the tail ports, caches those outputs, and
computes `(1-port)*lo + port*hi` through physical rational-word scaling,
addition and convolution. Leaf values are actual callback words with literal
denominator one; neither an integer answer encoder nor a rational output oracle
appears in the runtime.

The main correctness proof carries the actual restricted callbacks through
both recursive branches. Its capacity premise is a numeric expression derived
from the initial common denominator, port coefficient bound, retained degree
and local arity. Child denominators, individual convolution products and sums,
and the final addition are justified from those same representations. No
premise asserts that the desired child/output value already fits. The public
width `(2*b+3)*(w+1)+3` follows from the dyadic input bounds, with rounding and
strict-capacity slack retained.

Physical boundedness alone would also hold for a clipped, incorrect result;
the modules correctly keep it separate from arithmetic correctness. Conversely,
the correctness theorem need not constrain how many leading zero bits were in
an input, while the clock theorem explicitly bounds those actual physical
lengths and the entry callback clock. These two distinct premise sets must both
be established by the eventual source/entry adapter.

The local clock charges both recursive calls, every executed arithmetic stage,
literal-one arrays, inherited flat jet access charges, and each leaf callback.
The result is at most `2^w*(E+(w+1)*nodeBudget(J,Wbits))`. This bounds that
component's declared arithmetic/cell ledger. Building or traversing arbitrary
function-encoded port/assignment closures, producing the physical entry words,
computing clock reports themselves, and composing everything into a physical
machine remain outside the theorem. The author's scope report records these
limits accurately. No complete factoring time or storage theorem follows yet.

No mathematical correction requested. The next useful connector is physical
source-Horner/corrected-port acquisition, together with its proved common
representation, followed by the outer group/fibre/support/Hermite run.
