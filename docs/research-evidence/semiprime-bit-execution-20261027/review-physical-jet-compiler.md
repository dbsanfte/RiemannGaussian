# Independent physical jet/compiler review

Disposition: PASS for the value/refinement, structural capacity and stated primitive-clock interfaces, with the copy/preprocessing qualifications below. Read-only review of final JetBits, PolynomialCodeBits and physical-jet-compiler-proof.md. No source edits, recompilation or new experiment campaign.

## Jet arithmetic

The output words are produced by actual executeOperation calls or by actual dotBits convolution loops, not by interpreting an independently computed rational coefficient and assigning it a clock. collect constructs an array of scalar reports once, then maps outputs and sums stored clocks; the latter does not rerun the scalar callbacks. decode is used only in specifications/printing. wordAt's zero extension agrees exactly with frozen coefficient lookup, and zeroWord has a legal denominator.

Addition/scaling validity requires the original word denominators to be valid and a sufficient template. The fit conditions follow from input common representations: B+C over d, CB over ed, and JBC over de. The convolution invokes the actual finite pair list of length i+1 for i<J. Its global J bound controls every suffix product/sum, irrespective of cancellation. Default zero entries also have the required common representation, without pretending their literal denominator is d. multiplyBits_correct matches every frozen convolution coefficient.

The unconditional bounded-output theorems are shape statements about fitting. They are not a substitute for the sufficient-capacity correctness theorem. A too-small width can truncate values, as the recorded negative control demonstrates. The proved common-representation conditions are sufficient to prevent this, not output-value advice supplied by the caller.

The scalar and dot clocks include the actual Boolean rational arithmetic, reductions and padding. accessCost is the explicit conservative flat-address/copy upper charge, rather than a proved compilation of Array.getD and every control instruction to a tape machine. Natural-number clock bookkeeping, constructing convolution pair lists and the full physical array/control interpretation still require their stated separate composition. The report correctly preserves that scope.

## Structural compiler capacity

PolynomialCodeBits compiles an actual finite syntax tree with ORIGINAL physical-word constants. Runtime compile has no Polynomial/denote parameter and never calls valueCode, budget or rational interpretation to obtain output coefficients. It caches both recursive compiled children once and executes their jet operation.

The structural budgets correctly clear denominators for addition: (d,B)+(e,C) is represented over de with numerator Be+Cd. Multiplication has denominator de and numerator JBC for every retained convolution coefficient. Positivity comes from original constant validity; it is not assumed for an arbitrary desired output. X and constants, including zero/negative constants, have the claimed representations. J=0 may make a multiplication numerator budget zero but only vacuous retained coefficient statements are required; denominators remain positive.

requiredWidth takes maxima over every subtree rootWidth and the ORIGINAL physical word lengths. The latter matters for leading-zero encodings: a small numeric magnitude does not imply a short physical input. rootWidth=1+size(den)+size(num) safely dominates each individual bit size, and Nat.size_le gives strict capacity <2^W. safe_of_requiredWidth therefore establishes the entire recursive Safe property from original denominators and a structural width schedule. It does not assume that computed coefficients fit. compile_initialized is a real initializer/correctness theorem, with ConstantsValid an input-wellformedness premise rather than an output oracle.

The initializer does not itself validate denominators at runtime. Nor is its preprocessing clock part of compile.clock: budget uses bitValue and natural arithmetic on potentially large structural budgets, requiredWidth recursively recomputes subtree budgets, and List.replicate constructs the template. These steps must be implemented/charged or bounded by a separate word-length-based schedule. Their bit lengths are polynomial in the literal EXPRESSION TREE size and input word width; that statement is not a bound in a much smaller shared-DAG descriptor size. Repeated budget calculations can add polynomial overhead in tree size and require their own cost proof. The report expressly leaves that integration open.

## Copies and clocks

constantBits/indeterminate materialize J report/array cells and reuse literal/input word values. They do not call a Boolean deep-copy routine on each constant word; the length-based copy charges are conservative flat-model charges, while the Lean immutable implementation can share list references. Thus wording such as “physical copies” should be read as the stated cell/copy COST MODEL, not a separately proved executed deep-copy primitive or no-sharing tape representation. This does not compromise value correctness or the upper clock envelope, and the report already distinguishes these charges from a compiled tape machine.

Internal arithmetic really executes, and compile_cost sums the child clocks exactly once. Its nodeCost is a conservative sum of leaf/add/convolution envelopes, so it bounds the applicable operation at every node without relying on a scalar callback cost oracle. The primitive complexity is polynomial in J and chosen word width per literal tree node. Acquiring original source constants, solving/binomial/packing preprocessing, computing the structural schedule/template, persistent-array/function addressing and the complete global bit/control/storage machine remain distinct.

No mathematical correction requested. The recorded positive/overflow controls support executability and the necessity of capacity guards; they are not semiprime/performance or full rate evidence. This compiler and the separate local-bit interpreter constitute actual physical arithmetic refinements, not a complete factoring bit theorem.
