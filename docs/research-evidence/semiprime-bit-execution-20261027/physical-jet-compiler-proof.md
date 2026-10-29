# Physical rational jet and expression execution

Two new modules only: `SemiprimeJetBits` and `SemiprimePolynomialCodeBits`. Previous sources are unchanged. Final strict, root15/all-generated and isolated-object results are recorded in the adjacent logs/manifests.

## Actual executed arithmetic

JetBits represents each coefficient by an actual signed Boolean numerator and Boolean denominator. `addBits` and `scaleBits` call `RationalBits.executeOperation` on every requested coefficient; multiplication constructs each finite convolution input and invokes the actual cached Boolean `dotBits` loop. The output arrays contain these executed words. They do not encode an independently supplied rational answer. `collect` materializes scalar reports before mapping their words and summing their clocks, so the report does not execute each scalar instruction twice.

`decode` and the rational-array specifications occur in proofs only. The zero-extended physical lookup corresponds exactly to frozen JetArray.coefficient. The refinement theorems prove low-coefficient equality to the actual frozen ArrayOps.addJet/scaleJet and JetArray.multiply, together with validity of every returned denominator. Output physical widths are proved separately.

Common integer representations derive the fitting conditions: addition uses numerator B+C over d; scaling uses CB over ed; convolution uses JBC over de. The dot-product proof controls every intermediate product and partial sum. These are inequalities in the input height bounds and the chosen template, not assumptions about a desired output word. Future callers must instantiate them from their native height derivation. Deliberately insufficient template widths really truncate; the negative execution control demonstrates that omission of the conditions is unsound.

For template width W, each scalar rational operation costs at most 20000(W+1)^3 in the inherited Boolean/cell model. Addition/scaling cost J times this plus their actual input addressing/copy charges. Multiplication is bounded by

`J*(J*(40000*(W+1)^3+4)+4+J*(access(a)+access(b)))+2J+1`.

This deliberately replaces the triangular convolution count by J². The explicit access bound is `(input.size+1)*(2W+3)`, a conservative linear scan of flat physical input storage plus one copied/default word. In particular the arithmetic bound does not assume free arbitrary rational indexing. These extra addressing/cell charges are upper bounds for the array implementation, not a formally compiled tape machine. Natural-number report bookkeeping and input-word acquisition remain outside this clock model.

## Actual expression compiler and initialization

PolynomialCodeBits compiles a finite `PolynomialCode RationalWord`. Constant payloads are original physical input words. Symbols are literal zero/one words; internal nodes call the actual bit jets. Both children are cached once; node clocks are exactly their clocks plus the executed output clock and fixed node control. `compile_refines` proves equality to every retained coefficient of the existing rational SourceCodeArrays.compile on the interpreted input expression.

Intermediate capacity is derived structurally. A constant's budget is its literal denominator/magnitude; X has budget (1,1). For children (d,B),(e,C), an addition has budget `(de,Be+Cd)` and a multiplication `(de,JBC)`. `representation_extend` justifies the addition common denominator. The proof carries output legality, widths, all coefficient representations and actual expression coefficients together.

`requiredWidth` is computed from binary sizes of these structural budgets and the lengths of the original constant words. `safe_of_requiredWidth` proves every intermediate fit. `compile_initialized` therefore requires only nonzero denominators of the ORIGINAL constant words, not supplied coefficients, a supplied output-fit oracle, or assumed intermediate arithmetic results. Its explicit template is `replicate(requiredWidth,false)`. Computing that schedule and building that template are explicitly separate from compile.clock; this is not a claim that uncharged schedule generation is free.

`compile_cost` proves the actual summed clock is at most literal syntax nodes times `nodeCost(J,W)`, where nodeCost is the sum of the explicitly proved leaf/addition/convolution bounds. This is a fixed polynomial in J,W. The code does not attach a freely chosen clock to an arbitrary output value. Structural budget bit sizes are polynomial in the expression-tree size and original constant width (products add bit lengths, sums add at most one, and each multiplication adds O(log(J+1))); the corresponding generic machine schedule/constant-acquisition proof is a remaining integration step.

## Scope and verification

This closes actual bit-backed array addition/scaling/convolution and a generic physical expression compiler. It does NOT yet acquire every physical rational constant of the original source generator: the finite integer/binomial/conditional-expectation/packing source preprocessing must be connected to the word primitives. It also does not compile the array/control implementation into a complete primitive Turing machine or prove the whole factoring bit theorem.

Controls: add/scale/convolution including zero extension; the finite expression `(1-X)^2`; the explicit computed width; a deliberately too-small width. Outputs are `[0,0,0]`, `[-1,1,0]`, `[1,-2,1,0]`; initialized compiler width 9 gives `[1,-2,1,0]`. Clock/bound control is `(268566,7920048378)`. The width-one overflow control gives `[0]`, as expected. No semiprime or performance campaign was run.

The first combined lint attempt found two missing JetReport field docstrings. These were corrected before final verification; both semantic APIs stayed unchanged. Final PASS requires terminal exit status zero and the full audit log, not its successful suffix.

Final gates after docstring repair: both modules strict EXIT0; ordinary-root plus all15 scoped linters EXIT0, full log clean; all171 generated declarations /111 theorem constants have only the standard axioms. Both independent isolated objects match their canonical objects byte for byte, with unchanged source hashes.
