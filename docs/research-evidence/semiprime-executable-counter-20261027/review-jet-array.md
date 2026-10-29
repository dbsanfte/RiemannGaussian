# Independent semantic review: cached jets and weighted support menu

**PASS within the declared algebraic/height scope.** Read-only review of `SemiprimeJetArray.lean` and `SemiprimeJetArrayHeight.lean`; exact source hashes are in `review-jet-array-sources.json`. No additional numerical examples are used.

## Cached execution and Hermite semantics

`buildInverse` has exactly one recursive prefix call, binds its result to `old`, obtains the next coefficient from `old.coefficients`, and pushes that coefficient once. `dotPrefix` never recursively invokes the inverse recurrence. Its index pair is `a[len+1] * b[n-len]`, so `nextCoefficient n+1` computes exactly `−a0⁻¹ sum_(i=1..n+1) a_i b_(n+1−i)`. `inverse_coefficient` proves this against the previously established recurrence, rather than assuming a cache/value oracle.

`convolution` includes its i=0 term separately and uses `dotPrefix` for i=1..n. At n=0, the latter prefix is empty, so the boundary is correct. `multiply_asPolynomial` proves truncated multiplication modulo X^J, including zero padding outside stored widths. `quotient_correct` connects the actual inverse and actual multiplication arrays to Hermite's `localQuotient`; it requires the normalized denominator constant 1. This matches the intended normalized local Hermite denominator. The broader total inverse recurrence alone makes no unit claim for zero constant.

`inverse_work`, `multiply_work`, and `quotient_work` attach quadratic **rational-operation and coefficient-access counts** to those actual loops. They do not count rational numerator/denominator arithmetic, index arithmetic, loop control, stack frames, persistent-array copying/allocation, or memory traffic as primitive bits. In particular these are not already Turing-machine time/space results.

## Height proof

`inverseCoeff_representation` assumes one supplied common integer denominator d>0 and numerator bound B for every normalized input coefficient below J, with a0=1. It derives, rather than assumes, an integer representation of coefficient k over d^k. With `H=J(d+B+1)+1`, its numerator is bounded by H^k. The induction explicitly raises each product to common denominator d^(n+1); no multiplying unrelated rational denominators across a sum occurs.

`dotPrefix_representation` proves the same common power denominator for **every** partial sum of len terms, not only a completed inverse coefficient. `cached_dotPrefix_heights` instantiates it with the actual cached prior inverse array and covers every len≤n+1 used while computing the next coefficient (n+1<J). Thus partial-sum cancellation is not needed for the bound. The product terms also have the explicit common-denominator representations appearing in the proof, with magnitude at most B H^n; the final negation/multiplication by a0⁻¹ is harmless in this normalized a0=1 case.

`representation_reduced_bound` correctly converts these unreduced integer representations into bounds on actual reduced rational fields. `cached_inverse_bit_lengths` supplies explicit binary-length bounds for stored coefficients. Applying `clog_succ_le_of_le_pow` to `cached_dotPrefix_heights` yields the analogous explicit bound for each partial accumulator; that combination is available although not separately named in the module. Consequently stored inverse values and partial inverse dot sums have polynomial bit length in J, log d, log B, with no assumed output bound.

Remaining obligations are important: derive the common d/B for the **actual normalized Hermite packets and source row polynomials**, preserve it through all shifted jets/global accumulator sums, instantiate the general representation lemmas on every quotient/global intermediate, and charge full execution on a primitive bit model. The final extension now proves quotient output heights as detailed below; the actual-input/whole-loop bridges remain distinct. General rational input values with individually small reduced denominators do not automatically supply a polynomial-bit common denominator; the explicit common-denominator hypothesis must be instantiated.

## Exact weighted Möbius menu: small reusable route

Pinned sources (commit in attribution):

* `OAI/Algorithms/SubexponentialSAT/BranchTree.lean:160`, `choose_le_rpow_real D r hq hD hr`: `choose(D,r) <= (4D/u)^u` for 0<u≤D and r≤u. This numerical lemma is independent of SAT arity or sparsification, although its containing module imports `SparsificationConstants`.
* `.../SqrtLog/SupportProgramCount.lean`: `count n J = sum_(j<J) choose(n,j)`, `masks_length`, `calls_le_count` and literal output-size identities. These count unweighted supports, not the actual counter's `(E,U⊆E)` pairs.
* `.../SqrtLog/CostAssemblySupport.lean`: `support_le_entropy` and `eventually_support_target` convert a supplied numerical jet-order cutoff to the old proved runtime scale. Their `J` is strict support size; our Taylor q=floor(2nR/Q), J=q+1 has supports size≤q. Using J=q instead would omit the boundary.

For the actual menu

`C_q(n) = sum_(j=0..min(q,n)) 2^j choose(n,j)`

one can prove the finite bound directly, without importing full support-program enumeration:

`C_q(n) <= (q+1) * (8n/u)^u` whenever `0<u<=n` and `q<=u`.

Indeed each `2^j<=2^u` and each binomial is bounded by the published numerical lemma, so their product is `(8n/u)^u`. Terms beyond n are zero; q=0 can be handled as C0=1 separately if using u=q. Equivalently, use `C_q<=2^q * SupportProgram.count n (q+1)` and add q to the existing logarithmic exponent. This extra factor does not change the claimed old `O(n(log log n)^2/sqrt(log n))` rate for the actual schedule, but it must appear in the formal budget.

Small proof dependency recommendation: reproduce/attribute the standalone `choose_le_rpow_real` proof over Mathlib (it uses `Nat.choose_le_pow_div`, `Real.pow_div_factorial_le_exp`, elementary rpow inequalities), then add a weighted finite-sum lemma and feed the already established exact jet cutoff into it. Alternatively extend the optional vendor with the published BranchTree closure, but the whole `CostAssemblySupport` closure is unnecessary for this one finite inequality.

For execution, use an actual streamed ternary traversal (exclude index / include index with U-bit 0 / include with U-bit 1), pruned at support budget q. Its exact count recurrence is `W(n+1,J+1)=W(n,J+1)+2W(n,J)`, with strict J and suitable empty-budget/base cases. This directly enumerates the menu with depth n and O(n Cq) nodes/bit work per emitted record. The published `masks` function returns a whole list; its length theorem alone is not a streaming-space proof. A nested streamed support generator plus a 2^j-bit-choice generator is another correct small implementation. Neither route needs an arbitrary-support oracle or the full SAT endpoint.


## Final extension review (updated source)

**PASS.** `representation_add` preserves a common d and adds literal numerator bounds; `representation_mul` multiplies denominators/bounds; `representation_sum` sums integer numerators over one fixed denominator. None requires the desired reduced output height as a premise. `cached_inverse_common_representation` genuinely pads coefficient k from d^k to d^J by multiplying its integer numerator by d^(J−k); the envelope H^J remains valid because d≤H. This provides one common denominator for every retained cached inverse coefficient, rather than merely separate reduced-denominator bounds.

`multiply_representation` uses that common denominator and the actual convolution identity: coefficient k has k+1≤J summands, each over d*e, giving numerator bound J*B*C. `quotient_heights` instantiates this on the actual multiply-after-inverse arrays and proves output denominator ≤dH*dL^J and numerator ≤J*BH*(J(dL+BL+1)+1)^J. Positive dH,dL and normalized denominator constant 1 are explicit. Thus its logarithmic output heights are polynomial in J and the supplied input bit heights. The same common-denominator sum lemma also bounds an arbitrary partial convolution sum; the final code does not separately export a tracked-all-partial-multiplication theorem, so that small execution attachment should not be silently described as already named/proved. No cache oracle or assumed desired output bound appears.

The refreshed hash JSON pins the final JetArrayHeight extension. Strict/audit logs observed PASS (29 declarations, 27 theorem constants); this review is semantic and does not replace those compiler gates. The still necessary bridge is constructing dH,dL,BH,BL from actual Hermite/source packets and charging arithmetic/reduction/index/allocation and all global loops in the primitive model.
