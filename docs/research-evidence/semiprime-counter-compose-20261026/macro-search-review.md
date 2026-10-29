# Independent review: canonical macro arrays and actual-counter prefix search

26 October 2026. **PASS at the stated finite algebraic and search-correctness scope.** Reviewed final stable `SemiprimeMacroBitNetwork.lean` and `SemiprimeCounterSearch.lean`, plus the invoked CountRecovery definitions, against frozen `factor_network.py` / `shared_counter.py` / `factor_solver.py`. This supplements `boolean-jet-review.md`; no owned source was changed. Root performs combined compilation and all-declaration audits.

## Macro arrays

The three actual stage arrays use the code's convention: first input slot j1+r*j2 and root w^r; a twiddle w^(j1*k2); second root w^t; flattened output k2+t*k1. `macro_valid_output` proves the flat DFT identity from these stage equations and the period w^(rt)=1. The Fin product equivalence in `flatOutput` uses exactly this flattening, not its transpose.

Every stored stage word is a literal (n+1)-bit value with an explicit canonical bound below M=2^n+1. `residueWord` constructs the canonical representative and fits it in that physical width. `residueValue_injective` uses canonical integer uniqueness, so equality in the composite ring does not introduce extra bit extensions. `macro_valid_unique` fixes first-stage values, then twiddles, then second-stage values; the complete arrays, not only the final DFT outputs, are unique.

`macro_extension_count` is a legitimate zero/one count-preservation statement for any downstream predicate on the final array. It does not assume the downstream count or offer a transform oracle. The predicate is evaluated on the explicitly built transform output; acquiring downstream values cheaply remains separate.

The inverse root is the public power 4^(n-1), with proved inverse and period. `macro_valid_inverse` and `flatOutput_inverse` multiply by the actual transform length n and derive the normalized reflected Fourier equation at k=0 and k>0 with the correct `if k=0 then 0 else n-k`. A length normalizer exists by the proved unit-length theorem in the actual ring. There is no assumption that the modulus is prime or that field inversion is available. An executable polynomial-cost modular inverse still belongs to the machine/cost connection.

## Flags and exact signal accounting

`OrValid` has the exact recursive output-list shape and determines one output per non-initial input flag. Its unique extension and terminal-value theorems are correct also for an empty tail. `digit_or_nontrivial` and `actual_input_flag` derive the low-digit>=2 / high-digit!=0 sequential OR test for the ordinary radix value. This removes the earlier whole-operand flag formula as a *mathematical* obstacle to local decomposition; it does not yet construct the entire local graph.

The tagged word family counts two n-word input arrays, 3 stages in each of 3 transforms, n products, and n+1 carries: 13n+1 uniform-width words. The flag family counts 2d digit flags and 2(d-1) OR outputs. Hence the formal count `(13n+1)(n+1)+4d-2` and its equality-subdivision double agree with the actual code's previously audited signal count.

In particular, the code allocates **n+1 physical bits** even for carry words and separately enforces carry<2^n. The simpler BooleanNetwork relation uses n-bit carries. A final graph bridge must identify these by unique zero-high-bit padding; no count equivalence between the two whole graphs is claimed by the current signal-cardinality theorems.

The displayed arithmetic arities match the code: 2t words for a first-axis DFT, 2 words for a twiddle scale, 2r words for a second-axis DFT, and 3 words for a product or integer carry. They are arity calculations for named vertex kinds. A complete producer/consumer incidence map, port uniqueness, exact occurrence two, balanced-axis parameter choice and global small-scope Boolean graph correctness do not follow merely from the tagged cardinalities. The module explicitly retains this limit; no correction is requested.

## Prefix search uses the same counter

`Problem` provides original arities/tables/coordinates, coordinate coverage, bounded-degree/restoring rows and node certificates. It does not contain a desired count, an arbitrary correct counting oracle, or a promised accepting assignment. `prefixTable` keeps the same factor type, arities and coordinate map while checking every owned occurrence of each fixed bit. Coverage makes this exactly the original predicate restricted to those bit values. Contradictory prefixes reject; repeated searched indices remain semantically safe.

The formal every-occurrence policy is stronger syntactically than Python's one-existing-host policy, but they impose the same bit constraint on a global assignment. No extra unary factor, variable or scope is introduced. The layout/degree/node data is independent of local table contents and is literally reused by `prefixCounter` for every prefix.

`prefixCounter_eq_accepted` derives correctness from `counterValue_eq_original`, the actual product of zero/one local entries, and the proved prefix equivalence. It discharges the generic CountRecovery hcount premise, rather than exposing that premise as a new oracle assumption. `prefixCount` applies Nat.floor only after the rational result is proved equal to the natural accepted count; this is not an approximation, an assumed integrality readout or a way to hide a negative result.

`counterSearch` calls that actual prefix counter once initially and once for each requested zero-child branch. The proof keeps a nonempty full-prefix acceptance set, so all returned bits belong to **one** original accepting assignment. It is not merely a collection of individually extendible bits. The empty result is equivalent to no original accepting assignment; the query bound is at most the requested list length+1. Empty and repeated index lists cause no logical loophole.

This is a mathematical search attached to the finite counter expression. It does not yet prove the streamed primitive implementation/cost of those calls, select/decode the specific factor input bits in the final macro graph, or attach the complete factoring/resource theorem. Those boundaries are explicit and compatible with the earlier code audit.

## Final review disposition and pins

No substantive normalization, indexing, multiplicity, flag, count-oracle or prefix-scope error was found in the reviewed sources. `network-search-review-source-hashes.json` captures the four stable main sources: BooleanNetwork, JetRecurrence, MacroBitNetwork and CounterSearch. The MacroFermat support source is pinned separately in the earlier Boolean/Jet record. Tail's exact adapted source and Apache-2.0 attribution/provenance are recorded in `tail-external-source-provenance.json`, `tail-verification.json`, and `tail-proof.md`; frozen baseline files remain untouched.
