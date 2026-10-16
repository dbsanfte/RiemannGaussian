# Exact logspace interface and time scope

Official HEAD1581d4c source inspected, no build or full proof certification. Equality.lean theorem exact_logarithmic_space_derandomization asserts L=RL and RL=BPL. Its BPL_subset_L output is membership in L, not a bound preserving the randomized algorithm's exponent or running time.

Deterministic.lean defines L using existence of a deterministic LogSpace machine deciding the language. RL/BPL additionally carry an existential polynomialClock c k on input WORD LENGTH. Deterministic finite-configuration counting subsequently supplies some polynomial halting bound. Its explicit exponent includes h+w+2*c*w (line505), depending on the constructed machine and logspace constant, not the original time exponent. The final equality theorem does not export a quantitative relationship between randomized and deterministic clocks.

Factoring has binary input length ell=log N. No randomized polynomial-time O(log ell)-space factoring algorithm has been supplied here. An N^(1/6)-time process is exponential in ell and is not automatically a BPL witness under this definition. Padding to represent such a clock changes input length, space accounting, and the resulting polynomial time; the unspecified exponent does not preserve N^(1/6). Decision-to-search/output costs would also require a separate paid reduction. Thus the theorem interface alone gives no classical sixth-rate factoring algorithm and no replacement for the unpaid whole-family q-query. This does not exclude a new quantitative reduction proved separately.

Primary source paths: lean/OAI/Computability/Logspace/Equality.lean and Deterministic.lean at https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a .
