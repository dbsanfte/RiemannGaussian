# Fixed polynomial setup-resource closure

NEW `SemiprimeSetupPolynomialEnvelope` defines the diagonal `polynomialEnvelope S := FullSetupBudget.setupBudget S S S S S S S S S`. `setupBudget_le_envelope` proves domination whenever the actual dimensions n,F,M,r,Q,R,B,D,A are each at most S. The proof explicitly unfolds every scalar budget dependency, including finite enumeration, searched source, universal numerator polynomial, raw constraints, physical selector and its derived temporary bit widths; the remaining operations are additions, multiplications and fixed powers. `polynomialEnvelope_mono` is also proved.

The width is recomputed from B,Q,R. The exponentially larger measurement magnitude is not a resource dimension, and no state/minor/Fits advice or precomputed setup answer is supplied. This is a numerical closure of the existing mixed setup ledger, not a literal whole-machine-bit clock. The prior setup_work_bound theorem supplies its actual-execution link; this module does not redefine execution.

Built only after qholonomic confirmed the actual final FullSetupBudget canonical object was ready. Final strict canonical compile, root fifteen-linter and every-generated-declaration standard-only axiom audit PASS: 32 generated declarations,31 theorem constants (3 user declarations). Source API is frozen. No frozen source was edited.
