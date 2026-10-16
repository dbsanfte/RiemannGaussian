# Next-target check: inverse quadratic digits and Gauss products

2026-10-15. No promising new exact acquisition identity found. This is a short source-preservation check, not a no-go theorem.

The actual identity r_j^2=4N a_j (mod m^2) means
r_j^2=4N a_j+m^2 b_j
for an integer b_j. Exponentiating gives

gamma^(r_j^2)=gamma^(4N a_j) alpha^b_j, alpha=gamma^(m^2).

The alpha factor cannot be discarded: in the hard family alpha has large order, not order one. Moreover the desired target is gamma^r_j rather than gamma^(r_j^2). Thus completing a square in the public phase digit does not itself turn the target collection into a classical quadratic Gauss sum or product.

The precise elementary character issue is that t -> gamma^t does not define an additive character on Z/m^2 unless gamma^(m^2)=1. Changing a representative t by m^2 changes the value by alpha. Ordinary complete-residue Gauss identities require a genuine character (possibly in an extension ring); they do not apply to gamma evaluated at arbitrarily chosen integer lifts of those residues. The actual full-N lifts and midpoint carries supply exactly these nontrivial alpha phases.

Reindexing by inverse tags makes the low digit range over the nonzero public field and makes the slope digit quadratic, but does not remove the higher digit phases. Retaining those phases leaves a weighted, lifted quadratic curve. An exact Fourier expansion could encode the weights, but no bound compressing their acquisition and the ensuing long product to soft O(m) follows from this representation. Any such Fourier argument must also preserve multiplicative products and hidden-field zeros; evaluating an unweighted character sum is a different output.

A potential next theorem would therefore need an exact product identity for this weighted lifted curve with its alpha cocycle retained. No such identity was derived here, and the known antipodal pair trace identity remains the only concrete source-specific product folding obtained in this investigation.
