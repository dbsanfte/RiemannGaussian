# Attached original setup and full word-node cost join — completed

NEW `SemiprimeWordPacketSetupBudget` leaves prior sources/runtime unchanged. It proves the ACTUAL new WordPacketSetupCounter report is old ACTUAL setupWork + ACTUAL extra source encodingWork +1 + new ACTUAL WordPacketCounter.nativeWork. Only the unchanged setup arithmetic is reused; old/new native clocks are not equated.

`encodingWork_le` binds the original acquired source cache encoder. `nativeWork_le` derives every physical source word guard internally from the original constructor assumptions: common representation/sourceBits, exact R+1 row size, master inputBits width and actual incidence-scan getter budget. The entire getter family is bounded by M*n*(2M+6), with M=sum arities. Original entry magnitude length≤1 supplies the physical group-width guard. No source/shift/encoded-word answer, intermediate/output Fits, group-cost budget or native-count-answer advice is a premise.

The final `count_work` combines the proved setupBudget and encodingBudget with the new WordPacketCounterBudget.count_work. The new native reductionBudget contains ACTUAL nodeWidth, nodeControl, complete physical head/summary/support/node costs, one decode per completed node and scalar Hermite. Actual arity is an explicit argument because nodeWidth depends on total incidence computed from it; this is not replaced by an unrelated arity answer.

Remaining hypotheses are original r≥2/occurrence/interpolation guards, actual physical-design head/measurement caps H/cap, original local arity≤w, and actual original entry clock≤E / magnitude length≤1. The result is an attached actual-counter cost inequality, not an independent tally or arbitrary count-budget premise. The public runtime itself still supplies no counter answers.

Scope: source producer scalar arithmetic/canonical extraction, cached integer metadata tests, final scalar Hermite/floor/fallback and address/control refinements remain separate from the complete original-input primitive-bit clock. This module does not automatically transfer the earlier controller's public subpower theorem to the changed runtime. New global-rate composition remains a separate task.

Strict / ordinary-root15 / every generated transitive standard-three-axiom gates PASS: 13 declarations, nine theorem constants. Isolated object byte-identical canonical. Pins: word-packet-setup-budget-verification.json. No old files or sealed packet edited; no finite factoring campaign.
