import Examples.Precompiles.Modexp.MultiLimbClzCaller
import Examples.Precompiles.Modexp.MultiLimbClzSemantic

/-!
# Deployed leading-zero helper contract

Compatibility aggregation module for the exact caller/execution contracts and the pure arithmetic
semantics.  The implementation is split across stage and prefix modules so Lean kernel-checks each
generated trace segment independently; the split does not change the bytecode path, state, steps,
or exact gas expressions.
-/
