# P082: Zero-divisor methods for absolute concentration robustness

Author: Michael Mislan.

Literature problem numbers: 22, 23.

For mass-action networks whose complexes have at most two molecules, uniqueness
of a positive zero-divisor value is neither necessary nor sufficient for
absolute concentration robustness (ACR). Explicit networks show ACR with two
such values, and a unique such value without ACR. For rational rates, the
Gröbner-basis candidate algorithm can miss a zero-divisor ACR value under an
elimination order that is not a block order. Under a block order, with a family
of ideal elements whose leading monomials cover the ideal's, every real value
that is both a nonvacuous ACR value and a zero-divisor value is returned. A
returned candidate need not be an ACR value.

[Companion manuscript](../../papers/P082/paper.pdf) · [Metadata](formalization.yaml) · [Readiness](readiness.json) · [Claim-to-evidence](CLAIM-EVIDENCE.md)

## Candidate declarations for selection review

These are an inventory, not a claim that every declaration will be registered.

- `ACRZeroDivisors.question313_necessity_counterexample`
- `ACRZeroDivisors.question313_sufficiency_counterexample`
- `ACRZeroDivisors.OrderWitness.unrestricted_order_counterexample`
- `ACRZeroDivisors.mass_action_block_algorithm_complete`

## Statement draft

[Challenge](../../Registry/P082/Challenge.lean) · [Solution](../../Registry/P082/Solution.lean) · [Comparator](comparator.json)

The strengthened Challenge, Solution and worked applicability example compiled
locally before the later shared-`ChallengeDefinitions` refactor. The current
foundation candidate has not been compiled or compared, and no full kernel
receipt exists. The selected declarations are:

- `ACRZeroDivisors.question313_necessity_counterexample`
- `ACRZeroDivisors.question313_sufficiency_counterexample`
- `ACRZeroDivisors.OrderWitness.unrestricted_order_counterexample`
- `ACRZeroDivisors.mass_action_block_algorithm_complete`

## Companion-paper scope

The manuscript's formal-scope table (Section "Formal verification and
reproducibility") separates compiled algebra from conventional geometric and
dynamical arguments. The registry selection is the four declarations above,
not the regular-point, quantitative, reactor or release results. Historical
receipts authenticate the original source baseline. Seven polynomial-API
adaptations and the newer shared-definition refactor are prepared but not
fully checked on the target toolchain (see `preparation/P082-MIGRATION.md` and
`preparation/repairs/2026-09-25/FOUNDATION-P082.json` from the repository root).
The completeness theorem now requires every basis entry to be nonzero. The
Solution also imports a worked two-reaction application whose nonzero basis is
`X_B(1-X_A)` and whose algorithm output is exactly the ACR value `1`; that
example is not a selected declaration.
