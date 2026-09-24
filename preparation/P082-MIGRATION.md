# P082 target-toolchain migration

The four selected claims remain in scope. Statement compilation on Lean
4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55 exposed a genuine
API change, not an absent import or a mathematical counterexample.

The target `MvPolynomial` uses the wrapped additive monoid algebra. Its
coefficient accessor is `p.coeff e`; old `MvPolynomial.coeff e p` references no
longer elaborate. A polynomial is no longer definitionally the underlying
`Finsupp`, so bare Finsupp linear maps cannot be used as polynomial linear maps.

Failures found in the original Challenge:

- `OrderWitness.IsLeading` and `ReducedBasisCertificate`: old coefficient access.
- `OrderWitness.tCoefficient`: `Finsupp.linearCombination` has the wrong domain.

Prepared source-copy adaptations are recorded with before/after hashes in
`p082-polynomial-migration.json`:

- Polynomial-first coefficient access in seven affected source files.
- `tCoefficient` composed with `AddMonoidAlgebra.coeffLinearEquiv`.
- `normalForm` expressed using `AddMonoidAlgebra.mapDomainLinearMap`, with its
  monomial lemma adapted to that map's standard theorem.
- `coefficientProjection` transported between the two coefficient spaces.

The Challenge is regenerated from these same definitions. Source proof
verification remains pending; coefficient lemma rewrites and other API changes
may still need adjustment when the Solution is built.

Migration must preserve coefficient values, support, monomial order, ideal
membership, and the four selected theorem types. Comparator must verify the
Challenge/Solution correspondence. Compilation of the Challenge alone does not
validate the ported proofs.

No compatibility axioms or weakened replacement claims are permitted. The
original source snapshot remains recorded in `source-inventory.json`. Historical
4.30 receipts remain historical, not target-toolchain verification.

## Static reconciliation, 2026-09-24

The current canonical `<research workspace>/proofs/ACRZeroDivisors/` tree and
this repository's `proofs/ACRZeroDivisors/` tree have the same 41 module names.
Thirty-four modules are byte-identical. The seven differences are exactly the
seven files listed in `p082-polynomial-migration.json`; each recorded
`before_sha256` matches the current canonical source and each `after_sha256`
matches the current submission copy. No unrecorded source divergence was found.

The changed lines have three forms:

1. Old `coeff e p` notation becomes the target polynomial's `(p).coeff e`.
2. A Finsupp coefficient linear map is composed with
   `AddMonoidAlgebra.coeffLinearEquiv` to act on wrapped polynomials;
   `normalForm` uses `AddMonoidAlgebra.mapDomainLinearMap` in place of the old
   Finsupp-domain map.
3. Statements inside `OrderMain`, `OrderNormalForm` and
   `OrderReducedBasis` use the new coefficient accessor. The intended
   mathematical coefficient and monomial-order claims are unchanged, but
   their elaborated target meaning and proofs remain unchecked.

The textual theorem headers of all four selected declarations match the
canonical research headers exactly:

| Declaration | Fixed claim boundary |
|---|---|
| `ACRZeroDivisors.question313_necessity_counterexample` | A bimolecular network with nonvacuous ACR but without a unique positive coordinate candidate. |
| `ACRZeroDivisors.question313_sufficiency_counterexample` | A bimolecular network with a positive steady state and a unique positive coordinate candidate, yet without nonvacuous ACR. |
| `ACRZeroDivisors.OrderWitness.unrestricted_order_counterexample` | An admissible elimination order and reduced-basis witness, with ACR and a zero divisor, for which the unrestricted candidate algorithm misses the value. Its `ReducedBasisCertificate` includes adapted coefficient access, so textual header equality alone is insufficient to certify target semantic equality. |
| `ACRZeroDivisors.mass_action_block_algorithm_complete` | For a rational-rate mass-action source, assumes block compatibility, leading cover, basis membership, nonvacuous ACR and a coordinate candidate; concludes the block algorithm reports that candidate. It is not an unconditional ACR decision procedure. |

The target Challenge's recorded statement-only pass does not compile the
ported Solution or compare these elaborated declarations. The next authorized
verification must use this exact seven-file snapshot and the four selected
Comparator names; no research-side mathematics change is indicated by the
static comparison. No Lean was run for this reconciliation.
