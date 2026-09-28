# P082: theorem and literature correspondence

Common definitions (namespace `ACRZeroDivisors`): a `Reaction n` has source and
target exponent vectors in `ℕ^n` and a rational rate. `Bimolecular r` means
source and target molecularity at most 2 and `0 < rate`. `field rs x i` is the
real mass-action field. `steadyIdeal rs` is the ideal of `ℝ[x]` spanned by the
literal polynomial field components, and `rationalSteadyIdeal rs` is the same
over `ℚ`; neither is saturated, radicalized or extended by conservation laws.
`PositiveSteady rs x` means all `x i > 0` and `field rs x = 0`.
`NonvacuousACR rs i α` means a positive steady state exists and every positive
steady state has `x i = α`. The coordinate-candidate predicates
(`CoordinateCandidate`, `CoordinateCandidate4`, `SpeciesCoordinateCandidate`)
say that `X i - C α` lies in the real ideal or annihilates some element outside
it. This is the manuscript's set `Z_i` and condition (13) of the source.

## Selected declarations

| Declaration | Exact formal content | Manuscript | Evidence |
|---|---|---|---|
| `ACRZeroDivisors.question313_necessity_counterexample` | For the literal five-reaction network `A+B→2B, B→A, B→C, A+C→2C` (rate 1) and `C→A` (rate 3), species `A = x 0`: every reaction is `Bimolecular`, `NonvacuousACR necessityNetwork 0 2` holds, and `¬ ∃! α, 0 < α ∧ CoordinateCandidate (steadyIdeal necessityNetwork) α`. | Proposition 3.1 (the formal statement omits the full classification `Z_A = {2,3}`) | Recorded Comparator and three-kernel acceptance; see verification evidence. |
| `ACRZeroDivisors.question313_sufficiency_counterexample` | For the literal seven-reaction network `2A→A+C, C→A+D, D→A+B, A+B→B, B→A+B, A→∅` (rate 1) and `2B→∅` (rate 1/2), species `A = x 0`: every reaction is `Bimolecular`, a positive steady state exists, there is a unique `α > 0` with `CoordinateCandidate4 (steadyIdeal sufficiencyNetwork) α`, and `¬ ∃ α, NonvacuousACR sufficiencyNetwork 0 α`. | Proposition 3.2 | Recorded Comparator and three-kernel acceptance; see verification evidence. |
| `ACRZeroDivisors.OrderWitness.unrestricted_order_counterexample` | For exponents `(i,j,k)` of `u = x 0`, `v = x 1`, `t = x 2`, `MixedLT` compares `i+j`, then `k`, then `i`. It is a conjunction: (1) `AdmissibleEliminationOrder` (well-founded, irreflexive, transitive, total, translation-invariant, nothing below `0`, and any polynomial whose leading exponent has zero `z`-degree is pure in `t`); (2) `ReducedBasisCertificate`: the rational steady ideal of `T+U→T, V→U+V, U→U+V, T+V→T` (rate 1) equals `⟨u²−v², ut−v, vt−u⟩`, with those leading exponents, monic leaders, leading-ideal cover and reducedness; (3) all reactions are bimolecular; (4) `NonvacuousACR witnessNetwork 2 1`; (5) `X 2 − 1` is not in the real ideal but annihilates an element outside it; (6) `¬ AlgorithmCandidates {b1,b2,b3} 1`. `AlgorithmCandidates` returns the positive roots of the pure-`t` basis elements if any exist, and otherwise the positive roots of the `z`-leading coefficients in `ℚ[t]` for the graded order restricted to `z = (u,v)`. | Proposition 4.1 | Recorded Comparator and three-kernel acceptance; see verification evidence. |
| `ACRZeroDivisors.mass_action_block_algorithm_complete` | For any `n`, types `σ` and finite `ι`, reactions `rs` with arbitrary rational rates, a bijection `e : Fin n ≃ Option σ` (`t` is species `e.symm none`), monomial orders `full` on `Option σ` and `z` on `σ` with `BlockCompatible full z` (the `full` order is monotone in the `z`-part, i.e. a block order comparing `z` first), and `b : ι → ℚ[Option σ]` with every `b i ≠ 0`, `hcover` (every nonzero element of the renamed rational steady ideal has leading exponent divisible by that of some `b i`) and `hgen` (each `b i` lies in that ideal); for every real `a` with `NonvacuousACR rs (e.symm none) a` and `SpeciesCoordinateCandidate (steadyIdeal rs) (e.symm none) a`, it concludes `BlockAlgorithmCandidates z b a`: `0 < a` and either a chosen univariate entry of `b` vanishes at `a`, or, when there is none, some `z`-leading coefficient of some `b i` vanishes at `a`. | Theorem 5.1 and Corollary 5.2 (the corollary's zero-divisor ACR form over `ℝ`) | Recorded Comparator and three-kernel acceptance; see verification evidence. |

The necessity counterexample and the order counterexample are in `NecessityIdeal`
and `OrderMain`; the sufficiency counterexample and completeness theorem are in
`SufficiencyCounterexample` and `MassActionCompleteness`. `Registry/P082/Solution.lean`
imports these four modules.

## Literature correspondence

L. D. García Puente, E. Gross, H. A. Harrington, M. D. Johnston, N. Meshkat,
M. Pérez Millán and A. Shiu, *Absolute concentration robustness: algebra and
geometry*, J. Symbolic Comput. 128 (2025) 102398,
[doi:10.1016/j.jsc.2024.102398](https://doi.org/10.1016/j.jsc.2024.102398),
[arXiv:2401.00078v3](https://arxiv.org/html/2401.00078v3). The numbered question, conjecture and definitions were checked against this primary version.

- Question 3.13 asks whether, for at most bimolecular networks, uniqueness of
  the positive zero-divisor value (condition (13)) is necessary or sufficient
  for ACR. The first two declarations answer no in both directions.
- Conjecture 4.7 states that, for rational rate constants, Algorithm 1 (a
  reduced Gröbner basis for an elimination order, then roots of the univariate
  element or of the `z`-leading coefficients) returns every zero-divisor ACR
  value. The third declaration refutes this for an order admitted by the
  source's definition of an elimination order that is not a block order. The
  fourth proves completeness when the order is a block order, for any Gröbner
  basis given by the cover and membership hypotheses.

A returned candidate is not thereby an ACR value: the completeness theorem is
the implication ACR value and zero-divisor value ⇒ algorithmic candidate, not
its converse. The necessity network already returns the non-ACR value 3.

## Evidence boundary

- The completeness theorem takes the Gröbner-basis property as hypotheses
  (`hcover`, `hgen`, `BlockCompatible`). It does not compute a basis, isolate
  roots, bound complexity or decide ACR. The candidate set is an exact root-set
  specification. The strengthened theorem additionally requires every basis
  entry to be nonzero, ruling out a vacuous leading-cover witness built from a
  zero entry. The worked application in `ApplicabilityExample.lean` instantiates
  all hypotheses with the nonzero basis `X_B (1 - X_A)` for `A+B→2B, B→A`
  and proves that the algorithm output is exactly the ACR value `1`; this example
  is imported by the Solution but is not a selected Comparator declaration.
- The formal completeness statement covers real values `a`. The manuscript's
  extension-field form of Theorem 5.1 and Corollary 5.2(b) for arbitrary `L/ℚ`
  is not a selected declaration. Rates in the fourth declaration are arbitrary
  rationals; positivity is not assumed.
- The order counterexample refutes Conjecture 4.7 only under the unrestricted
  reading of "elimination order". It does not affect lexicographic or product
  orders.
- Not selected: regular-point coverage (Theorem 6.2), the quantitative bounds,
  the reactor and EnvZ/OmpR analyses and the release constructions of the
  manuscript. Several of these are conventional proofs by the manuscript's own
  account.

## Order correspondence

Section 4.1 defines an elimination order by the requirement that a polynomial with a pure-t leading monomial be pure in t. MixedLT satisfies this requirement along with the monomial-order axioms. Restricting MixedLT to t-degree zero compares total (u,v)-degree and then u-degree; this is exactly zKey, used by leadingCoefficientZ. Consequently the counterexample uses the same restricted-coefficient convention as Algorithm 1, not a different output rule. In the completeness theorem, BlockCompatible compares the entire z exponent before the t exponent, which is the product-order case described in Section 4.1. Nonzero basis entries, membership and leading cover are explicit assumptions.

## Verification evidence

The recorded run on Lean 4.35.0-rc2 passed exact statement comparison and con-ron, NanoDa and the Lean default kernel for all four declarations. Receipt, logs and source hashes are in `preparation/verification/P082-release-candidate-run/`. The only permitted axioms are `propext`, `Quot.sound` and `Classical.choice`.
