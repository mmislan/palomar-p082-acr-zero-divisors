module

public import proofs.ACRZeroDivisors.ChallengeDefinitions
public import proofs.ACRZeroDivisors.OrderCounterexample
public import proofs.ACRZeroDivisors.OrderReducedBasis

@[expose] public section

namespace ACRZeroDivisors.OrderWitness
open MvPolynomial

theorem mixed_order_admissible : AdmissibleEliminationOrder := by
  refine ⟨mixed_wellFounded,mixed_irrefl,fun _ _ _ => mixed_trans,
    mixed_trichotomy,mixed_add,?_,order_elimination_property⟩
  intro e
  simp [MixedLT,zDegree]

theorem coefficient_order_is_restriction (e f : Exponent) (he : e 2=0) (hf : f 2=0) :
    MixedLT e f ↔ zKey e < zKey f := by
  simp [MixedLT,zKey,Prod.Lex.toLex_lt_toLex,he,hf]

theorem witness_reduced_basis : ReducedBasisCertificate (rationalSteadyIdeal witnessNetwork) := by
  rw [ReducedBasisCertificate,witness_rational_ideal]
  exact ⟨rfl,b1_leading,b2_leading,b3_leading,basis_leaders_monic,basis_groebner_property,
    fun e he hne => standard_no_divisor e (basis_tails_standard.1 e he hne),
    fun e he hne => standard_no_divisor e (basis_tails_standard.2.1 e he hne),
    fun e he hne => standard_no_divisor e (basis_tails_standard.2.2 e he hne),
    basis_leaders_antichain⟩

theorem unrestricted_order_counterexample :
    AdmissibleEliminationOrder ∧
    ReducedBasisCertificate (rationalSteadyIdeal witnessNetwork) ∧
    (∀ r ∈ witnessNetwork, Bimolecular r) ∧
    NonvacuousACR witnessNetwork 2 1 ∧
    ((X 2-1 : Poly3) ∉ steadyIdeal witnessNetwork ∧
      ∃ h : Poly3, h ∉ steadyIdeal witnessNetwork ∧ (X 2-1)*h ∈ steadyIdeal witnessNetwork) ∧
    ¬ AlgorithmCandidates {b1,b2,b3} 1 := by
  exact ⟨mixed_order_admissible,witness_reduced_basis,witness_bimolecular,witness_acr,
    witness_zero_divisor,witness_no_candidates 1⟩

end ACRZeroDivisors.OrderWitness
