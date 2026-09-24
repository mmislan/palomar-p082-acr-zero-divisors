import proofs.ACRZeroDivisors.OrderCounterexample
import proofs.ACRZeroDivisors.OrderReducedBasis

namespace ACRZeroDivisors.OrderWitness
open MvPolynomial

/-- Explicit order axioms and the source's polynomial elimination condition. -/
def AdmissibleEliminationOrder : Prop :=
  WellFounded MixedLT ∧
  (∀ e, ¬ MixedLT e e) ∧
  (∀ e f g, MixedLT e f → MixedLT f g → MixedLT e g) ∧
  (∀ e f, MixedLT e f ∨ e=f ∨ MixedLT f e) ∧
  (∀ e f h, MixedLT (e+h) (f+h) ↔ MixedLT e f) ∧
  (∀ e, ¬ MixedLT e 0) ∧
  (∀ p e, IsLeading e p → zDegree e=0 → PureT p)

theorem mixed_order_admissible : AdmissibleEliminationOrder := by
  refine ⟨mixed_wellFounded,mixed_irrefl,fun _ _ _ => mixed_trans,
    mixed_trichotomy,mixed_add,?_,order_elimination_property⟩
  intro e
  simp [MixedLT,zDegree]

theorem coefficient_order_is_restriction (e f : Exponent) (he : e 2=0) (hf : f 2=0) :
    MixedLT e f ↔ zKey e < zKey f := by
  simp [MixedLT,zKey,Prod.Lex.toLex_lt_toLex,he,hf]

/-- Reduced Gröbner basis semantics for the three explicitly marked polynomials:
generation, actual leading terms, monicity, leading-ideal coverage and reducedness. -/
def ReducedBasisCertificate (I : Ideal P) : Prop :=
  I = basisIdeal ∧
  IsLeading L1 b1 ∧ IsLeading L2 b2 ∧ IsLeading L3 b3 ∧
  ((b1).coeff L1 = 1 ∧ (b2).coeff L2 = 1 ∧ (b3).coeff L3 = 1) ∧
  (∀ p ∈ I, p ≠ 0 → ∃ e, IsLeading e p ∧ (L1 ≤ e ∨ L2 ≤ e ∨ L3 ≤ e)) ∧
  (∀ e ∈ b1.support, e ≠ L1 → ¬ L1 ≤ e ∧ ¬ L2 ≤ e ∧ ¬ L3 ≤ e) ∧
  (∀ e ∈ b2.support, e ≠ L2 → ¬ L1 ≤ e ∧ ¬ L2 ≤ e ∧ ¬ L3 ≤ e) ∧
  (∀ e ∈ b3.support, e ≠ L3 → ¬ L1 ≤ e ∧ ¬ L2 ≤ e ∧ ¬ L3 ≤ e) ∧
  (¬ L1 ≤ L2 ∧ ¬ L1 ≤ L3 ∧ ¬ L2 ≤ L1 ∧ ¬ L2 ≤ L3 ∧ ¬ L3 ≤ L1 ∧ ¬ L3 ≤ L2)

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
