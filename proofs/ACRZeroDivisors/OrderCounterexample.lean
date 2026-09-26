import proofs.ACRZeroDivisors.ChallengeDefinitions
import proofs.ACRZeroDivisors.OrderOutput
import proofs.ACRZeroDivisors.NecessityIdeal
import Mathlib.Algebra.Polynomial.Eval.Algebra

namespace ACRZeroDivisors.OrderWitness
open MvPolynomial

theorem witness_bimolecular : ∀ r ∈ witnessNetwork, Bimolecular r := by
  norm_num [witnessNetwork,Bimolecular,Fin.sum_univ_succ]

theorem witness_field (u v t : ℝ) : field witnessNetwork ![u,v,t] = ![v-t*u,u-t*v,0] := by
  funext i
  fin_cases i <;> norm_num [field,witnessNetwork,Fin.prod_univ_succ] <;> ring

theorem b1_expression : b1 = (X 0)^2-(X 1)^2 := by
  simp only [b1,X_pow_eq_monomial]

theorem b2_expression : b2 = X 0*X 2-X 1 := by
  simp only [b2,X,monomial_mul_monomial,mul_one]

theorem b3_expression : b3 = X 1*X 2-X 0 := by
  simp only [b3,X,monomial_mul_monomial,mul_one]

theorem witness_polynomial_fieldQ : polynomialFieldQ witnessNetwork = ![-b2,-b3,0] := by
  funext i
  fin_cases i <;> norm_num [polynomialFieldQ,witnessNetwork,Fin.prod_univ_succ,
    map_ofNat,b2_expression,b3_expression] <;> ring

theorem witness_rational_ideal : rationalSteadyIdeal witnessNetwork = basisIdeal := by
  have h2 : b2 ∈ rationalSteadyIdeal witnessNetwork := by
    have h : -b2 ∈ rationalSteadyIdeal witnessNetwork := by
      apply Ideal.subset_span
      exact ⟨0,by rw [witness_polynomial_fieldQ]; rfl⟩
    simpa only [neg_neg] using (rationalSteadyIdeal witnessNetwork).neg_mem h
  have h3 : b3 ∈ rationalSteadyIdeal witnessNetwork := by
    have h : -b3 ∈ rationalSteadyIdeal witnessNetwork := by
      apply Ideal.subset_span
      exact ⟨1,by rw [witness_polynomial_fieldQ]; rfl⟩
    simpa only [neg_neg] using (rationalSteadyIdeal witnessNetwork).neg_mem h
  apply le_antisymm
  · rw [rationalSteadyIdeal,Ideal.span_le]
    rintro p ⟨i,rfl⟩
    rw [witness_polynomial_fieldQ]
    fin_cases i <;> simp [basisIdeal]
    all_goals exact Ideal.subset_span (by simp)
  · rw [basisIdeal,Ideal.span_le]
    intro p hp
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · have h := (rationalSteadyIdeal witnessNetwork).sub_mem
        ((rationalSteadyIdeal witnessNetwork).mul_mem_left (X 1) h2)
        ((rationalSteadyIdeal witnessNetwork).mul_mem_left (X 0) h3)
      show b1 ∈ rationalSteadyIdeal witnessNetwork
      convert h using 1
      rw [b1_expression,b2_expression,b3_expression]
      ring
    · exact h2
    · exact h3

theorem witness_polynomial_field : polynomialField witnessNetwork =
    ![X 1-X 2*X 0,X 0-X 2*X 1,0] := by
  funext i
  fin_cases i <;> norm_num [polynomialField,witnessNetwork,Fin.prod_univ_succ,map_ofNat] <;> ring

theorem witness_positive : PositiveSteady witnessNetwork ![1,1,1] := by
  constructor
  · intro i; fin_cases i <;> norm_num
  · intro i; rw [witness_field]; fin_cases i <;> norm_num

theorem witness_acr : NonvacuousACR witnessNetwork 2 1 := by
  refine ⟨⟨_,witness_positive⟩,?_⟩
  intro x hx
  have heq : x = ![x 0,x 1,x 2] := by funext i; fin_cases i <;> rfl
  have h0 := hx.2 0
  have h1 := hx.2 1
  rw [heq,witness_field] at h0 h1
  exact ((order_positive_locus (x 2) (x 0) (x 1) (hx.1 2) (hx.1 0)).mp ⟨h0,h1⟩).1

theorem witness_eval_zero (x : Fin 3 → ℝ)
    (hx : ∀ i, eval x (polynomialField witnessNetwork i) = 0)
    {p : Poly3} (hp : p ∈ steadyIdeal witnessNetwork) : eval x p = 0 := by
  have hle : steadyIdeal witnessNetwork ≤ RingHom.ker (eval x) := by
    rw [steadyIdeal,Ideal.span_le]
    rintro p ⟨i,rfl⟩
    exact hx i
  exact hle hp

theorem witness_zero_divisor :
    (X 2-1 : Poly3) ∉ steadyIdeal witnessNetwork ∧
    ∃ h : Poly3, h ∉ steadyIdeal witnessNetwork ∧ (X 2-1)*h ∈ steadyIdeal witnessNetwork := by
  constructor
  · intro h
    have bad := witness_eval_zero ![0,0,2] (by
      intro i; rw [witness_polynomial_field]; fin_cases i <;> norm_num) h
    norm_num at bad
  · refine ⟨X 0+X 1,?_,?_⟩
    · intro h
      have bad := witness_eval_zero ![1,1,1] (by
        intro i; rw [witness_polynomial_field]; fin_cases i <;> norm_num) h
      norm_num at bad
    · have h0 : polynomialField witnessNetwork 0 ∈ steadyIdeal witnessNetwork :=
        Ideal.subset_span ⟨0,rfl⟩
      have h1 : polynomialField witnessNetwork 1 ∈ steadyIdeal witnessNetwork :=
        Ideal.subset_span ⟨1,rfl⟩
      have h := (steadyIdeal witnessNetwork).neg_mem ((steadyIdeal witnessNetwork).add_mem h0 h1)
      rw [witness_polynomial_field] at h
      convert h using 1
      norm_num
      ring

theorem witness_no_candidates (alpha : ℝ) : ¬ AlgorithmCandidates {b1,b2,b3} alpha := by
  have hn : ¬ ∃ g ∈ ({b1,b2,b3} : Set P), PureT g := by
    rintro ⟨g,hg,h⟩
    exact basis_no_pureT g hg h
  rw [AlgorithmCandidates,ite_eq_right hn]
  rintro ⟨ha,g,hg,hroot⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · rw [b1_lcZ] at hroot
    norm_num at hroot
  · rw [b2_lcZ] at hroot
    norm_num at hroot
    exact (ne_of_gt ha) hroot
  · rw [b3_lcZ] at hroot
    norm_num at hroot

end ACRZeroDivisors.OrderWitness
