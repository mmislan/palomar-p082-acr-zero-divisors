import proofs.ACRZeroDivisors.SufficiencyIdeal
import Mathlib.Tactic.LinearCombination

namespace ACRZeroDivisors
open MvPolynomial

def CoordinateCandidate4 (I : Ideal Poly4) (alpha : ℝ) : Prop :=
  X 0-C alpha ∈ I ∨
    (X 0-C alpha ∉ I ∧ ∃ h : Poly4, h ∉ I ∧ (X 0-C alpha)*h ∈ I)

theorem diagonal_coordinate (alpha : ℝ) :
    diagonal (X 0-C alpha) = X 0-C alpha := by
  simp only [map_sub]
  simp [diagonal]

theorem coordinate_polynomial_ne_zero (alpha : ℝ) : (X 0-C alpha : Poly4) ≠ 0 := by
  intro h
  have hh := congrArg (eval (![alpha+1,0,0,0] : Fin 4 → ℝ)) h
  norm_num at hh

theorem sufficiency_coordinate_not_mem (alpha : ℝ) : X 0-C alpha ∉ sufficiencyIdeal := by
  intro h
  have hh := sufficiency_diagonal_zero h
  rw [diagonal_coordinate] at hh
  exact coordinate_polynomial_ne_zero alpha hh

theorem sufficiency_coordinate_regular (alpha : ℝ) (ha : alpha ≠ 1)
    (p : Poly4) (hp : (X 0-C alpha)*p ∈ sufficiencyIdeal) : p ∈ sufficiencyIdeal := by
  apply (sufficiency_two_kernel_criterion p).mpr
  constructor
  · have h := sufficiency_diagonal_zero hp
    rw [map_mul, diagonal_coordinate] at h
    exact (mul_eq_zero.mp h).resolve_left (coordinate_polynomial_ne_zero alpha)
  · have h := sufficiency_point_zero hp
    rw [map_mul] at h
    have hc : negativePoint (X 0-C alpha) = 1-alpha := by simp [negativePoint]
    rw [hc] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr ha.symm)

theorem sufficiency_candidate_iff (alpha : ℝ) :
    CoordinateCandidate4 sufficiencyIdeal alpha ↔ alpha = 1 := by
  constructor
  · intro h
    by_contra ha
    rcases h with h | ⟨_,p,hp,hm⟩
    · exact sufficiency_coordinate_not_mem alpha h
    · exact hp (sufficiency_coordinate_regular alpha ha p hm)
  · rintro rfl
    right
    refine ⟨sufficiency_coordinate_not_mem 1, sq, ?_, ?_⟩
    · intro h
      have hh := sufficiency_point_zero h
      norm_num [negativePoint, sq] at hh
    · simpa using sq_a_relation

theorem sufficiency_unique_candidate :
    ∃! alpha : ℝ, 0 < alpha ∧ CoordinateCandidate4 sufficiencyIdeal alpha := by
  refine ⟨1, ⟨by norm_num, (sufficiency_candidate_iff 1).mpr rfl⟩, ?_⟩
  intro alpha h
  exact (sufficiency_candidate_iff alpha).mp h.2

theorem sufficiency_polynomial_field :
    polynomialField sufficiencyNetwork = ![sA,sB,sC,sD] := by
  have hfin : (2 : Fin 3).succ = (3 : Fin 4) := rfl
  have hh : C (1/2 : ℝ) * (2 : Poly4) = 1 := by
    have h : (C (1/2 : ℝ) : Poly4) * C 2 = 1 := by
      rw [← map_mul]
      norm_num
    simpa only [map_ofNat] using h
  funext i
  fin_cases i <;> norm_num [polynomialField, sufficiencyNetwork, Fin.prod_univ_succ,
    sA,sB,sC,sD, map_ofNat, hfin]
  · ring
  · linear_combination -(X 1)^2 * hh
  · ring
  · ring

theorem sufficiency_original_ideal : steadyIdeal sufficiencyNetwork = sufficiencyIdeal := by
  unfold steadyIdeal sufficiencyIdeal
  rw [sufficiency_polynomial_field]
  congr 1
  ext p
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · intro hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩

theorem sufficiency_positive_one : PositiveSteady sufficiencyNetwork ![1,1,1,1] := by
  constructor
  · intro i; fin_cases i <;> norm_num
  · intro i; rw [sufficiency_field]; fin_cases i <;> norm_num

theorem sufficiency_positive_two : PositiveSteady sufficiencyNetwork ![2,2,4,4] := by
  constructor
  · intro i; fin_cases i <;> norm_num
  · intro i; rw [sufficiency_field]; fin_cases i <;> norm_num

theorem sufficiency_not_acr : ¬ ∃ alpha, NonvacuousACR sufficiencyNetwork 0 alpha := by
  rintro ⟨alpha,_,h⟩
  have h1 := h _ sufficiency_positive_one
  have h2 := h _ sufficiency_positive_two
  norm_num at h1 h2
  linarith

theorem question313_sufficiency_counterexample :
    (∀ r ∈ sufficiencyNetwork, Bimolecular r) ∧
    (∃ x, PositiveSteady sufficiencyNetwork x) ∧
    (∃! alpha : ℝ, 0 < alpha ∧ CoordinateCandidate4 (steadyIdeal sufficiencyNetwork) alpha) ∧
    ¬ ∃ alpha, NonvacuousACR sufficiencyNetwork 0 alpha := by
  rw [sufficiency_original_ideal]
  exact ⟨sufficiency_bimolecular, ⟨_,sufficiency_positive_one⟩,
    sufficiency_unique_candidate, sufficiency_not_acr⟩

end ACRZeroDivisors
