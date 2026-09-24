import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import proofs.ACRZeroDivisors.MassActionSource

namespace ACRZeroDivisors
open MvPolynomial

abbrev Poly3 := MvPolynomial (Fin 3) ℝ
noncomputable def nA : Poly3 := -X 0*X 1+X 1-X 0*X 2+3*X 2
noncomputable def nB : Poly3 := X 0*X 1-2*X 1
noncomputable def nC : Poly3 := X 0*X 2-3*X 2+X 1
noncomputable def necessityIdeal : Ideal Poly3 := Ideal.span {nA,nB,nC}

def CoordinateCandidate (I : Ideal Poly3) (alpha : ℝ) : Prop :=
  X 0 - C alpha ∈ I ∨
    (X 0 - C alpha ∉ I ∧ ∃ h : Poly3, h ∉ I ∧ (X 0 - C alpha)*h ∈ I)

theorem necessity_eval_zero (x : Fin 3 → ℝ)
    (hA : eval x nA = 0) (hB : eval x nB = 0) (hC : eval x nC = 0)
    {p : Poly3} (hp : p ∈ necessityIdeal) : eval x p = 0 := by
  have hle : necessityIdeal ≤ RingHom.ker (eval x) := by
    rw [necessityIdeal, Ideal.span_le]
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact hA
    · exact hB
    · exact hC
  exact hle hp

theorem necessity_candidate_two : CoordinateCandidate necessityIdeal 2 := by
  right
  constructor
  · intro h
    have bad := necessity_eval_zero (![0,0,0]) (by simp [nA])
      (by simp [nB]) (by simp [nC]) h
    norm_num at bad
  · refine ⟨X 1, ?_, ?_⟩
    · intro h
      have bad := necessity_eval_zero (![2,1,1]) (by norm_num [nA])
        (by norm_num [nB]) (by norm_num [nC]) h
      norm_num at bad
    · have hB : nB ∈ necessityIdeal := Ideal.subset_span (by simp)
      convert hB using 1
      norm_num [nB, map_ofNat]
      ring

theorem necessity_candidate_three : CoordinateCandidate necessityIdeal 3 := by
  right
  constructor
  · intro h
    have bad := necessity_eval_zero (![0,0,0]) (by simp [nA])
      (by simp [nB]) (by simp [nC]) h
    norm_num at bad
  · refine ⟨X 2*(X 0-2), ?_, ?_⟩
    · intro h
      have bad := necessity_eval_zero (![3,0,1]) (by norm_num [nA])
        (by norm_num [nB]) (by norm_num [nC]) h
      norm_num at bad
    · have hB : nB ∈ necessityIdeal := Ideal.subset_span (by simp)
      have hC : nC ∈ necessityIdeal := Ideal.subset_span (by simp)
      have hh := necessityIdeal.sub_mem (necessityIdeal.mul_mem_left (X 0-2) hC) hB
      convert hh using 1
      norm_num [nB, nC, map_ofNat]
      ring

theorem necessity_not_unique_candidate :
    ¬ ∃! alpha : ℝ, 0 < alpha ∧ CoordinateCandidate necessityIdeal alpha := by
  rintro ⟨alpha, _, huniq⟩
  have h2 := huniq 2 ⟨by norm_num, necessity_candidate_two⟩
  have h3 := huniq 3 ⟨by norm_num, necessity_candidate_three⟩
  have : (2 : ℝ) = 3 := h2.trans h3.symm
  norm_num at this

noncomputable def polynomialField {n : ℕ} (rs : List (Reaction n))
    (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  (rs.map fun r => C (r.rate : ℝ) * (∏ j, X j ^ r.source j) *
    (C (r.target i : ℝ) - C (r.source i : ℝ))).sum

noncomputable def steadyIdeal {n : ℕ} (rs : List (Reaction n)) :
    Ideal (MvPolynomial (Fin n) ℝ) := Ideal.span (Set.range (polynomialField rs))

theorem necessity_polynomial_field :
    polynomialField necessityNetwork = ![nA,nB,nC] := by
  funext i
  fin_cases i <;> norm_num [polynomialField, necessityNetwork, Fin.prod_univ_succ,
    nA, nB, nC, map_ofNat] <;> ring

theorem necessity_original_ideal : steadyIdeal necessityNetwork = necessityIdeal := by
  unfold steadyIdeal necessityIdeal
  rw [necessity_polynomial_field]
  congr 1
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

def PositiveSteady {n : ℕ} (rs : List (Reaction n)) (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 < x i) ∧ ∀ i, field rs x i = 0

def NonvacuousACR {n : ℕ} (rs : List (Reaction n)) (i : Fin n) (alpha : ℝ) : Prop :=
  (∃ x, PositiveSteady rs x) ∧ ∀ x, PositiveSteady rs x → x i = alpha

theorem necessity_literal_acr : NonvacuousACR necessityNetwork 0 2 := by
  constructor
  · refine ⟨![2,1,1], ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · intro i
      rw [necessity_field]
      fin_cases i <;> norm_num
  · intro x hx
    have heq : x = ![x 0,x 1,x 2] := by
      funext i; fin_cases i <;> rfl
    have hf := hx.2 1
    rw [heq, necessity_field] at hf
    norm_num at hf
    have h : necessitySteady (x 0) (x 1) (x 2) := by
      have hall := hx.2
      rw [heq, necessity_field] at hall
      exact ⟨hall 0, hall 1, hall 2⟩
    exact ((necessity_positive_locus (x 0) (x 1) (x 2) (hx.1 1)).mp h).1

theorem question313_necessity_counterexample :
    (∀ r ∈ necessityNetwork, Bimolecular r) ∧
    NonvacuousACR necessityNetwork 0 2 ∧
    ¬ ∃! alpha : ℝ, 0 < alpha ∧ CoordinateCandidate (steadyIdeal necessityNetwork) alpha := by
  rw [necessity_original_ideal]
  exact ⟨necessity_bimolecular, necessity_literal_acr, necessity_not_unique_candidate⟩

end ACRZeroDivisors


