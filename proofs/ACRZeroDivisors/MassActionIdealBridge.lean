import proofs.ACRZeroDivisors.NecessityIdeal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Algebra.Rat

namespace ACRZeroDivisors
open MvPolynomial

noncomputable def rationalPolynomialField {n : ℕ} (rs : List (Reaction n))
    (i : Fin n) : MvPolynomial (Fin n) ℚ :=
  (rs.map fun r => C r.rate * (∏ j, X j ^ r.source j) *
    (C (r.target i : ℚ) - C (r.source i : ℚ))).sum

noncomputable def rationalSteadyIdeal {n : ℕ} (rs : List (Reaction n)) :
    Ideal (MvPolynomial (Fin n) ℚ) := Ideal.span (Set.range (rationalPolynomialField rs))

theorem rational_field_cast {n : ℕ} (rs : List (Reaction n)) (i : Fin n) :
    map (algebraMap ℚ ℝ) (rationalPolynomialField rs i) = polynomialField rs i := by
  simp [rationalPolynomialField,polynomialField,map_list_sum,List.map_map,Function.comp_def]

theorem rational_ideal_cast {n : ℕ} (rs : List (Reaction n)) :
    (rationalSteadyIdeal rs).map (map (algebraMap ℚ ℝ)) = steadyIdeal rs := by
  rw [rationalSteadyIdeal,steadyIdeal,Ideal.map_span]
  congr 1
  ext p
  simp only [Set.mem_image,Set.mem_range]
  constructor
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩
    exact ⟨i,(rational_field_cast rs i).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨_,⟨i,rfl⟩,rational_field_cast rs i⟩

theorem eval_polynomial_field {n : ℕ} (rs : List (Reaction n)) (x : Fin n → ℝ)
    (i : Fin n) : eval x (polynomialField rs i) = field rs x i := by
  simp [polynomialField,field,map_list_sum,List.map_map,Function.comp_def]

theorem positive_steady_annihilates_ideal {n : ℕ} (rs : List (Reaction n))
    (x : Fin n → ℝ) (hx : PositiveSteady rs x) :
    ∀ p ∈ steadyIdeal rs, eval x p = 0 := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨i,rfl⟩ := hp
      rw [eval_polynomial_field]
      exact hx.2 i
  | zero => simp
  | add p q _ _ hp hq => simp [map_add,hp,hq]
  | smul a p _ hp => simp [smul_eq_mul,map_mul,hp]

end ACRZeroDivisors
