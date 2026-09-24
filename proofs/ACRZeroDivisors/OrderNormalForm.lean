import proofs.ACRZeroDivisors.OrderExponent
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring

namespace ACRZeroDivisors.OrderWitness
open MvPolynomial
abbrev P := MvPolynomial (Fin 3) ℚ

noncomputable def normalForm : P →ₗ[ℚ] P := AddMonoidAlgebra.mapDomainLinearMap ℚ ℚ normalExponent

theorem normalForm_monomial (e : Exponent) (c : ℚ) :
    normalForm (monomial e c) = monomial (normalExponent e) c := by
  exact AddMonoidAlgebra.mapDomainLinearMap_single normalExponent c e

theorem normalForm_binomial_mul (l r : Exponent)
    (h : ∀ e, normalExponent (e+l) = normalExponent (e+r)) (p : P) :
    normalForm (p*(monomial l 1-monomial r 1)) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial e c =>
      rw [mul_sub,monomial_mul,monomial_mul,map_sub,
        normalForm_monomial,normalForm_monomial,h]
      simp
  | add p q hp hq => simp [add_mul,map_add,hp,hq]

noncomputable def normalAnnihilator : Ideal P where
  carrier := {p | ∀ r, normalForm (r*p) = 0}
  zero_mem' := by intro r; simp
  add_mem' := by
    intro p q hp hq r
    simp only [mul_add,map_add,hp r,hq r,add_zero]
  smul_mem' := by
    intro c p hp r
    simpa only [smul_eq_mul,mul_assoc] using hp (r*c)

noncomputable def b1 : P := monomial (Finsupp.single 0 2) 1-monomial (Finsupp.single 1 2) 1
noncomputable def b2 : P :=
  monomial (Finsupp.single 0 1+Finsupp.single 2 1) 1-monomial (Finsupp.single 1 1) 1
noncomputable def b3 : P :=
  monomial (Finsupp.single 1 1+Finsupp.single 2 1) 1-monomial (Finsupp.single 0 1) 1
noncomputable def basisIdeal : Ideal P := Ideal.span {b1,b2,b3}

theorem basisIdeal_normal_zero {p : P} (hp : p ∈ basisIdeal) : normalForm p = 0 := by
  have hle : basisIdeal ≤ normalAnnihilator := by
    rw [basisIdeal,Ideal.span_le]
    intro g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · intro r
      exact normalForm_binomial_mul _ _ normal_relation_u2 r
    · intro r
      apply normalForm_binomial_mul
      intro e
      simpa only [← add_assoc] using normal_relation_tu e
    · intro r
      apply normalForm_binomial_mul
      intro e
      simpa only [← add_assoc] using normal_relation_tv e
  have h := hle hp 1
  simpa only [one_mul] using h

def IsLeading (e : Exponent) (p : P) : Prop :=
  (p).coeff e ≠ 0 ∧ ∀ d ∈ p.support, d = e ∨ MixedLT d e

theorem normal_le (e : Exponent) : normalExponent e = e ∨ MixedLT (normalExponent e) e := by
  by_cases h : Standard e
  · exact Or.inl (normal_eq_self e h)
  · exact Or.inr (normal_strictly_lower e h)

theorem normal_not_leading {e d : Exponent} (hde : MixedLT d e) : normalExponent d ≠ e := by
  intro he
  rcases normal_le d with h | h
  · rw [he] at h
    subst d
    exact mixed_irrefl e hde
  · rw [he] at h
    exact mixed_irrefl e (mixed_trans h hde)

theorem normalForm_as_sum (p : P) :
    normalForm p = ∑ d ∈ p.support, monomial (normalExponent d) ((p).coeff d) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum,normalForm_monomial]

theorem normal_preserves_standard_leader {e : Exponent} {p : P}
    (he : IsLeading e p) (hs : Standard e) : ((normalForm p)).coeff e = (p).coeff e := by
  classical
  rw [normalForm_as_sum,coeff_sum]
  rw [Finset.sum_eq_single e]
  · simp [normal_eq_self e hs]
  · intro d hd hde
    have hlt := (he.2 d hd).resolve_left hde
    simp [coeff_monomial,normal_not_leading hlt]
  · intro h
    exact False.elim (h (mem_support_iff.mpr he.1))

theorem basisIdeal_leading_not_standard {e : Exponent} {p : P}
    (hp : p ∈ basisIdeal) (he : IsLeading e p) : ¬ Standard e := by
  intro hs
  have h := normal_preserves_standard_leader he hs
  rw [basisIdeal_normal_zero hp,coeff_zero] at h
  exact he.1 h.symm

end ACRZeroDivisors.OrderWitness
