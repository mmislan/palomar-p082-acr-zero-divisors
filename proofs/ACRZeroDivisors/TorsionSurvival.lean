import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace ACRZeroDivisors
open MvPolynomial

/-- A coordinate-torsion class cannot be killed by a polynomial nonzero at
that coordinate value. This is the denominator-survival implication. -/
theorem coordinate_torsion_survives {σ K : Type*} [Field K]
    (I : Ideal (MvPolynomial σ (Polynomial K))) (a : K)
    (H : Polynomial K) (hH : H.eval a ≠ 0)
    (p : MvPolynomial σ (Polynomial K))
    (ht : C (Polynomial.X - Polynomial.C a) * p ∈ I)
    (hkill : C H * p ∈ I) : p ∈ I := by
  obtain ⟨q,hq⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := H) (a := a)
  have hconst : C (Polynomial.C (H.eval a)) * p ∈ I := by
    have h := I.sub_mem hkill (I.mul_mem_left (C q) ht)
    convert h using 1
    have hc := congrArg (C : Polynomial K →+* MvPolynomial σ (Polynomial K)) hq
    simp only [map_sub,map_mul] at hc
    simp only [map_sub]
    linear_combination -p * hc
  have h := I.mul_mem_left (C (Polynomial.C ((H.eval a)⁻¹))) hconst
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hH, map_one, one_mul] using h

theorem coordinate_torsion_survives_power {σ K : Type*} [Field K]
    (I : Ideal (MvPolynomial σ (Polynomial K))) (a : K)
    (H : Polynomial K) (hH : H.eval a ≠ 0) (n : ℕ)
    (p : MvPolynomial σ (Polynomial K))
    (ht : C (Polynomial.X - Polynomial.C a) * p ∈ I)
    (hkill : C (H^n) * p ∈ I) : p ∈ I := by
  apply coordinate_torsion_survives I a (H^n) _ p ht hkill
  simpa only [Polynomial.eval_pow] using pow_ne_zero n hH

end ACRZeroDivisors
