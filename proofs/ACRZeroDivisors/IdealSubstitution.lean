import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring

namespace ACRZeroDivisors
open MvPolynomial

theorem substitution_sub_mem {σ R : Type*} [CommRing R]
    (I : Ideal (MvPolynomial σ R)) (v : σ → MvPolynomial σ R)
    (hv : ∀ i, X i - v i ∈ I) (p : MvPolynomial σ R) :
    p - eval₂Hom C v p ∈ I := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p r hp hr =>
      have hh := I.add_mem hp hr
      (convert hh using 1; simp only [map_add]; ring)
  | mul_X p i hp =>
      have hh := I.add_mem (I.mul_mem_left (X i) hp)
        (I.mul_mem_left (eval₂Hom C v p) (hv i))
      (convert hh using 1; simp only [map_mul, eval₂Hom_X']; ring)

theorem mul_eval_sub_mem {σ R : Type*} [CommRing R]
    (I : Ideal (MvPolynomial σ R)) (v : σ → R) (q : MvPolynomial σ R)
    (hv : ∀ i, (X i-C (v i))*q ∈ I) (p : MvPolynomial σ R) :
    (p-C (eval v p))*q ∈ I := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p r hp hr =>
      have hh := I.add_mem hp hr
      (convert hh using 1; simp only [map_add]; ring)
  | mul_X p i hp =>
      have hh := I.add_mem (I.mul_mem_left (X i) hp)
        (I.mul_mem_left (C (eval v p)) (hv i))
      (convert hh using 1; simp only [map_mul, eval_X]; ring)

end ACRZeroDivisors

