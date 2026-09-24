import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring

namespace ACRZeroDivisors
open MvPolynomial

/-- The leading-ideal criterion for a given family of generators. -/
def HasLeadingCover {σ R ι : Type*} [CommRing R]
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ R))
    (b : ι → MvPolynomial σ R) : Prop :=
  ∀ p ∈ I, p ≠ 0 → ∃ i, m.degree (b i) ≤ m.degree p

/-- Monic division plus the leading-ideal criterion rules out coefficient torsion.
No finite-dimensionality or finiteness of the set of standard monomials is used. -/
theorem monic_coefficient_regular {σ R ι : Type*} [CommRing R] [IsDomain R]
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ R))
    (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (hgen : ∀ i, b i ∈ I) (hcover : HasLeadingCover m I b)
    (a : R) (ha : a ≠ 0) (p : MvPolynomial σ R)
    (hp : C a*p ∈ I) : p ∈ I := by
  classical
  obtain ⟨q,r,heq,_,hstd⟩ := MonomialOrder.div (m:=m) hb p
  have hq : Finsupp.linearCombination (MvPolynomial σ R) b q ∈ I := by
    rw [Finsupp.linearCombination_apply,Finsupp.sum]
    apply I.sum_mem
    intro i hi
    exact I.mul_mem_left (q i) (hgen i)
  have hr : C a*r ∈ I := by
    have h := I.sub_mem hp (I.mul_mem_left (C a) hq)
    convert h using 1
    rw [heq]
    ring
  have hr0 : r=0 := by
    by_contra hn
    have hca : (C a : MvPolynomial σ R) ≠ 0 := by simpa using ha
    obtain ⟨i,hi⟩ := hcover (C a*r) hr (mul_ne_zero hca hn)
    rw [m.degree_mul hca hn,m.degree_C,zero_add] at hi
    exact hstd (m.degree r) (m.degree_mem_support hn) i hi
  rw [heq,hr0,add_zero]
  exact hq

end ACRZeroDivisors
