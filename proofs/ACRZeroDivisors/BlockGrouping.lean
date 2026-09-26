import proofs.ACRZeroDivisors.ChallengeDefinitions
import proofs.ACRZeroDivisors.MonicRegularity
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Ideal.Maps

namespace ACRZeroDivisors
open MvPolynomial

theorem grouped_coeff {σ K : Type*} [CommRing K]
    (p : MvPolynomial (Option σ) K) (d : σ →₀ ℕ) (n : ℕ) :
    Polynomial.coeff (((optionEquivRight K σ p)).coeff d) n =
      (p).coeff (d.optionElim n) := by
  classical
  have hz (d : σ →₀ ℕ) (n : ℕ) : d.optionElim n = 0 ↔ d = 0 ∧ n = 0 := by
    constructor
    · intro h
      constructor
      · simpa using congrArg Finsupp.some h
      · simpa using congrArg (fun e => e none) h
    · rintro ⟨rfl,rfl⟩; simp
  induction p using MvPolynomial.induction_on generalizing d n with
  | C r =>
      have hz' : 0 = d.optionElim n ↔ 0 = d ∧ n = 0 := by
        rw [eq_comm, hz, eq_comm (a := d)]
      rw [optionEquivRight_C,coeff_C,coeff_C]
      by_cases hd : 0 = d
      · simp only [hd,ite_true,hz',true_and,Polynomial.coeff_C]
      · simp only [hd,ite_false,hz',false_and,Polynomial.coeff_zero]
  | add p q hp hq =>
      simp only [map_add,Polynomial.coeff_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hp,hq]
  | mul_X p i hp =>
      cases i with
      | some i =>
          have hshift : d.optionElim n - Finsupp.single (some i) 1 =
              (d - Finsupp.single i 1).optionElim n := by
            ext j; cases j <;> simp [Finsupp.single_apply]
          simp only [map_mul,optionEquivRight_X_some,coeff_mul_X',
            Finsupp.mem_support_iff,Finsupp.optionElim_apply_some,hshift]
          split_ifs <;> simp_all
      | none =>
          have hshift : d.optionElim n - Finsupp.single none 1 =
              d.optionElim (n-1) := by
            ext j; cases j <;> simp
          rw [map_mul,optionEquivRight_X_none,mul_comm _ (C Polynomial.X),
            coeff_C_mul,coeff_mul_X']
          simp only [Finsupp.mem_support_iff,Finsupp.optionElim_apply_none,hshift]
          cases n with
          | zero => simp
          | succ n => simpa using hp d n

theorem grouped_support {σ K : Type*} [CommRing K]
    (p : MvPolynomial (Option σ) K) (d : σ →₀ ℕ) :
    d ∈ (optionEquivRight K σ p).support ↔ ∃ n, d.optionElim n ∈ p.support := by
  simp only [mem_support_iff, ne_eq, ← grouped_coeff]
  rw [← not_forall]
  exact not_congr Polynomial.ext_iff

theorem grouped_degree {σ K : Type*} [CommRing K]
    (full : MonomialOrder (Option σ)) (z : MonomialOrder σ)
    (hblock : BlockCompatible full z) (p : MvPolynomial (Option σ) K) :
    z.degree (optionEquivRight K σ p) = (full.degree p).some := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  apply z.toSyn.injective
  apply le_antisymm
  · apply z.degree_le_iff.mpr
    intro d hd
    obtain ⟨n,hn⟩ := (grouped_support p d).mp hd
    simpa using hblock _ _ (full.le_degree hn)
  · apply z.le_degree
    apply (grouped_support p _).mpr
    exact ⟨full.degree p none, by simpa using full.degree_mem_support hp⟩

theorem block_grouping_leading_cover {σ K ι : Type*} [CommRing K]
    (full : MonomialOrder (Option σ)) (z : MonomialOrder σ)
    (hblock : BlockCompatible full z) (I : Ideal (MvPolynomial (Option σ) K))
    (b : ι → MvPolynomial (Option σ) K) (hcover : HasLeadingCover full I b) :
    HasLeadingCover z (I.map (optionEquivRight K σ).toRingHom)
      (fun i => optionEquivRight K σ (b i)) := by
  intro p hp hp0
  obtain ⟨q,hq,rfl⟩ := (Ideal.mem_map_iff_of_surjective
    (optionEquivRight K σ).toRingHom (optionEquivRight K σ).surjective).mp hp
  have hq0 : q ≠ 0 := by intro h; simp [h] at hp0
  obtain ⟨i,hi⟩ := hcover q hq hq0
  refine ⟨i,?_⟩
  change z.degree (optionEquivRight K σ (b i)) ≤ z.degree (optionEquivRight K σ q)
  rw [grouped_degree full z hblock,grouped_degree full z hblock]
  intro j
  exact hi (some j)

end ACRZeroDivisors
