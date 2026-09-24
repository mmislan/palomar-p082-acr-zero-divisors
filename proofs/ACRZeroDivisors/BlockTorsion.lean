import proofs.ACRZeroDivisors.BlockGrouping
import proofs.ACRZeroDivisors.BlockCoefficientCore
import proofs.ACRZeroDivisors.ScalarExtension

namespace ACRZeroDivisors
open MvPolynomial

theorem full_block_coefficient_regular {σ K ι : Type*} [Field K]
    (full : MonomialOrder (Option σ)) (z : MonomialOrder σ)
    (hblock : BlockCompatible full z) (I : Ideal (MvPolynomial (Option σ) K))
    (b : ι → MvPolynomial (Option σ) K)
    (hcover : HasLeadingCover full I b) (hgen : ∀ i, b i ∈ I)
    (H : Polynomial K)
    (hdiv : ∀ i, z.leadingCoeff (optionEquivRight K σ (b i)) ∣ H)
    (a : K) (hH : H.eval a ≠ 0) (p : MvPolynomial (Option σ) K)
    (hp : (X none - C a) * p ∈ I) : p ∈ I := by
  let e := optionEquivRight K σ
  have h : e p ∈ I.map e.toRingHom := by
    apply block_coefficient_regular z _ (fun i => e (b i))
      (block_grouping_leading_cover full z hblock I b hcover)
      (fun i => Ideal.mem_map_of_mem _ (hgen i)) H hdiv a hH
    have hh := Ideal.mem_map_of_mem e.toRingHom hp
    change optionEquivRight K σ ((X none - C a) * p) ∈ _ at hh
    rw [map_mul,map_sub,optionEquivRight_X_none,optionEquivRight_C,← map_sub] at hh
    exact hh
  obtain ⟨q,hq,heq⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp h
  exact e.injective heq ▸ hq

/-- A genuine nonzero coordinate-torsion class forces a root in the actual
finite list of z-leading coefficients of the input block basis. -/
theorem block_torsion_candidate {σ K ι : Type*} [Field K] [Fintype ι]
    (full : MonomialOrder (Option σ)) (z : MonomialOrder σ)
    (hblock : BlockCompatible full z) (I : Ideal (MvPolynomial (Option σ) K))
    (b : ι → MvPolynomial (Option σ) K)
    (hcover : HasLeadingCover full I b) (hgen : ∀ i, b i ∈ I)
    (a : K) (p : MvPolynomial (Option σ) K) (hp : p ∉ I)
    (ht : (X none - C a) * p ∈ I) :
    ∃ i, (z.leadingCoeff (optionEquivRight K σ (b i))).eval a = 0 := by
  classical
  by_contra! hn
  let H := ∏ i, z.leadingCoeff (optionEquivRight K σ (b i))
  have hH : H.eval a ≠ 0 := by
    simp only [H,Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hn i)
  apply hp
  apply full_block_coefficient_regular full z hblock I b hcover hgen H _ a hH p ht
  intro i
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

end ACRZeroDivisors
