import proofs.ACRZeroDivisors.BlockTorsion

namespace ACRZeroDivisors
open MvPolynomial

theorem grouped_map {σ K L : Type*} [Field K] [Field L] (f : K →+* L)
    (p : MvPolynomial (Option σ) K) :
    optionEquivRight L σ (map f p) =
      map (Polynomial.mapRingHom f) (optionEquivRight K σ p) := by
  ext d n
  simp only [grouped_coeff,coeff_map,Polynomial.coeff_map,Polynomial.coe_mapRingHom]

theorem grouped_leading_map {σ K L : Type*} [Field K] [Field L]
    (z : MonomialOrder σ) (f : K →+* L) (p : MvPolynomial (Option σ) K) :
    z.leadingCoeff (optionEquivRight L σ (map f p)) =
      Polynomial.map f (z.leadingCoeff (optionEquivRight K σ p)) := by
  rw [grouped_map]
  unfold MonomialOrder.leadingCoeff
  rw [degree_injective_map z _ (Polynomial.map_injective f f.injective),coeff_map]
  rfl

/-- Rational input bases may be tested against real witnesses: the witnesses
are not required to descend to the input field. -/
theorem block_extension_torsion_candidate {σ K L ι : Type*}
    [Field K] [Field L] [Algebra K L] [Fintype ι]
    (full : MonomialOrder (Option σ)) (z : MonomialOrder σ)
    (hblock : BlockCompatible full z) (I : Ideal (MvPolynomial (Option σ) K))
    (b : ι → MvPolynomial (Option σ) K)
    (hcover : HasLeadingCover full I b) (hgen : ∀ i, b i ∈ I)
    (a : L) (p : MvPolynomial (Option σ) L)
    (hp : p ∉ I.map (map (algebraMap K L)))
    (ht : (X none - C a) * p ∈ I.map (map (algebraMap K L))) :
    ∃ i, (z.leadingCoeff (optionEquivRight K σ (b i))).eval₂ (algebraMap K L) a = 0 := by
  obtain ⟨i,hi⟩ := block_torsion_candidate full z hblock _
    (fun i => map (algebraMap K L) (b i))
    (scalar_extension_leading_cover full I b hcover)
    (fun i => Ideal.mem_map_of_mem _ (hgen i)) a p hp ht
  refine ⟨i,?_⟩
  rwa [grouped_leading_map,Polynomial.eval_map] at hi

end ACRZeroDivisors
