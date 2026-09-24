import proofs.ACRZeroDivisors.MonicRegularity
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal

namespace ACRZeroDivisors
open MvPolynomial

theorem degree_injective_map {σ R S : Type*} [CommRing R] [CommRing S]
    (m : MonomialOrder σ) (f : R →+* S) (hf : Function.Injective f)
    (p : MvPolynomial σ R) : m.degree (map f p) = m.degree p := by
  classical
  unfold MonomialOrder.degree
  rw [support_map_of_injective p hf]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Clearing a coefficient denominator transports leading coverage. -/
theorem localization_leading_cover {σ R S ι : Type*}
    [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S]
    (hinj : Function.Injective (algebraMap R S))
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ R))
    (b : ι → MvPolynomial σ R) (hcover : HasLeadingCover m I b) :
    HasLeadingCover m (I.map (map (algebraMap R S)))
      (fun i => map (algebraMap R S) (b i)) := by
  intro p hp hp0
  obtain ⟨⟨q,s⟩,heq⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (M.map (C (σ := σ)))
      (MvPolynomial σ S)).mp hp
  obtain ⟨a,ha,has⟩ := s.property
  have heq' : p * C (algebraMap R S a) = map (algebraMap R S) q.val := by
    simpa only [algebraMap_def, ← has, map_C] using heq
  have ha0 : algebraMap R S a ≠ 0 :=
    (IsLocalization.map_units S (⟨a,ha⟩ : M)).ne_zero
  have hc0 : (C (algebraMap R S a) : MvPolynomial σ S) ≠ 0 := by
    simpa using ha0
  have hq0 : q.val ≠ 0 := by
    intro hq
    rw [hq,map_zero] at heq'
    exact mul_ne_zero hp0 hc0 heq'
  obtain ⟨i,hi⟩ := hcover q.val q.property hq0
  refine ⟨i, ?_⟩
  rw [degree_injective_map m _ hinj]
  have hd := congrArg m.degree heq'
  rw [m.degree_mul hp0 hc0,m.degree_C,add_zero,
    degree_injective_map m _ hinj] at hd
  exact hd.symm ▸ hi

theorem localization_coefficient_cancellation {σ R S ι : Type*}
    [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S]
    (hinj : Function.Injective (algebraMap R S))
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ R))
    (b : ι → MvPolynomial σ R) (hcover : HasLeadingCover m I b)
    (hgen : ∀ i, b i ∈ I)
    (hunit : ∀ i, IsUnit (algebraMap R S (m.leadingCoeff (b i))))
    (a : R) (ha : a ≠ 0) (p : MvPolynomial σ R)
    (hp : C a * p ∈ I) : ∃ s ∈ M, C s * p ∈ I := by
  have hmap : map (algebraMap R S) p ∈ I.map (map (algebraMap R S)) := by
    refine monic_coefficient_regular m _ (fun i => map (algebraMap R S) (b i))
      ?_ ?_ (localization_leading_cover M hinj m I b hcover)
      (algebraMap R S a) (fun h => ha (hinj (by simpa using h)))
      (map (algebraMap R S) p) ?_
    · intro i
      unfold MonomialOrder.leadingCoeff
      rw [degree_injective_map m _ hinj, coeff_map]
      exact hunit i
    · intro i
      exact Ideal.mem_map_of_mem _ (hgen i)
    · simpa only [map_mul,map_C] using
        (Ideal.mem_map_of_mem (map (algebraMap R S)) hp)
  obtain ⟨s,hs,hsp⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (M.map (C (σ := σ))) (MvPolynomial σ S) I p).mp hmap
  obtain ⟨s,hs,rfl⟩ := hs
  exact ⟨s,hs,hsp⟩

end ACRZeroDivisors
