import proofs.ACRZeroDivisors.CoefficientLocalization
import proofs.ACRZeroDivisors.TorsionSurvival

namespace ACRZeroDivisors
open MvPolynomial

/-- The coefficient-ring core of block completeness. Its remaining input
obligation is leading coverage over K[t], not merely over K(t). -/
theorem block_coefficient_regular {σ K ι : Type*} [Field K]
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ (Polynomial K)))
    (b : ι → MvPolynomial σ (Polynomial K))
    (hcover : HasLeadingCover m I b) (hgen : ∀ i, b i ∈ I)
    (H : Polynomial K) (hdiv : ∀ i, m.leadingCoeff (b i) ∣ H)
    (a : K) (hH : H.eval a ≠ 0)
    (p : MvPolynomial σ (Polynomial K))
    (hp : C (Polynomial.X - Polynomial.C a) * p ∈ I) : p ∈ I := by
  have hH0 : H ≠ 0 := by intro h; simp [h] at hH
  let S := Localization.Away H
  have hM := powers_le_nonZeroDivisors_of_noZeroDivisors hH0
  letI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hM
  have hinj := IsLocalization.injective S hM
  have hunits : ∀ i, IsUnit (algebraMap (Polynomial K) S (m.leadingCoeff (b i))) := by
    intro i
    obtain ⟨q,hq⟩ := hdiv i
    obtain ⟨v,hv⟩ := isUnit_iff_exists_inv.mp
      (IsLocalization.Away.algebraMap_isUnit H (S := S))
    apply isUnit_iff_exists_inv.mpr
    refine ⟨algebraMap (Polynomial K) S q * v, ?_⟩
    rw [← mul_assoc, ← map_mul, ← hq, hv]
  obtain ⟨s,hs,hsp⟩ := localization_coefficient_cancellation
    (S := S) (Submonoid.powers H) hinj m I b hcover hgen hunits
    (Polynomial.X - Polynomial.C a) (Polynomial.X_sub_C_ne_zero a) p hp
  obtain ⟨n,rfl⟩ := (Submonoid.mem_powers_iff s H).mp hs
  exact coordinate_torsion_survives_power I a H hH n p hp hsp

end ACRZeroDivisors
