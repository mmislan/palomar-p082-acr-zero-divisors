module

public import proofs.ACRZeroDivisors.CoefficientLocalization
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

namespace ACRZeroDivisors
open MvPolynomial

noncomputable def coefficientProjection {σ K L : Type*} [Field K] [Field L]
    [Algebra K L] (φ : L →ₗ[K] K) :
    MvPolynomial σ L →ₗ[K] MvPolynomial σ K :=
  (AddMonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap φ).comp
      (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap)

@[simp] theorem coefficientProjection_coeff {σ K L : Type*} [Field K] [Field L]
    [Algebra K L] (φ : L →ₗ[K] K) (p : MvPolynomial σ L) (d : σ →₀ ℕ) :
    ((coefficientProjection φ p)).coeff d = φ ((p).coeff d) := rfl

theorem coefficientProjection_mul_map {σ K L : Type*} [Field K] [Field L]
    [Algebra K L] (φ : L →ₗ[K] K) (p : MvPolynomial σ L)
    (q : MvPolynomial σ K) :
    coefficientProjection φ (p * map (algebraMap K L) q) =
      coefficientProjection φ p * q := by
  classical
  ext d
  simp only [coefficientProjection_coeff, coeff_mul, map_sum, coeff_map]
  apply Finset.sum_congr rfl
  intro e he
  rw [mul_comm ((p).coeff e.1), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

theorem coefficientProjection_mem {σ K L : Type*} [Field K] [Field L]
    [Algebra K L] (I : Ideal (MvPolynomial σ K))
    (p : MvPolynomial σ L) (hp : p ∈ I.map (map (algebraMap K L)))
    (φ : L →ₗ[K] K) : coefficientProjection φ p ∈ I := by
  have h : ∀ r : MvPolynomial σ L, ∀ ψ : L →ₗ[K] K,
      coefficientProjection ψ (r*p) ∈ I := by
    induction hp using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨q,hq,rfl⟩ := hx
        intro r ψ
        rw [coefficientProjection_mul_map]
        exact I.mul_mem_left _ hq
    | zero => intro r ψ; simp
    | add x y _ _ hx hy =>
        intro r ψ
        rw [mul_add,map_add]
        exact I.add_mem (hx r ψ) (hy r ψ)
    | smul a x _ hx =>
        intro r ψ
        simpa only [smul_eq_mul, ← mul_assoc] using hx (r*a) ψ
  simpa using h 1 φ

/-- A linear functional retaining the leading coefficient produces an original
ideal member with the same leader. No rationality of the new coefficients is assumed. -/
theorem scalar_extension_same_leader {σ K L : Type*} [Field K] [Field L]
    [Algebra K L] (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (p : MvPolynomial σ L) (hp : p ∈ I.map (map (algebraMap K L))) (hp0 : p ≠ 0) :
    ∃ q ∈ I, q ≠ 0 ∧ m.degree q = m.degree p := by
  classical
  obtain ⟨φ,hφ⟩ := Module.Projective.exists_dual_ne_zero K
    (m.leadingCoeff_ne_zero_iff.mpr hp0)
  let q := coefficientProjection φ p
  have hqcoeff : (q).coeff (m.degree p) ≠ 0 := hφ
  have hq0 : q ≠ 0 := by intro h; simp [h] at hqcoeff
  refine ⟨q,coefficientProjection_mem I p hp φ,hq0,?_⟩
  apply m.toSyn.injective
  apply le_antisymm
  · apply m.degree_le_iff.mpr
    intro d hd
    apply m.le_degree
    rw [mem_support_iff] at hd ⊢
    intro hzero
    apply hd
    change φ ((p).coeff d) = 0
    simp [hzero]
  · exact m.le_degree (mem_support_iff.mpr hqcoeff)

theorem scalar_extension_leading_cover {σ K L ι : Type*} [Field K] [Field L]
    [Algebra K L] (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (b : ι → MvPolynomial σ K) (hcover : HasLeadingCover m I b) :
    HasLeadingCover m (I.map (map (algebraMap K L)))
      (fun i => map (algebraMap K L) (b i)) := by
  intro p hp hp0
  obtain ⟨q,hq,hq0,heq⟩ := scalar_extension_same_leader m I p hp hp0
  obtain ⟨i,hi⟩ := hcover q hq hq0
  refine ⟨i,?_⟩
  rw [degree_injective_map m _ (algebraMap K L).injective, ← heq]
  exact hi

end ACRZeroDivisors
