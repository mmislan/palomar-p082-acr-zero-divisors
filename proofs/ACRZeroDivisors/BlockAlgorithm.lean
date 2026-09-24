import proofs.ACRZeroDivisors.BlockScalarExtension
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Rat

namespace ACRZeroDivisors
open MvPolynomial

theorem eval_grouped {σ K L : Type*} [Field K] [Field L]
    (f : K →+* L) (x : Option σ → L) (p : MvPolynomial (Option σ) K) :
    eval₂Hom (Polynomial.eval₂RingHom f (x none)) (fun i => x (some i))
      (optionEquivRight K σ p) = eval₂Hom f x p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      rw [optionEquivRight_C,eval₂Hom_C,eval₂Hom_C]
      exact Polynomial.eval₂_C f (x none)
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp =>
      simp only [map_mul,hp]
      cases i with
      | none =>
          rw [optionEquivRight_X_none,eval₂Hom_C,eval₂Hom_X']
          simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
      | some i => rw [optionEquivRight_X_some,eval₂Hom_X',eval₂Hom_X']

def UnivariateBasisEntry {σ ι : Type*} (b : ι → MvPolynomial (Option σ) ℚ)
    (j : ι × Polynomial ℚ) : Prop := optionEquivRight ℚ σ (b j.1) = C j.2

/-- Exact mathematical output: choose a univariate basis entry when one exists;
otherwise take the positive real roots of the actual z-leading coefficients. -/
noncomputable def BlockAlgorithmCandidates {σ ι : Type*}
    (z : MonomialOrder σ) (b : ι → MvPolynomial (Option σ) ℚ) (a : ℝ) : Prop := by
  classical
  exact 0 < a ∧ if h : ∃ j, UnivariateBasisEntry b j then
    (Classical.choose h).2.eval₂ (algebraMap ℚ ℝ) a = 0
  else ∃ i, (z.leadingCoeff (optionEquivRight ℚ σ (b i))).eval₂ (algebraMap ℚ ℝ) a = 0

def CoordinateCandidateAt {σ : Type*} (I : Ideal (MvPolynomial (Option σ) ℝ))
    (a : ℝ) : Prop :=
  X none - C a ∈ I ∨ ∃ p, p ∉ I ∧ (X none - C a)*p ∈ I

/-- Both branches of the corrected algorithm cover nonvacuous coordinate
candidates of the original ideal, using its rational input block basis. -/
theorem block_algorithm_complete {σ ι : Type*} [Fintype ι]
    (full : MonomialOrder (Option σ)) (z : MonomialOrder σ)
    (hblock : BlockCompatible full z) (I : Ideal (MvPolynomial (Option σ) ℚ))
    (b : ι → MvPolynomial (Option σ) ℚ)
    (hcover : HasLeadingCover full I b) (hgen : ∀ i, b i ∈ I)
    (a : ℝ) (ha : 0 < a) (x : Option σ → ℝ) (hxa : x none = a)
    (hx : ∀ p ∈ I.map (map (algebraMap ℚ ℝ)), eval x p = 0)
    (hc : CoordinateCandidateAt (I.map (map (algebraMap ℚ ℝ))) a) :
    BlockAlgorithmCandidates z b a := by
  classical
  refine ⟨ha,?_⟩
  change (if h : ∃ j, UnivariateBasisEntry b j then _ else _)
  split_ifs with h
  · let j := Classical.choose h
    have hj : optionEquivRight ℚ σ (b j.1) = C j.2 := Classical.choose_spec h
    have hb := hx _ (Ideal.mem_map_of_mem (map (algebraMap ℚ ℝ)) (hgen j.1))
    have he := eval_grouped (algebraMap ℚ ℝ) x (b j.1)
    rw [hj,eval₂Hom_C,hxa] at he
    change j.2.eval₂ (algebraMap ℚ ℝ) a = eval₂Hom (algebraMap ℚ ℝ) x (b j.1) at he
    change j.2.eval₂ (algebraMap ℚ ℝ) a = 0
    rw [he]
    simpa only [eval_map] using hb
  · have hone : (1 : MvPolynomial (Option σ) ℝ) ∉ I.map (map (algebraMap ℚ ℝ)) := by
      intro h1
      have hh := hx 1 h1
      simp at hh
    rcases hc with hm | ⟨p,hp,ht⟩
    · exact block_extension_torsion_candidate full z hblock I b hcover hgen a 1 hone
        (by simpa using hm)
    · exact block_extension_torsion_candidate full z hblock I b hcover hgen a p hp ht

end ACRZeroDivisors
