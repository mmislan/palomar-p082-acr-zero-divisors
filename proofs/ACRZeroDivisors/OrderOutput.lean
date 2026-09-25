import proofs.ACRZeroDivisors.OrderCertificate
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace ACRZeroDivisors.OrderWitness
open MvPolynomial

def zKey (e : Exponent) : ℕ ×ₗ ℕ := toLex (zDegree e,e 0)

noncomputable def tCoefficient (a b : ℕ) : P →ₗ[ℚ] Polynomial ℚ :=
  (Finsupp.linearCombination ℚ (fun e : Exponent =>
    if e 0=a ∧ e 1=b then Polynomial.X^(e 2) else 0)).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

theorem tCoefficient_monomial (a b : ℕ) (e : Exponent) (c : ℚ) :
    tCoefficient a b (monomial e c) =
      c • (if e 0=a ∧ e 1=b then Polynomial.X^(e 2) else 0) := by
  exact Finsupp.linearCombination_single _ _ _

noncomputable def leadingCoefficientZ (p : P) : Polynomial ℚ :=
  if h : p.support.Nonempty then
    let e := Classical.choose (p.support.exists_max_image zKey h)
    tCoefficient (e 0) (e 1) p
  else 0

theorem leadingCoefficientZ_eq (p : P) (e : Exponent) (he : e ∈ p.support)
    (hmax : ∀ d ∈ p.support, zKey d ≤ zKey e) :
    leadingCoefficientZ p = tCoefficient (e 0) (e 1) p := by
  classical
  have hn : p.support.Nonempty := ⟨e,he⟩
  rw [leadingCoefficientZ,dite_eq_left hn]
  let d := Classical.choose (p.support.exists_max_image zKey hn)
  have hd := Classical.choose_spec (p.support.exists_max_image zKey hn)
  have hk : zKey d = zKey e := le_antisymm (hmax d hd.1) (hd.2 e he)
  have hu : d 0 = e 0 := congrArg (fun x => (ofLex x).2) hk
  have hz : zDegree d = zDegree e := congrArg (fun x => (ofLex x).1) hk
  have hv : d 1 = e 1 := by dsimp [zDegree] at hz; omega
  change tCoefficient (d 0) (d 1) p = _
  rw [hu,hv]

theorem support_binomial {l r : Exponent} {d : Exponent}
    (hd : d ∈ (monomial l 1-monomial r 1 : P).support) : d=l ∨ d=r := by
  by_contra h
  have hl : d ≠ l := fun hdl => h (Or.inl hdl)
  have hr : d ≠ r := fun hdr => h (Or.inr hdr)
  have hz : ((monomial l 1-monomial r 1 : P)).coeff d = 0 := by
    simp [coeff_monomial,Ne.symm hl,Ne.symm hr]
  exact (mem_support_iff.mp hd) hz

theorem b1_lcZ : leadingCoefficientZ b1 = 1 := by
  rw [leadingCoefficientZ_eq b1 L1 (mem_support_iff.mpr b1_leading.1)]
  · norm_num [b1,L1,map_sub,tCoefficient_monomial]
  · intro d hd
    rcases support_binomial hd with rfl | rfl
    · exact le_rfl
    · norm_num [zKey,zDegree,L1,Prod.Lex.toLex_le_toLex]

theorem b2_lcZ : leadingCoefficientZ b2 = Polynomial.X := by
  rw [leadingCoefficientZ_eq b2 L2 (mem_support_iff.mpr b2_leading.1)]
  · norm_num [b2,L2,map_sub,tCoefficient_monomial]
  · intro d hd
    rcases support_binomial hd with rfl | rfl
    · exact le_rfl
    · norm_num [zKey,zDegree,L2,Prod.Lex.toLex_le_toLex]

theorem b3_lcZ : leadingCoefficientZ b3 = -1 := by
  have hne : (Finsupp.single 1 1+Finsupp.single 2 1 : Exponent) ≠ Finsupp.single 0 1 := by
    intro h
    have hh := congrArg (fun e : Exponent => e 0) h
    norm_num at hh
  have he : Finsupp.single 0 1 ∈ b3.support := by
    rw [mem_support_iff]
    norm_num [b3,coeff_monomial,hne]
  rw [leadingCoefficientZ_eq b3 (Finsupp.single 0 1) he]
  · norm_num [b3,map_sub,tCoefficient_monomial]
  · intro d hd
    rcases support_binomial hd with rfl | rfl
    · norm_num [zKey,zDegree,Prod.Lex.toLex_le_toLex]
    · exact le_rfl

def PureT (p : P) : Prop := ∀ e ∈ p.support, zDegree e = 0

theorem basis_no_pureT (p : P) (hp : p ∈ ({b1,b2,b3} : Set P)) : ¬ PureT p := by
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · intro h
    have hh := h L1 (mem_support_iff.mpr b1_leading.1)
    norm_num [L1,zDegree] at hh
  · intro h
    have hh := h L2 (mem_support_iff.mpr b2_leading.1)
    norm_num [L2,zDegree] at hh
  · intro h
    have hh := h L3 (mem_support_iff.mpr b3_leading.1)
    norm_num [L3,zDegree] at hh

end ACRZeroDivisors.OrderWitness
