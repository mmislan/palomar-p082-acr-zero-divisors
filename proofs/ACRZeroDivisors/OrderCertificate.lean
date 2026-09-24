import proofs.ACRZeroDivisors.OrderNormalForm
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.MvPolynomial.CommRing

namespace ACRZeroDivisors.OrderWitness
open MvPolynomial

@[simp] theorem fin3_ne20 : (2 : Fin 3) ≠ 0 := by decide
@[simp] theorem fin3_ne21 : (2 : Fin 3) ≠ 1 := by decide
@[simp] theorem fin3_ne02 : (0 : Fin 3) ≠ 2 := by decide
@[simp] theorem fin3_ne12 : (1 : Fin 3) ≠ 2 := by decide

def mixedKey (e : Exponent) : ℕ ×ₗ (ℕ ×ₗ ℕ) := toLex (zDegree e,toLex (e 2,e 0))

theorem mixedKey_lt (e f : Exponent) : mixedKey e < mixedKey f ↔ MixedLT e f := by
  simp only [mixedKey,Prod.Lex.toLex_lt_toLex,MixedLT]

theorem mixedKey_injective : Function.Injective mixedKey := by
  intro e f h
  have hz : zDegree e = zDegree f := congrArg (fun x => (ofLex x).1) h
  have ht : e 2 = f 2 := congrArg (fun x => (ofLex ((ofLex x).2)).1) h
  have hu : e 0 = f 0 := congrArg (fun x => (ofLex ((ofLex x).2)).2) h
  ext i
  fin_cases i
  · exact hu
  · change e 1 = f 1
    dsimp [zDegree] at hz; omega
  · exact ht

theorem mixed_wellFounded : WellFounded MixedLT := by
  have h := InvImage.wf mixedKey
    (wellFounded_lt : WellFounded ((· < ·) : (ℕ ×ₗ (ℕ ×ₗ ℕ)) → _ → Prop))
  exact h.mono (fun e f hef => (mixedKey_lt e f).mpr hef)

theorem mixed_trichotomy (e f : Exponent) : MixedLT e f ∨ e = f ∨ MixedLT f e := by
  rcases lt_trichotomy (mixedKey e) (mixedKey f) with h | h | h
  · exact Or.inl ((mixedKey_lt e f).mp h)
  · exact Or.inr (Or.inl (mixedKey_injective h))
  · exact Or.inr (Or.inr ((mixedKey_lt f e).mp h))

theorem leading_exists (p : P) (hp : p ≠ 0) : ∃ e, IsLeading e p := by
  classical
  have hn : p.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by simpa using hp)
  obtain ⟨e,he,hmax⟩ := p.support.exists_max_image mixedKey hn
  refine ⟨e,mem_support_iff.mp he,?_⟩
  intro d hd
  rcases lt_or_eq_of_le (hmax d hd) with h | h
  · exact Or.inr ((mixedKey_lt d e).mp h)
  · exact Or.inl (mixedKey_injective h)

noncomputable def L1 : Exponent := Finsupp.single 0 2
noncomputable def L2 : Exponent := Finsupp.single 0 1+Finsupp.single 2 1
noncomputable def L3 : Exponent := Finsupp.single 1 1+Finsupp.single 2 1

theorem nonstandard_divisible (e : Exponent) (he : ¬ Standard e) :
    L1 ≤ e ∨ L2 ≤ e ∨ L3 ≤ e := by
  by_cases hu : 2 ≤ e 0
  · exact Or.inl (Finsupp.single_le_iff.mpr hu)
  · have ht : 1 ≤ e 2 := by dsimp [Standard,zDegree] at he; omega
    have hz : 1 ≤ e 0+e 1 := by dsimp [Standard,zDegree] at he; omega
    by_cases hu0 : 1 ≤ e 0
    · right; left
      intro i
      fin_cases i
      · change L2 0 ≤ e 0
        simpa [L2] using hu0
      · change L2 1 ≤ e 1
        simp [L2]
      · change L2 2 ≤ e 2
        simpa [L2] using ht
    · right; right
      have hv : 1 ≤ e 1 := by omega
      intro i
      fin_cases i
      · change L3 0 ≤ e 0
        simp [L3]
      · change L3 1 ≤ e 1
        simpa [L3] using hv
      · change L3 2 ≤ e 2
        simpa [L3] using ht

theorem basis_groebner_property (p : P) (hp : p ∈ basisIdeal) (hne : p ≠ 0) :
    ∃ e, IsLeading e p ∧ (L1 ≤ e ∨ L2 ≤ e ∨ L3 ≤ e) := by
  obtain ⟨e,he⟩ := leading_exists p hne
  exact ⟨e,he,nonstandard_divisible e (basisIdeal_leading_not_standard hp he)⟩

theorem binomial_leading (l r : Exponent) (h : MixedLT r l) :
    IsLeading l (monomial l 1-monomial r 1 : P) := by
  have hne : l ≠ r := by intro he; subst r; exact mixed_irrefl l h
  constructor
  · simp [coeff_monomial,hne.symm]
  · intro d hd
    by_cases hdl : d = l
    · exact Or.inl hdl
    · have hdr : d = r := by
        by_contra hdr
        have hz : ((monomial l 1-monomial r 1 : P)).coeff d = 0 := by
          simp [coeff_monomial,Ne.symm hdl,Ne.symm hdr]
        exact (mem_support_iff.mp hd) hz
      subst d
      exact Or.inr h

theorem b1_leading : IsLeading L1 b1 := by
  apply binomial_leading
  norm_num [MixedLT,zDegree,L1,Finsupp.single_apply]

theorem b2_leading : IsLeading L2 b2 := by
  apply binomial_leading
  norm_num [MixedLT,zDegree,L2,Finsupp.single_apply]

theorem b3_leading : IsLeading L3 b3 := by
  apply binomial_leading
  norm_num [MixedLT,zDegree,L3,Finsupp.single_apply]

end ACRZeroDivisors.OrderWitness
