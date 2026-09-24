import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

namespace ACRZeroDivisors.OrderWitness

abbrev Exponent := Fin 3 →₀ ℕ

def zDegree (e : Exponent) : ℕ := e 0+e 1
def parity (e : Exponent) : ℕ := (e 0+e 2)%2
noncomputable def normalExponent (e : Exponent) : Exponent :=
  if zDegree e = 0 then e else
    Finsupp.single 0 (parity e) + Finsupp.single 1 (zDegree e-parity e)

def Standard (e : Exponent) : Prop := e 0 < 2 ∧ (e 2 = 0 ∨ zDegree e = 0)

def MixedLT (e f : Exponent) : Prop :=
  zDegree e < zDegree f ∨ (zDegree e = zDegree f ∧
    (e 2 < f 2 ∨ (e 2 = f 2 ∧ e 0 < f 0)))

theorem parity_lt (e : Exponent) : parity e < 2 := Nat.mod_lt _ (by decide)

theorem normal_of_zero (e : Exponent) (h : zDegree e = 0) : normalExponent e = e := by
  rw [normalExponent,if_pos h]

theorem normal_of_nonzero (e : Exponent) (h : zDegree e ≠ 0) :
    normalExponent e = Finsupp.single 0 (parity e) + Finsupp.single 1 (zDegree e-parity e) := by
  rw [normalExponent,if_neg h]

theorem normal_zero (e : Exponent) (h : zDegree e ≠ 0) : normalExponent e 0 = parity e := by
  rw [normal_of_nonzero e h]
  simp only [Finsupp.add_apply,Finsupp.single_apply]
  norm_num

theorem normal_one (e : Exponent) (h : zDegree e ≠ 0) : normalExponent e 1 = zDegree e-parity e := by
  rw [normal_of_nonzero e h]
  simp only [Finsupp.add_apply,Finsupp.single_apply]
  norm_num

theorem normal_two (e : Exponent) (h : zDegree e ≠ 0) : normalExponent e 2 = 0 := by
  rw [normal_of_nonzero e h]
  simp only [Finsupp.add_apply,Finsupp.single_apply]
  simp only [if_neg (show (0 : Fin 3) ≠ 2 by decide),
    if_neg (show (1 : Fin 3) ≠ 2 by decide),zero_add]

theorem normal_zDegree (e : Exponent) : zDegree (normalExponent e) = zDegree e := by
  by_cases h : zDegree e = 0
  · rw [normal_of_zero e h]
  · have hp := parity_lt e
    change normalExponent e 0+normalExponent e 1 = zDegree e
    rw [normal_zero e h,normal_one e h]
    omega

theorem normal_standard (e : Exponent) : Standard (normalExponent e) := by
  by_cases h : zDegree e = 0
  · rw [normal_of_zero e h]
    exact ⟨by dsimp [zDegree] at h; omega, Or.inr h⟩
  · exact ⟨by rw [normal_zero e h]; exact parity_lt e, Or.inl (normal_two e h)⟩

theorem normal_eq_self (e : Exponent) (he : Standard e) : normalExponent e = e := by
  by_cases h : zDegree e = 0
  · exact normal_of_zero e h
  · obtain ⟨hu,ht⟩ := he
    have ht0 : e 2 = 0 := ht.resolve_right h
    have hp : parity e = e 0 := by simp [parity,ht0,Nat.mod_eq_of_lt hu]
    ext i
    fin_cases i
    · exact (normal_zero e h).trans hp
    · change normalExponent e 1 = e 1
      rw [normal_one e h,hp]
      dsimp [zDegree]
      omega
    · exact (normal_two e h).trans ht0.symm

theorem normal_strictly_lower (e : Exponent) (he : ¬ Standard e) :
    MixedLT (normalExponent e) e := by
  have hz : zDegree e ≠ 0 := by
    intro hz
    apply he
    dsimp [Standard,zDegree] at *
    exact ⟨by omega, Or.inr hz⟩
  have hp := parity_lt e
  right
  refine ⟨normal_zDegree e, ?_⟩
  rw [normal_two e hz,normal_zero e hz]
  dsimp [Standard] at he
  omega

theorem mixed_irrefl (e : Exponent) : ¬ MixedLT e e := by
  simp [MixedLT]

theorem mixed_trans {e f g : Exponent} (hef : MixedLT e f) (hfg : MixedLT f g) :
    MixedLT e g := by
  dsimp [MixedLT] at *
  omega

theorem mixed_add (e f h : Exponent) : MixedLT (e+h) (f+h) ↔ MixedLT e f := by
  simp only [MixedLT,zDegree,Finsupp.add_apply]
  omega

theorem mixed_elimination (e f : Exponent) (he : zDegree e = 0) (hf : 0 < zDegree f) :
    MixedLT e f := by
  exact Or.inl (by omega)

theorem normal_relation_u2 (e : Exponent) :
    normalExponent (e+Finsupp.single 0 2) = normalExponent (e+Finsupp.single 1 2) := by
  have h0 : zDegree (e+Finsupp.single 0 2) ≠ 0 := by simp [zDegree]
  have h1 : zDegree (e+Finsupp.single 1 2) ≠ 0 := by simp [zDegree]
  have hp : parity (e+Finsupp.single 0 2) = parity (e+Finsupp.single 1 2) := by
    simp [parity]
    omega
  have hz : zDegree (e+Finsupp.single 0 2) = zDegree (e+Finsupp.single 1 2) := by
    simp [zDegree]
    omega
  rw [normal_of_nonzero _ h0,normal_of_nonzero _ h1,hp,hz]

theorem normal_relation_tu (e : Exponent) :
    normalExponent (e+Finsupp.single 0 1+Finsupp.single 2 1) =
    normalExponent (e+Finsupp.single 1 1) := by
  have h0 : zDegree (e+Finsupp.single 0 1+Finsupp.single 2 1) ≠ 0 := by
    simp [zDegree]
  have h1 : zDegree (e+Finsupp.single 1 1) ≠ 0 := by
    simp [zDegree]
  have hp : parity (e+Finsupp.single 0 1+Finsupp.single 2 1) =
      parity (e+Finsupp.single 1 1) := by
    simp [parity]; omega
  have hz : zDegree (e+Finsupp.single 0 1+Finsupp.single 2 1) =
      zDegree (e+Finsupp.single 1 1) := by
    simp [zDegree]; omega
  rw [normal_of_nonzero _ h0,normal_of_nonzero _ h1,hp,hz]

theorem normal_relation_tv (e : Exponent) :
    normalExponent (e+Finsupp.single 1 1+Finsupp.single 2 1) =
    normalExponent (e+Finsupp.single 0 1) := by
  have h0 : zDegree (e+Finsupp.single 1 1+Finsupp.single 2 1) ≠ 0 := by
    simp [zDegree]
  have h1 : zDegree (e+Finsupp.single 0 1) ≠ 0 := by
    simp [zDegree]
  have hp : parity (e+Finsupp.single 1 1+Finsupp.single 2 1) =
      parity (e+Finsupp.single 0 1) := by
    simp [parity]; omega
  have hz : zDegree (e+Finsupp.single 1 1+Finsupp.single 2 1) =
      zDegree (e+Finsupp.single 0 1) := by
    simp [zDegree]; omega
  rw [normal_of_nonzero _ h0,normal_of_nonzero _ h1,hp,hz]

end ACRZeroDivisors.OrderWitness

