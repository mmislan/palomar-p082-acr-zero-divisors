module

public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finsupp.Order
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Polynomial.Eval.Algebra

@[expose] public section

/-! Challenge definitions of P082, verbatim and in Challenge order, shared by the proof
modules so that auxiliary declarations are generated exactly as in the one-module Challenge. -/

namespace ACRZeroDivisors
open MvPolynomial

structure Reaction (n : ℕ) where
  source : Fin n → ℕ
  target : Fin n → ℕ
  rate : ℚ

def Bimolecular {n : ℕ} (r : Reaction n) : Prop :=
  (∑ i, r.source i) ≤ 2 ∧ (∑ i, r.target i) ≤ 2 ∧ 0 < r.rate

def field {n : ℕ} (rs : List (Reaction n)) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (rs.map fun r => (r.rate : ℝ) * (∏ j, x j ^ r.source j) *
    ((r.target i : ℝ) - (r.source i : ℝ))).sum

def necessityNetwork : List (Reaction 3) :=
  [⟨![1,1,0], ![0,2,0], 1⟩, ⟨![0,1,0], ![1,0,0], 1⟩,
   ⟨![0,1,0], ![0,0,1], 1⟩, ⟨![1,0,1], ![0,0,2], 1⟩,
   ⟨![0,0,1], ![1,0,0], 3⟩]

def sufficiencyNetwork : List (Reaction 4) :=
  [⟨![2,0,0,0], ![1,0,1,0], 1⟩, ⟨![0,0,1,0], ![1,0,0,1], 1⟩,
   ⟨![0,0,0,1], ![1,1,0,0], 1⟩, ⟨![1,1,0,0], ![0,1,0,0], 1⟩,
   ⟨![0,1,0,0], ![1,1,0,0], 1⟩, ⟨![1,0,0,0], ![0,0,0,0], 1⟩,
   ⟨![0,2,0,0], ![0,0,0,0], 1/2⟩]

abbrev Poly3 := MvPolynomial (Fin 3) ℝ

def CoordinateCandidate (I : Ideal Poly3) (alpha : ℝ) : Prop :=
  X 0 - C alpha ∈ I ∨
    (X 0 - C alpha ∉ I ∧ ∃ h : Poly3, h ∉ I ∧ (X 0 - C alpha)*h ∈ I)

noncomputable def polynomialField {n : ℕ} (rs : List (Reaction n))
    (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  (rs.map fun r => C (r.rate : ℝ) * (∏ j, X j ^ r.source j) *
    (C (r.target i : ℝ) - C (r.source i : ℝ))).sum

noncomputable def steadyIdeal {n : ℕ} (rs : List (Reaction n)) :
    Ideal (MvPolynomial (Fin n) ℝ) := Ideal.span (Set.range (polynomialField rs))

def PositiveSteady {n : ℕ} (rs : List (Reaction n)) (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 < x i) ∧ ∀ i, field rs x i = 0

def NonvacuousACR {n : ℕ} (rs : List (Reaction n)) (i : Fin n) (alpha : ℝ) : Prop :=
  (∃ x, PositiveSteady rs x) ∧ ∀ x, PositiveSteady rs x → x i = alpha

abbrev Poly4 := MvPolynomial (Fin 4) ℝ

def CoordinateCandidate4 (I : Ideal Poly4) (alpha : ℝ) : Prop :=
  X 0-C alpha ∈ I ∨
    (X 0-C alpha ∉ I ∧ ∃ h : Poly4, h ∉ I ∧ (X 0-C alpha)*h ∈ I)

noncomputable def rationalPolynomialField {n : ℕ} (rs : List (Reaction n))
    (i : Fin n) : MvPolynomial (Fin n) ℚ :=
  (rs.map fun r => C r.rate * (∏ j, X j ^ r.source j) *
    (C (r.target i : ℚ) - C (r.source i : ℚ))).sum

noncomputable def rationalSteadyIdeal {n : ℕ} (rs : List (Reaction n)) :
    Ideal (MvPolynomial (Fin n) ℚ) := Ideal.span (Set.range (rationalPolynomialField rs))

def HasLeadingCover {σ R ι : Type*} [CommRing R]
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ R))
    (b : ι → MvPolynomial σ R) : Prop :=
  ∀ p ∈ I, p ≠ 0 → ∃ i, m.degree (b i) ≤ m.degree p

def BlockCompatible {σ : Type*} (full : MonomialOrder (Option σ))
    (z : MonomialOrder σ) : Prop :=
  ∀ d e, full.toSyn d ≤ full.toSyn e → z.toSyn d.some ≤ z.toSyn e.some

def UnivariateBasisEntry {σ ι : Type*} (b : ι → MvPolynomial (Option σ) ℚ)
    (j : ι × Polynomial ℚ) : Prop := optionEquivRight ℚ σ (b j.1) = C j.2

noncomputable def BlockAlgorithmCandidates {σ ι : Type*}
    (z : MonomialOrder σ) (b : ι → MvPolynomial (Option σ) ℚ) (a : ℝ) : Prop := by
  classical
  exact 0 < a ∧ if h : ∃ j, UnivariateBasisEntry b j then
    (Classical.choose h).2.eval₂ (algebraMap ℚ ℝ) a = 0
  else ∃ i, (z.leadingCoeff (optionEquivRight ℚ σ (b i))).eval₂ (algebraMap ℚ ℝ) a = 0

def SpeciesCoordinateCandidate {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℝ))
    (i : Fin n) (a : ℝ) : Prop :=
  X i - C a ∈ I ∨ ∃ p, p ∉ I ∧ (X i - C a)*p ∈ I

end ACRZeroDivisors

namespace ACRZeroDivisors.OrderWitness
open MvPolynomial

abbrev Exponent := Fin 3 →₀ ℕ

def zDegree (e : Exponent) : ℕ := e 0+e 1

def MixedLT (e f : Exponent) : Prop :=
  zDegree e < zDegree f ∨ (zDegree e = zDegree f ∧
    (e 2 < f 2 ∨ (e 2 = f 2 ∧ e 0 < f 0)))

abbrev P := MvPolynomial (Fin 3) ℚ

noncomputable def b1 : P := monomial (Finsupp.single 0 2) 1-monomial (Finsupp.single 1 2) 1

noncomputable def b2 : P :=
  monomial (Finsupp.single 0 1+Finsupp.single 2 1) 1-monomial (Finsupp.single 1 1) 1

noncomputable def b3 : P :=
  monomial (Finsupp.single 1 1+Finsupp.single 2 1) 1-monomial (Finsupp.single 0 1) 1

noncomputable def basisIdeal : Ideal P := Ideal.span {b1,b2,b3}

def IsLeading (e : Exponent) (p : P) : Prop :=
  (p).coeff e ≠ 0 ∧ ∀ d ∈ p.support, d = e ∨ MixedLT d e

noncomputable def L1 : Exponent := Finsupp.single 0 2

noncomputable def L2 : Exponent := Finsupp.single 0 1+Finsupp.single 2 1

noncomputable def L3 : Exponent := Finsupp.single 1 1+Finsupp.single 2 1

def zKey (e : Exponent) : ℕ ×ₗ ℕ := toLex (zDegree e,e 0)

noncomputable def tCoefficient (a b : ℕ) : P →ₗ[ℚ] Polynomial ℚ :=
  (Finsupp.linearCombination ℚ (fun e : Exponent =>
    if e 0=a ∧ e 1=b then Polynomial.X^(e 2) else 0)).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

noncomputable def leadingCoefficientZ (p : P) : Polynomial ℚ :=
  if h : p.support.Nonempty then
    let e := Classical.choose (p.support.exists_max_image zKey h)
    tCoefficient (e 0) (e 1) p
  else 0

def PureT (p : P) : Prop := ∀ e ∈ p.support, zDegree e = 0

def witnessNetwork : List (Reaction 3) :=
  [⟨![1,0,1], ![0,0,1], 1⟩, ⟨![0,1,0], ![1,1,0], 1⟩,
   ⟨![1,0,0], ![1,1,0], 1⟩, ⟨![0,1,1], ![0,0,1], 1⟩]

noncomputable def polynomialFieldQ {n : ℕ} (rs : List (Reaction n))
    (i : Fin n) : MvPolynomial (Fin n) ℚ :=
  (rs.map fun r => C r.rate * (∏ j, X j^r.source j) *
    (C (r.target i : ℚ)-C (r.source i : ℚ))).sum

noncomputable def rationalSteadyIdeal {n : ℕ} (rs : List (Reaction n)) :
    Ideal (MvPolynomial (Fin n) ℚ) := Ideal.span (Set.range (polynomialFieldQ rs))

noncomputable def univariateT (p : P) : Polynomial ℚ :=
  eval₂Hom Polynomial.C ![0,0,Polynomial.X] p

noncomputable def AlgorithmCandidates (G : Set P) (alpha : ℝ) : Prop := by
  classical
  exact 0 < alpha ∧
  if ∃ g ∈ G, PureT g then
    ∃ g ∈ G, PureT g ∧ Polynomial.eval₂ (Rat.castHom ℝ) alpha (univariateT g) = 0
  else
    ∃ g ∈ G, Polynomial.eval₂ (Rat.castHom ℝ) alpha (leadingCoefficientZ g) = 0

def AdmissibleEliminationOrder : Prop :=
  WellFounded MixedLT ∧
  (∀ e, ¬ MixedLT e e) ∧
  (∀ e f g, MixedLT e f → MixedLT f g → MixedLT e g) ∧
  (∀ e f, MixedLT e f ∨ e=f ∨ MixedLT f e) ∧
  (∀ e f h, MixedLT (e+h) (f+h) ↔ MixedLT e f) ∧
  (∀ e, ¬ MixedLT e 0) ∧
  (∀ p e, IsLeading e p → zDegree e=0 → PureT p)

def ReducedBasisCertificate (I : Ideal P) : Prop :=
  I = basisIdeal ∧
  IsLeading L1 b1 ∧ IsLeading L2 b2 ∧ IsLeading L3 b3 ∧
  ((b1).coeff L1 = 1 ∧ (b2).coeff L2 = 1 ∧ (b3).coeff L3 = 1) ∧
  (∀ p ∈ I, p ≠ 0 → ∃ e, IsLeading e p ∧ (L1 ≤ e ∨ L2 ≤ e ∨ L3 ≤ e)) ∧
  (∀ e ∈ b1.support, e ≠ L1 → ¬ L1 ≤ e ∧ ¬ L2 ≤ e ∧ ¬ L3 ≤ e) ∧
  (∀ e ∈ b2.support, e ≠ L2 → ¬ L1 ≤ e ∧ ¬ L2 ≤ e ∧ ¬ L3 ≤ e) ∧
  (∀ e ∈ b3.support, e ≠ L3 → ¬ L1 ≤ e ∧ ¬ L2 ≤ e ∧ ¬ L3 ≤ e) ∧
  (¬ L1 ≤ L2 ∧ ¬ L1 ≤ L3 ∧ ¬ L2 ≤ L1 ∧ ¬ L2 ≤ L3 ∧ ¬ L3 ≤ L1 ∧ ¬ L3 ≤ L2)

end ACRZeroDivisors.OrderWitness
