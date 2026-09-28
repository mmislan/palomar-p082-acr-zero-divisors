module

public import proofs.ACRZeroDivisors.MassActionCompleteness
public import proofs.ACRZeroDivisors.BlockOrder

@[expose] public section

/-!
# A non-degenerate application of `mass_action_block_algorithm_complete`

The network is the two-species Shinar–Feinberg-type system

  `A + B → 2B` (rate 1),   `B → A` (rate 1),

with species `A = 0` and `B = 1`. Its field is `ẋ_A = x_B (1 - x_A)`,
`ẋ_B = -x_B (1 - x_A)`, so the network has nonvacuous ACR in `A` with value `1`.
The ACR value is a zero-divisor value of the steady-state ideal: `X_A - 1` is not
in the ideal, but `(X_A - 1) X_B` is, while `X_B` is not.

`A` is sent to the distinguished variable `none` and `B` to `some 0`. The full
order is the block order `blockOrder lex` (the `B`-block is compared first), and
the one-element basis is the NONZERO polynomial `X_B (1 - X_A)`, which generates the
renamed rational ideal, so it is a genuine (reduced up to sign) Gröbner basis.

We prove that every hypothesis of `mass_action_block_algorithm_complete`, including
`_hb0`, holds, apply the theorem to obtain that `1` is returned, and independently
compute that the algorithm's output on this basis is exactly `{1}`.
-/

namespace ACRZeroDivisors.ApplicabilityExample
open MvPolynomial

/-- `A + B → 2B` and `B → A`, both with rate `1`. -/
def shinarNetwork : List (Reaction 2) :=
  [⟨![1,1], ![0,2], 1⟩, ⟨![0,1], ![1,0], 1⟩]

theorem shinar_bimolecular : ∀ r ∈ shinarNetwork, Bimolecular r := by
  norm_num [shinarNetwork,Bimolecular,Fin.sum_univ_succ]

theorem shinar_field (a b : ℝ) :
    field shinarNetwork ![a,b] = ![b*(1-a),-(b*(1-a))] := by
  funext i
  fin_cases i <;> norm_num [field,shinarNetwork,Fin.prod_univ_succ] <;> ring

theorem shinar_rational_field :
    rationalPolynomialField shinarNetwork = ![X 1*(1-X 0),-(X 1*(1-X 0))] := by
  funext i
  fin_cases i <;> norm_num [rationalPolynomialField,shinarNetwork,Fin.prod_univ_succ,
    map_ofNat] <;> ring

theorem shinar_real_field :
    polynomialField shinarNetwork = ![X 1*(1-X 0),-(X 1*(1-X 0))] := by
  funext i
  fin_cases i <;> norm_num [polynomialField,shinarNetwork,Fin.prod_univ_succ,
    map_ofNat] <;> ring

/-- Species `A = 0` is the distinguished variable `none`; species `B = 1` is `some 0`. -/
def shinarEquiv : Fin 2 ≃ Option (Fin 1) where
  toFun i := if i = 0 then none else some 0
  invFun o := o.elim 0 fun _ => 1
  left_inv i := by fin_cases i <;> rfl
  right_inv o := by
    rcases o with _ | j
    · rfl
    · fin_cases j; rfl

theorem shinarEquiv_symm_none : shinarEquiv.symm none = 0 := rfl

/-- The `B`-block order: `z` on the `B` variable, then the exponent of `A`. -/
noncomputable def zOrder : MonomialOrder (Fin 1) := MonomialOrder.lex

noncomputable def fullOrder : MonomialOrder (Option (Fin 1)) := blockOrder zOrder

/-- The nonzero one-element basis `X_B (1 - X_A)`. -/
noncomputable def shinarBasis : Unit → MvPolynomial (Option (Fin 1)) ℚ :=
  fun _ => X (some 0)*(1-X none)

theorem shinarBasis_ne_zero : ∀ i, shinarBasis i ≠ 0 := by
  intro i h
  have h' := congrArg (eval fun o : Option (Fin 1) => o.elim (0 : ℚ) fun _ => 1) h
  simp [shinarBasis] at h'

theorem rename_generator :
    rename shinarEquiv (X 1*(1-X 0) : MvPolynomial (Fin 2) ℚ) = shinarBasis () := by
  simp only [shinarBasis,map_mul,map_sub,map_one,rename_X]
  rfl

theorem shinar_renamed_ideal_le :
    (rationalSteadyIdeal shinarNetwork).map (rename shinarEquiv).toRingHom ≤
      Ideal.span {shinarBasis ()} := by
  rw [Ideal.map_le_iff_le_comap,rationalSteadyIdeal,Ideal.span_le]
  rintro _ ⟨i,rfl⟩
  rw [SetLike.mem_coe,Ideal.mem_comap,shinar_rational_field]
  fin_cases i
  · change rename shinarEquiv (X 1*(1-X 0)) ∈ _
    rw [rename_generator]
    exact Ideal.mem_span_singleton_self _
  · change rename shinarEquiv (-(X 1*(1-X 0))) ∈ _
    rw [map_neg,rename_generator]
    exact neg_mem (Ideal.mem_span_singleton_self _)

theorem shinar_gen :
    ∀ i, shinarBasis i ∈ (rationalSteadyIdeal shinarNetwork).map
      (rename shinarEquiv).toRingHom := by
  intro i
  rw [← rename_generator]
  have h : (X 1*(1-X 0) : MvPolynomial (Fin 2) ℚ) ∈ rationalSteadyIdeal shinarNetwork :=
    Ideal.subset_span ⟨0,by rw [shinar_rational_field]; rfl⟩
  exact Ideal.mem_map_of_mem (rename shinarEquiv).toRingHom h

/-- The leading-cover (Gröbner) condition, with a nonzero basis element. -/
theorem shinar_cover :
    HasLeadingCover fullOrder
      ((rationalSteadyIdeal shinarNetwork).map (rename shinarEquiv).toRingHom)
      shinarBasis := by
  intro p hp hp0
  obtain ⟨q,rfl⟩ := Ideal.mem_span_singleton'.mp (shinar_renamed_ideal_le hp)
  have hq : q ≠ 0 := left_ne_zero_of_mul hp0
  refine ⟨(),?_⟩
  rw [fullOrder.degree_mul hq (shinarBasis_ne_zero ())]
  exact le_add_self

theorem shinar_positive : PositiveSteady shinarNetwork ![1,1] := by
  constructor
  · intro i; fin_cases i <;> norm_num
  · intro i; rw [shinar_field]; fin_cases i <;> norm_num

theorem shinar_acr : NonvacuousACR shinarNetwork (shinarEquiv.symm none) 1 := by
  rw [shinarEquiv_symm_none]
  refine ⟨⟨_,shinar_positive⟩,fun x hx => ?_⟩
  have heq : x = ![x 0,x 1] := by
    funext i; fin_cases i <;> rfl
  have hf := hx.2 0
  rw [heq,shinar_field] at hf
  have hb : x 1 ≠ 0 := (hx.1 1).ne'
  have h1 : 1-x 0 = 0 := by
    simpa [hb] using hf
  linarith

/-- The ACR value `1` is a zero-divisor coordinate candidate. -/
theorem shinar_candidate :
    SpeciesCoordinateCandidate (steadyIdeal shinarNetwork) (shinarEquiv.symm none) 1 := by
  rw [shinarEquiv_symm_none]
  right
  refine ⟨X 1,fun h => ?_,?_⟩
  · have h0 := positive_steady_annihilates_ideal shinarNetwork _ shinar_positive _ h
    simp at h0
  · have h0 : polynomialField shinarNetwork 0 ∈ steadyIdeal shinarNetwork :=
      Ideal.subset_span ⟨0,rfl⟩
    have h1 := (steadyIdeal shinarNetwork).neg_mem h0
    convert h1 using 1
    rw [shinar_real_field]
    simp only [Matrix.cons_val_zero,map_one]
    ring

/-- The ACR value is not a plain coordinate value: `X_A - 1` is not in the ideal. -/
theorem shinar_not_coordinate :
    (X 0-C 1 : MvPolynomial (Fin 2) ℝ) ∉ steadyIdeal shinarNetwork := by
  intro h
  have hle : steadyIdeal shinarNetwork ≤ RingHom.ker (eval ![(5 : ℝ),0]) := by
    rw [steadyIdeal,Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    rw [SetLike.mem_coe,RingHom.mem_ker,eval_polynomial_field,shinar_field]
    fin_cases i <;> simp
  have h0 := hle h
  rw [RingHom.mem_ker] at h0
  norm_num at h0

/-- All hypotheses of `mass_action_block_algorithm_complete` hold for this concrete,
non-degenerate instance (nonzero basis, genuine leading cover, nonvacuous ACR,
zero-divisor candidate). -/
theorem shinar_hypotheses :
    BlockCompatible fullOrder zOrder ∧
    (∀ i, shinarBasis i ≠ 0) ∧
    HasLeadingCover fullOrder
      ((rationalSteadyIdeal shinarNetwork).map (rename shinarEquiv).toRingHom)
      shinarBasis ∧
    (∀ i, shinarBasis i ∈ (rationalSteadyIdeal shinarNetwork).map
      (rename shinarEquiv).toRingHom) ∧
    NonvacuousACR shinarNetwork (shinarEquiv.symm none) 1 ∧
    SpeciesCoordinateCandidate (steadyIdeal shinarNetwork) (shinarEquiv.symm none) 1 :=
  ⟨blockOrder_compatible zOrder,shinarBasis_ne_zero,shinar_cover,shinar_gen,
    shinar_acr,shinar_candidate⟩

/-- The selected theorem applied to the instance: the ACR value `1` is returned. -/
theorem shinar_algorithm_returns_acr_value :
    BlockAlgorithmCandidates zOrder shinarBasis 1 :=
  mass_action_block_algorithm_complete shinarNetwork shinarEquiv fullOrder zOrder
    (blockOrder_compatible zOrder) shinarBasis shinarBasis_ne_zero shinar_cover shinar_gen
    1 shinar_acr shinar_candidate

theorem shinar_grouped_basis :
    optionEquivRight ℚ (Fin 1) (shinarBasis ()) = X 0*C (1-Polynomial.X) := by
  simp [shinarBasis]

theorem shinar_no_univariate_entry : ¬ ∃ j, UnivariateBasisEntry shinarBasis j := by
  rintro ⟨⟨⟨⟩,f⟩,hj⟩
  change optionEquivRight ℚ (Fin 1) (shinarBasis ()) = C f at hj
  rw [shinar_grouped_basis] at hj
  have h0 := congrArg (eval fun _ : Fin 1 => (0 : Polynomial ℚ)) hj
  have h1 := congrArg (eval fun _ : Fin 1 => (1 : Polynomial ℚ)) hj
  simp only [map_mul,eval_X,eval_C,zero_mul,one_mul] at h0 h1
  have h2 := congrArg (Polynomial.eval (0 : ℚ)) (h1.trans h0.symm)
  simp at h2

/-- Independent check: on this basis the algorithm's output is exactly `{1}`. -/
theorem shinar_algorithm_output (a : ℝ) :
    BlockAlgorithmCandidates zOrder shinarBasis a ↔ a = 1 := by
  unfold BlockAlgorithmCandidates
  split_ifs with h
  · exact absurd h shinar_no_univariate_entry
  have hlc : zOrder.leadingCoeff (optionEquivRight ℚ (Fin 1) (shinarBasis ())) =
      1-Polynomial.X := by
    rw [shinar_grouped_basis,MonomialOrder.leadingCoeff_mul,MonomialOrder.leadingCoeff_X,
      MonomialOrder.leadingCoeff_C,one_mul]
  constructor
  · rintro ⟨_,⟨⟩,hi⟩
    rw [hlc] at hi
    simp only [Polynomial.eval₂_sub,Polynomial.eval₂_one,Polynomial.eval₂_X] at hi
    linarith
  · rintro rfl
    refine ⟨one_pos,(),?_⟩
    rw [hlc]
    simp

end ACRZeroDivisors.ApplicabilityExample
