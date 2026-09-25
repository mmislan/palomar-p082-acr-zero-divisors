import proofs.ACRZeroDivisors.BlockGrouping
import Mathlib.Algebra.Order.Monoid.Lex
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Data.Prod.Lex

namespace ACRZeroDivisors

/-- Extend any z-monomial order by comparing the distinguished exponent last. -/
noncomputable def blockOrder {σ : Type*} (z : MonomialOrder σ) :
    MonomialOrder (Option σ) where
  syn := z.syn ×ₗ ℕ
  toSyn :=
    { toFun := fun d => toLex (z.toSyn d.some,d none)
      invFun := fun d => (z.toSyn.symm (ofLex d).1).optionElim (ofLex d).2
      left_inv := by intro d; simp
      right_inv := by intro d; simp
      map_add' := by intro d e; simp [Finsupp.some_add]; rfl }
  toSyn_monotone := by
    intro d e h
    apply Prod.Lex.toLex_le_toLex'.mpr
    exact ⟨z.toSyn_monotone (fun i => h (some i)),fun _ => h none⟩

theorem blockOrder_compatible {σ : Type*} (z : MonomialOrder σ) :
    BlockCompatible (blockOrder z) z := by
  intro d e h
  exact Prod.Lex.monotone_fst _ _ h

end ACRZeroDivisors
