import proofs.ACRZeroDivisors.PositiveLoci
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace ACRZeroDivisors

@[simp] theorem vec3_two {α : Type*} (a b c : α) : (![a,b,c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vec4_two {α : Type*} (a b c d : α) : (![a,b,c,d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vec4_three {α : Type*} (a b c d : α) : (![a,b,c,d] : Fin 4 → α) 3 = d := rfl

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

def orderNetwork : List (Reaction 3) :=
  [⟨![1,1,0], ![1,0,0], 1⟩, ⟨![0,0,1], ![0,1,1], 1⟩,
   ⟨![0,1,0], ![0,1,1], 1⟩, ⟨![1,0,1], ![1,0,0], 1⟩]

theorem necessity_bimolecular : ∀ r ∈ necessityNetwork, Bimolecular r := by
  norm_num [necessityNetwork, Bimolecular, Fin.sum_univ_succ]

theorem sufficiency_bimolecular : ∀ r ∈ sufficiencyNetwork, Bimolecular r := by
  norm_num [sufficiencyNetwork, Bimolecular, Fin.sum_univ_succ]

theorem order_bimolecular : ∀ r ∈ orderNetwork, Bimolecular r := by
  norm_num [orderNetwork, Bimolecular, Fin.sum_univ_succ]

theorem necessity_field (a b c : ℝ) :
    field necessityNetwork ![a,b,c] = ![-a*b+b-a*c+3*c, a*b-2*b, a*c-3*c+b] := by
  funext i
  fin_cases i <;> norm_num [field, necessityNetwork, Fin.prod_univ_succ] <;> ring

theorem sufficiency_field (a b c d : ℝ) :
    field sufficiencyNetwork ![a,b,c,d] =
      ![-a^2+c+d-a*b+b-a, d-b^2, a^2-c, c-d] := by
  funext i
  fin_cases i <;> norm_num [field, sufficiencyNetwork, Fin.prod_univ_succ] <;> ring

theorem order_field (t u v : ℝ) :
    field orderNetwork ![t,u,v] = ![0, v-t*u, u-t*v] := by
  funext i
  fin_cases i <;> norm_num [field, orderNetwork, Fin.prod_univ_succ] <;> ring

end ACRZeroDivisors



