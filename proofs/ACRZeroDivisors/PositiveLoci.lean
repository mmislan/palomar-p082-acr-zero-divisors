import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ACRZeroDivisors

def necessitySteady (a b c : ℝ) : Prop :=
  -a*b+b-a*c+3*c = 0 ∧ a*b-2*b = 0 ∧ a*c-3*c+b = 0

theorem necessity_positive_locus (a b c : ℝ) (hb : 0 < b) :
    necessitySteady a b c ↔ a = 2 ∧ b = c := by
  constructor
  · rintro ⟨_, hB, hC⟩
    have ha : a = 2 := by
      have h : b * (a - 2) = 0 := by nlinarith [hB]
      have := (mul_eq_zero.mp h).resolve_left (ne_of_gt hb)
      linarith
    subst a
    constructor
    · rfl
    · nlinarith [hC]
  · rintro ⟨rfl, rfl⟩
    unfold necessitySteady
    constructor
    · ring
    constructor <;> ring

def sufficiencySteady (a b c d : ℝ) : Prop :=
  -a^2+c+d-a*b+b-a = 0 ∧ d-b^2 = 0 ∧ a^2-c = 0 ∧ c-d = 0

theorem sufficiency_positive_locus (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) :
    sufficiencySteady a b c d ↔ b = a ∧ c = a^2 ∧ d = a^2 := by
  constructor
  · rintro ⟨_, hB, hC, hD⟩
    have h : (a-b)*(a+b) = 0 := by nlinarith
    have hab : a = b := by
      have := (mul_eq_zero.mp h).resolve_right (ne_of_gt (add_pos ha hb))
      linarith
    exact ⟨hab.symm, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩
    unfold sufficiencySteady
    constructor
    · ring
    constructor
    · ring
    constructor <;> ring

def orderSteady (t u v : ℝ) : Prop := v-t*u = 0 ∧ u-t*v = 0

theorem order_positive_locus (t u v : ℝ) (ht : 0 < t) (hu : 0 < u) :
    orderSteady t u v ↔ t = 1 ∧ u = v := by
  constructor
  · rintro ⟨hv, h_u⟩
    have hprod : (t-1)*(t+1)*u = 0 := by
      have hmul : t * (v-t*u) = 0 := by rw [hv, mul_zero]
      nlinarith [hmul]
    have ht1 : t = 1 := by
      have hh := (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hu)
      have := (mul_eq_zero.mp hh).resolve_right (by linarith)
      linarith
    exact ⟨ht1, by rw [ht1] at hv; linarith⟩
  · rintro ⟨rfl, rfl⟩
    unfold orderSteady
    constructor <;> ring

theorem sufficiency_two_positive_states :
    sufficiencySteady 1 1 1 1 ∧ sufficiencySteady 2 2 4 4 ∧ (1 : ℝ) ≠ 2 := by
  norm_num [sufficiencySteady]

end ACRZeroDivisors
