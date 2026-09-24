import proofs.ACRZeroDivisors.NecessityIdeal
import proofs.ACRZeroDivisors.IdealSubstitution

namespace ACRZeroDivisors
open MvPolynomial
abbrev Poly4 := MvPolynomial (Fin 4) ℝ
noncomputable def sA : Poly4 := -(X 0)^2+X 2+X 3-X 0*X 1+X 1-X 0
noncomputable def sB : Poly4 := X 3-(X 1)^2
noncomputable def sC : Poly4 := (X 0)^2-X 2
noncomputable def sD : Poly4 := X 2-X 3
noncomputable def sq : Poly4 := X 0-X 1
noncomputable def sufficiencyIdeal : Ideal Poly4 := Ideal.span {sA,sB,sC,sD}
noncomputable def diagonal : Poly4 →+* Poly4 :=
  eval₂Hom C ![X 0,X 0,(X 0)^2,(X 0)^2]
noncomputable def negativePoint : Poly4 →+* ℝ := eval ![1,-1,1,1]

theorem sA_mem : sA ∈ sufficiencyIdeal := Ideal.subset_span (by simp)
theorem sB_mem : sB ∈ sufficiencyIdeal := Ideal.subset_span (by simp)
theorem sC_mem : sC ∈ sufficiencyIdeal := Ideal.subset_span (by simp)
theorem sD_mem : sD ∈ sufficiencyIdeal := Ideal.subset_span (by simp)

theorem sufficiency_diagonal_zero {p : Poly4} (hp : p ∈ sufficiencyIdeal) : diagonal p = 0 := by
  have hle : sufficiencyIdeal ≤ RingHom.ker diagonal := by
    rw [sufficiencyIdeal, Ideal.span_le]
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      change diagonal _ = 0 <;>
      dsimp only [sA, sB, sC, sD] <;>
      simp only [map_add, map_sub, map_neg, map_mul, map_pow] <;>
      norm_num [diagonal]
    all_goals ring
  exact hle hp

theorem sufficiency_point_zero {p : Poly4} (hp : p ∈ sufficiencyIdeal) : negativePoint p = 0 := by
  have hle : sufficiencyIdeal ≤ RingHom.ker negativePoint := by
    rw [sufficiencyIdeal, Ideal.span_le]
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      change negativePoint _ = 0 <;>
      norm_num [negativePoint, sA, sB, sC, sD]
  exact hle hp

theorem sq_a_relation : (X 0-1)*sq ∈ sufficiencyIdeal := by
  have h := sufficiencyIdeal.add_mem
    (sufficiencyIdeal.add_mem sA_mem (sufficiencyIdeal.mul_mem_left 2 sC_mem)) sD_mem
  convert h using 1
  dsimp [sA, sC, sD, sq]
  ring

theorem sq_ab_relation : (X 0+X 1)*sq ∈ sufficiencyIdeal := by
  have h := sufficiencyIdeal.add_mem (sufficiencyIdeal.add_mem sB_mem sC_mem) sD_mem
  convert h using 1
  dsimp [sB, sC, sD, sq]
  ring

theorem sq_point_relations (i : Fin 4) :
    (X i-C (![1,-1,1,1] i))*sq ∈ sufficiencyIdeal := by
  have hb : (X 1+1)*sq ∈ sufficiencyIdeal := by
    have h := sufficiencyIdeal.sub_mem sq_ab_relation sq_a_relation
    (convert h using 1; ring)
  have hc : (X 2-1)*sq ∈ sufficiencyIdeal := by
    have h := sufficiencyIdeal.sub_mem
      (sufficiencyIdeal.mul_mem_left (X 0+1) sq_a_relation)
      (sufficiencyIdeal.mul_mem_left sq sC_mem)
    (convert h using 1; dsimp [sC]; ring)
  have hd : (X 3-1)*sq ∈ sufficiencyIdeal := by
    have h := sufficiencyIdeal.sub_mem hc (sufficiencyIdeal.mul_mem_left sq sD_mem)
    (convert h using 1; dsimp [sD]; ring)
  fin_cases i
  · simpa using sq_a_relation
  · simpa using hb
  · simpa using hc
  · simpa using hd

theorem diagonal_kernel_lift {p : Poly4} (hp : diagonal p = 0) :
    p ∈ sufficiencyIdeal ⊔ Ideal.span {sq} := by
  let J : Ideal Poly4 := sufficiencyIdeal ⊔ Ideal.span {sq}
  have hq : sq ∈ J := (show Ideal.span {sq} ≤ J from le_sup_right) (Ideal.subset_span (by simp))
  have hc : sC ∈ J := (show sufficiencyIdeal ≤ J from le_sup_left) sC_mem
  have hd : sD ∈ J := (show sufficiencyIdeal ≤ J from le_sup_left) sD_mem
  have hv : ∀ i : Fin 4, X i-(![X 0,X 0,(X 0)^2,(X 0)^2] : Fin 4 → Poly4) i ∈ J := by
    intro i
    fin_cases i
    · simp
    · (convert J.neg_mem hq using 1; dsimp [sq]; ring)
    · change X 2-(X 0)^2 ∈ J
      (convert J.neg_mem hc using 1; dsimp [sC]; ring)
    · change X 3-(X 0)^2 ∈ J
      (convert J.neg_mem (J.add_mem hc hd) using 1; dsimp [sC, sD]; ring)
  have h := substitution_sub_mem J _ hv p
  change p-diagonal p ∈ J at h
  simpa [hp] using h

theorem sufficiency_two_kernel_criterion (p : Poly4) :
    p ∈ sufficiencyIdeal ↔ diagonal p = 0 ∧ negativePoint p = 0 := by
  constructor
  · intro h
    exact ⟨sufficiency_diagonal_zero h, sufficiency_point_zero h⟩
  · rintro ⟨hd,hp⟩
    obtain ⟨f,hf,g,hg,hfg⟩ := Submodule.mem_sup.mp (diagonal_kernel_lift hd)
    obtain ⟨r,hr⟩ := Ideal.mem_span_singleton'.mp hg
    have hpr : negativePoint r = 0 := by
      have h := congrArg negativePoint hfg
      rw [map_add, sufficiency_point_zero hf, ← hr, map_mul] at h
      norm_num [negativePoint, sq] at h
      change negativePoint r * 2 = negativePoint p at h
      rw [hp] at h
      exact (mul_eq_zero.mp h).resolve_right (by norm_num)
    have hm := mul_eval_sub_mem sufficiencyIdeal (![1,-1,1,1]) sq sq_point_relations r
    change (r-C (negativePoint r))*sq ∈ sufficiencyIdeal at hm
    simp only [hpr, map_zero, sub_zero] at hm
    rw [← hfg, ← hr]
    exact sufficiencyIdeal.add_mem hf hm

end ACRZeroDivisors
