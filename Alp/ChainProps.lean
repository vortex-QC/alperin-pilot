import Mathlib
import Alp.Defs

/-!
# Alp · 打样第 3 件（a+）：lastIdx 规格引理（v4·raw 化+严格版+前缀补全）

raw 规格三件组（任意列表可复用——involution 的 findIdx? 稳定性底座）：
①i* 处本身 ¬P≤（需 P≠⊥+头⊥）
②i* 之后全体 P≤（需 Pairwise 严格序）
③i* 之前全体 ¬P≤（无条件·findIdx? 首满足性直读）
+按位单调两件（≤/<·Pairwise 归纳）。NormChain 版=推论（v3 接口保持）。
-/

namespace Alp

open scoped Classical

variable {X : Type*} [Group X]

/-- 桥：非空列表的 head! 即 getD 0 位元素（默认 ⊥）。 -/
private theorem head!_eq_getD_zero {l : List (Subgroup X)} (hl : l ≠ []) :
    l.head! = l.getD 0 (⊥ : Subgroup X) := by
  cases hl : l with
  | nil => rfl
  | cons a _ =>
    subst hl
    simp

/-! ## Pairwise 按位单调（≤ 与 < 两版） -/

/-- 按位单调（≤ 版）：i ≤ j < length ⇒ getD i ⊥ ≤ getD j ⊥。
★语义注记：真陈述必须加 j < l.length（越界 j 读 ⊥，链成员未必 ≤⊥）。 -/
theorem pairwise_getD_le {l : List (Subgroup X)} (hp : l.Pairwise (· < ·)) :
    ∀ i j, i ≤ j → j < l.length →
      l.getD i (⊥ : Subgroup X) ≤ l.getD j (⊥ : Subgroup X) := by
  induction l with
  | nil => intro i j _ hj; simp at hj
  | cons a l ih =>
    intro i j hij hjl
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
    simp only [List.length_cons] at hjl
    rcases i with _ | i'
    · rcases j with _ | j'
      · simp only [List.getD_cons_zero]
        exact le_refl _
      · have hj' : j' < l.length := by omega
        have hlt : a < l[j'] := hhead _ (List.getElem_mem hj')
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        rw [List.getD_eq_getElem (d := (⊥ : Subgroup X)) (hn := hj')]
        exact le_of_lt hlt
    · rcases j with _ | j'
      · omega
      · simp only [List.getD_cons_succ]
        exact ih htail i' j' (by omega) (by omega)

/-- 按位严格单调（< 版）：i < j < length ⇒ getD i ⊥ < getD j ⊥。 -/
theorem pairwise_getD_lt {l : List (Subgroup X)} (hp : l.Pairwise (· < ·)) :
    ∀ i j, i < j → j < l.length →
      l.getD i (⊥ : Subgroup X) < l.getD j (⊥ : Subgroup X) := by
  induction l with
  | nil => intro i j _ hj; simp at hj
  | cons a l ih =>
    intro i j hij hjl
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
    simp only [List.length_cons] at hjl
    rcases i with _ | i'
    · rcases j with _ | j'
      · omega
      · have hj' : j' < l.length := by omega
        have hlt : a < l[j'] := hhead _ (List.getElem_mem hj')
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        rw [List.getD_eq_getElem (d := (⊥ : Subgroup X)) (hn := hj')]
        exact hlt
    · rcases j with _ | j'
      · omega
      · simp only [List.getD_cons_succ]
        exact ih htail i' j' (by omega) (by omega)

/-! ## raw 规格三件组 -/

/-- raw 规格①：i* 处本身不满足 P≤（需 P≠⊥+头⊥——k=0 角除外条件）。 -/
theorem lastIdxNotLe_notLe_raw (P : Subgroup X) {l : List (Subgroup X)}
    (hl : l ≠ []) (hd0 : l.getD 0 (⊥ : Subgroup X) = ⊥) (hP : P ≠ ⊥) :
    ¬ (P ≤ l.getD (lastIdxNotLe P l) ⊥) := by
  unfold lastIdxNotLe
  cases hh : l.findIdx? (fun Q => P ≤ Q) with
  | some k =>
    obtain ⟨hk, hpk, hpre⟩ := List.findIdx?_eq_some_iff_getElem.mp hh
    rcases k with _ | k'
    · simp only
      rw [hd0]
      exact fun hle => hP (le_bot_iff.mp hle)
    · simp only [Nat.add_sub_cancel]
      have hn' : k' < l.length := by
        have hk' := hk
        have hpos := List.length_pos_of_ne_nil hl
        omega
      rw [List.getD_eq_getElem (d := (⊥ : Subgroup X)) (hn := hn')]
      exact fun h => hpre k' (by omega) (by simpa using h)
  | none =>
    simp only
    have hpos : 0 < l.length := List.length_pos_of_ne_nil hl
    rw [List.getD_eq_getElem (d := (⊥ : Subgroup X)) (hn := by omega)]
    have hnone := List.of_findIdx?_eq_none hh
    have hlast := hnone (l.length - 1)
    rw [List.getElem?_eq_getElem (by omega)] at hlast
    simpa using hlast

/-- raw 规格②：i* 之后全体满足 P≤（需 Pairwise 严格序——按位单调上闭）。 -/
theorem le_of_lt_lastIdx (P : Subgroup X) {l : List (Subgroup X)}
    (hp : l.Pairwise (· < ·))
    {j : ℕ} (hij : lastIdxNotLe P l < j) (hjl : j < l.length) :
    P ≤ l.getD j (⊥ : Subgroup X) := by
  unfold lastIdxNotLe at hij
  cases hh : l.findIdx? (fun Q => P ≤ Q) with
  | some k =>
    rw [hh] at hij
    simp only at hij
    obtain ⟨hk, hpk, hpre⟩ := List.findIdx?_eq_some_iff_getElem.mp hh
    have hjk : k ≤ j := by omega
    have hkD : l[k] = l.getD k (⊥ : Subgroup X) :=
      (List.getD_eq_getElem (d := (⊥ : Subgroup X)) (hn := by omega)).symm
    rw [hkD] at hpk
    have hpk' : P ≤ l.getD k (⊥ : Subgroup X) := by simpa using hpk
    exact le_trans hpk' (pairwise_getD_le hp k j hjk hjl)
  | none =>
    rw [hh] at hij
    simp only at hij
    omega

/-- raw 规格③：i* 之前全体不满足 P≤（无条件——findIdx? 首满足性直读；
some-0 角自动排除：k < i* 蕴含 findIdx?=some m 且 m ≥ 1）。 -/
theorem notLe_of_lt_lastIdx (P : Subgroup X) {l : List (Subgroup X)} {k : ℕ}
    (hk : k < lastIdxNotLe P l) : ¬ (P ≤ l.getD k (⊥ : Subgroup X)) := by
  unfold lastIdxNotLe at hk
  cases hh : l.findIdx? (fun Q => P ≤ Q) with
  | some m =>
    rw [hh] at hk
    simp only at hk
    obtain ⟨hm, _, hpre⟩ := List.findIdx?_eq_some_iff_getElem.mp hh
    have hkm : k < m := by omega
    have hkl : k < l.length := by omega
    rw [List.getD_eq_getElem (d := (⊥ : Subgroup X)) (hn := hkl)]
    exact fun hle => hpre k hkm (by simpa using hle)
  | none =>
    rw [hh] at hk
    simp only at hk
    have hkl : k < l.length := by omega
    rw [List.getD_eq_getElem (d := (⊥ : Subgroup X)) (hn := hkl)]
    have hnone := List.of_findIdx?_eq_none hh
    have hnk := hnone k
    rw [List.getElem?_eq_getElem hkl] at hnk
    simpa using hnk

/-! ## NormChain 接口（v3 保持·推论） -/

section Spec
variable (P : Subgroup X)

/-- 规格①（NormChain）：i* 处本身不满足 P≤。 -/
theorem getD_lastIdxNotLe_notLe {J : Subgroup X} (C : NormChain J) (hP : P ≠ ⊥) :
    ¬ (P ≤ C.members.getD (lastIdxNotLe P C.members) ⊥) :=
  lastIdxNotLe_notLe_raw P C.hne (by rw [← head!_eq_getD_zero C.hne, C.hhead]) hP

/-- 规格②（NormChain）：i* 之后全体满足 P≤。 -/
theorem getD_le_of_lt_lastIdxNotLe {J : Subgroup X} (C : NormChain J)
    {j : ℕ} (hij : lastIdxNotLe P C.members < j) (hjl : j < C.members.length) :
    P ≤ C.members.getD j ⊥ :=
  le_of_lt_lastIdx P C.hstrict hij hjl

end Spec

end Alp
