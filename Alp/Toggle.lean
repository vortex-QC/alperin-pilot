import Mathlib
import Alp.Defs
import Alp.ChainProps

/-!
# Alp · 打样第 3 件（b）：toggle 长度账·反号·无不动点·对合（pcore 版）

toggle 恒变长（真分支删一位/假分支插一位）。直接推论：
①无不动点：长度不同则列表不同；
②(-1)^长度 型权重反号——消去引理的权重侧；
③长度账为对合闭环铺底。
后半：i* 稳定性（插/删）+ toggleGenList 对合（P ≤ R·严格链）。
前缀 ¬P≤ 一律由 findIdx? 首满足性（hpre）直读，无需 spec① 的 ⊥-角条件。
-/

namespace Alp

open scoped Classical

variable {X : Type*} [Group X]

/-- lastIdxNotLe 落在链内：非空列表上 i* < length。 -/
theorem lastIdxNotLe_lt_length (P : Subgroup X) {l : List (Subgroup X)} (hl : l ≠ []) :
    lastIdxNotLe P l < l.length := by
  unfold lastIdxNotLe
  cases hh : l.findIdx? (fun Q => P ≤ Q) with
  | some k =>
    obtain ⟨hk, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hh
    show k - 1 < l.length
    omega
  | none =>
    have hpos := List.length_pos_of_ne_nil hl
    show l.length - 1 < l.length
    omega

/-- toggle 恒变长（长度账）：真分支删一位（+1=length），假分支插一位（=length+1）。 -/
theorem length_togglePcoreList (P : Subgroup X) {J : Subgroup X} (C : NormChain J) :
    (togglePcoreList P C).length + 1 = C.members.length ∨
    (togglePcoreList P C).length = C.members.length + 1 := by
  have hi := lastIdxNotLe_lt_length P C.hne
  simp only [togglePcoreList]
  split
  · rename_i h
    exact Or.inl (List.length_eraseIdx_add_one h.1)
  · refine Or.inr ?_
    rw [List.length_insertIdx_of_le_length (by omega)]

/-- 无不动点：长度必变故列表必不同。 -/
theorem togglePcoreList_ne (P : Subgroup X) {J : Subgroup X} (C : NormChain J) :
    togglePcoreList P C ≠ C.members := by
  rcases length_togglePcoreList P C with h | h
  · intro heq
    rw [heq] at h
    omega
  · intro heq
    rw [heq] at h
    omega

/-- 反号：toggle 把 (-1)^长度 型权重反号（消去引理权重侧）。 -/
theorem toggle_pow_length_reverse (P : Subgroup X) {J : Subgroup X} (C : NormChain J) :
    (-1 : ℤ) ^ (togglePcoreList P C).length = -(-1 : ℤ) ^ C.members.length := by
  rcases length_togglePcoreList P C with h | h
  · have hlen : C.members.length = (togglePcoreList P C).length + 1 := by omega
    rw [hlen, pow_succ]
    ring
  · rw [h, pow_succ]
    ring

/-! ## ④ 通用 toggle：nonnormal 复用底座 -/

/-- 通用 toggle：位-逻辑与 pcore 全同，插入元素 R 任意。 -/
noncomputable def toggleGenList (P : Subgroup X) (R : Subgroup X) (l : List (Subgroup X)) :
    List (Subgroup X) :=
  let i := lastIdxNotLe P l
  if _h : i + 1 < l.length ∧ l.getD (i + 1) ⊥ = R then
    l.eraseIdx (i + 1)
  else
    l.insertIdx (i + 1) R

/-- pcore toggle = 通用 toggle 取 R = Q_i ⊔ P（定义层桥）。 -/
theorem togglePcoreList_eq_gen (P : Subgroup X) {J : Subgroup X} (C : NormChain J) :
    togglePcoreList P C =
      toggleGenList P (C.members.getD (lastIdxNotLe P C.members) ⊥ ⊔ P) C.members := by
  simp only [togglePcoreList, toggleGenList]

/-- 通用长度账（R 任意）。 -/
theorem length_toggleGenList (P : Subgroup X) (R : Subgroup X) {l : List (Subgroup X)}
    (hl : l ≠ []) :
    (toggleGenList P R l).length + 1 = l.length ∨
    (toggleGenList P R l).length = l.length + 1 := by
  have hi := lastIdxNotLe_lt_length P hl
  simp only [toggleGenList]
  split
  · rename_i h
    exact Or.inl (List.length_eraseIdx_add_one h.1)
  · refine Or.inr ?_
    rw [List.length_insertIdx_of_le_length (by omega)]

/-- 通用无不动点（R 任意）。 -/
theorem toggleGenList_ne (P : Subgroup X) (R : Subgroup X) {l : List (Subgroup X)}
    (hl : l ≠ []) : toggleGenList P R l ≠ l := by
  rcases length_toggleGenList P R hl with h | h
  · intro heq
    rw [heq] at h
    omega
  · intro heq
    rw [heq] at h
    omega

/-- 通用反号（R 任意）。 -/
theorem toggleGen_pow_length_reverse (P : Subgroup X) (R : Subgroup X)
    {l : List (Subgroup X)} (hl : l ≠ []) :
    (-1 : ℤ) ^ (toggleGenList P R l).length = -(-1 : ℤ) ^ l.length := by
  rcases length_toggleGenList P R hl with h | h
  · have hlen : l.length = (toggleGenList P R l).length + 1 := by omega
    rw [hlen, pow_succ]
    ring
  · rw [h, pow_succ]
    ring

/-! ## ⑤→⑥ 稳定性与对合 -/

/-- 成员↔索引桥：x ∈ l ↔ ∃ j < length, l[j] = x。 -/
theorem mem_iff_getElem_idx {α : Type*} {b : α} {l : List α} :
    b ∈ l ↔ ∃ (j : ℕ) (hj : j < l.length), l[j]'hj = b := by
  constructor
  · intro h
    induction l with
    | nil => cases h
    | cons x t ih =>
      cases h with
      | head => exact ⟨0, by simp, rfl⟩
      | tail _ ht =>
        obtain ⟨j, hj, hje⟩ := ih ht
        refine ⟨j + 1, by simp only [List.length_cons]; omega, ?_⟩
        simpa using hje
  · rintro ⟨j, hj, hje⟩
    subst hje
    exact List.getElem_mem hj

/-- eraseIdx 位桥（j < i）：(eraseIdx i l)[j] = l[j]。 -/
theorem getElem_eraseIdx_of_lt' {α : Type*} {l : List α} {i j : ℕ} (hi : i < l.length)
    (hji : j < i) (hj : j < (l.eraseIdx i).length) :
    (l.eraseIdx i)[j] = l[j]'(by have := List.length_eraseIdx_add_one hi; omega) := by
  have h1 : (l.eraseIdx i)[j]? = l[j]? := List.getElem?_eraseIdx_of_lt hji
  rw [List.getElem?_eq_getElem hj] at h1
  have hlen := List.length_eraseIdx_add_one hi
  rw [List.getElem?_eq_getElem (by omega)] at h1
  simpa using h1

/-- eraseIdx 位桥（i ≤ j）：(eraseIdx i l)[j] = l[j+1]。 -/
theorem getElem_eraseIdx_of_ge' {α : Type*} {l : List α} {i j : ℕ} (hi : i < l.length)
    (hij : i ≤ j) (hj : j < (l.eraseIdx i).length) :
    (l.eraseIdx i)[j] = l[j + 1]'(by have := List.length_eraseIdx_add_one hi; omega) := by
  have h1 : (l.eraseIdx i)[j]? = l[j + 1]? := List.getElem?_eraseIdx_of_ge hij
  rw [List.getElem?_eq_getElem hj] at h1
  have hlen := List.length_eraseIdx_add_one hi
  rw [List.getElem?_eq_getElem (by omega)] at h1
  simpa using h1

/-- 值引理（some）：findIdx?=some m ⇒ lastIdxNotLe = m-1。 -/
private theorem lastIdxNotLe_eq_of_findIdx_some {P : Subgroup X} {l : List (Subgroup X)}
    {m : ℕ} (hh : l.findIdx? (fun Q : Subgroup X => P ≤ Q) = some m) :
    lastIdxNotLe P l = m - 1 := by
  unfold lastIdxNotLe
  rw [hh]

/-- 值引理（none）：findIdx?=none ⇒ lastIdxNotLe = length-1。 -/
private theorem lastIdxNotLe_eq_of_findIdx_none {P : Subgroup X} {l : List (Subgroup X)}
    (hh : l.findIdx? (fun Q : Subgroup X => P ≤ Q) = none) :
    lastIdxNotLe P l = l.length - 1 := by
  unfold lastIdxNotLe
  rw [hh]

/-- 稳定性（插）：于 i*+1 处插入 R（P ≤ R）不改变 i*。
m=0 角：R 插在 1 位而首满足位 0 原样保留——i* 仍 0 ✓。 -/
theorem lastIdxNotLe_insertIdx_eq (P R : Subgroup X) (hPR : P ≤ R)
    {l : List (Subgroup X)} (hl : l ≠ []) :
    lastIdxNotLe P (l.insertIdx (lastIdxNotLe P l + 1) R) = lastIdxNotLe P l := by
  have hpos : 0 < l.length := List.length_pos_of_ne_nil hl
  have hi := lastIdxNotLe_lt_length P hl
  cases hh : l.findIdx? (fun Q : Subgroup X => P ≤ Q) with
  | some m =>
    obtain ⟨hm, hpk, hpre⟩ := List.findIdx?_eq_some_iff_getElem.mp hh
    have hv : lastIdxNotLe P l = m - 1 := lastIdxNotLe_eq_of_findIdx_some hh
    rw [hv] at hi ⊢
    rcases m with _ | m'
    · -- m=0：首满足位 0 不受 1 位插入影响
      have hlenI0 : (l.insertIdx (0 - 1 + 1) R).length = l.length + 1 :=
        List.length_insertIdx_of_le_length (by omega) R
      have hfind : (l.insertIdx (0 - 1 + 1) R).findIdx? (fun Q : Subgroup X => P ≤ Q)
          = some 0 := by
        rw [List.findIdx?_eq_some_iff_getElem]
        refine ⟨by rw [hlenI0]; omega, ?_, fun j hj => absurd hj (by omega)⟩
        rw [List.getElem_insertIdx_of_lt (by omega) (by rw [hlenI0]; omega)]
        exact hpk
      rw [lastIdxNotLe_eq_of_findIdx_some hfind]
    · -- m≥1：R 恰插在首满足位上，成为新首满足
      have hfind : (l.insertIdx (m' + 1 - 1 + 1) R).findIdx? (fun Q : Subgroup X => P ≤ Q)
          = some (m' + 1 - 1 + 1) := by
        rw [List.findIdx?_eq_some_iff_getElem]
        have hlenI : (l.insertIdx (m' + 1 - 1 + 1) R).length = l.length + 1 :=
          List.length_insertIdx_of_le_length (by omega) R
        have hbr : (l.insertIdx (m' + 1 - 1 + 1) R)[m' + 1 - 1 + 1] = R := by
          have hbr0 : (l.insertIdx (m' + 1 - 1 + 1) R)[m' + 1 - 1 + 1] =
              (l.insertIdx (m' + 1 - 1 + 1) R)[m' + 1 - 1 + 1]'(by rw [hlenI]; omega) := rfl
          rw [hbr0, List.getElem_insertIdx_self (by rw [hlenI]; omega)]
        refine ⟨by rw [hlenI]; omega, ?_, ?_⟩
        · rw [hbr]
          exact decide_eq_true hPR
        · intro j hj
          rw [List.getElem_insertIdx_of_lt hj (by rw [hlenI]; omega)]
          refine fun hle => ?_
          have hnd := hpre j (by omega)
          exact hnd (by simpa using hle)
      rw [lastIdxNotLe_eq_of_findIdx_some hfind]
      omega
  | none =>
    rw [lastIdxNotLe_eq_of_findIdx_none hh]
    have hlenI : (l.insertIdx (l.length - 1 + 1) R).length = l.length + 1 :=
      List.length_insertIdx_of_le_length (by omega) R
    have hfind : (l.insertIdx (l.length - 1 + 1) R).findIdx? (fun Q : Subgroup X => P ≤ Q)
        = some (l.length - 1 + 1) := by
      rw [List.findIdx?_eq_some_iff_getElem]
      refine ⟨by rw [hlenI]; omega, ?_, ?_⟩
      · rw [List.getElem_insertIdx_self (by rw [hlenI]; omega)]
        exact decide_eq_true hPR
      · intro j hj
        rw [List.getElem_insertIdx_of_lt hj (by rw [hlenI]; omega)]
        refine fun hle => ?_
        have hnone := List.of_findIdx?_eq_none hh
        have hnj := hnone j
        rw [List.getElem?_eq_getElem (by omega)] at hnj
        exact hnj (by simpa using hle)
    rw [lastIdxNotLe_eq_of_findIdx_some hfind]
    omega

/-- 稳定性（删）：删除位 i*+1（严格链）不改变 i*。三子情形：
m=0 角 / 中删（后继顶上成为新首满足）/ 尾删（findIdx? 转 none）。 -/
theorem lastIdxNotLe_eraseIdx_eq (P : Subgroup X) {l : List (Subgroup X)}
    (_hl : l ≠ []) (hilt : lastIdxNotLe P l + 1 < l.length) (hp : l.Pairwise (· < ·)) :
    lastIdxNotLe P (l.eraseIdx (lastIdxNotLe P l + 1)) = lastIdxNotLe P l := by
  have hlenE : (l.eraseIdx (lastIdxNotLe P l + 1)).length + 1 = l.length :=
    List.length_eraseIdx_add_one hilt
  cases hh : l.findIdx? (fun Q => P ≤ Q) with
  | some m =>
    obtain ⟨hm, hpk, hpre⟩ := List.findIdx?_eq_some_iff_getElem.mp hh
    have hv : lastIdxNotLe P l = m - 1 := lastIdxNotLe_eq_of_findIdx_some hh
    rw [hv] at hilt hlenE ⊢
    rcases m with _ | m'
    · -- m=0：删 1 位，首满足位 0 原样保留
      have hfind : (l.eraseIdx (0 - 1 + 1)).findIdx? (fun Q => P ≤ Q) = some 0 := by
        rw [List.findIdx?_eq_some_iff_getElem]
        refine ⟨by omega, ?_, fun j hj => absurd hj (by omega)⟩
        rw [getElem_eraseIdx_of_lt' (hi := hilt) (hji := by omega) (hj := by omega)]
        exact hpk
      rw [lastIdxNotLe_eq_of_findIdx_some hfind]
    · rcases Nat.lt_or_ge (m' + 2) l.length with h2 | h2
      · -- 中删：后继 l[i*+2] 顶上成为新首满足
        have hfind : (l.eraseIdx (m' + 1 - 1 + 1)).findIdx? (fun Q => P ≤ Q)
            = some (m' + 1 - 1 + 1) := by
          rw [List.findIdx?_eq_some_iff_getElem]
          have hbr : (l.eraseIdx (m' + 1 - 1 + 1))[m' + 1 - 1 + 1]
              = l[m' + 1 - 1 + 2]'(by omega) :=
            getElem_eraseIdx_of_ge' (hi := hilt) (hij := by omega) (hj := by omega)
          have hb : P ≤ l[m' + 1 - 1 + 2] := by
            have hb1 : lastIdxNotLe P l < m' + 1 - 1 + 2 := by rw [hv]; omega
            have hb0 := le_of_lt_lastIdx P hp hb1
              (show m' + 1 - 1 + 2 < l.length by omega)
            have hbound : m' + 1 - 1 + 2 < l.length := by omega
            have hget : l.getD (m' + 1 - 1 + 2) (⊥ : Subgroup X)
                = l[m' + 1 - 1 + 2] := List.getD_eq_getElem l (d := (⊥ : Subgroup X)) hbound
            exact hget ▸ hb0
          refine ⟨by omega, ?_, ?_⟩
          · rw [hbr]
            exact decide_eq_true hb
          · intro j hj
            have hbr2 : (l.eraseIdx (m' + 1 - 1 + 1))[j] = l[j]'(by omega) :=
              getElem_eraseIdx_of_lt' (hi := hilt) (hji := by omega) (hj := by omega)
            have hnd := hpre j (by omega)
            rw [hbr2]
            exact fun hle => hnd (by simpa using hle)
        rw [lastIdxNotLe_eq_of_findIdx_some hfind]
        omega
      · -- 尾删：l' 全体 ¬P≤ ⇒ findIdx?=none ⇒ lastIdxNotLe = len'-1 = i*
        have hfind : (l.eraseIdx (m' + 1 - 1 + 1)).findIdx? (fun Q => P ≤ Q) = none := by
          rw [List.findIdx?_eq_none_iff]
          intro x hx
          obtain ⟨j, hj, hje⟩ := (mem_iff_getElem_idx).mp hx
          have hbr2 : (l.eraseIdx (m' + 1 - 1 + 1))[j] = l[j]'(by omega) :=
            getElem_eraseIdx_of_lt' (hi := hilt) (hji := by omega) (hj := by omega)
          have hnd := hpre j (by omega)
          rw [← hje, hbr2]
          simpa using hnd
        rw [lastIdxNotLe_eq_of_findIdx_none hfind]
        omega
  | none =>
    exfalso
    rw [lastIdxNotLe_eq_of_findIdx_none hh] at hilt
    omega

/-- 对合：toggleGenList（P ≤ R·严格链）自逆。
删分支：外层条件必假（后继= R 违反严格序/尾删无后继）→ 插回原位；
插分支：外层条件必真 → 删回原位。 -/
theorem toggleGenList_involution (P R : Subgroup X) (hPR : P ≤ R)
    {l : List (Subgroup X)} (hl : l ≠ []) (hp : l.Pairwise (· < ·)) :
    toggleGenList P R (toggleGenList P R l) = l := by
  have hi := lastIdxNotLe_lt_length P hl
  simp only [toggleGenList]
  split
  · -- 内层走了删：外层必走插
    rename_i h
    obtain ⟨hilt, hR⟩ := h
    rw [lastIdxNotLe_eraseIdx_eq P hl hilt hp]
    split
    · -- 外层条件真（不可能）：后继=R 违反严格序 / 尾删无后继
      exfalso
      rename_i hc
      obtain ⟨_, hR2⟩ := hc
      by_cases h2 : lastIdxNotLe P l + 2 < l.length
      · have hlt := pairwise_getD_lt hp (lastIdxNotLe P l + 1) (lastIdxNotLe P l + 2)
          (by omega) (by omega)
        have hbrid : (l.eraseIdx (lastIdxNotLe P l + 1)).getD (lastIdxNotLe P l + 1)
              (⊥ : Subgroup X) = l.getD (lastIdxNotLe P l + 2) (⊥ : Subgroup X) := by
          rw [List.getD_eq_getElem (d := (⊥ : Subgroup X))
              (hn := by have := List.length_eraseIdx_add_one (l := l) hilt; omega),
              List.getD_eq_getElem (d := (⊥ : Subgroup X)) (hn := by omega)]
          have h1 : (l.eraseIdx (lastIdxNotLe P l + 1))[lastIdxNotLe P l + 1]?
              = l[lastIdxNotLe P l + 2]? := List.getElem?_eraseIdx_of_ge (by omega)
          rw [List.getElem?_eq_getElem
              (by have := List.length_eraseIdx_add_one (l := l) hilt; omega)] at h1
          rw [List.getElem?_eq_getElem (by omega)] at h1
          simpa using h1
        rw [hbrid] at hR2
        rw [hR2.trans hR.symm] at hlt
        exact absurd hlt (lt_irrefl _)
      · have hlenE := List.length_eraseIdx_add_one (l := l) hilt
        omega
    · -- 外层条件假：插回原位
      rw [← hR, List.getD_eq_getElem (d := (⊥ : Subgroup X)) (hn := hilt)]
      exact List.insertIdx_eraseIdx_getElem hilt
  · -- 内层走了插：外层必走删
    rename_i h
    rw [lastIdxNotLe_insertIdx_eq P R hPR hl]
    split
    · -- 外层条件真：删回原位
      exact List.eraseIdx_insertIdx_self R
    · -- 外层条件假（不可能）：插入位恰为 R
      exfalso
      rename_i hc
      have hbnd : lastIdxNotLe P l + 1 < (l.insertIdx (lastIdxNotLe P l + 1) R).length := by
        have hli : (l.insertIdx (lastIdxNotLe P l + 1) R).length
            = l.length + 1 := List.length_insertIdx_of_le_length (by omega) R
        omega
      have hget2 : (l.insertIdx (lastIdxNotLe P l + 1) R).getD (lastIdxNotLe P l + 1)
          (⊥ : Subgroup X)
          = (l.insertIdx (lastIdxNotLe P l + 1) R)[lastIdxNotLe P l + 1] :=
        List.getD_eq_getElem (l.insertIdx (lastIdxNotLe P l + 1) R) (⊥ : Subgroup X) hbnd
      have hb2 : (l.insertIdx (lastIdxNotLe P l + 1) R).getD (lastIdxNotLe P l + 1)
          (⊥ : Subgroup X) = R := by
        rw [hget2, List.getElem_insertIdx_self hbnd]
      exact hc ⟨hbnd, hb2⟩

end Alp
