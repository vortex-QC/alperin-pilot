import Mathlib
import Alp.Defs
import Alp.ChainProps
import Alp.Toggle
import Alp.Preserve
import Alp.Assemble

/-!
# Alp · 打样第 5 件（⑧）：nonnormal 复用——泛谓词底座

202 手稿 lem:nonnormal-cancellation（group.tex:378）的形式化底座。
原文构造：i = 最大下标使 Q_i 不正规于 P（谓词 ¬(P ≤ N(Q_i))，与 pcore 的
¬(P ≤ Q_i) 不同谓词）；R = Q_i 在 P 中的正规闭包；R 缺席则插 i 后、在场则删。
本文件：泛谓词版 lastIdxNotLeG（r 参数化·pcore 桥定义层可通）；
稳定性/对合的 G 版候下段（⑤d 模式谓词参数化复制）。
R 三性质（Q_i<R≤Q_{i+1}/R<P·p-群极大子群论证）候再下段。
-/

namespace Alp

open scoped Classical

variable {X : Type*} [Group X]

/-- 泛谓词版最大不满足下标：最大 i 使 ¬r(l[i])。
数学：S={i : r(l[i])} 沿链上闭 ⇒ S={k..} 或空，最大不满足 = min S - 1
（S 空 = length-1）。沿链上闭性由调用处承担
（pcore: P≤ 沿 ≤ 传递；nonnormal: 链的正规性假设=后段成员全 ⊴ P）。 -/
noncomputable def lastIdxNotLeG (r : Subgroup X → Prop) [DecidablePred r]
    (l : List (Subgroup X)) : ℕ :=
  match l.findIdx? (fun Q => decide (r Q)) with
  | some k => k - 1
  | none => l.length - 1

/-- pcore 桥：lastIdxNotLe = 泛谓词版取 r := P ≤ ·（定义层同一 match）。 -/
theorem lastIdxNotLe_eq_G (P : Subgroup X) (l : List (Subgroup X)) :
    lastIdxNotLe P l = lastIdxNotLeG (fun Q => P ≤ Q) l := rfl

/-- 泛谓词版落链内：非空列表上 i* < length（两分支均 omega，不依赖谓词内容）。 -/
theorem lastIdxNotLeG_lt_length (r : Subgroup X → Prop) [DecidablePred r]
    {l : List (Subgroup X)} (hl : l ≠ []) :
    lastIdxNotLeG r l < l.length := by
  unfold lastIdxNotLeG
  cases hh : l.findIdx? (fun Q => decide (r Q)) with
  | some k =>
    obtain ⟨hk, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hh
    show k - 1 < l.length
    omega
  | none =>
    have hpos := List.length_pos_of_ne_nil hl
    show l.length - 1 < l.length
    omega

/-- 值引理 G（some）：findIdx?=some m ⇒ lastIdxNotLeG r l = m-1。 -/
theorem lastIdxNotLeG_eq_of_findIdx_some {r : Subgroup X → Prop} [DecidablePred r]
    {l : List (Subgroup X)} {m : ℕ}
    (hh : l.findIdx? (fun Q => decide (r Q)) = some m) :
    lastIdxNotLeG r l = m - 1 := by
  unfold lastIdxNotLeG
  rw [hh]

/-- 值引理 G（none）：findIdx?=none ⇒ lastIdxNotLeG r l = length-1。 -/
theorem lastIdxNotLeG_eq_of_findIdx_none {r : Subgroup X → Prop} [DecidablePred r]
    {l : List (Subgroup X)}
    (hh : l.findIdx? (fun Q => decide (r Q)) = none) :
    lastIdxNotLeG r l = l.length - 1 := by
  unfold lastIdxNotLeG
  rw [hh]

/-- 上闭性版规格②：i* 之后全体满足 r（链序+r 上闭）。 -/
theorem r_of_lt_lastIdxG (r : Subgroup X → Prop) [DecidablePred r]
    (hmono : ∀ a b : Subgroup X, r a → a ≤ b → r b)
    {l : List (Subgroup X)} (hp : l.Pairwise (· < ·))
    {j : ℕ} (hij : lastIdxNotLeG r l < j) (hjl : j < l.length) :
    r (l.getD j (⊥ : Subgroup X)) := by
  unfold lastIdxNotLeG at hij
  cases hh : l.findIdx? (fun Q => decide (r Q)) with
  | some k =>
    rw [hh] at hij
    simp only at hij
    obtain ⟨hk, hpk, hpre⟩ := List.findIdx?_eq_some_iff_getElem.mp hh
    have hjk : k ≤ j := by omega
    have hkD : l[k] = l.getD k (⊥ : Subgroup X) :=
      (List.getD_eq_getElem (d := (⊥ : Subgroup X)) (hn := by omega)).symm
    rw [hkD] at hpk
    have hpk' : r (l.getD k (⊥ : Subgroup X)) := by simpa using hpk
    exact hmono _ _ hpk' (pairwise_getD_le hp k j hjk hjl)
  | none =>
    rw [hh] at hij
    simp only at hij
    omega

/-- 稳定性 G（插）：于 i*+1 处插入 r-元素 R 不改变 i*。
三段同 pcore 版（m=0 角/m≥1 R 恰成新首满足/none 尾插），谓词项谓词化。 -/
theorem lastIdxNotLeG_insertIdx_eq (r : Subgroup X → Prop) [DecidablePred r]
    (R : Subgroup X) (hR : r R)
    {l : List (Subgroup X)} (hl : l ≠ []) :
    lastIdxNotLeG r (l.insertIdx (lastIdxNotLeG r l + 1) R) = lastIdxNotLeG r l := by
  have hpos : 0 < l.length := List.length_pos_of_ne_nil hl
  have hi := lastIdxNotLeG_lt_length r hl
  cases hh : l.findIdx? (fun Q => decide (r Q)) with
  | some m =>
    obtain ⟨hm, hpk, hpre⟩ := List.findIdx?_eq_some_iff_getElem.mp hh
    have hv : lastIdxNotLeG r l = m - 1 := lastIdxNotLeG_eq_of_findIdx_some hh
    rw [hv] at hi ⊢
    rcases m with _ | m'
    · -- m=0：首满足位 0 不受 1 位插入影响
      have hlenI0 : (l.insertIdx (0 - 1 + 1) R).length = l.length + 1 :=
        List.length_insertIdx_of_le_length (by omega) R
      have hfind : (l.insertIdx (0 - 1 + 1) R).findIdx? (fun Q => decide (r Q))
          = some 0 := by
        rw [List.findIdx?_eq_some_iff_getElem]
        refine ⟨by rw [hlenI0]; omega, ?_, fun j hj => absurd hj (by omega)⟩
        rw [List.getElem_insertIdx_of_lt (by omega) (by rw [hlenI0]; omega)]
        exact hpk
      rw [lastIdxNotLeG_eq_of_findIdx_some hfind]
    · -- m≥1：R 恰插在首满足位上，成为新首满足
      have hfind : (l.insertIdx (m' + 1 - 1 + 1) R).findIdx? (fun Q => decide (r Q))
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
          exact decide_eq_true hR
        · intro j hj
          rw [List.getElem_insertIdx_of_lt hj (by rw [hlenI]; omega)]
          refine fun hle => ?_
          have hnd := hpre j (by omega)
          exact hnd (by simpa using hle)
      rw [lastIdxNotLeG_eq_of_findIdx_some hfind]
      omega
  | none =>
    rw [lastIdxNotLeG_eq_of_findIdx_none hh]
    have hlenI : (l.insertIdx (l.length - 1 + 1) R).length = l.length + 1 :=
      List.length_insertIdx_of_le_length (by omega) R
    have hfind : (l.insertIdx (l.length - 1 + 1) R).findIdx? (fun Q => decide (r Q))
        = some (l.length - 1 + 1) := by
      rw [List.findIdx?_eq_some_iff_getElem]
      refine ⟨by rw [hlenI]; omega, ?_, ?_⟩
      · rw [List.getElem_insertIdx_self (by rw [hlenI]; omega)]
        exact decide_eq_true hR
      · intro j hj
        rw [List.getElem_insertIdx_of_lt hj (by rw [hlenI]; omega)]
        refine fun hle => ?_
        have hnone := List.of_findIdx?_eq_none hh
        have hnj := hnone j
        rw [List.getElem?_eq_getElem (by omega)] at hnj
        exact hnj (by simpa using hle)
    rw [lastIdxNotLeG_eq_of_findIdx_some hfind]
    omega

/-- 稳定性 G（删）：删除位 i*+1 不改变 i*。三子情形同 pcore 版
（m=0 角/中删后继顶上成新首满足/尾删转 none），谓词项谓词化。 -/
theorem lastIdxNotLeG_eraseIdx_eq (r : Subgroup X → Prop) [DecidablePred r]
    (hmono : ∀ a b : Subgroup X, r a → a ≤ b → r b)
    {l : List (Subgroup X)} (hl : l ≠ [])
    (hilt : lastIdxNotLeG r l + 1 < l.length) (hp : l.Pairwise (· < ·)) :
    lastIdxNotLeG r (l.eraseIdx (lastIdxNotLeG r l + 1)) = lastIdxNotLeG r l := by
  have hlenE : (l.eraseIdx (lastIdxNotLeG r l + 1)).length + 1 = l.length :=
    List.length_eraseIdx_add_one hilt
  cases hh : l.findIdx? (fun Q => decide (r Q)) with
  | some m =>
    obtain ⟨hm, hpk, hpre⟩ := List.findIdx?_eq_some_iff_getElem.mp hh
    have hv : lastIdxNotLeG r l = m - 1 := lastIdxNotLeG_eq_of_findIdx_some hh
    rw [hv] at hilt hlenE ⊢
    rcases m with _ | m'
    · -- m=0：删 1 位，首满足位 0 原样保留
      have hfind : (l.eraseIdx (0 - 1 + 1)).findIdx? (fun Q => decide (r Q)) = some 0 := by
        rw [List.findIdx?_eq_some_iff_getElem]
        refine ⟨by omega, ?_, fun j hj => absurd hj (by omega)⟩
        rw [getElem_eraseIdx_of_lt' (hi := hilt) (hji := by omega) (hj := by omega)]
        exact hpk
      rw [lastIdxNotLeG_eq_of_findIdx_some hfind]
    · rcases Nat.lt_or_ge (m' + 2) l.length with h2 | h2
      · -- 中删：后继 l[i*+2] 顶上成为新首满足
        have hfind : (l.eraseIdx (m' + 1 - 1 + 1)).findIdx? (fun Q => decide (r Q))
            = some (m' + 1 - 1 + 1) := by
          rw [List.findIdx?_eq_some_iff_getElem]
          have hbr : (l.eraseIdx (m' + 1 - 1 + 1))[m' + 1 - 1 + 1]
              = l[m' + 1 - 1 + 2]'(by omega) :=
            getElem_eraseIdx_of_ge' (hi := hilt) (hij := by omega) (hj := by omega)
          have hb : r l[m' + 1 - 1 + 2] := by
            have hb1 : lastIdxNotLeG r l < m' + 1 - 1 + 2 := by rw [hv]; omega
            have hb0 := r_of_lt_lastIdxG r hmono hp hb1
              (show m' + 1 - 1 + 2 < l.length by omega)
            have hget : l.getD (m' + 1 - 1 + 2) (⊥ : Subgroup X)
                = l[m' + 1 - 1 + 2] := List.getD_eq_getElem l (⊥ : Subgroup X) (by omega)
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
        rw [lastIdxNotLeG_eq_of_findIdx_some hfind]
        omega
      · -- 尾删：l' 全体 ¬r ⇒ findIdx?=none ⇒ lastIdxNotLeG = len'-1 = i*
        have hfind : (l.eraseIdx (m' + 1 - 1 + 1)).findIdx? (fun Q => decide (r Q)) = none := by
          rw [List.findIdx?_eq_none_iff]
          intro x hx
          obtain ⟨j, hj, hje⟩ := (mem_iff_getElem_idx).mp hx
          have hbr2 : (l.eraseIdx (m' + 1 - 1 + 1))[j] = l[j]'(by omega) :=
            getElem_eraseIdx_of_lt' (hi := hilt) (hji := by omega) (hj := by omega)
          have hnd := hpre j (by omega)
          rw [← hje, hbr2]
          simpa using hnd
        rw [lastIdxNotLeG_eq_of_findIdx_none hfind]
        omega
  | none =>
    exfalso
    rw [lastIdxNotLeG_eq_of_findIdx_none hh] at hilt
    omega

/-! ## ⑧ 泛谓词 toggle 底座 -/

/-- 通用 toggle G：谓词 r + 插入元素 R 任意（pcore 的 toggleGenList 泛谓词化）。 -/
noncomputable def toggleGenListG (r : Subgroup X → Prop) [DecidablePred r]
    (R : Subgroup X) (l : List (Subgroup X)) : List (Subgroup X) :=
  let i := lastIdxNotLeG r l
  if _h : i + 1 < l.length ∧ l.getD (i + 1) ⊥ = R then
    l.eraseIdx (i + 1)
  else
    l.insertIdx (i + 1) R

/-- 通用长度账 G（r 任意·R 任意）。 -/
theorem length_toggleGenListG (r : Subgroup X → Prop) [DecidablePred r]
    (R : Subgroup X) {l : List (Subgroup X)} (hl : l ≠ []) :
    (toggleGenListG r R l).length + 1 = l.length ∨
    (toggleGenListG r R l).length = l.length + 1 := by
  have hi := lastIdxNotLeG_lt_length r hl
  simp only [toggleGenListG]
  split
  · rename_i h
    exact Or.inl (List.length_eraseIdx_add_one h.1)
  · refine Or.inr ?_
    rw [List.length_insertIdx_of_le_length (by omega)]

/-- 反号 G（r 任意·R 任意）。 -/
theorem toggleGenListG_pow_length_reverse (r : Subgroup X → Prop) [DecidablePred r]
    (R : Subgroup X) {l : List (Subgroup X)} (hl : l ≠ []) :
    (-1 : ℤ) ^ (toggleGenListG r R l).length = -(-1 : ℤ) ^ l.length := by
  rcases length_toggleGenListG r R hl with h | h
  · have hlen : l.length = (toggleGenListG r R l).length + 1 := by omega
    rw [hlen, pow_succ]
    ring
  · rw [h, pow_succ]
    ring

/-- 对合 G：toggleGenListG（r 上闭·r R·严格链）自逆。
删分支：外层条件必假（后继=R 违反严格序/尾删无后继）→ 插回原位；
插分支：外层条件必真 → 删回原位。谓词项走 G 版稳定性。 -/
theorem toggleGenListG_involution (r : Subgroup X → Prop) [DecidablePred r]
    (hmono : ∀ a b : Subgroup X, r a → a ≤ b → r b)
    (R : Subgroup X) (hR : r R)
    {l : List (Subgroup X)} (hl : l ≠ []) (hp : l.Pairwise (· < ·)) :
    toggleGenListG r R (toggleGenListG r R l) = l := by
  have hi := lastIdxNotLeG_lt_length r hl
  simp only [toggleGenListG]
  split
  · -- 内层走了删：外层必走插
    rename_i h
    obtain ⟨hilt, hR⟩ := h
    rw [lastIdxNotLeG_eraseIdx_eq r hmono hl hilt hp]
    split
    · -- 外层条件真（不可能）：后继=R 违反严格序 / 尾删无后继
      exfalso
      rename_i hc
      obtain ⟨_, hR2⟩ := hc
      by_cases h2 : lastIdxNotLeG r l + 2 < l.length
      · have hlt := pairwise_getD_lt hp (lastIdxNotLeG r l + 1) (lastIdxNotLeG r l + 2)
          (by omega) (by omega)
        have hbrid : (l.eraseIdx (lastIdxNotLeG r l + 1)).getD (lastIdxNotLeG r l + 1)
              (⊥ : Subgroup X) = l.getD (lastIdxNotLeG r l + 2) (⊥ : Subgroup X) := by
          rw [List.getD_eq_getElem (d := (⊥ : Subgroup X))
              (hn := by have := List.length_eraseIdx_add_one (l := l) hilt; omega),
              List.getD_eq_getElem (d := (⊥ : Subgroup X)) (hn := by omega)]
          have h1 : (l.eraseIdx (lastIdxNotLeG r l + 1))[lastIdxNotLeG r l + 1]?
              = l[lastIdxNotLeG r l + 2]? := List.getElem?_eraseIdx_of_ge (by omega)
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
    rw [lastIdxNotLeG_insertIdx_eq r R hR hl]
    split
    · -- 外层条件真：删回原位
      exact List.eraseIdx_insertIdx_self R
    · -- 外层条件假（不可能）：插入位恰为 R
      exfalso
      rename_i hc
      have hbnd : lastIdxNotLeG r l + 1 < (l.insertIdx (lastIdxNotLeG r l + 1) R).length := by
        have hli : (l.insertIdx (lastIdxNotLeG r l + 1) R).length
            = l.length + 1 := List.length_insertIdx_of_le_length (by omega) R
        omega
      have hget2 : (l.insertIdx (lastIdxNotLeG r l + 1) R).getD (lastIdxNotLeG r l + 1)
          (⊥ : Subgroup X)
          = (l.insertIdx (lastIdxNotLeG r l + 1) R)[lastIdxNotLeG r l + 1] :=
        List.getD_eq_getElem (l.insertIdx (lastIdxNotLeG r l + 1) R) (⊥ : Subgroup X) hbnd
      have hb2 : (l.insertIdx (lastIdxNotLeG r l + 1) R).getD (lastIdxNotLeG r l + 1)
          (⊥ : Subgroup X) = R := by
        rw [hget2, List.getElem_insertIdx_self hbnd]
      exact hc ⟨hbnd, hb2⟩

/-! ## ⑧ R=f(A) 依赖版 toggle 与链层对合（⑤d 模式） -/

/-- G 稳定归约：lastIdxNotLeG 对 toggleGenListG 稳定。 -/
theorem lastIdxNotLeG_toggleGenListG_eq (r : Subgroup X → Prop) [DecidablePred r]
    (hmono : ∀ a b : Subgroup X, r a → a ≤ b → r b)
    (R : Subgroup X) (hR : r R)
    {l : List (Subgroup X)} (hl : l ≠ []) (hp : l.Pairwise (· < ·)) :
    lastIdxNotLeG r (toggleGenListG r R l) = lastIdxNotLeG r l := by
  simp only [toggleGenListG]
  split
  · rename_i h
    exact lastIdxNotLeG_eraseIdx_eq r hmono hl h.1 hp
  · exact lastIdxNotLeG_insertIdx_eq r R hR hl

/-- G 位不动：toggleGenListG 后位 i* 元素不动。 -/
theorem toggleGenListG_getD_i_eq (r : Subgroup X → Prop) [DecidablePred r]
    (R : Subgroup X) {l : List (Subgroup X)} (hl : l ≠ []) :
    (toggleGenListG r R l).getD (lastIdxNotLeG r l) (⊥ : Subgroup X)
      = l.getD (lastIdxNotLeG r l) (⊥ : Subgroup X) := by
  have hi := lastIdxNotLeG_lt_length r hl
  simp only [toggleGenListG]
  split
  · rename_i h
    obtain ⟨hilt, hR⟩ := h
    have hlenE := List.length_eraseIdx_add_one (l := l) hilt
    rw [List.getD_eq_getElem _ (d := (⊥ : Subgroup X)) (by omega),
      List.getD_eq_getElem l (d := (⊥ : Subgroup X)) (by omega)]
    exact getElem_eraseIdx_of_lt' hilt (by omega) (by omega)
  · have hlen : (l.insertIdx (lastIdxNotLeG r l + 1) R).length = l.length + 1 :=
      List.length_insertIdx_of_le_length (by omega) R
    rw [List.getD_eq_getElem _ (d := (⊥ : Subgroup X)) (by omega),
      List.getD_eq_getElem l (d := (⊥ : Subgroup X)) (by omega)]
    exact List.getElem_insertIdx_of_lt (by omega) (by rw [hlen]; omega)

/-- nonnormal 型 toggle（R=f(A) 依赖链版·原文 "Insert R immediately after A
if it is absent, and remove it if it is present"）：A=位 i* 元素，
R=f A 缺席则插 i* 后、在场则删。 -/
noncomputable def toggleGList (r : Subgroup X → Prop) [DecidablePred r]
    (f : Subgroup X → Subgroup X) (l : List (Subgroup X)) : List (Subgroup X) :=
  let i := lastIdxNotLeG r l
  if _h : i + 1 < l.length ∧ l.getD (i + 1) ⊥ = f (l.getD i ⊥) then
    l.eraseIdx (i + 1)
  else
    l.insertIdx (i + 1) (f (l.getD i ⊥))

/-- 定义层桥：toggleGList = toggleGenListG 取 R = f(A)。 -/
theorem toggleGList_eq_gen (r : Subgroup X → Prop) [DecidablePred r]
    (f : Subgroup X → Subgroup X) (l : List (Subgroup X)) :
    toggleGList r f l =
      toggleGenListG r (f (l.getD (lastIdxNotLeG r l) (⊥ : Subgroup X))) l := rfl

/-- ★链层对合（R=f(A) 版·⑤d 模式）：toggle(包装……)=原链的直接列表形态。
关键=两次 toggle 的 R 相同：i* 稳定→A=位 i* 元素不动→R₂=f A=R₁；
装配假设 hf 保证 r(R₁)（对合 G 版的谓词侧）。 -/
theorem toggleGList_involution (r : Subgroup X → Prop) [DecidablePred r]
    (hmono : ∀ a b : Subgroup X, r a → a ≤ b → r b)
    (f : Subgroup X → Subgroup X) (hf : ∀ Q, r (f Q))
    {l : List (Subgroup X)} (hl : l ≠ []) (hp : l.Pairwise (· < ·)) :
    toggleGList r f (toggleGList r f l) = l := by
  have hlne : l ≠ [] := hl
  have hR₁ : r (f (l.getD (lastIdxNotLeG r l) (⊥ : Subgroup X))) := hf _
  have hist : lastIdxNotLeG r (toggleGenListG r
      (f (l.getD (lastIdxNotLeG r l) (⊥ : Subgroup X))) l) = lastIdxNotLeG r l :=
    lastIdxNotLeG_toggleGenListG_eq r hmono _ hR₁ hl hp
  have hgetD : (toggleGenListG r
      (f (l.getD (lastIdxNotLeG r l) (⊥ : Subgroup X))) l).getD (lastIdxNotLeG r l)
        (⊥ : Subgroup X)
      = l.getD (lastIdxNotLeG r l) (⊥ : Subgroup X) :=
    toggleGenListG_getD_i_eq r _ hl
  calc toggleGList r f (toggleGList r f l)
      = toggleGenListG r
          (f ((toggleGenListG r
              (f (l.getD (lastIdxNotLeG r l) (⊥ : Subgroup X))) l).getD
            (lastIdxNotLeG r
              (toggleGenListG r
                (f (l.getD (lastIdxNotLeG r l) (⊥ : Subgroup X))) l)) (⊥ : Subgroup X)))
          (toggleGenListG r (f (l.getD (lastIdxNotLeG r l) (⊥ : Subgroup X))) l) := by
        rw [toggleGList_eq_gen, toggleGList_eq_gen]
    _ = toggleGenListG r
          (f (l.getD (lastIdxNotLeG r l) (⊥ : Subgroup X)))
          (toggleGenListG r (f (l.getD (lastIdxNotLeG r l) (⊥ : Subgroup X))) l) := by
        rw [hist, hgetD]
    _ = l := toggleGenListG_involution r hmono _ hR₁ hl hp

/-! ## ⑧ 保族与组装（nonnormal_cancellation） -/

/-- 保族 G：toggleGList 保 IsChain。
五性质：非空（长度账）/head⊥（谓词无关桥）/严格序（夹心 Q_i < f Q_i < Q_{i+1}：
hf_ge+hf_ne 左夹、hf_lt+r_of_lt_lastIdxG+分支等号排除右夹）/normalizer（hJf）。 -/
theorem toggleGList_mem_isChain (r : Subgroup X → Prop) [DecidablePred r]
    (hmono : ∀ a b : Subgroup X, r a → a ≤ b → r b)
    (f : Subgroup X → Subgroup X)
    (hf_ge : ∀ Q, Q ≤ f Q) (hf_ne : ∀ Q, Q ≠ f Q)
    (hf_lt : ∀ Q Q', Q < Q' → r Q' → f Q ≤ Q')
    {J P : Subgroup X} (hJf : ∀ Q, J ≤ Subgroup.normalizer ↑(f Q))
    {l : List (Subgroup X)} (hC : IsChain J P l) :
    IsChain J P (toggleGList r f l) := by
  have hi : lastIdxNotLeG r l < l.length := lastIdxNotLeG_lt_length r hC.1
  have hp : l.Pairwise (· < ·) := hC.2.2.1
  set A : Subgroup X := l.getD (lastIdxNotLeG r l) (⊥ : Subgroup X) with hA
  have hAlt : A < f A := lt_of_le_of_ne (hf_ge A) (hf_ne A)
  simp only [toggleGList]
  split
  · -- 删除分支
    rename_i h
    obtain ⟨hilt, hR⟩ := h
    refine ⟨?_, ?_, eraseIdx_pairwise (lastIdxNotLeG r l + 1) l hp, ?_⟩
    · intro hcon
      have h1 := List.length_eraseIdx_add_one hilt
      rw [hcon] at h1
      simp at h1
      omega
    · rw [getD_zero_eraseIdx_of_pos _ _ (by omega)]
      exact hC.2.1
    · intro Q hQ
      exact hC.2.2.2 Q (List.Sublist.mem hQ
        (List.eraseIdx_sublist l (lastIdxNotLeG r l + 1)))
  · -- 插入分支（h : ¬(界∧等)——否定函数应用取两件）
    rename_i h
    have hlenI : (l.insertIdx (lastIdxNotLeG r l + 1) (f A)).length = l.length + 1 :=
      List.length_insertIdx_of_le_length (by omega) _
    refine ⟨fun hcon => by
      have h1 : List.length (l.insertIdx (lastIdxNotLeG r l + 1) (f A)) = 0 :=
        congrArg List.length hcon
      omega, ?_,
      insertIdx_pairwise (lastIdxNotLeG r l + 1) l (by omega) ?_ ?_ hp, ?_⟩
    · rw [getD_zero_insertIdx_of_pos _ _ (by omega) hC.1]
      exact hC.2.1
    · -- 左夹：j ≤ i* ⇒ l[j] ≤ A < f A
      intro j _hjn hjl
      rw [← List.getD_eq_getElem l (d := (⊥ : Subgroup X)) hjl]
      exact lt_of_le_of_lt (pairwise_getD_le hp j (lastIdxNotLeG r l) (by omega)
        (by omega)) hAlt
    · -- 右夹：j ≥ i*+1 ⇒ f A < l[j]（i*+1 处 r 直接由上闭版规格②取）
      intro j hj hjl
      rw [← List.getD_eq_getElem l (d := (⊥ : Subgroup X)) hjl]
      have hA1le : f A ≤ l.getD (lastIdxNotLeG r l + 1) (⊥ : Subgroup X) :=
        hf_lt A _ (pairwise_getD_lt hp (lastIdxNotLeG r l)
          (lastIdxNotLeG r l + 1) (by omega) (by omega))
          (r_of_lt_lastIdxG r hmono hp (by omega) (by omega))
      rcases Nat.lt_or_eq_of_le hj with hjlt | hjeq
      · exact lt_of_le_of_lt hA1le
          (pairwise_getD_lt hp (lastIdxNotLeG r l + 1) j (by omega) hjl)
      · -- j = i*+1：分支内 i*+1 < length 真成立（=j < length），hilt/hneq 分支内建
        rw [← hjeq]
        have hilt : lastIdxNotLeG r l + 1 < l.length := by omega
        have hneq : l.getD (lastIdxNotLeG r l + 1) (⊥ : Subgroup X) ≠ f A := by
          intro hEq
          exact h ⟨hilt, hEq⟩
        exact lt_of_le_of_ne hA1le (Ne.symm hneq)
    · -- normalizer：老成员继承+新成员 hJf
      intro Q hQ
      rw [List.mem_insertIdx (by omega)] at hQ
      rcases hQ with rfl | hQm
      · exact hJf _
      · exact hC.2.2.2 Q hQm

/-- ★nonnormal_cancellation（打样组装件）：泛装配 f 的链族消去。
链族=全体 J-正规链（pcoreChainFinset 复用——nonnorm 消去发生在原文
"alternating sum over chain orbits" 的链族上）；tog=toggleGList；
对合=toggleGList_involution（列表层直接）；反号=length_toggleGenListG 桥。
装配假设四件（hf_r/hf_ge/hf_ne/hf_lt）=原文 R 三性质（R ⊴ P/A<R/R≤Q_{i+1}）
的假设化登记——p-群极大子群论证（R<P）与 normalClosure 具体化候深水区。 -/
theorem nonnormal_cancellation [Fintype X] {J P : Subgroup X}
    (r : Subgroup X → Prop) [DecidablePred r]
    (hmono : ∀ a b : Subgroup X, r a → a ≤ b → r b)
    (f : Subgroup X → Subgroup X)
    (hf_r : ∀ Q, r (f Q)) (hf_ge : ∀ Q, Q ≤ f Q) (hf_ne : ∀ Q, Q ≠ f Q)
    (hf_lt : ∀ Q Q', Q < Q' → r Q' → f Q ≤ Q')
    (hJP : J ≤ Subgroup.normalizer ↑P)
    (hJf : ∀ Q, J ≤ Subgroup.normalizer ↑(f Q)) :
    ∑ l ∈ pcoreChainFinset J P, (-1 : ℤ) ^ l.length = 0 := by
  classical
  -- （hJP 仅链族记号依赖·组装体内未用——保留签名对称性）
  let tog : {l // l ∈ pcoreChainFinset J P} → {l // l ∈ pcoreChainFinset J P} := fun a =>
    let ht₁ : IsChain J P (toggleGList r f a.1) :=
      toggleGList_mem_isChain (J := J) (P := P) r hmono f hf_ge hf_ne hf_lt hJf
        (Alp.mem_pcoreChainFinset.mp a.2)
    ⟨toggleGList r f a.1, Alp.mem_pcoreChainFinset.mpr ht₁⟩
  -- 对合（列表层直接）
  have hff' : ∀ a : {l // l ∈ pcoreChainFinset J P}, tog (tog a) = a := by
    intro a
    refine Subtype.ext ?_
    have hchain : IsChain J P a.1 := Alp.mem_pcoreChainFinset.mp a.2
    exact toggleGList_involution r hmono f hf_r hchain.1 hchain.2.2.1
  rw [← Finset.sum_coe_sort (pcoreChainFinset J P) fun l => (-1 : ℤ) ^ l.length]
  exact Alp.sum_eq_zero_of_sign_reversing_equiv
    (fun a : {l // l ∈ pcoreChainFinset J P} => (-1 : ℤ) ^ (a : List (Subgroup X)).length)
    ⟨tog, tog, hff', hff'⟩
    (fun a => by
      have hchain : IsChain J P a.1 := Alp.mem_pcoreChainFinset.mp a.2
      exact toggleGenListG_pow_length_reverse r
        (f (a.1.getD (lastIdxNotLeG r a.1) (⊥ : Subgroup X))) hchain.1)

end Alp
