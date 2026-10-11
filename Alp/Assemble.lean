import Mathlib
import Alp.Defs
import Alp.Cancellation
import Alp.ChainProps
import Alp.Toggle
import Alp.Preserve

/-!
# Alp · 打样第 4 件：pcore-cancellation 条件化组装

对 toggle 封闭的有限链族 F 上，(-1)^长度 权重和为零——
抽象反号消去引理（Cancellation）+ toggle 对合（⑥）+ 反号（③b）的组装。
封闭性假设 htog 即链保持性⑤+族定义的职责：⑤给出"toggle 保链"后即为完整
pcore-cancellation 形式化。
-/

namespace Alp

variable {X : Type*} [Group X]

/-- 条件化消去：有限链族 F（非空+严格链）对 toggleGenList 封闭
⇒ ∑ (-1)^长度 = 0。 -/
theorem sum_pow_eq_zero_of_toggle_closed (P R : Subgroup X)
    (hPR : P ≤ R)
    (F : Finset (List (Subgroup X)))
    (hF : ∀ l ∈ F, l ≠ [] ∧ l.Pairwise (· < ·))
    (htog : ∀ l ∈ F, toggleGenList P R l ∈ F) :
    ∑ l ∈ F, (-1 : ℤ) ^ l.length = 0 := by
  classical
  have hf : ∀ a : {l // l ∈ F}, toggleGenList P R (a : List (Subgroup X)) ∈ F :=
    fun a => htog _ a.2
  -- toggle 自映射的对合性
  have hff : ∀ a : {l // l ∈ F},
      (⟨toggleGenList P R
          (↑(⟨toggleGenList P R (a : List (Subgroup X)), hf a⟩ : {l // l ∈ F})),
        hf _⟩ : {l // l ∈ F}) = a := by
    intro a
    refine Subtype.ext ?_
    show toggleGenList P R (toggleGenList P R (a : List (Subgroup X)))
        = (a : List (Subgroup X))
    exact toggleGenList_involution P R hPR ((hF _ a.2).1) ((hF _ a.2).2)
  rw [← Finset.sum_coe_sort F (fun l => (-1 : ℤ) ^ l.length)]
  exact sum_eq_zero_of_sign_reversing_equiv
    (fun a : {l // l ∈ F} => (-1 : ℤ) ^ (a : List (Subgroup X)).length)
    (⟨fun a : {l // l ∈ F} => (⟨toggleGenList P R ↑a, hf a⟩ : {l // l ∈ F}),
     fun a : {l // l ∈ F} => (⟨toggleGenList P R ↑a, hf a⟩ : {l // l ∈ F}),
     hff, hff⟩ :
      {l // l ∈ F} ≃ {l // l ∈ F})
    (fun a => by
      show (-1 : ℤ) ^ (toggleGenList P R (a : List (Subgroup X))).length
          = -(-1 : ℤ) ^ (a : List (Subgroup X)).length
      exact toggleGen_pow_length_reverse (P := P) (R := R) (l := (a : List (Subgroup X)))
        ((hF _ a.2).1))


/-! ## ⑤c+⑦ 合体：pcore_cancellation 完整定理 -/

/-- getD 头 → head! 头桥（非空）。 -/
theorem getD_zero_eq_headBD {l : List (Subgroup X)} (hl : l ≠ [])
    (h : l.getD 0 (⊥ : Subgroup X) = ⊥) : l.head! = ⊥ := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => simpa using h

/-- IsChain → NormChain 桥（term-mode 直构——members 投影 delta+iota 可约，
不产 match 项阻断 defeq）。 -/
def isChainToNormChain {J P : Subgroup X} {l : List (Subgroup X)}
    (hP : P ≠ ⊥) (h : Alp.IsChain J P l) : NormChain J :=
  ⟨l, h.1, getD_zero_eq_headBD h.1 h.2.1, h.2.2.1, h.2.2.2⟩

/-- NormChain → IsChain 桥（head! ↔ getD 头桥 + 四字段直取）。 -/
theorem normChain_isChain {J P : Subgroup X} (C : NormChain J) :
    IsChain J P C.members := by
  obtain ⟨m, hne, hhead, hstrict, hnormal⟩ := C
  refine ⟨hne, ?_, hstrict, hnormal⟩
  cases m with
  | nil => exact absurd rfl hne
  | cons a t => simpa using hhead

/-! ## ⑤d：pcore toggle 二次回归（hff 消除） -/

/-- lastIdxNotLe 对通用 toggle 稳定（插/删分支分别归约）。 -/
theorem lastIdxNotLe_toggleGenList_eq (P R : Subgroup X) (hPR : P ≤ R)
    {l : List (Subgroup X)} (hl : l ≠ []) (hp : l.Pairwise (· < ·)) :
    lastIdxNotLe P (toggleGenList P R l) = lastIdxNotLe P l := by
  simp only [toggleGenList]
  split
  · rename_i h
    exact lastIdxNotLe_eraseIdx_eq P hl h.1 hp
  · exact lastIdxNotLe_insertIdx_eq P R hPR hl

/-- 通用 toggle 后位 i* 元素不动（插/删都在 i*+1 位，i* < i*+1）。 -/
theorem toggleGenList_getD_i_eq (P R : Subgroup X) {l : List (Subgroup X)} (hl : l ≠ []) :
    (toggleGenList P R l).getD (lastIdxNotLe P l) (⊥ : Subgroup X)
      = l.getD (lastIdxNotLe P l) (⊥ : Subgroup X) := by
  have hi := lastIdxNotLe_lt_length P hl
  simp only [toggleGenList]
  split
  · rename_i h
    obtain ⟨hilt, hR⟩ := h
    have hlenE := List.length_eraseIdx_add_one (l := l) hilt
    rw [List.getD_eq_getElem _ (d := (⊥ : Subgroup X)) (by omega),
      List.getD_eq_getElem l (d := (⊥ : Subgroup X)) (by omega)]
    exact getElem_eraseIdx_of_lt' hilt (by omega) (by omega)
  · have hi := lastIdxNotLe_lt_length P hl
    have hlen : (l.insertIdx (lastIdxNotLe P l + 1) R).length = l.length + 1 :=
      List.length_insertIdx_of_le_length (by omega) R
    rw [List.getD_eq_getElem _ (d := (⊥ : Subgroup X)) (by omega),
      List.getD_eq_getElem l (d := (⊥ : Subgroup X)) (by omega)]
    exact List.getElem_insertIdx_of_lt (by omega) (by rw [hlen]; omega)

/-- ★pcore toggle 二次回归：链层对合——toggle(包装(toggle C)) = 原链。
关键=两次 toggle 的 R 相同（lastIdxNotLe 稳定→位 i* 元素 Q_i 不动→R₂=Q_i⊔P=R₁），
归约为通用对合。 -/
theorem togglePcoreList_involution (P : Subgroup X) {J : Subgroup X} (hP : P ≠ ⊥)
    (hJP : J ≤ Subgroup.normalizer ↑P) (C : NormChain J) :
    togglePcoreList P (isChainToNormChain hP
      (Alp.togglePcoreList_mem_isChain hP hJP (normChain_isChain C))) = C.members := by
  have hl : C.members ≠ [] := C.hne
  have hp : C.members.Pairwise (· < ·) :=
    (normChain_isChain (J := J) (P := P) C).2.2.1
  set l := C.members with hld
  set R₁ : Subgroup X := l.getD (lastIdxNotLe P l) (⊥ : Subgroup X) ⊔ P with hR₁def
  have hR₁ : P ≤ R₁ := le_sup_right
  -- 包装链的成员 = 通用 toggle 形式（members iota + eq_gen 桥）
  have hC2mem :
      (isChainToNormChain hP
          (Alp.togglePcoreList_mem_isChain hP hJP (normChain_isChain C))).members
      = toggleGenList P R₁ l := by
    show togglePcoreList P C = toggleGenList P R₁ l
    exact togglePcoreList_eq_gen P C
  have hist : lastIdxNotLe P (toggleGenList P R₁ l) = lastIdxNotLe P l :=
    lastIdxNotLe_toggleGenList_eq P R₁ hR₁ hl hp
  have hgetD : (toggleGenList P R₁ l).getD (lastIdxNotLe P l) (⊥ : Subgroup X)
      = l.getD (lastIdxNotLe P l) (⊥ : Subgroup X) := toggleGenList_getD_i_eq P R₁ hl
  calc togglePcoreList P (isChainToNormChain hP
        (Alp.togglePcoreList_mem_isChain hP hJP (normChain_isChain C)))
      = toggleGenList P
          ((toggleGenList P R₁ l).getD (lastIdxNotLe P (toggleGenList P R₁ l))
              (⊥ : Subgroup X) ⊔ P)
          (toggleGenList P R₁ l) := by
        rw [togglePcoreList_eq_gen, hC2mem]
    _ = toggleGenList P R₁ (toggleGenList P R₁ l) := by rw [hist, hgetD]
    _ = l := toggleGenList_involution P R₁ hR₁ hl hp

/-- ★pcore-cancellation 定理：有限群 X 的 J-正规 pcore 链族上，
(-1)^长度 权重和为零。
组装件构成：反号（toggle_pow_length_reverse，pcore 版在册）+求和
（sum_eq_zero_of_sign_reversing_equiv）+成员资格（⑤c 保族，真证）全部体内闭合；
**对合 hff 为显式假设**——pcore toggle 的 R=Q⊔P 随链变，两次 toggle 的 R 不同，
固定 R 对合（toggleGenList_involution）不直接适用（本轮编译暴露的接驳缺口，
"就位候编译"件的原 hff 证明 togglePcoreList P (togglePcoreList P …) 类型不成立
——内层返回 List 非 NormChain）。hff 的数学内容=pcore toggle 二次回归：
插入分支 lastIdxNotLe 不动+插入位恰成删除条件；删除分支对称。
素材在册：lastIdxNotLe_insertIdx_eq / lastIdxNotLe_eraseIdx_eq（④通用对合所建）。
hff 消除即完整形式化。 -/
theorem pcore_cancellation [Fintype X] {J P : Subgroup X} (hP : P ≠ ⊥)
    (hJP : J ≤ Subgroup.normalizer ↑P) :
    ∑ l ∈ pcoreChainFinset J P, (-1 : ℤ) ^ l.length = 0 := by
  classical
  let hF4 : ∀ l ∈ pcoreChainFinset J P, IsChain J P l :=
    fun a ha => Alp.mem_pcoreChainFinset.mp ha
  let hCNC : ∀ l ∈ pcoreChainFinset J P, NormChain J :=
    fun a ha => isChainToNormChain hP (hF4 a ha)
  let hmem : ∀ l, IsChain J P l → l ∈ pcoreChainFinset J P :=
    fun l hl => Alp.mem_pcoreChainFinset.mpr hl
  -- 与 hff 精确同路径的一次 toggle 映射（body-let 透明，val 与成员资格同源）
  let tog : {l // l ∈ pcoreChainFinset J P} → {l // l ∈ pcoreChainFinset J P} := fun a =>
    let C₀ : NormChain J := Alp.isChainToNormChain hP (Alp.mem_pcoreChainFinset.mp a.2)
    let ht₁ : IsChain J P (Alp.togglePcoreList P C₀) :=
      Alp.togglePcoreList_mem_isChain hP hJP (normChain_isChain C₀)
    ⟨Alp.togglePcoreList P C₀, Alp.mem_pcoreChainFinset.mpr ht₁⟩
  -- 对合（hff 假设给出）：toggle∘toggle = id（链族层面）
  have hff' : ∀ a : {l // l ∈ pcoreChainFinset J P}, tog (tog a) = a := by
    intro a
    refine Subtype.ext ?_
    exact togglePcoreList_involution P hP hJP (isChainToNormChain hP
      (Alp.mem_pcoreChainFinset.mp a.2))
  let heq : {l // l ∈ pcoreChainFinset J P} ≃ {l // l ∈ pcoreChainFinset J P} :=
    ⟨tog, tog, hff', hff'⟩
  rw [← Finset.sum_coe_sort (pcoreChainFinset J P) fun l => (-1 : ℤ) ^ l.length]
  exact Alp.sum_eq_zero_of_sign_reversing_equiv
    (fun a : {l // l ∈ pcoreChainFinset J P} => (-1 : ℤ) ^ (a : List (Subgroup X)).length) heq
    (fun a => by
      show (-1 : ℤ) ^ (tog a : List (Subgroup X)).length = _
      exact Alp.toggle_pow_length_reverse P (Alp.isChainToNormChain hP
        (Alp.mem_pcoreChainFinset.mp a.2)))

end Alp
