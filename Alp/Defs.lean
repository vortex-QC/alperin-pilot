import Mathlib

/-!
# Alp · 打样第 2 件：链类型与 toggle 定义（pcore 版）

202 手稿 lem:pcore-cancellation 的形式化基础设施。
链 = J-正规化子群严格升链（⊥=Q₀<Q₁<…）；
toggle = 取最大 i 使 P≴Q_i，在 i 后插入/删除 Q_i⊔P（原文 toggle 构造）。
本文件只做定义层（零 sorry·性质证明归第 ③ 件）。
-/

namespace Alp

open scoped Classical

variable {X : Type*} [Group X]

/-- J-正规化子群链：非空严格升链，头为平凡群，每个成员被 J 正规化。 -/
structure NormChain (J : Subgroup X) where
  members : List (Subgroup X)
  hne : members ≠ []
  hhead : members.head! = ⊥
  hstrict : members.Pairwise (· < ·)
  hnormal : ∀ Q ∈ members, J ≤ Subgroup.normalizer Q

/-- 最大下标 i 使 P ≰ members[i]（经典选择）。
数学：S={i : P≤Q_i} 沿链上闭（P≤Q_i ∧ Q_i≤Q_j → P≤Q_j）故 S={k..} 或空；
最大不满足 = min S - 1（S 空 = length-1）。实现：原列表 findIdx? 首个满足 = min S。 -/
noncomputable def lastIdxNotLe (P : Subgroup X) (l : List (Subgroup X)) : ℕ :=
  match l.findIdx? (fun Q => P ≤ Q) with
  | some k => k - 1
  | none => l.length - 1

/-- pcore toggle 的原始列表层构造：
最大 i 处（P≴Q_i），若其后一项恰为 Q_i⊔P 则删除之，否则插入之。
原文逐字对应："Toggle Q_iP immediately after Q_i"。 -/
noncomputable def togglePcoreList (P : Subgroup X) {J : Subgroup X}
    (C : NormChain J) : List (Subgroup X) :=
  let i := lastIdxNotLe P C.members
  let Q := C.members.getD i ⊥
  let R := Q ⊔ P
  if _h : i + 1 < C.members.length ∧ C.members.getD (i + 1) ⊥ = R then
    C.members.eraseIdx (i + 1)
  else
    C.members.insertIdx (i + 1) R

end Alp
