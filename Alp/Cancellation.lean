import Mathlib

/-!
# Alp · 打样第 1 件：反号对合消去抽象模式

202 家族（块状 Alperin 权猜想）pcore-cancellation 与 nonnormal-cancellation
两条引理共用的数学骨架：若有限集上有一个对合等价把每点的权重映到相反数，
则总权重为零。原文的 toggle 构造（插入/删除链成员）给出该模式的具体实例。

证明：∑ w a = ∑ w (f a)（等价重索引）= ∑ -(w a) = -∑ w a，故 ∑ w a = 0。
-/

namespace Alp

/-- 反号对合消去：若对合等价 `f` 把权重 `w` 反号，则总权重为零。

这就是 202 手稿两条消去引理（lem:pcore-cancellation / lem:nonnormal-cancellation）
的公共抽象模式：原文对链轨道构造 toggle 对合（插入/删除中间成员），
验证它是无不动点、保链属性、反链长的对合——即落进本引理的条件。 -/
theorem sum_eq_zero_of_sign_reversing_equiv {α : Type*} [Fintype α]
    (w : α → ℤ) (f : α ≃ α) (hrev : ∀ a, w (f a) = -w a) :
    ∑ a, w a = 0 := by
  have h1 : ∑ a, w a = ∑ a, w (f a) :=
    Fintype.sum_equiv f.symm (fun a => w a) (fun a => w (f a)) fun a => by simp
  have h2 : ∑ a, w (f a) = -∑ a, w a := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => hrev a
  rw [h1, h2]
  omega

end Alp

#check @Alp.sum_eq_zero_of_sign_reversing_equiv
