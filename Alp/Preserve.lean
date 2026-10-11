import Mathlib
import Alp.Defs
import Alp.ChainProps
import Alp.Toggle

/-!
# Alp · 打样第 5 件（⑤a）：toggle 保严格序——纯列表引理

insertIdx/eraseIdx 对 Pairwise (·<·) 的保持（index 形式条件版）。
pcore 实例（Q_i < Q_i⊔P < Q_{i+1} 落位）候下件。
-/

namespace Alp

/-- 纯列表：按位条件下的 insertIdx 保严格序。
hleft：插入位之前全体 < a；hright：a < 插入位之后全体。 -/
theorem insertIdx_pairwise {α : Type*} [Preorder α] {a : α} : ∀ (n : ℕ) (l : List α),
    (hn : n ≤ l.length) →
    (∀ (j : ℕ) (_hjn : j < n) (hjl : j < l.length), l[j]'hjl < a) →
    (∀ (j : ℕ) (_hjn : n ≤ j) (hjl : j < l.length), a < l[j]'hjl) →
    l.Pairwise (· < ·) → (l.insertIdx n a).Pairwise (· < ·) := by
  intro n
  induction n with
  | zero =>
    intro l _hn _hleft hright hpair
    refine List.pairwise_cons.mpr ⟨fun c hc => ?_, hpair⟩
    obtain ⟨j, hj, hje⟩ := (mem_iff_getElem_idx).mp hc
    rw [← hje]
    exact hright j (by omega) hj
  | succ n ih =>
    intro l hn hleft hright hpair
    cases l with
    | nil => exact absurd hn (by simp [List.length_nil])
    | cons b t =>
      have hnle : n ≤ t.length := by
        simp only [List.length_cons] at hn
        omega
      show (b :: t.insertIdx n a).Pairwise (· < ·)
      obtain ⟨hheadb, htailb⟩ := List.pairwise_cons.mp hpair
      refine List.pairwise_cons.mpr ⟨fun c hc => ?_, ih t hnle ?_ ?_ htailb⟩
      · rw [List.mem_insertIdx hnle] at hc
        rcases hc with rfl | hct
        · exact hleft 0 (by omega) (by omega)
        · exact hheadb c hct
      · intro j hj hjl
        exact hleft (j + 1) (by omega) (by simp only [List.length_cons] at hjl ⊢; omega)
      · intro j hj hjl
        exact hright (j + 1) (by omega) (by simp only [List.length_cons] at hjl ⊢; omega)

/-- 纯列表：eraseIdx 保严格序（严格序传递性吸收被删元素）。 -/
theorem eraseIdx_pairwise {α : Type*} [Preorder α] : ∀ (n : ℕ) (l : List α),
    l.Pairwise (· < ·) → (l.eraseIdx n).Pairwise (· < ·) := by
  intro n
  induction n with
  | zero =>
    intro l hpair
    cases l with
    | nil => exact hpair.tail
    | cons a t => exact hpair.tail
  | succ n ih =>
    intro l hpair
    cases l with
    | nil => exact List.Pairwise.nil
    | cons b t =>
      show (b :: t.eraseIdx n).Pairwise (· < ·)
      obtain ⟨hheadb, htailb⟩ := List.pairwise_cons.mp hpair
      refine List.pairwise_cons.mpr ⟨fun c hc => ?_, ih t htailb⟩
      exact hheadb c (List.Sublist.mem hc (List.eraseIdx_sublist t n))

variable {X : Type*} [Group X]

/-! ## ⑤b：pcore 实例落位——togglePcoreList 保严格序 -/

/-- pcore toggle 保严格序：插入位 R=Q_i⊔P 严格夹心（Q_i < R 由 P≰Q_i spec①；
R < 后继由 sup_le+spec②+分支条件排除相等）。 -/
theorem togglePcoreList_pairwise (P : Subgroup X) {J : Subgroup X} (C : NormChain J)
    (hP : P ≠ ⊥) :
    (togglePcoreList P C).Pairwise (· < ·) := by
  have hi := lastIdxNotLe_lt_length P C.hne
  have hp : C.members.Pairwise (· < ·) := C.hstrict
  have hspec1 := getD_lastIdxNotLe_notLe P C hP
  simp only [togglePcoreList]
  split
  · -- 删除分支
    rename_i h
    exact eraseIdx_pairwise (lastIdxNotLe P C.members + 1) C.members hp
  · -- 插入分支
    rename_i h
    have hgt : C.members.getD (lastIdxNotLe P C.members) (⊥ : Subgroup X)
        < C.members.getD (lastIdxNotLe P C.members) (⊥ : Subgroup X) ⊔ P := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro hEq
      exact hspec1 (by rw [hEq]; exact le_sup_right)
    refine insertIdx_pairwise (lastIdxNotLe P C.members + 1) C.members (by omega) ?_ ?_ hp
    · intro j _hjn hjl
      rw [← List.getD_eq_getElem C.members (d := (⊥ : Subgroup X)) hjl]
      refine lt_of_le_of_lt ?_ hgt
      exact pairwise_getD_le hp j (lastIdxNotLe P C.members) (by omega) (by omega)
    · intro j hj hjl
      rw [← List.getD_eq_getElem C.members (d := (⊥ : Subgroup X)) hjl]
      have hilt1 : lastIdxNotLe P C.members + 1 < C.members.length := by omega
      have hRle : C.members.getD (lastIdxNotLe P C.members) (⊥ : Subgroup X) ⊔ P
          ≤ C.members.getD (lastIdxNotLe P C.members + 1) (⊥ : Subgroup X) :=
        sup_le (pairwise_getD_le hp (lastIdxNotLe P C.members)
          (lastIdxNotLe P C.members + 1) (by omega) hilt1)
          (le_of_lt_lastIdx P hp (by omega) hilt1)
      have hRlt1 : C.members.getD (lastIdxNotLe P C.members) (⊥ : Subgroup X) ⊔ P
          < C.members.getD (lastIdxNotLe P C.members + 1) (⊥ : Subgroup X) := by
        refine lt_of_le_of_ne hRle ?_
        intro hEq
        exact h ⟨hilt1, hEq.symm⟩
      rcases Nat.lt_or_eq_of_le hj with hjlt | hjeq
      · exact lt_of_lt_of_le hRlt1
          (pairwise_getD_le hp (lastIdxNotLe P C.members + 1) j (by omega) hjl)
      · rw [← hjeq]; exact hRlt1

/-- ⑤b' 桥：正规化的 map 形式（conj 共轭自同构保持 K）。 -/
theorem normalizer_iff_map (f : X →* X) (hf_inj : Function.Injective f) {g : X}
    (hgf : ∀ x, f x = g * x * g⁻¹) {K : Subgroup X} :
    g ∈ Subgroup.normalizer (↑K : Set X) ↔ Subgroup.map f K = K := by
  constructor
  · intro h
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨z, hzK, hz⟩ := Subgroup.mem_map.mp hy
      have h0 := (Subgroup.mem_normalizer_iff.mp h z).mp hzK
      have h1 : f z ∈ K := by rwa [← hgf z] at h0
      rwa [hz] at h1
    · intro y hy
      have hz : g⁻¹ * y * g ∈ K := by
        have h3 : g * (g⁻¹ * y * g) * g⁻¹ ∈ K := by
          group
          exact hy
        exact (Subgroup.mem_normalizer_iff.mp h (g⁻¹ * y * g)).mpr h3
      exact ⟨g⁻¹ * y * g, hz, by rw [hgf (g⁻¹ * y * g)]; group⟩
  · intro h x
    constructor
    · intro hx
      have h2 : f x ∈ Subgroup.map f K := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [h] at h2
      rwa [hgf x] at h2
    · intro hx
      rw [← h] at hx
      obtain ⟨z, hzK, hz⟩ := Subgroup.mem_map.mp hx
      rw [← hgf x] at hz
      have hzx : z = x := hf_inj hz
      rw [← hzx]
      exact hzK

/-- ⑤b'：正规化子对 sup 的封闭（conj 自同构保 Q、P ⇒ 保 Q⊔P）——closure 路线。 -/
theorem normalizer_sup {Q P : Subgroup X} {g : X}
    (hQ : g ∈ Subgroup.normalizer ↑Q) (hP : g ∈ Subgroup.normalizer ↑P) :
    g ∈ Subgroup.normalizer ↑(Q ⊔ P) := by
  set fdef : X →* X := MulEquiv.toMonoidHom (MulAut.conj g) with hfdef
  have hf_inj : Function.Injective fdef := by
    rw [hfdef]; exact MulEquiv.injective _
  have hgf : ∀ x, fdef x = g * x * g⁻¹ := by
    intro x
    rfl
  rw [normalizer_iff_map fdef hf_inj hgf, Subgroup.sup_eq_closure,
      MonoidHom.map_closure fdef, Set.image_union,
      ← Subgroup.coe_map fdef, ← Subgroup.coe_map fdef,
      ← Subgroup.sup_eq_closure]
  rw [normalizer_iff_map fdef hf_inj hgf] at hQ hP
  rw [hQ, hP]
  exact Subgroup.sup_eq_closure Q P



/-! ## ⑤c：族 F 具体化——链谓词与 toggle 保族 -/

variable [Fintype X]

/-- head 保持（eraseIdx，位 ≥1）。 -/
theorem getD_zero_eraseIdx_of_pos {α : Type*} {d : α} : ∀ (n : ℕ) (l : List α), 1 ≤ n →
    (l.eraseIdx n).getD 0 d = l.getD 0 d := by
  intro n
  induction n with
  | zero => intro l h; exact absurd h (by omega)
  | succ n ih =>
    intro l h
    cases l with
    | nil => rfl
    | cons a t =>
      simp only [List.eraseIdx_cons_succ, List.getD_cons_zero]

/-- head 保持（insertIdx，位 ≥1 且 l 非空）——rfl 直证（cons-iota）。 -/
theorem getD_zero_insertIdx_of_pos {α : Type*} {d d' : α} : ∀ (n : ℕ) (l : List α), 1 ≤ n →
    l ≠ [] → (l.insertIdx n d).getD 0 d' = l.getD 0 d' := by
  intro n l h hne
  cases n with
  | zero => exact absurd h (by omega)
  | succ n =>
    cases l with
    | nil => exact absurd rfl hne
    | cons a t => rfl

/-- 链谓词（pcore 族成员资格）：非空+头⊥+严格序+J 正规化全体成员。 -/
def IsChain (J P : Subgroup X) (l : List (Subgroup X)) : Prop :=
  l ≠ [] ∧ l.getD 0 (⊥ : Subgroup X) = ⊥ ∧ l.Pairwise (· < ·) ∧
    ∀ Q ∈ l, J ≤ Subgroup.normalizer ↑Q

/-- 偏序上两条严格升序列表若成员相同则相等（链由成员集唯一显化）。 -/
theorem chain_ext_of_mem_iff {α : Type*} [Preorder α] : ∀ (a b : List α),
    a.Pairwise (· < ·) → b.Pairwise (· < ·) → (∀ x, x ∈ a ↔ x ∈ b) → a = b := by
  intro a b
  induction a generalizing b with
  | nil =>
    intro _ _ hmem
    cases b with
    | nil => rfl
    | cons c t => exact absurd ((hmem c).2 (List.mem_cons_self)) (by simp)
  | cons x t iht =>
    intro ha hb hmem
    cases b with
    | nil => exact absurd ((hmem x).1 (List.mem_cons_self)) (by simp)
    | cons y t' =>
      obtain ⟨hax, hta⟩ := List.pairwise_cons.mp ha
      obtain ⟨hbx, htb'⟩ := List.pairwise_cons.mp hb
      have hxinb : x ∈ y :: t' := (hmem x).1 (List.mem_cons_self)
      have hyina : y ∈ x :: t := (hmem y).2 (List.mem_cons_self)
      have hxy : x = y := by
        rcases List.mem_cons.mp hxinb with hxy' | hxt
        · exact hxy'
        · exfalso
          have hylt : y < x := hbx x hxt
          rcases List.mem_cons.mp hyina with hyy | hyt
          · rw [hyy] at hylt; exact lt_irrefl x hylt
          · exact lt_asymm (hax y hyt) hylt
      rw [hxy]
      have hmem' : ∀ z, z ∈ t ↔ z ∈ t' := by
        intro z
        constructor
        · intro hz
          rcases List.mem_cons.mp ((hmem z).1 (List.mem_cons_of_mem x hz)) with hzy | hzt'
          · rw [hzy] at hz ⊢
            rw [← hxy] at hz
            exact absurd (hax x hz) (lt_irrefl x)
          · exact hzt'
        · intro hz
          rcases List.mem_cons.mp ((hmem z).2 (List.mem_cons_of_mem y hz)) with hzx | hzt
          · rw [hzx] at hz
            have hylt : y < x := hbx x hz
            rcases List.mem_cons.mp hyina with hyy | hyt
            · rw [hyy] at hylt; exact absurd hylt (lt_irrefl x)
            · exact (lt_asymm (hax y hyt) hylt).elim
          · exact hzt
      exact congrArg (fun l => y :: l) (iht t' hta htb' hmem')

/-- pcore 链族构造（签名子类型携带成员刻划——def 内 letI 实例不外泄，
刻划必须同块导出经 Aux.2 出口）。有限性：List α（α 非空）本质无限，
Fintype (List _) 不存在——走 subtype：严格升序链由成员集唯一显化
（chain_ext_of_mem_iff），l ↦ l.toFinset 在链上单射，注入有限 Finset (Subgroup X)。 -/
noncomputable def pcoreChainFinsetAux (J P : Subgroup X) :
    {F : Finset (List (Subgroup X)) // ∀ l, l ∈ F ↔ IsChain J P l} := by
  classical
  haveI : Finite (Subgroup X) :=
    Finite.of_injective (fun K : Subgroup X => (K : Set X)) SetLike.coe_injective
  letI : Fintype (Subgroup X) := Fintype.ofFinite (Subgroup X)
  have hinj : Function.Injective (fun a : {l : List (Subgroup X) // IsChain J P l} =>
      a.1.toFinset) := by
    intro a b hab
    simp only at hab
    have hmem : ∀ x, x ∈ a.1 ↔ x ∈ b.1 := fun x => by
      rw [← List.mem_toFinset, ← List.mem_toFinset, hab, List.mem_toFinset]
    exact Subtype.ext (chain_ext_of_mem_iff a.1 b.1 a.2.2.2.1 b.2.2.2.1 hmem)
  haveI : Finite {l : List (Subgroup X) // IsChain J P l} :=
    Finite.of_injective _ hinj
  letI : Fintype {l : List (Subgroup X) // IsChain J P l} := Fintype.ofFinite _
  refine ⟨(Finset.univ : Finset {l : List (Subgroup X) // IsChain J P l}).image Subtype.val,
    fun l => ?_⟩
  constructor
  · intro hmem
    obtain ⟨b, -, hbe⟩ := Finset.mem_image.mp hmem
    rw [← hbe]
    exact b.2
  · intro hl
    exact Finset.mem_image.mpr ⟨⟨l, hl⟩, Finset.mem_univ _, rfl⟩

/-- pcore 链族（全部 J-正规 pcore 链的 Finset）。 -/
noncomputable def pcoreChainFinset (J P : Subgroup X) : Finset (List (Subgroup X)) :=
  (pcoreChainFinsetAux J P).1

/-- 成员刻划：l ∈ 链族 ↔ l 是 J-正规 pcore 链。 -/
theorem mem_pcoreChainFinset {J P : Subgroup X} {l : List (Subgroup X)} :
    l ∈ pcoreChainFinset J P ↔ IsChain J P l :=
  (pcoreChainFinsetAux J P).2 l

-- ⑤c 核心：toggle 保族（htog 的实质内容）。hJP：J 正规化 P（原稿 setup）。
-- （omit Fintype：签名不需要 [Fintype X]——term-mode doc comment 与 omit in 冲突降级为普通注释）
omit [Fintype X] in theorem togglePcoreList_mem_isChain {J P : Subgroup X} (hP : P ≠ ⊥)
    (hJP : J ≤ Subgroup.normalizer ↑P) {C : NormChain J}
    (hC : IsChain J P C.members) :
    IsChain J P (togglePcoreList P C) := by
  have hi := lastIdxNotLe_lt_length P C.hne
  have hp : C.members.Pairwise (· < ·) := C.hstrict
  have hspec1 := getD_lastIdxNotLe_notLe P C hP
  unfold IsChain at hC ⊢
  obtain ⟨hne, hd0, hp', hnorm⟩ := hC
  simp only [togglePcoreList]
  split
  · -- 删除分支
    rename_i h
    refine ⟨?_, ?_, eraseIdx_pairwise (lastIdxNotLe P C.members + 1) C.members hp, ?_⟩
    · intro hcon
      have h1 := List.length_eraseIdx_add_one h.1
      rw [hcon] at h1
      simp at h1
      omega
    · rw [getD_zero_eraseIdx_of_pos _ _ (by omega)]
      exact hd0
    · intro Q hQ
      exact hnorm Q (List.Sublist.mem hQ
        (List.eraseIdx_sublist C.members (lastIdxNotLe P C.members + 1)))
  · -- 插入分支
    rename_i h
    have hlenI : (C.members.insertIdx (lastIdxNotLe P C.members + 1)
        (C.members.getD (lastIdxNotLe P C.members) ⊥ ⊔ P)).length = C.members.length + 1 :=
      List.length_insertIdx_of_le_length (by omega) _
    refine ⟨fun hcon => by
      have h1 : List.length (C.members.insertIdx (lastIdxNotLe P C.members + 1)
          (C.members.getD (lastIdxNotLe P C.members) ⊥ ⊔ P)) = 0 :=
        congrArg List.length hcon
      omega, ?_,
      insertIdx_pairwise (lastIdxNotLe P C.members + 1) C.members (by omega)
      ?_ ?_ hp, ?_⟩
    · have h1 : (C.members.insertIdx (lastIdxNotLe P C.members + 1)
          (C.members.getD (lastIdxNotLe P C.members) ⊥ ⊔ P)).getD 0 (⊥ : Subgroup X)
        = C.members.getD 0 (⊥ : Subgroup X) :=
        getD_zero_insertIdx_of_pos _ _ (by omega) hne
      rw [h1]
      exact hd0
    · intro j _hjn hjl
      have hgt : C.members.getD (lastIdxNotLe P C.members) (⊥ : Subgroup X)
          < C.members.getD (lastIdxNotLe P C.members) (⊥ : Subgroup X) ⊔ P :=
        lt_of_le_of_ne le_sup_left (fun hEq => hspec1 (by rw [hEq]; exact le_sup_right))
      have hle : C.members.getD j (⊥ : Subgroup X)
          ≤ C.members.getD (lastIdxNotLe P C.members) (⊥ : Subgroup X) :=
        pairwise_getD_le hp j (lastIdxNotLe P C.members) (by omega) (by omega)
      rw [← List.getD_eq_getElem C.members (d := (⊥ : Subgroup X)) hjl]
      exact lt_of_le_of_lt hle hgt
    · intro j hj hjl
      rw [← List.getD_eq_getElem C.members (d := (⊥ : Subgroup X)) hjl]
      have hilt1 : lastIdxNotLe P C.members + 1 < C.members.length := by omega
      have hR1 : C.members.getD (lastIdxNotLe P C.members) (⊥ : Subgroup X) ⊔ P
          < C.members.getD (lastIdxNotLe P C.members + 1) (⊥ : Subgroup X) := by
        refine lt_of_le_of_ne ?_ (fun hEq => h ⟨hilt1, hEq.symm⟩)
        exact sup_le (pairwise_getD_le hp (lastIdxNotLe P C.members)
          (lastIdxNotLe P C.members + 1) (by omega) hilt1)
          (le_of_lt_lastIdx P hp (by omega) hilt1)
      rcases Nat.lt_or_eq_of_le hj with hjlt | hjeq
      · have hle : C.members.getD (lastIdxNotLe P C.members + 1) (⊥ : Subgroup X)
          ≤ C.members.getD j (⊥ : Subgroup X) :=
          pairwise_getD_le hp (lastIdxNotLe P C.members + 1) j (by omega) hjl
        exact lt_of_lt_of_le hR1 hle
      · rw [← hjeq]
        exact hR1
    · intro Q hQ
      rw [List.mem_insertIdx (by omega)] at hQ
      rcases hQ with rfl | hQm
      · intro j hj
        have hmemQi : C.members.getD (lastIdxNotLe P C.members) (⊥ : Subgroup X)
            ∈ C.members := by
          rw [List.getD_eq_getElem C.members (d := (⊥ : Subgroup X)) (by omega)]
          exact List.getElem_mem (by omega)
        exact normalizer_sup (hnorm _ hmemQi hj) (hJP hj)
      · exact hnorm Q hQm

end Alp
