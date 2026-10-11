# alperin-pilot · 202 打样件形式化

**Pilot Lean formalization of the two cancellation lemmas underpinning the "202" manuscript (a block-theoretic Alperin-weight proof claimed CFSG-free): `pcore_cancellation` and `nonnormal_cancellation`. Lean 4 + Mathlib, 54 theorem/lemma declarations, zero sorry.**

## 这是什么 (What this is)

- 独立打样件（两条引理管线验证路线）：以机器验证确认手稿两条关键消去引理的组合骨架是牢靠的——`togglePcoreList` 在正规链上的对合（pcore 侧）及其 G 参数化推广（nonnormal 侧），最终组装为 `pcore_cancellation`（无假设完整版）与 `nonnormal_cancellation`。
- **不是**手稿主定理的完整形式化。可行性评估（在档）：有条件可行——需自建约 3-5k 行块理论基础设施（Mathlib 模表示论目前零覆盖：grep Brauer/Alperin 仅命中无关项）。
- 形式化过程两次逼出语义级问题并修正（min S 语义 / 越界 j 读 ⊥ 需加界）——类型检查作为语义审查工具的实例。

## 内容 (Contents)

| 路径 | 内容 |
|---|---|
| `Alp/Defs.lean` | 定义层：NormChain（members/hne/hhead/hstrict/hnormal 五字段）+ togglePcoreList（手稿 "Toggle Q_i P immediately after Q_i" 规则逐字转写） |
| `Alp/ChainProps.lean` | 链序/位规格引理 |
| `Alp/Preserve.lean` | 稳定/保族件 |
| `Alp/Toggle.lean` | 长度账/对合/无不动点/反号 |
| `Alp/Cancellation.lean` | `pcore_cancellation`（完整无假设版） |
| `Alp/Nonnormal.lean` | G 参数化通用 toggle + `nonnormal_cancellation`（手稿 group.tex:378 逐字转写） |
| `Alp/Assemble.lean` | 组装件 |
| `Alp.lean` | 根 import |
| `lakefile.lean` / `lean-toolchain` / `lake-manifest.json` | 构建配置（与上游研读项目同 toolchain/Mathlib 版本） |

## 验证 (Verification)

- 2026-10-11 复验：`lake build` **8932 jobs 全绿**（Build completed successfully, exit 0）；
- 全项目零 `sorry`（全库 grep 唯一命中为 `Alp/Defs.lean` 头注释中的"零 sorry"字样）；
- 主定理 `#print axioms` 抽检 = `[propext, Classical.choice, Quot.sound]` 标准三件套（2026-10-09/10 收敛轮抽检在档）。

## 状态 (Status)

Companion package（候发布轮，Zenodo record pending）。打样达成（全形式化候主人定）。
License: Code MIT / Docs CC-BY-4.0。
