import MyProofs.Foundations.PosteriorProcess.Basic
import MyProofs.Foundations.PosteriorProcess.Existence
import MyProofs.Foundations.PosteriorProcess.Sufficiency
import MyProofs.Foundations.PosteriorProcess.DoobDynkin
import MyProofs.Foundations.PosteriorProcess.Martingale

/-!
# Lemma 1「Posterior process」聚合入口

对应论文 `\label{lem:posterior-martingale}`。形式化进度（详见各文件顶部的
"论文原文陈述 + 逐符号对照"，以及项目根目录的 CORRESPONDENCE.md）：

| 论文部分         | Lean 声明                              | 状态       |
|------------------|----------------------------------------|------------|
| 存在性 + 核性质   | `PosteriorProcess.kernel_exists`       | ✅ 已证    |
| (i) 充分性       | `PosteriorProcess.sufficiency`         | ✅ 已证    |
| (ii) Doob–Dynkin（抽象） | `PosteriorProcess.factorization` | ✅ 已证    |
| (ii) Δ(Θ) 标准 Borel | `PosteriorProcess.deltaTheta_standardBorel` | ✅ 已证    |
| (ii) 完整版      | `PosteriorProcess.factorization_posterior` | ✅ 已证    |
| (iii) 鞅性质     | `PosteriorProcess.testfun_martingale`  | ✅ 已证    |

**Lemma 1 全部四部分已完整形式化，无 `sorry`**，全链仅依赖标准公理
`propext / Classical.choice / Quot.sound`。其中 `deltaTheta_standardBorel`（Δ(Θ) 标准 Borel）
是从零证成的 Mathlib 库缺口：`deltaTheta_polishSpace`（弱拓扑 Polish）＋ `deltaTheta_borelSpace`
（Giry σ-代数 = 弱拓扑 Borel σ-代数，双向）。
-/
