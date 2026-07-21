import MyProofs.PosteriorProcess.Basic
import MyProofs.PosteriorProcess.Existence
import MyProofs.PosteriorProcess.Sufficiency
import MyProofs.PosteriorProcess.DoobDynkin
import MyProofs.PosteriorProcess.Martingale
import MyProofs.PosteriorProcess.FootnoteBaire

/-!
# Lemma 1「Posterior process」聚合入口

对应论文 `\label{lem:posterior-martingale}`。形式化进度（详见各文件顶部的
"论文原文陈述 + 逐符号对照"，以及项目根目录的 CORRESPONDENCE.md）：

| 论文部分         | Lean 声明                              | 状态       |
|------------------|----------------------------------------|------------|
| 存在性 + 核性质   | `PosteriorProcess.kernel_exists`       | 🔵 `sorry` |
| (i) 充分性       | （待陈述）                              | ⚪ 未陈述   |
| (ii) Doob–Dynkin（抽象） | `PosteriorProcess.factorization` | ✅ 已证    |
| (ii) Δ(Θ) 标准 Borel（库缺口） | `PosteriorProcess.deltaTheta_standardBorel` | 🔵 `sorry` |
| (ii) 完整版      | `PosteriorProcess.factorization_posterior` | 🔵 依赖上者 |
| (iii) 鞅性质     | `PosteriorProcess.testfun_martingale`  | ✅ 已证    |
| (i) 脚注反证（审查）| `PosteriorProcess.indicatorRat_not_pointwiseLimit_continuous` | ✅ 已证 |
-/
