import MyProofs.PosteriorProcess.Basic
import MyProofs.PosteriorProcess.Existence
import MyProofs.PosteriorProcess.Sufficiency
import MyProofs.PosteriorProcess.DoobDynkin
import MyProofs.PosteriorProcess.Martingale

/-!
# Lemma 1「Posterior process」聚合入口

对应论文 `\label{lem:posterior-martingale}`。形式化进度（详见各文件顶部的
"论文原文陈述 + 逐符号对照"，以及项目根目录的 CORRESPONDENCE.md）：

| 论文部分         | Lean 声明                              | 状态       |
|------------------|----------------------------------------|------------|
| 存在性 + 核性质   | `PosteriorProcess.kernel_exists`       | 🔵 `sorry` |
| (i) 充分性       | （待陈述）                              | ⚪ 未陈述   |
| (ii) 因子分解    | `PosteriorProcess.factorization`       | 🔵 `sorry` |
| (iii) 鞅性质     | `PosteriorProcess.testfun_martingale`  | ✅ 已证    |
-/
