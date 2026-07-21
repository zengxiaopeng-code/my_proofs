import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Lemma 1 (Posterior process) · 共享设置

本文件夹 `PosteriorProcess/` 一一对应论文 **Lemma 1「Posterior process」**
(`\label{lem:posterior-martingale}`)。它被拆成 4 个节点，每个节点一个文件：

| 论文中的部分                    | 文件                | Lean 声明                              |
|---------------------------------|---------------------|----------------------------------------|
| 存在性 + 核性质 (eq:kernel-property) | `Existence.lean`    | `PosteriorProcess.kernel_exists`       |
| Part (i) 充分统计量             | `Sufficiency.lean`  | （待陈述）                             |
| Part (ii) Doob–Dynkin 因子分解  | `DoobDynkin.lean`   | `PosteriorProcess.factorization`       |
| Part (iii) 鞅性质               | `Martingale.lean`   | `PosteriorProcess.testfun_martingale` ✅|

## 论文对象 ↔ Mathlib 类型
| 论文记号                    | Mathlib 建模                                              |
|-----------------------------|----------------------------------------------------------|
| $(\Omega,\mathcal F,\mathbb P)$ | `[MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]` |
| $t\in\mathbb T$             | `{ι : Type*} [Preorder ι]`                                |
| 滤子 $(\mathcal F_t)$       | `(ℱ : MeasureTheory.Filtration ι m)`                      |
| $\Theta$（紧 Polish）       | `[MeasurableSpace Θ] [StandardBorelSpace Θ]`              |
| $\theta:\Omega\to\Theta$    | `(θ : Ω → Θ)`, `Measurable θ`                             |
| 后验核 $S_t:\Omega\to\Delta(\Theta)$ | `Ω → Measure Θ`（点点是概率测度）               |
| $\varphi:\Theta\to\mathbb R$（有界 Borel） | `(φ : Θ → ℝ)`, `Measurable φ` + 有界        |
| $\mathbb E[\varphi(\theta)\mid\mathcal F_t]$ | `P[(φ ∘ θ) | ℱ t]`                       |

每个证明文件重新声明所需 `variable`（Lean 的 `variable` 不跨文件）。
-/

open MeasureTheory

namespace PosteriorProcess

end PosteriorProcess
