import Mathlib

/-!
# 共享设置：Posterior process (lem:posterior-martingale)

对应论文 Lemma "Posterior process" 的公共对象。这里只做**文档说明**，
真正的定理陈述放在各自的文件里（每个文件重新声明所需的 `variable`）。

论文中的对象 ↔ Mathlib 类型：

| 论文记号                    | Mathlib 建模                                              |
|-----------------------------|----------------------------------------------------------|
| 概率空间 `(Ω, F, P)`        | `[MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]` |
| 时间 `t ∈ 𝕋`               | `{ι : Type*} [Preorder ι]`（可换成 `ℕ` 或 `[0,∞)`）      |
| 滤子 `(F_t)`                | `(ℱ : MeasureTheory.Filtration ι m)`                     |
| 状态空间 `Θ`（紧 Polish）   | `[MeasurableSpace Θ] [StandardBorelSpace Θ]`             |
| 随机变量 `θ : Ω → Θ`        | `(θ : Ω → Θ)`，`Measurable θ`                            |
| 后验核 `S_t : Ω → Δ(Θ)`     | `ProbabilityTheory.condDistrib` / `Kernel`（见 Existence）|
| 检验函数 `φ : Θ → ℝ`（有界 Borel） | `(φ : Θ → ℝ)`，`Measurable φ` + 有界                |
| `E[φ(θ) | F_t]`             | `P[(φ ∘ θ) | ℱ t]`（`MeasureTheory.condExp` 记号）       |

各部分对应文件：
* `Existence.lean`   — 后验核存在性 + 核性质 (eq:kernel-property)
* `Sufficiency.lean` — Part (i) 充分统计量
* `DoobDynkin.lean`  — Part (ii) `S_t = f_t(Z_t)`
* `Martingale.lean`  — Part (iii) 鞅性质  ← 已被 Lean 背书（无 sorry）
-/

open MeasureTheory

namespace Posterior

end Posterior
