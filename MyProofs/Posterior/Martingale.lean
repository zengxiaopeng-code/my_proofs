import Mathlib

/-!
# Part (iii)：后验过程的鞅性质

论文 Lemma "Posterior process" 的第 (iii) 部分。

论文把 `{S_t}` 说成一个"测度值鞅"，其**严格内容**（论文正文给的）是：
对每个有界 Borel 检验函数 `φ`，实值过程
`t ↦ ∫ φ dS_t = E[φ(θ) | F_t]` 是一个 `(F_t)`-鞅。

关键观察：**这在 Mathlib 里几乎是现成的**。`E[φ(θ) | F_t]` 就是条件期望过程
`fun t => P[(φ ∘ θ) | ℱ t]`，而"条件期望过程是鞅"正是
`MeasureTheory.martingale_condExp`（塔性质的直接推论）。
-/

open MeasureTheory

namespace Posterior

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Preorder ι] (ℱ : Filtration ι m)
variable {Θ : Type*} [MeasurableSpace Θ] (θ : Ω → Θ)

-- 概率测度是有限测度，故滤子自动是 σ-有限的（`martingale_condExp` 所需）。
example : SigmaFiniteFiltration P ℱ := inferInstance

/-- **Part (iii)（对固定检验函数 `φ`）**：
实值后验过程 `t ↦ E[φ(θ) | ℱ_t]` 是一个 `ℱ`-鞅。

注：论文里 `φ` 取有界 Borel；对**鞅性质本身**其实不需要有界性
（条件期望过程对任何函数都是鞅），有界性是为了保证
`∫ φ dS_t` 有限，这里作为忠实于论文的假设保留但不使用。 -/
theorem posterior_testfun_martingale
    (φ : Θ → ℝ) (_hφ : Measurable φ) (_hφb : ∃ C, ∀ x, |φ x| ≤ C) :
    Martingale (fun t => P[(φ ∘ θ) | ℱ t]) ℱ P :=
  martingale_condExp (φ ∘ θ) ℱ P

end Posterior
