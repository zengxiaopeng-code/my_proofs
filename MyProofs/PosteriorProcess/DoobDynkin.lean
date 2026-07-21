import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Lemma 1 (Posterior process) · Part (ii)：Doob–Dynkin 因子分解

## 论文原文陈述
> Since $\mathcal F_t=\sigma(Z_t)$ and $S_t$ is $\sigma(Z_t)$-measurable with values in the
> standard Borel space $\Delta(\Theta)$, the Doob–Dynkin lemma yields a Borel measurable
> $f_t:E_t\to\Delta(\Theta)$ such that $S_t(\omega)=f_t(Z_t(\omega))$ a.s.

## 形式化揭示的结构：论文这一句打包了两个独立事实
1. **Doob–Dynkin 本身**（`factorization`）：σ(Z)-可测 + 陪域标准 Borel ⇒ 因子分解。
   Mathlib 有 `Measurable.exists_eq_measurable_comp`。**已证 ✅（无 sorry）**
2. **`Δ(Θ)` 是标准 Borel**（`deltaTheta_standardBorel`）：因 Θ 紧 Polish。
   **Mathlib 缺口**：只给了 `MetrizableSpace (ProbabilityMeasure Θ)`，缺
   `PolishSpace (ProbabilityMeasure Θ)` 和 `BorelSpace (ProbabilityMeasure Θ)`
   两个实例（二者合成才是 StandardBorel）。**待补 🔵（sorry）**

`factorization_posterior` 把两者合起来 = 论文 Δ(Θ) 版本的完整 Part (ii)。
-/

open MeasureTheory

namespace PosteriorProcess

/-- **Part (ii) 的 Doob–Dynkin 内容（抽象版，已证）**。
若 `S : Ω → Δ` 关于 `σ(Z)` 可测（`Z : Ω → E`），且陪域 `Δ` 是**标准 Borel 空间**，
则存在可测 `f : E → Δ` 使 `S = f ∘ Z`。直接由 Mathlib 的 Doob–Dynkin 引理给出。 -/
theorem factorization {Ω E Δ : Type*} [MeasurableSpace E]
    [MeasurableSpace Δ] [StandardBorelSpace Δ] [Nonempty Δ]
    (Z : Ω → E) (S : Ω → Δ)
    (hS : @Measurable Ω Δ (MeasurableSpace.comap Z inferInstance) inferInstance S) :
    ∃ f : E → Δ, Measurable f ∧ S = f ∘ Z :=
  hS.exists_eq_measurable_comp

/-- **库缺口（待补）**：Θ 紧 Polish ⇒ `Δ(Θ) = ProbabilityMeasure Θ` 是标准 Borel。
需要在 Mathlib 现有 `MetrizableSpace (ProbabilityMeasure Θ)` 基础上补出
`PolishSpace` 与 `BorelSpace` 两个实例。这是一个独立的小型基础设施项目
（或可上游贡献给 Mathlib）。 -/
theorem deltaTheta_standardBorel (Θ : Type*) [TopologicalSpace Θ] [PolishSpace Θ]
    [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ] :
    StandardBorelSpace (ProbabilityMeasure Θ) := by
  sorry

/-- **Part (ii) 完整版（Δ(Θ) 版本）**：把抽象 Doob–Dynkin 应用到后验核 `S : Ω → Δ(Θ)`。
除 `deltaTheta_standardBorel` 的缺口外，其余逻辑完整；`Nonempty (Δ Θ)` 作为温和假设保留。 -/
theorem factorization_posterior {Ω E Θ : Type*} [MeasurableSpace E]
    [TopologicalSpace Θ] [PolishSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    [Nonempty (ProbabilityMeasure Θ)]
    (Z : Ω → E) (S : Ω → ProbabilityMeasure Θ)
    (hS : @Measurable Ω (ProbabilityMeasure Θ) (MeasurableSpace.comap Z inferInstance)
      inferInstance S) :
    ∃ f : E → ProbabilityMeasure Θ, Measurable f ∧ S = f ∘ Z :=
  haveI := deltaTheta_standardBorel Θ
  factorization Z S hS

end PosteriorProcess
