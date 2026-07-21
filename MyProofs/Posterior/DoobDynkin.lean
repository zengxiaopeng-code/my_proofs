import Mathlib

/-!
# Part (ii)：Doob–Dynkin 因子分解  `S_t = f_t(Z_t)`

论文 Lemma "Posterior process" 第 (ii) 部分：
因为 `F_t = σ(Z_t)`，且 `S_t` 是 `σ(Z_t)`-可测、取值于标准 Borel 空间 `Δ(Θ)`，
Doob–Dynkin 引理给出 Borel 可测的 `f_t` 使 `S_t = f_t(Z_t)` a.s.

Mathlib 里这是"关于 `comap` 可测 ⇒ 可因子分解"的一般事实（陪域需标准 Borel）。
-/

open MeasureTheory

namespace Posterior

variable {Ω : Type*} {m : MeasurableSpace Ω}
variable {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]

/-- **Doob–Dynkin 因子分解**。若后验核 `S` 关于 `σ(Z)` 可测
（`Z : Ω → E` 是公开历史），则存在可测的 `f`，使 `S = f ∘ Z`。 -/
theorem posterior_factorization {E : Type*} [MeasurableSpace E]
    (Z : Ω → E) (S : Ω → Measure Θ)
    (hS : @Measurable Ω (Measure Θ) (MeasurableSpace.comap Z inferInstance) inferInstance S) :
    ∃ f : E → Measure Θ, Measurable f ∧ S = f ∘ Z := by
  sorry

end Posterior
