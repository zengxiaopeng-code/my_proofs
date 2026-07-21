import Mathlib

/-!
# 后验核的存在性 + 核性质 (eq:kernel-property)

论文 Lemma "Posterior process" 的存在性部分：
存在 `F_t`-可测的后验核 `S_t : Ω → Δ(Θ)`，使得对每个有界 Borel `φ`，
  `∫ φ dS_t = E[φ(θ) | F_t]`  a.s.  ……(eq:kernel-property)

数学依据：`Θ` 紧 Polish ⇒ 标准 Borel ⇒ 正则条件分布存在
（Kallenberg 2002, Thm 6.3）。Mathlib 对应工具是
`ProbabilityTheory.condDistrib` / 测度的 disintegration。

下面把 `Δ(Θ)` 建模为 `Ω → Measure Θ`（点点是概率测度），
`F_t`-可测性写成 `Measurable[ℱ t] S`。
-/

open MeasureTheory

namespace Posterior

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Preorder ι] (ℱ : Filtration ι m)
variable {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ] (θ : Ω → Θ)

/-- **存在性 + 核性质**。对每个时间 `t`，存在 `ℱ t`-可测的后验核 `S`
（点点是 `Θ` 上的概率测度），满足对每个有界可测 `φ`，
`ω ↦ ∫ φ dS(ω)` 与条件期望 `E[φ(θ)|ℱ t]` a.s. 相等。 -/
theorem exists_posterior_kernel (hθ : Measurable θ) (t : ι) :
    ∃ S : Ω → Measure Θ,
      (∀ ω, IsProbabilityMeasure (S ω)) ∧
      Measurable[ℱ t] S ∧
      ∀ φ : Θ → ℝ, Measurable φ → (∃ C, ∀ x, |φ x| ≤ C) →
        (fun ω => ∫ x, φ x ∂(S ω)) =ᵐ[P] P[(φ ∘ θ) | ℱ t] := by
  sorry

end Posterior
