import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Lemma 1 (Posterior process) · 存在性 + 核性质 (eq:kernel-property)

## 论文原文
Lemma 1 的命题与证明（含存在性部分）的**逐字原文见 `docs/paper-lemma1.md`**（唯一权威来源）。

## Lean 陈述 ↔ 论文
| 论文                              | Lean                                            |
|-----------------------------------|-------------------------------------------------|
| 后验核 $S_t:\Omega\to\Delta(\Theta)$ | `S : Ω → Measure Θ`，`∀ ω, IsProbabilityMeasure (S ω)` |
| (a) $\mathcal F_t$-可测            | `Measurable[ℱ t] S`                             |
| (b)/eq:kernel-property            | `(fun ω => ∫ x, φ x ∂(S ω)) =ᵐ[P] P[(φ ∘ θ) | ℱ t]` |

数学依据：$\Theta$ 紧 Polish ⇒ 标准 Borel ⇒ 正则条件分布存在（Kallenberg 2002, Thm 6.3）。
Mathlib 对应 `ProbabilityTheory.condDistrib` / 测度 disintegration。**证明待填 (`sorry`)。**
-/

open MeasureTheory

namespace PosteriorProcess

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Preorder ι] (ℱ : Filtration ι m)
variable {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ] (θ : Ω → Θ)

/-- **Lemma 1, 存在性 + 核性质**。对每个时间 `t`，存在 `ℱ t`-可测的后验核 `S`，
满足对每个有界可测 `φ`，`ω ↦ ∫ φ dS(ω)` 与 `E[φ(θ)|ℱ t]` a.s. 相等。 -/
theorem kernel_exists (hθ : Measurable θ) (t : ι) :
    ∃ S : Ω → Measure Θ,
      (∀ ω, IsProbabilityMeasure (S ω)) ∧
      Measurable[ℱ t] S ∧
      ∀ φ : Θ → ℝ, Measurable φ → (∃ C, ∀ x, |φ x| ≤ C) →
        (fun ω => ∫ x, φ x ∂(S ω)) =ᵐ[P] P[(φ ∘ θ) | ℱ t] := by
  sorry

end PosteriorProcess
