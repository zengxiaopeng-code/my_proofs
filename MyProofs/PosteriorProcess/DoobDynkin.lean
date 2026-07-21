import Mathlib

/-!
# Lemma 1 (Posterior process) · Part (ii)：Doob–Dynkin 因子分解

## 论文原文陈述
> Since $\mathcal F_t=\sigma(Z_t)$ and $S_t$ is $\sigma(Z_t)$-measurable with values in the
> standard Borel space $\Delta(\Theta)$, the Doob–Dynkin lemma yields a Borel measurable
> $f_t:E_t\to\Delta(\Theta)$ such that $S_t(\omega)=f_t(Z_t(\omega))$ a.s.

## Lean 陈述 ↔ 论文
| 论文                          | Lean                                                    |
|-------------------------------|---------------------------------------------------------|
| 公开历史 $Z_t:\Omega\to E_t$  | `Z : Ω → E`                                             |
| $S_t$ 是 $\sigma(Z_t)$-可测   | `Measurable[comap Z] S`（关于 `Z` 生成的 σ-代数可测）    |
| $\Delta(\Theta)$ 标准 Borel   | `Measure Θ`（`Θ` 标准 Borel）                           |
| $\exists f_t,\ S_t=f_t(Z_t)$  | `∃ f : E → Measure Θ, Measurable f ∧ S = f ∘ Z`         |

**证明待填 (`sorry`)。** Mathlib 有 `comap`-可测 ⇒ 因子分解的一般结果（陪域需标准 Borel）。
-/

open MeasureTheory

namespace PosteriorProcess

variable {Ω : Type*} {m : MeasurableSpace Ω}
variable {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]

/-- **Lemma 1, Part (ii)**。若后验核 `S` 关于 `σ(Z)` 可测，则存在可测 `f`，使 `S = f ∘ Z`。 -/
theorem factorization {E : Type*} [MeasurableSpace E]
    (Z : Ω → E) (S : Ω → Measure Θ)
    (hS : @Measurable Ω (Measure Θ) (MeasurableSpace.comap Z inferInstance) inferInstance S) :
    ∃ f : E → Measure Θ, Measurable f ∧ S = f ∘ Z := by
  sorry

end PosteriorProcess
