import Mathlib.Probability.Martingale.Basic

/-!
# Lemma 1 (Posterior process) · Part (iii)：鞅性质

## 论文原文陈述（Part (iii)，逐字）
> Fix $s\le t$ and any bounded Borel $\varphi:\Theta\to\mathbb R$. Then
> $\mathbb E[\int_\Theta\varphi\,dS_t \mid \mathcal F_s]
>   = \mathbb E[\varphi(\theta)\mid\mathcal F_s]
>   = \int_\Theta\varphi\,dS_s$ a.s.
> Since $\varphi$ was arbitrary, $\mathbb E[S_t\mid\mathcal F_s]=S_s$ a.s. in $\Delta(\Theta)$.

## Lean 陈述 ↔ 论文，逐符号对照
| 论文                                   | Lean 里对应的部分                          |
|----------------------------------------|--------------------------------------------|
| 概率空间 $(\Omega,\mathcal F,\mathbb P)$| `Ω`, `m : MeasurableSpace Ω`, `P` (`IsProbabilityMeasure`) |
| 滤子 $(\mathcal F_t)$                   | `ℱ : Filtration ι m`                        |
| 随机变量 $\theta:\Omega\to\Theta$      | `θ : Ω → Θ`                                 |
| "for any bounded Borel $\varphi$"      | `(φ : Θ → ℝ) (_hφ : Measurable φ) (_hφb : 有界)` |
| $\int_\Theta\varphi\,dS_t=\mathbb E[\varphi(\theta)\mid\mathcal F_t]$ (核性质) | `P[(φ ∘ θ) | ℱ t]`（用核性质把 $\int\varphi\,dS_t$ 换成条件期望） |
| "$\{...\}$ is an $(\mathcal F_t)$-martingale" | `Martingale (fun t => P[(φ ∘ θ) | ℱ t]) ℱ P` |

## ⚠️ 建模选择（你需要认可这些才算"忠实"）
1. **"测度值鞅 $\mathbb E[S_t\mid\mathcal F_s]=S_s$" 被编码为"对每个 $\varphi$，实值过程
   $t\mapsto\int\varphi\,dS_t$ 是鞅"**。这正是论文正文给出的严格内容（$\Delta(\Theta)$ 不是向量空间，
   条件期望须逐 $\varphi$ 理解）。论文那句"a.s. in $\Delta(\Theta)$"要靠可数测度决定族合并，
   属另一步（见 CORRESPONDENCE.md 与人工审查）。
2. **这里直接用滤子 $\mathcal F_t$，未把它具体化为 $\sigma(Z_t)$**——对鞅性质无影响
   （$\sigma(Z_t)$ 只在 Part (ii) 用到）。
3. **`φ` 的有界性在此不被使用**（条件期望过程对任意可积函数都是鞅）；保留以忠实于论文。
-/

open MeasureTheory

namespace PosteriorProcess

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Preorder ι] (ℱ : Filtration ι m)
variable {Θ : Type*} [MeasurableSpace Θ] (θ : Ω → Θ)

/-- **Lemma 1, Part (iii)（对固定检验函数 `φ`）**：
实值后验过程 `t ↦ ∫ φ dSₜ = E[φ(θ) | ℱ_t]` 是一个 `ℱ`-鞅。 -/
theorem testfun_martingale
    (φ : Θ → ℝ) (_hφ : Measurable φ) (_hφb : ∃ C, ∀ x, |φ x| ≤ C) :
    Martingale (fun t => P[(φ ∘ θ) | ℱ t]) ℱ P :=
  martingale_condExp (φ ∘ θ) ℱ P

end PosteriorProcess
