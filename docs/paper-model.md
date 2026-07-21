# 论文模型设定（形式化的"论文源"）

> 本文件逐字保存论文中与形式化相关的**原文段落**，作为 Lean 建模的源头依据，
> 与 [`../CORRESPONDENCE.md`](../CORRESPONDENCE.md)（命题级并排比对）配套。
> ⚠️ 下面代码块内是**论文原文（含论文自定义 LaTeX 宏，如 `\T`=𝕋、`\F`=ℱ、`\P`=ℙ）**，未经改动；
> 我的批注一律在代码块**之外**，两者不混。

---

## 1. Environment（原文）

```latex
\paragraph{Environment.} Time is discrete, with dates $t\in\T:=\{0,1,2,\dots\}$.
There is a seller (designer) and a set of potential buyers for a resource. The
payoff-relevant uncertainty is defined on a Borel probability space
$(\Omega,\F,\mathbb P)$ together with the primitive state $\theta:\Omega\to\Theta$
where $\Theta$ is a compact Polish space. The set $\Delta(\Theta)$ denotes the set
of probability measures on $\Theta$, equipped with the weak topology. At each date
\(t\), public histories are represented by a public state $Z_t:\Omega\to E_t$ where
\(E_t\) is a Polish space and $\F_t=\sigma(Z_t)$ is an increasing filtration of
public-history $\sigma$-algebras with $\F_0$ trivial. A date-\(t\) continuation
mechanism rule is an \(\F_t\)-measurable map $\Gamma_t:\Omega\to\mathcal H_t$ where
\(\mathcal H_t\) is a Polish space of continuation mechanisms.\footnote{For example,
$\Gamma_t$ may specify a posted price, a menu, an auction, or a timing lottery. A
continuation mechanism $\Gamma_t$ is $\F_t$-measurable if its realization depends
only on the public history $\F_t$.}
```

### → Lean 建模对照（我的批注）

| 论文原文 | Lean 建模 | 已用于 |
|---|---|---|
| $t\in\T:=\{0,1,2,\dots\}$ | `ι = ℕ`（现用一般 `[Preorder ι]`，ℕ 是特例） | 各定理 |
| Borel 概率空间 $(\Omega,\F,\mathbb P)$ | `[MeasurableSpace Ω] (P) [IsProbabilityMeasure P]` | Martingale |
| $\theta:\Omega\to\Theta$，Θ 紧 Polish | `(θ : Ω → Θ)`；Θ: `[TopologicalSpace][PolishSpace][CompactSpace][BorelSpace]` | 全部 |
| $\Delta(\Theta)$ = Θ 上概率测度 + 弱拓扑 | `MeasureTheory.ProbabilityMeasure Θ` | DoobDynkin |
| $Z_t:\Omega\to E_t$，$E_t$ Polish | `(Z : Ω → E)`，`[MeasurableSpace E]`（Polish 足够） | DoobDynkin |
| $\F_t=\sigma(Z_t)$ 递增滤子，$\F_0$ trivial | `(ℱ : Filtration ι m)`；σ(Z) 用 `MeasurableSpace.comap Z` | Martingale/DoobDynkin |
| $\Gamma_t:\Omega\to\mathcal H_t$（continuation mechanism） | 尚未涉及（后续 lemma 用到再建模） | — |

---

## 2. Signal and experiment（原文）

```latex
\paragraph{Signal and experiment.} We assume that the date-0 public experiment is
freely designable within the class of finite public signals. Hence every finite
Bayes-plausible distribution over posteriors can be induced by some admissible
public experiment. Conversely, by the posterior martingale (see
\cref{lem:posterior-martingale}), every public experiment induces a Bayes-plausible
posterior distribution.
```

### → 批注

- 这段的"Conversely..."方向**直接引用 `lem:posterior-martingale`**（即我们正在形式化的 Lemma 1）：
  "every public experiment induces a Bayes-plausible posterior distribution" 正是 Part (iii)
  鞅性质（后验过程是鞅 ⇒ 期望守恒 ⇒ Bayes-plausible）的经济学表述。
- "finite Bayes-plausible distribution over posteriors" 等概念，等后续 lemma 涉及时再落 Lean。

---

## 维护约定
- 后续每上传一段论文原文（定义、假设、引理陈述），就**原样追加**到这里，再在
  `CORRESPONDENCE.md` 做命题级并排比对。原文与批注始终分开。
