# Lemma 1 (Posterior process)：论文 ↔ Lean 导航

> 每个 Lean 声明都是**链接**——点进去即看该声明的陈述 + 证明。
> ✅ 已证（`#print axioms` 无 `sorryAx`）　🔵 已陈述待证　⚪ 未陈述。
> **命题与证明的逐字原文见 [docs/paper-lemma1.md](docs/paper-lemma1.md)**（唯一权威来源）；背景设定见 [docs/paper-model.md](docs/paper-model.md)。

## 命题

*（以下为论文原文，逐字未改；完整命题 + 证明见 [docs/paper-lemma1.md](docs/paper-lemma1.md)）*
> For each $t\in\mathbb T$, there exists an $\mathcal F_t$-measurable posterior kernel $S_t:\Omega\to\Delta(\Theta)$ such that, for every bounded Borel function $\varphi:\Theta\to\mathbb R$,
> $$\int_\Theta \varphi(\theta')\,S_t(\omega)(d\theta') = \mathbb E[\varphi(\theta)\mid\mathcal F_t](\omega)\qquad\text{a.s.}$$
> In particular:
> **(i)** $S_t$ is a sufficient statistic for $\theta$ given $\mathcal F_t$: conditioning on $S_t$ and conditioning on $\mathcal F_t$ yield the same conditional distribution of $\theta$.
> **(ii)** Since $\mathcal F_t = \sigma(Z_t)$, the Doob–Dynkin lemma implies that $S_t = f_t(Z_t)$ for some Borel measurable function $f_t$; that is, the public history $Z_t$ induces the posterior $S_t$.
> **(iii)** $\{S_t\}_{t\in\mathbb T}$ is a bounded $(\mathcal F_t)$-martingale.

| 论文 | Lean（点击看证明） | 状态 |
|---|---|---|
| 存在核 + 核性质 | [`kernel_exists`](MyProofs/PosteriorProcess/Existence.lean) | 🔵 |
| (ii) $S_t=f_t(Z_t)$ | [`factorization_posterior`](MyProofs/PosteriorProcess/DoobDynkin.lean) | 🔵 |
| (iii) $\{S_t\}$ 是鞅 | [`testfun_martingale`](MyProofs/PosteriorProcess/Martingale.lean) | ✅ |

## 证明（论文每一步 → Lean）

*下表"论文这一步"是**导航标签**（非逐字原文）；每步的论文原文逐字见 [docs/paper-lemma1.md](docs/paper-lemma1.md)。*

| 论文这一步 | 用到 Mathlib | Lean（点击看证明） | 状态 |
|---|---|---|---|
| 存在性：正则条件分布 (Kallenberg 6.3) | `condDistrib` | [`kernel_exists`](MyProofs/PosteriorProcess/Existence.lean) | 🔵 |
| (i) 充分性：泛函单调类定理 | — | [`Sufficiency.lean`](MyProofs/PosteriorProcess/Sufficiency.lean) | ⚪ |
| (ii) Doob–Dynkin | `exists_eq_measurable_comp` | [`factorization`](MyProofs/PosteriorProcess/DoobDynkin.lean) | ✅ |
| (ii) Δ(Θ) 标准 Borel（库缺口） | — | [`deltaTheta_standardBorel`](MyProofs/PosteriorProcess/DoobDynkin.lean) | 🔵 |
| (iii) 鞅：塔性质 | `martingale_condExp` | [`testfun_martingale`](MyProofs/PosteriorProcess/Martingale.lean) | ✅ |

## ⚠️ 两处须知

- **建模选择（须认可）**：论文"$\{S_t\}$ 是测度值鞅"编码为"对每个 $\varphi$，实值 $t\mapsto\int\varphi\,dS_t$ 是鞅"（即论文正文给的严格定义）。
- **审查发现**：论文 (i) 脚注"有界 Borel = 连续函数逐点极限"**不成立**（Baire class；$\mathbf 1_{\mathbb Q}$ 反例），应删除；正文单调类论证正确。

## 读者怎么验证

```bash
lake build                                         # 无 error = Lean 内核验证通过
lake env lean MyProofs/PosteriorProcess/Audit.lean # 看 #print axioms，无 sorryAx = 真证完
```
