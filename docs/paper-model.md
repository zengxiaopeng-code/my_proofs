# 论文模型设定（形式化的"论文源"）

> 本文件**逐字**保存论文 §2（Model）全部 setting 组件的**原文**，作为 Lean 建模的源头依据。
> ⚠️ 代码块内是**论文原文**（含论文自定义宏，如 `\T`=𝕋、`\F`=ℱ、`\P`=ℙ、`\Sel`），
> 由脚本从正稿 `../../paper-source/` 按行区间**精确切片**生成，未经任何翻译/压缩/改写；
> 我的批注一律在代码块**之外**，两者不混。
>
> **判定标签**：`[已对上]` Lean 有忠实对应 · `[缺口]` Lean 中不存在 ·
> `[strengthening]` 论文推导的结论在 Lean 里被当作假设 · `[层级错位]` 有对应但抽象层级与论文不同。

## 覆盖速览（2026-07-23 核对）

| # | 论文 setting 组件 | Lean 现状 |
|---|---|---|
| 1 | Environment | 大部分 `[已对上]`；`Γ_t`/`H_t` `[缺口]` |
| 2 | Signal and experiment | `[已对上]`（经 Lemma 1 鞅性质） |
| 3 | Assumption 1 单发资源 | `[层级错位]`：只编码其推论，非假设本身 |
| 4 | Timeline（τ、日历 𝓜、R(𝓜)） | τ **`[已对上]`**（范围已收紧为 `Option {n // 1 ≤ n}`）；𝓜/R(𝓜) `[缺口]` |
| 5 | Continuation equilibria（𝓑ₜ,𝓔ₜ,πₜ,𝓡ₜ^Γ） | 𝓡ₜ^Γ **`[已对上]`**（作参数，= 论文的抽象边界）；𝓑ₜ/𝓔ₜ/πₜ 保持抽象（论文亦然） |
| 6 | Assumption 2 analytic equilibrium | (iv) **`[已对上]`**（假设在 𝓡ₜ^Γ 上，并推出 U 有界）；(i)–(iii) `[缺口]`（经 `hsel` 假设代理） |
| 7 | **Continuation value Uₜ 的定义式** | **`[已对上]`：`DMC.Paper.U` 即论文的 sup 定义式** |
| 8 | Equilibrium-branch representation（conc_f） | conc_f `[已对上]`；lower bound / R(𝓜) `[缺口]` |
| 9 | Assumption 3 Regularity | `[strengthening]`（一点 usc → 全体 usc，已在 docstring 标注） |
| 10 | State decomposition（Zₜ=(Sₜ,Yₜ)、𝒢 夹逼） | **`[已对上]`**：`AdmissibleRichness` 用 `MeasurableSpace` 的序逐字表达 |
| 11 | Non-posterior value（𝒢-selector、collapse） | collapse **`[已对上]`**（`ValueCollapse`+`valueCollapse_iff`）；𝒢-optimal selector `[缺口]` |
| 12 | Truncation value Vₜ + `eq:stopping-form`（§3.3） | Vₜ/V≥0/有界 **`[已对上]`**（皆由定义推出）；`eq:stopping-form` 仍 **`[strengthening]`**（唯一剩下的假设） |

---

## 1. Environment（§2.1 原文）

```latex
\paragraph{Environment.} Time is discrete, with dates $t\in\T:=\{0,1,2,\dots\}$. There is a seller (designer) and a set of potential buyers for a resource. The payoff-relevant uncertainty is defined on a Borel probability space $(\Omega,\F,\mathbb P)$ together with the primitive state $\theta:\Omega\to\Theta$ where $\Theta$ is a compact Polish space. The set $\Delta(\Theta)$ denotes the set of probability measures on $\Theta$, equipped with the weak topology. At each date \(t\), public histories are represented by a public state $Z_t:\Omega\to E_t$ where \(E_t\) is a Polish space and $\F_t=\sigma(Z_t)$ is an increasing filtration of public-history $\sigma$-algebras with $\F_0$ trivial. A date-\(t\) continuation mechanism rule is an \(\F_t\)-measurable map $\Gamma_t:\Omega\to\mathcal H_t$ where \(\mathcal H_t\) is a Polish space of continuation mechanisms.\footnote{For example, $\Gamma_t$ may specify a posted price, a menu, an auction, or a timing lottery. A continuation mechanism $\Gamma_t$ is $\F_t$-measurable if its realization depends only on the public history $\F_t$.}
```

### → Lean 建模对照（我的批注）

| 论文原文 | Lean 建模 | 判定 |
|---|---|---|
| $t\in\T:=\{0,1,2,\dots\}$ | `ι = ℕ`（现用一般 `[Preorder ι]`，ℕ 是特例） | `[已对上]` |
| Borel 概率空间 $(\Omega,\F,\mathbb P)$ | `[MeasurableSpace Ω] (P) [IsProbabilityMeasure P]` | `[已对上]` |
| $\theta:\Omega\to\Theta$，Θ 紧 Polish | `(θ : Ω → Θ)`；`[TopologicalSpace][PolishSpace][CompactSpace][BorelSpace]` | `[已对上]` |
| $\Delta(\Theta)$ = Θ 上概率测度 + 弱拓扑 | `DMC.Belief Θ = MeasureTheory.ProbabilityMeasure Θ` | `[已对上]` |
| $Z_t:\Omega\to E_t$，$E_t$ Polish | `(Z : Ω → E)`，`[MeasurableSpace E]` | `[已对上]` |
| $\F_t=\sigma(Z_t)$ 递增滤子，$\F_0$ trivial | `(ℱ : Filtration ι m)`；σ(Z) 用 `MeasurableSpace.comap Z` | `[已对上]` |
| **$\Gamma_t:\Omega\to\mathcal H_t$（$\F_t$-可测连续机制规则），$\mathcal H_t$ Polish** | `Model/Primitives.lean` 的参数 `H`/`mH`，机制规则 `Γ : Ω → H t` | **`[已对上]`** |

> `Γ_t`/`H_t` 是论文定义 `Uₜ` 时取 sup 的对象。**2026-07-23 已补**：`Model/Primitives.lean` 把它们作为参数引入，`Uₜ` 因此得以按论文原式定义（第 9 节）。

---

## 2. Signal and experiment（§2.1 原文）

```latex
\paragraph{Signal and experiment.} We assume that the date-0 public experiment is freely designable within the class of finite public signals. Hence every finite Bayes-plausible distribution over posteriors can be induced by some admissible public experiment. Conversely, by the posterior martingale (see \cref{lem:posterior-martingale}), every public experiment induces a Bayes-plausible posterior distribution.
```

### → Lean 建模对照（我的批注）

- "Conversely..." 方向**直接引用 `lem:posterior-martingale`**（我们已全证的 Lemma 1）：
  "every public experiment induces a Bayes-plausible posterior distribution" 正是 Part (iii)
  鞅性质的经济学表述。`[已对上]`
- "finite Bayes-plausible distribution over posteriors" → 用户已在 `Foundations/BeliefSpace.lean`
  用 `mixFinMeasure`/`mixFin`（有限凸组合）落地，并在 `Results/NoGain.concFBelief` 中作为 split 使用。`[已对上]`

---

## 3. Assumption 1（Single-shot resource，原文）

```latex
\begin{assumption}[Single-shot resource]\label{ass:single-shot}
The resource is economically single-shot: it can be allocated at most once. If the resource is assigned to some buyers and transfers are made, then no later date $t'>t$ can generate additional surplus.\footnote{If Assumption \ref{ass:single-shot} does not hold, the problem may degenerate into a simple problem of finding the pointwise optimal continuation mechanism at each date $t$, the intertemporal problem loses the single-shot structure that motivates our analysis.}
\end{assumption}
```

### → Lean 建模对照（我的批注）

- Lean `Model/SingleShot.lean` 的**结构名取自它**，但形式化的是它的**推论**（停时递归，见第 12 项），
  而非假设本身（"至多分配一次；分配后更晚日期不再产生额外剩余"）。
- 文件 docstring 已坦承："formalized through its operative content"。
- 判定 `[层级错位]`：论文的经济学假设 → Lean 里换成了它推出的数学性质。

---

## 4. Timeline（§2.1 原文）

```latex
\paragraph{Timeline.} Let $\tau\in\{1,2,...\}\cup\{\varnothing\}$ denote the date at which the resource is actually allocated. If $\tau=\varnothing$, no sale ever occurs.At each date $t$ and after any public state $Z_t$, the seller chooses, and
commits to, a continuation mechanism $\Gamma_t\in\mathcal H_t$, but cannot
commit to the mechanisms of later dates.\footnote{Formally, $\mathcal H_t$ contains no mechanism that binds later
choices. The calendar accordingly arises date by date. The seller chooses
$\Gamma_2$ only when date $1$ has ended and $Z_2$ has realized, $\Gamma_3$
only when date $2$ has ended, and so on. In $R(\mathcal M)$, the calendar
is the realized record of the game, not a plan fixed in advance.} is a recording by time: $\mathcal M=\{(Z_0,\Gamma_0), (Z_1,\Gamma_1),\dots\}$. Let \(R(\mathcal M)\) denote the supremum of the seller's ex-ante payoff over all sequentially rational Bayesian equilibria of the dynamic game associated with the calendar $\mathcal M$.
```

### → Lean 建模对照（我的批注）

| 论文原文 | Lean 建模 | 判定 |
|---|---|---|
| $\tau\in\{1,2,...\}\cup\{\varnothing\}$ | `DMC.AllocDate := Option {n : ℕ // 1 ≤ n}`（`none`=∅） | **`[已对上]`**（`allocDate_date_ge_one` 机检范围） |
| 日历 $\mathcal M=\{(Z_t,\Gamma_t)\}$ | 无 | `[缺口]` |
| $R(\mathcal M)$ = 卖方 ex-ante payoff 上确界 | 无 | `[缺口]` |

> **两处具体问题**：(a) 论文 τ 从 **1** 起，而 `Option ℕ` 允许 `some 0`——多出一个**无论文对应**的值，
> 现有忠实性检查 `allocDate_never_ne_date`/`_date_injective` 抓不到；
> (b) `AllocDate` **全项目未被任何定义/定理使用**（只有 `Meta/ModelFaithfulness.lean` 的检查引用它），
> 目前是纯装饰。修法：改用 `Option {n : ℕ // 1 ≤ n}`，或在真正用到 τ 时再引入。
>
> 图 `fig:model-timeline`（正稿 232–300 行，TikZ）是上述时间线的图示，无需形式化。

---

## 5. §2.2 导言（原文）

```latex
\subsection{Seller's optimal ex-ante value}\label{subsec:reduced-form}

To characterize \(R(\mathcal M)\), we identify the seller's payoff at each date of the game. That payoff is the value the seller can attain in the continuation problem itself, determined by its equilibria rather than defined recursively from later dates. The definitions that follow only make this object precise.
```

### → Lean 建模对照（我的批注）

- 关键句："That payoff is the value the seller can attain in the continuation problem itself,
  **determined by its equilibria rather than defined recursively from later dates**."
- 即 `Uₜ` **不是** Bellman 递归值，而是由该日连续博弈的均衡集合直接决定 —— 这正是它必须被
  **定义为一个 sup**（第 7 项）而非当作抽象数据的原因。

---

## 6. Continuation equilibria（§2.2 原文）

```latex
\paragraph{Continuation equilibria.} Fix a date \(t\), a public state \(z\in E_t\), and a continuation mechanism \(h\in\mathcal H_t\). Let $\mathcal B_t(z,h)$ denote the set of strategy--belief profiles of the continuation game that starts at date \(t\) after public state \(z\), when the chosen continuation mechanism is \(h\). Let $\mathcal E_t(z,h)\subseteq \mathcal B_t(z,h)$ denote the subset of continuation profiles that are sequentially rational Bayesian equilibria of this date-\(t\) continuation game. For each \(b\in\mathcal E_t(z,h)\), let
\[
\pi_t(\omega,z,h,b)\in\mathbb R
\]
be the seller's state-contingent payoff function under \(b\). For a continuation mechanism rule \(\Gamma_t\), the induced random payoff correspondence is
\[
\mathcal R_t^{\Gamma_t}(\omega)
:=
\bigl\{
\pi_t(\omega,Z_t(\omega),\Gamma_t(\omega),b),b \in \mathcal E_t(Z_t(\omega),\Gamma_t(\omega))
\bigr\}.
\]
```

### → Lean 建模对照（我的批注）

| 论文对象 | Lean 现状 | 判定 |
|---|---|---|
| $\mathcal B_t(z,h)$ 策略-信念 profile 集 | 0 处 | `[缺口]` |
| $\mathcal E_t(z,h)$ 序贯理性贝叶斯均衡子集 | 0 处 | `[缺口]` |
| $\pi_t(\omega,z,h,b)$ 卖方状态依存收益 | 0 处 | `[缺口]` |
| $\mathcal R_t^{\Gamma_t}(\omega)$ 诱导随机收益对应 | 0 处 | `[缺口]` |

> **这是论文自己的抽象边界**：论文**不构造** $\mathcal E_t$（不形式化序贯理性 PBE），
> 只用 Assumption 2 约束它，此后一切都建在 $\mathcal R_t^{\Gamma_t}$ 之上。
> 因此 Lean 的忠实做法**不是**从零形式化博弈论，而是**把抽象边界放在与论文相同的位置**：
> 以 $\mathcal R_t^{\Gamma_t}$（及 Assumption 2）为参数，其上的 $U_t,V_t$ 全部**定义**出来。

---

## 7. Assumption 2（Analytic equilibrium，原文）

```latex
\begin{assumption}[Analytic equilibrium]
\label{ass:analytic-equilibrium}
For every date $t\in\mathbb T$, every continuation mechanism $h\in\mathcal H_t$, and every public state $z\in E_t$:
\begin{enumerate}[label=\textup{(\roman*)}]
    \item\label{item:nonempty}
    The continuation equilibrium profile set $\mathcal E_t(z,h)$ is nonempty.
    \item\label{item:analytic-graph}
    The graph of the equilibrium correspondence $\operatorname{Gr}(\mathcal E_t)
    :=
    \bigl\{(z,h,b)\in E_t\times\mathcal H_t\times\mathcal B_t :
    b\in\mathcal E_t(z,h)\bigr\},$
    is an analytic subset of $E_t\times\mathcal H_t\times\mathcal B_t$.
    \item\label{item:meas-payoff}
    The payoff function
    $\pi_t$ is jointly Borel measurable.
    \item\label{item:bounded}
    The payoff correspondence $\mathcal R_t^{\Gamma_t}$ is
    uniformly bounded above.\footnote{Under \ref{item:nonempty}--\ref{item:meas-payoff}, the payoff correspondence $\mathcal R_t^{\Gamma_t}$ is automatically nonempty-valued and has analytic graph, so these properties need not be assumed separately. Condition~\ref{item:bounded} is the only independent content in \textup{(iv)}: it is an economic requirement that equilibrium values are finite.}
\end{enumerate}
\end{assumption}
```

### → Lean 建模对照（我的批注）

| 论文条款 | Lean 现状 | 判定 |
|---|---|---|
| (i) $\mathcal E_t(z,h)$ 非空 | 无 | `[缺口]` |
| (ii) $\operatorname{Gr}(\mathcal E_t)$ 解析 | 无 | `[缺口]` |
| (iii) $\pi_t$ 联合 Borel 可测 | 无 | `[缺口]` |
| (iv) $\mathcal R_t^{\Gamma_t}$ **一致上界** | `DateValues.U_bddAbove` | `[层级错位]` |

> (iv) 是论文自陈的"唯一独立内容……均衡值有限"。但论文把它假设在**收益对应 $\mathcal R_t^{\Gamma_t}$** 上，
> Lean 却直接假设在 **$U$** 上——差一层。若按第 6 项把边界下移，`U_bddAbove` 应由 (iv) **推出**。
> (ii)(iii) 是 `lem:selection-exists`/`lem:measurable-lifting` 的前提，将来做选择引理时才需要。

---

## 8. Remark（Assumption 2(ii) 的充分情形，原文）

```latex
\begin{remark}
    Condition~\ref{item:analytic-graph} is satisfied in two leading cases that cover most applications. First, if $\mathcal B_t(z,h)$ is a compact metric space and the best-reply correspondence is upper hemicontinuous with nonempty compact values, then $\operatorname{Gr}(\mathcal E_t)$ is closed, hence Borel, hence analytic. Second, if the strategy space is finite (e.g.\ finite auctions or
    finite menus), $\mathcal E_t(z,h)$ is a finite union of points for each $(z,h)$, so its graph is a countable union of Borel sets and thus analytic. In both cases \ref{item:analytic-graph} follows without
    additional argument.
\end{remark}
```

### → Lean 建模对照（我的批注）

- 说明 (ii) 在两类主流情形自动成立（紧度量 + 上半连续最优反应；或有限策略空间）。
- 暂无 Lean 对应；若将来把 (ii) 落地，这段给出可用的充分条件。`[缺口]`

---

## 9. Continuation value（§2.2 原文，**Uₜ 的定义**）

```latex
\paragraph{Continuation value.} For a continuation mechanism $\Gamma$, let
$\Sel(\mathcal R_t^{\Gamma_t})$ denote the set of universally measurable payoff selections of $\mathcal R_t^{\Gamma_t}$ (see \cref{lem:selection-exists}). Public history $Z_t$ induces a posterior $S_t:\Omega\to\Delta(\Theta)$ which summarizes all public learning about the primitive state $\theta$ (see \cref{lem:posterior-martingale}). Let $\mathbb P_t^\mu(\cdot)$ be a version of $\mathbb P(\cdot\mid S_t(\omega)=\mu)$, which denotes the conditional law of the state $\omega$ given the public posterior $\mu$. \emph{Conditioning on} the public continuation state \(Z_t\), the date-\(t\) \emph{continuation value} is\footnote{the definition is expectation-based: the object of interest is the seller's date-$t$ conditional expected equilibrium payoff at a given posterior, not a pathwise conditional essential supremum over value. Whenever a continuation value $U_t^{\mathcal G}$ admits multiple measurable versions, we fix once and for all a bounded upper semianalytic version and continue to denote it by the same symbol.}
\[
U_t^{\sigma(Z_t)}(\mu)
:=
\sup\Bigg\{
\int_\Omega \rho(\omega)\,\mathbb P_t^\mu(d\omega):
\Gamma \text{ is } \sigma(Z_t)\text{-measurable},
\
\rho\in \Sel\big(\mathcal R_t^{\Gamma_t}\big)
\Bigg\},
\qquad
\mu\in\Delta(\Theta).
\]
\begin{remark}[Continuation value]\label{Continuation value}
The continuation value \(U_t^{\sigma(Z_t)}\) is the seller's maximal conditional expected equilibrium payoff in the date-\(t\) continuation mechanism problem, given the public state \({Z_t}\) on which the continuation rule may condition. It is not a Bellman continuation value, but rather the equilibrium payoff from the continuation problem starting at date \(t\).
\end{remark}
```

### → Lean 建模对照（我的批注）

> **这是"definition 没和原文对上"最核心的一处。**

| 论文 | Lean 现状 | 判定 |
|---|---|---|
| $U_t^{\sigma(Z_t)}(\mu):=\sup\{\int_\Omega\rho\,d\mathbb P_t^\mu:\Gamma\ \sigma(Z_t)\text{-可测},\ \rho\in\Sel(\mathcal R_t^{\Gamma_t})\}$ | `DateValues.U : ℕ → Δ(Θ) → ℝ`，**无内涵的 opaque 字段** | **`[层级错位]`** |
| $\Sel(\mathcal R_t^{\Gamma_t})$ 泛可测收益选择 | 0 处 | `[缺口]` |
| $\mathbb P_t^\mu=\mathbb P(\cdot\mid S_t=\mu)$ 的一个版本 | 0 处（Lemma 1 的 `condDistrib` 可提供） | `[缺口]` |

> 论文**定义** `Uₜ`；Lean **公理化** `Uₜ`。于是 blueprint 里标着"paper §2.2"的 Definition 节点，
> 实际上不是论文的定义，而是形式化自造的接口。**修法**：以 $\mathcal R_t^{\Gamma_t}$、$\mathbb P_t^\mu$
> 为参数，把上式作为 Lean `def` 写出，`DateValues` 改为由它**构造**出的实例。

---

## 10. Equilibrium-branch representation（§2.2 原文，含 conc_f 定义）

```latex
\paragraph{Equilibrium-branch representation.} Let $\pi=\sum_{k=1}^K \alpha_k\delta_{\mu_k}$ be a finite-support posterior distribution induced by a public experiment,\footnote{Here \(\pi\) denotes a probability distribution over posterior beliefs; this notation is distinct from the payoff function \(\pi_t\).} where \(\alpha_k\) is the probability that posterior \(\mu_k\) is realized. For each \(k\), choose \(t_k\in\mathbb T\) and an \(\varepsilon\)-optimal selector \((\Gamma_k,\rho_k)\) for
\(U_{t_k}^{\mathcal F_{t_k}}(\mu_k)\), that is,
\[
\int_\Omega \rho_k(\omega)\,
\mathbb P_{t_k}^{\mu_k}(d\omega)
\ge
U_{t_k}^{\mathcal F_{t_k}}(\mu_k)-\varepsilon .
\]


\noindent\emph{Lower bound.} Under \cref{ass:analytic-equilibrium}, every payoff selection admits a universally measurable equilibrium lifting (see \cref{lem:measurable-lifting}). So the sequential pasting argument (see \cref{lem:sequential-pasting}) applied, these continuation selectors can be assigned after the posterior realizations of the date-0 public experiment to form a sequentially rational Bayesian equilibrium of the resulting mechanism calendar. The seller's ex-ante payoff in this equilibrium is at least
\[
R(\mathcal M) \geq \sum_{k=1}^K
\alpha_k U_{t_k}^{\mathcal F_{t_k}}(\mu_k)
-\varepsilon .
\]
This inequality states that the dynamic mechanism calendar can implement, up to \(\varepsilon\), the probability-weighted average of the posterior-contingent date-\(t_k\) continuation values generated after the public experiment.\footnote{The split used in the representation is not a recursive Bellman split. It is a split over complete continuation-equilibrium branches. For each posterior realization, the selected object is a full sequentially rational continuation profile of the game starting from the corresponding public continuation state.}

\bigskip
\noindent\emph{Upper bound.} For any function \(q:\Delta(\Theta)\to\mathbb R\), define its finite concavification by
\[
(\operatorname{conc}_f q)(\mu)
:=
\sup_{\pi\in\mathcal P_f(\Delta(\Theta)):
\int_{\Delta(\Theta)}\nu\,\pi(d\nu)=\mu}
\int_{\Delta(\Theta)}q(\nu)\,\pi(d\nu).
\]
```

### → Lean 建模对照（我的批注）

| 论文对象 | Lean 现状 | 判定 |
|---|---|---|
| $(\operatorname{conc}_f q)(\mu):=\sup_{\pi:\int\nu\,\pi(d\nu)=\mu}\int q\,d\pi$ | `Foundations/Concavification.concF` + `Results/NoGain.concFBelief`（并已证二者透明性对应 `concF_emb_eq_concFBelief`） | `[已对上]` |
| ε-最优 selector $(\Gamma_k,\rho_k)$ | 0 处 | `[缺口]` |
| lower bound $R(\mathcal M)\ge\sum\alpha_k U_{t_k}(\mu_k)-\varepsilon$ | 无 | `[缺口]`（=博弈桥，旁支） |

> conc_f 这条主链已经形式化得很扎实；缺的是把它和 `R(𝓜)` 连起来的博弈论桥（`prop:value-representation`）。

---

## 11. Assumption 3（Regularity，原文）

```latex
\begin{assumption}[Regularity]\label{ass:regularity}
The finite concavification
$\operatorname{conc}_f\!\big[\sup_{t\in\mathbb T}U_t^{\mathcal G_t}\big]$
is upper semicontinuous at the prior $S_0$.
\end{assumption}
\noindent Under \cref{ass:regularity},\footnote{\cref{ass:regularity} is the exact property used in the proofs of \cref{lem:upper-bound,lem:concf-conc}: the concavified envelope must not jump upward at $S_0$. It is implied by standard game-theoretic primitives. See \cref{app:regularity-sufficient} for a layered statement of primitive sufficient conditions.} the seller's ex-ante equilibrium payoff is bounded above by the finite concave envelope of the date-wise upper envelope of full-history continuation values (see \cref{lem:upper-bound}); the envelope is evaluated at the prior belief \(\mu_0\), where \(S_0(\omega)\equiv \mu_0\) for trivial \(\mathcal F_0\).
```

### → Lean 建模对照（我的批注）

- Lean 对应：`Results/NoGain.nogain_belief` 的 `husc` 假设（`concF` 在 K 上 usc）。
- **判定 `[strengthening]`**：论文只要求"在先验 $S_0$ **一点** usc"，Lean 用的是"在 K **全体** usc"——
  更强的假设 ⇒ 更弱的定理。已在定理 docstring 标注，**尚未接进 blueprint 标签**（待办）。
- 论文脚注指出该假设由标准博弈论原语蕴含（正稿 `app:regularity-sufficient` / R1–R3）。

---

## 12. Proposition（Equilibrium-branch representation，原文）

```latex
Combining this upper bound with the lower bound gives the belief-space representation of the seller's optimal ex-ante payoff:

\begin{proposition}[Equilibrium-branch representation]
\label{prop:value-representation}
Suppose \cref{ass:single-shot,ass:analytic-equilibrium,ass:regularity} holds, the seller's ex-ante payoff satisfies
\[
\sup_{\mathcal M} R(\mathcal M)
=
\Big(\operatorname{conc}_f
\big[\sup_{t\in\mathbb T} U_t^{\sigma(Z_t)}\big]\Big)(S_0).
\]
\end{proposition}

Two features make this representation available where it usually is not. The resource is allocated at most once, so the seller's payoff is realized at a single date and no surplus is double-counted across dates (\cref{ass:single-shot}). The posterior is a martingale, so beliefs are linked across dates only through Bayes plausibility, which is the only restriction on the posterior distributions a date-0 experiment can induce. The date-wise inputs \(U_t^{\sigma(Z_t)}\) are continuation equilibrium values rather than Bellman continuation values, so the branchwise selectors are pasted into a single sequentially rational equilibrium of the induced calendar (\cref{lem:measurable-lifting,lem:sequential-pasting}), with no separate consistency condition to verify.
```

### → Lean 建模对照（我的批注）

- 这是 §2 的收官命题：$\sup_{\mathcal M}R(\mathcal M)=(\operatorname{conc}_f[\sup_t U_t^{\sigma(Z_t)}])(S_0)$。
- Lean 现状：**未落地**。用户已改走"绕过博弈黑箱"的路线——把 no-gain 取为 value-representation
  **之后**的等价式（`Results/NoGain.nogain_belief_conc`），故主定理不依赖本命题。`[缺口]`（旁支，不挡主链）

---

## 13. State decomposition（§2.3 原文）

```latex
\subsection{The value beyond posterior }\label{subsec:representation.}
\paragraph{State decomposition.} As mentioned above, the posterior $S_t$ is sufficient for inference about $\theta$. However, two realized public histories may induce the same posterior $S_t$ and still lead to different date-$t$ continuation problems.\footnote{Examples include eligibility states, promised utilities, inventories, reputations, or other public variables that do not further change beliefs about \(\theta\), but may affect the continuation problem.} To capture this distinction, we impose the following decomposition of the public state. Without loss of generality, we rewrite the date-$t$ public state as
\[
Z_t:=(S_t,Y_t),
\]
where $S_t$ is the posterior and $Y_t$ denotes the non-posterior public continuation state.\footnote{Non-posterior public state $Y_t$ does not change beliefs about $\theta$ beyond what is already encoded in $S_t$, but it may remain payoff-relevant for the induced date-$t$ continuation mechanism problem. We provided a specific definition (\cref{eq:Non-posterior}) in \cref{sec:screening-application}.} Posterior $S_t$ summarizes public learning about the primitive state, whereas $(S_t,Y_t)$ is the full public state relevant for the date-$t$ mechanism problem. The state decomposition allows us to compare different public states at date $t$. Let $\mathcal G$ be a public state satisfying
\[
\sigma(S_t)\subseteq \mathcal G\subseteq \sigma(S_t,Y_t).
\]
That is, $\mathcal G$ summarizes the public states on which the seller is allowed to condition the date-$t$ continuation mechanism.
```

### → Lean 建模对照（我的批注）

| 论文对象 | Lean 现状 | 判定 |
|---|---|---|
| $Z_t:=(S_t,Y_t)$，$Y_t$ 非后验公共状态 | 0 处 | `[缺口]` |
| $\sigma(S_t)\subseteq\mathcal G\subseteq\sigma(S_t,Y_t)$ | 0 处 | `[缺口]` |

> **这是 collapse 目前无法陈述的根源。** Lean 现在用"两个互不相关的 `DateValues` 实例 +
> 假设 `U_post ≤ U_rich`"来模拟"条件丰富度"，而论文用的是**一条 σ-代数夹逼**。
> Lean 完全能逐字表达：`MeasurableSpace` 本身有序，写
> `comap S ≤ 𝒢 ∧ 𝒢 ≤ comap (fun ω => (S ω, Y ω))` 即可。
> 一旦 $\mathcal G$ 真实存在，论文那句"richer 公共状态扩大 $U_t$"就从**假设**变成 sup 单调性的**定理**。

---

## 14. Non-posterior value（§2.3 原文，含 collapse 定义）

```latex
\paragraph{Non-posterior value.} Fix a date \(t\), a posterior \(\mu\in\Delta(\Theta)\), and a public state \(\mathcal G\), a \(\mathcal G\)-admissible selector at \(\mu\) is a pair \((\Gamma_t,\rho)\) such that \(\Gamma_t\) is \(\mathcal G\)-measurable and $\rho\in \Sel(\mathcal R_t^{\Gamma_t})$. A selector \((\Gamma_t,\rho)\) is \(\mathcal G\)-\emph{optimal} at \(\mu\) if
\[
\int_\Omega \rho(\omega)\,\mathbb P_t^\mu(d\omega)
=
U_t^{\mathcal G}(\mu).
\]

Allowing richer public states $\{\G_t\}$ and a larger class of continuation mechanisms expands each date-$t$ continuation value $U_t$. When $\mathcal G=\sigma(S_t)$, the seller may condition only on the posterior belief; when $\mathcal G=\sigma(Z_t)$, the seller may condition on the realized public full-history, including the non-posterior continuation state $Y_t$. The gap between $U_t^{\sigma(S_t)}$ and $U_t^{\sigma(Z_t)}$ measures the incremental date-$t$ continuation value of non-posterior public states beyond beliefs.

\medskip
Given public state $\sigma(S_t)\subseteq \mathcal G\subseteq \sigma(S_t,Y_t)$ and $Y_t$, we say that the selector collapse holds from \(\sigma(S_t,Y_t)\) to \(\mathcal G\) if, for every \(\mu\), there exists a \(\sigma(S_t,Y_t)\)-optimal selector \((\Gamma_t,\rho)\) at \(\mu\) such that \(\Gamma_t\) is \(\mathcal G\)-measurable; and the continuation value collapse from \(\sigma(S_t,Y_t)\) to \(\mathcal G\) if
\[
U_t^{\sigma(S_t,Y_t)}(\mu)=U_t^{\mathcal G}(\mu)
\qquad
\forall\,\mu\in\Delta(\Theta).
\]
Continuation value collapse is weaker than selector collapse; the two coincide under additional structure.\footnote{In \cref{subsec:condi-selec-coll}, we record four sufficient conditions under which selector collapse to \(\mathcal G\) can be verified. } Date-wise selector collapses at every date is a sufficient  condition for the irrelevance of a richer public state. Its converse does not generally hold. We aim to characterize the necessary and sufficient conditions for the latter.
```

### → Lean 建模对照（我的批注）

| 论文对象 | Lean 现状 | 判定 |
|---|---|---|
| $\mathcal G$-admissible selector $(\Gamma_t,\rho)$ | 0 处 | `[缺口]` |
| $\mathcal G$-optimal at $\mu$ | 0 处 | `[缺口]` |
| **selector collapse** | 0 处 | `[缺口]` |
| **continuation value collapse** $U_t^{\sigma(S_t,Y_t)}(\mu)=U_t^{\mathcal G}(\mu)\ \forall\mu$ | 0 处 | `[缺口]` |

> collapse 是论文标题里的核心概念（Dynamic Mechanism **Collapse**），目前在 Lean 中**一个字都没有**。
> 它依赖第 9 项（$U_t$ 的真定义）和第 13 项（$\mathcal G$ 夹逼）——两者补上后即可逐字陈述。

---

## 15. Truncation value（§3.3 原文，**Vₜ 的定义 + 停时递归**）

```latex
\paragraph{Truncation value.}
Fix $t\in\mathbb T$, a public state $z$, and a continuation mechanism $h\in\mathcal H_t$. The \emph{truncation} of the date-$t$ subgame $(z,h)$ replaces every public continuation history at which $Z_{t+1}$ realizes with the absorbing no-sale node, which yields the seller payoff $0$ and assigns each buyer the reservation payoff $0$; let $\mathcal E_t^{\circ}(z,h)$ denote its set of sequentially rational strategy-belief profiles. For an $\sigma(Z_t)$-measurable continuation rule $\Gamma_t$, the \emph{truncation payoff correspondence} is
\[
\mathcal V_t^{\Gamma_t}(\omega)
:=
\bigl\{
\pi_t\bigl(\omega,Z_t(\omega),\Gamma_t(\omega),b\bigr):
b\in\mathcal E_t^{\circ}\bigl(Z_t(\omega),\Gamma_t(\omega)\bigr)
\bigr\},
\]
and the \emph{truncation value} conditioning on a public state $\mathcal G_t$ with $\sigma(S_t)\subseteq\mathcal G_t\subseteq\sigma(Z_t)$ is
\[
V_t^{\mathcal G_t}(\mu)
:=
\sup\Bigl\{
\int_\Omega \rho(\omega)\,\mathbb P_t^\mu(d\omega):
\Gamma_t\text{ is }\mathcal G_t\text{-measurable},\
\rho\in\Sel\bigl(\mathcal V_t^{\Gamma_t}\bigr)
\Bigr\},
\qquad
\mu\in\Delta(\Theta).
\]
By construction $V_t^{\mathcal G_t}\ge 0$, it is bounded (\cref{ass:analytic-equilibrium}); it is a function of the posterior $\mu$, with $\mathcal G_t$ entering only as the conditioning richness of the continuation rule, and it involves no integration over the posterior process. Under the single-shot resource \cref{ass:single-shot}, the continuation value is the Snell envelope of the truncation values along the posterior process (see \cref{lem:stopping-form})
\begin{equation}\label{eq:stopping-form}
U_t^{\mathcal G_t}(\mu)=\max\Bigl\{V_t^{\mathcal G_t}(\mu),\
\int_\Omega U_{t+1}^{\mathcal G_{t+1}}\bigl(S_{t+1}(\omega)\bigr)\,\mathbb P_t^\mu(d\omega)\Bigr\}.
\end{equation}



\medskip
The option to defer lifts the static value $V_t$ to the Snell envelope $U_t$, raising it at beliefs from which waiting is profitable. An affine price, however, is neutral to this option. The shadow value $\lambda$ induces a price $\ell(\mu)=\int_\Theta\lambda(\theta)\,\mu(d\theta)$ that is affine in the belief; since beliefs evolve as a martingale, $\ell(S_t)$ is itself a martingale, and by optional sampling its value at the prior does not depend on the date at which the single allocation occurs. An affine price therefore dominates the Snell envelope $U_t$ exactly when it dominates the truncation values $V_t$, so the dual certificate of collapse is determined by $V_t$ alone (see \cref{lem:cap-equiv}).
```

### → Lean 建模对照（我的批注）

> 虽在 §3.3，但它定义了 Model 层直接消费的 $V_t$ 与停时递归，故收录于此。

| 论文 | Lean 现状 | 判定 |
|---|---|---|
| $V_t^{\mathcal G_t}(\mu):=\sup\{\int\rho\,d\mathbb P_t^\mu:\Gamma_t\ \mathcal G_t\text{-可测},\rho\in\Sel(\mathcal V_t^{\Gamma_t})\}$ | `DateValues.V`，**opaque 字段** | `[层级错位]` |
| 截断收益对应 $\mathcal V_t^{\Gamma_t}$、截断均衡 $\mathcal E_t^{\circ}$ | 0 处 | `[缺口]` |
| **"By construction $V_t\ge 0$"** | `DateValues.V_nonneg`，**公理** | **`[strengthening]`** |
| **"it is bounded (Assumption 2)"** | `DateValues.U_bddAbove`，**公理** | **`[strengthening]`** |
| **`eq:stopping-form`：$U_t=\max\{V_t,\int U_{t+1}(S_{t+1})d\mathbb P_t^\mu\}$**（Snell envelope，由 Assumption 1 经 `lem:stopping-form` 推出） | `SingleShot.stopping`，**公理字段** | **`[strengthening]`** |

> **本项是全文最重要的忠实性发现**：`DateValues`/`SingleShot` 的每一条"公理"，
> 论文其实都是**推导出来的结论**（"by construction" / "bounded (Assumption 2)" / Snell envelope）。
> Lean 把论文的**定理假设掉了**。blueprint 目前把 `stopping` 标成 `[encoding]` 是**低估**，应为 `[strengthening]`。
> 修法同第 9 项：定义 $V_t$（把 $\mathcal V_t^{\Gamma_t}$ 作参数、并假设论文的原语"无售出吸收节点收益 0"），
> 则 $V_t\ge0$ 由 sup 推出，不再是公理。

---

## 维护约定

- 本文件由脚本按正稿行区间**精确切片**生成，**不得手工改动代码块内内容**。
  正稿更新后重新切片即可（正稿在仓库外 `../../paper-source/`，私密，不入库）。
- 后续每落地一项，把对应行的判定从 `[缺口]`/`[层级错位]`/`[strengthening]` 改为 `[已对上]`。
- 命题级并排比对见 [`../CORRESPONDENCE.md`](../CORRESPONDENCE.md) 与 blueprint。
