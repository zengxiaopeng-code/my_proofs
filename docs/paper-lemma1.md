# Lemma 1 (Posterior process)：论文逐字原文

> **权威档案**：本文件逐字转录论文中 Lemma 1（`\label{lem:posterior-martingale}`）的
> **命题与证明**，作为形式化的唯一原文来源。项目内其他文件（CORRESPONDENCE.md、blueprint、
> 各 `.lean` docstring）**一律指向此处，不再另行誊抄**，以杜绝漂移。
> 转录自论文 LaTeX 源；引用命令（`\citep{...}` 等）按原样保留。数学用 `$…$` 渲染，内容未改。

---

## Statement（命题）

For each $t\in\mathbb T$, there exists an $\mathcal F_t$-measurable posterior kernel
$S_t:\Omega\to\Delta(\Theta)$ such that, for every bounded Borel function
$\varphi:\Theta\to\mathbb R$,

$$\int_\Theta \varphi(\theta')\,S_t(\omega)(d\theta') = \mathbb E[\varphi(\theta)\mid\mathcal F_t](\omega)\qquad\text{a.s.}$$

In particular:

**(i)** $S_t$ is a sufficient statistic for $\theta$ given $\mathcal F_t$: conditioning on
$S_t$ and conditioning on $\mathcal F_t$ yield the same conditional distribution of $\theta$.

**(ii)** Since $\mathcal F_t = \sigma(Z_t)$, the Doob–Dynkin lemma implies that
$S_t = f_t(Z_t)$ for some Borel measurable function $f_t$; that is, the public history
$Z_t$ induces the posterior $S_t$.

**(iii)** $\{S_t\}_{t\in\mathbb T}$ is a bounded $(\mathcal F_t)$-martingale.

---

## Proof（证明）

### Existence of the posterior kernel.

Since $\Theta$ is a compact Polish space, $\Delta(\Theta)$ equipped with the weak topology
is also a compact Polish space, hence a standard Borel space. The map $\theta:\Omega\to\Theta$
is $\mathcal F$-measurable and $\mathcal F_t\subseteq\mathcal F$ is a sub-$\sigma$-algebra. By
the standard theorem on regular conditional distributions for Polish-space-valued random
variables `\citep[Theorem~6.3]{Kallenberg2002}`, there exists a Markov kernel
$S_t:\Omega\times\mathcal B(\Theta)\to[0,1]$ such that

**(a)** $\omega\mapsto S_t(\omega)(B)$ is $\mathcal F_t$-measurable for every $B\in\mathcal B(\Theta)$, and

**(b)** $S_t(\omega)(\cdot)=\mathbb P(\theta\in\cdot\mid\mathcal F_t)(\omega)$ $\;\mathbb P$-a.s.

Equivalently, for every bounded Borel $\varphi:\Theta\to\mathbb R$,

$$\int_\Theta\varphi(\theta')\,S_t(\omega)(d\theta') =\mathbb E[\varphi(\theta)\mid\mathcal F_t](\omega)\qquad\text{a.s.}\tag{eq:kernel-property}$$

### Part (i): Sufficiency.

Fix any bounded Borel $\varphi:\Theta\to\mathbb R$ and define $F:\Delta(\Theta)\to\mathbb R$ by
$F(\mu):=\int_\Theta\varphi(\theta')\,\mu(d\theta')$. By the functional monotone class theorem,
$F$ is Borel measurable on $\Delta(\Theta)$: it holds for continuous $\varphi$ by the definition
of the weak topology, and extends to all bounded Borel $\varphi$ by dominated convergence.
Therefore $\omega\mapsto F(S_t(\omega))$ is $\sigma(S_t)$-measurable. By
(eq:kernel-property), $\mathbb E[\varphi(\theta)\mid\mathcal F_t](\omega)=F(S_t(\omega))$ a.s., so
$\mathbb E[\varphi(\theta)\mid\mathcal F_t]$ is $\sigma(S_t)$-measurable. For any
$B\in\sigma(S_t)\subseteq\mathcal F_t$,

$$\mathbb E\bigl[\varphi(\theta)\mathbf 1_B\bigr] =\mathbb E\bigl[\mathbb E[\varphi(\theta)\mid\mathcal F_t]\mathbf 1_B\bigr] =\mathbb E\bigl[F(S_t)\mathbf 1_B\bigr].$$

Since $F(S_t)$ is $\sigma(S_t)$-measurable, uniqueness of conditional expectation gives
$\mathbb E[\varphi(\theta)\mid\mathcal F_t]=\mathbb E[\varphi(\theta)\mid S_t]$ a.s. As $\varphi$
was arbitrary, conditioning on $S_t$ and conditioning on $\mathcal F_t$ yield the same
conditional distribution of $\theta$.

### Part (ii): Induction by $Z_t$.

Since $\mathcal F_t=\sigma(Z_t)$ and $S_t$ is $\sigma(Z_t)$-measurable with values in the
standard Borel space $\Delta(\Theta)$, the Doob–Dynkin lemma `\citep[Lemma~1.14]{Kallenberg2002}`
yields a Borel measurable function $f_t:E_t\to\Delta(\Theta)$ such that

$$S_t(\omega)=f_t(Z_t(\omega))\qquad\mathbb P\text{-a.s.}$$

Hence $Z_t$ induces the posterior $S_t$ through the measurable map $f_t$.

### Part (iii): Martingale property.

Fix $s\le t$ and any bounded Borel $\varphi:\Theta\to\mathbb R$. Then

$$\mathbb E\!\left[\int_\Theta\varphi(\theta')\,S_t(\omega)(d\theta')\,\Big|\,\mathcal F_s\right] \overset{\text{(eq:kernel-property)}}{=} \mathbb E\bigl[\mathbb E[\varphi(\theta)\mid\mathcal F_t]\mid\mathcal F_s\bigr] \overset{\text{tower}}{=} \mathbb E[\varphi(\theta)\mid\mathcal F_s] \overset{\text{(eq:kernel-property)}}{=} \int_\Theta\varphi(\theta')\,S_s(\omega)(d\theta')\quad\text{a.s.},$$

where the second equality uses the tower property of conditional expectations and
$\mathcal F_s\subseteq\mathcal F_t$. Since $\varphi$ was arbitrary,
$\mathbb E[S_t\mid\mathcal F_s]=S_s$ a.s. in $\Delta(\Theta)$. Boundedness holds because
$S_t(\omega)$ is a probability measure: for every bounded $\varphi$,
$\bigl|\int_\Theta\varphi\,dS_t\bigr|\le\|\varphi\|_\infty<\infty$.
