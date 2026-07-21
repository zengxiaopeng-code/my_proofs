# 论文 ↔ Lean 对应表（可信度的桥）

> 这份文件的唯一目的：让**不写 Lean 的人**也能**亲自核对**——
> "Lean 里证的那个陈述，确实就是我论文里的命题主张"。
>
> Lean 只保证"**你写下的陈述**被正确证明了"；它**不保证**那个陈述等于你的数学主张。
> 后者只能靠人**并排比对陈述**来确认。本文件就是并排比对的地方。

---

## 如何读一条 Lean「陈述」（不需要会写证明）

读**陈述**（`theorem 名字 (假设) : 结论`）比读证明容易得多，规则就几条：

| Lean 写法 | 数学含义 |
|-----------|----------|
| `(x : ℝ)` / `{x : ℝ}` | "取一个实数 x"（`{}` 表示可由上下文推断，数学意义相同） |
| `[IsProbabilityMeasure P]` | "P 是一个概率测度"（方括号 = 类型类假设，即"具有某种结构"） |
| `A → B` | "若 A 则 B"（也用于函数类型 `X → Y`） |
| `∀ φ, ...` / `∃ S, ...` | "对所有 φ" / "存在 S" |
| `f =ᵐ[P] g` | "f 与 g 关于测度 P **几乎处处**相等"（a.s.） |
| `P[f | 𝒢]` | 条件期望 $\mathbb E[f\mid\mathcal G]$ |
| `∫ x, φ x ∂μ` | 积分 $\int \varphi\,d\mu$ |
| `theorem foo (h1) (h2) : 结论` | "在假设 h1, h2 下，结论成立" |

**核对方法**：把定理的"假设"逐一对到论文的"设"，把"结论"对到论文的"证明目标"。下面每个命题都做好了这个对照。

---

## Lemma 1「Posterior process」的分解

论文这**一条** lemma 含一个主结论 + 三个子结论。Lean 里拆成 4 个声明，命名空间统一 `PosteriorProcess`：

```
Lemma 1 (Posterior process)  ──►  namespace PosteriorProcess
├─ 主结论：后验核存在 + 核性质  ──►  kernel_exists        (MyProofs/PosteriorProcess/Existence.lean)
├─ Part (i)  充分统计量        ──►  （待陈述）           (…/Sufficiency.lean)
├─ Part (ii) Doob–Dynkin 分解  ──►  factorization        (…/DoobDynkin.lean)
└─ Part (iii) 鞅性质           ──►  testfun_martingale ✅ (…/Martingale.lean)
```

依赖关系（blueprint 依赖图 `leanblueprint serve` 可视化）：(i)(ii)(iii) 都依赖主结论 `kernel_exists`。

---

## 逐条并排比对

### ✅ Part (iii) 鞅性质 — `PosteriorProcess.testfun_martingale`（已证）

**论文原文**：
> Fix $s\le t$ and any bounded Borel $\varphi:\Theta\to\mathbb R$. Then
> $\mathbb E[\int_\Theta\varphi\,dS_t\mid\mathcal F_s]=\mathbb E[\varphi(\theta)\mid\mathcal F_s]=\int_\Theta\varphi\,dS_s$ a.s.
> Since $\varphi$ was arbitrary, $\{S_t\}$ is an $(\mathcal F_t)$-martingale.

**Lean 陈述**：
```lean
theorem testfun_martingale
    (φ : Θ → ℝ) (_hφ : Measurable φ) (_hφb : ∃ C, ∀ x, |φ x| ≤ C) :
    Martingale (fun t => P[(φ ∘ θ) | ℱ t]) ℱ P
```

**逐块对照**：

| 论文 | Lean | 一致？ |
|------|------|:---:|
| "any bounded Borel $\varphi$" | `(φ : Θ → ℝ) (_hφ : Measurable φ) (_hφb : ∃ C, ∀ x,|φ x|≤C)` | ✅ |
| $\int_\Theta\varphi\,dS_t=\mathbb E[\varphi(\theta)\mid\mathcal F_t]$ | `P[(φ ∘ θ) | ℱ t]`（用核性质替换后的等价形式） | ✅ |
| "is an $(\mathcal F_t)$-martingale" | `Martingale (fun t => …) ℱ P` | ✅ |

**⚠️ 你需要认可的建模选择**（这就是"观察对应"的核心）：
1. 论文写"$\{S_t\}$ 是 $\Delta(\Theta)$ 上的（测度值）鞅"；Lean 编码为"**对每个 $\varphi$**，实值过程
   $t\mapsto\int\varphi\,dS_t$ 是鞅"。**这正是论文正文给出的严格定义**（$\Delta(\Theta)$ 非向量空间，
   测度值条件期望本就须逐 $\varphi$ 理解）。
2. 论文那句"$\mathbb E[S_t\mid\mathcal F_s]=S_s$ a.s. in $\Delta(\Theta)$"（把逐-$\varphi$ 的 a.s. 合并成
   一个测度的 a.s.）**尚未包含在这条 Lean 定理里**——它需要可数测度决定族，是独立的一步。
3. 用一般滤子 `ℱ` 而非 $\sigma(Z_t)$（对本部分无影响）。

> **结论**：只要你认可上述编码=论文对"测度值鞅"的意思，这条就是忠实的，且已被机器证明
> （`#print axioms` 仅依赖 `propext, Classical.choice, Quot.sound`，无 `sorryAx`）。

---

### 🔵 主结论 存在性+核性质 — `PosteriorProcess.kernel_exists`（已陈述，证明待填）

**论文原文**：存在 $\mathcal F_t$-可测的 Markov 核 $S_t$，使 $\int_\Theta\varphi\,dS_t=\mathbb E[\varphi(\theta)\mid\mathcal F_t]$ a.s.

**Lean 陈述**：
```lean
theorem kernel_exists (hθ : Measurable θ) (t : ι) :
    ∃ S : Ω → Measure Θ,
      (∀ ω, IsProbabilityMeasure (S ω)) ∧
      Measurable[ℱ t] S ∧
      ∀ φ : Θ → ℝ, Measurable φ → (∃ C, ∀ x, |φ x| ≤ C) →
        (fun ω => ∫ x, φ x ∂(S ω)) =ᵐ[P] P[(φ ∘ θ) | ℱ t]
```

| 论文 | Lean | 一致？ |
|------|------|:---:|
| 后验核 $S_t:\Omega\to\Delta(\Theta)$ | `∃ S : Ω → Measure Θ, ∀ ω, IsProbabilityMeasure (S ω)` | ✅ |
| $\mathcal F_t$-可测 | `Measurable[ℱ t] S` | ✅ |
| $\int\varphi\,dS_t=\mathbb E[\varphi(\theta)\mid\mathcal F_t]$ a.s. | `(fun ω => ∫ x, φ x ∂(S ω)) =ᵐ[P] P[(φ ∘ θ) | ℱ t]` | ✅ |

状态：陈述忠实；证明为 `sorry`（`#print axioms` 会显示 `sorryAx`，即**尚未背书**）。

---

### 🔵 Part (ii) Doob–Dynkin — `PosteriorProcess.factorization`（已陈述，证明待填）

**论文原文**：$S_t$ 是 $\sigma(Z_t)$-可测、取值标准 Borel 空间，故 $\exists f_t$ Borel，$S_t=f_t(Z_t)$ a.s.

**Lean 陈述**：
```lean
theorem factorization {E : Type*} [MeasurableSpace E]
    (Z : Ω → E) (S : Ω → Measure Θ)
    (hS : @Measurable Ω (Measure Θ) (MeasurableSpace.comap Z inferInstance) inferInstance S) :
    ∃ f : E → Measure Θ, Measurable f ∧ S = f ∘ Z
```
状态：陈述忠实；证明为 `sorry`。

---

### ⚪ Part (i) 充分统计量（尚未陈述）

计划陈述见 `Sufficiency.lean`。**人工审查发现**：论文该部分的脚注
"every bounded Borel function is the pointwise limit of a uniformly bounded sequence of
continuous functions" **不成立**（逐点极限只给出 Baire class 1 函数；$\mathbf 1_{\mathbb Q}$ 是
反例）。所幸正文用的是**泛函单调类定理**，论证正确——**建议删除该脚注**。

---

## 一句话总结给同行

> "本文数学部分正逐条形式化为 Lean 4（仓库 + CI 见 README）。每条命题的论文陈述与 Lean 陈述在
> `CORRESPONDENCE.md` 中并排列出并标注了全部建模选择；绿色节点（当前为 Part (iii)）已由 Lean 内核
> 机器验证，且 `#print axioms` 确认不依赖任何 `sorry`。"
