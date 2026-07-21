import MyProofs.PosteriorProcess.Existence

/-!
# Lemma 1 (Posterior process) · Part (i)：充分统计量

## 论文原文陈述
> $S_t$ is a sufficient statistic for $\theta$ given $\mathcal F_t$: conditioning on $S_t$
> and conditioning on $\mathcal F_t$ yield the same conditional distribution of $\theta$.

## 计划的 Lean 陈述（待存在性节点精化后填入）
对给定后验核 `S`，∀ 有界可测 `φ`：
  `P[(φ ∘ θ) | ℱ t] =ᵐ[P] P[(φ ∘ θ) | MeasurableSpace.comap S inferInstance]`

## 人工审查笔记
论文正文用**泛函单调类定理**证 `F(μ):=∫φ dμ` 在 `Δ(Θ)` 上 Borel 可测——**这是对的**。
但论文脚注称"有界 Borel = 连续函数逐点极限"**不成立**（Baire class；$\mathbf 1_{\mathbb Q}$ 是反例），
应删除该脚注。详见 CORRESPONDENCE.md。
-/

open MeasureTheory

namespace PosteriorProcess

-- TODO: 待 `kernel_exists` 精化出具体的后验核对象后，在此陈述并证明充分性。

end PosteriorProcess
