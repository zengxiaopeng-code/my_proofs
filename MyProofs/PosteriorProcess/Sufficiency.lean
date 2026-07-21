import MyProofs.PosteriorProcess.Existence

/-!
# Lemma 1 (Posterior process) · Part (i)：充分统计量

## 论文原文
Lemma 1 的命题与证明（含本 Part (i)）的**逐字原文见 `docs/paper-lemma1.md`**（唯一权威来源）。

## 计划的 Lean 陈述（待存在性节点精化后填入）
对给定后验核 `S`，∀ 有界可测 `φ`：
  `P[(φ ∘ θ) | ℱ t] =ᵐ[P] P[(φ ∘ θ) | MeasurableSpace.comap S inferInstance]`

## 审查笔记（脚注错误——已由 Lean 反证）
论文正文用**泛函单调类定理**证 `F(μ):=∫φ dμ` 在 `Δ(Θ)` 上 Borel 可测——**这是对的**。
但论文脚注称"有界 Borel = 一致有界连续函数列的逐点极限"**不成立**（$\mathbf 1_{\mathbb Q}$ 是反例）。
该否定**已在 Lean 中证明**（无 `sorry`）：见 `FootnoteBaire.lean` 的
`PosteriorProcess.indicatorRat_not_pointwiseLimit_continuous`。故"脚注错"不再是人工判断，
而由 Lean 内核背书；建议在论文中删除该脚注（正文单调类论证不受影响）。
-/

open MeasureTheory

namespace PosteriorProcess

-- TODO: 待 `kernel_exists` 精化出具体的后验核对象后，在此陈述并证明充分性。

end PosteriorProcess
