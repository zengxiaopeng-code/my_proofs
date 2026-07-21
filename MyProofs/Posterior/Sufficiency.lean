import Mathlib
import MyProofs.Posterior.Existence

/-!
# Part (i)：充分统计量

论文 Lemma "Posterior process" 第 (i) 部分：`S_t` 是关于 `θ`（给定 `F_t`）的
充分统计量——对 `S_t` 取条件与对 `F_t` 取条件给出 `θ` 相同的条件分布。

证明依赖存在性文件里的后验核 `S`，以及
`F(μ) := ∫ φ dμ` 在 `Δ(Θ)` 上的 Borel 可测性（泛函单调类定理；
**注意论文脚注里"有界 Borel = 连续函数逐点极限"的说法是错的，见人工审查**）。

关键步骤：`E[φ(θ)|F_t] = F(S_t)` 是 `σ(S_t)`-可测 ⇒ 由条件期望唯一性，
`E[φ(θ)|σ(S_t)] = E[φ(θ)|F_t]` a.s.；因 `φ` 任意，两个条件分布相同。

陈述涉及 `σ(S_t)` 与后验核对象，较重，先留待精化。
-/

open MeasureTheory

namespace Posterior

-- TODO: 待存在性节点 (exists_posterior_kernel) 精化后，在此陈述充分性。
-- 计划形式：对给定的后验核 `S`，∀ 有界可测 φ，
--   P[(φ ∘ θ) | (ℱ t)] =ᵐ[P] P[(φ ∘ θ) | MeasurableSpace.comap S inferInstance]

end Posterior
