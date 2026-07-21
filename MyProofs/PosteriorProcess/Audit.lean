import MyProofs.PosteriorProcess

/-!
# 背书审计

`#print axioms` 列出一个定理**最终依赖的全部公理**。判据：

* 只出现 `propext`, `Classical.choice`, `Quot.sound`
  → 这是 Lean/Mathlib 的标准可信公理，**证明完整、已被内核背书**。
* 一旦出现 `sorryAx`
  → 证明里有 `sorry`（或依赖链上有），**尚未背书**。

这就是"Lean 到底证没证"的机器可查判据——无法造假。
-/

open PosteriorProcess

-- ✅ 已证：应只依赖 propext / Classical.choice / Quot.sound
#print axioms testfun_martingale

-- 🔵 含 sorry：应出现 sorryAx，暴露"还没证"
#print axioms kernel_exists

-- ✅ 已证：论文 (i) 脚注的反证（1_ℚ 非连续函数逐点极限）；应无 sorryAx
#print axioms indicatorRat_not_pointwiseLimit_continuous
