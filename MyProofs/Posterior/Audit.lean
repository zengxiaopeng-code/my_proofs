import MyProofs.Posterior

/-!
# 背书审计

`#print axioms` 列出一个定理**最终依赖的全部公理**。判据：

* 只出现 `propext`, `Classical.choice`, `Quot.sound`
  → 这是 Lean/Mathlib 的标准可信公理，**证明完整、已被内核背书**。
* 一旦出现 `sorryAx`
  → 证明里有 `sorry`（或依赖链上有），**尚未背书**。

这就是"Lean 到底证没证"的机器可查判据——无法造假。
-/

open Posterior

-- ✅ 已证：应只依赖 propext / Classical.choice / Quot.sound
#print axioms posterior_testfun_martingale

-- 🔵 含 sorry：应出现 sorryAx，暴露"还没证"
#print axioms exists_posterior_kernel
