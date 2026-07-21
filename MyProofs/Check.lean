import MyProofs.Posterior.Martingale

/-!
# 背书检查

`#print axioms` 列出一个定理最终依赖的所有公理。
- 只出现 `propext`, `Classical.choice`, `Quot.sound` → 这是 Mathlib 的三条标准公理，
  数学界公认可靠，等价于经典数学的基础。
- 若出现 `sorryAx` → 说明证明里藏了 `sorry`（没真正证完），**背书无效**。
-/

open Posterior

-- 已证的鞅定理：应只依赖三条标准公理，绝不含 sorryAx
#print axioms posterior_testfun_martingale
