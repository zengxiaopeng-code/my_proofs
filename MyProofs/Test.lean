import Mathlib

/-!
  环境自检文件。
  如果这个文件能编译通过、且下面每个定理左边都没有红色波浪线，
  说明 Lean + Mathlib 环境已经装好了。
-/

-- 例 1：最简单的等式，用 rfl（定义上相等）
example : 2 + 2 = 4 := by rfl

-- 例 2：自然数加法交换律（直接引用 Mathlib 的引理）
example (a b : ℕ) : a + b = b + a := by
  rw [Nat.add_comm]

-- 例 3：线性算术，交给 omega 自动证明
example (n : ℕ) (h : n > 3) : n + 1 > 4 := by
  omega

-- 例 4：环运算，交给 ring 自动证明
example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

-- 例 5：偶数 + 偶数 = 偶数（一个"像样"的证明，练手用）
theorem even_add_even (m n : ℕ) (hm : Even m) (hn : Even n) : Even (m + n) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  exact ⟨a + b, by rw [ha, hb]; ring⟩
