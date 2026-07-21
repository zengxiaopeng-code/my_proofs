# my_proofs — Lean 4 formalization

一篇经济学论文数学部分的 Lean 4 形式化，用于**机器验证证明无误**。
基于 Lean 4 + [Mathlib](https://github.com/leanprover-community/mathlib4)。

## 当前进度：Lemma "Posterior process"

| 节点 | Lean 声明 | 状态 |
|------|-----------|------|
| 存在性 + 核性质 | `Posterior.exists_posterior_kernel` | 🔵 已陈述，待证 (`sorry`) |
| (i) 充分统计量 | — | ⚪ 待陈述 |
| (ii) Doob–Dynkin 因子分解 | `Posterior.posterior_factorization` | 🔵 已陈述，待证 (`sorry`) |
| (iii) 鞅性质 | `Posterior.posterior_testfun_martingale` | ✅ **已证，无 sorry** |

依赖图（blueprint）见 [`blueprint/src/content.tex`](blueprint/src/content.tex)。

## 如何自行验证（复现）

```bash
elan default stable          # 需先装 elan (Lean 版本管理器)
lake exe cache get           # 下载预编译 Mathlib
lake build                   # 编译并逐步核验所有证明
```

确认某条定理确实"无 sorry、只依赖标准公理"：

```bash
lake env lean MyProofs/Check.lean
# 输出: '...posterior_testfun_martingale' depends on axioms:
#        [propext, Classical.choice, Quot.sound]
# —— 没有 sorryAx、没有自定义 axiom，即真正的机器背书。
```

## 说明

- CI（GitHub Actions）在每次推送时运行 `lake build`，验证形式化可编译。
- 注意 `sorry` 只产生警告不产生错误；"哪些定理真正无 sorry"以上表与 `#print axioms` 为准。
