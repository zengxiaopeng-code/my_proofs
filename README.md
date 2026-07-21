# my_proofs — Lean 4 formalization

一篇经济学论文数学部分的 Lean 4 形式化，用于**机器验证证明无误**。
基于 Lean 4 + [Mathlib](https://github.com/leanprover-community/mathlib4)。

## 论文 ↔ Lean 对应

👉 **[CORRESPONDENCE.md](CORRESPONDENCE.md)** — 每条命题的论文原文陈述与 Lean 陈述**并排比对** +
建模选择披露。这是核对"Lean 证的就是论文主张"的地方（不写 Lean 也能读）。

## 当前进度：Lemma 1「Posterior process」

命名空间 `PosteriorProcess` 一一对应论文 Lemma 1；文件夹 [`MyProofs/PosteriorProcess/`](MyProofs/PosteriorProcess/) 每个文件一个子结论。

| 论文部分 | Lean 声明 | 文件 | 状态 |
|----------|-----------|------|------|
| 存在性 + 核性质 | `PosteriorProcess.kernel_exists` | `Existence.lean` | 🔵 已陈述，待证 (`sorry`) |
| (i) 充分统计量 | — | `Sufficiency.lean` | ⚪ 待陈述 |
| (ii) Doob–Dynkin 因子分解 | `PosteriorProcess.factorization` | `DoobDynkin.lean` | 🔵 已陈述，待证 (`sorry`) |
| (iii) 鞅性质 | `PosteriorProcess.testfun_martingale` | `Martingale.lean` | ✅ **已证，无 sorry** |

依赖图（blueprint）见 [`blueprint/src/content.tex`](blueprint/src/content.tex)；`leanblueprint serve` 可视化。

## 如何自行验证（复现）

```bash
elan default stable          # 需先装 elan (Lean 版本管理器)
lake exe cache get           # 下载预编译 Mathlib
lake build                   # 编译并逐步核验所有证明
```

确认某条定理确实"无 sorry、只依赖标准公理"：

```bash
lake env lean MyProofs/PosteriorProcess/Audit.lean
# testfun_martingale → depends on axioms: [propext, Classical.choice, Quot.sound]  ✅ 真背书
# kernel_exists       → depends on axioms: [..., sorryAx]                          🔵 尚未证
```

## 说明

- CI（GitHub Actions）在每次推送时运行 `lake build`，验证形式化可编译。
- 注意 `sorry` 只产生警告不产生错误；"哪些定理真正无 sorry"以上表、`CORRESPONDENCE.md` 与 `#print axioms` 为准。
