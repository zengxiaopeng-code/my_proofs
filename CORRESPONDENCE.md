# Lemma 1 (Posterior process)：从哪看、怎么验证

本项目形式化论文的 **Lemma 1 (Posterior process)**。三份东西各司其职：

| 你想要 | 去哪 |
|---|---|
| **论文命题 + 证明的逐字原文**（核对是不是原命题） | [docs/paper-lemma1.md](docs/paper-lemma1.md)（唯一权威档案） |
| **论文每一步 ↔ 哪个 Lean 声明、证没证完**（可点开的对照 + 依赖图） | **blueprint**（`blueprint/web/index.html`；每个节点链到具体 Lean 声明，绿色=Lean 已完整背书） |
| **机器可查的"证没证"判据** | 见下方命令 |

> 行内标准做法：**blueprint 本身就是论文↔Lean 的对照**——它把证明按论文四步分解成节点，
> 每个节点链接对应 Lean 声明并标注是否已被内核证明。本文件只是入口指路，不再另列对照表。

## 读者怎么验证

```bash
lake build                                         # 无 error = Lean 内核验证通过（含 sorry 的会以 warning 提示）
lake env lean MyProofs/PosteriorProcess/Audit.lean # 看 #print axioms：无 sorryAx = 真证完；出现 sorryAx = 还没证
```

判据：`#print axioms X` 只出现 `propext / Classical.choice / Quot.sound` ⇒ 已背书；
一旦出现 `sorryAx` ⇒ 依赖链上有 `sorry`，尚未背书。无法造假。

## 当前状态速览

| 论文部分 | Lean 声明 | 状态 |
|---|---|---|
| 存在性 + 核性质 | `kernel_exists` | 🔵 含 sorry |
| (i) 充分性 | （未形式化） | ⚪ |
| (ii) Doob–Dynkin（抽象） | `factorization` | ✅ 已证 |
| (ii) Δ(Θ) 标准 Borel | `deltaTheta_standardBorel` | 🔵 库缺口 sorry |
| (ii) 完整版 | `factorization_posterior` | 🔵 依赖上者 |
| (iii) 鞅 | `testfun_martingale` | ✅ 已证 |
