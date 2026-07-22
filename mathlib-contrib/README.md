# mathlib-contrib

上游 Mathlib 贡献的暂存区——**不是本论文项目的一部分**，`lake build` 不会编译它
（此文件夹不在 `MyProofs` lib 的范围内）。

## `ProbabilityMeasureBorel.lean`

`BorelSpace` / `StandardBorelSpace (ProbabilityMeasure Θ)`：证明 Giry σ-代数 = 弱拓扑的
Borel σ-代数。这是从 `MyProofs/PosteriorProcess/DoobDynkin.lean` 里的 `deltaTheta_*` 引理
重新打包、泛化到最弱假设的版本，供未来投稿 Mathlib。

- **单独编译验证**（对 v4.32.0，已通过）：
  ```bash
  lake env lean mathlib-contrib/ProbabilityMeasureBorel.lean
  ```
- **投稿前要做**：
  1. 填文件头的 `<YOUR NAME>`（Mathlib 要求署名）。
  2. 对 Mathlib **master** 重新校验（个别引理名可能微调）——走 fork 的 PR CI。
  3. 交流文字（PR 描述 / Zulip / review 回复）**须本人亲笔**，勿贴 AI 生成内容。
- 现状：**已搁置，留待以后**。缺口已核实仍在 master 上（Loogle 全零结果）。
