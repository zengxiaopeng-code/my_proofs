# 像行内人一样管理 Lean 项目（playbook）

> 把数学圈（Mathlib/PFR/FLT 等）管理 Lean 形式化项目的规矩，落到本项目的实操清单。
> 每条都有：**是什么 / 为什么 / 本项目怎么做**。相关背景见 [[math-community-conventions]]。

---

## 1. 精确导入，永不 `import Mathlib`

- **是什么**：每个 `.lean` 只 `import` 它真正用到的具体模块，如
  `import Mathlib.Probability.Martingale.Basic`。
- **为什么**：`import Mathlib` 拉进整库（6000+ 模块）→ 编译慢、docgen 撑爆磁盘、依赖不透明。
  本项目实测：改精确导入后编译任务 **8663 → 2941**，单文件 **80s → 7s**。
- **怎么做**：
  1. 光标放引理名上按 **F12**（跳转定义）→ 落在哪个 `Mathlib/A/B/C.lean` → `import Mathlib.A.B.C`。
  2. 或用 `#min_imports in <声明>`（来自 `Mathlib.Tactic.MinImports`）自动算最小导入。
  3. 或"先写候选导入 → 编译 → 报 `unknown identifier` 就补"。
  4. CI 里有 lint 强制执行（见 §4）。你导入的模块会自动带上它的依赖，但不会拉进无关领域。

## 2. 结构：命名空间镜像文件夹，一个主题一个文件

- **是什么**：`namespace` 对应文件夹；每个文件放一个连贯主题；顶层聚合文件 `import` 各子模块。
- **本项目**：`MyProofs/PosteriorProcess/` ↔ `namespace PosteriorProcess` ↔ 论文 Lemma 1；
  每个子结论一个文件（Existence/Sufficiency/DoobDynkin/Martingale）；
  `MyProofs/PosteriorProcess.lean` 是聚合入口 + 进度表。
- **命名**：描述性名字（`testfun_martingale`、`kernel_exists`），名字本身说明陈述内容。

## 3. `sorry` / 公理纪律：机器可查的"证没证"

- **判据**：`#print axioms 定理名`。只出现 `propext, Classical.choice, Quot.sound` = 真背书；
  出现 `sorryAx` = 还没证完。见本项目 [`../MyProofs/PosteriorProcess/Audit.lean`](../MyProofs/PosteriorProcess/Audit.lean)。
- **规矩**：`sorry` 只是警告不是错误，所以"CI 绿"不等于"无 sorry"。哪些真绿以 `#print axioms` 为准。

## 4. CI：验证是底线，docgen 要喂饱

- **底线**：`lake build`（= lean-action）逐条核验证明。这一步绿 = 云端独立背书。
- **两条让 CI 健康的行内规矩**（本项目 `.github/workflows/lean_action_ci.yml`）：
  1. **禁止 `import Mathlib` 的 lint**：`! (find MyProofs -name '*.lean' | xargs grep -E '^import Mathlib$')`，有就判失败。
  2. **`jlumbroso/free-disk-space` 腾磁盘**：否则 docgen 会 `No space left on device` 崩溃。
- **docgen（可选装饰）**：生成可浏览 API 文档，很重；小项目可不要（FLT 都因跑几小时关掉过）。

## 5. 可追溯性：论文 ↔ Lean 必须可核对

- 每个 `.lean` 顶部贴**论文原文陈述** + 逐符号对照 + 建模选择披露。
- [`../CORRESPONDENCE.md`](../CORRESPONDENCE.md)：命题级并排比对（不写 Lean 也能核对"证的就是论文主张"）。
- [`paper-model.md`](paper-model.md)：论文 model 原文存档（每上传一段原文就追加）。
- **blueprint** 依赖图（`leanblueprint`）+ **checkdecls**（校验图里 `\lean` 名字真实存在）。

## 6. 可复现：版本全锁死

- `lean-toolchain` 锁 Lean 版本；`lake-manifest.json` 锁所有依赖的 commit；`lake exe cache get` 取预编译 Mathlib。
- 别人 clone 后 `lake exe cache get && lake build` 就能一比一复现你的验证。

## 7. 日常习惯

- 小步提交，提交信息说清"证了什么/发现什么"。
- 以 **CI 绿** 为对外信号；论文里附一句"Lean 形式化见 <repo>，CI 持续验证"。
- 发现论文里"一句话打包了非平凡事实"（如本项目 Δ(Θ) 标准 Borel），就**拆成独立节点**单独跟踪。

---

## 快速自检清单（新文件/新命题时过一遍）
- [ ] 没有 `import Mathlib`，只精确导入
- [ ] 顶部有论文原文陈述 + 对照
- [ ] `#print axioms` 确认无 `sorryAx`（或明确标注 sorry 待补）
- [ ] 命名描述性、放对 namespace/文件夹
- [ ] blueprint 节点 + CORRESPONDENCE 已更新
- [ ] 本地 `lake build` 通过再推送
