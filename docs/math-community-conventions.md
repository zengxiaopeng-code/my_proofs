# 数学圈 Lean 形式化项目的习惯（备忘录）

> 备忘目的：记住"论文/定理形式化"项目在 GitHub 上的通行做法，别忘了。
> 结论来自 2026-07 实地翻看四个公开旗舰项目的 CI 配置（见文末链接）。

## 一、雷打不动的"标配三件套"

做"把一篇论文/一个定理形式化"的项目，几乎都有这三样：

1. **CI 跑 `lake build`** —— 每次推送，GitHub 服务器自动编译并逐条核验所有证明。
   这是"机器背书"的底线，所有项目都有。
2. **`blueprint/` 依赖图**（[leanblueprint](https://github.com/PatrickMassot/leanblueprint)）——
   把论文拆成节点，绿=已证/蓝=已陈述待证，节点链到对应 Lean 声明。PFR、FLT、Carleson 都用。
3. **GitHub Pages 托管** —— 把依赖图部署成公开网页给同行点。
   ⚠️ **前提是仓库公开**。这些旗舰项目全是 public。私有仓库要托管得转公开或上付费计划。

## 二、docgen：**不是共识**，大项目也常常不要

docgen = 给代码生成一个可浏览的 HTML API 文档站（像 Mathlib 官方 docs 那样）。

**关键事实**：**FLT（Kevin Buzzard 的费马大定理项目，资源最雄厚之一）把 docgen 关掉了**，
其 workflow 原话：

> *"Documentation compilation disabled: docgen regularly runs for hours..."*
> （文档编译已禁用：docgen 经常跑好几个小时……）

对比：
| 项目 | docgen |
|------|--------|
| PFR | ✅ 建（`docgen-action`, `blueprint: true`） |
| FLT | ❌ **关掉**，理由"跑几小时" |
| DeepMind formal-conjectures | ✅ 建，但配一整套 olean/文档缓存硬扛 |

**记住**：docgen 是"项目大 + 有 CI 预算 + 愿维护缓存"才上的**展示装饰**，
**和证明验证无关**。小项目不要它完全正常，连 FLT 都可以不要。

## 三、精确导入 vs `import Mathlib`

PFR 和 FLT 都有一条 lint：**"Don't 'import Mathlib', use precise imports"**。

- `import Mathlib`：一行拉进整个库。**新手友好，但编译慢，docgen 会拉进整个 Mathlib**
  （这正是 docgen 慢的深层原因之一）。
- 精确导入（如 `import Mathlib.Probability.Martingale.Basic`）：成熟项目规范，编译和文档都轻得多。

**本项目现状**：起步用的是 `import Mathlib`（省心，小项目 OK）。项目长大后可切精确导入。

## 四、新趋势（留意，非必须）

FLT 的注释提到正在**迁移到 Verso blueprint**——Verso 是较新的文档/blueprint 系统，
可能逐步替代 leanblueprint。现在还早，先知道有这回事即可。

## 五、对本项目意味着什么

- 已踩在主流上：`lake build` CI ✅ + blueprint 依赖图 ✅ 都有了。
- docgen：留着无妨，但知道它慢且性价比低（对 3 个声明）；想快就删，不影响背书。
- Pages 托管：因仓库私有暂缓（见 [[hosting-decision-pending]] 记忆）。
- 精确导入：等声明多了再考虑切换。

## 参考项目（都可直接在 GitHub 看 CI 配置）

- PFR（Tao）：https://github.com/teorth/pfr
- FLT（Buzzard）：https://github.com/ImperialCollegeLondon/FLT
- Carleson（van Doorn）：https://github.com/fpvandoorn/carleson
- formal-conjectures（Google DeepMind）：https://github.com/google-deepmind/formal-conjectures
- leanblueprint 工具：https://github.com/PatrickMassot/leanblueprint
