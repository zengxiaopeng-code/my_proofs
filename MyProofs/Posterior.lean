import MyProofs.Posterior.Basic
import MyProofs.Posterior.Existence
import MyProofs.Posterior.Sufficiency
import MyProofs.Posterior.DoobDynkin
import MyProofs.Posterior.Martingale

/-!
# Lemma: Posterior process (聚合)

对应论文 `lem:posterior-martingale`。形式化进度：

| 节点         | Lean 声明                          | 状态       |
|--------------|------------------------------------|------------|
| 存在性+核性质 | `Posterior.exists_posterior_kernel`| `sorry`    |
| (i) 充分性   | （待陈述）                          | 未陈述     |
| (ii) 因子分解 | `Posterior.posterior_factorization`| `sorry`    |
| (iii) 鞅性质  | `Posterior.posterior_testfun_martingale` | ✅ 已证 |
-/
