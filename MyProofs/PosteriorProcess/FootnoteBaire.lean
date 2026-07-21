import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Lemma 1 (i) 脚注的 Lean 反证

Lemma 1 命题与证明的逐字原文见 `docs/paper-lemma1.md`（唯一权威来源）。

论文 Part (i) 的**脚注**断言：“每个有界 Borel 函数都是一致有界连续函数列的逐点极限”
（“by Lusin's theorem and dominated convergence”）。本文件把该断言的否定形式化，
从而由 **Lean 内核裁定该脚注为假**（不再是人工判断）。

本文件证的是比脚注更强的否定：有理数示性函数 `1_ℚ`（有界 Borel）**不是任何连续函数列的
逐点极限**（无论是否一致有界）。特别地它也不是一致有界连续函数列的逐点极限，脚注的断言不成立。
（论文正文用泛函单调类定理证 `F` Borel 可测——那一步是对的、且已由 blueprint 单独处理；
脚注只是它旁边一条方法有误、且非必要的注解。）

## 证明思路（自足的 Baire 纲反证，不依赖通用 Baire class 1 框架）
设 `gₙ → 1_ℚ` 逐点。令 `A_N = {x | ∀ n ≥ N, 1/2 ≤ gₙ x}`、`B_N = {x | ∀ n ≥ N, gₙ x ≤ 1/2}`
（连续函数的不等式集，皆闭）。每个有理点落入某 `A_N`（因 `gₙ→1`），每个无理点落入某 `B_N`
（因 `gₙ→0`），故 `ℝ = (⋃_N A_N) ∪ (⋃_N B_N)` 为可数个闭集之并。由 Baire 纲定理
（`nonempty_interior_of_iUnion_of_closed`），其中某个 `A_N` 或 `B_N` 含一个非空开集 `U`。
若 `U ⊆ A_N`：`U` 含无理点 `x`（无理数稠密），在其上 `1/2 ≤ gₙ x → 1/2 ≤ 0`，矛盾；
若 `U ⊆ B_N`：`U` 含有理点 `x`（有理数稠密），在其上 `gₙ x ≤ 1/2 → 1 ≤ 1/2`，矛盾。
-/

open Filter Set Topology

namespace PosteriorProcess

/-- 有理数（作为 ℝ 的子集）。`Irrational x` 恰为 `x ∉ ratSet`。 -/
private def ratSet : Set ℝ := Set.range ((↑) : ℚ → ℝ)

/-- `1_ℚ`：有理数示性函数，有理处取 `1`、无理处取 `0`。有界 Borel 函数。 -/
private noncomputable def indRat : ℝ → ℝ := ratSet.indicator (fun _ => 1)

/-- **论文 Lemma 1 (i) 脚注的反证**：`1_ℚ` 不是任何连续函数列的逐点极限。
因此脚注“有界 Borel 函数 = 一致有界连续函数列的逐点极限”不成立。 -/
theorem indicatorRat_not_pointwiseLimit_continuous :
    ¬ ∃ g : ℕ → ℝ → ℝ, (∀ n, Continuous (g n)) ∧
      ∀ x, Tendsto (fun n => g n x) atTop (nhds (indRat x)) := by
  rintro ⟨g, hg_cont, hg_lim⟩
  -- 闭集族
  set A : ℕ → Set ℝ := fun N => {x | ∀ n, N ≤ n → (1 : ℝ) / 2 ≤ g n x} with hA
  set B : ℕ → Set ℝ := fun N => {x | ∀ n, N ≤ n → g n x ≤ (1 : ℝ) / 2} with hB
  set F : Bool × ℕ → Set ℝ := fun p => bif p.1 then B p.2 else A p.2 with hF
  have hAclosed : ∀ N, IsClosed (A N) := by
    intro N
    have hEq : A N = ⋂ n, ⋂ _ : N ≤ n, {x | (1 : ℝ) / 2 ≤ g n x} := by
      ext x; simp only [hA, mem_setOf_eq, mem_iInter]
    rw [hEq]
    exact isClosed_iInter fun n => isClosed_iInter fun _ =>
      isClosed_le continuous_const (hg_cont n)
  have hBclosed : ∀ N, IsClosed (B N) := by
    intro N
    have hEq : B N = ⋂ n, ⋂ _ : N ≤ n, {x | g n x ≤ (1 : ℝ) / 2} := by
      ext x; simp only [hB, mem_setOf_eq, mem_iInter]
    rw [hEq]
    exact isClosed_iInter fun n => isClosed_iInter fun _ =>
      isClosed_le (hg_cont n) continuous_const
  have hFclosed : ∀ p, IsClosed (F p) := by
    rintro ⟨b, N⟩; cases b
    · exact hAclosed N
    · exact hBclosed N
  -- 覆盖：每个点属于某个 A_N 或 B_N
  have hcover : ⋃ p, F p = univ := by
    rw [iUnion_eq_univ_iff]
    intro x
    by_cases hx : x ∈ ratSet
    · have hval : indRat x = 1 := Set.indicator_of_mem hx (fun _ => (1 : ℝ))
      have hlim1 : Tendsto (fun n => g n x) atTop (nhds (1 : ℝ)) := by
        have h := hg_lim x; rwa [hval] at h
      have hev : ∀ᶠ n in atTop, (1 : ℝ) / 2 ≤ g n x := by
        have hio : ∀ᶠ n in atTop, g n x ∈ Ioi ((1 : ℝ) / 2) :=
          hlim1.eventually (Ioi_mem_nhds (by norm_num))
        exact hio.mono fun n hn => le_of_lt hn
      obtain ⟨N, hN⟩ := eventually_atTop.1 hev
      exact ⟨(false, N), fun n hn => hN n hn⟩
    · have hval : indRat x = 0 := Set.indicator_of_notMem hx (fun _ => (1 : ℝ))
      have hlim0 : Tendsto (fun n => g n x) atTop (nhds (0 : ℝ)) := by
        have h := hg_lim x; rwa [hval] at h
      have hev : ∀ᶠ n in atTop, g n x ≤ (1 : ℝ) / 2 := by
        have hio : ∀ᶠ n in atTop, g n x ∈ Iio ((1 : ℝ) / 2) :=
          hlim0.eventually (Iio_mem_nhds (by norm_num))
        exact hio.mono fun n hn => le_of_lt hn
      obtain ⟨N, hN⟩ := eventually_atTop.1 hev
      exact ⟨(true, N), fun n hn => hN n hn⟩
  -- Baire 纲：某闭集有内点
  obtain ⟨p, hp⟩ := nonempty_interior_of_iUnion_of_closed hFclosed hcover
  have hUopen : IsOpen (interior (F p)) := isOpen_interior
  have hUsub : interior (F p) ⊆ F p := interior_subset
  obtain ⟨b, N⟩ := p
  cases b
  · -- F = A N：取无理点得矛盾
    have hAsub : interior (A N) ⊆ A N := hUsub
    obtain ⟨x, hxU, hxirr⟩ :=
      dense_irrational.inter_open_nonempty (interior (A N)) hUopen hp
    have hxA : ∀ n, N ≤ n → (1 : ℝ) / 2 ≤ g n x := hAsub hxU
    have hval : indRat x = 0 :=
      Set.indicator_of_notMem hxirr (fun _ => (1 : ℝ))
    have hlim0 : Tendsto (fun n => g n x) atTop (nhds (0 : ℝ)) := by
      have h := hg_lim x; rwa [hval] at h
    have : (1 : ℝ) / 2 ≤ 0 :=
      ge_of_tendsto hlim0 (eventually_atTop.2 ⟨N, fun n hn => hxA n hn⟩)
    linarith
  · -- F = B N：取有理点得矛盾
    have hBsub : interior (B N) ⊆ B N := hUsub
    have hRatDense : Dense ratSet := Rat.denseRange_cast
    obtain ⟨x, hxU, hxrat⟩ :=
      hRatDense.inter_open_nonempty (interior (B N)) hUopen hp
    have hxB : ∀ n, N ≤ n → g n x ≤ (1 : ℝ) / 2 := hBsub hxU
    have hval : indRat x = 1 := Set.indicator_of_mem hxrat (fun _ => (1 : ℝ))
    have hlim1 : Tendsto (fun n => g n x) atTop (nhds (1 : ℝ)) := by
      have h := hg_lim x; rwa [hval] at h
    have : (1 : ℝ) ≤ 1 / 2 :=
      le_of_tendsto hlim1 (eventually_atTop.2 ⟨N, fun n hn => hxB n hn⟩)
    linarith

end PosteriorProcess
