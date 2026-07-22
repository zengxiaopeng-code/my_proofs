import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Finite concavification vs. the concave closure (Lemma `concf-conc`)

Abstract convex-analysis core behind the paper's belief-space representation. The paper works on
`Δ(Θ)`, but the statement is a general fact about a bounded-above function on a convex set `K` in a
real topological vector space, so we formalize it there and instantiate to `Δ(Θ)` separately.

Two envelopes of `q : E → ℝ`:

* `concF K q` — the **finite concavification**: the supremum of `∑ wᵢ q(zᵢ)` over finite convex
  combinations `∑ wᵢ zᵢ = x` with `zᵢ ∈ K` (the paper's finite Bayes-plausible splits).
* `concClosure K q` — the **concave closure**: the infimum of `f x + c` over continuous affine
  majorants `f + c ≥ q` on `K`.

## Main results

* `concF_le_concClosure`: `concF ≤ concClosure` pointwise on `K` (the easy direction; a pure affine
  Jensen argument, no topology). **Proved.**
* `concF_eq_concClosure_at` (paper's Lemma `concf-conc`): at a point `x₀` where `concF K q` is
  real-valued and upper semicontinuous, `concF K q x₀ = concClosure K q x₀`. The reverse
  inequality is the supporting-hyperplane / geometric Hahn–Banach step and is **not yet filled in**.
-/

open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The **finite concavification** of `q` on `K`: supremum of `∑ wᵢ q(zᵢ)` over finite convex
combinations `∑ wᵢ • zᵢ = x` with weights `wᵢ ≥ 0`, `∑ wᵢ = 1`, and points `zᵢ ∈ K`. -/
noncomputable def concF (K : Set E) (q : E → ℝ) (x : E) : ℝ :=
  sSup {v | ∃ (n : ℕ) (w : Fin n → ℝ) (z : Fin n → E),
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, z i ∈ K) ∧
    (∑ i, w i • z i = x) ∧ v = ∑ i, w i * q (z i)}

/-- The **concave closure** of `q` on `K`: infimum of `f x + c` over continuous affine majorants
`y ↦ f y + c` of `q` on `K`. -/
noncomputable def concClosure (K : Set E) (q : E → ℝ) (x : E) : ℝ :=
  sInf {v | ∃ (f : E →L[ℝ] ℝ) (c : ℝ), (∀ y ∈ K, q y ≤ f y + c) ∧ v = f x + c}

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- Easy direction of Lemma `concf-conc`: `concF ≤ concClosure` on `K`. Every affine majorant
dominates every finite convex combination (Jensen), so the sup of combinations is below the inf of
majorants. No topology is used. -/
theorem concF_le_concClosure (K : Set E) (q : E → ℝ) {M : ℝ} (hM : ∀ y ∈ K, q y ≤ M)
    {x : E} (hx : x ∈ K) :
    concF K q x ≤ concClosure K q x := by
  unfold concF concClosure
  apply csSup_le
  · exact ⟨q x, 1, fun _ => 1, fun _ => x, by simp, by simp, by simp [hx], by simp, by simp⟩
  rintro a ⟨n, w, z, hw0, hw1, hzK, hbary, rfl⟩
  apply le_csInf
  · refine ⟨M, (0 : E →L[ℝ] ℝ), M, ?_, ?_⟩
    · intro y hy; simpa using hM y hy
    · simp
  rintro b ⟨f, c, hmaj, rfl⟩
  calc ∑ i, w i * q (z i)
      ≤ ∑ i, w i * (f (z i) + c) := by
        apply Finset.sum_le_sum; intro i _
        exact mul_le_mul_of_nonneg_left (hmaj (z i) (hzK i)) (hw0 i)
    _ = f x + c := by
        rw [← hbary, map_sum]
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]
        congr 1
        apply Finset.sum_congr rfl; intro i _; rw [map_smul]; simp

/-- **Lemma `concf-conc`.** At a point `x₀ ∈ K` where the finite concavification `concF K q` is
real-valued and upper semicontinuous, it agrees with the concave closure:
`concF K q x₀ = concClosure K q x₀`.

`≤` is `concF_le_concClosure`. The reverse `≥` is the supporting-hyperplane step: `concF K q` is
concave, so upper semicontinuity at `x₀` yields, for every `ε > 0`, a continuous affine `f + c`
with `concF K q ≤ f + c` on `K` and `f x₀ + c ≤ concF K q x₀ + ε` (geometric Hahn–Banach applied to
the hypograph); such `f + c` is an affine majorant of `q`, giving `concClosure K q x₀ ≤
concF K q x₀ + ε`. Not yet filled in. -/
theorem concF_eq_concClosure_at (K : Set E) (hK : Convex ℝ K) (q : E → ℝ) {M : ℝ}
    (hM : ∀ y ∈ K, q y ≤ M) {x₀ : E} (hx₀ : x₀ ∈ K)
    (husc : UpperSemicontinuousAt (concF K q) x₀) :
    concF K q x₀ = concClosure K q x₀ := by
  sorry
