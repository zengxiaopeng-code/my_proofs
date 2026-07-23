import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Approximation

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
* `concF_eq_concClosure_at` (paper's Lemma `concf-conc`): on a closed convex `K` in a locally
  convex space where `concF K q` is bounded above and upper semicontinuous, `concF K q x₀ =
  concClosure K q x₀`. The reverse inequality is the supporting-hyperplane / geometric Hahn–Banach
  step, via Mathlib's `ConvexOn.exists_affine_le_of_lt`. **Proved.**
* `concF_concaveOn`, `concF_mono`: `concF K q` is concave on `K` and monotone in `q`. **Proved.**
* `nogain_iff` (paper's main theorem `thm:nogain-delta-eps`, abstract convex-analysis core): for
  `g ≤ ĝ`, no gain at `x₀` (`concF ĝ x₀ = concF g x₀`) iff a single continuous affine map caps both
  `g` and `ĝ` on `K` and is `ε`-tight against `concF g` at `x₀`. **Proved.**
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

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The defining supremum of `concF` is bounded above by any uniform bound `M` on `q` over `K`
(each finite combination averages values `≤ M`). Ensures `concF` is real-valued and gives the
`BddAbove` needed for the `sSup` manipulations in the concavity proof and the hard direction. -/
theorem concF_bddAbove (K : Set E) (q : E → ℝ) {M : ℝ} (hM : ∀ y ∈ K, q y ≤ M) (x : E) :
    BddAbove {v | ∃ (n : ℕ) (w : Fin n → ℝ) (z : Fin n → E),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, z i ∈ K) ∧
      (∑ i, w i • z i = x) ∧ v = ∑ i, w i * q (z i)} := by
  refine ⟨M, ?_⟩
  rintro v ⟨n, w, z, hw0, hw1, hzK, hbary, rfl⟩
  calc ∑ i, w i * q (z i)
      ≤ ∑ i, w i * M := by
        apply Finset.sum_le_sum; intro i _
        exact mul_le_mul_of_nonneg_left (hM (z i) (hzK i)) (hw0 i)
    _ = M := by rw [← Finset.sum_mul, hw1, one_mul]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- Scale a nonempty bounded-above set's supremum by a nonnegative scalar under a uniform bound:
if `a * u ≤ d` for every `u ∈ S`, then `a * sSup S ≤ d`. The `a = 0` case is separate (there
`a * sSup S = 0` and any witness gives `0 ≤ d`); for `a > 0` it is `csSup_le` after dividing. -/
theorem sSup_scale_le (a : ℝ) (S : Set ℝ) (d : ℝ) (ha : 0 ≤ a)
    (hne : S.Nonempty) (h : ∀ u ∈ S, a * u ≤ d) :
    a * sSup S ≤ d := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · obtain ⟨u, hu⟩ := hne
    simpa using h u hu
  · rw [← le_div_iff₀' ha']
    apply csSup_le hne
    intro u hu
    rw [le_div_iff₀' ha']
    exact h u hu

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The finite concavification is **concave** on `K`: given two finite convex-combination witnesses
for `x` and `y`, their weighted concatenation (via `Fin.append`) is a finite convex combination for
`a • x + b • y`, so `a * concF x + b * concF y ≤ concF (a • x + b • y)`. Pure affine bookkeeping;
no topology. This is the geometric heart of the hard direction of `concf-conc`. -/
theorem concF_concaveOn (K : Set E) (hK : Convex ℝ K) (q : E → ℝ) {M : ℝ}
    (hM : ∀ y ∈ K, q y ≤ M) :
    ConcaveOn ℝ K (concF K q) := by
  refine ⟨hK, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  set c := concF K q (a • x + b • y) with hc
  have hmem : ∀ u ∈ {v | ∃ (n : ℕ) (w : Fin n → ℝ) (z : Fin n → E),
        (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, z i ∈ K) ∧
        (∑ i, w i • z i = x) ∧ v = ∑ i, w i * q (z i)},
      ∀ v ∈ {v | ∃ (n : ℕ) (w : Fin n → ℝ) (z : Fin n → E),
        (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, z i ∈ K) ∧
        (∑ i, w i • z i = y) ∧ v = ∑ i, w i * q (z i)},
      a * u + b * v ≤ c := by
    rintro u ⟨n, wx, zx, hwx0, hwx1, hzKx, hbx, rfl⟩ v ⟨m, wy, zy, hwy0, hwy1, hzKy, hby, rfl⟩
    rw [hc]
    apply le_csSup (concF_bddAbove K q hM _)
    refine ⟨n + m, Fin.append (fun i => a * wx i) (fun j => b * wy j),
      Fin.append zx zy, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact mul_nonneg ha (hwx0 i)
      · rw [Fin.append_right]; exact mul_nonneg hb (hwy0 j)
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, ← Finset.mul_sum, hwx1, hwy1, mul_one, hab]
    · intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hzKx i
      · rw [Fin.append_right]; exact hzKy j
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, mul_smul, ← Finset.smul_sum, hbx, hby]
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, mul_assoc, ← Finset.mul_sum]
  have hSxne : {v | ∃ (n : ℕ) (w : Fin n → ℝ) (z : Fin n → E),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, z i ∈ K) ∧
      (∑ i, w i • z i = x) ∧ v = ∑ i, w i * q (z i)}.Nonempty :=
    ⟨q x, 1, fun _ => 1, fun _ => x, by simp, by simp, by simp [hx], by simp, by simp⟩
  have hSyne : {v | ∃ (n : ℕ) (w : Fin n → ℝ) (z : Fin n → E),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, z i ∈ K) ∧
      (∑ i, w i • z i = y) ∧ v = ∑ i, w i * q (z i)}.Nonempty :=
    ⟨q y, 1, fun _ => 1, fun _ => y, by simp, by simp, by simp [hy], by simp, by simp⟩
  have h1 : a * concF K q x ≤ c - b * concF K q y := by
    apply sSup_scale_le a _ _ ha hSxne
    intro u hu
    have h2 : b * concF K q y ≤ c - a * u := by
      apply sSup_scale_le b _ _ hb hSyne
      intro v hv
      have := hmem u hu v hv
      linarith
    linarith
  linarith

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- Negating an upper-semicontinuous function gives a lower-semicontinuous one (on a set). Used to
feed `concF` (upper semicontinuous by hypothesis) into `exists_affine_le_of_lt`, which is stated for
lower-semicontinuous convex functions. -/
theorem lowerSemicontinuousOn_neg_of_upper {f : E → ℝ} {K : Set E}
    (h : UpperSemicontinuousOn f K) :
    LowerSemicontinuousOn (fun z => -f z) K := by
  intro x hx y hy
  have := h x hx (-y) (by linarith)
  filter_upwards [this] with x' hx'
  linarith

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- Every continuous affine majorant `f + cc ≥ q` on `K` dominates the finite concavification
pointwise on `K`: `concF K q x ≤ f x + cc`. This is the single-majorant form of the easy direction
(`concF_le_concClosure`), and gives `BddBelow` for the concave-closure infimum in `concf-conc`. -/
theorem concF_le_of_majorant (K : Set E) (q : E → ℝ) (f : E →L[ℝ] ℝ) (cc : ℝ)
    (hmaj : ∀ y ∈ K, q y ≤ f y + cc) {x : E} (hx : x ∈ K) :
    concF K q x ≤ f x + cc := by
  unfold concF
  apply csSup_le
  · exact ⟨q x, 1, fun _ => 1, fun _ => x, by simp, by simp, by simp [hx], by simp, by simp⟩
  rintro a ⟨n, w, z, hw0, hw1, hzK, hbary, rfl⟩
  calc ∑ i, w i * q (z i)
      ≤ ∑ i, w i * (f (z i) + cc) := by
        apply Finset.sum_le_sum; intro i _
        exact mul_le_mul_of_nonneg_left (hmaj (z i) (hzK i)) (hw0 i)
    _ = f x + cc := by
        rw [← hbary, map_sum]
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]
        congr 1
        apply Finset.sum_congr rfl; intro i _; rw [map_smul]; simp

/-- **Lemma `concf-conc`.** On a closed convex `K` in a locally convex space, where the finite
concavification `concF K q` is bounded above and upper semicontinuous on `K`, it agrees with the
concave closure at every point: `concF K q x₀ = concClosure K q x₀`.

`≤` is `concF_le_concClosure`. The reverse `≥` is the supporting-hyperplane step:
* `concF K q` is concave on `K` (`concF_concaveOn`), so `-concF K q` is convex; it is lower
  semicontinuous on `K` (`lowerSemicontinuousOn_neg_of_upper` from `husc`).
* For `ε > 0`, Mathlib's `ConvexOn.exists_affine_le_of_lt`
  (`Mathlib/Analysis/Convex/Approximation.lean`, geometric Hahn–Banach on the epigraph) applied to
  `-concF K q` yields a continuous affine `l + cc ≤ -concF K q` on `K` with
  `l x₀ + cc = -concF K q x₀ - ε`. Then `f := -l`, `C := -cc` is an affine majorant of `q` on `K`
  (as `q ≤ concF K q ≤ f + C`), with `f x₀ + C = concF K q x₀ + ε`, so
  `concClosure K q x₀ ≤ concF K q x₀ + ε`. Let `ε → 0`.

**Faithfulness note `[weakening]`.** The paper's Assumption 3 posits upper semicontinuity only at
the prior `S₀`; here we require it on all of `K`. This is a *stronger* hypothesis (weaker theorem)
that is satisfied in the paper's setting — `K = Δ(Θ)` is compact and the reduced-form value is upper
semicontinuous, so `concF` is upper semicontinuous on all of `Δ(Θ)`. Flagged for the blueprint. -/
theorem concF_eq_concClosure_at [LocallyConvexSpace ℝ E]
    (K : Set E) (hK : Convex ℝ K) (q : E → ℝ) {M : ℝ}
    (hM : ∀ y ∈ K, q y ≤ M) {x₀ : E} (hx₀ : x₀ ∈ K)
    (hKclosed : IsClosed K)
    (husc : UpperSemicontinuousOn (concF K q) K) :
    concF K q x₀ = concClosure K q x₀ := by
  refine le_antisymm (concF_le_concClosure K q hM hx₀) ?_
  have hbdd : BddBelow {v | ∃ (f : E →L[ℝ] ℝ) (cc : ℝ),
      (∀ y ∈ K, q y ≤ f y + cc) ∧ v = f x₀ + cc} := by
    refine ⟨concF K q x₀, ?_⟩
    rintro v ⟨f, cc, hmaj, rfl⟩
    exact concF_le_of_majorant K q f cc hmaj hx₀
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨l, cc, hle, heq⟩ := ConvexOn.exists_affine_le_of_lt (𝕜 := ℝ)
    (s := K) (φ := fun z => -concF K q z) (x := x₀) (a := -concF K q x₀ - ε)
    hx₀ (by linarith) hKclosed (lowerSemicontinuousOn_neg_of_upper husc)
    ((concF_concaveOn K hK q hM).neg)
  have hmaj : ∀ y ∈ K, q y ≤ (-l) y + (-cc) := by
    intro y hy
    have h1 := hle ⟨y, hy⟩
    simp only [Set.restrict_apply, Pi.add_apply, Function.comp_apply,
      Function.const_apply, RCLike.re_to_real] at h1
    have hqle : q y ≤ concF K q y :=
      le_csSup (concF_bddAbove K q hM y)
        ⟨1, fun _ => 1, fun _ => y, by simp, by simp, by simp [hy], by simp, by simp⟩
    simp only [neg_apply]
    linarith
  have hval : (-l) x₀ + (-cc) = concF K q x₀ + ε := by
    simp only [RCLike.re_to_real] at heq
    simp only [neg_apply]; linarith
  calc concClosure K q x₀ ≤ (-l) x₀ + (-cc) :=
        csInf_le hbdd ⟨-l, -cc, hmaj, rfl⟩
    _ = concF K q x₀ + ε := hval

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The finite concavification is **monotone** in the function: if `g ≤ ĝ` on `K`, then
`concF K g ≤ concF K ĝ` at every point of `K`. Each finite convex-combination value of `g` is
dominated termwise by the same combination of `ĝ`, which lies below `concF K ĝ`. -/
theorem concF_mono (K : Set E) (g ĝ : E → ℝ) {M : ℝ} (hĝM : ∀ y ∈ K, ĝ y ≤ M)
    (hle : ∀ y ∈ K, g y ≤ ĝ y) {x : E} (hx : x ∈ K) :
    concF K g x ≤ concF K ĝ x := by
  unfold concF
  apply csSup_le
  · exact ⟨g x, 1, fun _ => 1, fun _ => x, by simp, by simp, by simp [hx], by simp, by simp⟩
  rintro a ⟨n, w, z, hw0, hw1, hzK, hbary, rfl⟩
  have hb : (∑ i, w i * ĝ (z i)) ∈ {v | ∃ (n : ℕ) (w : Fin n → ℝ) (z : Fin n → E),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, z i ∈ K) ∧
      (∑ i, w i • z i = x) ∧ v = ∑ i, w i * ĝ (z i)} :=
    ⟨n, w, z, hw0, hw1, hzK, hbary, rfl⟩
  calc ∑ i, w i * g (z i)
      ≤ ∑ i, w i * ĝ (z i) := by
        apply Finset.sum_le_sum; intro i _
        exact mul_le_mul_of_nonneg_left (hle (z i) (hzK i)) (hw0 i)
    _ ≤ concF K ĝ x := le_csSup (concF_bddAbove K ĝ hĝM x) hb

/-- **Theorem `nogain` — abstract convex-analysis core (paper's `thm:nogain-delta-eps`).**

On a closed convex `K` in a locally convex space, with `g ≤ ĝ` on `K` (the posterior-only vs. the
richer envelope), the richer envelope yields **no gain** over `g` at `x₀` — equal finite
concavifications, `concF K ĝ x₀ = concF K g x₀` — **iff** for every `ε > 0` there is a single
continuous affine `f + c` that caps *both* `g` and `ĝ` on `K` (the paper's *posterior support* and
*richer-state cap*) while being `ε`-tight against `concF K g` at `x₀` (the paper's *tightness at the
prior*). The affine `f + c` is the shadow value `ℓ_ε(μ) = ∫ λ_ε dμ` once instantiated on `Δ(Θ)`.

This is the pure duality behind the main theorem: `⟸` is `concF_le_of_majorant` + `concF_mono`;
`⟹` is the supporting hyperplane from `concF_eq_concClosure_at` (Lemma `concf-conc`) applied to `ĝ`,
picking an affine majorant within `ε` of the concave-closure infimum. Faithful to the paper's own
proof, only the *richer* envelope `ĝ` needs regularity (`hĝM`, `huscĝ`); `g` only needs to be
bounded above (`_hgM`, so that `concF K g x₀` is a genuine real value). -/
theorem nogain_iff [LocallyConvexSpace ℝ E]
    (K : Set E) (hK : Convex ℝ K) (hKcl : IsClosed K) (g ĝ : E → ℝ) {M : ℝ}
    (_hgM : ∀ y ∈ K, g y ≤ M) (hĝM : ∀ y ∈ K, ĝ y ≤ M)
    (hle : ∀ y ∈ K, g y ≤ ĝ y) {x₀ : E} (hx₀ : x₀ ∈ K)
    (huscĝ : UpperSemicontinuousOn (concF K ĝ) K) :
    concF K ĝ x₀ = concF K g x₀ ↔
      ∀ ε > 0, ∃ (f : E →L[ℝ] ℝ) (c : ℝ),
        (∀ y ∈ K, g y ≤ f y + c) ∧ (∀ y ∈ K, ĝ y ≤ f y + c) ∧
        (f x₀ + c ≤ concF K g x₀ + ε) := by
  constructor
  · -- (⟹) no gain ⇒ dual certificate exists
    intro h ε hε
    have hcc : concF K ĝ x₀ = concClosure K ĝ x₀ :=
      concF_eq_concClosure_at K hK ĝ hĝM hx₀ hKcl huscĝ
    have hne : {v | ∃ (f : E →L[ℝ] ℝ) (c : ℝ),
        (∀ y ∈ K, ĝ y ≤ f y + c) ∧ v = f x₀ + c}.Nonempty :=
      ⟨M, (0 : E →L[ℝ] ℝ), M, fun y hy => by simpa using hĝM y hy, by simp⟩
    have hlt : concClosure K ĝ x₀ < concClosure K ĝ x₀ + ε := by linarith
    obtain ⟨v, ⟨f, c, hmaj, rfl⟩, hv⟩ := exists_lt_of_csInf_lt hne hlt
    refine ⟨f, c, ?_, hmaj, ?_⟩
    · intro y hy; exact le_trans (hle y hy) (hmaj y hy)
    · rw [← hcc] at hv; linarith
  · -- (⟸) dual certificate ⇒ no gain
    intro h
    refine le_antisymm ?_ (concF_mono K g ĝ hĝM hle hx₀)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨f, c, _, hĝmaj, htight⟩ := h ε hε
    calc concF K ĝ x₀ ≤ f x₀ + c := concF_le_of_majorant K ĝ f c hĝmaj hx₀
      _ ≤ concF K g x₀ + ε := htight
