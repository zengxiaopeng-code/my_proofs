import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Belief space `Δ(Θ)` as a convex subset of a topological vector space

The abstract convex-analysis results in `Foundations/Concavification.lean` (`concf-conc`,
`nogain_iff`, …) live on a convex set `K` in a real locally convex space `E`. To instantiate them
on the paper's belief space `Δ(Θ) = ProbabilityMeasure Θ`, we embed `Δ(Θ)` into the real
topological vector space

  `E := WeakDual ℝ C(Θ, ℝ)`   (the dual of `C(Θ,ℝ)` with the weak-* topology)

via `μ ↦ (λ ↦ ∫ λ dμ)`. The shadow value `ℓ(μ) = ∫ λ dμ` of the paper is then an evaluation
functional on `E`.

## Stages

* **Stage 1 — the ambient space.** `E` carries every instance the concavification toolkit needs
  (`AddCommGroup`, `Module ℝ`, `TopologicalSpace`, `IsTopologicalAddGroup`, `ContinuousSMul ℝ`,
  `LocallyConvexSpace ℝ`) plus `T2Space` (used to show the embedded `Δ(Θ)` is closed). All but local
  convexity are `inferInstance`; local convexity is supplied by hand (see the instance below).
* **Stage 2 — the embedding.** `embCLM μ : C(Θ,ℝ) →L[ℝ] ℝ` is integration against `μ`; `emb μ` is
  its image in `E` under `StrongDual.toWeakDual`. `emb_apply` records the defining pairing
  `emb μ λ = ∫ λ dμ`. **(this commit)**

Later stages: continuity, injectivity and affineness of `emb`, and convexity/closedness of its
range `K := Set.range emb`, so that `concf-conc`/`nogain_iff` instantiate on `Δ(Θ)`.
-/

open MeasureTheory

namespace BeliefSpace

variable {Θ : Type*} [TopologicalSpace Θ] [CompactSpace Θ]

/-- The ambient real topological vector space: the weak-* dual of `C(Θ, ℝ)`. The belief space
`Δ(Θ)` embeds into it as a convex (compact, hence closed) subset. -/
abbrev E (Θ : Type*) [TopologicalSpace Θ] [CompactSpace Θ] := WeakDual ℝ C(Θ, ℝ)

/-- `WeakDual ℝ C(Θ,ℝ)` is locally convex. Built directly from the seminorm family of the weak
topology (`weakBilin_withSeminorms.toLocallyConvexSpace`), bypassing instance search for
`WeakBilin.locallyConvexSpace`: with base field `𝕜 = ℝ` that instance's `[Module ℝ E]` binder
overlaps its `[Module 𝕜 E]` binder, and instance resolution cannot reconcile the two `Module ℝ`
paths, so we supply the term explicitly. -/
noncomputable instance : LocallyConvexSpace ℝ (E Θ) :=
  (topDualPairing ℝ C(Θ, ℝ)).weakBilin_withSeminorms.toLocallyConvexSpace

-- Stage 1 sanity checks: `E` has exactly the instances the concavification toolkit assumes.
noncomputable example : AddCommGroup (E Θ) := inferInstance
noncomputable example : Module ℝ (E Θ) := inferInstance
noncomputable example : TopologicalSpace (E Θ) := inferInstance
example : IsTopologicalAddGroup (E Θ) := inferInstance
example : ContinuousSMul ℝ (E Θ) := inferInstance
example : LocallyConvexSpace ℝ (E Θ) := inferInstance
example : T2Space (E Θ) := inferInstance

section Embedding

variable [MeasurableSpace Θ] [BorelSpace Θ]

/-- Continuous functions on a compact space are integrable against any finite measure. -/
theorem integrable_contMap (μ : Measure Θ) [IsFiniteMeasure μ] (f : C(Θ, ℝ)) :
    Integrable (fun x => f x) μ := by
  have h := BoundedContinuousFunction.integrable μ (BoundedContinuousFunction.mkOfCompact f)
  rwa [show ⇑(BoundedContinuousFunction.mkOfCompact f) = fun x => f x from rfl] at h

/-- Integration against a finite measure, as a continuous linear functional `C(Θ,ℝ) →L[ℝ] ℝ`:
`f ↦ ∫ f dμ`, with operator norm at most `μ(univ)`. -/
noncomputable def embCLM (μ : Measure Θ) [IsFiniteMeasure μ] : C(Θ, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add (integrable_contMap μ f) (integrable_contMap μ g)
      map_smul' := fun c f => by simpa using integral_smul c (fun x => f x) }
    (μ.real Set.univ)
    (fun f => by
      have h := norm_integral_le_of_norm_le_const (μ := μ)
        (ae_of_all μ (fun x => f.norm_coe_le_norm x))
      rwa [mul_comm] at h)

/-- The belief-space embedding `Δ(Θ) ↪ E = WeakDual ℝ C(Θ,ℝ)`, `μ ↦ (λ ↦ ∫ λ dμ)`. -/
noncomputable def emb (μ : ProbabilityMeasure Θ) : E Θ :=
  StrongDual.toWeakDual (embCLM (μ : Measure Θ))

/-- The defining pairing: `emb μ` applied to `λ ∈ C(Θ,ℝ)` is `∫ λ dμ`. This is the paper's shadow
value `ℓ(μ) = ∫ λ dμ` read off the embedded belief. -/
theorem emb_apply (μ : ProbabilityMeasure Θ) (f : C(Θ, ℝ)) :
    emb μ f = ∫ x, f x ∂(μ : Measure Θ) := rfl

/-- Evaluation at `l ∈ C(Θ,ℝ)`, packaged as a continuous linear functional on `E`. On an embedded
belief `emb μ` it returns the paper's shadow value `∫ l dμ` (`evalCLM_emb`). This is the map
`C(Θ) → (E →L[ℝ] ℝ)` witnessing that every `∫ l d·` is a continuous affine functional on `Δ(Θ)`. -/
noncomputable def evalCLM (l : C(Θ, ℝ)) : E Θ →L[ℝ] ℝ where
  toFun x := x l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := WeakDual.eval_continuous l

@[simp] theorem evalCLM_emb (l : C(Θ, ℝ)) (μ : ProbabilityMeasure Θ) :
    evalCLM l (emb μ) = ∫ x, l x ∂(μ : Measure Θ) := emb_apply μ l

/-- The embedding `emb : Δ(Θ) → E` is continuous (weak convergence of beliefs ⟹ weak-*
convergence of the embedded functionals). By `WeakDual.continuous_of_continuous_eval` it suffices
that each evaluation `μ ↦ ∫ λ dμ` is continuous, which is
`FiniteMeasure.continuous_integral_continuousMap` composed with `μ ↦ μ.toFiniteMeasure`. -/
theorem emb_continuous : Continuous (emb : ProbabilityMeasure Θ → E Θ) := by
  refine WeakDual.continuous_of_continuous_eval (fun f => ?_)
  exact (FiniteMeasure.continuous_integral_continuousMap f).comp
    ProbabilityMeasure.toFiniteMeasure_continuous

/-- Convex combination `a·μ + b·ν` of two probability measures, as a plain measure. -/
noncomputable def mixMeasure (a b : ℝ) (μ ν : ProbabilityMeasure Θ) : Measure Θ :=
  ENNReal.ofReal a • (μ : Measure Θ) + ENNReal.ofReal b • (ν : Measure Θ)

omit [TopologicalSpace Θ] [CompactSpace Θ] [BorelSpace Θ] in
/-- A convex combination (`a,b ≥ 0`, `a+b = 1`) of probability measures is a probability measure. -/
theorem isProbMix (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (μ ν : ProbabilityMeasure Θ) : IsProbabilityMeasure (mixMeasure a b μ ν) := by
  constructor
  simp only [mixMeasure, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]

/-- Convex combination of two beliefs, as a probability measure. Its image under `emb` is the
corresponding convex combination in `E` (`emb_mix`). -/
noncomputable def mix (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (μ ν : ProbabilityMeasure Θ) : ProbabilityMeasure Θ :=
  ⟨mixMeasure a b μ ν, isProbMix a b ha hb hab μ ν⟩

/-- `emb` is affine: it carries a convex combination of beliefs to the convex combination of their
images in `E`. Pointwise this is linearity of the integral in the measure. -/
theorem emb_mix (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (μ ν : ProbabilityMeasure Θ) :
    emb (mix a b ha hb hab μ ν) = a • emb μ + b • emb ν := by
  refine DFunLike.ext _ _ (fun f => ?_)
  have hμ : Integrable (fun x => f x) (ENNReal.ofReal a • (μ : Measure Θ)) :=
    (integrable_contMap (μ : Measure Θ) f).smul_measure ENNReal.ofReal_ne_top
  have hν : Integrable (fun x => f x) (ENNReal.ofReal b • (ν : Measure Θ)) :=
    (integrable_contMap (ν : Measure Θ) f).smul_measure ENNReal.ofReal_ne_top
  change ∫ x, f x ∂(mixMeasure a b μ ν)
      = a * ∫ x, f x ∂(μ : Measure Θ) + b * ∫ x, f x ∂(ν : Measure Θ)
  rw [mixMeasure, integral_add_measure hμ hν, integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb, smul_eq_mul, smul_eq_mul]

/-- The range `K := Set.range emb` of the belief-space embedding is **convex**. -/
theorem convex_range_emb : Convex ℝ (Set.range (emb : ProbabilityMeasure Θ → E Θ)) := by
  rintro _ ⟨μ, rfl⟩ _ ⟨ν, rfl⟩ a b ha hb hab
  exact ⟨mix a b ha hb hab μ ν, emb_mix a b ha hb hab μ ν⟩

/-- Finite convex combination `∑ᵢ wᵢ · νᵢ` of beliefs, as a plain measure. -/
noncomputable def mixFinMeasure {n : ℕ} (w : Fin n → ℝ) (ν : Fin n → ProbabilityMeasure Θ) :
    Measure Θ :=
  ∑ i, ENNReal.ofReal (w i) • (ν i : Measure Θ)

omit [TopologicalSpace Θ] [CompactSpace Θ] [BorelSpace Θ] in
/-- A finite convex combination of probability measures is a probability measure. -/
theorem isProbMixFin {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (ν : Fin n → ProbabilityMeasure Θ) : IsProbabilityMeasure (mixFinMeasure w ν) := by
  constructor
  simp only [mixFinMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hw1, ENNReal.ofReal_one]

/-- Finite convex combination of beliefs, as a belief — the paper's finite **Bayes-plausible
split** `∑ᵢ wᵢ · νᵢ`. -/
noncomputable def mixFin {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (ν : Fin n → ProbabilityMeasure Θ) : ProbabilityMeasure Θ :=
  ⟨mixFinMeasure w ν, isProbMixFin w hw hw1 ν⟩

/-- **`emb` is affine on finite convex combinations**: it carries a finite Bayes-plausible split of
beliefs to the corresponding convex combination in `E`. This makes the finite convex-combination
splits used by `concF` on `K` correspond exactly to the paper's Bayes-plausible splits on `Δ(Θ)`.

The proof routes the evaluation through `evalCLM`, which turns `WeakDual` application into a
continuous-linear-map application so that `map_sum`/`map_smul` apply. -/
theorem emb_mixFin {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (ν : Fin n → ProbabilityMeasure Θ) :
    emb (mixFin w hw hw1 ν) = ∑ i, w i • emb (ν i) := by
  refine DFunLike.ext _ _ (fun l => ?_)
  have hint : ∀ i ∈ Finset.univ,
      Integrable (fun x => l x) (ENNReal.ofReal (w i) • (ν i : Measure Θ)) :=
    fun i _ => (integrable_contMap (ν i : Measure Θ) l).smul_measure ENNReal.ofReal_ne_top
  change ∫ x, l x ∂(mixFinMeasure w ν) = _
  rw [mixFinMeasure, integral_finsetSum_measure hint]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal (hw _), smul_eq_mul]
  rw [show ((∑ i, w i • emb (ν i) : E Θ)) l = evalCLM l (∑ i, w i • emb (ν i)) from rfl,
    map_sum]
  simp [map_smul, evalCLM_emb]

-- From here we ask `Θ` to be metrizable (true on the paper's compact Polish `Θ`): this gives both
-- `HasOuterApproxClosed Θ` (for injectivity) and `T2Space Θ` (for compactness of `Δ(Θ)`).
variable [TopologicalSpace.MetrizableSpace Θ]

/-- The embedding `emb` is injective: continuous functions separate probability measures on a
compact metrizable space. If `emb μ = emb ν` then `∫ f dμ = ∫ f dν` for every `f ∈ C(Θ,ℝ)`,
which forces `μ = ν` by `FiniteMeasure.ext_of_forall_integral_eq`. -/
theorem emb_injective : Function.Injective (emb : ProbabilityMeasure Θ → E Θ) := by
  intro μ ν h
  have hf : ∀ f : C(Θ, ℝ), ∫ x, f x ∂(μ : Measure Θ) = ∫ x, f x ∂(ν : Measure Θ) := by
    intro f
    have hfun := DFunLike.congr_fun h f
    rwa [emb_apply, emb_apply] at hfun
  have hFM : μ.toFiniteMeasure = ν.toFiniteMeasure := by
    refine FiniteMeasure.ext_of_forall_integral_eq (fun g => ?_)
    simpa using hf g.toContinuousMap
  apply ProbabilityMeasure.toMeasure_injective
  simpa using congrArg (fun η : FiniteMeasure Θ => (η : Measure Θ)) hFM

/-- The range `K := Set.range emb` is **closed**: `Δ(Θ)` is compact (Prokhorov, since `Θ` is
compact), `emb` is continuous, so the image is compact, hence closed in the Hausdorff space `E`. -/
theorem isClosed_range_emb : IsClosed (Set.range (emb : ProbabilityMeasure Θ → E Θ)) := by
  have hc : IsCompact (Set.range (emb : ProbabilityMeasure Θ → E Θ)) :=
    isCompact_range emb_continuous
  exact hc.isClosed

end Embedding

end BeliefSpace
