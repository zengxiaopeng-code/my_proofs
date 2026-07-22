import MyProofs.Foundations.PosteriorProcess.Existence

/-!
# Lemma 1 (Posterior process): sufficiency (Part (i))

Part of **Lemma 1 (Posterior process)** of the paper. The verbatim statement and proof are in
`docs/paper-lemma1.md` (the single source of truth).

Part (i): the posterior kernel `S` (from `kernel_exists`) is a sufficient statistic — conditioning
`θ` on `ℱ t` and on `σ(S)` yield the same conditional distribution:
  `P[(φ ∘ θ) | ℱ t] =ᵐ[P] P[(φ ∘ θ) | σ(S)]`  for every bounded measurable `φ`.

Proof (following the paper): `F(μ) := ∫ φ dμ` is Borel measurable on `Δ(Θ)`
(`measurable_integral_bounded`, the formal content of the paper's functional monotone-class step),
so `ω ↦ ∫ φ dS(ω)` is `σ(S)`-measurable. By `kernel_exists` it equals `P[(φ ∘ θ) | ℱ t]` a.s.;
hence that conditional expectation is `σ(S)`-measurable and, by uniqueness of conditional
expectation (`condExp_condExp_of_le` + `condExp_of_stronglyMeasurable`), equals `P[(φ ∘ θ) | σ(S)]`.
-/

open MeasureTheory ProbabilityTheory

namespace PosteriorProcess

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Preorder ι] (ℱ : Filtration ι m)
variable {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ] [Nonempty Θ] (θ : Ω → Θ)

omit [StandardBorelSpace Θ] [Nonempty Θ] in
/-- Measurability of `μ ↦ ∫ φ dμ` for bounded measurable `φ` — the formal content of the paper's
functional monotone-class step. Realized through the pos/neg-part lower integrals, which are
measurable in `μ` by `measurable_lintegral`. For every probability measure this expression equals
the Bochner integral `∫ φ dμ` (see `integral_eq_lintegral_pos_part_sub_lintegral_neg_part`). -/
theorem measurable_integral_bounded {φ : Θ → ℝ} (hφ : Measurable φ) :
    Measurable (fun μ : Measure Θ =>
      (∫⁻ x, ENNReal.ofReal (φ x) ∂μ).toReal - (∫⁻ x, ENNReal.ofReal (-φ x) ∂μ).toReal) :=
  ((Measure.measurable_lintegral hφ.ennreal_ofReal).ennreal_toReal).sub
    ((Measure.measurable_lintegral hφ.neg.ennreal_ofReal).ennreal_toReal)

/-- Part (i) of Lemma 1 (Sufficiency). The posterior kernel `S` from `kernel_exists` is a
sufficient statistic: for every bounded measurable `φ`, conditioning on `ℱ t` and on `σ(S)` give
the same conditional expectation of `φ(θ)`. -/
theorem sufficiency (hθ : Measurable θ) (t : ι) :
    ∃ S : Ω → Measure Θ,
      (∀ ω, IsProbabilityMeasure (S ω)) ∧
      Measurable[ℱ t] S ∧
      ∀ φ : Θ → ℝ, Measurable φ → (∃ C, ∀ x, |φ x| ≤ C) →
        P[(φ ∘ θ) | ℱ t] =ᵐ[P] P[(φ ∘ θ) | MeasurableSpace.comap S inferInstance] := by
  obtain ⟨S, hSprob, hSmeas, hSφ⟩ := kernel_exists (P := P) ℱ θ hθ t
  refine ⟨S, hSprob, hSmeas, ?_⟩
  intro φ hφ hφb
  obtain ⟨C, hC⟩ := hφb
  have hSφ' : (fun ω => ∫ x, φ x ∂ S ω) =ᵐ[P] P[(φ ∘ θ) | ℱ t] := hSφ φ hφ ⟨C, hC⟩
  set G : MeasurableSpace Ω := MeasurableSpace.comap S inferInstance with hG
  have hGF : G ≤ ℱ t := measurable_iff_comap_le.mp hSmeas
  have hFm : (ℱ t : MeasurableSpace Ω) ≤ m := ℱ.le t
  have hGm : G ≤ m := hGF.trans hFm
  -- `g ω := ∫ φ dS ω` equals `F (S ω)` where `F` is Borel, hence `g` is `σ(S)`-measurable
  set F : Measure Θ → ℝ := fun μ =>
      (∫⁻ x, ENNReal.ofReal (φ x) ∂μ).toReal - (∫⁻ x, ENNReal.ofReal (-φ x) ∂μ).toReal with hFdef
  have hFmeas : Measurable F := measurable_integral_bounded hφ
  have hFS : ∀ ω, F (S ω) = ∫ x, φ x ∂ S ω := by
    intro ω
    haveI := hSprob ω
    have hφint : Integrable φ (S ω) := by
      refine ⟨hφ.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := C) ?_⟩
      exact Filter.Eventually.of_forall fun x => (Real.norm_eq_abs _).le.trans (hC x)
    exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hφint).symm
  have hg_meas : StronglyMeasurable[G] (fun ω => ∫ x, φ x ∂ S ω) := by
    have hgF : (fun ω => ∫ x, φ x ∂ S ω) = fun ω => F (S ω) := funext fun ω => (hFS ω).symm
    rw [hgF]
    exact (hFmeas.comp (comap_measurable S)).stronglyMeasurable
  have hg_int : Integrable (fun ω => ∫ x, φ x ∂ S ω) P :=
    (integrable_congr hSφ').mpr integrable_condExp
  -- assemble via uniqueness of conditional expectation
  have hAB : P[P[(φ ∘ θ) | ℱ t] | G] =ᵐ[P] P[(φ ∘ θ) | G] := condExp_condExp_of_le hGF hFm
  have h1 : P[P[(φ ∘ θ) | ℱ t] | G] =ᵐ[P] P[(fun ω => ∫ x, φ x ∂ S ω) | G] :=
    condExp_congr_ae hSφ'.symm
  have h2 : P[(fun ω => ∫ x, φ x ∂ S ω) | G] = (fun ω => ∫ x, φ x ∂ S ω) :=
    condExp_of_stronglyMeasurable hGm hg_meas hg_int
  have h2' : P[(fun ω => ∫ x, φ x ∂ S ω) | G] =ᵐ[P] P[(φ ∘ θ) | ℱ t] := by rw [h2]; exact hSφ'
  exact (((hAB.symm.trans h1).trans h2').symm)

end PosteriorProcess
