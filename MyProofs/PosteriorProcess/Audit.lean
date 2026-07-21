import MyProofs.PosteriorProcess

/-!
# Verification audit

`#print axioms` lists the full set of axioms a theorem ultimately depends on. Criterion:

* Only `propext`, `Classical.choice`, `Quot.sound` appear
  → these are Lean/Mathlib's standard trusted axioms; the proof is complete and verified by
    the kernel.
* If `sorryAx` appears
  → there is a `sorry` somewhere on the dependency chain; not yet verified.

This is the machine-checkable criterion for "did Lean really prove it" — it cannot be faked.
-/

open PosteriorProcess

-- All four parts of Lemma 1 — each should depend only on
-- `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`).

-- Existence + kernel property
#print axioms kernel_exists
-- (i) Sufficiency
#print axioms sufficiency
#print axioms measurable_integral_bounded
-- (ii) Doob–Dynkin + Δ(Θ) standard Borel (a former Mathlib gap, proved from scratch)
#print axioms factorization
#print axioms deltaTheta_polishSpace
#print axioms deltaTheta_borelSpace
#print axioms deltaTheta_standardBorel
#print axioms factorization_posterior
-- (iii) Martingale property
#print axioms testfun_martingale
