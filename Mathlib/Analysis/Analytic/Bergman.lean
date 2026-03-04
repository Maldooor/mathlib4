module

public import Mathlib.Analysis.InnerProductSpace.Reproducing
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

open MeasureTheory

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]
variable [BorelSpace M] (μ : Measure M)
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable (f : M → E') (hf : ContMDiff I (modelWithCornersSelf 𝕜 E') ⊤ f)
variable (h : AEStronglyMeasurable f μ)

example : Continuous f :=  hf.continuous
