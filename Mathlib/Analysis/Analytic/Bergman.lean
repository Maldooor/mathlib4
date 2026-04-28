module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

open MeasureTheory
open Manifold
open scoped ENNReal

public noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]
variable (μ : Measure M)
variable (E' : Type*) [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable (p : ℝ≥0∞)

structure Bergman where
  toFun : M → E'
  memLp : MemLp toFun p μ
  contMDiff : ContMDiff I (modelWithCornersSelf 𝕜 E') ⊤ toFun

end
namespace Bergman

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]
variable (μ : Measure M)
variable (E' : Type*) [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable (p : ℝ≥0∞)

instance instFunLike : FunLike (Bergman I μ E' p) M E' where
  coe := toFun
  coe_injective' f := by cases f; congr!

@[ext]
lemma ext {f g : Bergman I μ E' p} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

lemma eq {f g : Bergman I μ E' p} (h : ⇑f = ⇑g) : f = g := ext I μ E' p (congrFun h)

instance instZero : Zero (Bergman I μ E' p) where
  zero := ⟨0, by simp, contMDiff_zero⟩

instance instAdd : Add (Bergman I μ E' p) where
  add f g := ⟨⇑f + ⇑g, f.2.add g.2, f.3.add g.3⟩

instance instNeg : Neg (Bergman I μ E' p) where
  neg f := ⟨-⇑f, f.2.neg, f.3.neg⟩

instance instSub : Sub (Bergman I μ E' p) where
  sub f g := ⟨⇑f - ⇑g, f.2.sub g.2, f.3.sub g.3⟩

instance instSMul : SMul 𝕜 (Bergman I μ E' p) where
  smul z f := ⟨z • ⇑f, f.2.const_smul z, f.3.const_smul z⟩

instance instSMulNat : SMul ℕ (Bergman I μ E' p) where
  smul n f := ⟨(n : 𝕜) • ⇑f, f.2.const_smul (n : 𝕜), f.3.const_smul (n : 𝕜)⟩

instance instSMulInt : SMul ℤ (Bergman I μ E' p) where
  smul n f := ⟨(n : 𝕜) • ⇑f, f.2.const_smul (n : 𝕜), f.3.const_smul (n : 𝕜)⟩

@[simp]
lemma coe_zero : ⇑(0 : (Bergman I μ E' p)) = 0 := rfl

@[simp]
lemma coe_add (f g : (Bergman I μ E' p)) : ⇑(f + g) = f + g := rfl

@[simp]
lemma coe_neg (f : (Bergman I μ E' p)) : ⇑(-f) = -f := rfl

@[simp]
lemma coe_sub (f g : (Bergman I μ E' p)) : ⇑(f - g) = f - g := rfl

@[simp]
lemma coe_smul (z : 𝕜) (f : (Bergman I μ E' p)) : ⇑(z • f) = z • f := rfl

@[simp]
lemma coe_nat_smul (n : ℕ) (f : (Bergman I μ E' p)) : ⇑(n • f) = (n : 𝕜) • f := rfl

@[simp]
lemma coe_int_smul (n : ℤ) (f : (Bergman I μ E' p)) : ⇑(n • f) = (n : 𝕜) • f := rfl

instance instAddCommGroup : AddCommGroup (Bergman I μ E' p) :=
  DFunLike.coe_injective.addCommGroup (fun (f : (Bergman I μ E' p)) ↦ ⇑f)
  (by simp) (by simp) (by simp) (by simp)
  (by simp [Nat.cast_smul_eq_nsmul]) (by simp [Int.cast_smul_eq_zsmul])

@[simp]
lemma aeStronglyMeasurable (f : (Bergman I μ E' p)) : AEStronglyMeasurable f μ := f.memLp.1

lemma eLpNorm_lt_top (f : Bergman I μ E' p) : eLpNorm f p μ < ∞ := f.memLp.2

lemma eLpNorm_neq_top (f : Bergman I μ E' p) : eLpNorm f p μ ≠ ∞ :=
  LT.lt.ne_top <| eLpNorm_lt_top _ _ _ _ f

lemma continuous (f : Bergman I μ E' p) : Continuous f := f.contMDiff.continuous

instance instNorm : Norm (Bergman I μ E' p) where
  norm f := (eLpNorm f p μ).toReal

lemma norm_def (f : Bergman I μ E' p) : ‖f‖ = (eLpNorm f p μ).toReal := rfl

lemma norm_nonneg (f : Bergman I μ E' p) : 0 ≤ ‖f‖ := by
  simp [norm_def]

instance instNormedAddCommGroup [Fact (1 ≤ p)] [μ.IsOpenPosMeasure] :
    NormedAddCommGroup (Bergman I μ E' p) where
  norm f := ‖f‖
  dist_self := by simp [norm_def]
  dist_comm f g := by
    simp only [coe_add, coe_neg, norm_def]
    rw [← eLpNorm_neg]
    simp
  dist_triangle f g h := by
    simp only [norm_def]
    have {f : Bergman I μ E' p} := eLpNorm_neq_top _ _ _ _ f
    rw [← ENNReal.toReal_add this this,
      ENNReal.toReal_le_toReal this <| ENNReal.add_ne_top.mpr ⟨this, this⟩]
    simpa using eLpNorm_add_le (aeStronglyMeasurable _ _ _ _ (-f + g))
      (aeStronglyMeasurable _ _ _ _ (-g + h)) Fact.out
  eq_of_dist_eq_zero := by
    intro f g hfg
    refine (Bergman.eq _ _ _ _) <| (Continuous.ae_eq_iff_eq μ f.continuous g.continuous).mp ?_
    rw [ae_eq_comm, ← sub_ae_eq_zero, ← neg_add_eq_sub]
    have := by simpa using eLpNorm_neq_top _ _ _ _ (-f + g)
    have h := aeStronglyMeasurable _ _ _ _ (-f + g)
    have hp : p ≠ 0 := by simp [← pos_iff_ne_zero, lt_of_lt_of_le zero_lt_one, Fact.out]
    simpa using (eLpNorm_eq_zero_iff h hp).mp <|
      by simpa [norm_def, ENNReal.toReal_eq_zero_iff, this] using hfg

instance instNormedSpace [Fact (1 ≤ p)] [μ.IsOpenPosMeasure] :
    NormedSpace 𝕜 (Bergman I μ E' p) where
  mul_smul _ _ _ := Bergman.eq _ _ _ _ <| by simp [mul_smul]
  one_smul _ := Bergman.eq _ _ _ _ <| by simp
  smul_zero _ := Bergman.eq _ _ _ _ <| by simp
  smul_add _ _ _ := Bergman.eq _ _ _ _ <| by simp
  add_smul _ _ _ := Bergman.eq _ _ _ _ <| by simp [add_smul]
  zero_smul _ := Bergman.eq _ _ _ _ <| by simp
  norm_smul_le x f := by simp [norm_def, eLpNorm_const_smul]

end

section

open Topology OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [instInnerProductSpace : InnerProductSpace ℂ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]
variable (μ : Measure M)
variable (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable (p : ℝ≥0∞) [FiniteDimensional ℂ E]

variable [FiniteDimensional ℝ E] --should be unnecessary

instance : InnerProductSpace ℝ E := .complexToReal

variable [MeasurableSpace E] [BorelSpace E] --Should also be unnecessary?

variable (x : M)

--show IsOpenPosMeasure?
--maybe this should be phrased in terms of filters instead, basically as a limit as the size of the
--  neighbourhood decreases..
def LocalMeasureAt (x : M) (u : Set M) : Measure E := μ.map (I ∘ (chartAt H x))
  |>.restrict <| I.symm ⁻¹' ((chartAt H x)'' u)

--should be open neighbourhoods
def DominatesLebesgue : Prop := ∀ x : M, ∃ u : TopologicalSpace.OpenNhdsOf x,
  volume.restrict (I.symm ⁻¹' ((chartAt H x)'' u)) ≪ LocalMeasureAt I μ x u

theorem dominatesLebesgue_subset (u v : TopologicalSpace.OpenNhdsOf x) (hsubst: u ≤ v)
    (h : volume.restrict (I.symm ⁻¹' ((chartAt H x)'' u)) ≪ LocalMeasureAt I μ x u) :
    volume.restrict (I.symm ⁻¹' ((chartAt H x)'' v)) ≪ LocalMeasureAt I μ x v := by
  simp [LocalMeasureAt]
  exact Measure.restrict_mono


variable [SFinite μ] --why do we need this again? Maybe we dont?

#check IsOpen.preimage
#check ContinuousOn.mono
#check Set.inter_subset_left
#check OpenPartialHomeomorph.isOpen_image_symm_of_subset_target

example (a b : Set M) : a ∩ b ⊆ a := Set.inter_subset_left

open Classical in
theorem supltnorm (f : Bergman I μ E' p) {K : Set M} (hK : IsCompact K)
    (h : DominatesLebesgue I μ) : ∃ C : ℝ, ∀ z ∈ K, ‖f z‖ ≤ C * ‖f‖ := by
  let V : K → Set M := fun x ↦
    (h x).choose ∩ ((chartAt H (x : M)).symm '' (((chartAt H (x : M)).target) ∩
    I ⁻¹' (Metric.ball (I <| (chartAt H (x : M)) (x : M)) 1)))
  have V_open (x : K) : IsOpen <| V x := by
    refine IsOpen.inter ?_ ?_
    · exact TopologicalSpace.OpenNhdsOf.isOpen _
    · refine isOpen_image_symm_of_subset_target _ ?_ Set.inter_subset_left
      simp [IsOpen.inter, (chartAt H _).open_target, IsOpen.preimage, I.continuous]
  have hVx : ∀ x, (hx : x ∈ K) → x ∈ V ⟨x, hx⟩ := by
    refine fun x xin ↦ ⟨TopologicalSpace.OpenNhdsOf.mem _, ⟨((chartAt H x) x), by simp⟩⟩
  have hVsubst (x) : V x ⊆ (chartAt H (x : M)).source := by
    simp [V]
    grw [Set.inter_subset_right, Set.inter_subset_left, symm_image_target_eq_source]
  obtain ⟨ι, coverK⟩ := hK.elim_finite_subcover V (V_open)
    (fun x xin ↦ Set.mem_iUnion.mpr ⟨⟨x, xin⟩, hVx x xin⟩)
  suffices h : ∀ i ∈ ι, ∃ C, ∀ z ∈ V i, ‖f z‖ ≤ C * ‖f‖ from ?_
  · refine (isEmpty_or_nonempty ι).elim (fun h1 ↦ by simp_all) (fun hι ↦ ?_)
    let Cfun := fun i ↦ if hi : i ∈ ι then (h i hi).choose else 0
    have (i) (hi : i ∈ ι) : ∀ z ∈ V i, ‖f z‖ ≤ (Cfun i) * ‖f‖ := by
      simpa [Cfun, hi] using (h i hi).choose_spec
    let C := ι.sup' (Finset.nonempty_coe_sort.mp hι) Cfun
    refine ⟨C, fun z zin ↦ ?_⟩
    obtain ⟨i, hi, zin⟩ := by simpa only [Set.mem_iUnion] using Set.mem_iUnion.mp <| coverK zin
    have := this i hi z zin
    have hc : Cfun i ≤ C := by simp only [C, Finset.le_sup' Cfun, hi]
    grw [this, hc]
    simp [norm_nonneg]
  intro x hx
  let D := I.symm ⁻¹' ((chartAt H (x : M)) '' V x)
  let w := I ((chartAt H (x : M)) x)
  have hD₁ : IsOpen D := by
    simp [D]
    refine Continuous.isOpen_preimage I.continuous_symm _ ?_
    exact (chartAt H ↑x).isOpen_image_of_subset_source (V_open x) (hVsubst x)
  have hD₂ : w ∈ D := ⟨x, by simp [hVx, w]⟩
  have hD₃ : volume.restrict D ≪ LocalMeasureAt I μ x (V x) := by
    simp only [D, V]
    have := (h x).choose_spec
    set v₁ := (h x).choose

    have : volume.restrict D ≤ volume.restrict
      (I.symm ⁻¹' ((chartAt H (x : M)) '' (h x).choose)) := by grind [Measure.restrict_mono]
    have := this.absolutelyContinuous
    have : LocalMeasureAt I μ x (h x).choose ≪ LocalMeasureAt I μ x (V x) := by sorry

  use 1
  intro z ⟨zin, hz⟩




  -- Cover K using atlas, more precicely neigbourhoods of each point smaller than
  --    1. (chartAt H x).source
  --    2. the neighbourhood required for DominatesLebesgue
  --    3. the preimage of the the unit ball of E under the chart --Whole unit ball is too big
  -- Take finite subcover by compactness
  -- Argue that we only need to prove statement for one set in cover
  -- Transfer to E using chart, (induce measure, show IsOpenPosMeasure --necessary?)
  -- Need to show that f is analyticOn when transfered to E
  -- Cover compact set by polydiscs
  -- Split integral up
  -- Use mean value theorem to estimate


end Bergman
