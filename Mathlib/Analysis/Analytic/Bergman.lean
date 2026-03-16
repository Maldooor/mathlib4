module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Measure.OpenPos

open MeasureTheory
open Manifold
open scoped ENNReal

public noncomputable section

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

namespace Bergman

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

variable [Fact (1 ≤ p)] [μ.IsOpenPosMeasure]

instance instNormedAddCommGroup : NormedAddCommGroup (Bergman I μ E' p) where
  norm f := (eLpNorm f p μ).toReal
  dist_self := by simp
  dist_comm f g := by
    simp only [coe_add, coe_neg]
    rw [← eLpNorm_neg]
    simp
  dist_triangle f g h := by
    have {f : Bergman I μ E' p} := eLpNorm_neq_top _ _ _ _ f
    rw [← ENNReal.toReal_add this this,
      ENNReal.toReal_le_toReal this <| ENNReal.add_ne_top.mpr ⟨this, this⟩]
    simpa using eLpNorm_add_le (aeStronglyMeasurable _ _ _ _ (-f + g))
      (aeStronglyMeasurable _ _ _ _ (-g + h)) (Fact.out : 1 ≤ p)
  eq_of_dist_eq_zero := by
    intro f g hfg
    refine (Bergman.eq _ _ _ _) <| (Continuous.ae_eq_iff_eq μ f.continuous g.continuous).mp ?_
    rw [@ae_eq_comm, ← sub_ae_eq_zero, ← neg_add_eq_sub]
    have := by simpa using eLpNorm_neq_top I μ E' p (-f + g)
    have h := by simpa using aeStronglyMeasurable I μ E' p (-f + g)
    have hp : p ≠ 0 := by
      simp [← pos_iff_ne_zero, lt_of_lt_of_le zero_lt_one, (Fact.out : 1 ≤ p)]
    simpa [ENNReal.toReal_eq_zero_iff, this] using (eLpNorm_eq_zero_iff h hp).mp <|
      by simpa [ENNReal.toReal_eq_zero_iff, this] using hfg

lemma norm_def (f : Bergman I μ E' p) : ‖f‖ = (eLpNorm f p μ).toReal := rfl

instance instNormedSpace : NormedSpace 𝕜 (Bergman I μ E' p) where
  mul_smul _ _ _ := Bergman.eq _ _ _ _ <| by simp [mul_smul]
  one_smul _ := Bergman.eq _ _ _ _ <| by simp
  smul_zero _ := Bergman.eq _ _ _ _ <| by simp
  smul_add _ _ _ := Bergman.eq _ _ _ _ <| by simp
  add_smul _ _ _ := Bergman.eq _ _ _ _ <| by simp [add_smul]
  zero_smul _ := Bergman.eq _ _ _ _ <| by simp
  norm_smul_le x f := by simp [norm_def, eLpNorm_const_smul]





end Bergman
