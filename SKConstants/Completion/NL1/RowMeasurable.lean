module

public import SKConstants.Completion.NL1.RowVariance
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace SKConstants.Completion.NL1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint LC5 LGram N13A LM5

theorem measurable_gramSchmidt {S : Type*} [MeasurableSpace S] {n k : ℕ}
    (T : S → Fin k → EuclideanSpace ℝ (Fin n)) (hT : ∀ j, Measurable (fun s => T s j))
    (j : Fin k) : Measurable (fun s => gramSchmidt ℝ (T s) j) := by
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have he : (fun s => gramSchmidt ℝ (T s) j) =
        fun s => T s j - ∑ i ∈ Finset.Iio j,
          (ℝ ∙ gramSchmidt ℝ (T s) i).starProjection (T s j) :=
      funext fun s => gramSchmidt_def ℝ (T s) j
    rw [he]
    refine (hT j).sub (Finset.measurable_sum _ (fun i hi => ?_))
    have hi := ih i (Finset.mem_Iio.mp hi)
    simp only [Submodule.starProjection_singleton]
    convert (((hi.inner (hT j)).div (hi.norm.pow_const 2)).smul hi) using 1

theorem measurable_gramSchmidtNormed {S : Type*} [MeasurableSpace S] {n k : ℕ}
    (T : S → Fin k → EuclideanSpace ℝ (Fin n)) (hT : ∀ j, Measurable (fun s => T s j))
    (j : Fin k) : Measurable (fun s => gramSchmidtNormed ℝ (T s) j) := by
  have h := measurable_gramSchmidt T hT j
  exact h.norm.inv.smul h

theorem measurable_arrayCoefficients (p : Parameters) (n : ℕ) :
    Measurable (arrayCoefficients (p := p) (n := n)) := by
  let T := fun z : RowArray p n => fun j : Fin (coarseCount p n) =>
    (Real.sqrt (n : ℝ))⁻¹ • WithLp.toLp 2 (fun i => arrayT z i j)
  have hT (j : Fin (coarseCount p n)) : Measurable (fun z => T z j) := by
    unfold T arrayT
    fun_prop
  have hx : Measurable (fun z : RowArray p n =>
      (Real.sqrt (n : ℝ))⁻¹ • WithLp.toLp 2 (arrayX z)) := by
    unfold arrayX
    fun_prop
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro j
  exact (measurable_gramSchmidtNormed T hT j).inner hx

theorem measurable_discardedVariance (p : Parameters) (n : ℕ) :
    Measurable (discardedVariance (p := p) (n := n)) := by
  have h := measurable_arrayCoefficients p n
  unfold discardedVariance
  exact (((Finset.measurable_sum _ (fun j _ =>
    (((EuclideanSpace.proj j).measurable.comp h).pow_const 4))).add
      ((measurable_const.sub (h.norm.pow_const 2)).pow_const 2)).div_const _)

end SKConstants.Completion.NL1
