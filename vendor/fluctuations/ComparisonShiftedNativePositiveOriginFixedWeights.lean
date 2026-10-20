module

public import ComparisonShiftedNativePositiveOriginMovingWeights

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
namespace ShiftedNativeBandModel
theorem fixedCapContactWeight_integral_positive_origin {ι : Type*} [Fintype ι]
    (m : ShiftedNativeBandModel)
    {ag zg : ℝ} (hag : m.rmin≤ag) (hzg : zg≤1)
    (a z weight : ι→ℝ) (hga : ∀i,ag≤a i) (hgz : ∀i,z i≤zg)
    (A : Set ℝ) (hA : MeasurableSet A) (hAsub : A⊆Ioo ag zg)
    (w : ℝ→ℝ) (hw : Measurable w) {W : ℝ} (hwb : ∀r,‖w r‖≤W)
    (μ : Measure ℝ) (hμ : μ≤volume) :
    Integrable (fun r=>deriv m.alpha.val.val r*fixedCapContactWeight a z weight A w r) μ ∧
    (∫r,deriv m.alpha.val.val r*fixedCapContactWeight a z weight A w r∂μ)=
      (∑i,weight i*(∫r in Ioo (a i) (z i),deriv m.alpha.val.val r∂μ))+
      (∫r in A,deriv m.alpha.val.val r*w r∂μ) := by
  have hiCap i := m.radiusWeight_integrableOn_positive_origin hag hzg
    (Ioo (a i) (z i)) measurableSet_Ioo
    (fun r hr=>⟨(hga i).trans_lt hr.1,hr.2.trans_le (hgz i)⟩)
    (fun _=>weight i) measurable_const (fun _=>le_rfl : ∀r : ℝ,‖weight i‖≤‖weight i‖)
  have hiContact := m.radiusWeight_integrableOn_positive_origin hag hzg
    A hA hAsub w hw hwb
  have heCap i : (fun r=>deriv m.alpha.val.val r*(Ioo (a i) (z i)).indicator (fun _=>weight i) r)=
      (Ioo (a i) (z i)).indicator (fun r=>deriv m.alpha.val.val r*weight i) := by
    funext r
    by_cases hr : r∈Ioo (a i) (z i) <;> simp [hr]
  have heContact : (fun r=>deriv m.alpha.val.val r*A.indicator w r)=
      A.indicator (fun r=>deriv m.alpha.val.val r*w r) := by
    funext r
    by_cases hr : r∈A <;> simp [hr]
  have hIc i : Integrable (fun r=>deriv m.alpha.val.val r*
      (Ioo (a i) (z i)).indicator (fun _=>weight i) r) μ := by
    rw [heCap]
    exact ((hiCap i).integrable_indicator measurableSet_Ioo).mono_measure hμ
  have hIA : Integrable (fun r=>deriv m.alpha.val.val r*A.indicator w r) μ := by
    rw [heContact]
    exact (hiContact.integrable_indicator hA).mono_measure hμ
  have heq : (fun r=>deriv m.alpha.val.val r*fixedCapContactWeight a z weight A w r)=
      (fun r=>∑i,deriv m.alpha.val.val r*(Ioo (a i) (z i)).indicator (fun _=>weight i) r)+
      (fun r=>deriv m.alpha.val.val r*A.indicator w r) := by
    funext r
    simp only [fixedCapContactWeight,mul_add,Finset.mul_sum,Pi.add_apply]
  rw [heq]
  constructor
  · exact (integrable_finsetSum _ (fun i _=>hIc i)).add hIA
  · change (∫r,(∑i,deriv m.alpha.val.val r*(Ioo (a i) (z i)).indicator
      (fun _=>weight i) r)+deriv m.alpha.val.val r*A.indicator w r∂μ)=_
    rw [integral_add (integrable_finsetSum _ (fun i _=>hIc i)) hIA,
      integral_finsetSum _ (fun i _=>hIc i),heContact,integral_indicator hA]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [heCap,integral_indicator measurableSet_Ioo,integral_mul_const,mul_comm]

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
