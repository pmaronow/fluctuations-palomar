module

public import ComparisonShiftedNativeBandCarrier
public import ComparisonCapSideVarianceComposition

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
namespace ShiftedNativeBandModel
private theorem boundedWeight_integrableOn_interval
    {a z : ℝ} (w : ℝ → ℝ) (hw : Measurable w) {B : ℝ}
    (hwb : ∀r,‖w r‖ ≤ B) : IntegrableOn w (Ioo a z) := by
  have hfinite : volume (Ioo a z)≠⊤ := ne_top_of_le_ne_top
    (by simp : volume (Icc a z)≠⊤) (measure_mono Ioo_subset_Icc_self)
  have hone : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioo a z) := integrableOn_const hfinite
  simpa only [IntegrableOn,mul_one] using hone.bdd_mul
    hw.stronglyMeasurable.aestronglyMeasurable.restrict (ae_of_all _ hwb)

theorem radiusWeight_integrableOn
    (m : ShiftedNativeBandModel)
    {a z : ℝ} (ha : m.rmin < a) (hz : z ≤ 1)
    (S : Set ℝ) (hS : MeasurableSet S) (hsub : S ⊆ Ioo a z)
    (w : ℝ → ℝ) (hw : Measurable w) {B : ℝ}
    (hwb : ∀r, ‖w r‖ ≤ B) :
    IntegrableOn (fun r => deriv m.alpha.val.val r*w r) S := by
  have hfMeas : AEStronglyMeasurable (fun r => deriv m.alpha.val.val r*w r) volume :=
    (stronglyMeasurable_deriv m.alpha.val.val).aestronglyMeasurable.mul
      hw.stronglyMeasurable.aestronglyMeasurable
  have hbound r (hr : r∈S) : ‖deriv m.alpha.val.val r*w r‖ ≤ m.M 1*B := by
    have hrr := hsub hr
    have hr01 : r∈Ioo m.rmin 1 := ⟨ha.trans hrr.1, hrr.2.trans_le hz⟩
    have hd : ‖deriv m.alpha.val.val r‖ ≤ m.M 1 :=
      norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hr01.1 hr01.2)
        (inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property)
    rw [norm_mul]
    exact mul_le_mul hd (hwb r) (norm_nonneg _) m.hM
  have hSf : volume S≠⊤ := ne_top_of_le_ne_top
    (by simp : volume (Icc a z)≠⊤)
    (measure_mono (hsub.trans Ioo_subset_Icc_self))
  have hOne : IntegrableOn (fun _ : ℝ => (1:ℝ)) S := integrableOn_const hSf
  simpa only [IntegrableOn, mul_one] using hOne.bdd_mul hfMeas.restrict
    ((ae_restrict_mem hS).mono (fun r hr => hbound r hr))

theorem inverse_weight_L1_le
    (m : ShiftedNativeBandModel)
    {a z : ℝ} (ha : m.rmin < a) (hz : z ≤ 1)
    (w v : ℝ → ℝ) (hw : Measurable w) (hv : Measurable v)
    {B : ℝ} (hwb : ∀r,‖w r‖ ≤ B) (hvb : ∀r,‖v r‖ ≤ B) :
    (∫r in Ioo a z,|deriv m.alpha.val.val r*v r-deriv m.alpha.val.val r*w r|) ≤
      m.M 1*(∫r in Ioo a z,|v r-w r|) := by
  have hwI := boundedWeight_integrableOn_interval w hw hwb (a:=a) (z:=z)
  have hvI := boundedWeight_integrableOn_interval v hv hvb (a:=a) (z:=z)
  have hfwI := m.radiusWeight_integrableOn ha hz
    (Ioo a z) measurableSet_Ioo (Subset.refl _) w hw hwb
  have hfvI := m.radiusWeight_integrableOn ha hz
    (Ioo a z) measurableSet_Ioo (Subset.refl _) v hv hvb
  have hpoint r (hr : r∈Ioo a z) :
      |deriv m.alpha.val.val r*v r-deriv m.alpha.val.val r*w r| ≤ m.M 1*|v r-w r| := by
    have hr01 : r∈Ioo m.rmin 1 := ⟨ha.trans hr.1,hr.2.trans_le hz⟩
    have hd : ‖deriv m.alpha.val.val r‖ ≤ m.M 1 :=
      norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hr01.1 hr01.2)
        (inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property)
    rw [←mul_sub,abs_mul]
    exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hd) (abs_nonneg _)
  have hh := setIntegral_mono_on (hfvI.sub hfwI).abs
    ((hvI.sub hwI).abs.const_mul (m.M 1)) measurableSet_Ioo hpoint
  simpa only [Pi.sub_apply,integral_const_mul] using hh

theorem inverse_weight_L1_tendsto
    (m : ShiftedNativeBandModel)
    {a z : ℝ} (ha : m.rmin < a) (hz : z ≤ 1)
    (w : ℝ → ℝ) (hw : Measurable w) (moving : ℕ → ℝ → ℝ)
    (hmove : ∀j,Measurable (moving j)) {B : ℝ}
    (hwb : ∀r,‖w r‖ ≤ B) (hmb : ∀j r,‖moving j r‖ ≤ B)
    (hL1 : Tendsto (fun j => ∫r in Ioo a z,|moving j r-w r|) atTop (𝓝 0)) :
    Tendsto (fun j => ∫r in Ioo a z,
      |deriv m.alpha.val.val r*moving j r-deriv m.alpha.val.val r*w r|) atTop (𝓝 0) := by
  have ht : Tendsto (fun j => m.M 1*(∫r in Ioo a z,|moving j r-w r|)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hL1.const_mul (m.M 1)
  exact squeeze_zero (fun j => integral_nonneg (fun _ => abs_nonneg _))
    (fun j => m.inverse_weight_L1_le ha hz w (moving j) hw (hmove j) hwb (hmb j)) ht

theorem fixedCapContactWeight_integral {ι : Type*} [Fintype ι]
    (m : ShiftedNativeBandModel)
    {ag zg : ℝ} (hag : m.rmin<ag) (hzg : zg≤1)
    (a z weight : ι→ℝ) (hga : ∀i,ag≤a i) (hgz : ∀i,z i≤zg)
    (A : Set ℝ) (hA : MeasurableSet A) (hAsub : A⊆Ioo ag zg)
    (w : ℝ→ℝ) (hw : Measurable w) {W : ℝ} (hwb : ∀r,‖w r‖≤W)
    (μ : Measure ℝ) (hμ : μ≤volume) :
    Integrable (fun r=>deriv m.alpha.val.val r*fixedCapContactWeight a z weight A w r) μ ∧
    (∫r,deriv m.alpha.val.val r*fixedCapContactWeight a z weight A w r∂μ)=
      (∑i,weight i*(∫r in Ioo (a i) (z i),deriv m.alpha.val.val r∂μ))+
      (∫r in A,deriv m.alpha.val.val r*w r∂μ) := by
  have hiCap i := m.radiusWeight_integrableOn hag hzg
    (Ioo (a i) (z i)) measurableSet_Ioo
    (fun r hr=>⟨(hga i).trans_lt hr.1,hr.2.trans_le (hgz i)⟩)
    (fun _=>weight i) measurable_const (fun _=>le_rfl : ∀r : ℝ,‖weight i‖≤‖weight i‖)
  have hiContact := m.radiusWeight_integrableOn hag hzg
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
