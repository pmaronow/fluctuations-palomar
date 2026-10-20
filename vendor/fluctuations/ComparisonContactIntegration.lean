module

public import VariableEndpointPhysicalRegularity
public import ComparisonContactDerivative
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 1000000

theorem inverseConstraint_density_ae_bound
    {k M : ℝ→ℝ} (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints 0 0 k M) :
    ∀ᵐ r,r∈Icc (0:ℝ) 1→‖deriv α.val.val r‖ ≤ M 1 := by
  have hLip := inverseIntegralConstraints_lipschitz hm hM α.property
  filter_upwards [volume.ae_ne (0:ℝ),volume.ae_ne (1:ℝ)] with r hr0 hr1 hr
  have hn : Icc (0:ℝ) 1∈𝓝 r := Icc_mem_nhds
    (lt_of_le_of_ne hr.1 hr0.symm) (lt_of_le_of_ne hr.2 hr1)
  exact norm_deriv_le_of_lipschitzOn hn hLip

theorem comparison_contact_weighted_integral_le
    {p S B : ℝ→ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hp : MonotoneOn p (Ioc (0:ℝ) 1))
    (hpb : ∀r∈Ioc (0:ℝ) 1,p r∈Icc (0:ℝ) (1-κ))
    (hS : MonotoneOn S (Icc (0:ℝ) 1))
    (hB : MonotoneOn B (Ioc (0:ℝ) 1))
    (hSb : ∀r∈Ioc (0:ℝ) 1,0 ≤ S r)
    (hBb : ∀r∈Ioc (0:ℝ) 1,(S r)^2 ≤ B r)
    {k M : ℝ→ℝ} (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints 0 0 k M)
    {a z : ℝ} (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1)
    (hAC : AbsolutelyContinuousOnInterval S a z)
    (A : Set ℝ) (hAm : MeasurableSet A) (hA : A⊆Icc a z)
    (hcontact : ∀ᵐ r,r∈A→comparisonBracket (p r) r (S r) (B r)=0) :
    IntegrableOn (fun r=>deriv α.val.val r*deriv S r) A ∧
    (∫r in A,deriv α.val.val r*deriv S r) ≤ (3/κ)*(∫r in A,deriv α.val.val r) := by
  have hA01 : A⊆Icc (0:ℝ) 1 := hA.trans (Icc_subset_Icc ha.le hz)
  have hAi : A⊆Ioc (0:ℝ) 1 := fun r hr=>⟨ha.trans_le (hA hr).1,(hA01 hr).2⟩
  have hiS : IntegrableOn (deriv S) A :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le haz).mp hAC.intervalIntegrable_deriv).mono_set hA
  have hαmono : MonotoneOn α.val.val (uIcc (0:ℝ) 1) :=
    α.val.property.2.monotoneOn _
  have hiα : IntegrableOn (deriv α.val.val) A :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hαmono.intervalIntegrable_deriv).mono_set hA01
  have hdα := inverseConstraint_density_ae_bound hm hM α
  have hαbound : ∀ᵐ r∂volume.restrict A,‖deriv α.val.val r‖ ≤ M 1 := by
    filter_upwards [ae_restrict_mem hAm,ae_restrict_of_ae hdα] with r hr hd
    exact hd (hA01 hr)
  have hiProd : IntegrableOn (fun r=>deriv α.val.val r*deriv S r) A :=
    hiS.bdd_mul (stronglyMeasurable_deriv _).aestronglyMeasurable hαbound
  have hd := comparison_contact_ae_deriv_le hκ hp hpb hS hB hSb hBb
  refine ⟨hiProd,?_⟩
  have hb : ∀ᵐ r,r∈A→deriv α.val.val r*deriv S r ≤ (3/κ)*deriv α.val.val r := by
    filter_upwards [hd,hcontact] with r hdr hcr hr
    have hs := hdr (hAi hr) (hcr hr)
    have hαn : 0 ≤ deriv α.val.val r := α.val.property.2.deriv_nonneg
    nlinarith
  calc
    (∫r in A,deriv α.val.val r*deriv S r) ≤ ∫r in A,(3/κ)*deriv α.val.val r :=
      setIntegral_mono_on_ae hiProd (hiα.const_mul _) hAm hb
    _=(3/κ)*(∫r in A,deriv α.val.val r) := integral_const_mul _ _

theorem actual_finiteHistory_overlap_increment_eq_integral
    {c : ℝ} {k M : ℝ→ℝ} (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (T ε s : ℝ) (ts : List ComparisonHistoryTerm)
    (hb : MonotoneOn (historyMatrixClock T ε s ts) (Icc (0:ℝ) 1))
    (hh : MonotoneOn (historyFieldClock ts) (Icc (0:ℝ) 1))
    (hh0 : 0 ≤ historyFieldClock ts 0)
    {d lam : ℝ} (hd : d≠0) (hlam : 0 ≤ lam)
    (hlb : lam ≤ historyMatrixClock T ε s ts 0)
    (α : inverseIntegralConstraints 0 0 k M) {a z : ℝ}
    (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1)
    (hbranch : α.val.val z < s ∨ s ≤ α.val.val a) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(historyMatrixClock T ε s ts u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(historyFieldClock ts u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
    S z-S a=∫r in a..z,deriv S r := by
  exact (actual_finiteHistory_radius_overlap_absolutelyContinuous hc hk hkc hm hM n dphys e
    T ε s ts hb hh hh0 hd hlam hlb α ha haz hz hbranch).integral_deriv_eq_sub.symm

end OAI.SKFluctuations.LaplaceWindowFormalization
