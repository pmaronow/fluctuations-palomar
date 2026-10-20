module

public import ComparisonNativeMasterBandConstruction

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

namespace NativeBandFrame

def UnitOscillation {m : NativeBandModel} {s : NativeBandRefinement m}
    {bins : ℕ} {cut w : ℝ} (f : NativeBandFrame m s bins cut w) (j : ℕ) (D : ℝ) : Prop :=
  ∀i∈f.A j,∀t∈f.A j,f.unit0 j i=f.unit0 j t→
    physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) t.val ≤
      physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val+D

theorem reverse_pair_le_of_unit_oscillation {m : NativeBandModel} {s : NativeBandRefinement m}
    {bins : ℕ} {cut w : ℝ} (f : NativeBandFrame m s bins cut w) (j : ℕ)
    {D : ℝ} (hD : 0 ≤ D) (hunit : f.UnitOscillation j D)
    (i t : Fin ((s.steps j).length+1)) (hi : i∈f.A j) (ht : t∈f.A j)
    (hit : i ≤ t) (heq : f.unit0 j i=f.unit0 j t) :
    physicalSideMovementMoment (m.n+1) (s.steps j) (m.q 0) i.val t.val ≤ m.reverse D := by
  have hs : OrderedSteps 0 (s.steps j) := sampleClockSteps_ordered m.q (s.as j) (s.ho j)
  have hmono := physicalPathSecondMoment_mono (m.n+1) (s.steps j) hs (m.q 0) hit (by omega)
  have hbase : 0 ≤ physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) t.val-
      physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val := sub_nonneg.mpr hmono
  have hinc : physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) t.val-
      physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val ≤ D := by linarith [hunit i hi t ht heq]
  have hlR : (2:ℝ)< m.l := by exact_mod_cast m.hl
  have hp : 0 ≤ ((m.l:ℝ)-2)/((m.l:ℝ)-1) := div_nonneg (by linarith) (by linarith)
  have hpow := Real.rpow_le_rpow hbase hinc hp
  have hraw := physical_movement_fourth_le_raw_interpolation (m.n+1) m.l m.hl
    (s.steps j) hs (m.q 0) m.hxs hit (by omega)
  let Q := physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
    (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id
  have hQ0 : 0 ≤ Q := zero_le_one.trans (physicalRawRatio_one_le _ _ _ _ _ _ _ _)
  have hmass0 : 0 ≤ m.xs+physicalCutMass 0 (s.steps j) t.val :=
    add_nonneg m.hxs.le (physicalCutMass_mem _ hs _).1
  have hmass := pow_le_pow_left₀ hmass0 (f.hmassUpper j t ht) m.l
  have hQ := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0:ℝ)≤2) hQ0)
    (mul_le_mul_of_nonneg_left (f.rawUpper j) (by norm_num : (0:ℝ)≤2)) (2*m.l)
  have hlarge := mul_le_mul hQ hmass (pow_nonneg hmass0 _) (pow_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) (zero_le_one.trans m.hQ)) _)
  have hbaseNonneg : 0 ≤ (2*Q)^(2*m.l)*(m.xs+physicalCutMass 0 (s.steps j) t.val)^m.l := by positivity
  have hlargepow := Real.rpow_le_rpow hbaseNonneg hlarge
    (div_nonneg zero_le_one (by linarith : 0 ≤ (m.l:ℝ)-1))
  exact hraw.trans (mul_le_mul hpow hlargepow (Real.rpow_nonneg hbaseNonneg _)
    (Real.rpow_nonneg hD _))

theorem finite_budget_of_unit_oscillation {m : NativeBandModel} {s : NativeBandRefinement m}
    {bins : ℕ} {cut w : ℝ} (f : NativeBandFrame m s bins cut w)
    (hcut : 0 < cut) (hw : 0 < w) (hRange : m.Q^2*m.y ≤ (bins:ℝ)*w)
    (j : ℕ) {D : ℝ} (hD : 0 ≤ D) (hunit : f.UnitOscillation j D) :
    f.defect j ≤ nativeConditionalLedgerBudget f.B (f.totalWidth j) cut (w+D)
      (f.sideFilled j) (f.unionGeometry.filled j) (m.reverse D) m.Lside := by
  have hs : OrderedSteps 0 (s.steps j) := sampleClockSteps_ordered m.q (s.as j) (s.ho j)
  have hsub (bb : Fin f.B) : (f.side bb).selected j⊆f.A j := by
    intro i hi;rw [f.hbin j bb] at hi;exact (Finset.mem_filter.mp hi).1
  have hQ0 : 0 ≤ physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id :=
    zero_le_one.trans (physicalRawRatio_one_le _ _ _ _ _ _ _ _)
  have hRangeActual : (physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id)^2*m.y ≤ (bins:ℝ)*w :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hQ0 (f.rawUpper j) _) m.hy.le).trans hRange
  have hheight := physical_native_unit_bins_profile_diameter (m.n+1) m.l (by have hl := m.hl;omega)
    (s.steps j) hs (m.q 0) (f.A j) (f.unit0 j) m.hxs hw (f.hmassUpper j) hRangeActual
    (fun i hi t ht heq=>hunit i hi t ht heq.symm)
  have hS : ∀bb,∀i∈(f.side bb).selected j,∀t∈(f.side bb).selected j,
      |physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) t.val-
        physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val| ≤ w+D := by
    intro bb i hi t ht
    rw [f.hbin j bb] at hi ht
    exact hheight (f.label bb) hi ht
  let T := f.unionGeometry.filled j
  let v := f.totalWidth j
  let tauC := T/v
  have hv : 0 < v := f.totalWidth_pos hcut j
  have htrace0 : (∑i,(∑bb,physicalSelectedCellMass (s.steps j) ((f.side bb).selected j) i)*
      actualCutCovarianceEnergy (m.n+1) (s.steps j) (m.q 0) i.val) ≤ T := by
    exact comparisonNativeSelectedUnionCovarianceEnergy_le_integral m.hc m.hk m.hkc m.hm m.hM
      m.n m.dphys m.e m.d m.lam m.b m.h m.alpha (s.as j) (s.ho j) (s.he j) (s.hm j) (s.hm0 j)
      (fun bb=>(f.side bb).selected j) (f.bin_disjoint j) m.hcut m.hcut1
      (fun bb=>(f.side bb).hleft j)
  have hT0 : 0 ≤ T := (Finset.sum_nonneg (fun i _=>mul_nonneg
    (Finset.sum_nonneg (fun bb _=>physicalSelectedCellMass_nonneg (s.steps j) hs ((f.side bb).selected j) i))
    (actualCutCovarianceEnergy_nonneg (m.n+1) (s.steps j) hs (m.q 0) i.val))).trans htrace0
  have htau : 0 ≤ tauC := div_nonneg hT0 hv.le
  have hvt : v*tauC=T := by dsimp [tauC];field_simp [hv.ne']
  have htrace : (∑i,(∑bb,physicalSelectedCellMass (s.steps j) ((f.side bb).selected j) i)*
      actualCutCovarianceEnergy (m.n+1) (s.steps j) (m.q 0) i.val) ≤ v*tauC := by rw [hvt];exact htrace0
  have hvariance : (∑bb,actualBinSideVariance (m.n+1) ((f.side bb).K j) (s.steps j) (m.q 0)
      ((f.side bb).selected j) ((f.side bb).unit j) ((f.side bb).x j) cut ((f.side bb).widths j)) ≤ f.sideFilled j := by
    apply Finset.sum_le_sum
    intro bb _
    exact physical_actual_bin_variance_le_native_integral m.hc m.hk m.hkc m.hm m.hM
      m.n m.dphys m.e m.d m.lam m.b m.h m.alpha (s.as j) (s.ho j) (s.he j) (s.hm j) (s.hm0 j)
      ((f.side bb).selected j) ((f.side bb).unit j) ((f.side bb).x j)
      ((f.side bb).hstart j) ((f.side bb).hend j) hcut ((f.side bb).hwidths j) ((f.side bb).hx j)
      m.hcut m.hcut1 ((f.side bb).hleft j)
  have hreverseL : ∀bb,∀i t:Fin ((s.steps j).length+1),i.val < t.val→
      fineCoupling (physicalSelectedCellMass (s.steps j) ((f.side bb).selected j)) ((f.side bb).unit j)
        (fun u v=>coarseLeft ((f.side bb).x j) 0 cut ((f.side bb).widths j-cut) u v) i t≠0→
      physicalSideMovementMoment (m.n+1) (s.steps j) (m.q 0) i.val t.val ≤ m.reverse D := by
    intro bb i t hit hP
    obtain ⟨hi,ht⟩ := physicalFineCoupling_mem_selected _ _ _ _ hP
    have heq := nonzero_fineCoarseLeft_reverse_same_unit _ _ _ (f.horder j bb)
      ((f.side bb).x j) ((f.side bb).hx j) 0 cut ((f.side bb).widths j-cut) hi ht hit hP
    have heq0 := (f.hclass0 j i (hsub bb hi) t (hsub bb ht)).mpr ((f.hclass j bb i hi t ht).mp heq)
    exact f.reverse_pair_le_of_unit_oscillation j hD hunit i t (hsub bb hi) (hsub bb ht) hit.le heq0
  have hreverseR : ∀bb,∀i t:Fin ((s.steps j).length+1),t.val < i.val→
      fineCoupling (physicalSelectedCellMass (s.steps j) ((f.side bb).selected j)) ((f.side bb).unit j)
        (fun u v=>coarseRight ((f.side bb).x j) ((f.side bb).widths j) cut ((f.side bb).widths j-cut) u v) i t≠0→
      physicalSideMovementMoment (m.n+1) (s.steps j) (m.q 0) i.val t.val ≤ m.reverse D := by
    intro bb i t hti hP
    obtain ⟨hi,ht⟩ := physicalFineCoupling_mem_selected _ _ _ _ hP
    have heq := nonzero_fineCoarseRight_reverse_same_unit _ _ _ (f.horder j bb)
      ((f.side bb).x j) ((f.side bb).hx j) ((f.side bb).widths j) cut ((f.side bb).widths j-cut) hi ht hti hP
    have heq0 := (f.hclass0 j t (hsub bb ht) i (hsub bb hi)).mpr ((f.hclass j bb i hi t ht).mp heq).symm
    rw [physicalSideMovementMoment_comm (m.n+1) (s.steps j) (m.q 0) i.val t.val]
    exact f.reverse_pair_le_of_unit_oscillation j hD hunit t i (hsub bb ht) (hsub bb hi) hti.le heq0
  have hn := physical_selected_bins_defect_le_variance_budget (m.n+1) f.B (s.steps j) hs (m.q 0)
    (fun bb=>(f.side bb).K j) (fun bb=>(f.side bb).selected j) (fun bb=>(f.side bb).unit j)
    (fun bb=>(f.side bb).x j) (fun bb=>(f.side bb).widths j)
    (fun bb=>(f.side bb).hstart j) (fun bb=>(f.side bb).hend j) hcut (fun bb=>(f.side bb).hwidths j)
    (fun bb=>(f.side bb).hx j) (fun bb=>(f.side bb).hmass j) (add_nonneg hw.le hD) htau
    (m.reverse_nonneg hD) m.hLside (f.hsideLog j) rfl hS hvariance htrace hreverseL hreverseR
  dsimp only at hn
  have hvt' : (∑bb,(f.side bb).widths j)*tauC=T := hvt
  rw [actualBinsVarianceBudget_native_expansion,hvt'] at hn
  have heq : (∑i,(∑bb,physicalSelectedCellMass (s.steps j) ((f.side bb).selected j) i)*
      actualCutReplicaDefect (m.n+1) (s.steps j) (m.q 0) i.val
        (physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val))=f.defect j := by
    apply Finset.sum_congr rfl
    intro i _
    rw [selectedCellMass_sum_eq_biUnion _ _ (f.bin_disjoint j)]
  rw [heq] at hn
  exact hn

end NativeBandFrame
end OAI.SKFluctuations.LaplaceWindowFormalization
