module

public import ComparisonNativeOuterComparableTrace

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators

theorem actual_native_outer_comparable_moving_column_trace_eventually
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : NativeBroadSliceGeometry m)
    {cl cu Az z0 : ℝ}
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hz0 : z0∈Icc (0:ℝ) 1)
    (hzxs : z0 ≤ Az*m.xs) (htravel : nativeCapTravel m ≤ m.xs)
    (hregular : ∀r∈Icc z0 1,cl*r ≤ m.alpha.val.val r ∧ m.alpha.val.val r ≤ cu*r)
    (houter : 2*cu*(Az+1)*m.xs ≤ m.alpha.val.val g.capZ)
    (moving : ℕ→ℝ→ℝ) (hmoveMeas : ∀j,Measurable (moving j))
    {B weight : ℝ} (hB : 0 ≤ B) (hweight : 0 ≤ weight)
    (hmoveBound : ∀j,∀r,‖moving j r‖ ≤ B)
    (hsupport : ∀j,∀ᵐ r,r∉Ioo m.ag m.zg → moving j r=0)
    (hcolumns : Tendsto (fun j=>∫r in Ioo m.ag m.zg,
      |moving j r-(Ioo g.a g.b).indicator (fun _=>weight) r|) atTop (𝓝 0))
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ j in atTop,
      (∫r,deriv m.alpha.val.val r*moving j r∂s.mu j) ≤
        (27*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2/m.P)*weight*
          (∫r in Ioo g.a g.b,deriv m.alpha.val.val r)+eps := by
  let domain:=Ioo m.ag m.zg
  let A:=Ioo g.a g.b
  let fixed:=A.indicator (fun _=>weight)
  let bound:=B+weight+1
  have hAsub : A⊆domain:=fun r hr=>⟨g.haGroup.trans_lt hr.1,hr.2.trans_le g.hbGroup⟩
  have hfixedMeas : Measurable fixed:=measurable_const.indicator measurableSet_Ioo
  have hfixedBound r : ‖fixed r‖ ≤ bound:=by
    by_cases hr : r∈A
    · simp only [fixed,indicator_of_mem hr,Real.norm_eq_abs,abs_of_nonneg hweight]
      dsimp [bound];linarith
    · simp only [fixed,indicator_of_notMem hr,norm_zero]
      dsimp [bound];positivity
  have hmoveBound' j r : ‖moving j r‖ ≤ bound:=
    (hmoveBound j r).trans (by dsimp [bound];linarith)
  have Herror:=comparison_inverse_weight_L1_tendsto m.hm m.hM m.alpha m.hag m.hzg
    fixed hfixedMeas moving hmoveMeas hfixedBound hmoveBound' hcolumns
  have hfixedI : IntegrableOn (fun r=>deriv m.alpha.val.val r*fixed r) domain:=
    comparison_radiusWeight_integrableOn m.hm m.hM m.alpha m.hag m.hzg domain measurableSet_Ioo
      (Subset.refl _) fixed hfixedMeas hfixedBound
  have hmoveI j : IntegrableOn (fun r=>deriv m.alpha.val.val r*moving j r) domain:=
    comparison_radiusWeight_integrableOn m.hm m.hM m.alpha m.hag m.hzg domain measurableSet_Ioo
      (Subset.refl _) (moving j) (hmoveMeas j) (hmoveBound' j)
  have Hfixed:=actual_native_outer_comparable_slice_weighted_trace_eventually m s g
    hcl hcu hAz hz0 hzxs htravel hregular houter (fun _=>weight) measurable_const hweight
    (fun _ _=>⟨hweight,le_rfl⟩) (show 0 < eps/2 by positivity)
  have Hsmall:=(tendsto_order.mp Herror).2 (eps/2) (by positivity)
  filter_upwards [Hfixed,Hsmall] with j hj hje
  have hdom : s.mu j ≤ volume:=
    (comparisonPhysicalRadiusMeasure_le_compact_volume m.hc m.hk m.hkc m.hm m.hM
      m.n m.dphys m.e m.d m.lam m.b m.h m.alpha (s.as j) (s.ho j)).trans Measure.restrict_le_self
  have Hmove:=dominated_setIntegral_difference_le domain domain (Subset.refl _) (s.mu j) hdom
    (fun r=>deriv m.alpha.val.val r*fixed r) (fun r=>deriv m.alpha.val.val r*moving j r)
    hfixedI (hmoveI j)
  have HfixedGlobal : (∫r in domain,deriv m.alpha.val.val r*fixed r∂s.mu j)=
      (∫r in A,deriv m.alpha.val.val r*weight∂s.mu j):=by
    have HE : (fun r=>deriv m.alpha.val.val r*fixed r)=
      A.indicator (fun r=>deriv m.alpha.val.val r*weight):=by
      funext r;by_cases hr : r∈A <;> simp [fixed,hr]
    rw [HE,setIntegral_indicator measurableSet_Ioo,inter_eq_right.mpr hAsub]
  have HmoveGlobal : (∫r in domain,deriv m.alpha.val.val r*moving j r∂s.mu j)=
      (∫r,deriv m.alpha.val.val r*moving j r∂s.mu j):=by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [ae_mono hdom (hsupport j)] with r hr hrd
    rw [hr hrd,mul_zero]
  rw [HfixedGlobal,HmoveGlobal] at Hmove
  dsimp only [A,domain] at Hmove
  nlinarith only [Hmove,hj,hje]

end OAI.SKFluctuations.LaplaceWindowFormalization
