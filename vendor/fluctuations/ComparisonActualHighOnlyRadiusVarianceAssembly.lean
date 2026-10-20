module

public import ComparisonActualHighOnlyTraceLimit
public import ComparisonShiftedNativeRadiusOriginalWeights

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option linter.unnecessarySeqFocus false
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable (a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)

theorem reciprocal_radius_trace_eventually
    (hN : 1  ≤  a.data.N) (hlog : 1  ≤  Real.log a.data.N) (hnd : 1/a.data.N  ≤  a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0  ≤  mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {lo z x kmin : ℝ} (hlo : (0:ℝ) < lo) (hloz : lo  ≤  z) (hz : z  ≤  1)
    (hx : 0 < x) (hkmin : 0 < kmin)
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>a.b (a.alpha.val.val r)) (Icc lo z))
    (hfield : LipschitzOnWith Kh (fun r=>a.h (a.alpha.val.val r)) (Icc lo z))
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo lo z)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let m:=a.shiftedNativeModel
    let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) z)
    ∀ᶠj : ℕ in atTop,
      (∫r in A,comparisonReciprocalDensityWeight a.alpha.val.val x kmin r
        ∂m.radiusMeasure dphys e (as j) (ho j))  ≤ 
          (a.radiusS z-a.radiusS lo)/(x^2*kmin*F)+epsilon := by
  dsimp only
  let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) z)
  let weight:=comparisonReciprocalDensityWeight a.alpha.val.val x kmin
  have hF : 0 < F:=mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith))
    (laplaceComparisonStrength_pos a.data.d a.hlam z))
  have hSm : MonotoneOn a.radiusS (Icc lo z):=
    a.radius_moments.1.mono (Icc_subset_Icc hlo.le hz)
  have hAC:=a.radiusS_absolutelyContinuous dphys e hlo hloz hz Kb Kh hparent hfield
  have hw r:=comparisonReciprocalDensityWeight_bounds a.alpha.val.val hx hkmin r
  have hwm : AEStronglyMeasurable weight volume:=
    (comparisonReciprocalDensityWeight_measurable a.alpha.val.val x kmin).aestronglyMeasurable
  have HFTC:=reciprocal_density_derivative_budget hloz hSm hAC hA
    (hAD.trans Ioo_subset_Icc_self) hwm (by positivity : 0  ≤  1/(x^2*kmin))
    (fun r _=>by simpa only [weight,Real.norm_eq_abs,abs_of_nonneg (hw r).1] using (hw r).2)
    (fun r _=>(hw r).1)
  have Htrace:=a.radius_trace_boundedWeight hN hlog hnd dphys e as ho hend mesh hmesh hmesh0
    hlim hlo hloz hz Kb Kh hparent hfield hA hAD weight hwm (1/(x^2*kmin))
    (fun r _=>by simpa only [weight,Real.norm_eq_abs,abs_of_nonneg (hw r).1] using (hw r).2)
    (fun r _=>(hw r).1) hepsilon
  filter_upwards [Htrace] with j hj
  apply hj.trans
  have HB:=div_le_div_of_nonneg_right HFTC hF.le
  have HB' : (∫r in A,weight r*deriv a.radiusS r)/F  ≤ 
      (a.radiusS z-a.radiusS lo)/(x^2*kmin*F):=by
    simpa only [div_eq_mul_inv,one_div,mul_inv_rev,mul_assoc,mul_comm,mul_left_comm,one_mul] using HB
  exact add_le_add HB' le_rfl

theorem plain_radius_trace_eventually
    (hN : 1  ≤  a.data.N) (hlog : 1  ≤  Real.log a.data.N) (hnd : 1/a.data.N  ≤  a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0  ≤  mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {lo z : ℝ} (hlo : (0:ℝ) < lo) (hloz : lo  ≤  z) (hz : z  ≤  1)
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>a.b (a.alpha.val.val r)) (Icc lo z))
    (hfield : LipschitzOnWith Kh (fun r=>a.h (a.alpha.val.val r)) (Icc lo z))
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo lo z)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let m:=a.shiftedNativeModel
    let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) z)
    ∀ᶠj : ℕ in atTop,(∫_r in A,(1:ℝ)∂m.radiusMeasure dphys e (as j) (ho j))  ≤ 
      (a.radiusS z-a.radiusS lo)/F+epsilon := by
  dsimp only
  let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) z)
  have hF : 0 < F:=mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith))
    (laplaceComparisonStrength_pos a.data.d a.hlam z))
  have hSm : MonotoneOn a.radiusS (Icc lo z):=
    a.radius_moments.1.mono (Icc_subset_Icc hlo.le hz)
  have HFTC:=reciprocal_density_derivative_budget (weight:=fun _ : ℝ=>(1:ℝ)) hloz hSm
    (a.radiusS_absolutelyContinuous dphys e hlo hloz hz Kb Kh hparent hfield) hA
    (hAD.trans Ioo_subset_Icc_self) measurable_const.aestronglyMeasurable
    (by norm_num : (0:ℝ)  ≤  1) (fun _ _=>by norm_num) (fun _ _=>by norm_num)
  have Htrace:=a.radius_trace_boundedWeight hN hlog hnd dphys e as ho hend mesh hmesh hmesh0
    hlim hlo hloz hz Kb Kh hparent hfield hA hAD (fun _=>1) measurable_const.aestronglyMeasurable 1
    (fun _ _=>by norm_num) (fun _ _=>by norm_num) hepsilon
  filter_upwards [Htrace] with j hj
  have HB:=div_le_div_of_nonneg_right HFTC hF.le
  exact hj.trans (add_le_add (by simpa only [one_mul] using HB) le_rfl)

private theorem original_column_integrable
    (m : ShiftedNativeBandModel) (as : List PositiveMass) (ho : MassOrdered 0 as)
    (col : Fin ((sampleClockSteps m.q 0 as).length+1)→ℝ) {B : ℝ} (hB : 0  ≤  B)
    (hcol : ∀i,col i∈Icc (0:ℝ) B) :
    IntegrableOn (fun r=>deriv m.alpha.val.val r*m.unitColumn as Finset.univ id col r)
      (Icc m.rmin 1) := by
  have hLip : LipschitzOnWith ⟨m.M 1,m.hM⟩ m.alpha.val.val (uIcc m.rmin 1):=by
    simpa only [uIcc_of_le m.hr] using inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property
  have hAC:=hLip.absolutelyContinuousOnInterval
  have hiD : IntegrableOn (deriv m.alpha.val.val) (Icc m.rmin 1):=
    (intervalIntegrable_iff_integrableOn_Icc_of_le m.hr).mp hAC.intervalIntegrable_deriv
  have hcolB r : m.unitColumn as Finset.univ id col r∈Icc (0:ℝ) B:=by
    apply radiusCellEnergyDensity_mem_Icc_bound m.R m.R_monotone as ho _ hB
    intro i
    unfold nativeSelectedColumn
    split_ifs
    · exact hcol _
    · exact ⟨le_rfl,hB⟩
    · exact ⟨le_rfl,hB⟩
  have hmeas:=m.unitColumn_measurable as Finset.univ id col
  have hbnd : ∀ᵐr∂volume.restrict (Icc m.rmin 1),‖m.unitColumn as Finset.univ id col r‖  ≤  B:=by
    filter_upwards [] with r
    rw [Real.norm_eq_abs,abs_of_nonneg (hcolB r).1]
    exact (hcolB r).2
  simpa only [IntegrableOn,mul_comm] using hiD.bdd_mul hmeas.aestronglyMeasurable.restrict hbnd

theorem original_radius_variance_eventually
    (hN : 1  ≤  a.data.N) (hlog : 1  ≤  Real.log a.data.N) (hnd : 1/a.data.N  ≤  a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0  ≤  mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {lo z x kmin : ℝ} (hlo : (0:ℝ) < lo) (hloz : lo  ≤  z) (hz : z  ≤  1)
    (hx : 0 < x) (hkmin : 0 < kmin)
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>a.b (a.alpha.val.val r)) (Icc lo z))
    (hfield : LipschitzOnWith Kh (fun r=>a.h (a.alpha.val.val r)) (Icc lo z))
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo lo z)
    (hfloor : ∀r∈A,kmin  ≤  a.data.k r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let m:=a.shiftedNativeModel
    let f:=comparisonRadiusMassWeight m.R a.alpha.val.val A x kmin
    let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) z)
    ∀ᶠj : ℕ in atTop,
      let steps:=sampleClockSteps m.q 0 (as j)
      let w:=comparisonOriginalRadiusWeights m.q (as j) f
      variance (fun p=>(physicalPinnedPair (uniformWeight (n+1)) (finiteFeature (n+1))
        (spinSource (n+1)) steps 0 w p.1 p.2).1)
        (rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) (m.q 0) steps)  ≤ 
          4*(a.radiusS z-a.radiusS lo)/(a.alpha.val.val lo*x^2*kmin*F)+epsilon := by
  dsimp only
  let m:=a.shiftedNativeModel
  let f:=comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin
  let w:=fun j=>comparisonOriginalRadiusWeights m.q (as j) f
  let W:=fun j r=>deriv m.alpha.val.val r*m.unitColumn (as j) Finset.univ id (fun i=>(w j i)^2) r
  let fixed:=A.indicator (comparisonReciprocalDensityWeight m.alpha.val.val x kmin)
  let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) z)
  let mu:=fun j=>m.radiusMeasure dphys e (as j) (ho j)
  let B:=(1/(x*kmin))^2
  let err:=epsilon*m.alpha.val.val lo/24
  have hmass : 0 < m.alpha.val.val lo:=m.profile_pos hlo (hloz.trans hz)
  have hwall : 0 < m.alpha.val.val lo-m.u0:=by
    have H:=inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property
      ⟨le_rfl,m.hr⟩ ⟨hlo.le,hloz.trans hz⟩ hlo
    rw [m.alpha.property.1] at H
    exact sub_pos.mpr H
  have herr : 0 < err:=by dsimp [err];positivity
  have hwbound j i : w j i∈Icc (0:ℝ) (1/(x*kmin)):=
    m.original_radius_weights_bounds hA hx hkmin (as j) (ho j) i
  have hsquare j i : (w j i)^2∈Icc (0:ℝ) B:=
    ⟨sq_nonneg _,pow_le_pow_left₀ (hwbound j i).1 (hwbound j i).2 2⟩
  have hiW j : IntegrableOn (W j) (Icc m.rmin 1):=
    original_column_integrable m (as j) (ho j) _ (sq_nonneg _) (hsquare j)
  have hiFixed : IntegrableOn fixed (Icc m.rmin 1):=by
    apply (memLp_of_bounded (p:=1) (a:=0) (b:=1/(x^2*kmin)) ?_ ?_).integrable le_rfl
    · exact Eventually.of_forall (fun r=>by
        by_cases hr : r∈A
        · rw [show fixed r=comparisonReciprocalDensityWeight m.alpha.val.val x kmin r from indicator_of_mem hr _]
          exact comparisonReciprocalDensityWeight_bounds m.alpha.val.val hx hkmin r
        · simp only [fixed,indicator_of_notMem hr];exact ⟨le_rfl,by positivity⟩)
    · exact ((comparisonReciprocalDensityWeight_measurable m.alpha.val.val x kmin).indicator hA).aestronglyMeasurable
  have herror:=m.originalRadiusWeights_square_tendsto_L1 hA hx hkmin hfloor
    as mesh ho hend hmesh hlim
  have htrace:=a.reciprocal_radius_trace_eventually hN hlog hnd dphys e as mesh ho hend
    hmesh hmesh0 hlim hlo hloz hz hx hkmin Kb Kh hparent hfield hA hAD herr
  have hmeshError : Tendsto (fun j=>mesh j*B) atTop (𝓝 0):=by simpa using hlim.mul_const B
  filter_upwards [htrace,(tendsto_order.mp herror).2 err herr,
    (tendsto_order.mp hlim).2 (m.alpha.val.val lo/2) (by positivity),
    (tendsto_order.mp hlim).2 (m.alpha.val.val lo-m.u0) hwall,
    (tendsto_order.mp hmeshError).2 err herr] with j hjtrace hjerror hjcut hjwall hjmesh
  have hdom:=m.radius_measure_le_compact_volume dphys e (as j) (ho j)
  have hsupport : (mu j).restrict (Icc m.rmin 1)=mu j:=
    Measure.restrict_eq_self_of_ae_mem ((ae_restrict_mem measurableSet_Icc).filter_mono (ae_mono hdom))
  have hmoving:=dominated_setIntegral_difference_le (Icc m.rmin 1) (Icc m.rmin 1)
    (Subset.refl _) (mu j) (hdom.trans Measure.restrict_le_self) fixed (W j) hiFixed (hiW j)
  rw [hsupport] at hmoving
  have hfixedInt : (∫r,fixed r∂mu j)=
      ∫r in A,comparisonReciprocalDensityWeight m.alpha.val.val x kmin r∂mu j:=integral_indicator hA
  rw [hfixedInt] at hmoving
  have hfilled : (∫r,W j r∂mu j)  ≤  (a.radiusS z-a.radiusS lo)/(x^2*kmin*F)+2*err:=by
    dsimp only [W,w,f,fixed,mu] at hmoving
    dsimp only [F,m] at hjtrace ⊢
    linarith
  have Hvar:=m.original_radius_variance_le_filled_of_mesh dphys e (as j) (ho j) (hend j)
    (hmesh j) (hmesh0 j) hlo hloz hz hx hkmin hA hAD hjcut.le hjwall.le
  have Hbudget : (2*(∫r,W j r∂mu j)+2*(mesh j*B))/(m.alpha.val.val lo/2)  ≤ 
      4*(a.radiusS z-a.radiusS lo)/(m.alpha.val.val lo*x^2*kmin*F)+epsilon:=by
    apply (div_le_iff₀ (by positivity : 0 < m.alpha.val.val lo/2)).mpr
    have HF:=mul_le_mul_of_nonneg_left hfilled (by norm_num : (0:ℝ)  ≤  2)
    have heq : (4*(a.radiusS z-a.radiusS lo)/(m.alpha.val.val lo*x^2*kmin*F)+epsilon)*
        (m.alpha.val.val lo/2)=2*((a.radiusS z-a.radiusS lo)/(x^2*kmin*F))+epsilon*m.alpha.val.val lo/2:=by
      field_simp [hmass.ne'];ring
    rw [heq]
    dsimp only [err] at HF hjmesh
    have HP:=mul_pos hepsilon hmass
    linarith
  exact Hvar.trans Hbudget

theorem original_radius_covariance_eventually
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {lo z kmin : ℝ} (hlo : (0:ℝ) < lo) (hloz : lo ≤ z) (hz : z ≤ 1)
    (hkmin : 0 < kmin)
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>a.b (a.alpha.val.val r)) (Icc lo z))
    (hfield : LipschitzOnWith Kh (fun r=>a.h (a.alpha.val.val r)) (Icc lo z))
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo lo z)
    (hfloor : ∀r∈A,kmin ≤ a.data.k r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let m:=a.shiftedNativeModel
    let f:=comparisonRadiusMassWeight m.R a.alpha.val.val A 1 kmin
    let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) z)
    ∀ᶠj : ℕ in atTop,
      let steps:=sampleClockSteps m.q 0 (as j)
      let w:=comparisonOriginalRadiusWeights m.q (as j) f
      (∑i,pathMassDifferences steps 0 i*w i*actualCutCovarianceEnergy (n+1) steps (m.q 0) i.val) ≤
        8*(a.radiusS z-a.radiusS lo)/(a.alpha.val.val lo^2*F)+epsilon := by
  dsimp only
  let m:=a.shiftedNativeModel
  let f:=comparisonRadiusMassWeight m.R m.alpha.val.val A 1 kmin
  let w:=fun j=>comparisonOriginalRadiusWeights m.q (as j) f
  let W:=fun j r=>deriv m.alpha.val.val r*m.unitColumn (as j) Finset.univ id (w j) r
  let fixed:=A.indicator (fun _=>(1:ℝ))
  let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) z)
  let mu:=fun j=>m.radiusMeasure dphys e (as j) (ho j)
  let B:=1/kmin
  let err:=epsilon*m.alpha.val.val lo^2/48
  have hmass : 0 < m.alpha.val.val lo:=m.profile_pos hlo (hloz.trans hz)
  have hwall : 0 < m.alpha.val.val lo-m.u0:=by
    have H:=inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property
      ⟨le_rfl,m.hr⟩ ⟨hlo.le,hloz.trans hz⟩ hlo
    rw [m.alpha.property.1] at H
    exact sub_pos.mpr H
  have herr : 0 < err:=by dsimp [err];positivity
  have hwbound j i : w j i∈Icc (0:ℝ) B:=by
    simpa only [one_mul] using
      m.original_radius_weights_bounds hA (by norm_num : (0:ℝ) < 1) hkmin (as j) (ho j) i
  have hiW j : IntegrableOn (W j) (Icc m.rmin 1):=
    original_column_integrable m (as j) (ho j) _ (by positivity) (hwbound j)
  have hiFixed : IntegrableOn fixed (Icc m.rmin 1):=(integrable_const (1:ℝ)).indicator hA
  have herror:=m.originalRadiusWeights_linear_tendsto_L1 hA (by norm_num : (0:ℝ) < 1) hkmin hfloor
    as mesh ho hend hmesh hlim
  have htrace:=a.plain_radius_trace_eventually hN hlog hnd dphys e as mesh ho hend
    hmesh hmesh0 hlim hlo hloz hz Kb Kh hparent hfield hA hAD herr
  have hmeshError : Tendsto (fun j=>mesh j*B) atTop (𝓝 0):=by simpa using hlim.mul_const B
  filter_upwards [htrace,(tendsto_order.mp herror).2 err herr,
    (tendsto_order.mp hlim).2 (m.alpha.val.val lo/2) (by positivity),
    (tendsto_order.mp hlim).2 (m.alpha.val.val lo-m.u0) hwall,
    (tendsto_order.mp hmeshError).2 err herr] with j hjtrace hjerror hjcut hjwall hjmesh
  have hdom:=m.radius_measure_le_compact_volume dphys e (as j) (ho j)
  have hsupport : (mu j).restrict (Icc m.rmin 1)=mu j:=
    Measure.restrict_eq_self_of_ae_mem ((ae_restrict_mem measurableSet_Icc).filter_mono (ae_mono hdom))
  have hmoving:=dominated_setIntegral_difference_le (Icc m.rmin 1) (Icc m.rmin 1)
    (Subset.refl _) (mu j) (hdom.trans Measure.restrict_le_self) fixed (W j) hiFixed (hiW j)
  rw [hsupport] at hmoving
  have hfixedInt : (∫r,fixed r∂mu j)=∫_r in A,(1:ℝ)∂mu j:=integral_indicator hA
  rw [hfixedInt] at hmoving
  have hfilled : (∫r,W j r∂mu j) ≤ (a.radiusS z-a.radiusS lo)/F+2*err:=by
    have HE : (fun r : ℝ=>1/(1:ℝ))=(fun _=>(1:ℝ)):=by funext r;norm_num
    dsimp only [W,w,f,fixed,mu] at hmoving
    dsimp only [F,m] at hjtrace ⊢
    simp only [HE] at hjerror
    linarith
  have Hcov:=m.original_radius_covariance_le_filled_of_mesh dphys e (as j) (ho j) (hend j)
    (hmesh j) (hmesh0 j) hlo hloz hz hkmin hA hAD hjcut.le hjwall.le
  have Hbudget : (2*(∫r,W j r∂mu j)+2*(mesh j*B))/(m.alpha.val.val lo/2)^2 ≤
      8*(a.radiusS z-a.radiusS lo)/(m.alpha.val.val lo^2*F)+epsilon:=by
    apply (div_le_iff₀ (by positivity : 0 < (m.alpha.val.val lo/2)^2)).mpr
    have HF:=mul_le_mul_of_nonneg_left hfilled (by norm_num : (0:ℝ) ≤ 2)
    have heq : (8*(a.radiusS z-a.radiusS lo)/(m.alpha.val.val lo^2*F)+epsilon)*
        (m.alpha.val.val lo/2)^2=2*((a.radiusS z-a.radiusS lo)/F)+epsilon*m.alpha.val.val lo^2/4:=by
      field_simp [hmass.ne'];ring
    rw [heq]
    dsimp only [err] at HF hjmesh
    have HP:=mul_pos hepsilon (sq_pos_of_pos hmass)
    linarith
  exact Hcov.trans Hbudget

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
