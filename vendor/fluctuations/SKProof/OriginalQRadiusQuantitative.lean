module

public import ComparisonActualHighWallThetaZeroRadiusVarianceAssembly
public import ComparisonShiftedNativeRadiusUniformVariance
public import ComparisonShiftedNativeRadiusMeanSquareAssembly
public import ComparisonNativeRadiusQuantitative

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta0 cl cu Az C0 Ct D Bclock : ℝ}

private theorem original_wall_uniform_column_integrable
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

private theorem original_q_radius_dominated_variance_eventually
    (a : ActualThetaZeroOverlapMinimum (n+1) margin delta0 cl cu Az C0 Ct D Bclock)
    (hN : 1  ≤  a.data.N) (hlog : 1  ≤  Real.log a.data.N) (hnd : 1/a.data.N  ≤  a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0  ≤  mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {lo z x kmin : ℝ} (hlo : a.data.rmin < lo) (hloz : lo  ≤  z) (hz : z  ≤  1)
    (hx : 0 < x) (hkmin : 0 < kmin)
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo lo z)
    (hfloor : ∀r∈A,kmin  ≤  a.data.k r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let m:=a.shiftedNativeModel
    let f:=comparisonRadiusMassWeight m.R a.alpha.val.val A x kmin
    let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*laplaceComparisonStrength a.data.d a.lam z)
    ∀ᶠj : ℕ in atTop,comparisonDominatedRadiusVarianceBound (n+1) m.q (as j) f
      (4*(a.radiusS z-a.radiusS lo)/(a.alpha.val.val lo*x^2*kmin*F)+epsilon) := by
  dsimp only
  let m:=a.shiftedNativeModel
  let f:=comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin
  let w:=fun j=>comparisonOriginalRadiusWeights m.q (as j) f
  let W:=fun j r=>deriv m.alpha.val.val r*m.unitColumn (as j) Finset.univ id (fun i=>(w j i)^2) r
  let fixed:=A.indicator (comparisonReciprocalDensityWeight m.alpha.val.val x kmin)
  let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*laplaceComparisonStrength a.data.d a.lam z)
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
    original_wall_uniform_column_integrable m (as j) (ho j) _ (sq_nonneg _) (hsquare j)
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
    hmesh hmesh0 hlim hlo hloz hz hx hkmin hA hAD herr
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
  have Hvar:=m.dominated_radius_variance_le_filled_of_mesh dphys e (as j) (ho j) (hend j)
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
  intro coeff hcoeff
  exact (Hvar coeff hcoeff).trans Hbudget

theorem original_q_radius_centered_defect_le
    (aM : ActualThetaZeroOverlapMinimum (n+1) margin delta0 cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ aM.data.N) (hlog : 1 ≤ Real.log aM.data.N) (hnd : 1/aM.data.N ≤ aM.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {a z xs y delta kmin B w : ℝ} (ha : aM.data.rmin < a) (haz : a ≤ z) (hz : z ≤ 1) (hxs : 0 < xs)
    (hy : xs+aM.alpha.val.val z ≤ y) (hdelta : 0 < delta) (hkmin : 0 < kmin)
    (hfloor : ∀r∈Ioo a z,kmin ≤ aM.data.k r)
    {bins : ℕ} (hbins : 0 < bins) (_hB : 0 ≤ B) (hw : 0 < w) (hwidth : B*y ≤ (bins:ℝ)*w)
    (hraw : ∀ᶠj in atTop,(physicalRawRatio (n+1) 2
      (sampleClockSteps (completedPathClock (n+1) aM.sweepBf aM.sweepHf) 0 (as j)) 0 xs
      (Measure.pi fun k=>gaussianReal 0 (completedPathClock (n+1) aM.sweepBf aM.sweepHf 0 k)) id measurable_id)^2 ≤ B) :
    let S:=aM.radiusS
    let F:=(n+1:ℝ)*(((1/3)/Real.log aM.data.N)*laplaceComparisonStrength aM.data.d aM.lam z)
    let V:=4*(S z-S a)/(aM.alpha.val.val a*delta^2*kmin*F)
    let T:=8*(S z-S a)/(aM.alpha.val.val a^2*F)
    (∫r in Ioo a z,aM.radiusB r-(S r)^2) ≤
      comparisonRadiusMeanSquareBudget bins (z-a) delta y B w V T (2*delta) := by
  dsimp only
  let m:=aM.shiftedNativeModel
  let bf:=aM.sweepBf
  let hf:=aM.sweepHf
  let q:=m.q
  let S := fun r=>aM.radiusS r
  let F := (n+1:ℝ)*(((1/3)/Real.log aM.data.N)*laplaceComparisonStrength aM.data.d aM.lam z)
  let V := 4*(S z-S a)/(aM.alpha.val.val a*delta^2*kmin*F)
  let T := 8*(S z-S a)/(aM.alpha.val.val a^2*F)
  let L := z-a
  let I := ∫r in Ioo a z,orderedPathB (n+1) bf hf (aM.alpha.val.val r)-(S r)^2
  have haI : a∈Icc aM.data.rmin 1 := ⟨ha.le,haz.trans hz⟩
  have hzI : z∈Icc aM.data.rmin 1 := ⟨ha.le.trans haz,hz⟩
  have halpha : 0<aM.alpha.val.val a:=m.profile_pos ha (haz.trans hz)
  have hzalpha : 0 ≤ aM.alpha.val.val z := halpha.le.trans (aM.alpha.val.property.2 haz)
  have hy0 : 0 ≤ y := (add_nonneg hxs.le hzalpha).trans hy
  have hL : 0 ≤ L := sub_nonneg.mpr haz
  have hF : 0<F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos aM.data.d (aM.hlam) z))
  have hmom:=aM.radius_moments
  have hS : 0 ≤ S z-S a:=sub_nonneg.mpr (hmom.1 haI hzI haz)
  have hV : 0 ≤ V:=by dsimp only [V];positivity
  have hT : 0 ≤ T:=by dsimp only [T];positivity
  have hdef:=m.radiusDefect_tendsto as mesh ho hend hmesh hlim ha.le hz hkmin hfloor
  have Hdefeq j : m.radiusDefect (as j)
      (comparisonRadiusMassWeight m.R m.alpha.val.val (Ioo a z) 1 kmin)=
      ∑i,m.radiusRowMass q (as j) Finset.univ a z i*
        actualCutReplicaDefect (n+1) (sampleClockSteps q 0 (as j)) (q 0) i.val
          (physicalPathSecondMoment (n+1) (sampleClockSteps q 0 (as j)) (q 0) i.val):=by
    unfold ShiftedNativeBandModel.radiusDefect
    apply Finset.sum_congr rfl
    intro i _
    rw [m.radiusRowMass_eq_duration_weight q (as j) (ho j) (hend j) ha haz hz
      (by norm_num : (0:ℝ) < 1) hkmin hfloor i,one_mul]
  dsimp only at hdef
  simp_rw [Hdefeq] at hdef
  have heta (eta : ℝ) (heta : 0<eta) : I ≤
      comparisonRadiusMeanSquareBudget bins L delta y B w (V+eta) (T+eta) (2*delta) := by
    have hvar:=aM.original_q_radius_dominated_variance_eventually hN hlog hnd
      dphys e as mesh ho hend hmesh hmesh0 hlim ha haz hz hdelta hkmin
      measurableSet_Ioo (Subset.refl _) hfloor heta
    have hcov:=aM.original_radius_covariance_eventually hN hlog hnd
      dphys e as mesh ho hend hmesh hmesh0 hlim ha haz hz hkmin
      measurableSet_Ioo (Subset.refl _) hfloor heta
    have hfinite : ∀ᶠj in atTop,
        (∑i,m.radiusRowMass q (as j) Finset.univ a z i*
          actualCutReplicaDefect (n+1) (sampleClockSteps q 0 (as j)) (q 0) i.val
            (physicalPathSecondMoment (n+1) (sampleClockSteps q 0 (as j)) (q 0) i.val)) ≤
        comparisonRadiusMeanSquareBudget bins L delta y B w (V+eta) (T+eta)
          (2*delta+2*(mesh j/m.c)) := by
      filter_upwards [hraw,hvar,hcov] with j hjRaw hjVar hjCov
      let steps := sampleClockSteps q 0 (as j)
      let Q := physicalRawRatio (n+1) 2 steps 0 xs (Measure.pi fun k=>gaussianReal 0 (q 0 k)) id measurable_id
      let mass := m.radiusRowMass q (as j) Finset.univ a z
      let Tj := ∑i,mass i*actualCutCovarianceEnergy (n+1) steps (q 0) i.val
      have hTj0 : 0 ≤ Tj := Finset.sum_nonneg (fun i _=>mul_nonneg
        (m.radiusRowMass_nonneg q (as j) Finset.univ a z i)
        (actualCutCovarianceEnergy_nonneg (n+1) steps (sampleClockSteps_ordered q _ (ho j)) (q 0) i.val))
      have hTj : Tj ≤ T+eta := by
        calc
          _ = ∑i,pathMassDifferences steps 0 i*comparisonOriginalRadiusWeights q (as j)
              (comparisonRadiusMassWeight m.R aM.alpha.val.val (Ioo a z) 1 kmin) i*
              actualCutCovarianceEnergy (n+1) steps (q 0) i.val := by
            apply Finset.sum_congr rfl
            intro i _
            dsimp only [mass]
            rw [m.radiusRowMass_eq_duration_weight q (as j)
              (ho j) (hend j) ha haz hz (by norm_num : (0:ℝ)<1) hkmin hfloor i,one_mul]
          _ ≤ _ := hjCov
      have hheight : Q^2*y ≤ (bins:ℝ)*w :=
        (mul_le_mul_of_nonneg_right hjRaw hy0).trans hwidth
      have hfin := m.radius_height_bin_defect_le (n+1) q
        (as j) (ho j) (hend j) (hmesh j) (hmesh0 j) ha haz hz hxs hy hdelta hw hkmin hfloor
        hbins (by positivity : 0 ≤ V+eta) hheight hjVar
      dsimp only at hfin
      have hfin' : (∑i,mass i*actualCutReplicaDefect (n+1) steps (q 0) i.val
          (physicalPathSecondMoment (n+1) steps (q 0) i.val)) ≤
          comparisonRadiusMeanSquareBudget bins L delta y (Q^2) w (V+eta) Tj (2*delta+2*(mesh j/m.c)) := by
        simpa only [comparisonRadiusMeanSquareBudget,←pow_mul,show 2*2=4 by decide] using hfin
      have hEj : 0 ≤ 2*delta+2*(mesh j/m.c) := by have hmj := hmesh0 j;have hc:=m.hc;positivity
      exact hfin'.trans (comparisonRadiusMeanSquareBudget_raw_covariance_mono bins hL hdelta hy0
        (sq_nonneg Q) hjRaw hTj0 hTj hEj)
    have hEmesh : Tendsto (fun j=>2*delta+2*(mesh j/m.c)) atTop (𝓝 (2*delta)) := by
      simpa only [zero_div,mul_zero,add_zero] using
        (tendsto_const_nhds.add (hlim.div_const m.c |>.const_mul 2))
    have hbudget := ((comparisonRadiusMeanSquareBudget_continuous bins L delta y B w (V+eta) (T+eta)).tendsto
      (2*delta)).comp hEmesh
    exact le_of_tendsto_of_tendsto hdef hbudget hfinite
  have hcont : Continuous (fun eta=>comparisonRadiusMeanSquareBudget bins L delta y B w (V+eta) (T+eta) (2*delta)) := by
    unfold comparisonRadiusMeanSquareBudget
    fun_prop
  have hlimit : Tendsto (fun eta=>comparisonRadiusMeanSquareBudget bins L delta y B w (V+eta) (T+eta) (2*delta))
      (𝓝[>] (0:ℝ)) (𝓝 (comparisonRadiusMeanSquareBudget bins L delta y B w V T (2*delta))) := by
    simpa only [add_zero] using (hcont.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  have hout : I ≤ comparisonRadiusMeanSquareBudget bins L delta y B w V T (2*delta) := by
    apply ge_of_tendsto hlimit
    filter_upwards [self_mem_nhdsWithin] with eta he
    exact heta eta he
  exact hout

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
