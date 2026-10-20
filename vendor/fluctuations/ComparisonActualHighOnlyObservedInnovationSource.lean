module

public import ComparisonActualHighOnlyInnovation
public import ComparisonActualHighOnlyAnalyticBasics
public import ComparisonSignedCavityObservedInnovationWitness
public import ComparisonSignedCavityObservedCalibrationScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
set_option autoImplicit false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock mesh v : ℝ}

theorem exists_observed_rest_pre_high_innovation_high_only
    (n : ℕ) (hn : 0< n) (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0< cl) (hlog : 1≤ Real.log M.data.N) (hnd : 1/M.data.N≤ M.data.d)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hmesh : 0≤ mesh) (hpart : PartitionMesh mesh 0 as)
    (hv : 0< v) (hsmall : mesh/(M.data.k 1)≤ v/16)
    {low high w : ℕ} (hhigh : high≤ as.length) (hhw : high≤ w) (hw : w≤ as.length+1)
    (hvr : M.R (partitionPoint 0 as high)=v)
    (hlow : M.R (partitionPoint 0 as low)≤ v/2) (hz : M.z≤ v/2) :
    let steps:=nativeSampledPhysicalSteps n M.bf M.hf as
    ∃pre : ℕ,low≤ pre ∧ pre≤ high ∧ cl*v/2≤ partitionPoint 0 as pre ∧
      let duration:=physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩)) (cutSlice steps pre high)
      0< duration ∧ laplaceComparisonStrength M.data.d M.lam v*v/(12*Real.log M.data.N)≤ duration ∧ duration≤ Bclock ∧
      PhysicalProjectionClock n steps low high w (cl*v/2) duration ∧
      PhysicalProjectionClock n (steps.drop low) 0 (high-low) (w-low) (cl*v/2) duration := by
  let R:=M.R
  let rg : Fin (as.length+2)→ℝ:=fun i=>R (partitionPoint 0 as i.val)
  let pre:=radiusGridCut rg (3*v/4)
  have hmono : Monotone rg:=fun i j hij=>M.shiftedNativeModel.R_monotone (partitionPoint_mono as ho hij)
  have hr0 : rg 0=0:=by
    change R (partitionPoint 0 as 0)=0
    rw [show partitionPoint 0 as 0=0 from by simp [partitionPoint]]
    have HH:=M.shiftedNativeModel.R_monotone M.data.hs.1
    change M.R 0≤M.R M.data.s at HH
    have HL : M.R M.data.s=0:=M.shiftedNativeModel.R_left
    exact le_antisymm (HL ▸ HH) (M.shiftedNativeModel.R_bounds 0).1
  have hroot : rg 0<3*v/4:=by rw [hr0];linarith only [M.hz.1,hz,hv]
  have hlast : 3*v/4≤ rg (Fin.last (as.length+1)):=by
    have HH:=M.shiftedNativeModel.R_monotone
      (partitionPoint_mono as ho (show high≤ as.length+1 by omega))
    change M.R (partitionPoint 0 as high)≤ rg (Fin.last (as.length+1)) at HH
    rw [hvr] at HH
    linarith only [HH,hv]
  have hstep : ∀j : Fin (as.length+1),rg j.succ-rg j.castSucc≤ mesh/(M.data.k 1):=
    fun j=>M.sampled_radius_step_le as ho hmesh hpart j.val
  have HP:=radiusGridPoint_bounds rg hmono hroot hlast hstep
  change 3*v/4-mesh/(M.data.k 1)≤ R (partitionPoint 0 as pre) ∧ R (partitionPoint 0 as pre)<3*v/4 at HP
  have Hprelow : v/2< R (partitionPoint 0 as pre):=by linarith only [HP.1,hsmall,hv]
  have hpreHigh : pre≤ high:=by
    by_contra hh
    have HH:=M.shiftedNativeModel.R_monotone (partitionPoint_mono as ho (le_of_not_ge hh))
    simp only [ActualHighOnlyOverlapMinimum.shiftedNativeModel_radius] at HH
    rw [hvr] at HH
    linarith only [HH,HP.2,hv]
  have hlowPre : low≤ pre:=by
    by_contra hh
    have HH:=M.shiftedNativeModel.R_monotone (partitionPoint_mono as ho (le_of_not_ge hh))
    simp only [ActualHighOnlyOverlapMinimum.shiftedNativeModel_radius] at HH
    linarith only [HH,hlow,Hprelow]
  have hpre0 : 0< R (partitionPoint 0 as pre):=by linarith only [Hprelow,M.hz.1,hz]
  have hpreMass : partitionPoint 0 as pre∈Icc M.data.s 1:=
    ⟨(M.radius_high_mass hpre0).le,(partitionPoint_mem as ho pre).2⟩
  have hhighMass : partitionPoint 0 as high∈Icc M.data.s 1:=
    ⟨hpreMass.1.trans (partitionPoint_mono as ho hpreHigh),(partitionPoint_mem as ho high).2⟩
  have hpreReg : R (partitionPoint 0 as pre)∈Icc M.z 1:=
    ⟨hz.trans Hprelow.le,(M.shiftedNativeModel.R_bounds _).2⟩
  have hmass : cl*v/2≤ partitionPoint 0 as pre:=by
    have HR:=(M.regular _ hpreReg).1
    change cl*R (partitionPoint 0 as pre) ≤ M.alpha.val.val (R (partitionPoint 0 as pre)) at HR
    rw [show M.alpha.val.val (R (partitionPoint 0 as pre))=partitionPoint 0 as pre from M.shiftedNativeModel.R_spec hpreMass] at HR
    have HH:=mul_le_mul_of_nonneg_left Hprelow.le hcl.le
    linarith only [HR,HH]
  let steps:=nativeSampledPhysicalSteps n M.bf M.hf as
  let duration:=physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩)) (cutSlice steps pre high)
  have HE : duration=(M.hf (partitionPoint 0 as high):ℝ)-(M.hf (partitionPoint 0 as pre):ℝ):=
    native_sampled_field_duration_slice n M.bf M.hf (M.bf_monotone)
      (M.hf_monotone) as ho ⟨0,hn⟩ hpreHigh hhigh
  have hN1 : 1≤ M.data.N:=by exact_mod_cast Nat.succ_pos n
  have Hgap:=M.high_field_radius_gap hN1 hlog hnd hpreMass hhighMass
    (partitionPoint_mono as ho hpreHigh)
  rw [hvr] at Hgap
  have Hcoef : 0≤ ((1:ℝ)/3)/Real.log M.data.N*laplaceComparisonStrength M.data.d M.lam v:=by
    exact mul_nonneg (by positivity) (laplaceComparisonStrength_pos _ M.hlam _).le
  have HDlow : laplaceComparisonStrength M.data.d M.lam v*v/(12*Real.log M.data.N)≤ duration:=by
    rw [HE]
    have HH:=mul_le_mul_of_nonneg_left (show v/4≤ v-R (partitionPoint 0 as pre) by linarith only [HP.2]) Hcoef
    have HElem : laplaceComparisonStrength M.data.d M.lam v*v/(12*Real.log M.data.N)≤
        (((1:ℝ)/3)/Real.log M.data.N*laplaceComparisonStrength M.data.d M.lam v)*(v-R (partitionPoint 0 as pre)):=by
      convert HH using 1;ring
    exact HElem.trans Hgap
  have HDpos : 0< duration:=(div_pos
    (mul_pos (laplaceComparisonStrength_pos _ M.hlam _) hv) (by positivity)).trans_le HDlow
  have HDhigh : duration≤ Bclock:=by
    rw [HE]
    have HH:=M.hf_monotone (partitionPoint_mem as ho high) (by simp : (1:ℝ)∈Icc 0 1)
      (partitionPoint_mem as ho high).2
    have HP:=M.hf_monotone (by simp : (0:ℝ)∈Icc 0 1) (partitionPoint_mem as ho pre)
      (partitionPoint_mem as ho pre).1
    have HHr : (M.hf (partitionPoint 0 as high):ℝ)≤M.hf 1:=by exact_mod_cast HH
    have HPr : (M.hf 0:ℝ)≤M.hf (partitionPoint 0 as pre):=by exact_mod_cast HP
    linarith only [HHr,HPr,M.clockBudget]
  have HC:=native_sampled_field_layer_projection_clock n M.bf M.hf as ho ⟨0,hn⟩
    (by positivity : 0≤ cl*v/2) hlowPre hpreHigh hhw hhigh hw hmass
  exact ⟨pre,hlowPre,hpreHigh,hmass,HDpos,HDlow,HDhigh,HC,actual_physical_projection_clock_suffix HC⟩

theorem exists_observed_rest_finite_innovation_high_only
    (n : ℕ) (hn : 0< n) (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0< cl) (hlog : 1≤ Real.log M.data.N) (hnd : 1/M.data.N≤ M.data.d)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (hmesh : 0≤ mesh) (hpart : PartitionMesh mesh 0 as)
    (hv : 0< v) (hsmall : mesh/(M.data.k 1)≤ v/16) {low high : ℕ} (hhigh : high≤ as.length)
    (hvr : M.R (partitionPoint 0 as high)=v)
    (hlow : M.R (partitionPoint 0 as low)≤ v/2) (hz : M.z≤ v/2) :
    let steps:=nativeSampledPhysicalSteps n M.bf M.hf as
    ∃pre : ℕ,low≤ pre ∧ pre≤ high ∧ cl*v/2≤ partitionPoint 0 as pre ∧
      let innovation:=cutSlice steps pre high
      let duration:=physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩)) innovation
      0< duration ∧ laplaceComparisonStrength M.data.d M.lam v*v/(12*Real.log M.data.N)≤ duration ∧ duration≤ Bclock ∧
      (steps.drop low).take (high-low)=cutSlice steps low pre++innovation ∧
      (steps.drop low).drop (high-low)=steps.drop high ∧
      OrderedSteps (cl*v/2) (innovation++steps.drop high) ∧
      ∃d : Fin innovation.length→ℝ,(∀j,0≤ d j) ∧ (∑j,d j)=duration ∧
        (∀j i,(hierarchyClocks innovation j (Sum.inl i):ℝ)=d j) := by
  obtain ⟨pre,hlp,hph,hmass,hpos,hlower,hupper,-,-⟩:=
    exists_observed_rest_pre_high_innovation_high_only n hn M hcl hlog hnd as ho hmesh hpart hv hsmall hhigh le_rfl (by omega) hvr hlow hz
  have HF:=native_observed_innovation_finite_witness n M.bf M.hf as ho ⟨0,hn⟩
    (by positivity : 0≤ cl*v/2) hlp hph hhigh hmass
  exact ⟨pre,hlp,hph,hmass,hpos,hlower,hupper,HF⟩

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
