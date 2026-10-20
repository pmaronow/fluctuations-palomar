module

public import ComparisonSignedCavityActualMinimumResampling
public import ComparisonNativeRadiusQuantitative
public import ComparisonNativeRadiusRawEndpoint

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

theorem cavity_partitionPoint_exists_of_mem (as : List PositiveMass) {u : PositiveMass}
    (hu : u ∈ as) (a : ℝ) :
    ∃i ≤ as.length,partitionPoint a as i=u.val := by
  induction as generalizing a with
  | nil => simp at hu
  | cons v vs ih =>
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ⟨1,by simp, by simp only [partitionPoint,partitionValues,partitionValues_zero,id_eq]⟩
    · obtain ⟨i,hi,he⟩ := ih hu v.val
      exact ⟨i+1,by simp; omega,by simpa only [partitionPoint,partitionValues] using he⟩

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def cavityRadiusDefect (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (a z : ℝ) : ℝ :=
  ∫r in Ioo a z,orderedPathB (n+1) M.bf M.hf (M.alpha.val.val r)-
    (orderedPathS (n+1) M.bf M.hf (M.alpha.val.val r))^2

theorem cavity_floor_on_interval
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {a z : ℝ} (ha : 0 < a) (_hz : z ≤ 1) (r : ℝ) (hr : r ∈ Ioo a z) :
    M.context.k z ≤ M.context.k r := by
  have hN := M.context.hN
  have hU := M.context.hU
  have hr0 : 0 ≤ r := ha.le.trans hr.1.le
  have hden : 0 < r+M.context.N^(2*delta)*M.context.U := by positivity
  unfold NativeOverlapContext.k comparisonFloor
  exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hden)
    (pow_le_pow_left₀ hden.le (by linarith [hr.2.le]) 2)

end NativeOverlapMinimum

theorem eventually_actual_minimum_cavity_radius_budget
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃B : ℝ,0 < B ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀(a z : ℝ),0 < a → a≤z → z≤1 →
      ∀(dphys : ℕ) (_e : Fin (dphys+1) ≃ FeatureIndex (n+1)) (Kb Kh : ℝ≥0),
      LipschitzOnWith Kb (fun r=>M.b (M.alpha.val.val r)) (Icc a z) →
      LipschitzOnWith Kh (fun r=>M.h (M.alpha.val.val r)) (Icc a z) →
      let S := fun r=>orderedPathS (n+1) M.bf M.hf (M.alpha.val.val r)
      let y := M.xs+M.alpha.val.val z
      let F := (n+1:ℝ)*(((1/3)/Real.log (n+1))*laplaceComparisonStrength M.context.d M.lam z)
      S z-S a ≤ B*y ∧
      ∀(bins : ℕ),0 < bins → ∀tau : ℝ,0 < tau →
        M.cavityRadiusDefect a z ≤
          comparisonRadiusMeanSquareBudget bins (z-a) tau y B (B*y/(bins:ℝ))
            (4*(S z-S a)/(M.alpha.val.val a*tau^2*M.context.k z*F))
            (8*(S z-S a)/(M.alpha.val.val a^2*F)) (2*tau) := by
  obtain ⟨C,hC,hraw⟩ := eventually_native_minimum_original_boundary_raw
    1 Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have hshift : Tendsto (fun n:ℕ=>n+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k] with n hn
    omega
  have hlog : ∀ᶠn : ℕ in atTop,1≤Real.log (n+1:ℝ) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hshift).eventually
        (eventually_ge_atTop 1)
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hshift.eventually hraw,hshift.eventually (eventually_comparisonLowerScale_depth hC0 hm),hlog]
    with n hnraw hdepth hnlog
  intro M a z ha haz hz dphys e Kb Kh hparent hfield
  dsimp only
  let c := M.context
  have haI : a ∈ Icc (0:ℝ) 1 := ⟨ha.le,haz.trans hz⟩
  have hzI : z ∈ Icc (0:ℝ) 1 := ⟨ha.le.trans haz,hz⟩
  have hua : 0 < M.alpha.val.val a := by
    have H := inverseConstraint_strictMonoOn c.hc c.hk c.hkc M.alpha.property
      (by norm_num) haI ha
    simpa only [M.alpha.property.1] using H
  have huz : 0 < M.alpha.val.val z := hua.trans_le (M.alpha.val.property.2 haz)
  let u : PositiveMass := ⟨M.alpha.val.val z,huz⟩
  have hu1 : u.val≤1 := (M.alpha.val.property.1 z).2
  obtain ⟨us,hus,huretain,_,hQ⟩ := hnraw M u hu1 [] (by simp)
  let as := finiteCutMasses us
  let mesh := fun j:ℕ=>((j+1:ℕ):ℝ)⁻¹
  have ho j : MassOrdered 0 (as j) := finiteCutMasses_ordered us hus j
  have he j : partitionEnd 0 (as j)=1 := finiteCutMasses_end us hus j
  have hmesh j : PartitionMesh (mesh j) 0 (as j) := finiteCutMasses_mesh us hus j
  have hQ' : ∀ᶠj : ℕ in atTop,
      (physicalRawRatio (n+1) 2 (sampleClockSteps (completedPathClock (n+1) M.bf M.hf) 0 (as j))
        0 M.xs (Measure.pi fun i=>gaussianReal 0 (completedPathClock (n+1) M.bf M.hf 0 i))
        id measurable_id)^2 ≤ 2*C := by
    filter_upwards [hQ] with j hj
    exact hj.1
  have had := comparisonVariableEndpoint_clocks_admissible c.hc c.hk c.hkc c.hm c.hM
    M.b M.h c.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hbf : MonotoneOn M.bf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.1
  have hhf : MonotoneOn M.hf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.2.1
  have hretain j : ∃i≤(as j).length,partitionPoint 0 (as j) i=M.alpha.val.val z :=
    cavity_partitionPoint_exists_of_mem (as j) (finiteCutMasses_nodes us j huretain) 0
  have hSz := orderedPathS_le_retained_native_raw n 2 (by norm_num) M.bf M.hf hbf hhf
    as mesh ho he hmesh uniformMasses_mesh_tendsto huz M.hxs hretain hQ'
  have hmom := comparisonVariableEndpoint_radius_moments c.hc c.hk c.hkc c.hm c.hM
    (n+1) (by omega) M.b M.h c.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hSa : 0 ≤ orderedPathS (n+1) M.bf M.hf (M.alpha.val.val a) :=
    (hmom.2.2 a haI).1.1
  constructor
  · linarith
  intro bins hbins tau htau
  have hy : 0 < M.xs+M.alpha.val.val z := add_pos M.hxs huz
  have hb : 0 < (bins:ℝ) := by exact_mod_cast hbins
  have hwidth : (2*C)*(M.xs+M.alpha.val.val z) ≤
      (bins:ℝ)*((2*C)*(M.xs+M.alpha.val.val z)/(bins:ℝ)) := by
    rw [mul_div_cancel₀ _ hb.ne']
  have hnd : 1/c.N≤c.d := by
    have H := hdepth c.E c.d c.hE c.hd M.hlower
    have hs : comparisonLowerScale c.N c.E c.d≤c.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ c.hd).mpr (by simpa only [c,pow_two] using M.hupper)
    exact H.trans hs
  have hkmin : 0 < c.k z := comparisonFloor_pos c.hN c.hU hzI.1
  have H := comparison_native_radius_centered_defect_le c.hc c.hk c.hkc c.hm c.hM
    (show (1:ℝ)≤(n+1:ℝ) by norm_num) hnlog c.hd
    (by simpa only [c,NativeOverlapContext.N,Nat.cast_add,Nat.cast_one] using hnd)
    M.hlam M.hld n dphys e
    M.b M.h M.hb M.hh M.hh0 M.hlb M.alpha as mesh ho he hmesh
    (fun _=>by dsimp [mesh]; positivity) uniformMasses_mesh_tendsto ha haz hz M.hxs
    (le_rfl : M.xs+M.alpha.val.val z≤M.xs+M.alpha.val.val z) htau hkmin
    (fun r hr=>M.cavity_floor_on_interval ha hz r hr) Kb Kh hparent hfield hbins
    (by positivity : 0 ≤ 2*C) (div_pos (mul_pos (by positivity) hy) hb) hwidth hQ'
  exact H

end OAI.SKFluctuations.LaplaceWindowFormalization
