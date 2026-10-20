module

public import ComparisonActualHighWallRetainedRaw
public import ComparisonActualHighWallHighMassNumerics
public import ComparisonNativeActualMeanRawUpper

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem mass_mean_nonneg
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) : 0≤ orderedPathS (n+1) a.bf a.hf u := by
  by_cases hu0:u=0
  · subst u;simp only [orderedPathS,orderedPathPair_zero,le_refl]
  · exact (orderedPath_SK_bounds (n+1) (by omega) a.bf a.hf
      (a.data.bf_monotone a.alpha) (a.data.hf_monotone a.alpha)
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),hu.2⟩).1

theorem mass_mean_monotone
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    MonotoneOn (orderedPathS (n+1) a.bf a.hf) (Icc (0:ℝ) 1) := by
  intro u hu v hv huv
  by_cases hu0:u=0
  · subst u;simpa only [orderedPathS,orderedPathPair_zero] using a.mass_mean_nonneg hv
  · have huPos:0< u:=lt_of_le_of_ne hu.1 (Ne.symm hu0)
    exact (orderedPath_SK_monotone (n+1) (by omega) a.bf a.hf
      (a.data.bf_monotone a.alpha) (a.data.hf_monotone a.alpha)).1
      ⟨huPos,hu.2⟩ ⟨huPos.trans_le huv,hv.2⟩ huv

end ActualHighWallOverlapMinimum

theorem eventually_actual_high_wall_mass_mean_upper
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃B : ℝ,0 < B ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀u∈Ioc (0:ℝ) 1,orderedPathS (n+1) M.bf M.hf u ≤ B*(M.xs+u) := by
  obtain ⟨C,hC,hraw⟩ := eventually_actual_high_wall_original_boundary_raw
    1 Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have hshift : Tendsto (fun n:ℕ=>n+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k] with n hn
    omega
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hshift.eventually hraw] with n hnraw
  intro M u hu
  let up : PositiveMass := ⟨u,hu.1⟩
  obtain ⟨us,hus,huretain,_,hQ⟩ := hnraw M up hu.2 [] (by simp)
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
  have hbf : MonotoneOn M.bf (Icc (0:ℝ) 1) := M.data.bf_monotone M.alpha
  have hhf : MonotoneOn M.hf (Icc (0:ℝ) 1) := M.data.hf_monotone M.alpha
  have hretain j : ∃i≤(as j).length,partitionPoint 0 (as j) i=u :=
    cavity_partitionPoint_exists_of_mem (as j) (finiteCutMasses_nodes us j huretain) 0
  exact orderedPathS_le_retained_native_raw n 2 (by norm_num) M.bf M.hf hbf hhf
    as mesh ho he hmesh uniformMasses_mesh_tendsto hu.1 M.hxs hretain hQ'

theorem eventually_actual_high_wall_floor_mass_small
    {m delta cl cu Az C0 Ct D Bclock epsilon : ℝ}
    (hC0 : 0< C0) (hroom : 0<3*m+delta) (hepsilon : 0< epsilon) :
    ∀ᶠn : ℕ in atTop,∀a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀W : ℝ,a.xs≤ W→a.data.N^(-delta)*comparisonSmallMass a.data.N a.data.E≤ epsilon*W := by
  have H:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^3) (d:=epsilon) (q:=-(3*m+delta)) (r:=0)
      hepsilon (by linarith))
  filter_upwards [H] with n hn
  intro a W hxs
  have hW : 0< W:=a.hxs.trans_le hxs
  have hratio : comparisonSmallMass a.data.N a.data.E/W≤ C0^3*a.data.N^(-3*m):=
    (div_le_div_of_nonneg_left a.data.hU.le a.hxs hxs).trans (a.high_mass_small_ratio hC0)
  have Hmul:=mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg a.data.hN.le (-delta))
  have HE : a.data.N^(-delta)*(C0^3*a.data.N^(-3*m))=C0^3*a.data.N^(-(3*m+delta)):=by
    rw [←mul_assoc,mul_comm (a.data.N^(-delta)) (C0^3),mul_assoc,←Real.rpow_add a.data.hN]
    congr 2;ring
  rw [HE] at Hmul
  have HC : C0^3*a.data.N^(-(3*m+delta))≤ epsilon:=by
    simpa only [ActualHighWallData.N,Real.rpow_zero,mul_one] using hn
  have HH : (a.data.N^(-delta)*comparisonSmallMass a.data.N a.data.E)/W≤ epsilon:=by
    simpa only [mul_div_assoc] using Hmul.trans HC
  exact (div_le_iff₀ hW).mp HH

theorem eventually_actual_high_wall_small_mass_small
    {m delta cl cu Az C0 Ct D Bclock epsilon : ℝ}
    (hm : 0< m) (hC0 : 0< C0) (hepsilon : 0< epsilon) :
    ∀ᶠn : ℕ in atTop,∀a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀W : ℝ,a.xs≤ W→comparisonSmallMass a.data.N a.data.E≤ epsilon*W := by
  have H:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^3) (d:=epsilon) (q:=-3*m) (r:=0)
      hepsilon (by linarith))
  filter_upwards [H] with n hn
  intro a W hxs
  have hW : 0< W:=a.hxs.trans_le hxs
  have hratio : comparisonSmallMass a.data.N a.data.E/W≤ C0^3*a.data.N^(-3*m):=
    (div_le_div_of_nonneg_left a.data.hU.le a.hxs hxs).trans (a.high_mass_small_ratio hC0)
  have HC : C0^3*a.data.N^(-3*m)≤ epsilon:=by
    simpa only [ActualHighWallData.N,Real.rpow_zero,mul_one] using hn
  exact (div_le_iff₀ hW).mp (hratio.trans HC)
theorem eventually_actual_high_wall_floor_mass_polynomial
    {m delta cl cu Az C0 Ct D Bclock c1 : ℝ}
    (hC0 : 0 < C0) (hc1 : c1 < 3*m+delta) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀W : ℝ,M.xs ≤ W →
        M.data.N^(-delta)*(comparisonSmallMass M.data.N M.data.E) ≤ (1/2)*M.data.N^(-c1)*W := by
  have H := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^3) (d:=1/2)
      (q:=-(3*m+delta)) (r:=-c1) (by norm_num) (by linarith))
  filter_upwards [H] with n hn
  intro M W hxs
  have hW : 0 < W := M.hxs.trans_le hxs
  have hratio : (comparisonSmallMass M.data.N M.data.E)/W ≤ C0^3*M.data.N^(-3*m) :=
    (div_le_div_of_nonneg_left M.data.hU.le M.hxs hxs).trans
      (M.high_mass_small_ratio hC0)
  have Hmul := mul_le_mul_of_nonneg_left hratio
    (Real.rpow_nonneg M.data.hN.le (-delta))
  have He : M.data.N^(-delta)*(C0^3*M.data.N^(-3*m)) =
      C0^3*M.data.N^(-(3*m+delta)) := by
    rw [←mul_assoc,mul_comm (M.data.N^(-delta)) (C0^3),mul_assoc,
      ←Real.rpow_add M.data.hN]
    congr 2
    ring
  rw [He] at Hmul
  have Hcoeff : C0^3*M.data.N^(-(3*m+delta)) ≤ (1/2)*M.data.N^(-c1) := by
    simpa only [ActualHighWallData.N] using hn
  have Hratio' : (M.data.N^(-delta)*(comparisonSmallMass M.data.N M.data.E))/W ≤ (1/2)*M.data.N^(-c1) := by
    simpa only [mul_div_assoc] using Hmul.trans Hcoeff
  exact (div_le_iff₀ hW).mp Hratio'

end OAI.SKFluctuations.LaplaceWindowFormalization
