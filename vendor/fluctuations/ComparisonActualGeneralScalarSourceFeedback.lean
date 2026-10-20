module

public import ComparisonActualGeneralConstantJointFourNumerics
public import ComparisonActualGeneralDefectBootstrap

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set Filter MeasureTheory ProbabilityTheory LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 20000000

theorem actual_general_constant_joint_source_eq_original_mean_gap
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (star U : ℕ)
    (hs : star < U) (hU : U ≤ as.length) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n bf hf as
    actualGeneralConstantJointSource (n:=n) bf hf as star U=
      finitePhysicalMean (n+1) as b h star-nativeOriginalScalarPairMean as K star := by
  dsimp only [actualGeneralConstantJointSource]
  apply native_actual_constant_joint_source_eq_original_mean_gap n as star U hs hU ho
  · exact native_continuum_mixed_clock_eq_original_center n bf hf hbf hhf as ho
  · exact fun _=>NNReal.coe_nonneg _
  · exact fun _=>NNReal.coe_nonneg _
  · exact native_continuum_mixed_clock_nonneg n bf hf hbf hhf as ho
  · intro i j hij
    exact hbf (partitionPoint_mem as ho i) (partitionPoint_mem as ho j) (partitionPoint_mono as ho hij)
  · intro i j hij
    exact hhf (partitionPoint_mem as ho i) (partitionPoint_mem as ho j) (partitionPoint_mono as ho hij)
  · exact native_continuum_mixed_clock_monotone n bf hf hbf hhf as ho

theorem scalar_defect_times_mean_le_original_source
    {S K mean G b h chi d Ch Cr Cm : ℝ}
    (_hd : 0 ≤ d) (hh : 0 ≤ h) (hchi : chi∈Icc (0:ℝ) 1)
    (hK : K=h+b*S) (hS : 0 ≤ S)
    (hfield : h ≤ Ch*d^3) (hscalar : |G-chi^2*K| ≤ Cr*d^3)
    (hmesh : |mean-S| ≤ Cm*d^3) :
    |1-b*chi^2| *S ≤ |mean-G|+(Ch+Cr+Cm)*d^3 := by
  have hchi2 : chi^2 ≤ 1:=by nlinarith only [hchi.1,hchi.2]
  have hproduct : |chi^2*h| ≤ Ch*d^3:=by
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg chi) hh)]
    exact (mul_le_of_le_one_left hh hchi2).trans hfield
  have HE : (1-b*chi^2)*S=(S-mean)+(mean-G)+(G-chi^2*K)+chi^2*h:=by rw [hK];ring
  rw [←abs_of_nonneg hS,←abs_mul,HE]
  have H1:=abs_add_le ((S-mean)+(mean-G)+(G-chi^2*K)) (chi^2*h)
  have H2:=abs_add_le ((S-mean)+(mean-G)) (G-chi^2*K)
  have H3:=abs_add_le (S-mean) (mean-G)
  rw [abs_sub_comm S mean] at H3
  nlinarith only [H1,H2,H3,hmesh,hscalar,hproduct]

theorem actual_general_scalar_defect_feedback_on_grid
    {n : ℕ} {d Ch Cr Cm c : ℝ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (star U : ℕ)
    (hs : star < U) (hU : U ≤ as.length) (hd : 0 < d) (hc : 0 < c)
    (hmean : c*d ≤ nativePhysicalResourceCenter n bf hf as star)
    (hfield : (hf (partitionPoint 0 as star):ℝ) ≤ Ch*d^3)
    (hscalar :
      let K:=nativeContinuumMixedClock n bf hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |nativeOriginalScalarPairMean as K star-chi^2*K star| ≤ Cr*d^3)
    (hmesh : |finitePhysicalMean (n+1) as
      (fun j=>(bf (partitionPoint 0 as j):ℝ)) (fun j=>(hf (partitionPoint 0 as j):ℝ)) star-
        nativePhysicalResourceCenter n bf hf as star| ≤ Cm*d^3) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |1-(bf (partitionPoint 0 as star):ℝ)*chi^2| *(c*d) ≤
      |actualGeneralConstantJointSource (n:=n) bf hf as star U|+(Ch+Cr+Cm)*d^3 := by
  dsimp only at hscalar ⊢
  have Hchi:=actual_general_continuum_chi_mem_unit_on_any_grid (n:=n) bf hf hbf hhf as ho U
    (by omega) hU
  have HS : 0 ≤ nativePhysicalResourceCenter n bf hf as star:=
    (mul_pos hc hd).le.trans hmean
  have HK:=native_continuum_mixed_clock_eq_original_center n bf hf hbf hhf as ho star
  have HR:=scalar_defect_times_mean_le_original_source hd.le (NNReal.coe_nonneg _) Hchi HK HS
    hfield hscalar hmesh
  rw [←actual_general_constant_joint_source_eq_original_mean_gap (n:=n) bf hf hbf hhf as ho star U hs hU] at HR
  exact (mul_le_mul_of_nonneg_left hmean (abs_nonneg _)).trans HR

end OAI.SKFluctuations.Cavity
