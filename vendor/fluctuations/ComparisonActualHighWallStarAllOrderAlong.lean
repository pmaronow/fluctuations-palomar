module

public import ComparisonActualHighWallBufferedSequenceAlong
public import ComparisonActualHighWallCanonicalProjectionGeometryAlong
public import ComparisonActualHighWallBufferedSequence
public import ComparisonActualHighWallCanonicalProjectionGeometry
public import ComparisonActualHighWallStarProjectionMoment
public import ComparisonNativeStarActualAllOrder

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeStarBuffer NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000
attribute [local instance] Classical.propDecidable

def ActualHighWallStarOrderSavingAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (p : ℕ) (Craw saving : ℝ)
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,
    ∀extra : List PositiveMass,(∀u∈extra,u.val ≤ 1) →
    ∃us : List PositiveMass,(∀u∈us,u.val ≤ 1) ∧ (∀u∈extra,u∈us) ∧ (w n).star∈us ∧
      ∀ᶠj : ℕ in atTop,
        let as := finiteCutMasses us j
        let q := completedPathClock (dim n+1) (M n).bf (M n).hf
        let steps := sampleClockSteps q 0 as
        (physicalRawRatio (dim n+1) (p+1) steps 0 (M n).xs
          (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id)^2 ≤ 2*Craw ∧
        nativeRetainedCenteredMoment (dim n) (p+1) (M n).bf (M n).hf as (w n).star.val
          (orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val) ≤
            (((dim n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1))

theorem eventually_actual_high_wall_star_order_at_slow_window_along
    (p : ℕ) {m delta cl cu Az C0 Ct D Bclock L : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hL : 0 < L)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hWlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow (M n) ((M n).data.d) L Cs (w n)) :
    ∃Craw : ℝ,0 < Craw ∧ ActualHighWallStarOrderSavingAlong p Craw
      (actualSlowWindowExponent m delta/64) dim M (fun n=>(M n).data.d) w := by
  let W := fun n=>(M n).data.d
  let c := actualSlowWindowExponent m delta
  have hc : 0 < c := actualSlowWindowExponent_pos hm hdelta hroom
  have Hc := (actualSlowWindowExponent_bounds hm hdelta).2.2
  have hprojection : 2*(c/8) < 3*m-delta-3*c := by linarith
  have hxs n : (M n).xs ≤ W n := by change (M n).xs ≤ (M n).data.d;rw [hfixed n]
  have hW n : 0 < W n := (M n).hxs.trans_le (hxs n)
  obtain ⟨Craw,hCraw,Hbuffer⟩ := eventually_actual_high_wall_slow_window_buffers_along p
    hm hdelta hroom hcl hcu hAz hC0 hCt hL dim hdim M W hxs (fun _=>le_rfl) hWlim w hw
  obtain ⟨Kv,Cprof,Lcount,H0,hKv,hCprof,hLcount,hH0,Hgeometry⟩ :=
    ActualHighWallOverlapMinimum.eventually_actual_high_wall_fixed_canonical_projection_geometry_along hm hdelta hroom hcl hcu hAz hC0 hL
      dim hdim M hfixed hWlim
  have Hkv := ((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_coefficient_rpow_le (c:=Kv) (d:=1) (q:=-(c/8)) (r:=-(c/16))
      zero_lt_one (by linarith))
  have Hproject := ((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_actual_high_wall_original_projection_moment p Bclock
      (cl:=cl) (cu:=cu) (Az:=Az) (Ddepth:=D)
      (c1:=3*c) (saving:=c/8) hm hC0 hCt hCprof.le hLcount.le
      (by positivity : 0 ≤ 2*Craw) hH0.le hprojection)
  have Hconstant := hdim.eventually (eventually_star_pair_constant_absorbed p (actualBufferedStarPairConstant p Cs) hc)
  refine ⟨Craw,hCraw,?_⟩
  filter_upwards [Hbuffer,Hgeometry,Hproject,Hkv,Hconstant,hw] with n hnBuffer hnGeom hnProj hnKv hnConst hnWindow
  intro extra hextra
  have hWn : 0 < W n := hW n
  have hN1 : (1:ℝ) ≤ ((dim n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos (dim n)
  obtain ⟨us,hus,hretain,hbudget⟩ := hnBuffer extra hextra
  obtain ⟨p0,p1,p3,p4,hp0,hp1,hp3,hp4,hr0,hr1,hr3,hr4,hrstar,Hdata⟩ := hbudget
  obtain ⟨_,_,_,hxv,hv1,HG⟩ := hnGeom
  have Hgeom := HG Cs (w n) hnWindow p3 hp3 us hus hrstar hr3
  obtain ⟨potential,_,_,_,_,_,_,_,_,_,hSlo,hShi,_⟩ := hnWindow
  have hbf := (M n).data.bf_monotone (M n).alpha
  have hhf := (M n).data.hf_monotone (M n).alpha
  have hSnonneg : 0 ≤ orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val := by
    have hcstar : 0 < starMassBandConstant cu Az/cu := div_pos (star_mass_band_constant_pos hcu hAz) hcu
    exact (mul_pos (by positivity : 0 < 3*(starMassBandConstant cu Az/cu)/4) (hW n)).le.trans hSlo
  have hSabs : |orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val| ≤ Cs*W n := by
    rw [abs_of_nonneg hSnonneg]
    exact hShi
  have hScaled : ((dim n+1:ℕ):ℝ)^(-(c/8))*(Kv*W n) ≤ ((dim n+1:ℕ):ℝ)^(-(c/16))*W n := by
    have H := mul_le_mul_of_nonneg_right hnKv (hW n).le
    simpa only [one_mul,mul_assoc,mul_left_comm,mul_comm,Function.comp_def] using H
  refine ⟨us,hus,hretain,hrstar,?_⟩
  filter_upwards [Hdata,Hgeom] with j hj hjGeom
  let as := finiteCutMasses us j
  let ho := finiteCutMasses_ordered us hus j
  let q := completedPathClock (dim n+1) (M n).bf (M n).hf
  let steps := sampleClockSteps q 0 as
  let fork := (physicalRetainedIndex steps (w n).star.val).val
  let t := (physicalRetainedIndex steps p3.val).val
  let S := orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val
  let epsilon := ((dim n+1:ℕ):ℝ)^(-(c/16))
  obtain ⟨B,_,_,hCm,hCp,hEta,hRaw⟩ := hj
  have hProj := hnProj (M n) as ho fork t (H0/(Kv*W n)) (Kv*W n)
    ((M n).data.N^(-(3*c))) (by positivity) hxv hv1 le_rfl hjGeom hRaw
  have hProjW : physicalOverlapProjectionErrorMoment (dim n+1) (p+1) steps
      (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id fork t ≤
        (epsilon*W n)^(2*(p+1)) := by
    exact hProj.trans (pow_le_pow_left₀ (by positivity) hScaled _)
  have heps : 0 < epsilon := by dsimp only [epsilon];positivity
  have heps1 : epsilon ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    hN1 (by linarith)
  have Hstar := physical_star_from_buffer_data_polynomial (dim n+1) (p+1) (by omega)
    steps (sampleClockSteps_ordered q as ho) (q 0) fork t S B heps heps1 (hW n).le hCs.le
    hSabs hCm hCp hEta hProjW
  have Hnative := nativeRetainedCenteredMoment_eq_physicalStar (dim n) (p+1) (M n).bf (M n).hf
    hbf hhf as ho (w n).star.val S
  refine ⟨hRaw,?_⟩
  rw [Hnative]
  exact Hstar.trans (hnConst (W n) (hW n).le)

end OAI.SKFluctuations.LaplaceWindowFormalization
