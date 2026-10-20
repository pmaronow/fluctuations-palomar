module

public import ComparisonActualHighWallScalarRemainderAlong
public import ComparisonActualHighWallFeedbackField
public import ComparisonActualGeneralScalarSourceFeedback
public import ComparisonActualHighWallSlowWindowData
public import ComparisonActualHighWallOriginalMeanCorrectionAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

 theorem eventually_actual_high_wall_original_scalar_feedback_at_calibrated_star_along
    (Bclock Cmass A : ℝ) (hCm : 0 ≤ Cmass) (hA : 0 ≤ A)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃R : ℝ,0 < R ∧ ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d → R*M.data.d ≤ 1 →
      ∀(L Cs : ℝ) (w : ActualSlowWindowChoice),
        ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow M M.data.d L Cs w →
      ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → w.star∈us →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let star:=retainedMassPrefixIndex w.star.val as
        ∀(U V : ℕ),star < U → U ≤ V → V ≤ as.length →
          M.data.s ≤ partitionPoint 0 as U →
          partitionPoint 0 as U < partitionPoint 0 as V →
          partitionPoint 0 as V ≤ A*M.data.d →
          partitionPoint 0 as star ≤ Cmass*M.data.d →
        let K:=nativeContinuumMixedClock (dim n) M.bf M.hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2| *
          ((3*(starMassBandConstant cu Az/cu)/4)*M.data.d) ≤
            |actualGeneralConstantJointSource (n:=dim n) M.bf M.hf as star U|+C*M.data.d^3 := by
  obtain ⟨R,hR,HR⟩:=eventually_actual_high_wall_original_scalar_remainder_of_buffer_along
    (D:=D) Bclock A hA hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  let Ch:=1/16+(Az+1/cl)*(1+Cmass)
  let Cr:=nativeScalarLowRemainderConstant A R R
  let C:=Ch+Cr+1
  have hCh : 0 < Ch:=by dsimp only [Ch];positivity
  have hCr : 0 ≤ Cr:=nativeScalarLowRemainderConstant_nonneg hA hR.le hR.le
  have hc : 0 < 3*(starMassBandConstant cu Az/cu)/4:=by
    have HC:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    positivity
  refine ⟨R,hR,C,by dsimp only [C];linarith,?_⟩
  filter_upwards [HR] with n hnR
  intro M hwork hsmall L Cs w hw us hus hstar
  obtain ⟨P,hi,hblocks,hq,hqlow,htotal,hNodes,hstarBand,hH,hThermal,hSlo,hShi,
    hRlo,hRhi,hxs,hz,hK,hGap,hosc⟩:=hw
  have Hmesh:=eventually_native_finite_physical_mean_uniform_center (dim n) M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) (M.data.root_field_zero M.alpha)
    us hus (M.data.d^3) (pow_pos M.data.hd 3)
  filter_upwards [Hmesh] with k hkMesh
  dsimp only at hkMesh ⊢
  intro U V hs hUV hV hhigh hbuffer hsize hmass
  let as:=finiteCutMasses us k
  let star:=retainedMassPrefixIndex w.star.val as
  have ho:=finiteCutMasses_ordered us hus k
  have hU : U ≤ as.length:=hUV.trans hV
  have Hscalar:=hnR M hwork as ho M.data.d M.data.hd.le hwork.le hsmall
    star U V hs hUV hV hhigh hbuffer hsize
  have Hfield:=M.field_clock_cubic_of_low_source_mass hcl hAz hCm hwork
    (partitionPoint_mem as ho star) hmass
  have Hcenter : nativePhysicalResourceCenter (dim n) M.bf M.hf as star=
      orderedPathS (dim n+1) M.bf M.hf w.star.val:=by
    unfold nativePhysicalResourceCenter
    rw [←native_ordered_source_center_eq_completed (dim n) M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) (partitionPoint_mem as ho star)]
    rw [nativeRetainedCut_partitionPoint as ho w.star (finiteCutMasses_nodes us k hstar)]
  have Hmean : (3*(starMassBandConstant cu Az/cu)/4)*M.data.d ≤
      nativePhysicalResourceCenter (dim n) M.bf M.hf as star:=by rw [Hcenter];exact hSlo
  have Hmesh' : |finitePhysicalMean (dim n+1) as
      (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) star-
        nativePhysicalResourceCenter (dim n) M.bf M.hf as star| ≤ 1*M.data.d^3:=by
    simpa only [one_mul] using hkMesh star (hs.le.trans hU)
  have HF:=actual_general_scalar_defect_feedback_on_grid (n:=dim n) M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho star U hs hU
    M.data.hd hc Hmean Hfield Hscalar Hmesh'
  exact HF

end OAI.SKFluctuations.Cavity
