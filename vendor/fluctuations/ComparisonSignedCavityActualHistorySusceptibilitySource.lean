module

public import ComparisonSignedCavityActualSusceptibilitySourceNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

theorem actual_selected_bad_history_susceptibility_bound_by_joint_source_along
    {m delta cl cu Az C0 Ct D Bclock T L Cs c0 A : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hA : 0 ≤ A)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hTemp : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cs (w n)) :
    ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀us : List PositiveMass,
      (∀u∈us,u.val ≤ 1)→(w n).star∈us→∀ᶠk : ℕ in atTop,
      ∀(before after : List PositiveMass) (a : PositiveMass),
        before++a::after=finiteCutMasses us k→∀V : ℕ,
        let as:=before++a::after
        let star:=retainedMassPrefixIndex (w n).star.val as
        let U:=before.length+1
        star < U→U ≤ V→V ≤ as.length→a.val < partitionPoint 0 as V→
        partitionPoint 0 as V ≤ A*W n→
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let S:=nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |(T-epsilon)*chi^2-1| ≤ C*(W n)^2+
          |nativeActualConstantJointStarSource (dim n) as star U b h K S|/
            ((3*(starMassBandConstant cu Az/cu)/4)*W n) := by
  obtain ⟨R,hR,HR⟩:=eventually_actual_selected_bad_history_original_continuum_scalar_remainder
    Bclock T A c0 (by linarith) hA hc0 hm hdelta hroom hcl hcu hAz hC0 hCt
    hmargin hcapmargin dim hdim root M epsilon shell hepsilon hb hh Hhistory W hxs hWlim
  let c:=starMassBandConstant cu Az/cu
  let Cr:=nativeScalarLowRemainderConstant A R R
  let C:=((c+1)/4+Cr+1)/(3*c/4)
  have hc : 0 < c:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
  have hCr : 0 ≤ Cr:=nativeScalarLowRemainderConstant_nonneg hA hR.le hR.le
  have hC : 0 < C:=by dsimp only [C];positivity
  have Htotal:=actual_selected_bad_history_total_clock_and_root dim root M
    epsilon shell hepsilon hb hh Hhistory
  refine ⟨C,hC,?_⟩
  filter_upwards [HR,Htotal,hw] with n hnR hnTotal hnSharp
  intro us hus hstar
  have hW : 0 < W n:=(M n).hxs.trans_le (hxs n)
  have HM:=nativeRetainedFinitePhysicalMean_tendsto (dim n) (M n).bf (M n).hf
    (M n).inherited_bf_monotone (M n).inherited_hf_monotone us hus (w n).star hstar
  have Hmean:=HM.eventually (Metric.ball_mem_nhds _ (pow_pos hW 3))
  filter_upwards [Hmean] with k hkMean
  intro before after a hgrid V
  dsimp only
  intro hs hUV hV hbuffer hsize
  let as:=before++a::after
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=before.length+1
  have ho : MassOrdered 0 as:=by
    dsimp only [as]
    rw [hgrid]
    exact finiteCutMasses_ordered us hus k
  have hstar' : (w n).star∈as:=by
    dsimp only [as]
    rw [hgrid]
    exact finiteCutMasses_nodes us k hstar
  have Hscalar:=hnR before after a ho star V hs hUV hV hbuffer hsize
    (ClockTree.single (S:=Spin (dim n)×Bool) as) 0 ho (singleSlot as)
  dsimp only at Hscalar
  rw [native_full_gamma_row_hessian (dim n) (ClockTree.single (S:=Spin (dim n)×Bool) as)
    ho 0 ho U (by dsimp [U];omega)] at Hscalar
  have Hmesh : |finitePhysicalMean (dim n+1) as
      (fun j=>((M n).bf (partitionPoint 0 as j):ℝ))
      (fun j=>((M n).hf (partitionPoint 0 as j):ℝ)) star-
      orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val| ≤ (W n)^3 := by
    dsimp only [as,star]
    rw [hgrid]
    exact (show |_ - _| < (W n)^3 by simpa only [Metric.mem_ball,Real.dist_eq] using hkMean).le
  exact actual_sharp_susceptibility_bound_by_joint_source (M n) hcu hAz hW hnTotal.1
    (w n) hnSharp as ho hstar' U hs (hUV.trans hV) Hmesh Hscalar

end OAI.SKFluctuations.LaplaceWindowFormalization
