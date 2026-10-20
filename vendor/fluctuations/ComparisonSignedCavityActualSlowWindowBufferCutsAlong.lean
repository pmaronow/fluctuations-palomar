module

public import ComparisonSignedCavityActualBufferEndpointGeometryAlong
public import ComparisonNativeStarMinimumCommonBuffers

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy NativeStarBuffer
set_option maxHeartbeats 8000000

namespace NativeOverlapMinimum

theorem eventually_actual_slow_window_buffer_cuts_along
    {m delta cl cu Az C0 Ct D Bclock L : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hL : 0 < L)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0)) :
    ∃K Cprof Rmacro Ddepth : ℝ,1 ≤ K ∧ 0 < Cprof ∧ 0 < Rmacro ∧ 0 < Ddepth ∧
      Rmacro ≤ 1/(4*K) ∧ ∀ᶠn : ℕ in atTop,
      ∀T Cs : ℝ,∀w : ActualSlowWindowChoice,IsActualCalibratedSlowWindow (M n) (W n) T L Cs w →
      ∃past future : ActualMinimumRetainedBufferCuts (M n)
        (2*actualSlowWindowExponent m delta) K Cprof Ddepth Rmacro,
        past.lo.val=massNode (calibratedBandStart cu Az*W n) w.quarter (4*w.index) ∧
        past.hi.val=massNode (calibratedBandStart cu Az*W n) w.quarter (4*w.index+1) ∧
        future.lo.val=massNode (calibratedBandStart cu Az*W n) w.quarter (4*w.index+3) ∧
        future.hi.val=massNode (calibratedBandStart cu Az*W n) w.quarter (4*(w.index+1)) ∧
        past.hi.val-past.lo.val=w.quarter ∧ future.hi.val-future.lo.val=w.quarter := by
  have hc1 := actualSlowWindowExponent_pos hm hdelta hroom
  obtain ⟨K,Cprof,Rmacro,Ddepth,hK,hCp,hRm,hDd,hmacro,HG⟩ :=
    eventually_actual_buffer_endpoint_geometry_along hm hcl hcu hAz hC0 hL hc1 dim hdim M W hxs hWlim
  refine ⟨K,Cprof,Rmacro,Ddepth,hK,hCp,hRm,hDd,hmacro,?_⟩
  filter_upwards [HG] with n hn
  intro T Cs w hw
  obtain ⟨p,hi,hN,hq,hqlower,htotal,hnodes,_⟩ := hw
  let start := calibratedBandStart cu Az*W n
  have hcut : ∀j : ℕ,j+1 ≤ 4*w.blocks →
      ∃cut : ActualMinimumRetainedBufferCuts (M n)
        (2*actualSlowWindowExponent m delta) K Cprof Ddepth Rmacro,
        cut.lo.val=massNode start w.quarter j ∧
        cut.hi.val=massNode start w.quarter (j+1) ∧ cut.hi.val-cut.lo.val=w.quarter := by
    intro j hj
    have hlo := hnodes j (by omega)
    have hhi := hnodes (j+1) hj
    have hgap : massNode start w.quarter (j+1)-massNode start w.quarter j=w.quarter := by
      unfold massNode
      push_cast
      ring
    have hlt : massNode start w.quarter j < massNode start w.quarter (j+1) := by
      linarith only [hgap,hq]
    have hwidth : (M n).context.N^(-actualSlowWindowExponent m delta)*W n ≤
        massNode start w.quarter (j+1)-massNode start w.quarter j := by rw [hgap];exact hqlower
    obtain ⟨hlopos,hhi1,hxslo,hzlo,_,hratio,hmass,hcaproom,hroom,hwidth',hmassupper,
      J,hJ,hreach,hdyadic,hdepth⟩ := hn (massNode start w.quarter j)
        (massNode start w.quarter (j+1)) hlo hhi hlt.le hwidth
    let lo : PositiveMass := ⟨massNode start w.quarter j,hlopos⟩
    let hi : PositiveMass := ⟨massNode start w.quarter (j+1),hlopos.trans hlt⟩
    have hdepth' : (J:ℝ) ≤ Ddepth*Real.log ((dim n+1:ℕ):ℝ) := by
      have H : (J:ℝ) ≤ ((J+3:ℕ):ℝ) := by exact_mod_cast Nat.le_add_right J 3
      exact H.trans hdepth
    let cut : ActualMinimumRetainedBufferCuts (M n)
        (2*actualSlowWindowExponent m delta) K Cprof Ddepth Rmacro := {
      lo:=lo,hi:=hi,ordered:=hlt,high_le_one:=hhi1,
      scale_lower:=hxslo,regular_lower:=hzlo,room:=hroom,radius_ratio:=hratio,
      cap_mass:=hmass,cap_room:=hcaproom,mass_upper:=hmassupper,mass_lower:=hwidth',
      height:=J,height_pos:=hJ,reach:=hreach,dyadic_room:=hdyadic,height_bound:=hdepth' }
    exact ⟨cut,rfl,rfl,hgap⟩
  obtain ⟨past,hplo,hphi,hpgap⟩ := hcut (4*w.index) (by omega)
  obtain ⟨future,hflo,hfhi,hfgap⟩ := hcut (4*w.index+3) (by omega)
  refine ⟨past,future,hplo,hphi,hflo,?_,hpgap,hfgap⟩
  convert hfhi using 1

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
