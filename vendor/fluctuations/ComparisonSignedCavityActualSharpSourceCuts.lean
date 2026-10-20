module

public import ComparisonSignedCavityActualSharpSlowWindowSequence
public import ComparisonSignedCavityActualCalibratedBandGeometry
public import ComparisonSignedCavityContinuumMixedClock

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 16000000

structure ActualSharpSourceCutGeometry
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℝ) (w : ActualSlowWindowChoice) (high outer : PositiveMass)
    (radius cFirst cK A : ℝ) : Prop where
  star_lt : w.star.val < high.val
  high_lt : high.val < outer.val
  outer_le_one : outer.val ≤ 1
  outer_scale : outer.val ≤ A*W
  first_high : 2*cFirst*W ≤ high.val
  radius_lower : W ≤ radius
  radius_upper : radius ≤ 1
  radius_high : radius ≤ M.R high.val
  star_radius : M.R w.star.val ≤ radius/2
  regular_radius : M.z ≤ radius/2
  clock_star : cK*W ≤ actualMixedClock (n+1) M.bf M.hf w.star.val

theorem exists_actual_sharp_source_cuts_along
    {m delta cl cu Az C0 Ct D Bclock Tstar L Cs : ℝ}
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hTstar : 0 < Tstar) (hL : 0 < L)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar L Cs (w n)) :
    ∃Ku Kv cFirst cK : ℝ,1 < Ku ∧ 1 ≤ Kv ∧ 0 < cFirst ∧
      2*cu*(Az+1) ≤ cFirst ∧ 0 < cK ∧∃high outer : ℕ→PositiveMass,
      (∀n,(high n).val=Ku*W n ∧ (outer n).val=(Ku+1)*W n) ∧
      ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cK (Ku+1) := by
  let a:=calibratedBandStart cu Az
  let b:=a+4*L
  let Kv:=1+2*(b/cl)
  let Ku:=2*a+b+cu*Kv+1
  let cK:=3*Tstar*(starMassBandConstant cu Az/cu)/8
  have ha : 0 < a:=calibrated_band_start_pos hcu hAz
  have hb : 0 < b:=by dsimp only [b];positivity
  have hv : 1 ≤ Kv:=by dsimp only [Kv];linarith [div_pos hb hcl]
  have hcuKv : 0 ≤ cu*Kv:=mul_nonneg hcu.le (zero_le_one.trans hv)
  have hu : 1 < Ku:=by dsimp only [Ku];linarith
  have hfirst : 2*cu*(Az+1) ≤ a:=by
    dsimp only [a,calibratedBandStart,starMassBandConstant]
    nlinarith
  have hcK : 0 < cK:=by
    have hc:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cK]
    positivity
  have hW n : 0 < W n:=(M n).hxs.trans_le (hxs n)
  let high (n:ℕ) : PositiveMass:=⟨Ku*W n,mul_pos (zero_lt_one.trans hu) (hW n)⟩
  let outer (n:ℕ) : PositiveMass:=⟨(Ku+1)*W n,mul_pos (by linarith) (hW n)⟩
  have Houter : ∀ᶠn in atTop,(Ku+1)*W n ≤ 1:=by
    have H:=hWlim.const_mul (Ku+1)
    simp only [mul_zero] at H
    exact H.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  have Hrad : ∀ᶠn in atTop,Kv*W n ≤ 1:=by
    have H:=hWlim.const_mul Kv
    simp only [mul_zero] at H
    exact H.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Ku,Kv,a,cK,hu,hv,ha,hfirst,hcK,high,outer,fun n=>⟨rfl,rfl⟩,?_⟩
  filter_upwards [hw,Houter,Hrad] with n hnSharp hnOuter hnRad
  have hWn:=hW n
  obtain ⟨p,hindex,_,hquarter,_,_,hnodes,hstar,_,_,_,_,_,hRhi,_,hz,hclock,_⟩:=hnSharp.1
  have hnode:=hnodes (4*(w n).index+3) (by omega)
  have hstarUpper : (w n).star.val ≤ b*W n:=by
    have H:=hstar.2
    have Hn:=hnode.2
    change NativeStarBuffer.massNode (a*W n) (w n).quarter (4*(w n).index+3) ≤ b*W n at Hn
    linarith
  have hKuB : b < Ku:=by dsimp only [Ku];linarith
  have hKuA : starMassBandConstant cu Az ≤ Ku:=by
    have hA:=star_mass_band_constant_pos hcu hAz
    have haa : starMassBandConstant cu Az ≤ a:=by dsimp only [a,calibratedBandStart];linarith
    dsimp only [Ku]
    have hkv0:0 ≤ cu*Kv:=mul_nonneg hcu.le (zero_le_one.trans hv)
    linarith
  have hHigh1 : Ku*W n ≤ 1:=by nlinarith only [hnOuter,hWn]
  have hRU:=(M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz hWn (hxs n)
    (a:=Ku) (b:=Ku) hKuA hHigh1 (show Ku*W n∈Icc (Ku*W n) (Ku*W n) from ⟨le_rfl,le_rfl⟩)
  have hKvKu : Kv ≤ Ku/cu:=by
    apply (le_div_iff₀ hcu).mpr
    dsimp only [Ku]
    linarith
  have hRstar : (M n).R (w n).star.val ≤ (Kv*W n)/2:=by
    have H : b/cl ≤ Kv/2:=by dsimp only [Kv];linarith
    have HH:=mul_le_mul_of_nonneg_right H hWn.le
    change (M n).R (w n).star.val ≤ (b/cl)*W n at hRhi
    nlinarith only [hRhi,HH]
  refine ⟨?_,?_,hnOuter,le_rfl,?_,?_,hnRad,?_,hRstar,?_,hclock⟩
  · change (w n).star.val < Ku*W n
    exact hstarUpper.trans_lt (mul_lt_mul_of_pos_right hKuB hWn)
  · change Ku*W n < (Ku+1)*W n
    nlinarith
  · change 2*a*W n ≤ Ku*W n
    apply mul_le_mul_of_nonneg_right _ hWn.le
    dsimp only [Ku]
    linarith
  · exact (one_mul (W n)).symm.trans_le (mul_le_mul_of_nonneg_right hv hWn.le)
  · exact (mul_le_mul_of_nonneg_right hKvKu hWn.le).trans hRU.1
  · have hR0 := comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha (w n).star.val
    nlinarith only [hz,hRstar,hR0.1]

end OAI.SKFluctuations.LaplaceWindowFormalization
