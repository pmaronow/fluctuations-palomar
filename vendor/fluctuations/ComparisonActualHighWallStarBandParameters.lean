module

public import ComparisonActualHighWallStarCapCover
public import ComparisonActualHighWallStarClockDistinct

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000

theorem eventually_actual_high_wall_star_band_parameters
    {m delta cl cu Az C0 Ct D Bclock A : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az)
    (hC0 : 0< C0) (hA : cu*Az< A)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤ W n)
    (hs : Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0)) :
    ∀ᶠn in atTop,
      (M n).data.s< A*W n ∧ cu*Az*(M n).xs< A*W n ∧
      (M n).cavityCapTravel≤(A*W n)/(2*cu) ∧
      (M n).cavityCapTravel≤((A*W n)/cu-Az*(M n).xs)/2 ∧
      comparisonSmallMass (M n).data.N (M n).data.E≤(cl/(2*cu))*(A*W n) ∧
      4*(M n).data.s≤(cl/(4*cu))*(A*W n) ∧
      (M n).data.rmin+(M n).cavityCapTravel≤(A/(2*cu))*W n := by
  have hA0 : 0< A:=(mul_nonneg hcu.le hAz).trans_lt hA
  have hroom : 0<3*m+delta:=by linarith
  let low:=A/(4*cu)
  let gap:=(A/cu-Az)/4
  let Ucap:=min (cl*A/(2*cu)) low
  have hlow : 0< low:=by dsimp only [low];positivity
  have hgap : 0< gap:=by
    have HG : Az< A/cu:=(lt_div_iff₀ hcu).mpr (by nlinarith only [hA])
    dsimp only [gap];linarith
  have hUcap : 0< Ucap:=lt_min (by positivity) hlow
  have HTlow:=(tendsto_add_atTop_nat 1).eventually
    (eventually_actual_high_wall_cap_travel_small (m:=m) (delta:=delta) (cl:=cl) (cu:=cu)
      (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hC0 hroom hlow)
  have HTgap:=(tendsto_add_atTop_nat 1).eventually
    (eventually_actual_high_wall_cap_travel_small (m:=m) (delta:=delta) (cl:=cl) (cu:=cu)
      (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hC0 hroom hgap)
  have HU:=eventually_actual_high_wall_small_mass_small (m:=m) (delta:=delta) (cl:=cl) (cu:=cu)
    (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0 hUcap
  have HSlow:=hs.eventually (gt_mem_nhds (show (0:ℝ)< A/2 by positivity))
  have HScap:=hs.eventually (gt_mem_nhds (show (0:ℝ)< cl*A/(16*cu) by positivity))
  filter_upwards [HTlow,HTgap,HU,HSlow,HScap] with n htlow htgap hu hslow hscap
  have hW : 0< W n:=(M n).hxs.trans_le (hxs n)
  have hts : (M n).cavityCapTravel≤ low*W n:=
    (htlow (M n)).1.trans (mul_le_mul_of_nonneg_left (hxs n) hlow.le)
  have htg : (M n).cavityCapTravel≤ gap*W n:=
    (htgap (M n)).1.trans (mul_le_mul_of_nonneg_left (hxs n) hgap.le)
  have hus : comparisonSmallMass (M n).data.N (M n).data.E≤ Ucap*W n:=hu (M n) (W n) (hxs n)
  have hslow' := (div_lt_iff₀ hW).mp hslow
  have hscap' := (div_lt_iff₀ hW).mp hscap
  have hgpoint : cu*Az*(M n).xs< A*W n:=
    (mul_le_mul_of_nonneg_left (hxs n) (mul_nonneg hcu.le hAz)).trans_lt
      (mul_lt_mul_of_pos_right hA hW)
  have hUT : comparisonSmallMass (M n).data.N (M n).data.E≤ low*W n:=hus.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hW.le)
  have hUC : comparisonSmallMass (M n).data.N (M n).data.E≤(cl/(2*cu))*(A*W n):=by
    have HX:=hus.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hW.le)
    convert HX using 1;ring
  have hroomwall : (M n).data.rmin+(M n).cavityCapTravel≤(A/(2*cu))*W n:=by
    have HR:=(M n).radius_le_smallMass.trans hUT
    dsimp only [low] at HR hts
    have HE : A/(2*cu)=2*(A/(4*cu)):=by field_simp;ring
    rw [HE];linarith
  refine ⟨by nlinarith only [hslow',mul_pos hA0 hW],hgpoint,?_,?_,hUC,?_,hroomwall⟩
  · have HE : (A*W n)/(2*cu)=2*(low*W n):=by dsimp only [low];ring
    rw [HE]
    linarith [mul_pos hlow hW]
  · have HX:=mul_le_mul_of_nonneg_left (hxs n) hAz
    have HE : ((A*W n)/cu-Az*W n)/2=2*(gap*W n):=by dsimp only [gap];ring
    have HP : 0<gap*W n:=mul_pos hgap hW
    have HH : (M n).cavityCapTravel≤2*(gap*W n):=by linarith
    rw [←HE] at HH
    exact HH.trans (div_le_div_of_nonneg_right (sub_le_sub_left HX _) (by norm_num))
  · have HE : (cl/(4*cu))*(A*W n)=4*((cl*A/(16*cu))*W n):=by ring
    rw [HE];linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
