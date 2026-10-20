module

public import ComparisonSignedCavityActualLowErrorTransport
public import ComparisonSignedCavityMinimumSourceClocks

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem actual_low_edgeBudget_mono {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    {f g : ℕ→ℝ} (hfg : ∀j,j ≤ as.length → f j ≤ g j) :
    ClockTree.edgeBudget a as f ≤ ClockTree.edgeBudget a as g := by
  induction as generalizing a f g with
  | nil => exact mul_le_mul_of_nonneg_left (hfg 0 le_rfl) (sub_nonneg.mpr ho.2)
  | cons b bs ih =>
    exact add_le_add (mul_le_mul_of_nonneg_left (hfg 0 (by simp)) (sub_nonneg.mpr ho.2.1))
      (ih ho.2.2 (fun j hj=>hfg (1+j) (by simp only [List.length_cons];omega)))

theorem actual_low_edgeBudget_linear (as : List PositiveMass) (a c d : ℝ) (f g : ℕ→ℝ) :
    ClockTree.edgeBudget a as (fun j=>c*f j+d*g j)=
      c*ClockTree.edgeBudget a as f+d*ClockTree.edgeBudget a as g := by
  induction as generalizing a f g with
  | nil => simp only [ClockTree.edgeBudget];ring
  | cons b bs ih => simp only [ClockTree.edgeBudget,ih];ring

theorem actual_low_edgeBudget_ones_le {as : List PositiveMass} (ho : MassOrdered 0 as)
    (U : ℕ) (hU : U ≤ as.length) :
    ClockTree.edgeBudget 0 as (fun j=>if j<U then (1:ℝ) else 0) ≤ 1 := by
  rw [native_low_edgeBudget_eq_prefix_cells as 0 U hU,massCellSum_const,massPartition_take_end]
  simpa only [sub_zero,mul_one] using (partitionPoint_mem as ho U).2

theorem actual_minimum_current_low_error_density_on_every_final_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (Temp C : ℝ) (hTemp : 0 ≤ Temp) (hC : 0 < C)
    (hbareb : ∀u,a.b u=Temp) (hbareh : ∀u,a.h u=0) (hxs1 : a.xs ≤ 1)
    (us : List PositiveMass) (hu : ∀u∈us,u.val ≤ 1) :
    ∀ᶠjGrid : ℕ in atTop,
      let as:=finiteCutMasses us jGrid
      let b:=fun j=>(a.bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(a.hf (partitionPoint 0 as j):ℝ)
      let S:=fun j=>orderedPathS (n+1) a.bf a.hf (partitionPoint 0 as j)
      let K:=fun j=>h j+b j*S j
      ∀U : ℕ,U ≤ as.length → partitionPoint 0 as U ≤ min (C*a.canonicalDirectTestBandScale) 1 →
      ∀l t : ℝ,l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        ClockTree.edgeBudget 0 as
          (nativeWholeLawErrorRadius n as
            (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
            (cutLowError n U b h K)) ≤
          actualLowErrorComparisonConstant (4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp) Temp*
            (a.actualOriginalLowErrorDensitySaving C*a.xs^2+1/(n+1:ℕ)) := by
  filter_upwards [a.actual_cut_low_error_edgeBudget_on_every_final_net C hC us hu] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U hU hmass l t hl ht
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(a.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(a.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) a.bf a.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let M:=4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp
  let E:=actualLowErrorComparisonConstant M Temp
  let R:=nativeOriginalCutLowErrorRadius n a.bf a.hf as
  let site:=(1/(n+1:ℕ):ℝ)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hu jGrid
  have had:=comparisonVariableEndpoint_clocks_admissible a.context.hc a.context.hk a.context.hkc
    a.context.hm a.context.hM a.b a.h a.context.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 a.alpha
  have hb:=toNNReal_monotoneOn had.1
  have hh:=toNNReal_monotoneOn had.2.1
  have hbond j (_hj : j ≤ as.length) : (a.bf (partitionPoint 0 as j):ℝ) ≤ Temp :=
    (a.bare_source_clock_bounds hcl hAz Temp hbareb hbareh (partitionPoint_mem as ho j)).2.1
  have Hfield:=(a.bare_source_clock_bounds hcl hAz Temp hbareb hbareh
    (partitionPoint_mem as ho as.length)).2.2.2
  have hCf:=NativeOverlapMinimum.bare_source_clock_constant_nonneg (D:=D) hcl hAz
  have Hsmall : h as.length ≤ 2*NativeOverlapMinimum.bareSourceClockConstant cl Az D := by
    have HH:=mul_le_mul_of_nonneg_left
      (show a.xs+partitionPoint 0 as as.length ≤ 2 by linarith [(partitionPoint_mem as ho as.length).2]) hCf
    exact Hfield.trans (by linarith only [HH])
  have HS:=(physicalOrderedPathS_mem_unit n a.bf a.hf hb hh (partitionPoint_mem as ho as.length)).2
  have Hmul:=mul_le_mul_of_nonneg_left HS (NNReal.coe_nonneg (a.bf (partitionPoint 0 as as.length)))
  have hclock : h as.length+b as.length*S as.length+b as.length+h as.length ≤ M := by
    have HB:=hbond as.length le_rfl
    dsimp only [b,h,S,M] at *
    linarith
  have Hmono:=actual_low_edgeBudget_mono ho (fun j hj=>
    native_actual_low_error_radius_le_original n U a.bf a.hf hb hh ho hl ht hTemp hbond hclock j hj)
  have heq : (fun j=>if j<U then E*(R j+site) else 0)=
      (fun j=>E*(if j<U then R j else 0)+(E*site)*(if j<U then 1 else 0)) := by
    funext j
    split_ifs <;> ring
  change ClockTree.edgeBudget 0 as _ ≤ ClockTree.edgeBudget 0 as
    (fun j=>if j<U then E*(R j+site) else 0) at Hmono
  rw [heq,actual_low_edgeBudget_linear] at Hmono
  have HD:=hgrid U hU hmass
  have HE : 0 ≤ E:=actualLowErrorComparisonConstant_nonneg M hTemp
  have Hfirst:=mul_le_mul_of_nonneg_left HD HE
  have Hsite:=mul_le_mul_of_nonneg_left (actual_low_edgeBudget_ones_le ho U hU)
    (show 0 ≤ E*site by dsimp [site];positivity)
  apply Hmono.trans ((add_le_add Hfirst Hsite).trans_eq _)
  dsimp only [E,M,site]
  ring

end OAI.SKFluctuations.Cavity
