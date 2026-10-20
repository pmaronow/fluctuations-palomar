module

public import ComparisonSignedCavityScalarRelocatedSchedule
public import ActualMixedClockCDF

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity GaussianCalculus Scalar
set_option maxHeartbeats 5000000

def nativeOriginalScalarPairMean (as : List PositiveMass) (q : ℕ→ℝ) (j : ℕ) : ℝ :=
  (ClockTree.pairClock (S:=Bool) as j).disorderExpect
    (fun _=>(1/2:ℝ)) scalarFeature (fun _=>0) (fun k _=>q k)
    (fun sigma=>scalarFeature (ClockTree.pairSpin as j sigma).1 (fun _=>1)*
      scalarFeature (ClockTree.pairSpin as j sigma).2 (fun _=>1)) 0

theorem scalarSmallClockFluxConstant_covariance_rescale
    {T A R : ℝ} (hT : 0<T) :
    scalarSmallClockFluxConstant T A (R/T)=scalarSmallClockFluxConstant 1 A R := by
  have hlin : scalarThirdMomentConstant T=T*scalarThirdMomentConstant 1 := by
    unfold scalarThirdMomentConstant
    ring
  unfold scalarSmallClockFluxConstant
  rw [hlin,abs_mul,abs_of_pos hT]
  field_simp [hT.ne']

def nativeScalarLowRemainderConstant (A R Ru : ℝ) : ℝ :=
  scalarSmallClockFluxConstant 1 A R*R^2+68*A*Ru*R

theorem nativeScalarLowRemainderConstant_nonneg {A R Ru : ℝ}
    (hA : 0≤A) (hR : 0≤R) (hRu : 0≤Ru) :
    0≤nativeScalarLowRemainderConstant A R Ru := by
  unfold nativeScalarLowRemainderConstant scalarSmallClockFluxConstant
  positivity

theorem scalarBoundaryClocks_quantile_at_cut_lower
    {l : ℝ} (as : List PositiveMass) (ho : MassOrdered l as)
    (q : ℕ → ℝ) (hq : Monotone q) (j : ℕ) (hj : j ≤ as.length) :
    q j ≤ scheduleRadiusQuantile (q 0) (scalarBoundaryClocks as q) (partitionPoint l as j) := by
  induction as generalizing l q j with
  | nil =>
    have hj0 : j=0 := by simpa using hj
    subst j
    simp [scalarBoundaryClocks,scheduleRadiusQuantile,heatSteps,stepClockFunction]
  | cons a as ih =>
    cases j with
    | zero => exact scheduleRadiusQuantile_lower _ _ _
    | succ j =>
      have hj' : j ≤ as.length := by simpa using hj
      have hq' : Monotone (fun k=>q (k+1)) := hq.comp (monotone_id.add_const 1)
      have H:=ih ho.2.2 (fun k=>q (k+1)) hq' j hj'
      have hmass := (partitionPoint_mem as ho.2.2 j).1
      change q (j+1) ≤ scheduleRadiusQuantile (q 0)
        (⟨a.val,a.property,Real.toNNReal (q 1-q 0)⟩::
          scalarBoundaryClocks as (fun k=>q (k+1))) (partitionPoint a.val as j)
      rw [scheduleRadiusQuantile_cons,ite_eq_left hmass]
      have he : q 0+((q 1-q 0).toNNReal:ℝ)=q 1 := by
        rw [Real.coe_toNNReal _ (sub_nonneg.mpr (hq (by omega : 0 ≤ 1)))]
        ring
      rw [he]
      exact H

theorem nativeScalarClockProfile_mass_cap_of_buffer
    {T A W : ℝ} (hT : 0 < T) (as : List PositiveMass) (ho : MassOrdered 0 as)
    (q : ℕ → ℝ) (hq : Monotone q) (hq0 : q 0=0) (htotal : q as.length=T)
    (U V : ℕ) (hV : V ≤ as.length) (hgap : q U < q V)
    (hmass : partitionPoint 0 as V ≤ A*W) :
    (nativeScalarClockProfile hT as q hq hq0 htotal).val (q U/T) ≤ A*W := by
  let cs:=scalarBoundaryClocks as q
  have hd : (scheduleDuration cs:ℝ)=T := by
    rw [scalarBoundaryClocks_duration as q hq,hq0,sub_zero,htotal]
  have hb : ∀v∈Icc (0:ℝ) 1,normalizedScheduleQuantile T 0 cs v∈Icc (0:ℝ) 1 :=
    normalizedScheduleQuantile_bounds hT le_rfl cs (by linarith [hd])
  have H:=scalarBoundaryClocks_quantile_at_cut_lower as ho q hq V hV
  rw [hq0] at H
  have hclock : q U/T < normalizedScheduleQuantile T 0 cs (partitionPoint 0 as V) := by
    exact (div_lt_div_of_pos_right (hgap.trans_le H) hT)
  have hcap:=quantileMassProfile_le_of_larger_clock
    (normalizedScheduleQuantile T 0 cs)
    ((normalizedScheduleQuantile_monotone hT.le cs).monotoneOn _) hb
    (partitionPoint_mem as ho V) hclock
  exact hcap.trans hmass

theorem partitionPoint_after_before_one (l : ℝ)
    (before after : List PositiveMass) (a : PositiveMass) :
    partitionPoint l (before++a::after) (before.length+1)=a.val := by
  induction before generalizing l with
  | nil => simp [partitionPoint,partitionValues]
  | cons b before ih =>
    change partitionPoint b.val (before++a::after) (before.length+1)=a.val
    exact ih b.val

theorem native_scalar_pair_low_remainder_of_buffer
    {T W A R Ru : ℝ} (hT : 0 < T)
    (before after : List PositiveMass) (a : PositiveMass)
    (ho : MassOrdered 0 (before++a::after)) (q : ℕ → ℝ) (hq : Monotone q)
    (hq0 : q 0=0) (htotal : q (before++a::after).length=T)
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hR : 0 ≤ R) (hRu : 0 ≤ Ru)
    (j V : ℕ) (hj : j < before.length+1) (hUV : before.length+1 ≤ V)
    (hV : V ≤ (before++a::after).length) (hgap : q (before.length+1) < q V)
    (hsize : partitionPoint 0 (before++a::after) V ≤ A*W)
    (hjclock : q j ≤ R*W) (hUclock : q (before.length+1) ≤ Ru*W) (hsmall : q j ≤ 1) :
    |(ClockTree.pairClock (S:=Bool) (before++a::after) j).disorderExpect
        (fun _=>(1/2:ℝ)) scalarFeature (fun _=>0) (fun k _=>q k)
        (fun sigma=>scalarFeature (ClockTree.pairSpin (before++a::after) j sigma).1 (fun _=>1)*
          scalarFeature (ClockTree.pairSpin (before++a::after) j sigma).2 (fun _=>1)) 0-
      ((scalarTerminal.schedule (scalarBoundaryClocks (before++a::after)
        (relocatedClock (before.length+1) 0 q))).H 0 0)^2*q j| ≤
      T^2*(scalarSmallClockFluxConstant T A (R/T)*(R/T)^2+
        68*A*(Ru/T)*(R/T))*W^3 := by
  let as:=before++a::after
  let U:=before.length+1
  let alpha:=nativeScalarClockProfile hT as q hq hq0 htotal
  have hU : U ≤ as.length := hUV.trans hV
  have hjlen : j ≤ as.length := hj.le.trans hU
  have hq0' k : 0 ≤ q k := by rw [←hq0];exact hq (by omega)
  have hqU : q U ≤ T := by rw [←htotal];exact hq hU
  have hmass:=nativeScalarClockProfile_mass_cap_of_buffer hT as ho q hq hq0 htotal
    U V hV hgap hsize
  have ha : a.val ≤ A*W := by
    have H:=partitionPoint_mono as ho hUV
    rw [partitionPoint_after_before_one] at H
    exact H.trans hsize
  have ha1 : a.val ≤ 1 := ho.members_le_one a (by simp)
  have H:=scalarCovarianceResponse_low_flattened_taylor hT alpha hW hA
    (div_nonneg hR hT.le) (div_nonneg hRu hT.le)
    (div_nonneg (hq0' j) hT.le)
    (div_le_div_of_nonneg_right (hq hj.le) hT.le)
    ((div_le_one₀ hT).mpr hqU)
    ((div_le_div_of_nonneg_right hjclock hT.le).trans_eq (by ring))
    ((div_le_div_of_nonneg_right hUclock hT.le).trans_eq (by ring))
    (by rw [mul_div_cancel₀ _ hT.ne'];exact hsmall)
    a.property ha1 ha hmass (nativeScalarClockProfile_right_continuous hT as q hq hq0 htotal)
  rw [mul_div_cancel₀ _ hT.ne'] at H
  rw [native_scalar_pairClock_eq_schedule_response hT as ho q hq hq0 htotal j hjlen,
    native_relocated_hessian_eq_low_flattened hT before after a ho q hq hq0 htotal]
  exact H

theorem native_scalar_pair_low_remainder_uniform_of_buffer
    {T W A R Ru : ℝ} (hT : 0<T)
    (before after : List PositiveMass) (a : PositiveMass)
    (ho : MassOrdered 0 (before++a::after)) (q : ℕ→ℝ) (hq : Monotone q)
    (hq0 : q 0=0) (htotal : q (before++a::after).length=T)
    (hW : 0≤W) (hA : 0≤A) (hR : 0≤R) (hRu : 0≤Ru)
    (j V : ℕ) (hj : j<before.length+1) (hUV : before.length+1≤V)
    (hV : V≤(before++a::after).length) (hgap : q (before.length+1)<q V)
    (hsize : partitionPoint 0 (before++a::after) V≤A*W)
    (hjclock : q j≤R*W) (hUclock : q (before.length+1)≤Ru*W) (hsmall : q j≤1) :
    |nativeOriginalScalarPairMean (before++a::after) q j-
      ((scalarTerminal.schedule (scalarBoundaryClocks (before++a::after)
        (relocatedClock (before.length+1) 0 q))).H 0 0)^2*q j|≤
        nativeScalarLowRemainderConstant A R Ru*W^3 := by
  have H:=native_scalar_pair_low_remainder_of_buffer hT before after a ho q hq hq0 htotal
    hW hA hR hRu j V hj hUV hV hgap hsize hjclock hUclock hsmall
  rw [scalarSmallClockFluxConstant_covariance_rescale hT] at H
  have he : T^2*(scalarSmallClockFluxConstant 1 A R*(R/T)^2+
      68*A*(Ru/T)*(R/T))=nativeScalarLowRemainderConstant A R Ru := by
    unfold nativeScalarLowRemainderConstant
    field_simp [hT.ne']
  rw [he] at H
  exact H

theorem native_gamma_row_scalar_low_remainder_of_buffer
    (n : ℕ) {T W A R Ru : ℝ} (hT : 0<T)
    (before after : List PositiveMass) (a : PositiveMass)
    (ho : MassOrdered 0 (before++a::after)) (q : ℕ→ℝ) (hq : Monotone q)
    (hq0 : q 0=0) (htotal : q (before++a::after).length=T)
    (hW : 0≤W) (hA : 0≤A) (hR : 0≤R) (hRu : 0≤Ru)
    (j V : ℕ) (hj : j<before.length+1) (hUV : before.length+1≤V)
    (hV : V≤(before++a::after).length) (hgap : q (before.length+1)<q V)
    (hsize : partitionPoint 0 (before++a::after) V≤A*W)
    (hjclock : q j≤R*W) (hUclock : q (before.length+1)≤Ru*W) (hsmall : q j≤1)
    (tree : ClockTree (Spin n×Bool) (before++a::after))
    (start : ℝ) (hoa : MassOrdered start (before++a::after)) (s : tree.Slot) :
    let chi:=((tree.markedAttach start).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree (before.length+1) q (p.embed s) p.mark)).sum
    |nativeOriginalScalarPairMean (before++a::after) q j-chi^2*q j|≤
      nativeScalarLowRemainderConstant A R Ru*W^3 := by
  dsimp only
  rw [native_full_gamma_row_hessian n tree ho start hoa (before.length+1) (by omega) q s]
  exact native_scalar_pair_low_remainder_uniform_of_buffer hT before after a ho q hq hq0 htotal
    hW hA hR hRu j V hj hUV hV hgap hsize hjclock hUclock hsmall

end OAI.SKFluctuations.LaplaceWindowFormalization
