module

public import ComparisonSignedCavityScalarLowRemainder
public import ComparisonSignedCavityScalarResponse
public import ComparisonSignedCavitySusceptibilityBounds

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity GaussianCalculus Scalar
set_option maxHeartbeats 4500000

theorem scalarBoundaryClocks_zero_prefix_F (J : HeatJet 0)
    (as : List PositiveMass) (q : ℕ→ℝ) (hz : ∀j≤as.length,q j=0) :
    (J.schedule (scalarBoundaryClocks as q)).F=J.F := by
  induction as generalizing q with
  | nil => rfl
  | cons a as ih =>
    have h0 := hz 0 (by omega)
    have h1 := hz 1 (by simp)
    have htail := ih (fun j=>q (j+1)) (by intro j hj;exact hz (j+1) (by simpa using Nat.succ_le_succ hj))
    funext x
    change clockContinuation a.val
      (J.schedule (scalarBoundaryClocks as (fun j=>q (j+1)))).F
      (Real.toNNReal (q 1-q 0)) x=J.F x
    rw [htail,h0,h1,sub_self,Real.toNNReal_zero,NNReal.coe_zero,
      clockContinuation_zero a.property.ne']

theorem scalarBoundaryClocks_relocated_prefix_F (J : HeatJet 0)
    (before after : List PositiveMass) (a : PositiveMass) (q : ℕ→ℝ) :
    (J.schedule (scalarBoundaryClocks (before++a::after)
      (relocatedClock (before.length+1) 0 q))).F=
    fun x=>clockContinuation a.val
      (J.schedule (scalarBoundaryClocks after (fun j=>q (before.length+1+j)))).F
      (Real.toNNReal (q (before.length+1))) x := by
  rw [scalarBoundaryClocks_append,HeatJet.schedule_append]
  rw [scalarBoundaryClocks_zero_prefix_F _ before _ (by
    intro j hj
    simp only [relocatedClock,show j<before.length+1 by omega,ite_true,zero_mul])]
  have hshift : (fun j=>relocatedClock (before.length+1) 0 q (before.length+(j+1)))=
      fun j=>q (before.length+1+j) := by
    funext j
    simp only [relocatedClock,show ¬before.length+(j+1)<before.length+1 by omega,ite_false]
    exact congrArg q (by omega)
  funext x
  change clockContinuation a.val
    (J.schedule (scalarBoundaryClocks after
      (fun j=>relocatedClock (before.length+1) 0 q (before.length+(j+1))))).F
    (Real.toNNReal (relocatedClock (before.length+1) 0 q (before.length+1)-
      relocatedClock (before.length+1) 0 q before.length)) x=_
  rw [hshift]
  simp only [relocatedClock,lt_self_iff_false,ite_false,
    show before.length<before.length+1 by omega,ite_true,zero_mul,sub_zero]

def nativeScalarClockProfile {T : ℝ} (hT : 0<T) (as : List PositiveMass)
    (q : ℕ→ℝ) (hq : Monotone q) (hq0 : q 0=0) (htotal : q as.length=T) :
    boundedMassProfiles := actualScalarScheduleMass hT (scalarBoundaryClocks as q) (by
      rw [scalarBoundaryClocks_duration as q hq,hq0,sub_zero,htotal])

theorem nativeScalarClockProfile_right_continuous {T : ℝ} (hT : 0<T)
    (as : List PositiveMass) (q : ℕ→ℝ) (hq : Monotone q)
    (hq0 : q 0=0) (htotal : q as.length=T) (s : ℝ) :
    ContinuousWithinAt (nativeScalarClockProfile hT as q hq hq0 htotal).val (Ici s) s :=
  quantileMassProfile_right_continuous _ _ s

theorem nativeScalarClockProfile_tail_F {T : ℝ} (hT : 0<T)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (q : ℕ→ℝ) (hq : Monotone q)
    (hq0 : q 0=0) (htotal : q as.length=T) (U : ℕ) (hU : U≤as.length) :
    (scalarTailJet hT (nativeScalarClockProfile hT as q hq hq0 htotal) (q U/T)).F=
      (scalarTerminal.schedule (scalarBoundaryClocks (as.drop U) (fun j=>q (U+j)))).F := by
  let pre:=scalarBoundaryClocks (as.take U) q
  let post:=scalarBoundaryClocks (as.drop U) (fun j=>q (U+j))
  let cs:=scalarBoundaryClocks as q
  let alpha:=nativeScalarClockProfile hT as q hq hq0 htotal
  have hsplit : cs=pre++post := by
    have H:=scalarBoundaryClocks_append (as.take U) (as.drop U) q
    simpa only [List.take_append_drop,List.length_take,Nat.min_eq_left hU,cs,pre,post] using H
  have hdur : (scheduleDuration cs:ℝ)=T := by
    rw [scalarBoundaryClocks_duration as q hq,hq0,sub_zero,htotal]
  have hmatch : ScheduleProfileMatches (rescaledMassProfile alpha hT) cs 0 :=
    actual_schedule_cdf_matches hT le_rfl cs (by linarith [hdur]) (scalarBoundaryClocks_ordered ho q)
  rw [hsplit] at hmatch hdur
  have hm := (ScheduleProfileMatches.prefix_suffix _ pre post 0 hmatch).2
  simp only [zero_add] at hm
  have hpre : (scheduleDuration pre:ℝ)=q U := by
    rw [scalarBoundaryClocks_duration (as.take U) q hq,List.length_take,Nat.min_eq_left hU,hq0,sub_zero]
  have ht : T*(1-q U/T)=(scheduleDuration post:ℝ) := by
    rw [scheduleDuration_append,NNReal.coe_add,hpre] at hdur
    field_simp
    nlinarith [hdur]
  have hs : T*(q U/T)=q U := mul_div_cancel₀ _ hT.ne'
  funext x
  change (scalarProfileHeatJet (rescaledMassProfile alpha hT)
    (fun s=>(alpha.property.1 (s/T)).2) (T*(q U/T))
      (Real.toNNReal (T*(1-q U/T)))).F x=(scalarTerminal.schedule post).F x
  rw [hs,ht,Real.toNNReal_coe]
  have H:=finite_scalar_profile_eq_schedule scalarTerminal (rescaledMassProfile alpha hT)
    (fun s=>(alpha.property.1 (s/T)).2) post (q U) (by simpa only [hpre] using hm) x
  exact (scalarProfileHeatJet_F _ _ _ _ x).trans H

theorem native_relocated_hessian_eq_low_flattened {T : ℝ} (hT : 0<T)
    (before after : List PositiveMass) (a : PositiveMass)
    (ho : MassOrdered 0 (before++a::after)) (q : ℕ→ℝ) (hq : Monotone q)
    (hq0 : q 0=0) (htotal : q (before++a::after).length=T) :
    (scalarTerminal.schedule (scalarBoundaryClocks (before++a::after)
      (relocatedClock (before.length+1) 0 q))).H 0 0=
    scalarLowFlattenedSusceptibility hT
      (nativeScalarClockProfile hT (before++a::after) q hq hq0 htotal)
      (q (before.length+1)/T) a.property := by
  have htail:=nativeScalarClockProfile_tail_F hT (before++a::after) ho q hq hq0 htotal
    (before.length+1) (by simp)
  rw [List.drop_length_add_append,List.drop_one,List.tail_cons] at htail
  have hF : (scalarTerminal.schedule (scalarBoundaryClocks (before++a::after)
      (relocatedClock (before.length+1) 0 q))).F=
      ((scalarTailJet hT (nativeScalarClockProfile hT (before++a::after) q hq hq0 htotal)
        (q (before.length+1)/T)).evolve a.property (T*(q (before.length+1)/T))).F := by
    rw [scalarBoundaryClocks_relocated_prefix_F]
    funext x
    change _=clockContinuation a.val _ (T*(q (before.length+1)/T)) x
    rw [htail,mul_div_cancel₀ _ hT.ne']
    have hp : 0≤q (before.length+1) := by
      rw [←hq0]
      exact hq (by omega)
    rw [Real.coe_toNNReal _ hp]
  exact congrFun (HeatJet.H_congr_F hF) 0

end OAI.SKFluctuations.LaplaceWindowFormalization
