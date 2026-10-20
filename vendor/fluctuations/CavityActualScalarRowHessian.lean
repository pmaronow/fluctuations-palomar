module

public import CavityScalarGammaTopology
public import CavityScalarObservedBound

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

theorem scalar_marked_row_general {steps : List (GaussianStep (Fin 1))}
    (T : ReplicaTree (Fin 1) Bool steps) {a : ℝ} (ho : OrderedSteps a steps)
    (s : T.Slot) (x : ℝ) :
    ((T.markedAttach a).map (fun p=>p.coeff*scalarPlacementGamma T s p x)).sum =
      scalarSourceJet steps 2 x+a*(scalarSourceJet steps 1 x)^2 := by
  have he : ((T.markedAttach a).map (fun p=>p.coeff*scalarPlacementGamma T s p x)).sum =
      T.row (fun _=>(1/2:ℝ)) scalarFeature a
        (fun σ=>scalarFeature (T.atSlot σ s) (fun _=>1))
        (fun σ=>scalarFeature σ (fun _=>1)) (fun _=>x) := by
    simp_rw [scalarPlacementGamma_eq_eval]
    unfold ReplicaTree.row ReplicaTree.rowList
    rw [←T.markedAttach_forget a]
    simp only [List.map_map]
    rfl
  rw [he]
  have ho0:=ho.lower le_rfl ho.nonneg
  have hd:=T.hasDerivAt_expect (by intro σ; norm_num : ∀ σ : Bool, (0:ℝ)<1/2)
    scalarFeature (fun _=>1) ho (fun σ=>scalarFeature (T.atSlot σ s) (fun _=>1)) 0 x
  have hf (y : ℝ) : (0:Fin 1→ℝ)+y • (fun _=>(1:ℝ))=(fun _=>y) := by ext i; simp
  simp_rw [hf] at hd
  have hm (y : ℝ) : T.expect (fun _:Bool=>(1/2:ℝ)) scalarFeature
      (fun σ=>scalarFeature (T.atSlot σ s) (fun _=>1)) (fun _=>y)=scalarSourceJet steps 1 y :=
    (T.expect_atSlot (by intro σ; norm_num : ∀ σ : Bool, (0:ℝ)<1/2)
      scalarFeature ho s (fun σ=>scalarFeature σ (fun _=>1)) (fun _=>y)).trans
      (scalarSourceJet_one_mean ho0 y).symm
  simp_rw [hm,←scalarSourceJet_one_mean ho0] at hd
  have hh:=hd.unique (scalarSourceJet_hasDerivAt ho0 1 x)
  nlinarith

theorem scalarCutGamma_eq_actual_realized {as : List PositiveMass}
    (T : ClockTree Bool as) (ho : MassOrdered 0 as) (U : ℕ) (hU0 : 0<U)
    (K : ℕ→ℝ) (s : T.Slot) (p : ClockTree.MarkedPlacement T) :
    scalarCutGamma p.tree U K (p.embed s) p.mark =
      scalarPlacementGamma (T.realize (scalarClockIncrements (relocatedClock U 0 K)))
        (T.slotEquiv (scalarClockIncrements (relocatedClock U 0 K)) s)
        (p.realize (scalarClockIncrements (relocatedClock U 0 K))) 0 := by
  have hq0 : relocatedClock U 0 K 0=0 := by simp [relocatedClock,hU0]
  have H:=actual_scalar_pair_eq_realized p.tree ho (relocatedClock U 0 K) hq0 (p.embed s) p.mark
  simpa only [scalarCutGamma,scalarCutMoment,ClockTree.slotProduct,mul_one,
    scalarFeature_apply_spin,one_mul,scalarPlacementGamma,ClockTree.MarkedPlacement.realize,
    Equiv.symm_apply_apply,Pi.zero_def] using H

theorem scalar_actual_gamma_row_zero {as : List PositiveMass}
    (T : ClockTree Bool as) (ho0 : MassOrdered 0 as) (a : ℝ) (hoa : MassOrdered a as)
    (U : ℕ) (hU0 : 0<U) (K : ℕ→ℝ) (s : T.Slot) :
    ((T.markedAttach a).map (fun p=>p.coeff*scalarCutGamma p.tree U K (p.embed s) p.mark)).sum =
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0 := by
  let inc:=scalarClockIncrements (relocatedClock U 0 K)
  let cs:=scalarBoundaryClocks as (relocatedClock U 0 K)
  have hsteps : clockSteps as inc=heatSteps (ι:=Fin 1) cs := by
    unfold inc scalarClockIncrements
    rw [clockSteps_cumulative]
    exact (scalarBoundaryClocks_heatSteps as (relocatedClock U 0 K)).symm
  have H:=scalar_marked_row_general (T.realize inc) (clockSteps_ordered hoa inc)
    (T.slotEquiv inc s) 0
  rw [←T.markedAttach_realize a inc] at H
  simp only [List.map_map,Function.comp_def] at H
  change ((T.markedAttach a).map (fun p=>p.coeff*
    scalarPlacementGamma (T.realize inc) (T.slotEquiv inc s) (p.realize inc) 0)).sum =
      scalarSourceJet (clockSteps as inc) 2 0+
        a*(scalarSourceJet (clockSteps as inc) 1 0)^2 at H
  have he : ((T.markedAttach a).map (fun p=>p.coeff*scalarCutGamma p.tree U K (p.embed s) p.mark)).sum =
      ((T.markedAttach a).map (fun p=>p.coeff*
        scalarPlacementGamma (T.realize inc) (T.slotEquiv inc s) (p.realize inc) 0)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    rw [scalarCutGamma_eq_actual_realized T ho0 U hU0 K s p]
  rw [he]
  rw [H,hsteps,scalarSourceJet_schedule_gradient_zero cs (scalarBoundaryClocks_ordered ho0 _)]
  simp only [zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,add_zero]
  simpa only [Pi.zero_def] using scalarSourceJet_two_schedule cs
    (scalarBoundaryClocks_ordered ho0 _) 0

theorem native_full_gamma_row_hessian (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho0 : MassOrdered 0 as)
    (a : ℝ) (hoa : MassOrdered a as) (U : ℕ) (hU0 : 0<U) (K : ℕ→ℝ) (s : T.Slot) :
    ((T.markedAttach a).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed s) p.mark)).sum =
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0 := by
  rw [native_full_gamma_row_eq_scalar n T ho0 U K s a]
  exact scalar_actual_gamma_row_zero T.scalarTopology ho0 a hoa U hU0 K _

theorem native_rest_gamma_row_hessian (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) (ho0 : MassOrdered 0 as)
    (a : ℝ) (hoa : MassOrdered a as) (U : ℕ) (hU0 : 0<U) (K : ℕ→ℝ) (s : T.Slot) :
    ((T.markedAttach a).map (fun p=>p.coeff*
      scalarGammaFromTopology as U K (p.tree.splitIndex (p.embed s) p.mark) (p.hit s))).sum =
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0 := by
  rw [native_rest_gamma_row_eq_scalar n T ho0 U K s a]
  exact scalar_actual_gamma_row_zero T.scalarTopology ho0 a hoa U hU0 K _

end OAI.SKFluctuations.Cavity
