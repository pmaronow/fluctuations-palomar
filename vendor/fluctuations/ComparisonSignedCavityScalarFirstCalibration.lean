module

public import ComparisonSignedCavityFrozenAssembly
public import CavityActualScalarRowHessian

@[expose] public section

noncomputable section
set_option maxHeartbeats 7500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_cross_split_of_same_cut_blocks {S : Type*} {as : List PositiveMass}
    (T : ClockTree S as) (U : ℕ) (a z c d : T.Slot)
    (haz : T.splitIndex a z < U) (hac : U ≤ T.splitIndex a c)
    (hzd : U ≤ T.splitIndex z d) : T.splitIndex c d=T.splitIndex a z := by
  let j:=T.splitIndex a z
  have hca : U ≤ T.splitIndex c a := by rwa [T.splitIndex_symm]
  have hdz : U ≤ T.splitIndex d z := by rwa [T.splitIndex_symm]
  have hl : j ≤ T.splitIndex c d :=
    T.splitIndex_cut_trans j c z d
      (T.splitIndex_cut_trans j c a z (haz.le.trans hca) le_rfl) (haz.le.trans hzd)
  have hu : T.splitIndex c d ≤ j := by
    by_contra H
    have hcd : j+1 ≤ T.splitIndex c d := by omega
    have ha : j+1 ≤ T.splitIndex a c := (by omega : j+1 ≤ U).trans hac
    have hd : j+1 ≤ T.splitIndex d z := (by omega : j+1 ≤ U).trans hdz
    have HH:=T.splitIndex_cut_trans (j+1) a d z
      (T.splitIndex_cut_trans (j+1) a c d ha hcd) hd
    change j+1 ≤ j at HH
    omega
  exact le_antisymm hu hl

theorem native_scalar_low_weight_forward (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (a z c d : T.Slot) (hU : U ≤ as.length)
    (haz : T.splitIndex a z < U) :
    (if T.splitIndex c d<U then K (T.splitIndex c d) else 0)*
      (fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d)=
    K (T.splitIndex a z)*(fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d) := by
  by_cases hac : U ≤ T.splitIndex a c
  · by_cases hzd : U ≤ T.splitIndex z d
    · rw [native_cross_split_of_same_cut_blocks T U a z c d haz hac hzd]
      simp only [haz,ite_true]
    · rw [fullScalarCutGamma_cross_zero T ho U K z d hU (lt_of_not_ge hzd)]
      simp only [mul_zero]
  · rw [fullScalarCutGamma_cross_zero T ho U K a c hU (lt_of_not_ge hac)]
    simp only [zero_mul,mul_zero]

theorem native_scalar_low_weight_pair (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (a z c d : T.Slot) (hU : U ≤ as.length)
    (haz : T.splitIndex a z < U) :
    (if T.splitIndex c d<U then K (T.splitIndex c d) else 0)*
      (fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d+
        fullScalarCutGamma T U K a d*fullScalarCutGamma T U K z c)=
    K (T.splitIndex a z)*
      (fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d+
        fullScalarCutGamma T U K a d*fullScalarCutGamma T U K z c) := by
  have H1:=native_scalar_low_weight_forward n T ho U K a z c d hU haz
  have H2:=native_scalar_low_weight_forward n T ho U K a z d c hU haz
  rw [T.splitIndex_symm d c] at H2
  nlinarith

theorem native_inserted_scalar_low_mean (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree) :
    r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (insertedRestTest (fun _=>1) (restLowKernel n U 0 K) p r) 0=
      if r.tree.splitIndex (r.embed p.mark) r.mark<U then
        K (r.tree.splitIndex (r.embed p.mark) r.mark) else 0 := by
  let c:=if r.tree.splitIndex (r.embed p.mark) r.mark<U then
    K (r.tree.splitIndex (r.embed p.mark) r.mark) else 0
  have hf : insertedRestTest (fun _=>1) (restLowKernel n U 0 K) p r=fun _=>c*(1:ℝ) := by
    funext τ
    dsimp only [insertedRestTest,restLowKernel,c]
    split_ifs <;> simp
  rw [hf,r.tree.cavityLeft.disorderExpect_const_mul (restWeight_pos n) (restFeature n) ho,
    r.tree.cavityLeft.disorderExpect_one (restWeight_pos n) (restFeature n) ho,mul_one]

theorem fullScalarCutGamma_marked_preserves {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (a z : T.Slot)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0) :
    fullScalarCutGamma p.tree U K (p.embed a) (p.embed z)=fullScalarCutGamma T U K a z := by
  simpa only [fullScalarCutGamma,List.map_cons,List.map_nil] using
    fullScalarCutMoment_marked_preserves T ho U K [a,z] p hp

def nativeDoubleGammaForward {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K : ℕ→ℝ) (a z : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
      fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark)).sum)).sum

theorem native_double_gamma_forward_eq_hessian_sq (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (hU0 : 0 < U) (K : ℕ→ℝ) (a z : T.Slot) :
    nativeDoubleGammaForward T U K a z=
      ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2 := by
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have HI (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0) :
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
        fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark)).sum=
      fullScalarCutGamma p.tree U K (p.embed a) p.mark*chi := by
    have HE : (p.tree.markedAttach 0).map (fun r=>r.coeff*
        fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
        fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark)=
      (p.tree.markedAttach 0).map (fun r=>
        fullScalarCutGamma p.tree U K (p.embed a) p.mark*
        (r.coeff*fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark)) := by
      apply List.map_congr_left
      intro r hr
      rw [fullScalarCutGamma_marked_preserves p.tree ho U K (p.embed a) p.mark r hr]
      ring
    rw [HE,List.sum_map_mul_left,native_full_gamma_row_hessian n p.tree ho 0 ho U hU0 K]
  unfold nativeDoubleGammaForward
  have HE : (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
        fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark)).sum)=
    (T.markedAttach 0).map (fun p=>
      (p.coeff*fullScalarCutGamma p.tree U K (p.embed a) p.mark)*chi) := by
    apply List.map_congr_left
    intro p hp
    rw [HI p hp]
    ring
  rw [HE,List.sum_map_mul_right,native_full_gamma_row_hessian n T ho 0 ho U hU0 K]
  dsimp only [chi]
  ring

theorem native_scalar_first_retained_eq_K_hessian_sq (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (a z : T.Slot) (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    retainedSignedJets n q U b h K [restLowKernel n U 0 K] T (fun _=>1) [a,z]=
      K (T.splitIndex a z)*
        ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2 := by
  have hU0 : 0 < U := by omega
  rw [retained_one_low_eq_gamma_allocations n q U b h K T ho (fun _=>1)
    (restLowKernel n U 0 K) (by intro j hj σ τ;simp [restLowKernel,not_lt.mpr hj]) a z hU haz]
  have HE : (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest (fun _=>1) (restLowKernel n U 0 K) p r) 0*
        (fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark+
         fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)))).sum)=
    (T.markedAttach 0).map (fun p=>K (T.splitIndex a z)*
      (p.coeff*((p.tree.markedAttach 0).map (fun r=>
        r.coeff*fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark+
        r.coeff*fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
          fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark)).sum)) := by
    apply List.map_congr_left
    intro p hp
    have HEI : (p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest (fun _=>1) (restLowKernel n U 0 K) p r) 0*
        (fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark+
         fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)))=
      (p.tree.markedAttach 0).map (fun r=>K (T.splitIndex a z)*
        (r.coeff*fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark+
        r.coeff*fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
          fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark)) := by
      apply List.map_congr_left
      intro r hr
      have hs : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed z))=T.splitIndex a z := by
        rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,
          (T.markedAttach_embed_preserves 0 p hp).2]
      have HA:=native_scalar_low_weight_pair n r.tree ho U K
        (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark hU
        (by rw [hs];exact haz)
      rw [hs] at HA
      rw [native_inserted_scalar_low_mean n q U K T ho p r]
      calc
        _ = r.coeff*((if r.tree.splitIndex (r.embed p.mark) r.mark<U then
            K (r.tree.splitIndex (r.embed p.mark) r.mark) else 0)*
          (fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
            fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark+
           fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
            fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark))) := by ring
        _ = _ := by rw [HA];ring
    rw [HEI,List.sum_map_mul_left]
    ring
  rw [HE,List.sum_map_mul_left]
  simp_rw [List.sum_map_add,mul_add,List.sum_map_add]
  change K (T.splitIndex a z)*
    (nativeDoubleGammaForward T U K a z+nativeDoubleGammaForward T U K z a)/2=_
  rw [native_double_gamma_forward_eq_hessian_sq n T ho U hU0 K a z,
    native_double_gamma_forward_eq_hessian_sq n T ho U hU0 K z a]
  ring

theorem actual_scalar_first_low_eq_K_hessian_sq (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (a z : T.Slot)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    cutLowJet n q U b h K T (fun σ=>sitePair T a z (T.cavityAssignment σ).2) 0 1 0 0=
      K (T.splitIndex a z)*
        ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2 := by
  rw [←nativeScalarTest_pair,actual_scalar_low_coefficient_eq_retained n q U b h K T ho
    [a,z] hq0 hq hb hh hK hbm hhm hKm]
  simpa only [List.replicate_one] using native_scalar_first_retained_eq_K_hessian_sq n q U b h K
    T ho a z hU haz

end OAI.SKFluctuations.Cavity
