module

public import ComparisonSignedCavityActualExteriorPartnerRowCollapse
public import ComparisonSignedCavityProjectionRestrictionReplacement

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree

theorem native_target_singleton_original_rest_disorder_exchange (n : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (z : T.Slot) (k : ℕ)
    (h : ∀c:T.Slot,k≤T.splitIndex z c→c=z) (ho : MassOrdered 0 as)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : k≤p.tree.splitIndex (p.embed z) p.mark)
    (q : ℕ→Cavity.RestCoordinate n→ℝ)
    (Q : T.cavityLeft.Assignment→Spin n→ℝ) :
    p.tree.cavityLeft.disorderExpect (Cavity.restWeight n) (Cavity.restFeature n) 0 q
      (fun τ=>Q (p.restRestrict τ) (p.restSpin τ)) 0=
    p.tree.cavityLeft.disorderExpect (Cavity.restWeight n) (Cavity.restFeature n) 0 q
      (fun τ=>Q (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot z) (p.restRestrict τ) (p.restSpin τ))
        (T.cavityLeft.atSlot (p.restRestrict τ) (T.cavityLeftSlot z))) 0 := by
  rw [p.tree.cavityLeft.disorderExpect_integral (Cavity.restWeight_pos n) (Cavity.restFeature n) ho,
    p.tree.cavityLeft.disorderExpect_integral (Cavity.restWeight_pos n) (Cavity.restFeature n) ho]
  unfold zeroContinuation
  apply integral_congr_ae
  exact Eventually.of_forall fun y=>
    native_target_singleton_full_rest_exchange T z k h (Cavity.restWeight_pos n) (Cavity.restFeature n)
      ho p hp hh _ Q (0+y)

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 26000000

theorem native_second_low_singleton_rest_gamma_row_collapse (n : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (z : T.Slot) (star U : ℕ) (hs : star<U) (hU : U≤as.length)
    (h : NativeTargetStarSingleton T z star) (b hfield K : ℕ→ℝ)
    (q : ℕ→RestCoordinate n→ℝ) (Q : T.cavityLeft.Assignment→Spin n→ℝ)
    (hQ : ∀τ u w,Q (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot z) τ u) w=Q τ w) :
    ((T.markedAttach 0).map (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed z) p.mark*
      p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun τ=>Q (p.restRestrict τ) (p.restSpin τ)) 0)).sum=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun τ=>Q τ (T.cavityLeft.atSlot τ (T.cavityLeftSlot z))) 0 := by
  have HE : ((T.markedAttach 0).map (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed z) p.mark*
      p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun τ=>Q (p.restRestrict τ) (p.restSpin τ)) 0)).sum=
    ((T.markedAttach 0).map (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed z) p.mark*
      p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun τ=>Q (p.restRestrict τ)
          (T.cavityLeft.atSlot (p.restRestrict τ) (T.cavityLeftSlot z))) 0)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    by_cases hh : U≤p.tree.splitIndex (p.embed z) p.mark
    · have H:=native_target_singleton_original_rest_disorder_exchange n T z (star+1)
        (fun c hc=>h c (by omega)) ho p hp (by omega) q Q
      simp_rw [hQ] at H
      rw [H]
    · rw [fullScalarCutGamma_cross_zero p.tree ho U K (p.embed z) p.mark hU (lt_of_not_ge hh)]
      ring
  rw [HE]
  exact native_observed_gamma_rest_test_collapse n q U b hfield K T ho 0 ho (by omega) z
    (fun τ=>Q τ (T.cavityLeft.atSlot τ (T.cavityLeftSlot z)))

def nativeSecondLowFreshPartnerProductRow (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (e z : T.Slot) (P F G : T.cavityLeft.Assignment→ℝ) : ℝ :=
  ((T.markedAttach 0).map fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed z) p.mark*
    p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun τ=>P (p.restRestrict τ)*
        (F (p.restRestrict τ)*restLowKernel n U b h (p.tree.splitIndex (p.embed e) p.mark)
          (T.cavityLeft.atSlot (p.restRestrict τ) (T.cavityLeftSlot e)) (p.restSpin τ)-
          G (p.restRestrict τ))) 0).sum

theorem native_second_low_fresh_partner_product_row_collapse (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (e z : T.Slot) (star : ℕ) (hs : star<U) (hU : U≤as.length)
    (hz : NativeTargetStarSingleton T z star) (hez : T.splitIndex e z<U)
    (P F G : T.cavityLeft.Assignment→ℝ)
    (hP : ∀τ u,P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot z) τ u)=P τ)
    (hF : ∀τ u,F (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot z) τ u)=F τ)
    (hG : ∀τ u,G (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot z) τ u)=G τ) :
    nativeSecondLowFreshPartnerProductRow n q U b h K T e z P F G=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun τ=>P τ*(F τ*restLowKernel n U b h (T.splitIndex e z)
            (T.cavityLeft.atSlot τ (T.cavityLeftSlot e))
            (T.cavityLeft.atSlot τ (T.cavityLeftSlot z))-G τ)) 0 := by
  have hne : e≠z := by
    intro H
    rw [H,T.splitIndex_self] at hez
    omega
  let Q:=fun τ d=>P τ*(F τ*restLowKernel n U b h (T.splitIndex e z)
      (T.cavityLeft.atSlot τ (T.cavityLeftSlot e)) d-G τ)
  have hQ : ∀τ u w,Q (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot z) τ u) w=Q τ w := by
    intro τ u w
    dsimp only [Q]
    rw [hP,hF,hG,nativeReplaceAtSlot_at,ite_eq_right (fun H=>hne (T.cavityLeftSlot.injective H))]
  have HE : nativeSecondLowFreshPartnerProductRow n q U b h K T e z P F G=
      ((T.markedAttach 0).map (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed z) p.mark*
        p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun τ=>Q (p.restRestrict τ) (p.restSpin τ)) 0)).sum := by
    unfold nativeSecondLowFreshPartnerProductRow
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    by_cases hh : U≤p.tree.splitIndex (p.embed z) p.mark
    · have Hsplit : p.tree.splitIndex (p.embed e) p.mark=T.splitIndex e z := by
        have HA : p.tree.splitIndex (p.embed e) (p.embed z)<U := by
          rw [(T.markedAttach_embed_preserves 0 p hp).2]
          exact hez
        exact (native_cross_split_of_same_cut_blocks p.tree U (p.embed e) (p.embed z)
          (p.embed e) p.mark HA (by rw [p.tree.splitIndex_self];exact hU) hh).trans
          ((T.markedAttach_embed_preserves 0 p hp).2 e z)
      rw [Hsplit]
    · rw [fullScalarCutGamma_cross_zero p.tree ho U K (p.embed z) p.mark hU (lt_of_not_ge hh)]
      ring
  rw [HE]
  exact native_second_low_singleton_rest_gamma_row_collapse n T ho z star U hs hU hz b h K q Q hQ

end OAI.SKFluctuations.Cavity
