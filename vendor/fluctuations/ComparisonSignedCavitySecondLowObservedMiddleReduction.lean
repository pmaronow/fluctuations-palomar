module

public import ComparisonSignedCavitySecondLowFreshPartnerCollapse

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000

def nativeSecondLowObservedMiddlePartnerRow (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (c z : T.Slot) (P F G : T.cavityLeft.Assignment→ℝ) : ℝ :=
  ((T.markedAttach 0).map fun s=>s.coeff*fullScalarCutGamma s.tree U K (s.embed c) s.mark*
    nativeSecondLowFreshPartnerProductRow n q U b h K s.tree s.mark (s.embed z)
      (fun τ=>P (s.restRestrict τ)) (fun τ=>F (s.restRestrict τ)) (fun τ=>G (s.restRestrict τ))).sum

theorem native_second_low_observed_middle_partner_row_exact (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (c z : T.Slot) (star : ℕ) (hs : star<U) (hU : U≤as.length)
    (hz : NativeTargetStarSingleton T z star) (hcz : T.splitIndex c z ≤ star)
    (P F G : T.cavityLeft.Assignment→ℝ)
    (hP : ∀τ u,P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot z) τ u)=P τ)
    (hF : ∀τ u,F (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot z) τ u)=F τ)
    (hG : ∀τ u,G (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot z) τ u)=G τ) :
    nativeSecondLowObservedMiddlePartnerRow n q U b h K T c z P F G=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        nativeObservedGammaRow n q U K T 0 c
          (fun τ e=>P τ*(F τ*restLowKernel n U b h (T.splitIndex c z) e
            (T.cavityLeft.atSlot τ (T.cavityLeftSlot z))-G τ)) := by
  unfold nativeSecondLowObservedMiddlePartnerRow nativeObservedGammaRow
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hsm
  by_cases hh : U ≤ s.tree.splitIndex (s.embed c) s.mark
  · have Hsplit : s.tree.splitIndex s.mark (s.embed z)=T.splitIndex c z := by
      exact (s.tree.splitIndex_low_eq_of_high s.mark (s.embed c) (s.embed z)
        (by simpa only [s.tree.splitIndex_symm s.mark (s.embed c)] using hh) (by
          rw [(T.markedAttach_embed_preserves 0 s hsm).2]
          omega)).trans ((T.markedAttach_embed_preserves 0 s hsm).2 c z)
    have Houtside : s.tree.splitIndex (s.embed z) s.mark ≤ star := by
      rw [s.tree.splitIndex_symm,Hsplit]
      exact hcz
    have Hsingle : NativeTargetStarSingleton s.tree (s.embed z) star:=hz.retain_outside_mark s hsm Houtside
    have HP : ∀τ u,P (s.restRestrict (nativeReplaceAtSlot s.tree.cavityLeft
        (s.tree.cavityLeftSlot (s.embed z)) τ u))=P (s.restRestrict τ) := by
      intro τ u
      rw [s.restRestrict_replace_target (T.markedAttach_embed_preserves 0 s hsm).1,hP]
    have HF : ∀τ u,F (s.restRestrict (nativeReplaceAtSlot s.tree.cavityLeft
        (s.tree.cavityLeftSlot (s.embed z)) τ u))=F (s.restRestrict τ) := by
      intro τ u
      rw [s.restRestrict_replace_target (T.markedAttach_embed_preserves 0 s hsm).1,hF]
    have HG : ∀τ u,G (s.restRestrict (nativeReplaceAtSlot s.tree.cavityLeft
        (s.tree.cavityLeftSlot (s.embed z)) τ u))=G (s.restRestrict τ) := by
      intro τ u
      rw [s.restRestrict_replace_target (T.markedAttach_embed_preserves 0 s hsm).1,hG]
    rw [native_second_low_fresh_partner_product_row_collapse n q U b h K s.tree ho
      s.mark (s.embed z) star hs hU Hsingle (by rw [Hsplit];omega)
      (fun τ=>P (s.restRestrict τ)) (fun τ=>F (s.restRestrict τ)) (fun τ=>G (s.restRestrict τ)) HP HF HG,Hsplit]
    have HE : (fun τ : s.tree.cavityLeft.Assignment=>P (s.restRestrict τ)*
        (F (s.restRestrict τ)*restLowKernel n U b h (T.splitIndex c z)
          (s.tree.cavityLeft.atSlot τ (s.tree.cavityLeftSlot s.mark))
          (s.tree.cavityLeft.atSlot τ (s.tree.cavityLeftSlot (s.embed z)))-G (s.restRestrict τ)))=
        (fun τ=>P (s.restRestrict τ)*(F (s.restRestrict τ)*
          restLowKernel n U b h (T.splitIndex c z) (s.restSpin τ)
            (T.cavityLeft.atSlot (s.restRestrict τ) (T.cavityLeftSlot z))-G (s.restRestrict τ))) := by
      funext τ
      rw [s.restRestrict_at]
      rfl
    rw [HE]
    ring
  · rw [fullScalarCutGamma_cross_zero s.tree ho U K (s.embed c) s.mark hU (lt_of_not_ge hh)]
    ring

def nativeSecondLowObservedMiddleResidual (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (c z : T.Slot) (P F : T.cavityLeft.Assignment→ℝ) : ℝ :=
  ((T.markedAttach 0).map fun s=>s.coeff*fullScalarCutGamma s.tree U K (s.embed c) s.mark*
    s.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun τ=>P (s.restRestrict τ)*F (s.restRestrict τ)*
        (restLowKernel n U b h (T.splitIndex c z) (s.restSpin τ)
            (T.cavityLeft.atSlot (s.restRestrict τ) (T.cavityLeftSlot z))-
          restLowKernel n U b h (T.splitIndex c z)
            (T.cavityLeft.atSlot (s.restRestrict τ) (T.cavityLeftSlot c))
            (T.cavityLeft.atSlot (s.restRestrict τ) (T.cavityLeftSlot z)))) 0).sum

theorem native_second_low_observed_middle_eq_baseline_add_residual (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (c z : T.Slot) (star : ℕ) (hs : star<U) (hU : U≤as.length)
    (hz : NativeTargetStarSingleton T z star) (hcz : T.splitIndex c z ≤ star)
    (P F G : T.cavityLeft.Assignment→ℝ)
    (hP : ∀τ u,P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot z) τ u)=P τ)
    (hF : ∀τ u,F (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot z) τ u)=F τ)
    (hG : ∀τ u,G (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot z) τ u)=G τ) :
    nativeSecondLowObservedMiddlePartnerRow n q U b h K T c z P F G=
      ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2*
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun τ=>P τ*(F τ*restLowKernel n U b h (T.splitIndex c z)
            (T.cavityLeft.atSlot τ (T.cavityLeftSlot c))
            (T.cavityLeft.atSlot τ (T.cavityLeftSlot z))-G τ)) 0+
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        nativeSecondLowObservedMiddleResidual n q U b h K T c z P F := by
  rw [native_second_low_observed_middle_partner_row_exact n q U b h K T ho c z star hs hU hz hcz P F G hP hF hG,
    native_observed_gamma_product_difference_exact n q U b h K T ho 0 ho (by omega) c P F G
      (fun τ e=>restLowKernel n U b h (T.splitIndex c z) e
        (T.cavityLeft.atSlot τ (T.cavityLeftSlot z)))]
  unfold nativeSecondLowObservedMiddleResidual
  ring

end OAI.SKFluctuations.Cavity
