module

public import ComparisonSignedCavityActualLongitudinalAllocation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

theorem native_G_Gamma_centered_low_test_eq_target_split (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (σc σd : T.cavityLeft.Assignment→Spin n)
    (a z c d : T.Slot) (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    fullScalarCutGamma T U K z d*
      nativeRetainedHighPairing n q U b h K T
        (fun σ=>P σ*restCenteredLowKernel n U b S (T.splitIndex c d) (σc σ) (σd σ)) a c=
    fullScalarCutGamma T U K z d*
      nativeRetainedHighPairing n q U b h K T
        (fun σ=>P σ*restCenteredFixedForkKernel n b S (T.splitIndex a z)
          (T.splitIndex c d) (σc σ) (σd σ)) a c := by
  by_cases hac : U ≤ T.splitIndex a c
  · by_cases hzd : U ≤ T.splitIndex z d
    · rw [native_cross_split_of_same_cut_blocks T U a z c d haz hac hzd]
      simp only [restCenteredLowKernel,haz,ite_true,restCenteredFixedForkKernel]
    · rw [fullScalarCutGamma_cross_zero T ho U K z d hU (lt_of_not_ge hzd)]
      simp only [zero_mul]
  · rw [native_retained_high_pairing_cross_zero n q U b h K T ho _ a c hU (lt_of_not_ge hac),
      native_retained_high_pairing_cross_zero n q U b h K T ho _ a c hU (lt_of_not_ge hac)]

theorem native_G_centered_low_allocation_eq_fixed_target_fork (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    nativeGKernelLowAllocation n q U b h K T P a z (restCenteredLowKernel n U b S)=
      nativeGKernelLowAllocation n q U b h K T P a z
        (restCenteredFixedForkKernel n b S (T.splitIndex a z)) := by
  unfold nativeGKernelLowAllocation
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  have HS : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed z))=T.splitIndex a z := by
    rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2]
  have hrev : r.tree.splitIndex (r.embed (p.embed z)) (r.embed (p.embed a)) < U := by
    rw [r.tree.splitIndex_symm,HS]
    exact haz
  have H₁:=native_G_Gamma_centered_low_test_eq_target_split n q U b h K S r.tree ho
    (fun σ=>P (p.restRestrict (r.restRestrict σ)))
    (fun σ=>p.restSpin (r.restRestrict σ)) r.restSpin
    (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark hU (by rwa [HS])
  have H₂:=native_G_Gamma_centered_low_test_eq_target_split n q U b h K S r.tree ho
    (fun σ=>P (p.restRestrict (r.restRestrict σ)))
    (fun σ=>p.restSpin (r.restRestrict σ)) r.restSpin
    (r.embed (p.embed a)) (r.embed (p.embed z)) r.mark (r.embed p.mark) hU (by rwa [HS])
  have H₃:=native_G_Gamma_centered_low_test_eq_target_split n q U b h K S r.tree ho
    (fun σ=>P (p.restRestrict (r.restRestrict σ)))
    (fun σ=>p.restSpin (r.restRestrict σ)) r.restSpin
    (r.embed (p.embed z)) (r.embed (p.embed a)) r.mark (r.embed p.mark) hU hrev
  have H₄:=native_G_Gamma_centered_low_test_eq_target_split n q U b h K S r.tree ho
    (fun σ=>P (p.restRestrict (r.restRestrict σ)))
    (fun σ=>p.restSpin (r.restRestrict σ)) r.restSpin
    (r.embed (p.embed z)) (r.embed (p.embed a)) (r.embed p.mark) r.mark hU hrev
  rw [r.tree.splitIndex_symm r.mark (r.embed p.mark)] at H₂ H₃
  rw [r.tree.splitIndex_symm (r.embed (p.embed z)) (r.embed (p.embed a))] at H₃ H₄
  rw [HS] at H₁ H₂ H₃ H₄
  have HEQ (A : ℕ→Spin n→Spin n→ℝ) : insertedRestTest P A p r=
      fun σ=>P (p.restRestrict (r.restRestrict σ))*
        A (r.tree.splitIndex (r.embed p.mark) r.mark) (p.restSpin (r.restRestrict σ)) (r.restSpin σ) := rfl
  rw [HEQ (restCenteredLowKernel n U b S),
    HEQ (restCenteredFixedForkKernel n b S (T.splitIndex a z))]
  linear_combination r.coeff*(H₁+H₂+H₃+H₄)

end OAI.SKFluctuations.Cavity
