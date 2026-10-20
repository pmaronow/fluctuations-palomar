module

public import ComparisonSignedCavityActualGCenterIndependence

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000

theorem native_low_scalar_forward_split_weight {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K F : ℕ→ℝ) (a z c d : T.Slot) (hU : U ≤ as.length)
    (haz : T.splitIndex a z < U) :
    F (T.splitIndex c d)*(fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d)=
      F (T.splitIndex a z)*(fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d) := by
  by_cases hac : U ≤ T.splitIndex a c
  · by_cases hzd : U ≤ T.splitIndex z d
    · rw [native_cross_split_of_same_cut_blocks T U a z c d haz hac hzd]
    · rw [fullScalarCutGamma_cross_zero T ho U K z d hU (lt_of_not_ge hzd)]
      simp only [mul_zero]
  · rw [fullScalarCutGamma_cross_zero T ho U K a c hU (lt_of_not_ge hac)]
    simp only [zero_mul,mul_zero]

theorem native_low_scalar_pairing_split_weight {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K F : ℕ→ℝ) (a z c d : T.Slot) (hU : U ≤ as.length)
    (haz : T.splitIndex a z < U) :
    F (T.splitIndex c d)*nativeLowScalarPairing T U K a z c d=
      F (T.splitIndex a z)*nativeLowScalarPairing T U K a z c d := by
  have H₁:=native_low_scalar_forward_split_weight T ho U K F a z c d hU haz
  have H₂:=native_low_scalar_forward_split_weight T ho U K F a z d c hU haz
  rw [T.splitIndex_symm d c] at H₂
  unfold nativeLowScalarPairing
  linear_combination H₁+H₂

theorem native_low_scalar_pairing_centered_kernel_eq_target_split
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (b K S : ℕ→ℝ) (a z c d : T.Slot) (hU : U ≤ as.length)
    (haz : T.splitIndex a z < U) (σ τ : Spin n) :
    nativeLowScalarPairing T U K a z c d*restCenteredLowKernel n U b S (T.splitIndex c d) σ τ=
      nativeLowScalarPairing T U K a z c d*
        (b (T.splitIndex a z)*((∑i,spinValue (σ i)*spinValue (τ i))/(n+1:ℕ)-S (T.splitIndex a z))) := by
  have H:=native_low_scalar_pairing_split_weight T ho U K
    (fun j=>restCenteredLowKernel n U b S j σ τ) a z c d hU haz
  simp only [restCenteredLowKernel,haz,ite_true] at H
  simpa only [restCenteredLowKernel,mul_comm] using H

def restCenteredFixedForkKernel (n : ℕ) (b S : ℕ→ℝ) (j₀ : ℕ)
    (_ : ℕ) (σ τ : Spin n) : ℝ :=
  b j₀*((∑i,spinValue (σ i)*spinValue (τ i))/(n+1:ℕ)-S j₀)

theorem native_scalar_weighted_low_high_jet_eq_fixed_target_fork (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : ClockTree.MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
    nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
      (r.embed p.mark) r.mark*
      retainedSignedJets n q U b h K [restHighKernel n U b h K] r.tree
        (insertedRestTest P (restCenteredLowKernel n U b S) p r) []=
    nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
      (r.embed p.mark) r.mark*
      retainedSignedJets n q U b h K [restHighKernel n U b h K] r.tree
        (insertedRestTest P (restCenteredFixedForkKernel n b S (T.splitIndex a z)) p r) [] := by
  let A:=nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
    (r.embed p.mark) r.mark
  have hs : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed z))=T.splitIndex a z := by
    rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2]
  have Htest : (fun σ=>A*insertedRestTest P (restCenteredLowKernel n U b S) p r σ)=
    (fun σ=>A*insertedRestTest P (restCenteredFixedForkKernel n b S (T.splitIndex a z)) p r σ) := by
    funext σ
    have H:=native_low_scalar_pairing_centered_kernel_eq_target_split r.tree ho U b K S
      (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark hU (by rwa [hs])
      (p.restSpin (r.restRestrict σ)) (r.restSpin σ)
    rw [hs] at H
    dsimp only [A,insertedRestTest,restCenteredFixedForkKernel]
    linear_combination P (p.restRestrict (r.restRestrict σ))*H
  have H:=congrArg (fun F=>retainedSignedJets n q U b h K [restHighKernel n U b h K] r.tree F []) Htest
  rw [retained_signed_jets_const_mul_test,retained_signed_jets_const_mul_test] at H
  exact H

end OAI.SKFluctuations.Cavity
