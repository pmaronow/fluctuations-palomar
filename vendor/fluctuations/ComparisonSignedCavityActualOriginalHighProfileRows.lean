module

public import ComparisonSignedCavityActualOriginalHighProfileHistory

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeOriginalHighRowGamma {n : ℕ} {as : List PositiveMass}
    (U : ℕ) (K : ℕ→ℝ) (st : NativeHighSwitchState (Spin n×Bool) as)
    (p : MarkedPlacement st.tree) : ℝ :=
  fullScalarCutGamma p.tree U K (p.embed st.target) p.mark

theorem nativeOriginalHighRowGamma_abs_le_one {n : ℕ} {as : List PositiveMass}
    (ho : MassOrdered 0 as) (U : ℕ) (K : ℕ→ℝ)
    (st : NativeHighSwitchState (Spin n×Bool) as) (p : MarkedPlacement st.tree) :
    |nativeOriginalHighRowGamma U K st p|≤1 := by
  exact native_full_scalar_cut_moment_abs_le_one p.tree ho U K [p.embed st.target,p.mark]

theorem nativeActualInitialExpansion_original_high_profiles_le
    {n : ℕ} {as : List PositiveMass} (ho : MassOrdered 0 as)
    (i star U : ℕ) (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length) (a : ℝ)
    (bf hf : ℝ→ℝ≥0) (K : ℕ→ℝ) (Mclock Temp p : ℝ) (hTemp : 0 ≤ Temp) (hp : 0 < p)
    (ops : List NativeActualExpansionOp) :
    let R:=nativeOriginalHighErrorEnvelope n U bf hf as Mclock Temp
    let f2:=fun j=>((R j)^(2/p))^2
    let L:=nativeActualResourceExpansion (nativeOriginalHighRowGamma (n:=n) U K) hs (by omega) ops
      (nativeActualInitialState as i star a (by omega))
    ((L.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f2+edgeBudget 0 as f2))).sum≤
        nativeActualProfileVariation 2 ops*edgeBudget 0 as f2) ∧
      ((L.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R))).sum≤
        nativeActualProfileVariation 2 ops*edgeBudget 0 as R) := by
  dsimp only
  let R:=nativeOriginalHighErrorEnvelope n U bf hf as Mclock Temp
  let f2:=fun j=>((R j)^(2/p))^2
  have hR j : 0 ≤ R j := by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hlo j (hj : j < U) : R j=0 := by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    simp only [hj,ite_true]
  have hf2 j : 0 ≤ f2 j:=sq_nonneg _
  have hlo2 j (hj : j < U) : f2 j=0 := by
    dsimp only [f2]
    rw [hlo j hj,Real.zero_rpow (ne_of_gt (div_pos (by norm_num : (0:ℝ)<2) hp)),zero_pow (by omega : (2:ℕ)≠0)]
  have hΓ : ∀(st : NativeHighSwitchState (Spin n×Bool) as) g,
      g∈st.tree.markedAttach 0→|nativeOriginalHighRowGamma U K st g|≤1 := by
    intro st g hg
    exact nativeOriginalHighRowGamma_abs_le_one ho U K st g
  exact ⟨nativeActualInitialExpansion_high_profile_le ho _ hΓ hi hs hU a ops f2 hf2 hlo2,
    nativeActualInitialExpansion_high_profile_le ho _ hΓ hi hs hU a ops R hR hlo⟩

end OAI.SKFluctuations.Cavity
