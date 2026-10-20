module

public import ComparisonSignedCavityActualHighTaylorParts
public import ComparisonSignedCavityActualHighTaylorProfilePrice
public import ComparisonActualHighWallCenteredFixedLowOneHigh
public import ComparisonActualHighWallCenteredFixedLowTwoHigh
public import ComparisonActualHighWallCenteredTransientHigh
public import ComparisonActualHighWallHighProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000

theorem eventually_actual_high_wall_canonical_HIGH_parts_profile
    (aDegree rBound dOrder : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm),
          partitionPoint 0 as U ≤ Ccut*M.data.d →
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
          let R:=M.data.highErrorEnvelope M.alpha as U
          |nativeActualHigherHighPart part n q U b h K T (G.canonicalHighWallSource M forms).product a z l t| ≤
            C*M.data.d*M.data.d^aDegree*
              ((T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)))+
                M.data.d*(T.forkCost R+edgeBudget 0 as R)) := by
  have hLowOrder : 2*(p/(p-2)) ≤ ((2*dOrder:ℕ):ℝ):=by
    push_cast
    linarith
  obtain ⟨C₀,hC₀,H₀⟩:=eventually_actual_high_wall_canonical_centered_fixed_low_two_one_high_budget
    (D:=D) aDegree rBound Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨C₁,hC₁,H₁⟩:=eventually_actual_high_wall_canonical_centered_fixed_low_one_two_high_budget
    (D:=D) aDegree rBound dOrder dOrder hd hd p hp hOrder hLowOrder Bclock Cmass Ccut
    hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨C₂,hC₂,H₂⟩:=eventually_actual_high_wall_canonical_centered_transient_HIGH_budget
    (D:=D) aDegree rBound Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=C₀+C₁+C₂+1
  have hC : 0 < C:=by dsimp only [C];linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [H₀,H₁,H₂] with n hn₀ hn₁ hn₂
  intro M hwork L us hus hret hmesh
  filter_upwards [hn₀ M hwork L us hus hret hmesh,
    hn₁ M hwork L us hus hret hmesh,hn₂ M hwork L us hus hret hmesh]
    with jGrid hj₀ hj₁ hj₂
  dsimp only at hj₀ hj₁ hj₂ ⊢
  intro U T hU hT G forms hcut hmass a z l t hl ht part
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=M.data.highErrorEnvelope M.alpha as U
  let F₁:=T.forkCost R+edgeBudget 0 as R
  let F₂:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))
  let Z:=M.data.d^aDegree
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 ≤ M.data.d:=M.data.hd.le
  have hZ : 0 ≤ Z:=pow_nonneg M.data.hd.le _
  have hR j : 0 ≤ R j:=by
    dsimp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ M.data.hTpos.le)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hF₁ : 0 ≤ F₁:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hF₂ : 0 ≤ F₂:=add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
    (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
  have HP₀:=M.data.current_high_profile_le_original M.alpha
    T ho U (show (0:ℝ)∈Icc 0 1 by norm_num) ht (exponent:=1) (by norm_num)
  simp only [Real.rpow_one] at HP₀
  have HP₁:=M.data.current_high_profile_le_original M.alpha
    T ho U (show (0:ℝ)∈Icc 0 1 by norm_num) ht (exponent:=4/p) (by positivity)
  have HP₂:=M.data.current_high_profile_le_original M.alpha
    T ho U hl ht (exponent:=1) (by norm_num)
  simp only [Real.rpow_one] at HP₂
  fin_cases part
  · change |nativeCenteredFixedLowHigh n q U b h K T (G.canonicalHighWallSource M forms).product a z 2 1 t| ≤ _
    have H:=hj₀ U T t hU ht hT G forms hcut hmass a z
    apply (H.trans (mul_le_mul_of_nonneg_left HP₀ (by positivity))).trans
    exact actual_high_one_error_price_le hC.le (by dsimp only [C];linarith) hW hZ hF₁ hF₂
  · change |nativeCenteredFixedLowHigh n q U b h K T (G.canonicalHighWallSource M forms).product a z 1 2 t| ≤ _
    have H:=hj₁ U T t hU ht hT G forms hcut hmass a z
    apply (H.trans (mul_le_mul_of_nonneg_left HP₁ (by positivity))).trans
    exact actual_high_two_error_price_le hC.le (by dsimp only [C];linarith) hW hZ hF₁ hF₂
  · change |nativeCenteredTransientHighThird n q U b h K T (G.canonicalHighWallSource M forms).product a z l t| ≤ _
    have H:=hj₂ U T l t hU hl ht hT G forms hcut hmass a z
    apply (H.trans (mul_le_mul_of_nonneg_left HP₂ (by positivity))).trans
    exact actual_high_transient_price_le hC.le hC₂.le (by dsimp only [C];linarith) hW M.data.hd1 hZ hF₁ hF₂

end OAI.SKFluctuations.Cavity
