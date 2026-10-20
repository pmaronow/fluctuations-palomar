module

public import ComparisonSignedCavityActualHighTaylorParts
public import ComparisonSignedCavityActualHighTaylorProfilePrice
public import ComparisonSignedCavityInheritedConstantCenteredFixedLowOneHigh
public import ComparisonSignedCavityInheritedConstantCenteredFixedLowTwoHigh
public import ComparisonSignedCavityInheritedConstantCenteredTransientHigh
public import ComparisonSignedCavityInheritedErrorTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000

theorem eventually_actual_minimum_inherited_constant_HIGH_parts_profile
    (rBound dOrder : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀W : ℝ,M.xs ≤ W → W ≤ 1 → partitionPoint 0 as U ≤ Ccut*W →
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
          let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
          |nativeActualHigherHighPart part n q U b h K T (fun _=>1) a z l t| ≤
            C*W*
              (T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
                W*(T.forkCost R+edgeBudget 0 as R)) := by
  have hLowOrder : 2*(p/(p-2)) ≤ ((2*dOrder:ℕ):ℝ):=by
    push_cast
    linarith
  obtain ⟨C₀,hC₀,H₀⟩:=eventually_actual_minimum_inherited_constant_centered_fixed_low_two_one_high_budget
    (D:=D) rBound Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨C₁,hC₁,H₁⟩:=eventually_actual_minimum_inherited_constant_centered_fixed_low_one_two_high_budget
    (D:=D) rBound dOrder hd p hp hLowOrder Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨C₂,hC₂,H₂⟩:=eventually_actual_minimum_inherited_constant_centered_transient_HIGH_budget
    (D:=D) rBound Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=C₀+C₁+C₂+1
  have hC : 0 < C:=by dsimp only [C];linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [H₀,H₁,H₂] with n hn₀ hn₁ hn₂
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn₀ M hsource hxs L us hus hret hmesh,
    hn₁ M hsource hxs L us hus hret hmesh,hn₂ M hsource hxs L us hus hret hmesh]
    with jGrid hj₀ hj₁ hj₂
  dsimp only at hj₀ hj₁ hj₂ ⊢
  intro U T hU hT W hxW hW₁ hcut a z l t hl ht part
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let F₁:=T.forkCost R+edgeBudget 0 as R
  let F₂:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))
  let Z : ℝ:=1
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 ≤ W:=(M.hxs.trans_le hxW).le
  have hZ : 0 ≤ Z:=zero_le_one
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hF₁ : 0 ≤ F₁:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hF₂ : 0 ≤ F₂:=add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
    (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
  have HP₀:=actual_minimum_inherited_current_high_profile_le_original M Temp Cf hTemp hCf hsource hxs
    T ho U (show (0:ℝ)∈Icc 0 1 by norm_num) ht (e:=1) (by norm_num)
  simp only [Real.rpow_one] at HP₀
  have HP₁:=actual_minimum_inherited_current_high_profile_le_original M Temp Cf hTemp hCf hsource hxs
    T ho U (show (0:ℝ)∈Icc 0 1 by norm_num) ht (e:=4/p) (by positivity)
  have HP₂:=actual_minimum_inherited_current_high_profile_le_original M Temp Cf hTemp hCf hsource hxs
    T ho U hl ht (e:=1) (by norm_num)
  simp only [Real.rpow_one] at HP₂
  fin_cases part
  · change |nativeCenteredFixedLowHigh n q U b h K T (fun _=>1) a z 2 1 t| ≤ _
    have H:=hj₀ U T t hU ht hT W hxW hcut a z
    apply (H.trans (mul_le_mul_of_nonneg_left HP₀ (by positivity))).trans
    simpa only [Z,mul_one] using actual_high_one_error_price_le hC.le (by dsimp only [C];linarith) hW hZ hF₁ hF₂
  · change |nativeCenteredFixedLowHigh n q U b h K T (fun _=>1) a z 1 2 t| ≤ _
    have H:=hj₁ U T t hU ht hT W hxW hcut a z
    apply (H.trans (mul_le_mul_of_nonneg_left HP₁ (by positivity))).trans
    simpa only [Z,mul_one] using actual_high_two_error_price_le hC.le (by dsimp only [C];linarith) hW hZ hF₁ hF₂
  · change |nativeCenteredTransientHighThird n q U b h K T (fun _=>1) a z l t| ≤ _
    have H:=hj₂ U T l t hU hl ht hT W hxW hcut a z
    apply (H.trans (mul_le_mul_of_nonneg_left HP₂ (by positivity))).trans
    simpa only [Z,mul_one] using actual_high_transient_price_le hC.le hC₂.le (by dsimp only [C];linarith) hW hW₁ hZ hF₁ hF₂

end OAI.SKFluctuations.Cavity
