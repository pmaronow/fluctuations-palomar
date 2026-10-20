module

public import ComparisonSignedCavityInheritedConstantGWordRestoration
public import ComparisonSignedCavityOriginalLongitudinalProfileBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem eventually_actual_minimum_inherited_constant_longitudinal_restoration_profile
    (rBound : ℕ) (p : ℝ) (hp : 2 < p)
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cq : ℝ,0 < Cq ∧∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀W : ℝ,M.xs ≤ W → partitionPoint 0 as U ≤ Ccut*W →∀a : T.Slot,
          let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as Mclock Temp
          let f2:=fun j=>((R j)^(2/p))^2
          |nativeOriginalLongitudinalRestoration n q U b h K S T (fun _=>1) a| ≤
            (pairForkVariation (rBound+3)*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p))*
              nativeOriginalRestorationProfileVariation rBound*(T.forkCost f2+edgeBudget 0 as f2)+
            (absJetVariation (rBound+3) 1*(Cq*W))*forkVariation rBound 3*
              (T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Cq,hCq,H⟩:=eventually_actual_minimum_inherited_constant_G_word_restoration_original_budget
    (D:=D) rBound p hp Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cq,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT W hxW hcut a
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  have Hsum : |nativeOriginalLongitudinalRestoration n
      (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U b h K S T (fun _=>1) a| ≤
      ((nativeOriginalGMarkedWords T).map (fun g=>|g.coefficient| *
        nativeOriginalGWordRestorationCost g U (rBound+3) M.bf M.hf K a (4*Cf+2*Temp) Temp p 1 1 (Cq*W))).sum := by
    rw [native_original_longitudinal_restoration_eq_words]
    exact native_original_G_word_weighted_sum_abs_le T _ _
      (fun g _=>hgrid U T hU hT W hxW hcut g a)
  have Hwords:=native_original_G_word_restoration_sum_le_profiles T
    (finiteCutMasses_ordered us hus jGrid) U (rBound+3) rBound hT M.bf M.hf K a
    (4*Cf+2*Temp) Temp p 1 1 (Cq*W) hTemp (by norm_num) (by norm_num)
    (mul_nonneg hCq.le (M.hxs.le.trans hxW))
  exact Hsum.trans (by simpa only [mul_one] using Hwords)

end OAI.SKFluctuations.Cavity
