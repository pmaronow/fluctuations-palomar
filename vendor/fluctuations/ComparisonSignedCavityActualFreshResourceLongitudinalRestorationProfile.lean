module

public import ComparisonSignedCavityActualResourceLongitudinalRestorationFromMinimum
public import ComparisonSignedCavityActualCenteredResourceLongitudinalRestoration
public import ComparisonSignedCavityTransientForkCost

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem eventually_actual_minimum_inherited_centered_resource_longitudinal_restoration_profile
    (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
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
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound →
        seed.length+k ≤ degree →
        ∀x W : ℝ,M.xs ≤ x → x ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀a : T.Slot,
        let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
        |(W⁻¹)^k*nativeActualOriginalCenteredResourceLongitudinalRestoration M U P a| ≤
          |P.coefficient| *nativeResourceScale x W 1 seed*
            (C*(T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
              W*(T.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_resource_longitudinal_restoration_from_minimum
    (D:=D) degree dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth x W hx hxW hW1 hmi hms hcut a
  have ho:=finiteCutMasses_ordered us hus jGrid
  rw [native_actual_centered_resource_longitudinal_restoration_eq_two_resources M U P ho a,mul_add]
  have HP:=hj i star U k seed T P hP hi hs hU hT hdepth x W hx hxW hW1 hmi hms hcut a
  have HF:=hj i star U k seed T P.freeze hP.freeze hi hs hU hT hdepth x W hx hxW hW1 hmi hms hcut a
  simp only [NativeResourceTerm.freeze,abs_neg] at HF
  apply ((abs_add_le _ _).trans (add_le_add HP HF)).trans_eq
  ring

theorem eventually_actual_minimum_inherited_fresh_resource_longitudinal_restoration_profile
    (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
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
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound →
        seed.length+k ≤ degree →
        ∀x W : ℝ,M.xs ≤ x → x ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀right : Bool,
        let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
        |(W⁻¹)^k*nativeActualOriginalFreshResourceLongitudinalRestoration M U P right| ≤
          |P.coefficient| *nativeResourceScale x W 1 seed*
            (C*(T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
              W*(T.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_centered_resource_longitudinal_restoration_profile
    (D:=D) degree dOrder (rBound+1) hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth x W hx hxW hW1 hmi hms hcut right
  let as:=finiteCutMasses us jGrid
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let f:=fun j=>(R j)^(4/p)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves ≤ rBound+1:=by
    have HH:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 P.live.test.target star)
    omega
  have H0:=hj i star U k seed g.tree (P.retarget 0) hP.retarget hi hs hU hg hdepth
    x W hx hxW hW1 hmi hms hcut (if right then g.mark else g.embed P.live.test.target)
  have hlo j (hj : j<U) : R j=0:=by
    simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hflo j (hj : j<U) : f j=0:=by
    dsimp only [f]
    rw [hlo j hj,Real.zero_rpow (by positivity : 4/p≠0)]
  have Hf:=nativeFreshAtSlot_high_forkCost T 0 P.live.test.target hs f hflo
  have HR:=nativeFreshAtSlot_high_forkCost T 0 P.live.test.target hs R hlo
  rw [native_actual_fresh_resource_longitudinal_restoration_eq_centered_retarget M U P ho right]
  change |(W⁻¹)^k*nativeActualOriginalCenteredResourceLongitudinalRestoration M U (P.retarget 0)
    (if right then g.mark else g.embed P.live.test.target)| ≤ |P.coefficient| *nativeResourceScale x W 1 seed*
      (C*(T.forkCost f+edgeBudget 0 as f+W*(T.forkCost R+edgeBudget 0 as R)))
  change |(W⁻¹)^k*nativeActualOriginalCenteredResourceLongitudinalRestoration M U (P.retarget 0)
    (if right then g.mark else g.embed P.live.test.target)| ≤ |P.coefficient| *nativeResourceScale x W 1 seed*
      (C*(g.tree.forkCost f+edgeBudget 0 as f+W*(g.tree.forkCost R+edgeBudget 0 as R))) at H0
  simpa only [show g.tree.forkCost f=T.forkCost f from Hf,
    show g.tree.forkCost R=T.forkCost R from HR] using H0

end OAI.SKFluctuations.Cavity
