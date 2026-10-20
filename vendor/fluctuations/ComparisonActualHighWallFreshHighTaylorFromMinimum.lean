module

public import ComparisonActualHighWallResourceHighTaylorFromMinimum
public import ComparisonActualGeneralFreshResourceHighTaylorReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_fresh_resource_HIGH_parts_from_minimum
    (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
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
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound →
        seed.length+k ≤ degree →
        
        partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
        partitionPoint 0 as U ≤ Ccut*M.data.d →
        ∀(l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
        let R:=M.data.highErrorEnvelope M.alpha as U
        |(M.data.d⁻¹)^k*actualGeneralOriginalFreshResourceHigherHighPart M.bf M.hf U P part l t| ≤
          |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*
            (C*M.data.d*((T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)))+
              M.data.d*(T.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_resource_HIGH_parts_from_minimum
    (D:=D) degree dOrder (rBound+1) hd p hp hOrder Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut l t hl ht part
  let as:=finiteCutMasses us jGrid
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  let R:=M.data.highErrorEnvelope M.alpha as U
  let f:=fun j=>(R j)^(4/p)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves ≤ rBound+1:=by
    have HH:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 P.live.test.target star)
    omega
  have hlo j (hj : j<U) : R j=0:=by simp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hflo j (hj : j<U) : f j=0:=by
    dsimp only [f]
    rw [hlo j hj,Real.zero_rpow (ne_of_gt (div_pos (by norm_num) (by linarith : 0<p)))]
  have HR:=nativeFreshAtSlot_high_forkCost T 0 P.live.test.target hs R hlo
  have HF:=nativeFreshAtSlot_high_forkCost T 0 P.live.test.target hs f hflo
  change g.tree.forkCost R=T.forkCost R at HR
  change g.tree.forkCost f=T.forkCost f at HF
  rw [actual_general_original_fresh_resource_HIGH_part_eq_two_resources M.bf M.hf U P ho part l t,mul_add]
  have HP:=hj i star U k seed g.tree (P.retarget 0) hP.retarget hi hs hU hg hdepth hmi hms hcut
    (g.embed P.live.test.target) g.mark l t hl ht part
  have HPf:=hj i star U k seed g.tree (P.retarget 0).freeze hP.retarget.freeze hi hs hU hg hdepth hmi hms hcut
    (g.embed P.live.test.target) g.mark l t hl ht part
  simp only [NativeResourceTerm.freeze,abs_neg] at HPf
  change |(M.data.d⁻¹)^k*actualGeneralResourceHigherHighPart M.bf M.hf U (P.retarget 0) part
    (g.embed P.live.test.target) g.mark l t| ≤ |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*
      (C*M.data.d*(g.tree.forkCost f+edgeBudget 0 as f+M.data.d*(g.tree.forkCost R+edgeBudget 0 as R))) at HP
  rw [HF,HR] at HP
  change |(M.data.d⁻¹)^k*actualGeneralResourceHigherHighPart M.bf M.hf U (P.retarget 0).freeze part
    (g.embed P.live.test.target) g.mark l t| ≤ |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*
      (C*M.data.d*(g.tree.forkCost f+edgeBudget 0 as f+M.data.d*(g.tree.forkCost R+edgeBudget 0 as R))) at HPf
  rw [HF,HR] at HPf
  apply ((abs_add_le _ _).trans (add_le_add HP HPf)).trans_eq
  dsimp only [f,R,as]
  ring

end OAI.SKFluctuations.Cavity
