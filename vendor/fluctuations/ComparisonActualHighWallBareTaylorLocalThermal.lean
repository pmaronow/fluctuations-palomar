module

public import ComparisonActualHighWallResourceTaylorLocalThermal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_bare_Taylor_local_thermal_profile
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
        ∀(i star U : ℕ) (seed : List NativeResourceMark)
          (st : NativeActualResourceState (Spin n×Bool) as i star),
        NativeActualResourceGenerated i star U seed st.generation st.tree st.term → i ≤ star → star < U →
        U ≤ as.length → st.tree.leaves ≤ rBound →
        seed.length+st.generation ≤ degree →
        
        partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
        Ccut*M.data.d ≤ 1 → partitionPoint 0 as U ≤ Ccut*M.data.d →
        let R:=M.data.highErrorEnvelope M.alpha as U
        let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
        let ds:=nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ)
        let I:=∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
          (orderedPathS (n+1) M.bf M.hf u)^2)
        |(M.data.d⁻¹)^st.generation*actualGeneralFourCategoryContrast M.bf M.hf U st .higherTaylor| ≤
          |st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*
            (C*(M.data.d*(st.tree.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
              M.data.d*(st.tree.forkCost R+edgeBudget 0 as R))+M.data.d^2*(di+ds+I))) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_fresh_resource_Taylor_local_thermal_profile
    (D:=D) degree dOrder (rBound+1) hd p hp hOrder Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cfinal:=2*C
  have hCfinal : 0 < Cfinal:=by dsimp only [Cfinal];positivity
  refine ⟨Cfinal,hCfinal,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U seed st hP hi hs hU hT hdepth hmi hms hcut1 hcut 
  let as:=finiteCutMasses us jGrid
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  let R:=M.data.highErrorEnvelope M.alpha as U
  let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
  let ds:=nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ)
  let I:=∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
    (orderedPathS (n+1) M.bf M.hf u)^2)
  let f:=fun l=>(R l)^(4/p)
  let profile:=st.tree.forkCost f+edgeBudget 0 as f+M.data.d*(st.tree.forkCost R+edgeBudget 0 as R)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves ≤ rBound+1:=by
    have HH:=st.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem st.tree 0 st.term.live.test.target star)
    omega
  have H0:=hj i star U st.generation seed st.tree st.term hP hi hs hU (by omega) hdepth hmi hms hcut1 hcut 
  have H1:=hj i star U st.generation seed g.tree (st.term.retarget 0) hP.retarget hi hs hU hg hdepth hmi hms hcut1 hcut 
  have hlo l (hl : l<U) : R l=0:=by simp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope,hl,ite_true]
  have hflo l (hl : l<U) : f l=0:=by
    dsimp only [f]
    rw [hlo l hl,Real.zero_rpow (ne_of_gt (div_pos (by norm_num) (by linarith : 0<p)))]
  have HR:=nativeFreshAtSlot_high_forkCost st.tree 0 st.term.live.test.target hs R hlo
  have HF:=nativeFreshAtSlot_high_forkCost st.tree 0 st.term.live.test.target hs f hflo
  change g.tree.forkCost R=st.tree.forkCost R at HR
  change g.tree.forkCost f=st.tree.forkCost f at HF
  change |(M.data.d⁻¹)^st.generation*actualGeneralOriginalFreshResourceTaylorRemainder M.bf M.hf U (st.term.retarget 0)| ≤
    |st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*
      (C*(M.data.d*(g.tree.forkCost f+edgeBudget 0 as f+M.data.d*(g.tree.forkCost R+edgeBudget 0 as R))+M.data.d^2*(di+ds+I))) at H1
  rw [HF,HR] at H1
  let B:=|st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*(M.data.d*profile+M.data.d^2*(di+ds+I)))
  have H0' : |(M.data.d⁻¹)^st.generation*actualGeneralOriginalFreshResourceTaylorRemainder M.bf M.hf U st.term| ≤ B:=by
    convert H0 using 1
  have H1' : |(M.data.d⁻¹)^st.generation*actualGeneralOriginalFreshResourceTaylorRemainder M.bf M.hf U (st.term.retarget 0)| ≤ B:=by
    convert H1 using 1
  have hB : 0 ≤ B:=(abs_nonneg _).trans H0'
  have Hdiff : |(M.data.d⁻¹)^st.generation*actualGeneralOriginalFreshResourceTaylorRemainder M.bf M.hf U st.term-
      (1/2:ℝ)*((M.data.d⁻¹)^st.generation*actualGeneralOriginalFreshResourceTaylorRemainder M.bf M.hf U (st.term.retarget 0))| ≤ 2*B:=by
    have HH:=abs_sub ((M.data.d⁻¹)^st.generation*actualGeneralOriginalFreshResourceTaylorRemainder M.bf M.hf U st.term)
      ((1/2:ℝ)*((M.data.d⁻¹)^st.generation*actualGeneralOriginalFreshResourceTaylorRemainder M.bf M.hf U (st.term.retarget 0)))
    rw [abs_mul (1/2:ℝ),abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at HH
    linarith only [HH,H0',H1',hB]
  rw [actual_general_four_higher_Taylor_contrast_eq_resources M.bf M.hf U st ho]
  have Hring : (M.data.d⁻¹)^st.generation*(actualGeneralOriginalFreshResourceTaylorRemainder M.bf M.hf U st.term-
      (1/2:ℝ)*actualGeneralOriginalFreshResourceTaylorRemainder M.bf M.hf U (st.term.retarget 0))=
      (M.data.d⁻¹)^st.generation*actualGeneralOriginalFreshResourceTaylorRemainder M.bf M.hf U st.term-
        (1/2:ℝ)*((M.data.d⁻¹)^st.generation*actualGeneralOriginalFreshResourceTaylorRemainder M.bf M.hf U (st.term.retarget 0)):=by ring
  rw [Hring]
  exact Hdiff.trans_eq (by dsimp only [B,profile,f,R,as,Cfinal,di,ds,I];ring)

end OAI.SKFluctuations.Cavity
