module

public import ComparisonSignedCavityInheritedConstantGRestoration
public import ComparisonSignedCavityGRestorationWords
public import ComparisonSignedCavityGRestorationDiagonal
public import ComparisonSignedCavityGRestorationOriginalBudget
public import ComparisonSignedCavityInheritedErrorTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
theorem eventually_actual_minimum_inherited_constant_G_word_restoration_original_budget
    (rBound : ℕ)
    (p : ℝ) (hp : 2 < p)
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cq : ℝ,0 < Cq ∧ ∀ᶠn : ℕ in atTop,
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
        ∀W : ℝ,M.xs ≤ W → partitionPoint 0 as U ≤ Ccut*W →
        ∀(g : NativeOriginalGMarkedWord T) (a : T.Slot),
          |nativeActualLawRestorationRemainder n q U b h K g.tree
            (g.originalRestorationTest U K b S (fun _=>1) a)| ≤
            nativeOriginalGWordRestorationCost g U (rBound+3) M.bf M.hf K a Mclock Temp p
              1
              1 (Cq*W) := by
  obtain ⟨Cq,hCq,HL⟩:=eventually_actual_minimum_inherited_constant_G_low_restoration
    (D:=D) (rBound+3) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cq,hCq,?_⟩
  filter_upwards [HL] with n hnL
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hnL M hsource hxs L us hus hret hmesh] with jGrid hgridL
  dsimp only at hgridL ⊢
  intro U T hU hT W hxW hcut g a
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as Mclock Temp
  let j:=g.tree.splitIndex (g.z.embed g.r.mark) g.z.mark
  let κ:=|(1/2:ℝ)*fullScalarCutConnected4 g.tree U K
    (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
    (g.z.embed g.r.mark) g.z.mark|
  let CH : ℝ:=1
  let CL : ℝ:=1
  let BH:=κ*(ClockTree.pairForkVariation (rBound+3)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
    (R j)^(2/p)*(g.tree.forkCost (fun j=>(R j)^(2/p))+ClockTree.edgeBudget 0 as (fun j=>(R j)^(2/p))))
  let BL:=κ*(ClockTree.absJetVariation (rBound+3) 1*CL*R j*(Cq*W))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  by_cases hdiag : g.z.embed g.r.mark=g.z.mark
  · rw [nativeOriginalGWordRestorationCost,ite_eq_left hdiag,
      actual_minimum_G_word_diagonal_restoration_zero M T ho g U (fun _=>1) a hdiag,abs_zero]
  · have hCH : 0 ≤ CH:=by dsimp [CH];positivity
    have hCL : 0 ≤ CL:=by dsimp [CL];positivity
    have hκ : 0 ≤ κ:=abs_nonneg _
    have hW : 0 ≤ W := M.hxs.le.trans hxW
    have hPV := ClockTree.pairForkVariation_nonneg (rBound+3)
    have hAV := ClockTree.absJetVariation_nonneg (rBound+3) 1
    have hR (j : ℕ) : 0 ≤ R j:=by
      dsimp only [R,nativeOriginalHighErrorEnvelope]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
          (add_nonneg (Real.sqrt_nonneg _) (by positivity))
    have hH (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
        |cutMixedJet n q U b h K g.tree
          (g.originalRestorationTest U K b S (fun _=>1) a) 0 0 0 t| ≤ BH:=by
      have Htest : g.originalRestorationTest U K b S (fun _=>1) a=
          nativeOriginalHighGAtom g.tree U K b S
            (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
            (g.z.embed g.r.mark) g.z.mark := by
        funext σ
        simp only [NativeOriginalGMarkedWord.originalRestorationTest,one_mul]
      rw [Htest]
      have Hleaves : g.tree.leaves ≤ rBound+3:=g.leaves_le.trans (by omega)
      have H:=actual_inherited_constant_G_high_restoration_bound M hsource hTemp p hp (rBound+3)
        as ho U g.tree t hU ht Hleaves
        (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
        (g.z.embed g.r.mark) g.z.mark hdiag
      dsimp only at H
      change _ ≤ κ*(pairForkVariation (rBound+3)*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
        (nativeWholeLawErrorRadius n as (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) j)^(2/p)*
        nativeWholeLawProfileCost n (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) g.tree (2/p)) at H
      have HC : pairForkVariation (rBound+3)=pairForkVariation (rBound+3)*CH:=by simp only [CH,mul_one]
      rw [HC] at H
      apply H.trans
      have HR:=Real.rpow_le_rpow (nativeWholeLawErrorRadius_nonneg n as _ _ j)
        (actual_minimum_inherited_current_high_error_radius_le_original (l:=0) (t:=t) M Temp Cf hTemp hCf hsource hxs ho U
          (by norm_num) ht j (g.tree.splitIndex_le_clockLength _ _)) (show 0 ≤ 2/p by positivity)
      have HC:=actual_minimum_inherited_current_high_profile_le_original (l:=0) (t:=t) M Temp Cf hTemp hCf hsource hxs g.tree ho U
        (by norm_num) ht (show 0 ≤ 2/p by positivity)
      have hProf := native_whole_law_profile_cost_nonneg n ho
        (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) g.tree (2/p)
      have hRj := hR j
      dsimp only [BH]
      gcongr
    have hL (l : ℝ) (hl : l∈Icc (0:ℝ) 1) :
        |cutLowJet n q U b h K g.tree
          (g.originalRestorationTest U K b S (fun _=>1) a) 0 1 l 1| ≤ BL:=by
      have Htest : g.originalRestorationTest U K b S (fun _=>1) a=
          nativeOriginalHighGAtom g.tree U K b S
            (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
            (g.z.embed g.r.mark) g.z.mark := by
        funext σ
        simp only [NativeOriginalGMarkedWord.originalRestorationTest,one_mul]
      rw [Htest]
      have Hleaves : g.tree.leaves ≤ rBound+3:=g.leaves_le.trans (by omega)
      have H:=hgridL U g.tree l hU hl Hleaves W hxW hcut
        (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
        (g.z.embed g.r.mark) g.z.mark hdiag
      apply H.trans
      have HR:=actual_minimum_inherited_current_high_error_radius_le_original (l:=l) (t:=1) M Temp Cf hTemp hCf hsource hxs ho U
        hl (by norm_num) j (g.tree.splitIndex_le_clockLength _ _)
      dsimp only [BL]
      gcongr
    have H:=native_actual_law_restoration_abs_le n q U b h K g.tree
      (g.originalRestorationTest U K b S (fun _=>1) a) BH BL hH hL
    rw [nativeOriginalGWordRestorationCost,ite_eq_right hdiag]
    convert H using 1
    dsimp only [BH,BL,κ,CH,CL,R,j,Mclock,K,b,h,S,as]
    ring

end OAI.SKFluctuations.Cavity
