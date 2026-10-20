module

public import ComparisonSignedCavitySecondLowActualOriginalConstantB0Budget
public import SKProof.Port.ComparisonActualOriginalQLowB0StarUnobservedCompatibleSourceAlong
public import SKProof.Port.ComparisonActualOriginalQLowB0UnobservedPhysicalSourceAlong
public import SKProof.Port.ComparisonActualOriginalQLowB0ResourceConsumerInterfacesSourceAlong

@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualThetaZeroOverlapMinimum
open NativeOverlapMinimum (ActualSlowWindowChoice)
attribute [local instance] Classical.propDecidable
attribute [local instance] nativeSecondLowSlotFintype
def ActualSecondLowOriginalConstantB0BudgetOnEveryFinalNet_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (saving Couter Cerr C : ℝ)
    (M : (n:ℕ) → ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (w : ℕ → ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (w n).star∈us →
      (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) star
        ∀(U : ℕ),U ≤ as.length → star<U → partitionPoint 0 as U ≤ Couter*W n →
          let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+
            partitionPoint 0 as U/(n+1:ℕ)
          |nativeSecondLowJointLedger n q U b h K g.tree (fun _=>1) [g.embed (singleSlot as),g.mark]/2| ≤
            16*((n+1:ℕ):ℝ)^(-saving)*W n*(M n).xs^2+C*W n*Cerr*rho

theorem actual_second_low_original_constant_B0_budget_original_q
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (Couter : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCouter : 0 ≤ Couter)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ) → ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ → ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_original_q (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃C : ℝ,0<C ∧ ActualSecondLowOriginalConstantB0BudgetOnEveryFinalNet_original_q
      (actualMassSavingExponent m delta/32) Couter (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) C M W w := by
  obtain ⟨Cm,hCm,HM⟩:=eventually_actual_minimum_inherited_second_low_unobserved_moving_entry_budget_original_q
    (D:=D) 0 2 Bclock Temp Cf 0 Couter (Couter+1) hTemp hCf le_rfl hCouter (by linarith)
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have HS:=actual_second_low_unobserved_fixed_error_star_entry_saving_along_original_q 0 2 0 Couter
    hTemp hCf le_rfl hCouter hm hdelta hroom hcl hcu hAz hC0 hCt (fun n=>n) tendsto_id M W hcanonical hWlim w Hsource Hcutoff hw
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨16*Cm,mul_pos (by norm_num) hCm,?_⟩
  filter_upwards [HM,HS,Hsource,HW1,Hcutoff] with n hnM hnS hnSource hnW hnCutoff
  have hxW:(M n).xs ≤ W n:=(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm
  have hxs:(M n).xs ≤ 1:=hxW.trans hnW
  intro L us hus hstar hret hmesh
  filter_upwards [hnM (M n) hnCutoff.1 hnCutoff.2 hnSource hxs L us hus hret hmesh,hnS L us hus hstar hret hmesh]
    with jGrid hgridM hgridS
  dsimp only at hgridM hgridS ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) star
  intro U hU hstarU houter
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hWpos:0<W n:=(M n).hxs.trans_le hxW
  have hdensity:partitionPoint 0 as U ≤ min ((Couter+1)*(M n).directTestWorkingScale) 1:=by
    apply le_min
    · rw [←hcanonical n]
      nlinarith only [houter,hWpos]
    · exact (partitionPoint_mem as ho U).2
  have hpersistent:NativePersistentLowForks star star U g.tree:=
    (native_single_persistentLowForks star star U hU).freshStar 0 (singleSlot as)
  have hleaves:g.tree.leaves ≤ 2:=by
    have H:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g
      (nativeFreshAtSlot_mem (single as) 0 (singleSlot as) star)
    simpa only [single_leaves_exact] using H
  have Hsplit:g.tree.splitIndex (g.embed (singleSlot as)) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,splitIndex_self,
      Nat.min_eq_left (show star ≤ as.length from hstarU.le.trans hU)]
  have haz:g.tree.splitIndex (g.embed (singleSlot as)) g.mark<U:=Hsplit ▸ hstarU
  let G:=nativeSecondLowEmptyOldShape n g.tree
  let forms:Fin 0 → NativeSourceFactorForm:=Fin.elim0
  have hmass:∀e,G.sourceLowMass e ≤ (0:ℝ)*sourceFactorScale (M n).xs (W n) (∅ : Finset (Fin 0)) e:=by
    intro e
    exact Fin.elim0 e
  have hP:(G.canonicalOriginalQSource (M n) forms).restProduct=(fun _=>1):=by
    funext τ
    simp only [ActualNaturalBoundaryShape.restProduct,Fin.prod_univ_zero]
  let starRate:=((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*W n*(M n).xs^2
  let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+partitionPoint 0 as U/(n+1:ℕ)
  let movingRate:=Cm*W n*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*rho
  have Hpoint (j : Fin 8):|nativeSecondLowClassLedger n q U b h K g.tree hU (fun _=>1)
      (g.embed (singleSlot as)) g.mark j false/2| ≤ 2*starRate+2*movingRate:=by
    have BS1:=hgridS U g.tree hU hleaves hstarU houter G forms ∅ (M n).xs le_rfl hxW hmass
      (g.embed (singleSlot as)) g.mark haz j true
    have BS2:=hgridS U g.tree hU hleaves hstarU houter G forms ∅ (M n).xs le_rfl hxW hmass
      (g.embed (singleSlot as)) g.mark haz j false
    have BM1:=hgridM star star U g.tree hU le_rfl hstarU hpersistent hleaves G forms ∅ (M n).xs (W n)
      le_rfl hxW hmass houter hdensity (g.embed (singleSlot as)) g.mark haz j true
    have BM2:=hgridM star star U g.tree hU le_rfl hstarU hpersistent hleaves G forms ∅ (M n).xs (W n)
      le_rfl hxW hmass houter hdensity (g.embed (singleSlot as)) g.mark haz j false
    rw [hP] at BS1 BS2 BM1 BM2
    simp only [sourceMonomialScale,Finset.card_empty,pow_zero] at BS1 BS2 BM1 BM2
    rw [native_second_low_original_unobserved_class_eq_star_moving n q star U b h K g.tree ho hU
      (fun _=>1) (g.embed (singleSlot as)) g.mark j]
    simp only [add_div]
    apply (abs_add_le _ _).trans
    apply (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add BS1 BS2)) BM1)) BM2).trans_eq
    dsimp [starRate,movingRate,rho]
    ring
  rw [native_second_low_single_fresh_graft_joint_ledger_half_eq_unobserved n q star U b h K as ho hU hstarU]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun j _hj=>Hpoint j)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  dsimp [starRate,movingRate,rho]
  ring

end OAI.SKFluctuations.Cavity
