module

public import ComparisonSignedCavitySecondLowConstantStarOnlySource
public import ComparisonSignedCavitySecondLowInheritedUnobservedMovingEntryBudget
public import ComparisonSignedCavitySecondLowActualFixedErrorStarEntrySavingAlong

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option autoImplicit false
set_option maxHeartbeats 40000000

def ActualSecondLowStarOnlyUnobservedBudgetOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (aDegree rBound : ℕ) (saving Cmass Couter Cerr Cmoving : ℝ)
    (dim : ℕ→ℕ)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (w : ℕ → ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (w n).star∈us →
      (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ → RestCoordinate (dim n) → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (hU : U ≤ as.length),
          star<U → NativePersistentLowForks star star U T → T.leaves ≤ rBound →
          partitionPoint 0 as U ≤ Couter*W n →
        ∀(G : ActualNaturalBoundaryShape (dim n) aDegree T)
          (forms : Fin aDegree → NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x : ℝ),(M n).xs ≤ x → x ≤ W n →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial e) →
        ∀(a z : T.Slot),T.splitIndex a z=star →
          let p0:=sourceMonomialScale x (W n) initial
          let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+
            partitionPoint 0 as U/(dim n+1:ℕ)
          |∑j : Fin 8,nativeSecondLowClassLedger (dim n) q U b h K T hU
            (G.canonicalMinimumSource (M n) forms).restProduct a z j false/2| ≤
            16*((dim n+1:ℕ):ℝ)^(-saving)*W n*(M n).xs^2*p0+
            Cmoving*W n*Cerr*rho*p0

theorem actual_second_low_star_only_unobserved_budget_along
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (aDegree rBound : ℕ) (Cmass Couter : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass) (hCouter : 0 ≤ Couter)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ → ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cmoving : ℝ,0<Cmoving ∧
      ActualSecondLowStarOnlyUnobservedBudgetOnEveryFinalNetAlong aDegree rBound
        (actualMassSavingExponent m delta/32) Cmass Couter
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Cmoving dim M W w := by
  obtain ⟨Cm,hCmRate,HM⟩:=eventually_actual_minimum_inherited_second_low_unobserved_moving_entry_budget
    (D:=D) aDegree rBound Bclock Temp Cf Cmass Couter (Couter+1) hTemp hCf hCm hCouter (by linarith)
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have HS:=actual_second_low_unobserved_fixed_error_star_entry_saving_along aDegree rBound Cmass Couter
    hTemp hCf hCm hCouter hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim w Hsource hw
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨16*Cm,mul_pos (by norm_num) hCmRate,?_⟩
  filter_upwards [hdim.eventually HM,HS,Hsource,HW1] with n hnM hnS hnSource hnW
  have hxs:(M n).xs≤1:=((M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm).trans hnW
  intro L us hus hstar hret hmesh
  filter_upwards [hnM (M n) hnSource hxs L us hus hret hmesh,
    hnS L us hus hstar hret hmesh] with jGrid hgridM hgridS
  dsimp only at hgridM hgridS ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  intro U T hU hstarU hpersistent hT houter G forms initial x hxsx hxW hmass a z hsplit
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have haz:T.splitIndex a z<U:=hsplit ▸ hstarU
  have hW:0<W n:=(M n).hxs.trans_le (hxsx.trans hxW)
  have hdensity:partitionPoint 0 as U≤ min ((Couter+1)*(M n).canonicalDirectTestBandScale) 1:=by
    apply le_min
    · rw [←hcanonical n];nlinarith only [houter,hW]
    · exact (partitionPoint_mem as ho U).2
  let P:=(G.canonicalMinimumSource (M n) forms).restProduct
  let p0:=sourceMonomialScale x (W n) initial
  let starRate:=((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*W n*(M n).xs^2*p0
  let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+partitionPoint 0 as U/(dim n+1:ℕ)
  let movingRate:=Cm*W n*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*rho*p0
  have Hpoint (j : Fin 8):|nativeSecondLowClassLedger (dim n) q U b h K T hU P a z j false/2|≤
      2*starRate+2*movingRate:=by
    have BS1:=hgridS U T hU hT hstarU houter G forms initial x hxsx hxW hmass a z haz j true
    have BS2:=hgridS U T hU hT hstarU houter G forms initial x hxsx hxW hmass a z haz j false
    have BM1:=hgridM star star U T hU le_rfl hstarU hpersistent hT G forms initial x (W n)
      hxsx hxW hmass houter hdensity a z haz j true
    have BM2:=hgridM star star U T hU le_rfl hstarU hpersistent hT G forms initial x (W n)
      hxsx hxW hmass houter hdensity a z haz j false
    rw [native_second_low_original_unobserved_class_eq_star_moving (dim n) q star U b h K T ho hU P a z j]
    simp only [add_div]
    apply (abs_add_le _ _).trans
    apply (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add BS1 BS2)) BM1)) BM2).trans_eq
    dsimp [starRate,movingRate,rho,P,p0,K,q,b,h,as]
    ring
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun j _=>Hpoint j)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  dsimp [starRate,movingRate,rho,P,p0,K,q,b,h,as]
  ring

end OAI.SKFluctuations.Cavity
