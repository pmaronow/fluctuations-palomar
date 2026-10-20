module

public import ComparisonSignedCavitySecondLowActualUnobservedCompleteBudgetAlong
public import ComparisonSignedCavitySecondLowActualUnobservedTotalBudgetAlong
public import SKProof.Port.ComparisonActualOriginalQLowB0InitialPhysicalConsumerSourceAlong
public import SKProof.Port.ComparisonActualOriginalQLowB0StarUnobservedCompatibleSourceAlong
public import SKProof.Port.ComparisonActualOriginalQLowB0UnobservedPhysicalSourceAlong

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
private theorem low_b0_initial_abs_add_five_le (a b c d e : ℝ) :
    |a+b+c+d+e| ≤ |a|+|b|+|c|+|d|+|e| := by
  calc
    _ ≤ |a+b+c+d|+|e|:=abs_add_le _ _
    _ ≤ (|a+b+c|+|d|)+|e|:=add_le_add (abs_add_le _ _) le_rfl
    _ ≤ ((|a+b|+|c|)+|d|)+|e|:=add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    _ ≤ _:=add_le_add (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl) le_rfl

def ActualSecondLowUnobservedCompleteBudgetOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (aDegree rBound : ℕ) (saving Cmass Ccut Couter Cerr Cinitial Cmoving : ℝ)
    (dim : ℕ→ℕ)
    (M : (n:ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (w : ℕ → ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (w n).star∈us →
      (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ → RestCoordinate (dim n) → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i V U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (hU : U ≤ as.length),
          0<V → i<V → V ≤ star → star<U → NativePersistentLowForks i star U T →
          partitionPoint 0 as V ≤ Ccut*(M n).xs → T.leaves ≤ rBound →
          partitionPoint 0 as U ≤ Couter*W n →
        ∀(G : ActualNaturalBoundaryShape (dim n) aDegree T)
          (forms : Fin aDegree → NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x : ℝ),(M n).xs ≤ x → x ≤ W n →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial e) →
        ∀(a z : T.Slot),T.splitIndex a z=star → ∀j : Fin 8,
          let p0:=sourceMonomialScale x (W n) initial
          let di:=nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf as i+1/(dim n+1:ℕ)
          let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+
            partitionPoint 0 as U/(dim n+1:ℕ)
          |nativeSecondLowClassLedger (dim n) q U b h K T hU
            (G.canonicalOriginalQSource (M n) forms).restProduct a z j false/2| ≤
            Cinitial*partitionPoint 0 as U*(M n).xs*Cerr*di*p0+
            2*((dim n+1:ℕ):ℝ)^(-saving)*W n*(M n).xs^2*p0+
            Cmoving*W n*Cerr*rho*p0

theorem actual_second_low_unobserved_complete_budget_along_original_q
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (aDegree rBound : ℕ) (Cmass Ccut Couter : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hCouter : 0 ≤ Couter)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ → ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_original_q (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cinitial Cmoving : ℝ,0<Cinitial ∧ 0<Cmoving ∧
      ActualSecondLowUnobservedCompleteBudgetOnEveryFinalNetAlong_original_q aDegree rBound
        (actualMassSavingExponent m delta/32) Cmass Ccut Couter
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Cinitial Cmoving dim M W w := by
  obtain ⟨Ci,hCi,HI⟩:=eventually_actual_minimum_inherited_second_low_unobserved_initial_entry_budget_original_q
    (D:=D) aDegree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCm hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cm,hCmRate,HM⟩:=eventually_actual_minimum_inherited_second_low_unobserved_moving_entry_budget_original_q
    (D:=D) aDegree rBound Bclock Temp Cf Cmass Couter (Couter+1) hTemp hCf hCm hCouter (by linarith)
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have HS:=actual_second_low_unobserved_fixed_error_star_entry_saving_along_original_q aDegree rBound Cmass Couter
    hTemp hCf hCm hCouter hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim w Hsource Hcutoff hw
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Ci,2*Cm,hCi,mul_pos (by norm_num) hCmRate,?_⟩
  filter_upwards [hdim.eventually HI,hdim.eventually HM,HS,Hsource,HW1,Hcutoff] with n hnI hnM hnS hnSource hnW hnCutoff
  have hxs:(M n).xs ≤ 1:=((M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm).trans hnW
  intro L us hus hstar hret hmesh
  filter_upwards [hnI (M n) hnCutoff.1 hnCutoff.2 hnSource hxs L us hus hret hmesh,
    hnM (M n) hnCutoff.1 hnCutoff.2 hnSource hxs L us hus hret hmesh,hnS L us hus hstar hret hmesh] with jGrid hgridI hgridM hgridS
  dsimp only at hgridI hgridM hgridS ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ → RestCoordinate (dim n) → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  intro i V U T hU hV hiV hVstar hstarU hpersistent hcut hT houter G forms initial x hxsx hxW hmass a z hsplit j
  have hiStar:i<star:=lt_of_lt_of_le hiV hVstar
  have hVU:V ≤ U:=hVstar.trans hstarU.le
  have haz:T.splitIndex a z<U:=hsplit ▸ hstarU
  have htarget:i<T.splitIndex a z:=hsplit ▸ hiStar
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hWpos:0<W n:=(M n).hxs.trans_le (hxsx.trans hxW)
  have hdensity:partitionPoint 0 as U ≤ min ((Couter+1)*(M n).directTestWorkingScale) 1:=by
    apply le_min
    · rw [←hcanonical n]
      nlinarith only [houter,hWpos]
    · exact (partitionPoint_mem as ho U).2
  have Binitial:=hgridI U V T hU hV hVU hcut hT G forms initial x (W n) hxsx hxW hmass a z haz i hiV j
  have Bstar1:=hgridS U T hU hT hstarU houter G forms initial x hxsx hxW hmass a z haz j true
  have Bstar2:=hgridS U T hU hT hstarU houter G forms initial x hxsx hxW hmass a z haz j false
  have Bmoving1:=hgridM i star U T hU hiStar.le hstarU hpersistent hT G forms initial x (W n) hxsx hxW
    hmass houter hdensity a z haz j true
  have Bmoving2:=hgridM i star U T hU hiStar.le hstarU hpersistent hT G forms initial x (W n) hxsx hxW
    hmass houter hdensity a z haz j false
  let P:=(G.canonicalOriginalQSource (M n) forms).restProduct
  let vi:=nativeSecondLowInitialUnobservedClassLedger (dim n) q i U b h K T hU P a z j
  let vs1:=nativeSecondLowFixedErrorUnobservedClassLedger (dim n) q star U b h K T hU P a z j true
  let vs2:=nativeSecondLowFixedErrorUnobservedClassLedger (dim n) q star U b h K T hU P a z j false
  let vm1:=nativeSecondLowMovingErrorUnobservedClassLedger (dim n) q i star U b h K T hU P a z j true
  let vm2:=nativeSecondLowMovingErrorUnobservedClassLedger (dim n) q i star U b h K T hU P a z j false
  have HsourceEq:=native_second_low_original_unobserved_class_eq_initial_star_moving (dim n) q i star U b h K T ho hU P
    a z htarget haz (ne_of_lt hiStar) j
  change nativeSecondLowClassLedger (dim n) q U b h K T hU P a z j false=vi+vs1+vs2+vm1+vm2 at HsourceEq
  rw [HsourceEq]
  have Hhalf:(vi+vs1+vs2+vm1+vm2)/2=vi/2+vs1/2+vs2/2+vm1/2+vm2/2:=by ring
  rw [Hhalf]
  apply (low_b0_initial_abs_add_five_le _ _ _ _ _).trans
  apply (add_le_add (add_le_add (add_le_add (add_le_add Binitial Bstar1) Bstar2) Bmoving1) Bmoving2).trans_eq
  ring

def ActualSecondLowUnobservedTotalBudgetOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (aDegree rBound : ℕ) (saving Cmass Ccut Couter Cerr Cinitial Cmoving : ℝ)
    (dim : ℕ→ℕ)
    (M : (n:ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (w : ℕ → ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (w n).star∈us →
      (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ → RestCoordinate (dim n) → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i V U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (hU : U ≤ as.length),
          0<V → i<V → V ≤ star → star<U → NativePersistentLowForks i star U T →
          partitionPoint 0 as V ≤ Ccut*(M n).xs → T.leaves ≤ rBound →
          partitionPoint 0 as U ≤ Couter*W n →
        ∀(G : ActualNaturalBoundaryShape (dim n) aDegree T)
          (forms : Fin aDegree → NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x : ℝ),(M n).xs ≤ x → x ≤ W n →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial e) →
        ∀(a z : T.Slot),T.splitIndex a z=star →
          let p0:=sourceMonomialScale x (W n) initial
          let di:=nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf as i+1/(dim n+1:ℕ)
          let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+
            partitionPoint 0 as U/(dim n+1:ℕ)
          |∑j : Fin 8,nativeSecondLowClassLedger (dim n) q U b h K T hU
            (G.canonicalOriginalQSource (M n) forms).restProduct a z j false/2| ≤
            Cinitial*partitionPoint 0 as U*(M n).xs*Cerr*di*p0+
            16*((dim n+1:ℕ):ℝ)^(-saving)*W n*(M n).xs^2*p0+
            Cmoving*W n*Cerr*rho*p0

theorem actual_second_low_unobserved_total_budget_along_original_q
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (aDegree rBound : ℕ) (Cmass Ccut Couter : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hCouter : 0 ≤ Couter)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ → ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_original_q (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cinitial Cmoving : ℝ,0<Cinitial ∧ 0<Cmoving ∧
      ActualSecondLowUnobservedTotalBudgetOnEveryFinalNetAlong_original_q aDegree rBound
        (actualMassSavingExponent m delta/32) Cmass Ccut Couter
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Cinitial Cmoving dim M W w := by
  obtain ⟨Ci,Cm,hCi,hCm,H⟩:=actual_second_low_unobserved_complete_budget_along_original_q aDegree rBound Cmass Ccut Couter
    hTemp hCf hCm hCcut hCouter hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim w Hsource Hcutoff hw
  refine ⟨8*Ci,8*Cm,mul_pos (by norm_num) hCi,mul_pos (by norm_num) hCm,?_⟩
  filter_upwards [H] with n hn
  intro L us hus hstar hret hmesh
  filter_upwards [hn L us hus hstar hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro i V U T hU hV hiV hVstar hstarU hpersistent hcut hT houter G forms initial x hxsx hxW hmass a z hsplit
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun j _hj=>hgrid i V U T hU hV hiV hVstar hstarU hpersistent hcut hT houter
    G forms initial x hxsx hxW hmass a z hsplit j)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end OAI.SKFluctuations.Cavity
