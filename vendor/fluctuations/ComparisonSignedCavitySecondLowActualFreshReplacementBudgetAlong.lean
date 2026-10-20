module

public import ComparisonSignedCavitySecondLowActualFreshFullB0BudgetAlong
public import ComparisonSignedCavitySecondLowActualOccupiedOldCBaselineBudgetAlong

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 50000000
set_option backward.isDefEq.respectTransparency false

def ActualSecondLowFreshB0ReplacementBudgetOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (saving eta Cmass Ccut Couter Cerr Cinitial Cmoving Csaved Cstar : ℝ)
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val≤1) → (w n).star∈us →
      (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤(M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i V U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (hU : U≤as.length),
          0<V → i<V → V ≤ star → star<U → NativePersistentLowForks i star U T →
          partitionPoint 0 as V≤Ccut*(M n).xs → T.leaves≤rBound →
          partitionPoint 0 as U≤Couter*W n → W n≤(M n).R (partitionPoint 0 as U) →
          (M n).R (partitionPoint 0 as star)≤(M n).R (partitionPoint 0 as U)/2 →
          (M n).z≤(M n).R (partitionPoint 0 as U)/2 →
        ∀(G : ActualNaturalBoundaryShape (dim n) degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x : ℝ),(M n).xs≤x → x≤W n →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x (W n) initial e) →
        ∀s : T.Slot,
          let g:=nativeFreshAtSlot T 0 s star
          let P:=(G.canonicalMinimumSource (M n) forms).restProduct
          let Pg:=fun old=>P (g.restRestrict old)
          let χ:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let p0:=sourceMonomialScale x (W n) initial
          let di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ)
          let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+
            partitionPoint 0 as U/(dim n+1:ℕ)
          |nativeSecondLowJointLedger (dim n) q U b h K g.tree Pg [g.embed s,g.mark]/2-
            χ^2*nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s star hU P|≤
            Cinitial*partitionPoint 0 as U*(M n).xs*Cerr*di*p0+
            Cstar*((dim n+1:ℕ):ℝ)^(-saving)*W n*(M n).xs^2*p0+
            Cmoving*W n*Cerr*rho*p0+
            Csaved*((dim n+1:ℕ):ℝ)^(-eta)*W n*(M n).xs^2*p0

theorem actual_second_low_fresh_B0_modulo_c_replacement_budget_along
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter Ccal : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    (hCcal : 1≤Ccal) (heta : 0≤eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta<6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2≤Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cinitial Cmoving Csaved Cstar : ℝ,0<Cinitial ∧ 0<Cmoving ∧ 0<Csaved ∧ 0<Cstar ∧
      ActualSecondLowFreshB0ReplacementBudgetOnEveryFinalNetAlong degree rBound
        (actualMassSavingExponent m delta/32) eta Cmass Ccut Couter
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Cinitial Cmoving Csaved Cstar dim M W w := by
  obtain ⟨Ci,Cm,Cs,hCi,hCmRate,hCs,HF⟩:=actual_second_low_fresh_full_B0_budget_along degree rBound
    Cmass Ccut Couter Ccal hTemp hCf hCm hCcut hCouter hCcal heta
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim w Hsource Hcompare hw
  obtain ⟨Cb,Cstar,hCb,hCstar,HB⟩:=actual_second_low_occupied_old_c_baseline_budget_along degree rBound
    Cmass Ccut Couter hTemp hCf hCm hCcut hCouter hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hcanonical hWlim w Hsource hw
  refine ⟨Ci+Cb,Cm,Cs,16+Cstar,add_pos hCi hCb,hCmRate,hCs,by linarith,?_⟩
  filter_upwards [HF,HB] with n hnF hnB
  intro L us hus hstar hret hmesh
  filter_upwards [hnF L us hus hstar hret hmesh,hnB L us hus hstar hret hmesh] with jGrid hgridF hgridB
  dsimp only at hgridF hgridB ⊢
  intro i V U T hU hV hiV hVstar hstarU hpersistent hcut hT houter hWU hRstar hz
    G forms initial x hxsx hxW hmass s
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let g:=nativeFreshAtSlot T 0 s star
  let P:=(G.canonicalMinimumSource (M n) forms).restProduct
  let Pg:=fun old=>P (g.restRestrict old)
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have Hfull:=hgridF i V U T hU hV hiV hVstar hstarU hpersistent hcut hT houter hWU hRstar hz
    G forms initial x hxsx hxW hmass s
  have Hbase:=hgridB i V U T hU hiV hVstar hstarU hT hpersistent hcut houter
    G forms initial x hxsx hxW hmass s
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have Hchi:|chi|≤1:=native_second_low_original_chi_abs_le_one ho U K
  have Hchi2:|chi|^2≤1:=by nlinarith [abs_nonneg chi]
  have Hscaled:|chi^2*nativeSecondLowFreshOccupiedOldCBaselineSource (dim n) q U b h K T s star hU P|≤
      |nativeSecondLowFreshOccupiedOldCBaselineSource (dim n) q U b h K T s star hU P|:=by
    rw [abs_mul,abs_pow]
    exact (mul_le_mul_of_nonneg_right Hchi2 (abs_nonneg _)).trans_eq (one_mul _)
  have HS:=Hscaled.trans Hbase
  have Hjoin:=native_second_low_fresh_occupied_unweighted_eq_old_baseline_add_replacement
    (dim n) q U b h K T ho s star hstarU hU P
  have HE:nativeSecondLowJointLedger (dim n) q U b h K g.tree Pg [g.embed s,g.mark]/2-
      chi^2*nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s star hU P=
      (nativeSecondLowJointLedger (dim n) q U b h K g.tree Pg [g.embed s,g.mark]/2-
        chi^2*nativeSecondLowFreshOccupiedUnweightedCSource (dim n) q U b h K T s star hU P)+
      chi^2*nativeSecondLowFreshOccupiedOldCBaselineSource (dim n) q U b h K T s star hU P:=by
    rw [Hjoin]
    ring
  rw [HE]
  apply (abs_add_le _ _).trans
  apply (add_le_add Hfull HS).trans_eq
  ring

end OAI.SKFluctuations.Cavity
