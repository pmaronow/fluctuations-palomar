module

public import ComparisonSignedCavitySecondLowActualUnobservedCompleteBudgetAlong

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 30000000

def ActualSecondLowUnobservedTotalBudgetOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (aDegree rBound : ℕ) (saving Cmass Ccut Couter Cerr Cinitial Cmoving : ℝ)
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
          let di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ)
          let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+
            partitionPoint 0 as U/(dim n+1:ℕ)
          |∑j : Fin 8,nativeSecondLowClassLedger (dim n) q U b h K T hU
            (G.canonicalMinimumSource (M n) forms).restProduct a z j false/2| ≤
            Cinitial*partitionPoint 0 as U*(M n).xs*Cerr*di*p0+
            16*((dim n+1:ℕ):ℝ)^(-saving)*W n*(M n).xs^2*p0+
            Cmoving*W n*Cerr*rho*p0

theorem actual_second_low_unobserved_total_budget_along
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (aDegree rBound : ℕ) (Cmass Ccut Couter : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hCouter : 0 ≤ Couter)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ → ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cinitial Cmoving : ℝ,0<Cinitial ∧ 0<Cmoving ∧
      ActualSecondLowUnobservedTotalBudgetOnEveryFinalNetAlong aDegree rBound
        (actualMassSavingExponent m delta/32) Cmass Ccut Couter
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Cinitial Cmoving dim M W w := by
  obtain ⟨Ci,Cm,hCi,hCm,H⟩:=actual_second_low_unobserved_complete_budget_along aDegree rBound Cmass Ccut Couter
    hTemp hCf hCm hCcut hCouter hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim w Hsource hw
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
