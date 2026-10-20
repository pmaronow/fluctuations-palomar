module

public import ComparisonSignedCavitySecondLowOccupiedOldCBaselineSource
public import ComparisonSignedCavitySecondLowInheritedRawAtomBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal ENNReal
set_option maxHeartbeats 30000000

theorem eventually_actual_minimum_inherited_second_low_old_c_error_atom_budget
    (degree rBound : ℕ) (Bclock Temp Cf Cmass : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U≤as.length → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x W : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀(f c z : T.Slot),T.splitIndex f c<U → T.splitIndex c z<U → f≠z → ∀firstError : Bool,
          let errorCut:=if firstError then T.splitIndex f c else T.splitIndex c z
          let otherCut:=if firstError then T.splitIndex c z else T.splitIndex f c
          let d:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as errorCut+1/(n+1:ℕ))
          |T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
            (nativeSecondLowOldCBaselineErrorAtom n U b h K T
              (G.canonicalMinimumSource M forms).restProduct f c z firstError) 0|≤
            C*d*(M.xs+partitionPoint 0 as otherCut)*sourceMonomialScale x W initial := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_second_low_actual_raw_atom_budget
    (D:=D) degree rBound Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M HS hxs L us hus hret hmesh
  filter_upwards [hn M HS hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT G forms initial x W hxsx hxW hmass f c z Hfc Hcz Hfz firstError
  have Hfn:f≠c:=native_second_low_low_slots_ne T U hU f c Hfc
  have Hcn:c≠z:=native_second_low_low_slots_ne T U hU c z Hcz
  have hzero:(0:ℝ)∈Icc (0:ℝ) 1:=⟨le_rfl,zero_le_one⟩
  have hone:(1:ℝ)∈Icc (0:ℝ) 1:=⟨zero_le_one,le_rfl⟩
  cases firstError
  · exact hgrid U T 0 0 hU hzero hzero hT G forms initial x W hxsx hxW hmass c z Hcz
      f c f z 0 Hfc Hfn Hfz hzero
  · exact hgrid U T 0 0 hU hzero hzero hT G forms initial x W hxsx hxW hmass f c Hfc
      c z f z 1 Hcz Hcn Hfz hone

end OAI.SKFluctuations.Cavity
