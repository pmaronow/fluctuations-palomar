module

public import ComparisonSignedCavitySecondLowOccupiedOldCBaselineSource
public import ComparisonSignedCavitySecondLowActualStarAtomSavingAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped BigOperators Topology NNReal ENNReal
set_option maxHeartbeats 35000000
theorem actual_second_low_star_old_c_baseline_point_budget_along
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Tstar Lwin Cs : ℝ}
    (degree rBound : ℕ) (Cmass Couter : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass) (hCouter : 0≤Couter)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (HS : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val≤1)→(w n).star∈us→
      (∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤(M n).xs→
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as),
          U≤as.length→star<U→T.leaves≤rBound→
          partitionPoint 0 as U≤Couter*W n→
        ∀(G : ActualNaturalBoundaryShape (dim n) degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x : ℝ),(M n).xs≤x→x≤W n→
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x (W n) initial e)→
        ∀(f c z : T.Slot),f≠z→
          T.splitIndex f c=star→T.splitIndex c z=star→
          let p0:=sourceMonomialScale x (W n) initial
          |T.cavityLeft.disorderExpect (restWeight (dim n)) (restFeature (dim n)) 0 q
            (nativeSecondLowUnweightedCOldPayload (dim n) U b h K T f c z
              (G.canonicalMinimumSource (M n) forms).restProduct) 0|≤
            2*((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*(M n).xs^2*p0 := by
  have Hstar:=actual_second_low_star_error_atom_saving_along degree rBound Cmass Couter 1
    hTemp hCf hCm hCouter zero_le_one hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hcanonical hWlim w HS hw
  filter_upwards [Hstar] with n hnStar
  intro L us hus hstar hret hmesh
  filter_upwards [hnStar L us hus hstar hret hmesh] with jGrid hgridStar
  dsimp only at hgridStar ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  intro U T hU hstarU hT houter G forms initial x hxsx hxW hmass f c z Hfz Hfc Hcz
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have Hfs:T.splitIndex f c<U:=Hfc ▸ hstarU
  have Hcs:T.splitIndex c z<U:=Hcz ▸ hstarU
  have Hfn:f≠c:=native_second_low_low_slots_ne T U hU f c Hfs
  have Hcn:c≠z:=native_second_low_low_slots_ne T U hU c z Hcs
  have hzero:(0:ℝ)∈Icc (0:ℝ) 1:=⟨le_rfl,zero_le_one⟩
  have hone:(1:ℝ)∈Icc (0:ℝ) 1:=⟨zero_le_one,le_rfl⟩
  have B1:=hgridStar U T 0 0 hU hstarU houter hzero hzero hT G forms initial x hxsx hxW hmass
    f c c z f z 1 Hfc Hcs Hcn Hfz hone
  have B2:=hgridStar U T 0 0 hU hstarU houter hzero hzero hT G forms initial x hxsx hxW hmass
    c z f c f z 0 Hcz Hfs Hfn Hfz hzero
  simp only [one_mul] at B1 B2
  rw [native_second_low_old_c_baseline_expect_eq_error_atoms (dim n) q U b h K T ho]
  apply (abs_add_le _ _).trans
  simpa only [nativeSecondLowOldCBaselineErrorAtom,ite_true,Bool.false_eq_true,ite_false,two_mul,add_mul]
    using add_le_add B1 B2

end OAI.SKFluctuations.Cavity
