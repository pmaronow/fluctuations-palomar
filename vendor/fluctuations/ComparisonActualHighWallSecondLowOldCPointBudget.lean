module

public import ComparisonActualHighWallSecondLowOldCAtomBudget
public import ComparisonActualHighWallOriginalLowRadius
public import ComparisonActualHighWallJointLowCubicPrice

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal ENNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_second_low_old_c_baseline_point_budget
    (degree rBound : ℕ) (Bclock Cmass Ccut : ℝ) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length →
          partitionPoint 0 as U ≤ Ccut*M.data.d → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree → NativeSourceFactorForm),
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀(f c z : T.Slot),T.splitIndex f c < U → T.splitIndex c z < U → f ≠ z →
          |T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
            (nativeSecondLowUnweightedCOldPayload n U b h K T f c z
              (G.canonicalHighWallSource M forms).restProduct) 0| ≤ C*M.data.d^2*M.data.d^degree := by
  obtain ⟨Ca,hCa,HA⟩:=eventually_actual_high_wall_second_low_old_c_error_atom_budget
    (D:=D) degree rBound Bclock Cmass Ccut hCm hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cd,hCd,HD⟩:=eventually_actual_high_wall_original_low_error_radius_bigO
    (D:=D) Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let CB:=actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0)
  have hCB : 0 ≤ CB:=actualLowErrorComparisonConstant_nonneg _ (le_max_right _ _)
  let C:=2*Ca*CB*(Cd+1)+1
  refine ⟨C,by dsimp [C];positivity,?_⟩
  filter_upwards [HA,HD,eventually_actual_high_wall_site_le_square (delta:=delta) (cl:=cl) (cu:=cu)
    (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0] with n hnA hnD hnSite
  intro M hwork L us hus hret hmesh
  filter_upwards [hnA M hwork L us hus hret hmesh,hnD M hwork L us hus hret hmesh]
    with k hkA hkD
  dsimp only at hkA hkD ⊢
  intro U T hU hcut hT G forms hmass f c z Hfc Hcz Hfz
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have hd:=M.data.hd
  have ho:=finiteCutMasses_ordered us hus k
  have Hsite : (1:ℝ)/(n+1:ℕ) ≤ M.data.d:=by
    have HH:=hnSite M hwork
    have HH' : 3*(1/((n+1:ℕ):ℝ)) ≤ M.data.d^2:=by convert HH using 1;ring
    have Hds : M.data.d^2 ≤ M.data.d:=by nlinarith only [hd.le,M.data.hd1]
    linarith only [HH',Hds,show (0:ℝ) ≤ 1/(n+1:ℕ) by positivity]
  have Hfactor : actualLowErrorComparisonConstant (2*M.data.T) M.data.T ≤ CB:=
    actual_wall_low_error_comparison_constant_le (M.data.hepsilon.1.trans M.data.hepsilon.2).le
      (M.hT.trans (le_max_left _ _))
  have Hatom (firstError : Bool) :
      |T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
        (nativeSecondLowOldCBaselineErrorAtom n U b h K T
          (G.canonicalHighWallSource M forms).restProduct f c z firstError) 0| ≤
        Ca*CB*(Cd+1)*M.data.d^2*M.data.d^degree := by
    let i:=if firstError then T.splitIndex f c else T.splitIndex c z
    have hiU : i < U:=by cases firstError <;> assumption
    have hmassi : partitionPoint 0 as i ≤ Ccut*M.data.d:=
      (partitionPoint_mono as ho hiU.le).trans hcut
    have Hi:=hkD i (hiU.le.trans hU) hmassi
    have Herr : actualLowErrorComparisonConstant (2*M.data.T) M.data.T*
        (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)) ≤ CB*(Cd+1)*M.data.d := by
      have Hlow : nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ) ≤ (Cd+1)*M.data.d:=by
        linarith only [Hi,Hsite]
      have HH:=mul_le_mul Hfactor Hlow
        (add_nonneg (Real.sqrt_nonneg _) (by positivity)) hCB
      convert HH using 1;ring
    have HH:=hkA U T hU hcut hT G forms hmass f c z Hfc Hcz Hfz firstError
    have Hmul:=mul_le_mul_of_nonneg_left Herr (show 0 ≤ Ca*M.data.d*M.data.d^degree by positivity)
    apply HH.trans
    convert Hmul using 1 <;> ring
  rw [native_second_low_old_c_baseline_expect_eq_error_atoms n q U b h K T ho]
  apply (abs_add_le _ _).trans
  apply (add_le_add (Hatom true) (Hatom false)).trans
  have Hcoef : 2*Ca*CB*(Cd+1) ≤ C:=by dsimp [C];linarith
  have HH:=mul_le_mul_of_nonneg_right Hcoef (show 0 ≤ M.data.d^2*M.data.d^degree by positivity)
  convert HH using 1 <;> ring

end OAI.SKFluctuations.Cavity
