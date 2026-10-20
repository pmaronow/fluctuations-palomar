module

public import ComparisonActualHighWallFreshResourceJointLowPrice
public import ComparisonActualHighWallOriginalLowRadius
public import ComparisonActualHighWallLowDensity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_wall_low_error_comparison_constant_le {T B : ℝ}
    (hT : 0≤T) (hTB : T≤B) :
    actualLowErrorComparisonConstant (2*T) T≤actualLowErrorComparisonConstant (2*B) B := by
  have hB : 0≤B:=hT.trans hTB
  have HE1 : Real.exp (220*(2*T))≤Real.exp (220*(2*B)):=Real.exp_le_exp.mpr (by linarith)
  have HE2 : Real.exp (110*T)+1≤Real.exp (110*B)+1:=by
    have H:=Real.exp_le_exp.mpr (show 110*T≤110*B by linarith)
    linarith only [H]
  have Hmul : 2*Real.exp (220*(2*T))*(Real.exp (110*T)+1)≤
      2*Real.exp (220*(2*B))*(Real.exp (110*B)+1):=
    mul_le_mul (mul_le_mul_of_nonneg_left HE1 (by norm_num : (0:ℝ)≤2)) HE2
      (by positivity) (by positivity)
  have HS:=Real.sqrt_le_sqrt Hmul
  exact mul_le_mul hTB HS (Real.sqrt_nonneg _) hB

theorem eventually_actual_high_wall_fresh_resource_joint_LOW_cubic_price
    (degree rBound : ℕ) (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
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
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
        partitionPoint 0 as U ≤ Ccut*M.data.d →
        |(M.data.d⁻¹)^k*actualGeneralOriginalFreshResourceJointLowRestoration M.bf M.hf U P| ≤
          |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^3) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_fresh_resource_joint_LOW_restoration_price
    (D:=D) degree rBound Bclock Cmass Ccut hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cd,hCd,HD⟩:=eventually_actual_high_wall_original_low_error_radius_bigO
    (D:=D) Bclock Cmass hCmass hm hdelta hroom hcl hcu hAz hC0 hCt
  let CB:=actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0)
  have hCB : 0≤CB:=actualLowErrorComparisonConstant_nonneg _ (le_max_right _ _)
  let C:=Cp*CB*(Cd+1)+1
  have hC : 0<C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HP,HD,eventually_actual_high_wall_site_le_square (D:=D) (Bclock:=Bclock) hm hC0]
    with n hnP hnD hnSite
  intro M hwork L us hus hret hmesh
  filter_upwards [hnP M hwork L us hus hret hmesh,hnD M hwork L us hus hret hmesh]
    with jGrid hjP hjD
  dsimp only at hjP hjD ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut
  let as:=finiteCutMasses us jGrid
  let R:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ))
  have HD:=hjD star (hs.le.trans hU) hms
  have Hsite : 1/(n+1:ℕ)≤M.data.d:=by
    have H:=hnSite M hwork
    have H' : 3*(1/((n+1:ℕ):ℝ))≤M.data.d^2:=by convert H using 1; ring
    have HN : (0:ℝ)≤1/(n+1:ℕ):=by positivity
    have Hd2 : M.data.d^2≤M.data.d:=by nlinarith only [M.data.hd.le,M.data.hd1]
    linarith only [H',HN,Hd2]
  have Hrad : R≤CB*(Cd+1)*M.data.d:=by
    have Hfactor:=actual_wall_low_error_comparison_constant_le (B:=max Bclock 0)
      (M.data.hepsilon.1.trans M.data.hepsilon.2).le (M.hT.trans (le_max_left Bclock 0))
    have Hsum : nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ)≤(Cd+1)*M.data.d:=by
      nlinarith only [HD,Hsite]
    exact (mul_le_mul Hfactor Hsum
      (add_nonneg (Real.sqrt_nonneg _) (by positivity)) hCB).trans_eq (by ring)
  have HP:=hjP i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut
  have hscale : 0≤|P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed:=
    mul_nonneg (abs_nonneg _) (actual_resource_raw_scale_pos seed M.data.hd M.data.hd).le
  apply HP.trans
  have Hprice:=mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right Hrad (sq_nonneg M.data.d)) hCp.le
  have Hconst:=mul_le_mul_of_nonneg_right (show Cp*CB*(Cd+1)≤C by dsimp only [C];linarith)
    (pow_nonneg M.data.hd.le 3)
  apply mul_le_mul_of_nonneg_left _ hscale
  calc
    Cp*R*M.data.d^2=Cp*(R*M.data.d^2):=by ring
    _≤Cp*(CB*(Cd+1)*M.data.d*M.data.d^2):=Hprice
    _=Cp*CB*(Cd+1)*M.data.d^3:=by ring
    _≤C*M.data.d^3:=Hconst

end OAI.SKFluctuations.Cavity
