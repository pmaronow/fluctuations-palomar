module

public import ComparisonSignedCavityActualPairedRawResampling
public import ComparisonSignedCavityWholeLawZeroLowError
public import ComparisonSignedCavityActualHighErrorProfile
public import CavityRetainedFrozenExpansion

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_retained_first_high_rest_L2_bound (n U rBound : ℕ)
    (q : ℕ → RestCoordinate n → ℝ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (hT : T.leaves ≤ rBound)
    (P : T.cavityLeft.Assignment → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hP : T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>P σ^2) 0 ≤ C^2) :
    |retainedSignedJets n q U b h K [restHighKernel n U b h K] T P []| ≤
      pairForkVariation rBound*C*nativeWholeLawProfileCost n
        (cutFullVariance n q U 0 0 b h K) (cutTSlope n U 0 b h K) T 1 := by
  let law:=cutFullVariance n q U 0 0 b h K
  let A:=cutTSlope n U 0 b h K
  let Pfull:=fun σ=>P (T.cavityAssignment σ).1
  have HP : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>Pfull σ^2) 0 ≤ C^2 := by
    rw [show (fun σ=>Pfull σ^2)=(fun σ=>(fun τ=>P τ^2) (T.cavityAssignment σ).1) from rfl,
      native_decoupled_rest_expect n q U b h K T ho (fun τ=>P τ^2)]
    exact hP
  have H:=T.disorderProfileJets_oneError_offDiagonal_wholeLaw_L2
    (fullWeight_pos n) (fullFeature n) ho 0 law 0 hT Pfull hC HP
    (ReplicaTree.coordinateProfile (fullFeature n) A)
    (fun σ=>fullFeature_coordinateProfile_self n A as.length σ)
    (nativeWholeLawErrorRadius_nonneg n as law A)
    (fun j=>le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law A j))
  have HE:=actual_site_rest_jets_eq_retained n q U b h K
    [restHighKernel n U b h K] T ho P []
  simp only [List.map_cons,List.map_nil,siteRestKernel_eq_cut_high,siteMonomial,mul_one] at HE
  rw [←HE]
  simpa only [nativeWholeLawProfileCost,Real.rpow_one,law,A,Pfull] using H

theorem actual_minimum_retained_first_high_rest_L2_bound
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (Temp : ℝ) (hTemp : 0 ≤ Temp)
    (hb : ∀u,M.b u=Temp) (hh : ∀u,M.h u=0) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U rBound : ℕ) (hT : T.leaves ≤ rBound) (P : T.cavityLeft.Assignment → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hP : T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0
      (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun _=>(M.hf (partitionPoint 0 as j):ℝ))) (fun σ=>P σ^2) 0 ≤ C^2) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
      (4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp) Temp
    |retainedSignedJets n q U b h K [restHighKernel n U b h K] T P []| ≤
      pairForkVariation rBound*C*(T.forkCost R+edgeBudget 0 as R) := by
  dsimp only
  apply (native_retained_first_high_rest_L2_bound n U rBound _ _ _ _ T ho hT P hC hP).trans
  have HE:=actual_minimum_current_high_profile_le_original M hcl hAz Temp hTemp hb hh hxs
    T ho U (l:=0) (t:=0) (by norm_num) (by norm_num) (e:=1) (by norm_num)
  simp only [Real.rpow_one] at HE
  exact mul_le_mul_of_nonneg_left HE (mul_nonneg (pairForkVariation_nonneg _) hC)

theorem paired_raw_resampling_gamma_scale {x W v B rho : ℝ}
    (hx : 0 < x) (hxW : x ≤ W) (hv : 0 < v) :
    v*(rho*savedExteriorScale (B*x) W v)^2/x*(x^2/W) ≤
      rho^2*B^6*W*x^2 := by
  have hW : 0 < W:=hx.trans_le hxW
  rw [mul_pow,savedExteriorScale_sq hW hv]
  have HE : v*(rho^2*((B*x)^6/(W^3*v)))/x*(x^2/W)=
      rho^2*B^6*x^2*(x^5/W^4) := by
    field_simp
  rw [HE]
  have Hpow : x^5 ≤ W^5:=pow_le_pow_left₀ hx.le hxW 5
  have Hscale : x^5/W^4 ≤ W := (div_le_iff₀ (pow_pos hW 4)).mpr (by nlinarith only [Hpow])
  have H:=mul_le_mul_of_nonneg_left Hscale
    (mul_nonneg (mul_nonneg (sq_nonneg rho) (by positivity : 0 ≤ B^6)) (sq_nonneg x))
  nlinarith only [H]

end OAI.SKFluctuations.Cavity
