module

public import ComparisonSignedCavityOriginalSameFreshMomentBound

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_calibrated_original_fresh_residual
    (Bclock Temp Cmass Ccal : ℝ) (hCmass : 0≤Cmass) (hCcal : 1≤Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs≤1 →
        M.xs^2≤Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
          partitionPoint 0 as (pre.length+mid.length)≤Cmass*W →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (s e b : T.Slot) (U : ℕ),
          0 < mid.length → pre.length+mid.length < U →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T → U≤T.splitIndex s e →
          (T.splitIndex s b=pre.length ∨ T.splitIndex s b=pre.length+mid.length) →
        ∀v : ℝ,W≤v → M.R (partitionPoint 0 as (T.splitIndex s e))=v →
          M.R (partitionPoint 0 as (pre.length+mid.length))≤v/2 → M.z≤v/2 →
        ∀(Z : T.cavityLeft.Assignment→ℝ) (p : ℝ),0≤p →
          T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q (fun σ=>Z σ^2) 0≤p^2 →
          |nativeOriginalFreshResidual n T s e b 0 (pre.length+mid.length) 0 q 0 Z|≤
            p*(C*(n:ℝ)^(-eta)*savedProjectedScale M.xs W v) := by
  obtain ⟨C,hC,H⟩:=eventually_calibrated_minimum_star_subtree_projection_fourth
    Bclock Temp Cmass Ccal hCmass hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hb hh hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hb hh hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut hmass T s e b U hmid hU hT hse hsb v hWv hvr hlow hz Z p hp hZ
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>(M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
    (fun _=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
  let r:=C*(n:ℝ)^(-eta)*savedProjectedScale M.xs W v
  have hW : 0 < W:=M.hxs.trans_le (le_max_left _ _)
  have hv : 0 < v:=hW.trans_le hWv
  have hr : 0≤r:=by
    change 0≤C*(n:ℝ)^(-eta)*(M.xs^3/(W*v))
    exact mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (div_nonneg (pow_nonneg M.hxs.le _) (mul_nonneg hW.le hv.le))
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  have hfrac : ((n:ℝ)/(n+1:ℕ))≤1 := by
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast Nat.le_succ n
  have hfrac4 : ((n:ℝ)/(n+1:ℕ))^4≤1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by positivity : 0≤(n:ℝ)/(n+1:ℕ)) hfrac 4
  have hdrop : ((n:ℝ)/(n+1:ℕ))^4*r^4≤r^4 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfrac4 (pow_nonneg hr 4)
  have hJ (Dtree : ClockTree (Spin n) tail) (td de : Dtree.Slot) (hne : td≠de)
      (hsplit : pre.length+mid.length+Dtree.splitIndex td de=T.splitIndex s e) :=
    hk pre mid tail hcut hmass Dtree td de hne v hWv (by simpa only [hsplit] using hvr) hlow hz
  rcases hsb with hsb|hsb
  · apply native_original_fresh_moment_bound n pre mid tail T s e b ho 0 q 0
      (native_actual_full_fresh_anchor_with_old_moments n pre mid tail T s e b
        hmid hU hT hsb hse ho 0 q 0) Z hp hr hZ
    intro Dtree td de hne hsplit
    exact (hJ Dtree td de hne hsplit).1.trans hdrop
  · apply native_original_same_fresh_moment_bound n pre mid tail T s e b ho 0 q 0
      (native_actual_full_same_fresh_anchor_with_old_moments n pre mid tail T s e b
        hmid hU hT hsb hse ho 0 q 0) Z hp hr hZ
    intro Dtree td de hne hsplit
    exact (hJ Dtree td de hne hsplit).2.trans hdrop

end OAI.SKFluctuations.Cavity
