module

public import ComparisonSignedCavityInheritedCanonicalRestProductResampling
public import ComparisonSignedCavityInheritedRestBoundaryResampling

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_rest_product_resampling
    (a : ℕ) (ha : 0 < a) (Bclock Temp Cf Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,1 ≤ C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a → NativeSourceFactorForm) (initial : Finset (Fin a)) (x v : ℝ),M.xs≤x → x≤W →
          0 < v → W ≤ Rmacro/2 →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e),
          (∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e)) →
          (∀e,G.j e≠j' e →
            let rh:=M.R (partitionPoint 0 as (T.splitIndex (G.j e) (j' e)))
            4*W ≤ rh ∧ M.z ≤ min (rh/8) (Rmacro/4) ∧
            M.R (G.sourceLowMass e) ≤ min (rh/8) (Rmacro/4) ∧
            v ≤ partitionPoint 0 as (T.splitIndex (G.j e) (j' e))) →
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>((G.canonicalMinimumSource M f).restProduct σ-
            ((G.retarget j' hne).canonicalMinimumSource M f).restProduct σ)^2) 0 ≤
          ((a:ℝ)*(1+Temp)*(2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v)/x*
            (C^a*sourceMonomialScale x W initial))^2 := by
  obtain ⟨C,hC,Hmom⟩:=eventually_actual_inherited_canonical_rest_product_from_resampling (D:=D) a ha
    Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  have hell : a-1+1=a:=by omega
  have Hsave:=eventually_actual_minimum_inherited_rest_all_high_resampling (delta:=delta)
    (Az:=Az) (Ct:=Ct) (D:=D) (a-1) Bclock Temp Cf Ccal Rmacro F hCf
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  simp only [hell] at Hsave
  refine ⟨C,hC,?_⟩
  filter_upwards [Hmom,Hsave,eventually_gt_atTop (0:ℕ)] with n hmom hsave hn
  intro M hsource hxs hcompare L us hus hret hmesh
  filter_upwards [hmom M hsource hxs L us hus hret hmesh,hsave M hsource hxs hcompare L us hus hret hmesh] with k hk hksave
  dsimp only at hk hksave ⊢
  intro T G f initial x v hxsx hxW hv hWmacro hmass j' hne hlow hgeometry
  let as:=finiteCutMasses us k
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  let r:=2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v
  have hxspos := M.hxs
  have hxsW : M.xs ≤ W:=le_max_left _ _
  have hW : 0 < W:=M.hxs.trans_le hxsW
  have hr : 0 < r:=mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos
    (by exact_mod_cast hn : (0:ℝ)<n) _))
    (savedExteriorScale_pos (by positivity) hW hv)
  apply hk T G f initial x W r hxsx hxW hr hmass j' hne hlow
  · intro e he
    obtain ⟨hRh,_,hRl,_⟩:=hgeometry e he
    have hrh : 0 < M.R (partitionPoint 0 as (T.splitIndex (G.j e) (j' e))):=
      lt_of_lt_of_le (by positivity : 0 < 4*W) hRh
    have hlower:=hRl.trans (min_le_left _ _)
    by_contra hnot
    have H:=comparisonSweepQuantile_monotone M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha (partitionPoint_mono as
        (finiteCutMasses_ordered us hus k) (show T.splitIndex (G.j e) (j' e) ≤
          T.splitIndex (G.i e) (G.j e) by omega))
    change M.R (partitionPoint 0 as (T.splitIndex (G.j e) (j' e))) ≤ M.R (G.sourceLowMass e) at H
    linarith
  · intro e he
    obtain ⟨hRh,hz,hRl,hvhi⟩:=hgeometry e he
    have H:=hksave (T.splitIndex (G.i e) (G.j e)) (T.splitIndex (G.j e) (j' e))
      (T.splitIndex_le_clockLength _ _) hWmacro hRh hz hRl
    apply H.trans
    apply pow_le_pow_left₀ (by
      apply mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      unfold savedExteriorScale
      positivity)
    exact mul_le_mul_of_nonneg_left
      (savedExteriorScale_antitone_mass (by positivity) hW hv hvhi)
      (by positivity)

end OAI.SKFluctuations.Cavity
