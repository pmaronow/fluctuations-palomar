module

public import ComparisonSignedCavityActualPairedRawResampling
public import ComparisonSignedCavityInheritedCanonicalRestFactorMoments
public import ComparisonSignedCavityInheritedRestBoundaryResampling

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_inherited_canonical_rest_paired_product_from_resampling
    (a : ℕ) (ha : 0  <  a) (Bclock Temp Cf Cmass : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0  ≤  Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0  ≤  Az) (hC0 : 0  <  C0) (hCt : 0  ≤  Ct) :
    ∃C : ℝ,1  ≤  C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf  →  M.xs  ≤  1  →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val  ≤  1)  →  (∀u∈uniformMasses L,u∈us)  →  ((L+1:ℕ):ℝ)⁻¹  ≤  M.xs  →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ  →  RestCoordinate n  →  ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a  →  NativeSourceFactorForm) (initial : Finset (Fin a)) (x W r : ℝ),
          M.xs  ≤  x  →  x  ≤  W  →  0  <  r  →
          (∀e,G.sourceLowMass e  ≤  Cmass*sourceFactorScale x W initial e)  →
        ∀(j' : Fin a  →  T.Slot) (hne : ∀e,G.i e≠j' e),
          (∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e))  →
          (∀e,G.j e≠j' e  →  T.splitIndex (G.i e) (G.j e) < T.splitIndex (G.j e) (j' e))  →
          (∀e,G.j e≠j' e  →  originalBoundaryResamplingMoment n (a+1) as
            (fun j=>restFiniteRealVariance n (q j)) (T.splitIndex (G.i e) (G.j e))
            (T.splitIndex (G.j e) (j' e))  ≤  r^(2*(a+1)))  →
        ∀(b s e : T.Slot),s≠e  →
          T.splitIndex b s=T.splitIndex b e  →  T.splitIndex b s < T.splitIndex s e  →
          originalBoundaryResamplingMoment n (a+1) as
            (fun j=>restFiniteRealVariance n (q j)) (T.splitIndex b s)
            (T.splitIndex s e) ≤ r^(2*(a+1))  →
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>(nativeRestEndpointDifference n T b s e σ*
            ((G.canonicalMinimumSource M f).restProduct σ-
              ((G.retarget j' hne).canonicalMinimumSource M f).restProduct σ))^2) 0  ≤
          ((a:ℝ)*r*((1+Temp)*r/x)*(C^a*sourceMonomialScale x W initial))^2 := by
  obtain ⟨Cp,hCp,H⟩:=eventually_actual_minimum_inherited_canonical_rest_factor_moments
    (a+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=1+Cp
  have hC : 1  ≤  C:=by dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [H,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro T G f initial x W r hxsx hxW hr hmass j' hne hlow hgap hres b s e hse hblow hbgap hend
  let as:=finiteCutMasses us k
  let q : ℕ  →  RestCoordinate n  →  ℝ:=fun j=>Sum.elim
    (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
  let GC:=G.canonicalMinimumSource M f
  let rho:=fun e=>C*sourceFactorScale x W initial e
  have hx : 0  <  x:=M.hxs.trans_le hxsx
  have hW : 0  <  W:=hx.trans_le hxW
  have hCb : 0  <  1+Temp:=by linarith
  have hrho : ∀e,0  <  rho e:=fun e=>mul_pos (zero_lt_one.trans_le hC)
    (source_factor_scale_pos hx hW initial e)
  have hbeta : ∀e,|GC.β e|  ≤  1+Temp:=by
    intro e
    have HC:=hsource (G.sourceLowMass e) (partitionPoint_mem as (finiteCutMasses_ordered us hus k) (T.splitIndex (G.i e) (G.j e)))
    exact native_source_slope_bound (f e) (NNReal.coe_nonneg _) HC.1
  have Hraw:=hk a T G f initial x W hxsx hxW hmass
  have Hraw':=hk a T (G.retarget j' hne) f initial x W hxsx hxW (by
    intro e
    rw [G.retarget_sourceLowMass j' hne hlow]
    exact hmass e)
  rw [G.retarget_canonicalMinimumSource M f j' hne hlow] at Hraw' ⊢
  have hraw : ∀e,T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>|GC.restFactor e σ|^(2*(a+1))) 0  ≤  (rho e)^(2*(a+1)):=by
    intro e
    apply (Hraw e).trans
    apply pow_le_pow_left₀ (mul_nonneg hCp.le (source_factor_scale_pos hx hW initial e).le)
    exact mul_le_mul_of_nonneg_right (by dsimp [C];linarith : Cp  ≤  C)
      (source_factor_scale_pos hx hW initial e).le
  have hraw' : ∀e,T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>|(GC.retarget j' hne).restFactor e σ|^(2*(a+1))) 0  ≤  (rho e)^(2*(a+1)):=by
    intro e
    apply (Hraw' e).trans
    apply pow_le_pow_left₀ (mul_nonneg hCp.le (source_factor_scale_pos hx hW initial e).le)
    exact mul_le_mul_of_nonneg_right (by dsimp [C];linarith : Cp  ≤  C)
      (source_factor_scale_pos hx hW initial e).le
  have Hprod:=GC.restProduct_paired_retarget_square hn0 ha (finiteCutMasses_ordered us hus k) q
    j' hne hlow hgap b s e hse hblow hbgap rho hrho (xi:=(1+Temp)*r/x) (by positivity) hCb hr hbeta hraw hraw' (by
      intro e he
      apply (hres e he).trans
      exact pow_le_pow_left₀ hr.le (rest_resampling_relative_factor hx
        (source_factor_scale_ge_initial hxW initial e) hC hCb hr.le) _) hend
  simpa only [rho,Finset.prod_mul_distrib,source_factor_scale_product,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin] using Hprod

theorem eventually_actual_minimum_inherited_canonical_rest_paired_resampling
    (a : ℕ) (ha : 0 < a) (Bclock Temp Cf Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,1 ≤ C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf  →  M.xs ≤ 1  →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs  →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)  →  (∀u∈uniformMasses L,u∈us)  →  ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs  →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        let r:=fun v=>2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a → NativeSourceFactorForm) (initial : Finset (Fin a)) (v : ℝ),
          0 < v  →  W ≤ Rmacro/2  →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e)  →
        ∀(j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e),
          (∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e))  →
          (∀e,G.j e≠j' e  →
            let rh:=M.R (partitionPoint 0 as (T.splitIndex (G.j e) (j' e)))
            4*W ≤ rh ∧ M.z ≤ min (rh/8) (Rmacro/4) ∧
            M.R (G.sourceLowMass e) ≤ min (rh/8) (Rmacro/4) ∧
            v ≤ partitionPoint 0 as (T.splitIndex (G.j e) (j' e)))  →
        ∀(b s e : T.Slot),s≠e  →
          T.splitIndex b s=T.splitIndex b e  →  T.splitIndex b s < T.splitIndex s e  →
          (let rh:=M.R (partitionPoint 0 as (T.splitIndex s e));
            4*W ≤ rh ∧ M.z ≤ min (rh/8) (Rmacro/4) ∧
            M.R (partitionPoint 0 as (T.splitIndex b s)) ≤ min (rh/8) (Rmacro/4) ∧
            v ≤ partitionPoint 0 as (T.splitIndex s e))  →
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>(nativeRestEndpointDifference n T b s e σ*
            ((G.canonicalMinimumSource M f).restProduct σ-
              ((G.retarget j' hne).canonicalMinimumSource M f).restProduct σ))^2) 0 ≤
          ((a:ℝ)*(r v)*((1+Temp)*(r v)/M.xs)*
            (C^a*sourceMonomialScale M.xs W initial))^2 := by
  obtain ⟨C,hC,Hmom⟩:=eventually_actual_inherited_canonical_rest_paired_product_from_resampling
    (D:=D) a ha Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hsave:=eventually_actual_minimum_inherited_rest_all_high_resampling (D:=D) a
    Bclock Temp Cf Ccal Rmacro F hCf hm hdelta hroom hgap hcl hcu hAz hC0 hCt
    hCcal hmacro hRhalf hFmass hFradius
  refine ⟨C,hC,?_⟩
  filter_upwards [Hmom,Hsave,eventually_gt_atTop (0:ℕ)] with n hmom hsave hn
  intro M hsource hxs hcompare L us hus hret hmesh
  filter_upwards [hmom M hsource hxs L us hus hret hmesh,
    hsave M hsource hxs hcompare L us hus hret hmesh] with k hk hksave
  dsimp only at hk hksave ⊢
  intro T G f initial v hv hWmacro hmass j' hne hlow hgeometry b s e hse hblow hbgap hgeom
  let as:=finiteCutMasses us k
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  let r:=2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v
  have hxW : M.xs ≤ W:=le_max_left _ _
  have hW : 0 < W:=M.hxs.trans_le hxW
  have hxspos:=M.hxs
  have hr : 0 < r:=mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos
    (by exact_mod_cast hn : (0:ℝ) < n) _))
    (savedExteriorScale_pos (by positivity) hW hv)
  have Hsaved (lo hi : ℕ) (hhi : hi ≤ as.length)
      (HG : 4*W ≤ M.R (partitionPoint 0 as hi) ∧
        M.z ≤ min (M.R (partitionPoint 0 as hi)/8) (Rmacro/4) ∧
        M.R (partitionPoint 0 as lo) ≤ min (M.R (partitionPoint 0 as hi)/8) (Rmacro/4) ∧
        v ≤ partitionPoint 0 as hi) :
      originalBoundaryResamplingMoment n (a+1) as
        (fun j=>restFiniteRealVariance n (Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ))
          (fun _=>(M.hf (partitionPoint 0 as j):ℝ)))) lo hi ≤ r^(2*(a+1)) := by
    obtain ⟨hRh,hz,hRl,hvhi⟩:=HG
    have H:=hksave lo hi hhi hWmacro hRh hz hRl
    apply H.trans
    apply pow_le_pow_left₀ (by
      apply mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      unfold savedExteriorScale
      positivity)
    exact mul_le_mul_of_nonneg_left
      (savedExteriorScale_antitone_mass (by positivity) hW hv hvhi) (by positivity)
  apply hk T G f initial M.xs W r le_rfl hxW hr hmass j' hne hlow
  · intro j hj
    obtain ⟨hRh,_,hRl,_⟩:=hgeometry j hj
    have hrh : 0 < M.R (partitionPoint 0 as (T.splitIndex (G.j j) (j' j))):=
      lt_of_lt_of_le (by positivity : 0 < 4*W) hRh
    have hlower:=hRl.trans (min_le_left _ _)
    by_contra hnot
    have H:=comparisonSweepQuantile_monotone M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha (partitionPoint_mono as
        (finiteCutMasses_ordered us hus k) (show T.splitIndex (G.j j) (j' j) ≤
          T.splitIndex (G.i j) (G.j j) by omega))
    change M.R (partitionPoint 0 as (T.splitIndex (G.j j) (j' j))) ≤ M.R (G.sourceLowMass j) at H
    linarith
  · intro j hj
    exact Hsaved _ _ (T.splitIndex_le_clockLength _ _) (hgeometry j hj)
  · exact hse
  · exact hblow
  · exact hbgap
  · exact Hsaved _ _ (T.splitIndex_le_clockLength _ _) hgeom

end OAI.SKFluctuations.Cavity
