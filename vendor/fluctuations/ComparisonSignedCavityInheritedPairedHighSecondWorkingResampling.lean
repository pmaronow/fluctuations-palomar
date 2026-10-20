module

public import ComparisonSignedCavityInheritedPairedRawResampling
public import ComparisonSignedCavityInheritedPairedNearHigh
public import ComparisonSignedCavityInheritedTwoHighRestPayloadL2

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_rest_paired_resampling_working_scale
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
        ∀(x : ℝ), M.xs ≤ x → x ≤ W →
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a → NativeSourceFactorForm) (initial : Finset (Fin a)) (v : ℝ),
          0 < v  →  W ≤ Rmacro/2  →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e)  →
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
          ((a:ℝ)*(r v)*((1+Temp)*(r v)/x)*
            (C^a*sourceMonomialScale x W initial))^2 := by
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
  intro x hxsx hxW T G f initial v hv hWmacro hmass j' hne hlow hgeometry b s e hse hblow hbgap hgeom
  let as:=finiteCutMasses us k
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  let r:=2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v
  have hxsW : M.xs ≤ W:=le_max_left _ _
  have hW : 0 < W:=M.hxs.trans_le hxsW
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
  apply hk T G f initial x W r hxsx hxW hr hmass j' hne hlow
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

theorem eventually_actual_minimum_inherited_canonical_paired_high_second_resampling_working_scale
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
        let bclock:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let hclock:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>hclock j+bclock j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        ∀(U rBound : ℕ),
        ∀(x : ℝ), M.xs ≤ x → x ≤ W →
        let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
          (4*Cf+2*Temp) Temp
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a → NativeSourceFactorForm) (initial : Finset (Fin a)) (v : ℝ),
          T.leaves ≤ rBound → 0 < v → W ≤ Rmacro/2 →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e)  →
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
        |nativeRestPayloadHighSecondIntegral n q U bclock hclock K T
          (fun σ=>nativeRestEndpointDifference n T b s e σ*
            ((G.canonicalMinimumSource M f).restProduct σ-
              ((G.retarget j' hne).canonicalMinimumSource M f).restProduct σ))| ≤
          nativeInheritedHighSecondL2Price rBound Temp Cf*
            ((a:ℝ)*(r v)*((1+Temp)*(r v)/x)*
              (C^a*sourceMonomialScale x W initial))*
            (T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_canonical_rest_paired_resampling_working_scale
    (D:=D) a ha Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hsource hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hsource hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U rBound x hxsx hxW T G f initial v hT hv hWmacro hmass j' hne hlow hgeometry b s e hse hblow hbgap hgeom
  have HP:=hk x hxsx hxW T G f initial v hv hWmacro hmass j' hne hlow hgeometry b s e hse hblow hbgap hgeom
  have HC : 0 ≤ (a:ℝ)*(2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs)
      (max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))) v)*
      ((1+Temp)*(2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs)
        (max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))) v)/x)*
      (C^a*sourceMonomialScale x
        (max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))) initial) := by
    have hx:=M.hxs.trans_le hxsx
    have hxspos:=M.hxs
    have hW : 0 < max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs)):=
      M.hxs.trans_le (le_max_left _ _)
    have HC : 0 < C:=zero_lt_one.trans_le hC
    unfold savedExteriorScale sourceMonomialScale
    positivity
  exact actual_minimum_inherited_rest_high_second_integral_L2_bound M Temp Cf hTemp hCf hsource hxs T
    (finiteCutMasses_ordered us hus k) U rBound hT _ HC HP

theorem eventually_actual_minimum_inherited_canonical_paired_near_high_working_scale
    (a : ℕ) (ha : 0 < a) (Bclock Temp Cf Cmass : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cs Cp : ℝ,0 < Cs ∧ 0 < Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a → NativeSourceFactorForm) (initial : Finset (Fin a)) (x W : ℝ),
          M.xs ≤ x → x ≤ W → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e),
          (∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e)) →
        ∀(G₀ : ActualNaturalBoundaryShape n 1 T) (j₀' : Fin 1 → T.Slot)
          (hne₀ : ∀e,G₀.i e≠j₀' e),
          (∀e,T.splitIndex (G₀.i e) (G₀.j e)=T.splitIndex (G₀.i e) (j₀' e)) →
          G₀.sourceLowMass 0 ≤ Cmass*W →
        let H:=G₀.canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)
        let H':=(G₀.retarget j₀' hne₀).canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)
        let P:=G.canonicalMinimumSource M f
        let P':=(G.retarget j' hne).canonicalMinimumSource M f
        let paired:=fun σ=>(H.restProduct σ-H'.restProduct σ)*(P.restProduct σ-P'.restProduct σ)
        let Cpair:=4*Cs*W*(Cp^a*sourceMonomialScale x W initial)
        (T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>paired σ^2) 0 ≤ Cpair^2) ∧
        ∀(U rBound : ℕ),T.leaves ≤ rBound →
          let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
            (4*Cf+2*Temp) Temp
          |retainedSignedJets n q U b h K [restHighKernel n U b h K] T paired []| ≤
            pairForkVariation rBound*Cpair*(T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_rest_even_moment
    (D:=D) a 2 ha (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCm
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_minimum_inherited_canonical_rest_even_moment
    (D:=D) 1 2 (by norm_num) (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCm
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cs,Cp,hCs,hCp,?_⟩
  filter_upwards [HP,HS] with n hnP hnS
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hsource hxs L us hus hret hmesh,
    hnS M hsource hxs L us hus hret hmesh] with k hkP hkS
  dsimp only at hkP hkS ⊢
  intro T G f initial x W hxsx hxW hmass j' hne hlow G₀ j₀' hne₀ hlow₀ hmass₀
  have hx : 0 < x:=M.hxs.trans_le hxsx
  have hxsW : M.xs ≤ W:=hxsx.trans hxW
  have hW : 0 < W:=hx.trans_le hxW
  have hxspos:=M.hxs
  have hscale : 0 < Cp^a*sourceMonomialScale x W initial := by
    unfold sourceMonomialScale
    positivity
  have HP:=hkP T G f initial x W hxsx hxW hmass
  have HQ:=hkP T (G.retarget j' hne) f initial x W hxsx hxW (by
    intro e
    rw [G.retarget_sourceLowMass j' hne hlow]
    exact hmass e)
  have HS:=hkS T G₀ (fun _=>NativeSourceFactorForm.centered) ∅ W W hxsW le_rfl (by
    intro e
    have he : e=0:=Subsingleton.elim _ _
    simpa only [he,sourceFactorScale,Finset.notMem_empty,ite_false] using hmass₀)
  have HS':=hkS T (G₀.retarget j₀' hne₀) (fun _=>NativeSourceFactorForm.centered) ∅ W W hxsW le_rfl (by
    intro e
    rw [G₀.retarget_sourceLowMass j₀' hne₀ hlow₀]
    have he : e=0:=Subsingleton.elim _ _
    simpa only [he,sourceFactorScale,Finset.notMem_empty,ite_false] using hmass₀)
  simp only [sourceMonomialScale,Finset.card_empty,pow_zero,one_mul,Nat.sub_zero,pow_one] at HS HS'
  have H:=native_rest_two_differences_square n T (finiteCutMasses_ordered us hus k) _ _ _ _ _
    (mul_pos hCs hW) hscale HS HS' HP HQ
  have HE : 4*(Cs*W)*(Cp^a*sourceMonomialScale x W initial)=
      4*Cs*W*(Cp^a*sourceMonomialScale x W initial):=by ring
  rw [HE] at H
  refine ⟨H,?_⟩
  intro U rBound hT
  exact actual_minimum_inherited_retained_first_high_rest_L2_bound M Temp Cf hTemp hCf hsource hxs
    T (finiteCutMasses_ordered us hus k) U rBound hT _ (by positivity) H

end OAI.SKFluctuations.Cavity
