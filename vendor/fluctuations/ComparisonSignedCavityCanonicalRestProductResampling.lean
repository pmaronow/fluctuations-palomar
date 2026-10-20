module

public import ComparisonSignedCavityRestResamplingScale

@[expose] public section

noncomputable section
set_option maxHeartbeats 9000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_canonical_rest_product_from_resampling
    (a : ℕ) (ha : 0 < a) (Bclock Temp Cmass : ℝ)
    (hTemp : 0 ≤ Temp) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,1 ≤ C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a → NativeSourceFactorForm) (initial : Finset (Fin a)) (x W r : ℝ),
          M.xs ≤ x → x ≤ W → 0 < r →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e),
          (∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e)) →
          (∀e,G.j e≠j' e → T.splitIndex (G.i e) (G.j e)<T.splitIndex (G.j e) (j' e)) →
          (∀e,G.j e≠j' e → originalBoundaryResamplingMoment n a as
            (fun j=>restFiniteRealVariance n (q j)) (T.splitIndex (G.i e) (G.j e))
            (T.splitIndex (G.j e) (j' e)) ≤ r^(2*a)) →
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>((G.canonicalMinimumSource M f).restProduct σ-
            ((G.retarget j' hne).canonicalMinimumSource M f).restProduct σ)^2) 0 ≤
          ((a:ℝ)*(1+Temp)*r/x*(C^a*sourceMonomialScale x W initial))^2 := by
  obtain ⟨Cp,hCp,H⟩:=eventually_actual_minimum_canonical_rest_factor_moments
    a ha Bclock Temp Cmass hTemp hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=1+Cp
  have hC : 1 ≤ C:=by dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [H,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hn M hb hh hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro T G f initial x W r hxsx hxW hr hmass j' hne hlow hgap hres
  let as:=finiteCutMasses us k
  let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
    (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
  let GC:=G.canonicalMinimumSource M f
  let rho:=fun e=>C*sourceFactorScale x W initial e
  have hx : 0 < x:=M.hxs.trans_le hxsx
  have hW : 0 < W:=hx.trans_le hxW
  have hCb : 0 < 1+Temp:=by linarith
  have hrho : ∀e,0 < rho e:=fun e=>mul_pos (zero_lt_one.trans_le hC)
    (source_factor_scale_pos hx hW initial e)
  have hbeta : ∀e,|GC.β e| ≤ 1+Temp:=by
    intro e
    have HC:=M.bare_source_clock_bounds hcl hAz Temp hb hh
      (u:=G.sourceLowMass e) (partitionPoint_mem as (finiteCutMasses_ordered us hus k) (T.splitIndex (G.i e) (G.j e)))
    exact native_source_slope_bound (f e) HC.1 HC.2.1
  have Hraw:=hk a T G f initial x W hxsx hxW hmass
  have Hraw':=hk a T (G.retarget j' hne) f initial x W hxsx hxW (by
    intro e
    rw [G.retarget_sourceLowMass j' hne hlow]
    exact hmass e)
  rw [G.retarget_canonicalMinimumSource M f j' hne hlow] at Hraw' ⊢
  have hraw : ∀e,T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>|GC.restFactor e σ|^(2*a)) 0 ≤ (rho e)^(2*a):=by
    intro e
    apply (Hraw e).trans
    apply pow_le_pow_left₀ (mul_nonneg hCp.le (source_factor_scale_pos hx hW initial e).le)
    exact mul_le_mul_of_nonneg_right (by dsimp [C];linarith : Cp ≤ C)
      (source_factor_scale_pos hx hW initial e).le
  have hraw' : ∀e,T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>|(GC.retarget j' hne).restFactor e σ|^(2*a)) 0 ≤ (rho e)^(2*a):=by
    intro e
    apply (Hraw' e).trans
    apply pow_le_pow_left₀ (mul_nonneg hCp.le (source_factor_scale_pos hx hW initial e).le)
    exact mul_le_mul_of_nonneg_right (by dsimp [C];linarith : Cp ≤ C)
      (source_factor_scale_pos hx hW initial e).le
  have Hprod:=GC.restProduct_retarget_square hn0 ha (finiteCutMasses_ordered us hus k) q
    j' hne hlow hgap rho hrho (xi:=(1+Temp)*r/x) (by positivity) hCb hbeta hraw hraw' (by
      intro e he
      apply (hres e he).trans
      exact pow_le_pow_left₀ hr.le (rest_resampling_relative_factor hx
        (source_factor_scale_ge_initial hxW initial e) hC hCb hr.le) _)
  simpa only [rho,rest_resampling_product_scale] using Hprod

end OAI.SKFluctuations.Cavity
