module

public import ComparisonActualHighWallCanonicalRestProductResampling
public import ComparisonActualHighWallRestBoundaryResampling

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_high_wall_canonical_rest_product_resampling
    (a : ℕ) (ha : 0 < a) (Bclock Cmass Rmacro F : ℝ)
    (hCm : 0 ≤ Cmass)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,1 ≤ C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=M.data.d
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a → NativeSourceFactorForm) (initial : Finset (Fin a)) (x v : ℝ),M.xs≤x → x≤W →
          0 < v → W ≤ Rmacro/2 →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e),
          (∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e)) →
          (∀e,G.j e≠j' e →
            let rh:=M.data.wallRadius M.alpha (partitionPoint 0 as (T.splitIndex (G.j e) (j' e)))
            4*W ≤ rh ∧ M.z ≤ min (rh/8) (Rmacro/4) ∧
            M.data.wallRadius M.alpha (G.sourceLowMass e) ≤ min (rh/8) (Rmacro/4) ∧
            v ≤ partitionPoint 0 as (T.splitIndex (G.j e) (j' e))) →
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>((G.canonicalHighWallSource M f).restProduct σ-
            ((G.retarget j' hne).canonicalHighWallSource M f).restProduct σ)^2) 0 ≤
          ((a:ℝ)*(1+max Bclock 0)*(2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v)/x*
            (C^a*sourceMonomialScale x W initial))^2 := by
  obtain ⟨C,hC,Hmom⟩:=eventually_actual_high_wall_canonical_rest_product_from_resampling
    (D:=D) a ha Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  have hell : a-1+1=a:=by omega
  have Hsave:=eventually_actual_high_wall_rest_all_high_resampling (D:=D)
    (a-1) Bclock Rmacro F hm hdelta hroom hgap hcl hcu hAz hC0 hCt
    hmacro hRhalf hFmass hFradius
  simp only [hell] at Hsave
  refine ⟨C,hC,?_⟩
  filter_upwards [Hmom,Hsave,eventually_gt_atTop (0:ℕ)] with n hmom hsave hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hmom M hwork L us hus hret hmesh,hsave M hwork L us hus hret hmesh] with k hk hksave
  dsimp only at hk hksave ⊢
  intro T G f initial x v hxsx hxW hv hWmacro hmass j' hne hlow hgeometry
  let as:=finiteCutMasses us k
  let W:=M.data.d
  let r:=2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v
  have hxspos := M.hxs
  have hxsW : M.xs ≤ W:=hwork.le
  have hW : 0 < W:=M.hxs.trans_le hxsW
  have hr : 0 < r:=mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos
    (by exact_mod_cast hn : (0:ℝ)<n) _))
    (savedExteriorScale_pos (by positivity) hW hv)
  have hxEq : x=M.data.d:=le_antisymm hxW (hwork ▸ hxsx)
  have Hmass : ∀e,G.sourceLowMass e≤Cmass*M.data.d:=by
    intro e
    simpa only [hxEq,sourceFactorScale,ite_self] using hmass e
  have Hscale : sourceMonomialScale x W initial=M.data.d^a:=by
    rw [hxEq,sourceMonomialScale_self]
  rw [Hscale,hxEq]
  refine (hk T G f r hr Hmass j' hne hlow ?_ ?_).trans_eq ?_
  · intro e he
    obtain ⟨hRh,_,hRl,_⟩:=hgeometry e he
    have hrh : 0 < M.data.wallRadius M.alpha (partitionPoint 0 as (T.splitIndex (G.j e) (j' e))):=
      lt_of_lt_of_le (by positivity : 0 < 4*W) hRh
    have hlower:=hRl.trans (min_le_left _ _)
    by_contra hnot
    have H:=M.data.wallRadius_monotone M.alpha (partitionPoint_mono as
        (finiteCutMasses_ordered us hus k) (show T.splitIndex (G.j e) (j' e) ≤
          T.splitIndex (G.i e) (G.j e) by omega))
    change M.data.wallRadius M.alpha (partitionPoint 0 as (T.splitIndex (G.j e) (j' e))) ≤ M.data.wallRadius M.alpha (G.sourceLowMass e) at H
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

  · dsimp only [r,W]
    ring

end OAI.SKFluctuations.Cavity
