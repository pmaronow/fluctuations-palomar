module

public import ComparisonActualHighWallPairedRawResampling
public import ComparisonActualHighWallTwoHighRestPayloadL2

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_canonical_paired_high_second_resampling
    (a : ℕ) (ha : 0 < a) (Bclock Cmass Rmacro F : ℝ) (hCm : 0 ≤ Cmass)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,1 ≤ C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)  →  (∀u∈uniformMasses L,u∈us)  →  ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs  →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=M.data.d
        let r:=fun v=>2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v
        let bclock:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let hclock:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>hclock j+bclock j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        ∀(U rBound : ℕ),
        let R:=M.data.highErrorEnvelope M.alpha as U
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a → NativeSourceFactorForm) (v : ℝ),
          T.leaves ≤ rBound → 0 < v → W ≤ Rmacro/2 →
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d)  →
        ∀(j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e),
          (∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e))  →
          (∀e,G.j e≠j' e  →
            let rh:=M.data.wallRadius M.alpha (partitionPoint 0 as (T.splitIndex (G.j e) (j' e)))
            4*W ≤ rh ∧ M.z ≤ min (rh/8) (Rmacro/4) ∧
            M.data.wallRadius M.alpha (G.sourceLowMass e) ≤ min (rh/8) (Rmacro/4) ∧
            v ≤ partitionPoint 0 as (T.splitIndex (G.j e) (j' e)))  →
        ∀(b s e : T.Slot),s≠e  →
          T.splitIndex b s=T.splitIndex b e  →  T.splitIndex b s < T.splitIndex s e  →
          (let rh:=M.data.wallRadius M.alpha (partitionPoint 0 as (T.splitIndex s e));
            4*W ≤ rh ∧ M.z ≤ min (rh/8) (Rmacro/4) ∧
            M.data.wallRadius M.alpha (partitionPoint 0 as (T.splitIndex b s)) ≤ min (rh/8) (Rmacro/4) ∧
            v ≤ partitionPoint 0 as (T.splitIndex s e))  →
        |nativeRestPayloadHighSecondIntegral n q U bclock hclock K T
          (fun σ=>nativeRestEndpointDifference n T b s e σ*
            ((G.canonicalHighWallSource M f).restProduct σ-
              ((G.retarget j' hne).canonicalHighWallSource M f).restProduct σ))| ≤
          actualHighWallHighSecondL2Price rBound Bclock*
            ((a:ℝ)*(r v)*((1+max Bclock 0)*(r v)/M.data.d)*
              (C^a*M.data.d^a))*
            (T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_canonical_rest_paired_resampling
    (D:=D) a ha Bclock Cmass Rmacro F hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U rBound T G f v hT hv hWmacro hmass j' hne hlow hgeometry b s e hse hblow hbgap hgeom
  have HP:=hk T G f v hv hWmacro hmass j' hne hlow hgeometry b s e hse hblow hbgap hgeom
  have HC : 0 ≤ (a:ℝ)*(2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs)
      (M.data.d) v)*
      ((1+max Bclock 0)*(2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs)
        (M.data.d) v)/M.data.d)*
      (C^a*M.data.d^a) := by
    have hx:=M.hxs
    have hW : 0 < M.data.d:=
      M.hxs.trans_le hwork.le
    have HC : 0 < C:=zero_lt_one.trans_le hC
    unfold savedExteriorScale
    positivity
  exact actual_high_wall_rest_high_second_integral_L2_bound M T
    (finiteCutMasses_ordered us hus k) U rBound hT _ HC HP

end OAI.SKFluctuations.Cavity
