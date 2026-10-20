module

public import ComparisonActualHighWallRestFactorMoments
public import ComparisonActualGeneralRetargetSource
public import ComparisonActualHighWallRestBoundaryResampling
public import ComparisonSignedCavityRestResamplingScale

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_canonical_rest_product_from_resampling
    (a : ℕ) (ha : 0  <  a) (Bclock Cmass : ℝ) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0  ≤  Az) (hC0 : 0  <  C0) (hCt : 0  ≤  Ct) :
    ∃C : ℝ,1  ≤  C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val  ≤  1)  →  (∀u∈uniformMasses L,u∈us)  →  ((L+1:ℕ):ℝ)⁻¹  ≤  M.xs  →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ  →  RestCoordinate n  →  ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a  →  NativeSourceFactorForm) (r : ℝ),0 < r →
          (∀e,G.sourceLowMass e  ≤  Cmass*M.data.d)  →
        ∀(j' : Fin a  →  T.Slot) (hne : ∀e,G.i e≠j' e),
          (∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e))  →
          (∀e,G.j e≠j' e  →  T.splitIndex (G.i e) (G.j e) < T.splitIndex (G.j e) (j' e))  →
          (∀e,G.j e≠j' e  →  originalBoundaryResamplingMoment n a as
            (fun j=>restFiniteRealVariance n (q j)) (T.splitIndex (G.i e) (G.j e))
            (T.splitIndex (G.j e) (j' e))  ≤  r^(2*a))  →
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>((G.canonicalHighWallSource M f).restProduct σ-
              ((G.retarget j' hne).canonicalHighWallSource M f).restProduct σ)^2) 0  ≤
          ((a:ℝ)*((1+max Bclock 0)*r/M.data.d)*(C^a*M.data.d^a))^2 := by
  obtain ⟨Cp,hCp,H⟩:=eventually_actual_high_wall_canonical_rest_factor_moments
    a ha Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=1+Cp
  have hC : 1  ≤  C:=by dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [H,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro T G f r hr hmass j' hne hlow hgap hres
  let as:=finiteCutMasses us k
  let q : ℕ  →  RestCoordinate n  →  ℝ:=fun j=>Sum.elim
    (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
  let GC:=G.canonicalHighWallSource M f
  let rho:=fun _ : Fin a=>C*M.data.d
  have hx:=M.data.hd
  have hW:=M.data.hd
  have hCb : 0 < 1+max Bclock 0:=by have HH:=le_max_right Bclock (0:ℝ);linarith
  have hrho : ∀e,0  <  rho e:=fun e=>mul_pos (zero_lt_one.trans_le hC)
    M.data.hd
  have hbeta : ∀e,|GC.β e|  ≤  1+max Bclock 0:=by
    intro e
    have hu: G.sourceLowMass e∈Icc (0:ℝ) 1:=partitionPoint_mem as
      (finiteCutMasses_ordered us hus k) (T.splitIndex (G.i e) (G.j e))
    have HT:=M.data.total_clock_le M.alpha _ hu
    have HP:=(M.hf (G.sourceLowMass e)).coe_nonneg
    have HC : (M.bf (G.sourceLowMass e):ℝ) ≤ max Bclock 0:=by
      have HB:=M.hT.trans (le_max_left Bclock 0)
      linarith
    exact native_source_slope_bound (f e) (NNReal.coe_nonneg _) HC
  have Hraw:=hk a T G f hmass
  have Hraw':=hk a T (G.retarget j' hne) f (by
    intro e
    rw [G.retarget_sourceLowMass j' hne hlow]
    exact hmass e)
  have Hret:=G.retarget_canonicalPhysicalSource M.bf M.hf f j' hne hlow
  change (G.retarget j' hne).canonicalHighWallSource M f=
    (G.canonicalHighWallSource M f).retarget j' hne at Hret
  rw [Hret] at Hraw' ⊢
  have hraw : ∀e,T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>|GC.restFactor e σ|^(2*a)) 0  ≤  (rho e)^(2*a):=by
    intro e
    apply (Hraw e).trans
    apply pow_le_pow_left₀ (mul_nonneg hCp.le M.data.hd.le)
    exact mul_le_mul_of_nonneg_right (by dsimp [C];linarith : Cp  ≤  C)
      M.data.hd.le
  have hraw' : ∀e,T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>|(GC.retarget j' hne).restFactor e σ|^(2*a)) 0  ≤  (rho e)^(2*a):=by
    intro e
    apply (Hraw' e).trans
    apply pow_le_pow_left₀ (mul_nonneg hCp.le M.data.hd.le)
    exact mul_le_mul_of_nonneg_right (by dsimp [C];linarith : Cp  ≤  C)
      M.data.hd.le
  have Hprod:=GC.restProduct_retarget_square hn0 ha (finiteCutMasses_ordered us hus k) q
    j' hne hlow hgap rho hrho (xi:=(1+max Bclock 0)*r/M.data.d) (by positivity) hCb hbeta hraw hraw' (by
      intro e he
      apply (hres e he).trans
      exact pow_le_pow_left₀ hr.le (rest_resampling_relative_factor hx
        le_rfl hC hCb hr.le) _)
  simpa only [rho,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow] using Hprod

end OAI.SKFluctuations.Cavity
