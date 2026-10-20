module

public import ComparisonActualHighWallLowProfileMoments
public import ComparisonSignedCavityInheritedRawResourcePairBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_raw_resource_initial_pair_even_moment
    (d : ℕ) (hd : 0 < d) (Bclock Cmass : ℝ) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤M.xs→
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        ∀(U j : ℕ) (a t : ℝ),a∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→j≤as.length → partitionPoint 0 as j ≤ Cmass*M.data.d →
          (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
            (finitePhysicalCavitySquareVariance n U as b h a t)
            (fun σ=>|deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
              (joinSpin (ClockTree.pairSpin as j σ).2)-nativePhysicalResourceCenter n M.bf M.hf as j|^(2*d)) 0≤
            (C*M.data.d)^(2*d) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_canonical_square_even_moment
    (D:=D) 1 d (by norm_num) hd Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  let as:=finiteCutMasses us k
  intro U j a t ha ht hj hmass
  have Hpair:=hk U (pairClock as j) a t ha ht
    (nativeOnePairCenteredShape n as j) (fun _=>.centered) (by
      intro e
      have he : e=(0:Fin 1):=Subsingleton.elim _ _
      subst e
      rw [native_one_pair_shape_low_mass n _ j hj]
      exact hmass)
  simpa only [actual_high_wall_one_pair_centered_product M as j hj,pow_one] using Hpair

theorem eventually_actual_high_wall_raw_resource_pair_budget
    (degree : ℕ) (hd : 0 < degree) (Bclock Cmass : ℝ) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃A : ℝ,1 ≤ A ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        ∀(U i star : ℕ) (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
          P.resources.length ≤ degree → i ≤ as.length → star ≤ as.length →
        partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
        ∀l t : ℝ,l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
          P.PairMomentBudget (fullWeight n) (fullFeature n) 0
            (finitePhysicalCavitySquareVariance n U as b h l t)
            (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
            (nativePhysicalResourceCenter n M.bf M.hf as) 0 A M.data.d M.data.d 1 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_raw_resource_initial_pair_even_moment
    (D:=D) degree hd Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let A:=max 1 C
  have hA : 1 ≤ A:=le_max_left _ _
  have hCA : C ≤ A:=le_max_right _ _
  refine ⟨A,hA,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U i star T P hdegree hi hs hmi hms l t hl ht
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let q:=finitePhysicalCavitySquareVariance n U as b h l t
  let R:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)
  let center:=nativePhysicalResourceCenter n M.bf M.hf as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have HX (j : ℕ) (hj : j ≤ as.length)
      (hmass : partitionPoint 0 as j ≤ Cmass*M.data.d) (d : ℕ) (hd0 : 0 < d) (hdD : d ≤ degree) :
      (pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0 q
        (fun σ=>|R (pairSpin as j σ).1 (pairSpin as j σ).2-center j|^(2*d)) 0 ≤ (A*M.data.d)^(2*d) := by
    let V:=pairClock (S:=Spin n×Bool) as j
    let F:=fun σ : V.Assignment=>R (pairSpin as j σ).1 (pairSpin as j σ).2-center j
    have hy0 : 0 < M.data.d:=M.data.hd
    have HH:=hk U j l t hl ht hj hmass
    have HH' : V.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>|F σ|^(2*degree)) 0 ≤
        (A*M.data.d)^(2*degree) := HH.trans (pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_right hCA hy0.le) _)
    have Hlow:=V.disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 q 0 F
      (p:=(2*d:ℕ)) (r:=(2*degree:ℕ)) (by exact_mod_cast (show 0<2*d by omega))
      (by exact_mod_cast (show 2*d≤2*degree by omega))
      (mul_nonneg (zero_le_one.trans hA) hy0.le)
      (by simpa only [Real.rpow_natCast] using HH')
    simpa only [Real.rpow_natCast,V,F] using Hlow
  apply P.pairMomentBudget_of_canonical_bounds degree hdegree (fullWeight n) (fullFeature n) 0 q
    R center 0 A M.data.d M.data.d 1
  intro mark _ d hd0 hdD
  cases mark with
  | initial=>exact HX i hi hmi d hd0 hdD
  | oldStar=>exact HX star hs hms d hd0 hdD
  | markedStar j=>
    simpa only [NativeResourceMark.cut,NativeResourceMark.savedScale,one_mul] using
      (HX star hs hms d hd0 hdD)

end OAI.SKFluctuations.Cavity
