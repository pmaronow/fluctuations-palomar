module

public import ComparisonSignedCavityInheritedRawResourcePairBudget
public import SKProof.Port.ComparisonActualOriginalQPhysicalSourceProfiles
public import SKProof.Port.ComparisonActualOriginalQContinuumSourceMoments

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
theorem native_one_pair_centered_product_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (j : ℕ) (hj : j≤as.length)
    (σ : (ClockTree.pairClock (S:=Spin n×Bool) as j).Assignment) :
    ((nativeOnePairCenteredShape n as j).canonicalOriginalQSource M (fun _=>.centered)).product σ=
      deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
        (joinSpin (ClockTree.pairSpin as j σ).2)-nativePhysicalResourceCenter n M.sweepBf M.sweepHf as j := by
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  rw [Fin.prod_univ_one]
  simp only [ActualNaturalBoundaryShape.canonicalOriginalQSource,NativeSourceFactorForm.intercept,
    NativeSourceFactorForm.slope]
  rw [native_one_pair_shape_low_mass n as j hj]
  simp only [nativeOnePairCenteredShape,ClockTree.pairLeft_atSlot,ClockTree.pairRight_atSlot,
    fullBoundaryAffineFactor]
  change -nativePhysicalResourceCenter n M.sweepBf M.sweepHf as j+
    1*deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
      (joinSpin (ClockTree.pairSpin as j σ).2)=_
  ring

theorem eventually_actual_minimum_inherited_raw_resource_initial_pair_even_moment_original_q
    (d : ℕ) (hd : 0 < d) (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0≤Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf→M.xs≤1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤M.xs→
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        ∀(U j : ℕ) (a t : ℝ),a∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→j≤as.length→∀x : ℝ,M.xs≤x→partitionPoint 0 as j≤Cmass*x→
          (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
            (finitePhysicalCavitySquareVariance n U as b h a t)
            (fun σ=>|deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
              (joinSpin (ClockTree.pairSpin as j σ).2)-nativePhysicalResourceCenter n M.sweepBf M.sweepHf as j|^(2*d)) 0≤
            (C*x)^(2*d) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_canonical_square_even_moment_original_q
    1 d (by norm_num) hd Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  let as:=finiteCutMasses us k
  intro U j a t ha ht hj x hxsx hmass
  have Hpair:=hk U (ClockTree.pairClock as j) a t ha ht
    (nativeOnePairCenteredShape n _ j) (fun _=>.centered) Finset.univ x x hxsx le_rfl (by
      intro e
      have he : e=(0:Fin 1):=Subsingleton.elim _ _
      subst e
      rw [native_one_pair_shape_low_mass n _ j hj]
      simpa only [sourceFactorScale,Finset.mem_univ,ite_true] using hmass)
  simp_rw [native_one_pair_centered_product_original_q M _ j hj] at Hpair
  simpa [sourceMonomialScale] using Hpair

theorem eventually_actual_minimum_inherited_raw_resource_pair_budget_original_q
    (degree : ℕ) (hd : 0 < degree) (Bclock Temp Cf Cmass : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃A : ℝ,1 ≤ A ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        ∀(U i star : ℕ) (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
          P.resources.length ≤ degree → i ≤ as.length → star ≤ as.length →
        ∀x W : ℝ,M.xs ≤ x → x ≤ W →
          partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        ∀l t : ℝ,l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
          P.PairMomentBudget (fullWeight n) (fullFeature n) 0
            (finitePhysicalCavitySquareVariance n U as b h l t)
            (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
            (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) 0 A x W 1 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_raw_resource_initial_pair_even_moment_original_q
    (D:=D) degree hd Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let A:=max 1 C
  have hA : 1 ≤ A:=le_max_left _ _
  have hCA : C ≤ A:=le_max_right _ _
  refine ⟨A,hA,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U i star T P hdegree hi hs x W hxsx hxW hmi hms l t hl ht
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let q:=finitePhysicalCavitySquareVariance n U as b h l t
  let R:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)
  let center:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have HX (j : ℕ) (hj : j ≤ as.length) (y : ℝ) (hy : M.xs ≤ y)
      (hmass : partitionPoint 0 as j ≤ Cmass*y) (d : ℕ) (hd0 : 0 < d) (hdD : d ≤ degree) :
      (pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0 q
        (fun σ=>|R (pairSpin as j σ).1 (pairSpin as j σ).2-center j|^(2*d)) 0 ≤ (A*y)^(2*d) := by
    let V:=pairClock (S:=Spin n×Bool) as j
    let F:=fun σ : V.Assignment=>R (pairSpin as j σ).1 (pairSpin as j σ).2-center j
    have hy0 : 0 < y:=M.hxs.trans_le hy
    have HH:=hk U j l t hl ht hj y hy hmass
    have HH' : V.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>|F σ|^(2*degree)) 0 ≤
        (A*y)^(2*degree) := HH.trans (pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_right hCA hy0.le) _)
    have Hlow:=V.disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 q 0 F
      (p:=(2*d:ℕ)) (r:=(2*degree:ℕ)) (by exact_mod_cast (show 0<2*d by omega))
      (by exact_mod_cast (show 2*d≤2*degree by omega))
      (mul_nonneg (zero_le_one.trans hA) hy0.le)
      (by simpa only [Real.rpow_natCast] using HH')
    simpa only [Real.rpow_natCast,V,F] using Hlow
  apply P.pairMomentBudget_of_canonical_bounds degree hdegree (fullWeight n) (fullFeature n) 0 q
    R center 0 A x W 1
  intro mark _ d hd0 hdD
  cases mark with
  | initial=>exact HX i hi x hxsx hmi d hd0 hdD
  | oldStar=>exact HX star hs W (hxsx.trans hxW) hms d hd0 hdD
  | markedStar j=>
    simpa only [NativeResourceMark.cut,NativeResourceMark.savedScale,one_mul] using
      (HX star hs W (hxsx.trans hxW) hms d hd0 hdD)

end OAI.SKFluctuations.Cavity
