module

public import ComparisonSignedCavityActualMixedStarProjectionPowers
public import ComparisonSignedCavityActualInheritedRestStarAlong

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum
set_option maxHeartbeats 12000000

def ActualOriginalStarProjectionPowerOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (p : ℕ) (saving : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → (w n).star∈us →
    ∀ᶠk : ℕ in atTop,
      let as:=finiteCutMasses us k
      let q : ℕ → RestCoordinate (dim n) → ℝ:=fun j=>Sum.elim
        (fun _=>((M n).bf (partitionPoint 0 as j):ℝ))
        (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
      let center:=orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      ∀(T : ClockTree (Spin (dim n)) tail) (s : T.Slot),
        let qs:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j))
        (∫z,T.expect (restWeight (dim n)) (restFeature (dim n)) qs
          (fun σ=>|nativeStarCenteredProjection (dim n) tail qs center (exteriorForestStarRoot z) (T.atSlot σ s)|^(2*(p+1)))
          (exteriorForestStarRoot z)
          ∂nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0) ≤
          (((dim n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1))

theorem actual_rest_star_to_projection_powers_along
    {m delta cl cu Az C0 Ct D Bclock saving : ℝ}
    (p : ℕ) {dim : ℕ→ℕ} (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (H : ActualOriginalRestStarMomentOnEveryFinalNetAlong p saving M W w) :
    ActualOriginalStarProjectionPowerOnEveryFinalNetAlong p saving M W w := by
  filter_upwards [H] with n hn
  intro us hus hstar
  filter_upwards [hn us hus hstar] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut hindex T s
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  apply (native_common_star_projection_power_le_original_pair (dim n) (2*(p+1)) pre mid tail ho T s
    0 _ (orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val) 0).trans
  have HK (bs : List PositiveMass) (hbs : bs=finiteCutMasses us k) (j : ℕ)
      (hj : j=retainedMassPrefixIndex (w n).star.val (finiteCutMasses us k)) :
      (ClockTree.pairClock bs j).disorderExpect (restWeight (dim n)) (restFeature (dim n)) 0
        (fun j=>Sum.elim (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
          (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)))
        (fun σ=>|deletedOverlap (dim n) (joinSpin ((ClockTree.pairSpin bs j σ).1,false))
          (joinSpin ((ClockTree.pairSpin bs j σ).2,false))-
            orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val|^(2*(p+1))) 0 ≤
        (((dim n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1)) := by
    subst bs j
    exact hk
  exact HK _ hcut _ hindex

def ActualMixedStarProjectionPowersOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (j k : ℕ) (saving : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → (w n).star∈us →
    ∀ᶠr : ℕ in atTop,
      let as:=finiteCutMasses us r
      let q : ℕ → RestCoordinate (dim n) → ℝ:=fun l=>Sum.elim
        (fun _=>((M n).bf (partitionPoint 0 as l):ℝ))
        (fun _=>((M n).hf (partitionPoint 0 as l):ℝ))
      let center:=orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      ∀(T : ClockTree (Spin (dim n)) tail) (s t : T.Slot),
        let qs:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+(mid.length+l))
        nativeRootTestExpect (dim n) T qs
          (nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0)
          exteriorForestStarRoot
          (fun z σ=>(nativeStarCenteredProjection (dim n) tail qs center (exteriorForestStarRoot z) (T.atSlot σ s)^j*
            nativeStarCenteredProjection (dim n) tail qs center (exteriorForestStarRoot z) (T.atSlot σ t)^k)^2) ≤
          (((dim n+1:ℕ):ℝ)^(-saving)*W n)^(2*(j+k))

theorem actual_star_projection_powers_to_mixed_along
    {m delta cl cu Az C0 Ct D Bclock saving : ℝ}
    (j k : ℕ) {dim : ℕ→ℕ} (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW : ∀n,0 ≤ W n) (w : ℕ→ActualSlowWindowChoice)
    (H : ∀p : ℕ,ActualOriginalStarProjectionPowerOnEveryFinalNetAlong p saving M W w) :
    ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w := by
  filter_upwards [H (2*j-1),H (2*k-1)] with n hnJ hnK
  intro us hus hstar
  filter_upwards [hnJ us hus hstar,hnK us hus hstar] with r hrJ hrK
  dsimp only at hrJ hrK ⊢
  intro pre mid tail hcut hindex T s t
  let q : ℕ → RestCoordinate (dim n) → ℝ:=fun l=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) l):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) l):ℝ))
  let qs:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+(mid.length+l))
  let center:=orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val
  let μ:=nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let := nativeExteriorForestDisorderRootLaw_probability (restWeight_pos (dim n)) (restFeature (dim n))
    pre mid tail ho 0 q 0
  apply native_star_projection_mixed_power_second_le (dim n) j k T ho.suffix_end.suffix_end qs μ
    exteriorForestStarRoot departedAnchorExteriorRoot_measurable center s t
    (((dim n+1:ℕ):ℝ)^(-saving)*W n) (mul_nonneg (Real.rpow_nonneg (by positivity) _) (hW n))
  · by_cases hj : j=0
    · subst j
      simp only [mul_zero,pow_zero,nativeRootTestExpect]
      simp only [T.expect_const (restWeight_pos (dim n)) (restFeature (dim n)) ho.suffix_end.suffix_end]
      simp
    · have he : 2*(2*j-1+1)=4*j := by omega
      simpa only [he,nativeRootTestExpect,qs,μ,q,center] using hrJ pre mid tail hcut hindex T s
  · by_cases hk : k=0
    · subst k
      simp only [mul_zero,pow_zero,nativeRootTestExpect]
      simp only [T.expect_const (restWeight_pos (dim n)) (restFeature (dim n)) ho.suffix_end.suffix_end]
      simp
    · have he : 2*(2*k-1+1)=4*k := by omega
      simpa only [he,nativeRootTestExpect,qs,μ,q,center] using hrK pre mid tail hcut hindex T t

theorem actual_inherited_native_star_to_all_projection_powers_along
    {m delta cl cu Az C0 Ct D Bclock Temp Cf saving : ℝ}
    (hCf : 0 ≤ Cf) (hC0 : 0 < C0) (hsaving : 0 < saving)
    (hroom : saving < (5:ℝ)/6+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (w : ℕ→ActualSlowWindowChoice)
    (Hnative : ∀p : ℕ,ActualNativeStarMomentOnEveryFinalNetAlong p saving M W w) :
    (∀p : ℕ,ActualOriginalRestStarMomentOnEveryFinalNetAlong p (saving/2) M W w) ∧
    (∀p : ℕ,ActualOriginalStarProjectionPowerOnEveryFinalNetAlong p (saving/2) M W w) ∧
    ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k (saving/2) M W w := by
  have Hrest (p : ℕ) : ActualOriginalRestStarMomentOnEveryFinalNetAlong p (saving/2) M W w :=
    actual_inherited_native_star_every_final_net_to_rest_along p hCf hC0 hsaving hroom
      dim hdim M W hxs hWlim hsource w (Hnative p)
  have Hpow (p : ℕ) : ActualOriginalStarProjectionPowerOnEveryFinalNetAlong p (saving/2) M W w :=
    actual_rest_star_to_projection_powers_along p M W w (Hrest p)
  exact ⟨Hrest,Hpow,fun j k=>actual_star_projection_powers_to_mixed_along j k M W
    (fun n=>(M n).hxs.le.trans (hxs n)) w Hpow⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
