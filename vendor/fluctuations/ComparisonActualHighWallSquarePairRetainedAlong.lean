module

public import ComparisonActualHighWallSquareStarRetainedAlong
public import ComparisonActualHighWallRawResourcePairBudget
public import ComparisonActualHighWallStarProducerAllOrderAlong

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

def ActualHighWallSquareResourcePairBudgetsOnGrid
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree : ℕ) (A saving Cmass : ℝ)
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (u : PositiveMass) (as : List PositiveMass) : Prop :=
  let star:=retainedMassPrefixIndex u.val as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let center:=nativePhysicalResourceCenter n M.bf M.hf as
  let epsilon:=((n+1:ℕ):ℝ)^(-saving)
  let budget:=fun (U i : ℕ) (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T)
      (a t : ℝ)=>
    P.PairMomentBudget (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as b h a t)
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) center 0
      A M.data.d M.data.d epsilon
  (∀(U i k : ℕ) (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
    NativeActualResourceGenerated i star U [] k T P→k ≤ degree→
    ∀a t : ℝ,a∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→budget U i T P a t) ∧
  (∀(U i k : ℕ) (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
    NativeActualResourceGenerated i star U [.initial] k T P→1+k ≤ degree→i ≤ as.length→
    partitionPoint 0 as i ≤ Cmass*M.data.d→
    ∀a t : ℝ,a∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→budget U i T P a t)

def ActualHighWallSquareResourcePairBudgetOnRetainedMasterAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (degree : ℕ) (A saving Cmass : ℝ)
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,
    ∀L : ℕ,((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs→
    ∀extra : List PositiveMass,(∀u∈extra,u.val ≤ 1)→
    ∃us : List PositiveMass,(∀u∈us,u.val ≤ 1) ∧ (∀u∈extra,u∈us) ∧
      (∀u∈uniformMasses L,u∈us) ∧ (w n).star∈us ∧
      ∀ᶠj : ℕ in atTop,
        ActualHighWallSquareResourcePairBudgetsOnGrid degree A saving Cmass
          (M n) (w n).star (finiteCutMasses us j)

theorem actual_high_wall_square_resource_pair_budget_of_actual_square_star_along
    (degree : ℕ) (hd : 0 < degree)
    {m delta cl cu Az C0 Ct D Bclock saving : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (Cmass : ℝ) (hCm : 0 ≤ Cmass)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (w : ℕ→ActualSlowWindowChoice)
    (Hstar : ActualHighWallOriginalSquareStarOnRetainedMasterAlong (degree-1) saving
      dim M (fun n=>(M n).data.d) w) :
    ∃A : ℝ,1 ≤ A ∧ ActualHighWallSquareResourcePairBudgetOnRetainedMasterAlong
      degree A saving Cmass dim M w := by
  obtain ⟨Cin,hCin,Hinitial⟩:=eventually_actual_high_wall_raw_resource_initial_pair_even_moment
    degree hd Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let A:=max 1 Cin
  have hA1 : 1 ≤ A:=le_max_left _ _
  have hCA : Cin ≤ A:=le_max_right _ _
  refine ⟨A,hA1,?_⟩
  filter_upwards [hdim.eventually Hinitial,Hstar] with n hn hsn
  intro L hmesh extra hextra
  obtain ⟨us,hus,hretain,hstar,HstarData⟩:=hsn (extra++uniformMasses L) (by
    intro u hu
    rcases List.mem_append.mp hu with h | h
    · exact hextra u h
    · exact (uniformMasses_ordered L).members_le_one u h)
  have hext : ∀u∈extra,u∈us:=fun u hu=>hretain u (List.mem_append_left _ hu)
  have hret : ∀u∈uniformMasses L,u∈us:=fun u hu=>hretain u (List.mem_append_right _ hu)
  refine ⟨us,hus,hext,hret,hstar,?_⟩
  filter_upwards [hn (M n) (hfixed n) L us hus hret hmesh,HstarData] with j hj hsj
  dsimp only at hj hsj ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun k=>((M n).bf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>((M n).hf (partitionPoint 0 as k):ℝ)
  let ho:=finiteCutMasses_ordered us hus j
  let center:=nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as
  let epsilon:=((dim n+1:ℕ):ℝ)^(-saving)
  have hdpos : 0 < (M n).data.d:=(M n).data.hd
  have heps : 0 < epsilon:=by dsimp only [epsilon];positivity
  have hNode : partitionPoint 0 as star=(w n).star.val:=
    nativeRetainedCut_partitionPoint as ho (w n).star (finiteCutMasses_nodes us j hstar)
  have hCenterStar : center star=orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val:=by
    dsimp only [center]
    rw [native_physical_resource_center_at_positive_cut (dim n) (M n).bf (M n).hf
      ((M n).data.bf_monotone (M n).alpha) ((M n).data.hf_monotone (M n).alpha)
      as ho star (by rw [hNode];exact (w n).star.property),hNode]
  have HstarLow (U : ℕ) (a t : ℝ) (ha : a∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
      (l : ℕ) (hl : 0 < l) (hlD : l ≤ degree) :
      (pairClock (S:=Spin (dim n)×Bool) as star).disorderExpect (fullWeight (dim n))
        (fullFeature (dim n)) 0 (finitePhysicalCavitySquareVariance (dim n) U as b h a t)
        (fun σ=>|deletedOverlap (dim n) (joinSpin (pairSpin as star σ).1)
          (joinSpin (pairSpin as star σ).2)-center star|^(2*l)) 0 ≤
        (A*(epsilon*(M n).data.d))^(2*l):=by
    let V:=pairClock (S:=Spin (dim n)×Bool) as star
    let F:=fun σ : V.Assignment=>deletedOverlap (dim n) (joinSpin (pairSpin as star σ).1)
      (joinSpin (pairSpin as star σ).2)-center star
    have horder : degree-1+1=degree:=by omega
    have Hhigh:=hsj U a t ha ht
    simp only [horder] at Hhigh
    have HH : V.disorderExpect (fullWeight (dim n)) (fullFeature (dim n)) 0
        (finitePhysicalCavitySquareVariance (dim n) U as b h a t)
        (fun σ=>|F σ|^(2*degree)) 0 ≤ (A*(epsilon*(M n).data.d))^(2*degree):=by
      change nativeOriginalSquareCenteredMoment (dim n) degree U as b h star (center star) a t ≤ _
      rw [hCenterStar]
      exact Hhigh.trans (pow_le_pow_left₀ (by positivity)
        (le_mul_of_one_le_left (by positivity : 0 ≤ epsilon*(M n).data.d) hA1) _)
    have Hlow:=V.disorderExpect_rpow_moment_le (fullWeight_pos (dim n)) (fullFeature (dim n))
      ho 0 (finitePhysicalCavitySquareVariance (dim n) U as b h a t) 0 F
      (p:=(2*l:ℕ)) (r:=(2*degree:ℕ)) (by exact_mod_cast (show 0 < 2*l by omega))
      (by exact_mod_cast (show 2*l ≤ 2*degree by omega)) (by positivity : 0 ≤ A*(epsilon*(M n).data.d))
      (by simpa only [Real.rpow_natCast] using HH)
    simpa only [Real.rpow_natCast,V,F] using Hlow
  change (∀_, _) ∧ (∀_, _)
  constructor
  · intro U i k T P hP hdegree a t ha ht
    apply hP.pairMomentBudget_of_constant_star_bounds degree hdegree
      (fullWeight (dim n)) (fullFeature (dim n)) 0
      (finitePhysicalCavitySquareVariance (dim n) U as b h a t)
      (fun σ τ=>deletedOverlap (dim n) (joinSpin σ) (joinSpin τ)) center 0
      A (M n).data.d (M n).data.d epsilon
    exact HstarLow U a t ha ht
  · intro U i k T P hP hdegree hi hmass a t ha ht
    apply hP.pairMomentBudget_of_initial_star_bounds degree hdegree
      (fullWeight (dim n)) (fullFeature (dim n)) 0
      (finitePhysicalCavitySquareVariance (dim n) U as b h a t)
      (fun σ τ=>deletedOverlap (dim n) (joinSpin σ) (joinSpin τ)) center 0
      A (M n).data.d (M n).data.d epsilon
    · intro l hl hlD
      let V:=pairClock (S:=Spin (dim n)×Bool) as i
      let F:=fun σ : V.Assignment=>deletedOverlap (dim n) (joinSpin (pairSpin as i σ).1)
        (joinSpin (pairSpin as i σ).2)-center i
      have HH:=hj U i a t ha ht hi hmass
      have HH' : V.disorderExpect (fullWeight (dim n)) (fullFeature (dim n)) 0
          (finitePhysicalCavitySquareVariance (dim n) U as b h a t)
          (fun σ=>|F σ|^(2*degree)) 0 ≤ (A*(M n).data.d)^(2*degree):=
        HH.trans (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCA hdpos.le) _)
      have Hlow:=V.disorderExpect_rpow_moment_le (fullWeight_pos (dim n)) (fullFeature (dim n))
        ho 0 (finitePhysicalCavitySquareVariance (dim n) U as b h a t) 0 F
        (p:=(2*l:ℕ)) (r:=(2*degree:ℕ)) (by exact_mod_cast (show 0 < 2*l by omega))
        (by exact_mod_cast (show 2*l ≤ 2*degree by omega)) (by positivity : 0 ≤ A*(M n).data.d)
        (by simpa only [Real.rpow_natCast] using HH')
      simpa only [Real.rpow_natCast,V,F] using Hlow
    · exact HstarLow U a t ha ht

end OAI.SKFluctuations.LaplaceWindowFormalization
