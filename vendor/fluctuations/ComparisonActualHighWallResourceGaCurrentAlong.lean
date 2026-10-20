module

public import ComparisonActualHighWallCurrentGaAlongCubic
public import ComparisonActualHighWallRawResourcePairBudget
public import ComparisonActualGeneralResourceGaReadout
public import ComparisonActualGeneralResourceScalarLiveNorm

@[expose] public section

noncomputable section
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Cavity LaplaceWindowFormalization NativeOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualHighWallResourceGaCurrentOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (degree rBound : ℕ) (eta Cmass C : ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠj : ℕ in atTop,
    let as:=finiteCutMasses us j
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
    ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (U k : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P →
      P.resources.length ≤ degree → 0 < mid.length → pre.length+mid.length < U →
      U≤(pre++(mid++tail)).length → T.leaves≤rBound →
    ∀x V : ℝ,(M n).xs ≤ x → x ≤ W n →
      partitionPoint 0 as pre.length ≤ Cmass*x → W n ≤ V → V ≤ 1 →
      V≤(M n).data.wallRadius (M n).alpha (partitionPoint 0 as U) →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ V/2 → (M n).z ≤ V/2 →
      |((W n)⁻¹)^k*actualGeneralResourceGaCurrent (M n).bf (M n).hf U P| ≤
        |P.coefficient| *C*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2)*nativeResourceScale x (W n) 1 seed

theorem actual_high_wall_resource_Ga_current_from_cubic_rows_along (hdim : Tendsto dim atTop atTop)
    {m delta cl cu Az C0 Ct D Bclock eta Cmass : ℝ}
    (degree rBound : ℕ) (hCm : 0 ≤ Cmass)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hcanonical : ∀n,W n=(M n).data.d)
    (Hrows : ∀a b d : ℕ,ActualHighWallCurrentGProjectedCubicOnEveryFinalNetAlong a b d rBound eta Cmass M W w) :
    ∃C : ℝ,0<C ∧ ActualHighWallResourceGaCurrentOnEveryFinalNetAlong degree rBound eta Cmass C M W w := by
  obtain ⟨A,hA,HA⟩:=eventually_actual_high_wall_raw_resource_pair_budget
    (D:=D) (degree+1) (by omega) Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=2*((1+Cmass)^degree*A^degree)
  have hC : 0<C:=by dsimp only [C];have hA0:=zero_lt_one.trans_le hA;positivity
  refine ⟨C,hC,?_⟩
  let F:=Fin (degree+1)×Fin (degree+1)×Fin (degree+1)
  have HF (p : F):=Hrows p.1 p.2.1 p.2.2
  filter_upwards [Filter.eventually_all.mpr HF,hdim.eventually HA] with n hnR hnA
  intro L us hus hret hmesh hstar
  filter_upwards [Filter.eventually_all.mpr (fun p : F=>hnR p L us hus hret hmesh hstar),
    hnA (M n) (hfixed n) L us hus hret hmesh] with j hjR hjA
  dsimp only at hjR hjA ⊢
  intro pre mid tail hcut hindex hmass T U k seed P hP hdegree hmid hs hU hT
    x V hx hxW hmi hWV hV1 hVU hlow hz
  have he : P.live.test.edges.length ≤ degree:=by
    have HH:=P.live.realizes.length_eq
    have HL : P.live.tags.length ≤ P.resources.length:=by
      simp only [NativeResourceTerm.resources,List.length_append]
      omega
    simp only [List.length_map,NativeResourceMonomial.tags] at HH HL
    omega
  have hlen : P.live.test.edges.length=P.live.test.exterior.length+
      P.live.test.teeth.length+P.live.test.incoming.length:=by
    simp only [NativeGeneratedTest.edges,List.length_append,List.length_map]
  let p : F:=⟨⟨P.live.test.exterior.length,by omega⟩,
    ⟨P.live.test.edges.length-P.live.test.teeth.length,by omega⟩,
    ⟨P.live.test.teeth.length,by omega⟩⟩
  have HL:=hjR p pre mid tail hcut hindex hmass T U k seed P hP hmid hs hU
    rfl rfl (by dsimp only [p];omega) hT V hWV hV1 hVU hlow hz
  have HP:=hjA U pre.length (pre.length+mid.length)
  rw [←hcut] at HP
  have hxEq : x=(M n).data.d:=le_antisymm
    (hxW.trans_eq (hcanonical n)) (by simpa only [hfixed n] using hx)
  have HP':=HP T P (by omega) (by omega) (by omega)
    (by simpa only [hcut,hxEq] using hmi)
    (by simpa only [hcut,hcanonical n] using hmass)
    1 1 (by norm_num) (by norm_num)
  rw [←hxEq] at HP'
  have hWx : W n=x:=(hcanonical n).trans hxEq.symm
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus j
  have H:=actual_general_resource_original_scalar_live_normalized_bound (M n).bf (M n).hf (M n).xs (M n).hxs hP ho (by omega) (by omega)
    hdegree hA hx hxW hCm (by simpa only [hcut] using hmi)
    (price:=2*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2))
    (by have hW:0<W n:=(M n).hxs.trans_le (hx.trans hxW);positivity) (by simpa only [hWx] using HP')
    (actualGeneralDecoupledGProjectedResampling T P.live.test (pre.length+mid.length) U (M n).bf (M n).hf
      (fun j=>Sum.elim (fun _=>((M n).bf (partitionPoint 0 (pre++(mid++tail)) j):ℝ))
        (fun _=>((M n).hf (partitionPoint 0 (pre++(mid++tail)) j):ℝ))))
    (by simpa only [hcut] using HL)
  change |(W n)⁻¹^k*actualGeneralResourceGaCurrent (M n).bf (M n).hf U P|≤_ at H
  apply H.trans_eq
  dsimp only [C]
  ring

theorem actual_high_wall_same_star_resource_Ga_current_along
    (hdim : Tendsto dim atTop atTop)
    {m delta eta saving cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (Cmass : ℝ) (hCm : 1 ≤ Cmass) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).data.d)
    (hWlim : Tendsto W atTop (𝓝 0)) (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hsaving : 0 ≤ saving) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualHighWallMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) :
    ∃C : ℝ,0 < C ∧ ActualHighWallResourceGaCurrentOnEveryFinalNetAlong
      degree rBound eta Cmass C M W w := by
  exact actual_high_wall_resource_Ga_current_from_cubic_rows_along hdim degree rBound
    (zero_le_one.trans hCm) hm hdelta hroom hcl hcu hAz hC0 hCt M W w hfixed hcanonical
    (fun a b d=>eventually_actual_high_wall_same_star_current_G_cubic_rows_along hdim Cmass hCm heta
      hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim hfixed saving hsaving w Hmixed a b d rBound)

end OAI.SKFluctuations.Cavity
