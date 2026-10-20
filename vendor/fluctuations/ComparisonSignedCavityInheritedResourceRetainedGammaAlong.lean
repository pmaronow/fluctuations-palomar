module

public import ComparisonSignedCavityInheritedResourceGaCurrent
public import ComparisonSignedCavityInheritedCurrentGammaCubicAlong
public import ComparisonSignedCavityActualResourceRetainedGammaNorm

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

def ActualResourceRetainedGammaOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (degree rBound : ℕ) (eta Cmass C : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
      V≤(M n).R (partitionPoint 0 as U) →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ V/2 → (M n).z ≤ V/2 →
      |((W n)⁻¹)^k*nativeActualResourceRetainedGammaRow (M n) U V P| ≤
        |P.coefficient| *C*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2)*nativeResourceScale x (W n) 1 seed

theorem actual_resource_retained_Gamma_from_cubic_rows_along (hdim : Tendsto dim atTop atTop)
    {m delta cl cu Az C0 Ct D Bclock Temp Cf eta Cmass : ℝ}
    (degree rBound : ℕ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (hsource : ∀ᶠn : ℕ in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hxs : ∀ᶠn : ℕ in atTop,(M n).xs ≤ 1)
    (Hrows : ∀a b d : ℕ,ActualCurrentProjectedCubicRowOnEveryFinalNetAlong a b d eta Cmass M W w) :
    ∃C : ℝ,0<C ∧ ActualResourceRetainedGammaOnEveryFinalNetAlong degree rBound eta Cmass C M W w := by
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget
    (D:=D) (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=2*((1+Cmass)^degree*A^degree)
  have hC : 0<C:=by dsimp only [C];have hA0:=zero_lt_one.trans_le hA;positivity
  refine ⟨C,hC,?_⟩
  let F:=Fin (degree+1)×Fin (degree+1)×Fin (degree+1)
  have HF (p : F):=Hrows p.1 p.2.1 p.2.2
  filter_upwards [Filter.eventually_all.mpr HF,hdim.eventually HA,hsource,hxs] with n hnR hnA hnsource hnxs
  intro L us hus hret hmesh hstar
  filter_upwards [Filter.eventually_all.mpr (fun p : F=>hnR p L us hus hret hmesh hstar),
    hnA (M n) hnsource hnxs L us hus hret hmesh] with j hjR hjA
  dsimp only at hjR hjA ⊢
  intro pre mid tail hcut hindex hmass T U k seed P hP hdegree hmid hs hU _hT
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
  have HL:=hjR p pre mid tail hcut hindex hmass T U k seed P hP hmid hs
    rfl rfl (by dsimp only [p];omega) V hWV hV1 hlow hz
  have HP:=hjA U pre.length (pre.length+mid.length)
  rw [←hcut] at HP
  have HP':=HP T P (by omega) (by omega) (by omega) x (W n) hx hxW
    (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass)
    1 1 (by norm_num) (by norm_num)
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus j
  have hNode : partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length)=(w n).star.val:=by
    rw [hcut,hindex]
    exact nativeRetainedCut_partitionPoint _ (finiteCutMasses_ordered us hus j) (w n).star
      (finiteCutMasses_nodes us j hstar)
  have hCenter : nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf
      (pre++(mid++tail)) (pre.length+mid.length)=
      orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val:=by
    unfold nativePhysicalResourceCenter
    rw [hNode]
    exact (orderedPathPair_eq_completed (dim n+1) (by omega) (M n).bf (M n).hf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone (orderedOverlap (dim n+1))
      ⟨(w n).star.property,by rw [←hNode];exact (partitionPoint_mem _ ho _).2⟩).symm
  have H:=actual_resource_original_scalar_live_normalized_bound (M n) hP ho (by omega) (by omega)
    hdegree hA hx hxW hCm (by simpa only [hcut] using hmi)
    (price:=2*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2))
    (by have hW:0<W n:=(M n).hxs.trans_le (hx.trans hxW);positivity) HP'
    (nativeResetProjectedGammaRow (dim n) T P.live.test (M n) U V
      (fun j=>Sum.elim (fun _=>((M n).bf (partitionPoint 0 (pre++(mid++tail)) j):ℝ))
        (fun _=>((M n).hf (partitionPoint 0 (pre++(mid++tail)) j):ℝ)))
      (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (pre++(mid++tail))) 0
      (nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf (pre++(mid++tail)) (pre.length+mid.length)))
    (by rw [hCenter];simpa only [hcut] using HL)
  change |((W n)⁻¹)^k*nativeActualResourceRetainedGammaRow (M n) U V P| ≤ _ at H
  apply H.trans_eq
  dsimp only [C]
  ring

theorem eventually_inherited_same_star_resource_retained_Gamma_along (hdim : Tendsto dim atTop atTop)
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (degree rBound : ℕ) (Cmass : ℝ) (hCm : 1 ≤ Cmass) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn : ℕ in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (saving : ℝ) (hsaving : 0 ≤ saving) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) :
    ∃C : ℝ,0<C ∧ ActualResourceRetainedGammaOnEveryFinalNetAlong degree rBound eta Cmass C M W w := by
  have HX : ∀ᶠn : ℕ in atTop,(M n).xs ≤ 1:=by
    filter_upwards [hWlim.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))] with n hn
    exact ((M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm).trans hn.le
  exact actual_resource_retained_Gamma_from_cubic_rows_along hdim degree rBound hTemp hCf
    (zero_le_one.trans hCm) hm hdelta hroom hcl hcu hAz hC0 hCt M W w hsource HX
    (inherited_same_star_current_Gamma_cubic_rows_along Cmass hCm heta hsaving hm hdelta hroom hgap
      hcl hcu hAz hC0 hCt hTemp hCf hCcal hdim M W hcanonical hWlim hcompare hsource w Hmixed)

end OAI.SKFluctuations.Cavity
