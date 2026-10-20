module

public import ComparisonSignedCavityCanonicalExteriorPayload
public import ComparisonSignedCavityActualStarSubtreeErrorEven

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem NativeCanonicalExteriorSource.error_moment_eq
    {n a : ℕ} {pre mid tail : List PositiveMass}
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))} {s : T.cavityLeft.Slot}
    {G : ActualNaturalBoundaryShape n a T} {v : RestCoordinate n→ℝ}
    {q : ℕ→RestCoordinate n→ℝ} {x : RestCoordinate n→ℝ}
    (E : NativeCanonicalExteriorSource n a pre mid tail T s G v q x)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (F : T.cavityLeft.Assignment→ℝ) (error : E.D.Assignment→ℝ)
    (hF : ∀η ζ δ,F (E.read η ζ δ)=error δ) (p : ℕ) :
    nativeRootTestExpect n E.D (nativeStarSuffixClock n pre mid q)
      (nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x)
      exteriorForestStarRoot (fun _ δ=>error δ^p)=
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) v q (fun σ=>F σ^p) x := by
  rw [E.whole_law]
  unfold nativeRootTestExpect nativeStarSuffixClock
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  simp_rw [nativeExteriorForestConditionalTest_eq_joint,ClockTree.expect_fork,hF]
  rw [E.Es.expect_const (restWeight_pos n) (restFeature n) ho.suffix_end.suffix_end,
    E.Ei.expect_const (restWeight_pos n) (restFeature n) ho.suffix_end]

theorem eventually_actual_minimum_canonical_source_error_even_bound
    (order : ℕ) (horder : 0 < order) (Bclock Temp : ℝ) (hTemp : 0 ≤ Temp)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (a : ℕ)
          (G : ActualNaturalBoundaryShape n a T) (s e f : T.cavityLeft.Slot),e ≠ f →
        ∀E : NativeCanonicalExteriorSource n a pre mid tail T s G 0 q 0,
        ∀error : E.D.Assignment→ℝ,
          let j:=T.cavityLeft.splitIndex e f
          let center:=orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
          (∀η ζ δ,deletedOverlap n (joinSpin (T.cavityLeft.atSlot (E.read η ζ δ) e,false))
            (joinSpin (T.cavityLeft.atSlot (E.read η ζ δ) f,false))-center=error δ) →
          nativeRootTestExpect n E.D (nativeStarSuffixClock n pre mid q)
            (nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0)
            exteriorForestStarRoot (fun _ δ=>error δ^(2*order)) ≤
            (C*(M.xs+partitionPoint 0 as j))^(2*order) := by
  obtain ⟨C,hC,HR⟩:=eventually_actual_minimum_bare_centered_pair_even_moment
    (D:=D) order horder Bclock Temp hTemp hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HR,eventually_gt_atTop (0:ℕ)] with n hn hn0
  let : Nonempty (RestCoordinate n):=⟨Sum.inr ⟨0,hn0⟩⟩
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hn M hb hh hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut T a G s e f hef E error herror
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let j:=T.cavityLeft.splitIndex e f
  let Q:=fun σ τ=>deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))-S j
  have ho:MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  have hj:j ≤ (pre++(mid++tail)).length:=T.cavityLeft.splitIndex_le_clockLength e f
  rw [E.error_moment_eq ho (fun σ=>Q (T.cavityLeft.atSlot σ e) (T.cavityLeft.atSlot σ f)) error herror]
  rw [T.cavityLeft.disorderExpect_pairAtSlot_actual (restWeight_pos n) (restFeature n)
    ho 0 q 0 e f hef (fun σ τ=>Q σ τ^(2*order))]
  have HT:=native_rest_centered_pair_eq_decoupled n order hn0 ho b h K 0 j hj (S j)
  simp only [(even_two_mul order).pow_abs] at HT
  change (ClockTree.pairClock (pre++(mid++tail)) j).disorderExpect (restWeight n) (restFeature n) 0 q
    (fun σ=>(deletedOverlap n (joinSpin ((ClockTree.pairSpin _ j σ).1,false))
      (joinSpin ((ClockTree.pairSpin _ j σ).2,false))-S j)^(2*order)) 0 ≤ _
  rw [HT]
  have HH:=hk 0 0 0 (by norm_num) (by norm_num) j (by simpa only [hcut] using hj)
  have HK (bs : List PositiveMass) (hbs:bs=as) :
      (ClockTree.pairClock bs j).disorderExpect (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q 0 0 0 b h K)
        (fun σ=>(deletedOverlap n (joinSpin (ClockTree.pairSpin bs j σ).1)
          (joinSpin (ClockTree.pairSpin bs j σ).2)-S j)^(2*order)) 0 ≤
        (C*(M.xs+partitionPoint 0 as j))^(2*order) := by
    subst bs
    simpa only [(even_two_mul order).pow_abs,q,b,h,K,S,as] using HH
  exact HK (pre++(mid++tail)) hcut

end OAI.SKFluctuations.Cavity
