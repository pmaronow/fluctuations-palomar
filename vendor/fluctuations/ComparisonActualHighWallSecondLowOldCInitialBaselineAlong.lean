module

public import ComparisonActualHighWallSecondLowOldCInitialPoint
public import ComparisonActualGeneralCanonicalMarkedReset
public import ComparisonSignedCavityActualTerminalGAtom

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal ENNReal
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

private theorem old_c_weight_abs_le {α : Type} (L : List α) (w F : α→ℝ)
    {B : ℝ} (H : ∀x∈L,|F x|≤B) :
    |(L.map (fun x=>w x*F x)).sum|≤(L.map (fun x=>|w x|)).sum*B := by
  induction L with
  | nil=>simp
  | cons x L ih=>
    simp only [List.map_cons,List.sum_cons,add_mul]
    exact (abs_add_le _ _).trans (add_le_add
      (by rw [abs_mul];exact mul_le_mul_of_nonneg_left (H x List.mem_cons_self) (abs_nonneg _))
      (ih (fun y hy=>H y (List.mem_cons_of_mem _ hy))))

private theorem old_c_filtered_nonneg_sum_le {α : Type} (L : List α) (P : α→Bool)
    (F : α→ℝ) (H : ∀x∈L,0≤F x) :
    ((L.filter P).map F).sum≤(L.map F).sum := by
  induction L with
  | nil=>simp
  | cons x L ih=>
    have HH:=ih (fun y hy=>H y (List.mem_cons_of_mem x hy))
    cases HP : P x with
    | true=>simpa only [List.filter_cons,HP,ite_true,List.map_cons,List.sum_cons]
        using add_le_add (le_refl (F x)) HH
    | false=>
      simp only [List.filter_cons,HP,Bool.false_eq_true,ite_false,List.map_cons,List.sum_cons]
      exact HH.trans (le_add_of_nonneg_left (H x List.mem_cons_self))

private theorem old_c_HIGH_variation {S : Type} {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (a : T.Slot) (U rBound : ℕ) (hT : T.leaves≤rBound) :
    ((nativeHighMarkedRows T a (U-1) 0).map (fun p=>|p.coeff|)).sum≤2*(rBound:ℝ) := by
  rw [nativeHighMarkedRows_eq_filter]
  apply (old_c_filtered_nonneg_sum_le (T.markedAttach 0)
    (fun p=>decide (U-1<p.tree.splitIndex (p.embed a) p.mark)) _ (fun p _=>abs_nonneg p.coeff)).trans
  rw [T.markedAttach_variation ho,sub_zero]
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hT) (by norm_num)

theorem eventually_actual_high_wall_second_low_occupied_old_c_baseline_initial_modulus_price_along
    (degree rBound : ℕ) (Bclock Cmass Ccut : ℝ) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C Ci : ℝ,0 < C ∧ 0 < Ci ∧ ∀ᶠn in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ → RestCoordinate (dim n) → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i star U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (hU : U ≤ as.length),
        i ≤ star → star < U → T.leaves ≤ rBound → NativePersistentLowForks i star U T →
        partitionPoint 0 as U ≤ Ccut*M.data.d →
        ∀(G : ActualNaturalBoundaryShape (dim n) (degree+1) T) (forms : Fin (degree+1) → NativeSourceFactorForm),
        (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀(e0 : Fin (degree+1)) (initialCut : ℕ),forms e0=.centered →
          T.splitIndex (G.i e0) (G.j e0)=initialCut → ∀s : T.Slot,
        |nativeSecondLowFreshOccupiedOldCBaselineSource (dim n) q U b h K T s star hU
          (G.canonicalHighWallSource M forms).restProduct| ≤ C*M.data.d^3*M.data.d^degree*(Ci*M.data.d*
            originalInitialLowMomentModulus
              (originalHighWallInitialPairErrorScale M as initialCut) (Ci*M.data.d) 8) := by
  obtain ⟨Cp,Ci,hCp,hCi,HP⟩:=eventually_actual_high_wall_second_low_old_c_baseline_point_initial_modulus_budget
    (D:=D) degree (rBound+2) Bclock Cmass Ccut hCm hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let Poly:ℝ:=2*(rBound+1)^2
  have hPoly : 0 < Poly:=by dsimp [Poly];positivity
  let C:=Poly*Cp*Ccut+1
  refine ⟨C,Ci,by dsimp [C];positivity,hCi,?_⟩
  filter_upwards [hdim.eventually HP] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 as j)
  let q : ℕ → RestCoordinate (dim n) → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  intro i star U T hU hiStar hstarU hT hpersistent hcut G forms hmass e0 initialCut hform hinit s
  let g:=nativeFreshAtSlot T 0 s star
  have hgMem:g∈T.markedAttach 0:=nativeFreshAtSlot_mem T 0 s star
  let Gg:=G.retainOnMarked 0 g hgMem
  let P:=(G.canonicalHighWallSource M forms).restProduct
  let Pg:=fun old=>P (g.restRestrict old)
  have hgLeaves:g.tree.leaves ≤ rBound+1:=
    (T.markedAttach_leaves 0 g hgMem).trans (Nat.add_le_add_right hT 1)
  let eta:=originalInitialLowMomentModulus
    (originalHighWallInitialPairErrorScale M as initialCut) (Ci*M.data.d) 8
  let A:=Ci*M.data.d*eta
  have he:=original_high_wall_initial_pair_error_scale_nonneg M as initialCut
  have hA : 0 ≤ A:=mul_nonneg (mul_nonneg hCi.le M.data.hd.le)
    (original_initial_low_moment_modulus_nonneg he (mul_nonneg hCi.le M.data.hd.le) 8)
  let B:=Cp*M.data.d^2*M.data.d^degree*A
  have hB : 0 ≤ B:=mul_nonneg (mul_nonneg (mul_nonneg hCp.le (pow_nonneg M.data.hd.le 2))
    (pow_nonneg M.data.hd.le degree)) hA
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hUmas : 0 ≤ partitionPoint 0 as U:=(partitionPoint_mem as ho U).1
  have Hpoint (block : NativeSecondLowFreshOccupiedMiddleBlock T s star U hU)
      (p : MarkedPlacement g.tree) (hp : p∈nativeHighMarkedRows g.tree (g.embed s) (U-1) 0) :
      |p.tree.cavityLeft.disorderExpect (restWeight (dim n)) (restFeature (dim n)) 0 q
        (nativeSecondLowUnweightedCOldPayload (dim n) U b h K p.tree p.mark
          (p.embed (nativeSecondLowOccupiedBlockRepresentative g.tree U hU block.val)) (p.embed g.mark)
          (fun old=>Pg (p.restRestrict old))) 0| ≤ B := by
    have hpMem:=((mem_nativeHighMarkedRows g.tree (g.embed s) (U-1) 0 p).mp hp).1
    let Gp:=Gg.retainOnMarked 0 p hpMem
    have hpLeaves:p.tree.leaves ≤ rBound+2:=
      (g.tree.markedAttach_leaves 0 p hpMem).trans (by omega)
    have HPsource:(Gp.canonicalHighWallSource M forms).restProduct=(fun old=>Pg (p.restRestrict old)):=by
      funext τ
      exact (Gg.retained_canonical_physical_restProduct M.bf M.hf forms 0 p hpMem τ).trans
        (G.retained_canonical_physical_restProduct M.bf M.hf forms 0 g hgMem (p.restRestrict τ))
    have Hmass : ∀e,Gp.sourceLowMass e ≤ Cmass*M.data.d:=by
      intro e
      rw [ActualNaturalBoundaryShape.retained_source_mass,ActualNaturalBoundaryShape.retained_source_mass]
      exact hmass e
    have Hcuts:=native_second_low_fresh_occupied_old_c_equal_LOW_cuts T s i star U hU
      hiStar hstarU hpersistent block p hp
    have Hfc : p.tree.splitIndex p.mark
        (p.embed (nativeSecondLowOccupiedBlockRepresentative g.tree U hU block.val)) < U := by
      rcases Hcuts with H|H <;> rw [H.1]
      · exact hiStar.trans_lt hstarU
      · exact hstarU
    have Hcz : p.tree.splitIndex (p.embed (nativeSecondLowOccupiedBlockRepresentative g.tree U hU block.val))
        (p.embed g.mark) < U := by
      rcases Hcuts with H|H <;> rw [H.2]
      · exact hiStar.trans_lt hstarU
      · exact hstarU
    have Hfz:p.mark ≠ p.embed g.mark:=native_second_low_low_slots_ne p.tree U hU _ _
      ((native_second_low_fresh_HIGH_mark_tooth_split_eq_star T s star U hU hstarU p hp).trans_lt hstarU)
    have Hinitial : p.tree.splitIndex (Gp.i e0) (Gp.j e0)=initialCut:=by
      dsimp only [Gp,Gg,ActualNaturalBoundaryShape.retainOnMarked]
      rw [(g.tree.markedAttach_embed_preserves 0 p hpMem).2,
        (T.markedAttach_embed_preserves 0 g hgMem).2]
      exact hinit
    have HH:=hk U p.tree hU hcut hpLeaves Gp forms Hmass e0 initialCut hform Hinitial p.mark
      (p.embed (nativeSecondLowOccupiedBlockRepresentative g.tree U hU block.val)) (p.embed g.mark)
      Hfc Hcz Hfz
    rw [HPsource] at HH
    exact HH
  have Hblock (block : NativeSecondLowFreshOccupiedMiddleBlock T s star U hU) :
      |nativeSecondLowCanonicalOldCBaselineSource (dim n) q U b h K g.tree Pg
        (g.embed s) (nativeSecondLowOccupiedBlockRepresentative g.tree U hU block.val) g.mark|≤
        2*(rBound+1)*partitionPoint 0 as U*B := by
    unfold nativeSecondLowCanonicalOldCBaselineSource
    have Hnorm (p : MarkedPlacement g.tree) (hp : p∈nativeHighMarkedRows g.tree (g.embed s) (U-1) 0) :
        |fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*partitionPoint 0 as U*
          p.tree.cavityLeft.disorderExpect (restWeight (dim n)) (restFeature (dim n)) 0 q
            (nativeSecondLowUnweightedCOldPayload (dim n) U b h K p.tree p.mark
              (p.embed (nativeSecondLowOccupiedBlockRepresentative g.tree U hU block.val)) (p.embed g.mark)
              (fun old=>Pg (p.restRestrict old))) 0|≤partitionPoint 0 as U*B := by
      rw [abs_mul,abs_mul,abs_of_nonneg hUmas]
      have HG:=native_full_scalar_cut_moment_abs_le_one p.tree ho U K [p.embed (g.embed s),p.mark]
      change |fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark|≤1 at HG
      apply (mul_le_mul (mul_le_mul_of_nonneg_right HG hUmas) (Hpoint block p hp)
        (abs_nonneg _) (mul_nonneg zero_le_one hUmas)).trans_eq
      ring
    have HH:=old_c_weight_abs_le (nativeHighMarkedRows g.tree (g.embed s) (U-1) 0)
      (fun p=>p.coeff) _ Hnorm
    simp_rw [mul_assoc] at HH ⊢
    apply HH.trans
    convert mul_le_mul_of_nonneg_right (old_c_HIGH_variation g.tree ho (g.embed s) U (rBound+1) hgLeaves)
      (mul_nonneg hUmas hB) using 1; push_cast; ring
  unfold nativeSecondLowFreshOccupiedOldCBaselineSource
  dsimp only
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun block _=>Hblock block)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have Hcount:=native_second_low_fresh_occupied_middle_block_count T s star U hU
  have HcountR:(Fintype.card (NativeSecondLowFreshOccupiedMiddleBlock T s star U hU):ℝ)≤rBound:=
    Nat.cast_le.mpr (Hcount.trans hT)
  have Hpoly:(Fintype.card (NativeSecondLowFreshOccupiedMiddleBlock T s star U hU):ℝ)*
      (2*(rBound+1))≤Poly:=by
    dsimp [Poly]
    have Hr:0≤(rBound:ℝ):=Nat.cast_nonneg _
    nlinarith only [HcountR,Hr]
  have Htotal:=mul_le_mul_of_nonneg_right Hpoly (mul_nonneg hUmas hB)
  have Hstep : (Fintype.card (NativeSecondLowFreshOccupiedMiddleBlock T s star U hU):ℝ)*
      (2*(rBound+1)*partitionPoint 0 as U*B) ≤ Poly*partitionPoint 0 as U*B := by
    convert Htotal using 1 <;> ring
  apply Hstep.trans
  have Hmass:=mul_le_mul_of_nonneg_right hcut (mul_nonneg hPoly.le hB)
  have Hcoefficient : Poly*Cp*Ccut ≤ C:=by dsimp [C];linarith
  have Hlast:=mul_le_mul_of_nonneg_right Hcoefficient
    (mul_nonneg (mul_nonneg (pow_nonneg M.data.hd.le 3) (pow_nonneg M.data.hd.le degree)) hA)
  apply (show Poly*partitionPoint 0 as U*B ≤ (Poly*Cp*Ccut)*M.data.d^3*M.data.d^degree*A by
    convert Hmass using 1 <;> dsimp [B] <;> ring).trans (by convert Hlast using 1 <;> dsimp only [A,eta] <;> ring)

end OAI.SKFluctuations.Cavity
