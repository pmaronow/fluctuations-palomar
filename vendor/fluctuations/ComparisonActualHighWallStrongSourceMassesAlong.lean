module

public import ComparisonActualHighWallPairedFarGeometry
public import ComparisonSignedCavityActualDyadicRetainedChain

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

structure ActualHighWallStrongSourceMasses
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Cmass Ccut Cx c Rmacro : ℝ) (source outer : PositiveMass) : Prop where
  source_upper : source.val ≤ Ccut*M.data.d
  outer_upper : outer.val ≤ (Ccut+1)*M.data.d
  source_lt_outer : source.val < outer.val
  outer_le_one : outer.val ≤ 1
  source_lower : Cx*M.xs ≤ source.val
  high_lower : 2*c*M.data.d ≤ source.val
  low_lt_source : Cmass*M.data.d < source.val
  above_wall : M.data.s ≤ source.val
  scale_small : M.data.d ≤ Rmacro/2
  low_radius_small : (Az+1/cl)*(1+Cmass)*M.data.d ≤ Rmacro/4
  high_radius : 4*M.data.d ≤ M.data.wallRadius M.alpha source.val
  seed_radius : M.z ≤ min (M.data.wallRadius M.alpha source.val/8) (Rmacro/4)
  low_radius : ∀u∈Icc (0:ℝ) 1,u ≤ Cmass*M.data.d →
    M.data.wallRadius M.alpha u ≤ min (M.data.wallRadius M.alpha source.val/8) (Rmacro/4)

 theorem exists_actual_high_wall_strong_source_masses_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (Cmass Cx c Rmacro : ℝ) (hCm : 0 ≤ Cmass) (hCx : 0 < Cx) (hc : 0 < c)
    (hmacro : 0 < Rmacro) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0)) :
    ∃Ccut : ℝ,0 < Ccut ∧ ∀ᶠn in atTop,∃source outer : PositiveMass,
      source.val=Ccut*(M n).data.d ∧ outer.val=(Ccut+1)*(M n).data.d ∧
      ActualHighWallStrongSourceMasses (M n) Cmass Ccut Cx c Rmacro source outer := by
  let Clow:=(Az+1/cl)*(1+Cmass)
  let base:=8*cu*Clow+4*cu+cu*Az+1
  let Ccut:=base+Cmass+Cx+2*c+1
  have hClow : 0 < Clow:=by dsimp only [Clow];positivity
  have hbase : 1 ≤ base:=by
    have H1:=mul_nonneg hcu.le hClow.le
    have H2:=mul_nonneg hcu.le hAz
    dsimp only [base];nlinarith
  have hcut : 0 < Ccut:=by dsimp only [Ccut];positivity
  have hnear : 8*cu*((Az+1/cl)*(1+Cmass))+4*cu+cu*Az+1 ≤ Ccut:=by
    change base ≤ Ccut
    dsimp only [Ccut];linarith
  have hCxcut : Cx ≤ Ccut:=by dsimp only [Ccut];linarith
  have hccut : 2*c ≤ Ccut:=by dsimp only [Ccut];linarith
  have hmasscut : Cmass < Ccut:=by dsimp only [Ccut];linarith
  have hunitcut : 1 ≤ Ccut:=by dsimp only [Ccut];linarith
  have Hunit:=((hdlim.const_mul (Ccut+1)).eventually
    (eventually_lt_nhds (show (Ccut+1)*(0:ℝ) < 1 by simp)))
  have Hlow:=((hdlim.const_mul Clow).eventually
    (eventually_lt_nhds (show Clow*(0:ℝ) < Rmacro/4 by simpa using div_pos hmacro (by norm_num : (0:ℝ) < 4))))
  have Hscale:=hdlim.eventually
    (eventually_lt_nhds (show (0:ℝ) < Rmacro/2 by positivity))
  refine ⟨Ccut,hcut,?_⟩
  filter_upwards [Hunit,Hlow,Hscale] with n hnUnit hnLow hnScale
  let source : PositiveMass:=⟨Ccut*(M n).data.d,mul_pos hcut (M n).data.hd⟩
  let outer : PositiveMass:=⟨(Ccut+1)*(M n).data.d,mul_pos (by linarith) (M n).data.hd⟩
  have Hlt : source.val < outer.val:=by dsimp only [source,outer];nlinarith only [(M n).data.hd]
  have HunitS : source.val ≤ 1:=Hlt.le.trans hnUnit.le
  have Hlow' : (Az+1/cl)*(1+Cmass)*(M n).data.d ≤ Rmacro/4:=by exact hnLow.le
  have Hgeometry:=(M n).actual_paired_far_radius_geometry hcl hcu hAz hCm (M n).data.hd
    (hfixed n).le hnear Hlow' ⟨source.property.le,HunitS⟩ (by dsimp only [source];rfl)
  refine ⟨source,outer,rfl,rfl,?_,⟩
  refine ⟨le_rfl,le_rfl,Hlt,hnUnit.le,?_,?_,?_,?_,hnScale.le,Hlow',Hgeometry.1,Hgeometry.2.1,Hgeometry.2.2⟩
  · rw [hfixed n]
    exact mul_le_mul_of_nonneg_right hCxcut (M n).data.hd.le
  · exact mul_le_mul_of_nonneg_right hccut (M n).data.hd.le
  · exact mul_lt_mul_of_pos_right hmasscut (M n).data.hd
  · exact (M n).hsxs.trans (by
      rw [hfixed n]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hunitcut (M n).data.hd.le)

 theorem ActualHighWallStrongSourceMasses.exists_dyadic_retained_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Cmass Ccut Cx c Rmacro : ℝ}
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {source outer : PositiveMass}
    (H : ActualHighWallStrongSourceMasses M Cmass Ccut Cx c Rmacro source outer)
    (Lnet : ℕ) (extra : List PositiveMass) (hextra : ∀u∈extra,u.val ≤ 1) :
    ∃us : List PositiveMass,(∀u∈us,u.val ≤ 1) ∧
      source∈us ∧ outer∈us ∧ (∀u∈extra,u∈us) ∧ (∀u∈uniformMasses Lnet,u∈us) ∧
      (∀j≤nativeDyadicCutDepth source.val,nativeDyadicMassCut source.val source.property j∈us) ∧
      ∀k U,U ≤ (finiteCutMasses us k).length → partitionPoint 0 (finiteCutMasses us k) U=source.val →
        NativeDyadicRetainedReadout source.val source.property (finiteCutMasses us k) U := by
  have Hsource1 : source.val ≤ 1:=H.source_lt_outer.le.trans H.outer_le_one
  have Hmore : ∀u∈source::outer::extra,u.val ≤ 1:=by
    intro u hu
    simp only [List.mem_cons] at hu
    rcases hu with rfl|rfl|hu
    · exact Hsource1
    · exact H.outer_le_one
    · exact hextra u hu
  obtain ⟨us,hus,hnodes,hret,hmesh,Hgrid⟩:=native_dyadic_chain_exists_common_net
    source.property Hsource1 Lnet (source::outer::extra) Hmore
  exact ⟨us,hus,hret source (by simp),hret outer (by simp),
    fun u hu=>hret u (by simp [hu]),hmesh,hnodes,Hgrid⟩

end OAI.SKFluctuations.Cavity
