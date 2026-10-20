module

public import SKConstants.ScalarActualQueryStability
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory NormedSpace InnerProductSpace
open scoped NNReal Topology BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace SKConstants
open GaussianProposal

def queryEndpointGapFactor (n : ℕ) (M : ℝ) : ℝ :=
  Real.sqrt (n : ℝ)+2+3*Real.sqrt (n : ℝ)*M+2*M

def queryDirectionGapFactor (K : ℕ) (L : ℝ) : ℝ := 4*(1+(K : ℝ))*L+16

def coupledScalarQueryGapFactor (n K : ℕ) (L M : ℝ) : ℝ :=
  ((n : ℝ)*queryEndpointGapFactor n M+1)*queryDirectionGapFactor K L+
    (n : ℝ)*queryEndpointGapFactor n M+4

theorem scalarMeshMatrixQuery_pathGap_le
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : ∀ t, LipschitzWith 1 (m t))
    (scale : ℕ → ℝ) (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (r K : ℕ)
    (s t : ScalarMeshPaperPast H δ τ (r+K))
    (z w : StoppedNoise (Fin (r+K)) K)
    (W W' : Matrix (Fin (r+K)) (Fin (r+K)) ℝ)
    (c η C M sMin : ℝ) (hc : 0<c) (hη : 0≤η) (hC : 0≤ C) (hM : 0≤ M) (hsMin : 0<sMin)
    (hcN : c*Real.sqrt ((r+K : ℕ) : ℝ)≤1)
    (hseed : ∀ i, |s.1.1 i-t.1.1 i|≤η)
    (hD : ∀ i, ‖s.1.2.1 i-t.1.2.1 i‖≤η)
    (hInitial : scalarMeshPathGap s t≤η)
    (hfC : scalarStieltjesPathBound f H≤ C) (hgC : scalarStieltjesPathBound g H≤ C)
    (hδ : ∀ j : Fin K, 0<δ (j.val+1) ∧ δ (j.val+1)≤1)
    (hscale : ∀ j : Fin K, sMin≤ scale (j.val+1))
    (hbridge : ∀ j : Fin K, (∑ i, ‖s.1.2.2 (j.val+1) i-t.1.2.2 (j.val+1) i‖)≤η)
    (hW : ‖W-W'‖≤η) (hW' : ‖W'‖≤ M)
    (hz : ∀ j : Fin K, ‖WithLp.toLp 2 (fun i => paperNoiseTrace (r+K) K z j (.inl i))‖≤ M)
    (hzw : ∀ j : Fin K, ‖WithLp.toLp 2 (fun i =>
      paperNoiseTrace (r+K) K z j (.inl i)-paperNoiseTrace (r+K) K w j (.inl i))‖≤η)
    (hA : ‖familyGram (fun j => c • WithLp.toLp 2
      (paperMatrixQueryTargetTrace r (r+K) ((r+K : ℕ) : ℝ)
        (scalarMeshPaperTarget b f g hf hg m scale H δ τ (r+K) K)
        (scalarMeshPaperUpdate H δ τ (r+K) K) K (s,1) z W j))-1‖≤(3/4 : ℝ))
    (hB : ‖familyGram (fun j => c • WithLp.toLp 2
      (paperMatrixQueryTargetTrace r (r+K) ((r+K : ℕ) : ℝ)
        (scalarMeshPaperTarget b f g hf hg m scale H δ τ (r+K) K)
        (scalarMeshPaperUpdate H δ τ (r+K) K) K (t,1) w W' j))-1‖≤(3/4 : ℝ)) :
    scalarMeshPathGap
      (paperMatrixQueryRun r (r+K) ((r+K : ℕ) : ℝ)
        (scalarMeshPaperTarget b f g hf hg m scale H δ τ (r+K) K)
        (scalarMeshPaperUpdate H δ τ (r+K) K) K (s,1) z W)
      (paperMatrixQueryRun r (r+K) ((r+K : ℕ) : ℝ)
        (scalarMeshPaperTarget b f g hf hg m scale H δ τ (r+K) K)
        (scalarMeshPaperUpdate H δ τ (r+K) K) K (t,1) w W')≤
      2*η*(coupledScalarQueryGapFactor (r+K) K (scalarQueryTargetGapFactor b H C sMin) M)^K := by
  let target := scalarMeshPaperTarget b f g hf hg m scale H δ τ (r+K) K
  let update := scalarMeshPaperUpdate H δ τ (r+K) K
  let za := paperMatrixQueryNoiseRun r (r+K) ((r+K : ℕ) : ℝ) target update K (s,1) z W
  let zb := paperMatrixQueryNoiseRun r (r+K) ((r+K : ℕ) : ℝ) target update K (t,1) w W'
  let S := paperScalarPastTrace r (r+K) target update K (s,1) za
  let T := paperScalarPastTrace r (r+K) target update K (t,1) zb
  let U := fun j => WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (s,1) za j)
  let V := fun j => WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (t,1) zb j)
  let u : Fin K → ℝ := fun j => ‖U j-V j‖
  let B : Fin (K+1) → ℝ := fun j => scalarMeshPathGap (S j) (T j)
  let L := scalarQueryTargetGapFactor b H C sMin
  let A := queryDirectionGapFactor K L
  let E := ((r+K : ℕ) : ℝ)*queryEndpointGapFactor (r+K) M
  have hLa : 0≤ L := by dsimp [L,scalarQueryTargetGapFactor]; positivity
  have hAa : 0≤ A := by dsimp [A,queryDirectionGapFactor]; positivity
  have hEa : 0≤ E := by dsimp [E,queryEndpointGapFactor]; positivity
  have hBa (j) : 0≤ B j := scalarMeshPathGap_nonneg _ _
  have hua (j) : 0≤ u j := norm_nonneg _
  have hB0 : B 0≤η := by simpa only [B,S,T,paperScalarPastTrace_zero] using hInitial
  have hSA (j) : (S j).1=s.1 := scalarMeshPaperTrace_static H δ τ r (r+K) K target (s,1) za j
  have hTB (j) : (T j).1=t.1 := scalarMeshPaperTrace_static H δ τ r (r+K) K target (t,1) zb j
  have hdir (j : Fin K) : u j≤ A*(η+B j.castSucc+queryDirectionGapPrefix u j.castSucc) := by
    have h := actualPaper_directionTrace_difference_recursive_le r K target update s t za zb c hc hA hB j
    have htarget := scalarMeshPaperTargetTrace_difference_le b f g hf hg m hm scale H δ τ r K
      s t za zb c η C sMin hc.le hη hC hsMin (by simpa only [Nat.cast_add] using hcN)
      hseed hD hfC hgC j (hscale j)
    have hnorm := familyGram_small_vector_norm_le
      (fun j => c • WithLp.toLp 2 (paperTargetTrace r (r+K) target update K (t,1) zb j)) hB j
    have hp := queryDirectionGapPrefix_nonneg u hua j.castSucc
    rw [←queryDirectionGapPrefix_castSucc] at h
    change u j≤4*((1+(K : ℝ))*_+2*_*queryDirectionGapPrefix u j.castSucc) at h
    have hbase : 0≤η+B j.castSucc := add_nonneg hη (hBa _)
    have hmul1 := mul_le_mul_of_nonneg_left htarget (by positivity : 0≤1+(K : ℝ))
    have hmul2 := mul_le_mul_of_nonneg_right hnorm hp
    dsimp only [A,queryDirectionGapFactor,L] at hmul1 ⊢
    change _≤ L*(η+B j.castSucc) at htarget
    dsimp only [L] at htarget
    nlinarith [mul_nonneg hLa hp]
  have hpath (j : Fin K) : B j.succ≤ B j.castSucc+E*(η+queryDirectionGapPrefix u j.succ)+3*η := by
    have hindex : K-(K-1-j.val)=j.val+1 := by omega
    let az := WithLp.toLp 2 (fun i => paperNoiseTrace (r+K) K z j (.inl i))
    let bz := WithLp.toLp 2 (fun i => paperNoiseTrace (r+K) K w j (.inl i))
    let ae := WithLp.toLp 2 (fun i => paperNoiseTrace (r+K) K za j (.inl i))
    let be := WithLp.toLp 2 (fun i => paperNoiseTrace (r+K) K zb j (.inl i))
    have hz' : ‖az‖≤ M := hz j
    have hzw' : ‖az-bz‖≤η := by
      have heq : az-bz=WithLp.toLp 2 (fun i =>
          paperNoiseTrace (r+K) K z j (.inl i)-paperNoiseTrace (r+K) K w j (.inl i)) := by
        ext i
        rfl
      rw [heq]
      exact hzw j
    have hend := actualPaper_completedEndpoint_difference_le r K ((r+K : ℕ) : ℝ) target update s t za zb c hc hA hB W W' az bz j
    rw [←paperMatrixQueryNoiseTrace_endpoint r (r+K) ((r+K : ℕ) : ℝ) target update K (s,1) z W j,
      ←paperMatrixQueryNoiseTrace_endpoint r (r+K) ((r+K : ℕ) : ℝ) target update K (t,1) w W' j] at hend
    rw [←queryDirectionGapPrefix_succ] at hend
    change ‖ae-be‖≤ Real.sqrt ((r+K : ℕ) : ℝ)*‖W-W'‖+
      Real.sqrt ((r+K : ℕ) : ℝ)*‖W'‖*u j+2*queryDirectionGapPrefix u j.succ*
      (Real.sqrt ((r+K : ℕ) : ℝ)*‖W'‖+‖az‖)+2*‖az-bz‖ at hend
    have hp := queryDirectionGapPrefix_nonneg u hua j.succ
    have hup : u j≤ queryDirectionGapPrefix u j.succ := by
      rw [queryDirectionGapPrefix_step]
      have := queryDirectionGapPrefix_nonneg u hua j.castSucc
      linarith
    have hcoef : 0≤ Real.sqrt ((r+K : ℕ) : ℝ)*M := mul_nonneg (Real.sqrt_nonneg _) hM
    have hend' : ‖ae-be‖≤ queryEndpointGapFactor (r+K) M*(η+queryDirectionGapPrefix u j.succ) := by
      have h1 := mul_le_mul_of_nonneg_left hW (Real.sqrt_nonneg ((r+K : ℕ) : ℝ))
      have h2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hW' (Real.sqrt_nonneg ((r+K : ℕ) : ℝ))) (hua j)
      have h3 := mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hW' (Real.sqrt_nonneg ((r+K : ℕ) : ℝ))) hz') (by positivity : 0≤2*queryDirectionGapPrefix u j.succ)
      have h4 := mul_le_mul_of_nonneg_left hup hcoef
      dsimp [queryEndpointGapFactor]
      nlinarith [mul_nonneg (Real.sqrt_nonneg ((r+K : ℕ) : ℝ)) hp,
        mul_nonneg hcoef hη,mul_nonneg hM hη,mul_nonneg hM hp]
    have hbridge' : (∑ i, ‖(S j.castSucc).1.2.2 (K-(K-1-j.val)) i-
        (T j.castSucc).1.2.2 (K-(K-1-j.val)) i‖)≤η := by
      rw [hSA,hTB,hindex]
      exact hbridge j
    have hδ' : 0<δ (K-(K-1-j.val)) := by rw [hindex]; exact (hδ j).1
    have hsmall : Real.sqrt (δ (K-(K-1-j.val)) : ℝ)≤1 := by
      rw [hindex]
      exact (Real.sqrt_le_one).mpr (by exact_mod_cast (hδ j).2)
    have hupdate := scalarMeshPaperUpdate_pathGap_le H δ τ (r+K) K (K-1-j.val) hδ'
      (S j.castSucc) (T j.castSucc) (paperNoiseTrace (r+K) K za j) (paperNoiseTrace (r+K) K zb j)
    have heq : WithLp.toLp 2 (fun i => paperNoiseTrace (r+K) K za j (.inl i)-
        paperNoiseTrace (r+K) K zb j (.inl i))=ae-be := by ext i; rfl
    rw [heq] at hupdate
    have hstepA := paperScalarPastTrace_step r (r+K) target update K (s,1) za j
    have hstepB := paperScalarPastTrace_step r (r+K) target update K (t,1) zb j
    change S j.succ=_ at hstepA
    change T j.succ=_ at hstepB
    dsimp only [B]
    rw [hstepA,hstepB]
    change _≤ B j.castSucc+E*(η+queryDirectionGapPrefix u j.succ)+3*η
    have h5 := mul_le_mul_of_nonneg_right hsmall
      (mul_nonneg (by positivity : 0≤((r+K : ℕ) : ℝ)) (norm_nonneg (ae-be)))
    have h6 := mul_le_mul_of_nonneg_left hend' (by positivity : 0≤((r+K : ℕ) : ℝ))
    dsimp [E]
    nlinarith
  have hfinal := coupledQueryGap_geometric_bound B u η A E hη hAa hEa hBa hua hB0 hdir hpath (Fin.last K)
  have hp := queryDirectionGapPrefix_nonneg u hua (Fin.last K)
  have hlastA : S (Fin.last K)=paperMatrixQueryRun r (r+K) ((r+K : ℕ) : ℝ) target update K (s,1) z W := by
    rw [paperMatrixQueryRun_eq_replayed_terminal]
    exact paperScalarPastTrace_last r (r+K) target update K (s,1) za
  have hlastB : T (Fin.last K)=paperMatrixQueryRun r (r+K) ((r+K : ℕ) : ℝ) target update K (t,1) w W' := by
    rw [paperMatrixQueryRun_eq_replayed_terminal]
    exact paperScalarPastTrace_last r (r+K) target update K (t,1) zb
  dsimp only [B] at hfinal
  rw [hlastA,hlastB,Fin.val_last] at hfinal
  change _≤2*η*((E+1)*A+E+4)^K
  linarith

end SKConstants
