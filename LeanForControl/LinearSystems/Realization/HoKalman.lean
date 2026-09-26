import LeanForControl.LinearSystems.Realization.FiniteDetermination
import Mathlib.LinearAlgebra.Isomorphisms
import Architect

/-!
# Finite Ho-Kalman realization from compatible Hankel data

The state space is the range of a finite block Hankel map. Explicit kernel and
range compatibility let the one-step shift descend to this range. The first
column and row yield input and output maps; repeated shifts recover the
specified finite Markov window. The state dimension equals Hankel rank.

Reference: Ho and Kalman, "Effective construction of linear state-variable
models from input/output functions" (1966).
-/

namespace LinearSystems

open Matrix

namespace Realization

variable {𝕜 : Type*} [Field 𝕜]
variable {m p r s : ℕ}

/-- The finite block Hankel matrix built from supplied Markov blocks, with an
explicit shift in the sequence index.

Reference: Ho and Kalman (1966). -/
def shiftedHankel (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s shift : ℕ) :
    Matrix (Fin r × Fin p) (Fin s × Fin m) 𝕜 :=
  Matrix.of fun ia jb => M (shift + (ia.1 : ℕ) + (jb.1 : ℕ)) ia.2 jb.2

/-- Compatibility conditions ensuring that the shifted Hankel map induces a
well-defined endomorphism of the unshifted Hankel range.

The kernel inclusion gives independence from the chosen input-history
representative.  The range inclusion makes the shifted image a state again.

Reference: Ho and Kalman (1966). -/
structure HankelShiftCompatible
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ) : Prop where
  /-- Null histories for the unshifted Hankel matrix remain null after one
  shift. -/
  ker_le :
    LinearMap.ker (shiftedHankel M r s 0).mulVecLin ≤
      LinearMap.ker (shiftedHankel M r s 1).mulVecLin
  /-- Every shifted output history belongs to the unshifted Hankel range. -/
  range_le :
    LinearMap.range (shiftedHankel M r s 1).mulVecLin ≤
      LinearMap.range (shiftedHankel M r s 0).mulVecLin

/-- Identically zero Markov blocks satisfy the finite Hankel shift
compatibility conditions at every pair of horizons.

Original: rank-zero edge-case infrastructure for LeanForControl. -/
theorem zeroHankelShiftCompatible (r s : ℕ) :
    HankelShiftCompatible
      (fun _ => (0 : Matrix (Fin p) (Fin m) 𝕜)) r s where
  ker_le := by
    intro u _
    rw [LinearMap.mem_ker]
    ext ia
    simp [shiftedHankel, Matrix.mulVec]
  range_le := by
    rintro y ⟨u, rfl⟩
    refine ⟨0, ?_⟩
    ext ia
    simp [shiftedHankel, Matrix.mulVec]

/-- The canonical finite Ho–Kalman state space: the range of the unshifted
Hankel map.

Reference: Ho and Kalman (1966). -/
def hankelStateSpace (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) :=
  LinearMap.range (shiftedHankel M r s 0).mulVecLin

/-- The shifted Hankel map, with codomain restricted to the canonical state
space using range compatibility.

Original: finite Ho–Kalman infrastructure for LeanForControl. -/
def hankelShiftToState (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s) :
    (Fin s × Fin m → 𝕜) →ₗ[𝕜] hankelStateSpace M r s :=
  (shiftedHankel M r s 1).mulVecLin.codRestrict
    (hankelStateSpace M r s) fun u =>
      h.range_le ⟨u, rfl⟩

/-- The shifted Hankel map descends through the quotient by the unshifted
Hankel kernel.

This is the central well-definedness step of the finite Ho–Kalman
construction.

Reference: Ho and Kalman (1966). -/
def hankelShiftQuotientMap (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s) :
    ((Fin s × Fin m → 𝕜) ⧸
        LinearMap.ker (shiftedHankel M r s 0).mulVecLin) →ₗ[𝕜]
      hankelStateSpace M r s :=
  (LinearMap.ker (shiftedHankel M r s 0).mulVecLin).liftQ
    (hankelShiftToState M r s h) (by
      intro u hu
      rw [LinearMap.mem_ker] at hu ⊢
      apply Subtype.ext
      exact LinearMap.mem_ker.mp
        (h.ker_le (LinearMap.mem_ker.mpr hu)))

/-- The canonical state transition on the finite Hankel range.

Reference: Ho and Kalman (1966). -/
noncomputable def hankelStateMap
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s) :
    hankelStateSpace M r s →ₗ[𝕜] hankelStateSpace M r s :=
  (hankelShiftQuotientMap M r s h).comp
    (shiftedHankel M r s 0).mulVecLin.quotKerEquivRange.symm.toLinearMap

/-- On a state represented by an input history, the canonical state map is
exactly one Hankel shift.

Reference: Ho and Kalman (1966). -/
theorem hankelStateMap_apply_image
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s)
    (u : Fin s × Fin m → 𝕜) :
    hankelStateMap M r s h
        ⟨(shiftedHankel M r s 0).mulVecLin u, ⟨u, rfl⟩⟩ =
      ⟨(shiftedHankel M r s 1).mulVecLin u, h.range_le ⟨u, rfl⟩⟩ := by
  let y : LinearMap.range (shiftedHankel M r s 0).mulVecLin :=
    ⟨(shiftedHankel M r s 0).mulVecLin u, ⟨u, rfl⟩⟩
  change hankelStateMap M r s h y = _
  rw [hankelStateMap, LinearMap.comp_apply]
  have hrepr :
      (shiftedHankel M r s 0).mulVecLin.quotKerEquivRange.symm.toLinearMap
          y =
        (LinearMap.ker (shiftedHankel M r s 0).mulVecLin).mkQ u :=
    by
      dsimp [y]
      exact
        LinearMap.quotKerEquivRange_symm_apply_image
          (shiftedHankel M r s 0).mulVecLin u ⟨u, rfl⟩
  calc
    (hankelShiftQuotientMap M r s h)
        ((shiftedHankel M r s 0).mulVecLin.quotKerEquivRange.symm.toLinearMap
          y) =
        (hankelShiftQuotientMap M r s h)
          ((LinearMap.ker
            (shiftedHankel M r s 0).mulVecLin).mkQ u) :=
      congrArg (hankelShiftQuotientMap M r s h) hrepr
    _ = _ := rfl

/-! ## Block-column generators and input/output maps -/

/-- Embed an input vector as a history supported in one block column.

Original: finite-history plumbing for LeanForControl. -/
def hankelColumnHistory (s : ℕ) (j : Fin s) :
    (Fin m → 𝕜) →ₗ[𝕜] (Fin s × Fin m → 𝕜) where
  toFun u jb := if jb.1 = j then u jb.2 else 0
  map_add' u v := by
    ext jb
    by_cases hj : jb.1 = j <;> simp [hj]
  map_smul' a u := by
    ext jb
    by_cases hj : jb.1 = j <;> simp [hj]

/-- Multiplying a shifted block Hankel matrix by a single block-column
history extracts the corresponding block column.

Original: block-matrix plumbing for LeanForControl. -/
theorem shiftedHankel_mulVec_hankelColumnHistory
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s shift : ℕ) (j : Fin s) (u : Fin m → 𝕜) :
    (shiftedHankel M r s shift).mulVec
        (hankelColumnHistory s j u) =
      fun ia => (M (shift + (ia.1 : ℕ) + (j : ℕ))).mulVec u ia.2 := by
  ext ia
  change
    (∑ jb : Fin s × Fin m,
      M (shift + (ia.1 : ℕ) + (jb.1 : ℕ)) ia.2 jb.2 *
        (if jb.1 = j then u jb.2 else 0)) =
      ∑ b : Fin m, M (shift + (ia.1 : ℕ) + (j : ℕ)) ia.2 b * u b
  rw [Fintype.sum_prod_type]
  simp

/-- The state represented by one block column of the unshifted Hankel
matrix.

Original: canonical generator for LeanForControl's Ho–Kalman construction. -/
def hankelColumnState
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ)
    (j : Fin s) (u : Fin m → 𝕜) : hankelStateSpace M r s :=
  ⟨(shiftedHankel M r s 0).mulVecLin (hankelColumnHistory s j u),
    ⟨hankelColumnHistory s j u, rfl⟩⟩

/-- The induced Hankel state map sends each available block-column generator
to the next one.

Reference: Ho and Kalman (1966). -/
theorem hankelStateMap_apply_hankelColumnState
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s)
    (k : ℕ) (hk : k + 1 < s) (u : Fin m → 𝕜) :
    hankelStateMap M r s h
        (hankelColumnState M r s ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩ u) =
      hankelColumnState M r s ⟨k + 1, hk⟩ u := by
  change
    hankelStateMap M r s h
        ⟨(shiftedHankel M r s 0).mulVecLin
            (hankelColumnHistory s ⟨k, _⟩ u), ⟨_, rfl⟩⟩ = _
  rw [hankelStateMap_apply_image]
  apply Subtype.ext
  change
    (shiftedHankel M r s 1).mulVec
        (hankelColumnHistory s ⟨k, _⟩ u) =
      (shiftedHankel M r s 0).mulVec
        (hankelColumnHistory s ⟨k + 1, hk⟩ u)
  rw [shiftedHankel_mulVec_hankelColumnHistory,
      shiftedHankel_mulVec_hankelColumnHistory]
  ext ia
  dsimp only
  congr 2
  omega

/-- The canonical Ho–Kalman input map: an input is sent to the first block
column of the Hankel range.

Reference: Ho and Kalman (1966). -/
def hankelInputMap
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ) (hs : 0 < s) :
    (Fin m → 𝕜) →ₗ[𝕜] hankelStateSpace M r s :=
  ((shiftedHankel M r s 0).mulVecLin.codRestrict
    (hankelStateSpace M r s) fun u => ⟨u, rfl⟩).comp
      (hankelColumnHistory s ⟨0, hs⟩)

/-- The input map is the zeroth block-column generator.

Original: input-generator API for LeanForControl. -/
theorem hankelInputMap_apply
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ)
    (hs : 0 < s) (u : Fin m → 𝕜) :
    hankelInputMap M r s hs u = hankelColumnState M r s ⟨0, hs⟩ u :=
  rfl

/-- Read one output block from a vector in the finite Hankel output-history
space.

Original: output-history projection for LeanForControl. -/
def hankelOutputBlock (r : ℕ) (i : Fin r) :
    (Fin r × Fin p → 𝕜) →ₗ[𝕜] (Fin p → 𝕜) where
  toFun y a := y (i, a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical Ho–Kalman output map reads the first output block of a
Hankel-range state.

Reference: Ho and Kalman (1966). -/
def hankelOutputMap
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ) (hr : 0 < r) :
    hankelStateSpace M r s →ₗ[𝕜] (Fin p → 𝕜) :=
  (hankelOutputBlock r ⟨0, hr⟩).comp
    (hankelStateSpace M r s).subtype

/-- The output map applied to a block-column generator is the corresponding
Markov block applied to the input.

Reference: Ho and Kalman (1966). -/
theorem hankelOutputMap_apply_hankelColumnState
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ)
    (hr : 0 < r) (j : Fin s) (u : Fin m → 𝕜) :
    hankelOutputMap M r s hr (hankelColumnState M r s j u) =
      (M j).mulVec u := by
  ext a
  simp [hankelOutputMap, hankelOutputBlock, hankelColumnState,
    shiftedHankel_mulVec_hankelColumnHistory]

/-- Repeated application of the induced state shift sends the input generator
to the corresponding available block-column generator.

Reference: Ho and Kalman (1966). -/
theorem hankelStateMap_pow_apply_hankelInputMap
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s)
    (hs : 0 < s) (k : ℕ) (hk : k < s) (u : Fin m → 𝕜) :
    ((hankelStateMap M r s h) ^ k) (hankelInputMap M r s hs u) =
      hankelColumnState M r s ⟨k, hk⟩ u := by
  induction k with
  | zero =>
      simpa only [pow_zero, one_apply] using
        hankelInputMap_apply M r s hs u
  | succ k ih =>
      have hk' : k < s := Nat.lt_trans (Nat.lt_succ_self k) hk
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply, ih hk']
      exact hankelStateMap_apply_hankelColumnState M r s h k hk u

/-- Basis-free finite Ho–Kalman recovery: the abstract input, state, and
output maps reproduce every supplied Markov block whose column generator is
present in the finite Hankel window.

Reference: Ho and Kalman (1966). -/
@[blueprint "thm:finite-ho-kalman-markov-recovery-linear"
  (statement := /-- For every column index $k<s$, the canonical finite
    Hankel range construction satisfies $C_H A_H^k B_H=M_k$ as a linear-map
    identity. -/)]
theorem hankelOutput_statePow_input
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s)
    (hr : 0 < r) (hs : 0 < s) (k : ℕ) (hk : k < s)
    (u : Fin m → 𝕜) :
    hankelOutputMap M r s hr
        (((hankelStateMap M r s h) ^ k) (hankelInputMap M r s hs u)) =
      (M k).mulVec u := by
  rw [hankelStateMap_pow_apply_hankelInputMap M r s h hs k hk u,
    hankelOutputMap_apply_hankelColumnState]

/-- Linear-map form of finite Ho–Kalman Markov recovery.

Reference: Ho and Kalman (1966). -/
theorem hankelOutput_comp_statePow_comp_input
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s)
    (hr : 0 < r) (hs : 0 < s) (k : ℕ) (hk : k < s) :
    (hankelOutputMap M r s hr).comp
        (((hankelStateMap M r s h) ^ k).comp
          (hankelInputMap M r s hs)) =
      (M k).mulVecLin := by
  apply LinearMap.ext
  intro u
  apply funext
  intro a
  exact congrFun (hankelOutput_statePow_input M r s h hr hs k hk u) a

/-- A finite basis of the canonical Hankel state space.

Original: coordinate infrastructure for LeanForControl. -/
noncomputable def hankelStateBasis
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ) :=
  Module.finBasis 𝕜 (hankelStateSpace M r s)

/-- The matrix of the canonical finite Hankel shift in range coordinates.

Reference: Ho and Kalman (1966). -/
noncomputable def hankelStateMatrix
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s) :
    Matrix (Fin (Module.finrank 𝕜 (hankelStateSpace M r s)))
      (Fin (Module.finrank 𝕜 (hankelStateSpace M r s))) 𝕜 :=
  LinearMap.toMatrix (hankelStateBasis M r s) (hankelStateBasis M r s)
    (hankelStateMap M r s h)

/-- The matrix of the canonical finite Hankel input map in range coordinates.

Reference: Ho and Kalman (1966). -/
noncomputable def hankelInputMatrix
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (hs : 0 < s) :
    Matrix (Fin (Module.finrank 𝕜 (hankelStateSpace M r s))) (Fin m) 𝕜 :=
  LinearMap.toMatrix (Pi.basisFun 𝕜 (Fin m)) (hankelStateBasis M r s)
    (hankelInputMap M r s hs)

/-- The matrix of the canonical finite Hankel output map in range coordinates.

Reference: Ho and Kalman (1966). -/
noncomputable def hankelOutputMatrix
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (hr : 0 < r) :
    Matrix (Fin p) (Fin (Module.finrank 𝕜 (hankelStateSpace M r s))) 𝕜 :=
  LinearMap.toMatrix (hankelStateBasis M r s) (Pi.basisFun 𝕜 (Fin p))
    (hankelOutputMap M r s hr)

/-- The finite Ho–Kalman realization in coordinates of the canonical Hankel
range basis.  The feedthrough matrix is supplied separately from the
state-mediated Markov blocks.

Reference: Ho and Kalman (1966). -/
noncomputable def hoKalmanRealization
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (D : Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s)
    (hr : 0 < r) (hs : 0 < s) :
    Realization 𝕜 (Module.finrank 𝕜 (hankelStateSpace M r s)) m p where
  A := hankelStateMatrix M r s h
  B := hankelInputMatrix M r s hs
  C := hankelOutputMatrix M r s hr
  D := D

/-- The coordinate state matrix acts exactly as the abstract induced Hankel
state map.

Original: coordinate infrastructure for LeanForControl. -/
theorem hankelStateMatrix_mulVec_coordinates
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s)
    (x : hankelStateSpace M r s) :
    hankelStateMatrix M r s h *ᵥ (hankelStateBasis M r s).equivFun x =
      (hankelStateBasis M r s).equivFun (hankelStateMap M r s h x) := by
  simpa [hankelStateMatrix, Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (hankelStateBasis M r s)
      (hankelStateBasis M r s) (hankelStateMap M r s h) x

/-- The coordinate input matrix acts exactly as the abstract first-column
input map.

Original: coordinate infrastructure for LeanForControl. -/
theorem hankelInputMatrix_mulVec_coordinates
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (hs : 0 < s) (u : Fin m → 𝕜) :
    hankelInputMatrix M r s hs *ᵥ u =
      (hankelStateBasis M r s).equivFun (hankelInputMap M r s hs u) := by
  simpa [hankelInputMatrix, Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (Pi.basisFun 𝕜 (Fin m))
      (hankelStateBasis M r s) (hankelInputMap M r s hs) u

/-- The coordinate output matrix acts exactly as the abstract first-row
output map.

Original: coordinate infrastructure for LeanForControl. -/
theorem hankelOutputMatrix_mulVec_coordinates
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (hr : 0 < r) (x : hankelStateSpace M r s) :
    hankelOutputMatrix M r s hr *ᵥ (hankelStateBasis M r s).equivFun x =
      hankelOutputMap M r s hr x := by
  simpa [hankelOutputMatrix, Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (hankelStateBasis M r s)
      (Pi.basisFun 𝕜 (Fin p)) (hankelOutputMap M r s hr) x

/-- Powers of the coordinate state matrix act as powers of the abstract
induced Hankel state map.

Original: coordinate infrastructure for LeanForControl. -/
theorem hankelStateMatrix_pow_mulVec_coordinates
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s) (k : ℕ)
    (x : hankelStateSpace M r s) :
    (hankelStateMatrix M r s h ^ k) *ᵥ
        (hankelStateBasis M r s).equivFun x =
      (hankelStateBasis M r s).equivFun
        (((hankelStateMap M r s h) ^ k) x) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih,
        hankelStateMatrix_mulVec_coordinates, pow_succ', Module.End.mul_apply]

/-- The bundled finite Ho–Kalman realization recovers every supplied Markov
block in its valid column window.

Reference: Ho and Kalman (1966). -/
@[blueprint "thm:finite-ho-kalman-markov-recovery"
  (statement := /-- The finite Ho--Kalman realization satisfies
    $C_HA_H^kB_H=M_k$ for every $k<s$. -/)]
theorem hoKalmanRealization_markovParameter_eq
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (D : Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s)
    (hr : 0 < r) (hs : 0 < s) (k : ℕ) (hk : k < s) :
    (hoKalmanRealization M D r s h hr hs).markovParameter k = M k := by
  rw [Matrix.ext_iff_mulVec]
  intro u
  change
    (hankelOutputMatrix M r s hr * hankelStateMatrix M r s h ^ k *
        hankelInputMatrix M r s hs) *ᵥ u = M k *ᵥ u
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hankelInputMatrix_mulVec_coordinates,
    hankelStateMatrix_pow_mulVec_coordinates,
    hankelOutputMatrix_mulVec_coordinates]
  exact hankelOutput_statePow_input M r s h hr hs k hk u

/-- The dimension of the canonical finite Ho–Kalman state space is the rank
of the unshifted Hankel matrix.

Reference: Ho and Kalman (1966). -/
theorem hankelStateSpace_finrank_eq_rank
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ) :
    Module.finrank 𝕜 (hankelStateSpace M r s) =
      Matrix.rank (shiftedHankel M r s 0) :=
  rfl

/-- The bundled finite Ho–Kalman realization has state dimension equal to
the rank of the unshifted finite Hankel matrix.

Reference: Ho and Kalman (1966). -/
theorem hoKalmanRealization_stateDim_eq_rank
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ) :
    Module.finrank 𝕜 (hankelStateSpace M r s) =
      Matrix.rank (shiftedHankel M r s 0) :=
  hankelStateSpace_finrank_eq_rank M r s


end Realization

end LinearSystems
