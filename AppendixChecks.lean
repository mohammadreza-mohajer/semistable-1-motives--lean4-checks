import Std

/-!
# Semistable appendix: selected algebraic formalizations

Run with Lean 4.19.0. The accompanying lean_output.txt and lean_run_status.json
record the compiler result and the dependency reports for these nine declarations.

Scope:
* The formal algebra of the reduced differential, under explicit hypotheses.
* The scalar 2-by-2 block trace identity over the integers.
* The concrete eight projective/trace-zero matrices in the rank-three example.
* Their pairing matrix and the integral self-pairing Gram determinant.
* The point count of y^2 = x^3 + x + 1 over F_5.

This does not formalize period rings, semistable comparison, local Tate duality,
the full monodromy theorem, convergence, or the Iwasawa comparison. The code
models precisely the algebraic identities stated below. There are no additional
imports beyond the standard Lean distribution.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace SemistableAppendix

/-! ## Reduced differentials

Only the operations and hypotheses used by the cancellation are included.
For the mixed reduced complex, use R, sigma on Y and T, and the Hodge map.
For the unreduced semistable complex, the same algebraic template has
R = N, sigmaY = phi and sigmaT = p phi. Instantiating those objects in a
theory of semistable periods is outside this file.
-/

structure ReducedData (Y T H : Type) where
  zeroT : T
  subY : Y -> Y -> Y
  subT : T -> T -> T
  R : Y -> T
  sigmaY : Y -> Y
  sigmaT : T -> T
  hodge : Y -> H
  sub_self : forall t : T, subT t t = zeroT
  map_sub : forall x y : Y, R (subY x y) = subT (R x) (R y)
  commutes : forall y : Y, R (sigmaY y) = sigmaT (R y)

def deltaZero {Y T H : Type} (d : ReducedData Y T H) (y : Y) : Y × T × H :=
  (d.subY y (d.sigmaY y), d.R y, d.hodge y)

def deltaOne {Y T H : Type} (d : ReducedData Y T H) (x : Y × T × H) : T :=
  d.subT (d.R x.1) (d.subT x.2.1 (d.sigmaT x.2.1))

theorem reduced_differential_square_zero
    {Y T H : Type} (d : ReducedData Y T H) (y : Y) :
    deltaOne d (deltaZero d y) = d.zeroT := by
  change d.subT (d.R (d.subY y (d.sigmaY y)))
    (d.subT (d.R y) (d.sigmaT (d.R y))) = d.zeroT
  rw [d.map_sub, d.commutes, d.sub_self]

/-! ## Scalar block trace

This is the block trace formula with one-dimensional lower blocks. It is
an identity for arbitrary integer entries, not a sample evaluation.
-/

abbrev M2 := Fin 2 -> Fin 2 -> Int

def mul2 (A B : M2) : M2 :=
  fun i j => A i 0 * B 0 j + A i 1 * B 1 j

def trace2 (A : M2) : Int := A 0 0 + A 1 1

def blockA2 (alpha u d : Int) : M2 :=
  fun i j =>
    if i.val = 0 then (if j.val = 0 then 0 else alpha)
    else (if j.val = 0 then u else d)

def blockB2 (beta v e : Int) : M2 :=
  fun i j =>
    if i.val = 0 then (if j.val = 0 then -e else beta)
    else (if j.val = 0 then v else e)

theorem scalar_block_trace (alpha u d beta v e : Int) :
    trace2 (mul2 (blockB2 beta v e) (blockA2 alpha u d)) =
      alpha * v + beta * u + e * d := by
  change ((-e) * 0 + beta * u) + (v * alpha + e * d) =
    (alpha * v + beta * u) + e * d
  rw [Int.mul_zero, Int.zero_add, Int.mul_comm v alpha]
  rw [← Int.add_assoc]
  rw [Int.add_comm (beta * u) (alpha * v)]

/-! ## The rank-three matrices

The matrices have integer entries. The projective representatives are six
off-diagonal units, E_00, E_11. Their proposed duals are the transposed units,
E_00-E_22, E_11-E_22. This file verifies their pairings. The identification
with arithmetic cohomology lattices is not a theorem of this file.
-/

abbrev M3 := Fin 3 -> Fin 3 -> Int

def unit3 (a b : Fin 3) : M3 :=
  fun i j => if i = a ∧ j = b then 1 else 0

def sub3 (A B : M3) : M3 := fun i j => A i j - B i j

def mul3 (A B : M3) : M3 :=
  fun i j => A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j

def trace3 (A : M3) : Int := A 0 0 + A 1 1 + A 2 2

def primalByNat (k : Nat) : M3 :=
  match k with
  | 0 => unit3 0 1
  | 1 => unit3 0 2
  | 2 => unit3 1 0
  | 3 => unit3 1 2
  | 4 => unit3 2 0
  | 5 => unit3 2 1
  | 6 => unit3 0 0
  | _ => unit3 1 1

def dualByNat (k : Nat) : M3 :=
  match k with
  | 0 => unit3 1 0
  | 1 => unit3 2 0
  | 2 => unit3 0 1
  | 3 => unit3 2 1
  | 4 => unit3 0 2
  | 5 => unit3 1 2
  | 6 => sub3 (unit3 0 0) (unit3 2 2)
  | _ => sub3 (unit3 1 1) (unit3 2 2)

def primal (k : Fin 8) : M3 := primalByNat k.val
def dual (k : Fin 8) : M3 := dualByNat k.val

theorem concrete_dual_matrices_are_trace_zero :
    forall k : Fin 8, trace3 (dual k) = 0 := by
  decide

theorem concrete_projective_dual_pairing :
    forall i j : Fin 8,
      trace3 (mul3 (dual j) (primal i)) =
        (if i = j then (1 : Int) else 0) := by
  decide

def selfGram : List (List Int) :=
  (List.range 8).map (fun i =>
    (List.range 8).map (fun j => trace3 (mul3 (dualByNat i) (dualByNat j))))

def expectedSelfGram : List (List Int) :=
  [[0, 0, 1, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1, 0, 0],
   [0, 1, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 2, 1],
   [0, 0, 0, 0, 0, 0, 1, 2]]

theorem concrete_self_gram_matrix : selfGram = expectedSelfGram := by
  decide

/-! Cofactor expansion defines the determinant used in the concrete calculation.
The first argument is its matrix size. No general matrix determinant theorem
is asserted for malformed or nonsquare lists.
-/

def eraseColumn (j : Nat) (row : List Int) : List Int :=
  row.take j ++ row.drop (j + 1)

def laplaceSum (cofactor : Nat -> Int) : List Int -> Nat -> Int
  | [], _ => 0
  | a :: tail, j =>
      (if a = 0 then 0 else
        (if j % 2 = 0 then a else -a) * cofactor j) +
      laplaceSum cofactor tail (j + 1)

def laplaceDet : Nat -> List (List Int) -> Int
  | 0, _ => 1
  | n + 1, rows =>
      match rows with
      | [] => 0
      | row :: tail =>
          laplaceSum (fun j => laplaceDet n (tail.map (eraseColumn j))) row 0

theorem concrete_self_trace_determinant : laplaceDet 8 selfGram = -3 := by
  decide

/-! ## The elliptic example over F_5

Residues are represented by the natural numbers 0,...,4. The equation is
tested modulo 5, and the nonsingular Weierstrass model has one point at
infinity. Good reduction and ordinarity require the separate mathematical
arguments in the manuscript; only the count and the resulting trace are here.
-/

def affineCount5 : Nat :=
  (List.range 5).foldl (fun total x =>
    total + (List.range 5).foldl (fun count y =>
      if (y * y) % 5 = (x * x * x + x + 1) % 5
      then count + 1 else count) 0) 0

def projectiveCount5 : Nat := affineCount5 + 1

theorem elliptic_affine_point_count : affineCount5 = 8 := by
  decide

theorem elliptic_projective_point_count : projectiveCount5 = 9 := by
  decide

theorem elliptic_frobenius_trace : (5 : Int) + 1 - (9 : Int) = -3 := by
  decide

/-! Report the logical dependencies of each checked declaration. -/

#print axioms reduced_differential_square_zero
#print axioms scalar_block_trace
#print axioms concrete_dual_matrices_are_trace_zero
#print axioms concrete_projective_dual_pairing
#print axioms concrete_self_gram_matrix
#print axioms concrete_self_trace_determinant
#print axioms elliptic_affine_point_count
#print axioms elliptic_projective_point_count
#print axioms elliptic_frobenius_trace

end SemistableAppendix
