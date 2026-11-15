import Hypertournaments.FiveConstrained.Catalogue
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic

/-!
# Executable one-point certificate test in the five-constrained ternary class

The class palette names five-vertex types. Its four-vertex palette is the
union of their actual four-supports. This is the normalized `≤ 5`-local
class, including carriers with fewer than five vertices.

All bits below are raw `Hyper.orient` values on increasing triples.
The base occupies `0,...,m-1`, followed by the two new vertices.
-/

namespace Hypertournaments.FiveConstrained

/-- An explicit one-point-versus-one-point diagram. -/
structure CertificateDiagram where
  baseSize : ℕ
  base : ℕ
  left : ℕ
  right : ℕ
  deriving DecidableEq, Repr

/-- The index of an increasing pair in lexicographic order. The identical
rank is used by the intrinsic mask presentation. -/
def certificatePairRank (n a b : ℕ) : ℕ :=
  ((List.range a).map (fun i => n - i - 1)).sum + (b - a - 1)

/-- The index of an increasing triple in lexicographic order. -/
def certificateTripleRank (n a b c : ℕ) : ℕ :=
  ((List.range a).map (fun i => (n - i - 1).choose 2)).sum +
    ((List.range (b - a - 1)).map (fun j => n - (a + 1 + j) - 1)).sum +
      (c - b - 1)

/-- Both local requirement masks of a finite structure. -/
structure CertificateRequirements where
  four : ℕ
  five : ℕ
  deriving DecidableEq, Repr

/-- The union of the side requirements and the mixed requirements for every
assignment. This is only finite data; `certificateProfile` computes it from
the actual orientation packets. -/
structure CertificateProfile where
  side : CertificateRequirements
  mixed : List CertificateRequirements
  deriving DecidableEq, Repr

/-- Increasing pairs on a finite ordinal. -/
def certificatePairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun a =>
    ((List.range n).filter fun b => a < b).map fun b => (a, b)

/-- Increasing triples on a finite ordinal. -/
def certificateTriples (n : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range n).flatMap fun a =>
    (List.range n).flatMap fun b =>
      ((List.range n).filter fun c => a < b ∧ b < c).map fun c => (a, b, c)

/-- Increasing four-subsets, represented by their increasing list. -/
def certificateFourSets (n : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range n).flatMap fun a =>
    (List.range n).flatMap fun b =>
      (List.range n).flatMap fun c =>
        ((List.range n).filter fun d => a < b ∧ b < c ∧ c < d).map
          fun d => (a, b, c, d)

/-- Increasing five-subsets. -/
def certificateFiveSets (n : ℕ) : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (List.range n).flatMap fun a =>
    (List.range n).flatMap fun b =>
      (List.range n).flatMap fun c =>
        (List.range n).flatMap fun d =>
          ((List.range n).filter fun e => a < b ∧ b < c ∧ c < d ∧ d < e).map
            fun e => (a, b, c, d, e)

/-- A lexicographic ten-bit five-packet. -/
def certificatePacket5 (a b c d e f g h i j : Bool) : ℕ :=
  a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat +
    16 * e.toNat + 32 * f.toNat + 64 * g.toNat +
      128 * h.toNat + 256 * i.toNat + 512 * j.toNat

/-- Four-type index from the four lexicographically ordered raw facets. -/
def certificateType4 (abc abd acd bcd : Bool) : ℕ :=
  let p := bcd.toNat + (!acd).toNat + abd.toNat + (!abc).toNat
  min p (4 - p)

/-- The prescribed orientation on an increasing triple in either side. -/
def CertificateDiagram.sideBit (d : CertificateDiagram) (rightSide : Bool)
    (a b c : ℕ) : Bool :=
  if c < d.baseSize then
    d.base.testBit (certificateTripleRank d.baseSize a b c)
  else
    (if rightSide then d.right else d.left).testBit
      (certificatePairRank d.baseSize a b)

/-- Five-packet induced on an increasing five-set of one side. -/
def certificateSidePacket5 (d : CertificateDiagram) (rightSide : Bool)
    (q : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ :=
  let (a, b, c, e, f) := q
  let s := d.sideBit rightSide
  certificatePacket5 (s a b c) (s a b e) (s a b f) (s a c e) (s a c f)
    (s a e f) (s b c e) (s b c f) (s b e f) (s c e f)

/-- Four-type induced on an increasing four-set of one side. -/
def certificateSideType4 (d : CertificateDiagram) (rightSide : Bool)
    (q : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  let (a, b, c, e) := q
  let s := d.sideBit rightSide
  certificateType4 (s a b c) (s a b e) (s a c e) (s b c e)

/-- Add one label to a requirement bit mask. -/
def certificateAddType (mask label : ℕ) : ℕ := mask ||| (2 ^ label)

/-- Requirements of both fully prescribed one-point sides. -/
def certificateSideRequirements (d : CertificateDiagram) : CertificateRequirements where
  four := [false, true].foldl (fun mask rightSide =>
    (certificateFourSets (d.baseSize + 1)).foldl
      (fun mask q => certificateAddType mask (certificateSideType4 d rightSide q)) mask) 0
  five := [false, true].foldl (fun mask rightSide =>
    (certificateFiveSets (d.baseSize + 1)).foldl
      (fun mask q => certificateAddType mask (type5 (certificateSidePacket5 d rightSide q)).val) mask) 0

/-- The literal ten-bit packet on `{a,b,c,left,right}`. -/
def certificateMixedPacket5 (d : CertificateDiagram) (x : ℕ)
    (a b c : ℕ) : ℕ :=
  certificatePacket5
    (d.base.testBit (certificateTripleRank d.baseSize a b c))
    (d.left.testBit (certificatePairRank d.baseSize a b))
    (d.right.testBit (certificatePairRank d.baseSize a b))
    (d.left.testBit (certificatePairRank d.baseSize a c))
    (d.right.testBit (certificatePairRank d.baseSize a c))
    (x.testBit a)
    (d.left.testBit (certificatePairRank d.baseSize b c))
    (d.right.testBit (certificatePairRank d.baseSize b c))
    (x.testBit b) (x.testBit c)

/-- The four-type on `{a,b,left,right}`. -/
def certificateMixedType4 (d : CertificateDiagram) (x a b : ℕ) : ℕ :=
  certificateType4 (d.left.testBit (certificatePairRank d.baseSize a b))
    (d.right.testBit (certificatePairRank d.baseSize a b)) (x.testBit a) (x.testBit b)

/-- Requirements only on the sets meeting both new points. All other sets
belong to one of the two sides. -/
def certificateMixedRequirements (d : CertificateDiagram) (x : ℕ) : CertificateRequirements where
  four := (certificatePairs d.baseSize).foldl
    (fun mask q => certificateAddType mask (certificateMixedType4 d x q.1 q.2)) 0
  five := (certificateTriples d.baseSize).foldl
    (fun mask q => certificateAddType mask
      (type5 (certificateMixedPacket5 d x q.1 q.2.1 q.2.2)).val) 0

/-- Compute the exact finite profile of an explicit diagram. -/
def certificateProfile (d : CertificateDiagram) : CertificateProfile where
  side := certificateSideRequirements d
  mixed := (List.range (2 ^ d.baseSize)).map (certificateMixedRequirements d)

/-- The normalized four-type palette, derived from the five-type palette. -/
def certificateSupport4 (palette : ℕ) : ℕ :=
  (List.finRange 12).foldl
    (fun mask t => if palette.testBit t.val then mask ||| support4 t else mask) 0

/-- Bitwise containment. -/
def certificateSubset (required allowed : ℕ) : Bool := (required &&& allowed) == required

/-- Actual local requirements are all allowed by the normalized palette. -/
def certificateAccepts (palette : ℕ) (r : CertificateRequirements) : Bool :=
  certificateSubset r.four (certificateSupport4 palette) &&
    certificateSubset r.five palette

/-- The finite profile obstruction: both sides are admitted, and no mixed
assignment is admitted. Unequal links are checked separately by
`certificateCheck`, because profiles alone omit that datum. -/
def certificateBlocks (palette : ℕ) (p : CertificateProfile) : Bool :=
  certificateAccepts palette p.side &&
    p.mixed.all (fun r => !(certificateAccepts palette r))

/-- Complete executable test, including the ordinary-AP identification case. -/
def certificateCheck (palette : ℕ) (d : CertificateDiagram) : Bool :=
  decide (d.left ≠ d.right) && certificateBlocks palette (certificateProfile d)

/-- The five surviving normalized palettes. -/
def certificatePositive (palette : ℕ) : Bool :=
  palette == 1 || palette == 119 || palette == 257 || palette == 3583 || palette == 4095

end Hypertournaments.FiveConstrained
