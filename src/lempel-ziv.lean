/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

/-
A toy Lempel-Ziv compressor and decompressor.
Only works for `List (Fin 2)`
-/

inductive LZBlock (α : Type u) [BEq α] where
| reg  : Nat → List α → α → LZBlock α    -- regular block
| last : Nat → List α → LZBlock α         -- last block (so no final character)

open LZBlock

variables {α : Type u} [BEq α]

namespace LZBlock

def getStr : LZBlock α → List α
| reg n s c  => s ++ [c]
| last n s   => s

def getId : LZBlock α → Nat
| reg n s c  => n
| last n s   => n

def getPrefix : LZBlock α → List α
| reg n s c => s
| last n s  => s

def mkEmpty : LZBlock α := last 0 []

instance [ToString α] : ToString (LZBlock α) where
    toString b := match b with
    | reg n s c => "R" ++ toString s ++ toString c
    | last n s  => "L" ++ toString s

end LZBlock

class HasBitstringRepr (α : Type u) where
    toBitstring : α → List (Fin 2)

def toBitstr [HasBitstringRepr α] (x : α) : List (Fin 2) :=
    HasBitstringRepr.toBitstring x

def toBitstrPr [HasBitstringRepr α] (x : α) (pr : Nat) : List (Fin 2) :=
    let xs := toBitstr x
    let s := List.replicate pr (0 : Fin 2) ++ xs
    List.drop (s.length - pr) s

partial def natToBitstring : Nat → List (Fin 2)
| 0                     => []
| 1                     => [1]
| Nat.succ (Nat.succ n) => let n' := n+2
    if n' % 2 = 1 then (natToBitstring (n'/2)) ++ [1] else (natToBitstring (n'/2)) ++ [0]

instance : HasBitstringRepr Bool where
    toBitstring := fun n => if n then [1] else [0]

instance : HasBitstringRepr Nat := ⟨natToBitstring⟩

instance {n : Nat} : HasBitstringRepr (Fin n) := ⟨natToBitstring ∘ Coe.coe⟩

instance : HasBitstringRepr Char := ⟨natToBitstring ∘ Char.toNat⟩

/-- Segment the input string into LZ blocks -/
def toBlocks (curList : List (LZBlock α)) (curBlock : List α) : List α → List (LZBlock α)
| []        => curList ++ [last curList.length curBlock]
| (x :: xs) => let nextBlk := curBlock ++ [x]
    match curList.find? (fun blk => (blk.getStr == nextBlk)) with
    | none   => toBlocks (curList ++ [reg curList.length curBlock x]) [] xs
    | some b => toBlocks curList nextBlk xs

def getPrefixId (lst : List (LZBlock α)) (b : LZBlock α) : Nat :=
    let lstn := List.enum lst
    match lstn.find? (fun blk => blk.2.getStr == b.getPrefix) with
    | none => panic! "Help!"
    | some blk => blk.1

def compressBlocks [HasBitstringRepr α] (s : List α) : List (List (Fin 2)) :=
    let blks := toBlocks [mkEmpty] [] s
    let ids := List.map (getPrefixId blks) blks
    let ids_enum := List.enum ids
    let f : LZBlock α → Nat × Nat → List (Fin 2)
    | last _ str,  (k₁, k₂)  => toBitstrPr k₂ (toBitstr (k₁ - 1)).length
    | reg _ str c,  (k₁, k₂) => (toBitstrPr k₂ (toBitstr (k₁ - 1)).length) ++ (toBitstrPr c 1)
    List.map₂ f blks ids_enum

def main : IO Unit :=
do let str := [0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1]
   let strLZ := toBlocks [mkEmpty] [] str
   IO.print strLZ
   IO.print "\n"
   IO.print $ List.map (getPrefixId strLZ) $ strLZ
   IO.print "\n"
   IO.print $ compressBlocks str
   IO.print "\n"
   IO.print $ toBitstr 0


#eval main