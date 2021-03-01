/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

/-
A toy Lempel-Ziv compressor and decompressor.
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
    | reg n s c => toString (s ++ [c])
    | last n s  => toString s

end LZBlock

/-- Segment the input string into LZ blocks -/
def toBlocks (curList : List (LZBlock α)) (curBlock : List α) : List α → List (LZBlock α)
| []        => curList ++ [last curList.length curBlock]
| (x :: xs) => let nextBlk := curBlock ++ [x]
    match curList.find? (fun blk => (blk.getStr == nextBlk)) with
    | none   => toBlocks (curList ++ [reg curList.length curBlock x]) [] xs
    | some b => toBlocks curList nextBlk xs

def getPrefixId (lst : List (LZBlock α)) (b : List α) : Nat :=
    let lstn := List.enum lst
    match lstn.find? (fun blk => blk.2.getStr == b) with
    | none => panic! "Help!"
    | some blk => blk.1

--inductive Bit
--| Zero
--| One
--
--open Bit
--
--instance : BEq Bit :=
--    ⟨fun a b => match a, b with
--    | Zero, Zero => true
--    | Zero, One  => false
--    | One, Zero  => false
--    | One, One   => true⟩
--
--instance : ToString Bit where
--    toString b := match b with
--    | Zero => "0"
--    | One => "1"
--
--def listBitToString : List Bit → String
--| []        => ""
--| (x :: xs) => (toString x) ++ (listBitToString xs)

def main : IO Unit :=
do let str := "aaaaaabbbbbbbbbbbb"
   IO.print $ "Voici une chaîne: " ++ str ++ "\n"
   let strLZ := toBlocks [mkEmpty] [] str.toList
   --IO.print $ List.map getPrefixId $ toBlocks [mkEmpty] [] str.toList
   IO.print "\n"
   IO.print strLZ

#eval main