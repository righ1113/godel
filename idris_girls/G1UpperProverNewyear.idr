-- $ chcp 65001
-- $ idris
-- > :l G1UpperProverNewyear
module G1UpperProverNewyear

import G4LowerFormalPSpring
import G3MiddleFunctionsWinter
import G2Postulate

%default total


gx1 : GNat
gx1 = 17

-- 46
data IsProvable : GNat -> Type where
  Yes : (p ** True = proves p x) -> IsProvable x

postulate p315 : (c, d : GNat) -> True = proves c (forall d (r d)) -> IsProvable (r c)

||| Double negation elimination
--DNE : Type -> Type
--DNE p = Not $ Not p -> p
-- 二重否定除去
postulate dne : ((a -> Void) -> Void) -> a 
dne2 : a -> ((a -> Void) -> Void) 
dne2 x f = f x

||| The converse of contraposition: (p -> q) -> Not q -> Not p
Transposition : Type -> Type -> Type
Transposition p q = (Not q -> Not p) -> p -> q

-- E1
fuga2 : Transposition ((Not . IsProvable) 17) ((t:GNat) -> False = proves t 17)
fuga2 prf p = let ans1 = flip prf p in let ans2 = dne ans1 in ans2
fuga4 : (((t : Nat) -> False = proves t 17) -> Void) -> IsProvable 17
fuga3 : (((t : Nat) -> False = proves t 17) -> Void) -> (IsProvable 17 -> Void) -> Void
fuga3 = dne2 . fuga4
fuga5 : (IsProvable 17 -> Void) -> (t : Nat) -> False = proves t 17
fuga5 = fuga2 fuga3



hoge : IsProvable (forall 17 (r 17)) -> GNat
hoge (Yes dep) -- = ?rhs1
  = let s = fst dep in let prf = snd dep in
    let d5 = p315 s gx1 prf in ?rhs1



namespace a
  -- 46_2
  data IsProvable2 : Bool -> GNat -> Type where
    Yes : (p ** True = proves p x) -> IsProvable2 True x
    No : ((t : GNat) -> False = proves t x) -> IsProvable2 False x

  huga : IsProvable2 True (forall 17 (r 17)) -> GNat
  huga (Yes dep) = 3







