-- $ chcp 65001
-- $ idris
-- > :l G1UpperProverNewyear
--
-- Idris の実行には Docker がおすすめ
--
module G1UpperProverNewyear

import G4LowerFormalPSpring
import G3MiddleFunctionsWinter

%default total


-- 46  p が見えるようにしてある
data IsProvable : Bool -> Nat -> Nat -> Type where
  Yes : (p ** True  = proves p x) -> IsProvable True  p x
  No  : (p ** False = proves p x) -> IsProvable False p x

postulate r : GNat -> GNat

namespace C
  contradiction : Type
  contradiction = Type --「形式的体系P は矛盾している」
  ωcontradiction : Type
  ωcontradiction = Type --「形式的体系P はω矛盾している」
postulate d4d5tod6 : (m : Nat) -> IsProvable True m (myNot (r m)) -> IsProvable True s (r s) -> C.contradiction
postulate a5       : (m : Nat) -> True = proves s (forall l.ｘ１ (r l.ｘ１)) -> IsProvable True m (myNot (r m))
postulate d1tod5   : IsProvable True s (forall l.ｘ１ (r l.ｘ１)) -> IsProvable True s (r s)
--
postulate e3e4toe5 : IsProvable True t (r t) -> IsProvable True t (myNot (forall l.ｘ１ (r l.ｘ１))) -> C.ωcontradiction
postulate b5       : (m : Nat) -> False = proves m (forall l.ｘ１ (r l.ｘ１)) -> IsProvable True m (r m)

-- answer1Plum : 無矛盾なら g を証明できない    g = forall l.ｘ１ (r l.ｘ１)
answer1Plum : Not C.contradiction -> Not (IsProvable True s (forall l.ｘ１ (r l.ｘ１)))
answer1Plum nCon d1 with (d1)
  | (Yes (s ** d2)) = nCon (d4d5tod6 s (a5 s d2) (d1tod5 d1))

-- answer2Peach : ω無矛盾なら myNot g を証明できない    Not IsProvable True = IsProvable False を使用
answer2Peach : IsProvable False t (forall l.ｘ１ (r l.ｘ１)) ->
  Not C.ωcontradiction -> Not (IsProvable True t (myNot (forall l.ｘ１ (r l.ｘ１))))
answer2Peach d7 nOmega e4 with (d7)
  | (No (t ** e1)) = nOmega (e3e4toe5 (b5 t e1) e4)



