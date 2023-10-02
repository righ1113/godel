module G4LowerFormalPSpring

%access public export
%default total


-- 形式的体系P
-- 数項化された自然数
GNat : Type
GNat = Nat

-- 10.6.1 基本記号のゲーデル数
Ｏ : GNat
Ｏ = 1
ｆ : GNat
ｆ = 3
否定 : GNat
否定 = 5
または : GNat
または = 7
全ての : GNat
全ての = 9
左かっこ : GNat
左かっこ = 11
右かっこ : GNat
右かっこ = 13

-- 10.4.4 公理
-- 公理 I-1~3 に対応するゲーデル数
postulate α１ : GNat
postulate α２ : GNat
postulate α３ : GNat

namespace l
  ｘ１ : GNat
  ｘ１ = 17

-- Q(x, y) に表現定理を適用すると、形式的体系P に q が存在する事が保証される
postulate q : GNat -> GNat -> GNat



