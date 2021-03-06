module G3MiddleFunctionsWinter

import G4LowerFormalPSpring

%access public export
%default total


-- 【後から気づいた】形式的体系P の関数を使って実装する必要は無い、原始再帰的であれば良い
-- 本での「述語」は「特性関数（Bool値を返す）」にする
-- 10.8.2 整数論
-- 1
canDivide : GNat -> GNat -> Bool
canDivide x d = canDivide' x d x where
  canDivide' x d Z     = False
  canDivide' x d (S n) = if x == d * (S n) then True else canDivide' x d n
-- 2
isPrime : GNat -> Bool
isPrime Z         = False
isPrime (S Z)     = False
isPrime (S (S x)) = isPrime' (S (S x)) (S (S x)) where
  isPrime' x Z     = True
  isPrime' x (S d) = if not ((S d) == 1) && not ((S d) == x) && canDivide x (S d) then False else isPrime' x d
-- 3
prime : GNat -> GNat -> GNat
prime Z     _ = 0
prime (S n) x = prime' n x Z x where
  prime' _ _ _ Z           = 0
  prime' n x p (S stopper) = if p == x + 1 then 0 else if prime n x < p && canDivide x p && isPrime p then p else prime' n x (S p) stopper
-- 4
factorial : GNat -> GNat
factorial Z     = 1
factorial (S n) = (S n) * factorial n
-- 5
pri : GNat -> GNat
pri Z     = 0
pri (S n) = pri' n Z ((factorial $ pri n) + 1 + 1) where
  pri' _ _  Z           = 0
  pri' n pp (S stopper) = if pri n < pp && isPrime pp then pp else pri' n (S pp) stopper 
-- 10.8.3 列
-- 6
elem : GNat -> GNat -> GNat
elem x n = elem' x n Z (x + 1) where
  elem' _ _ _ Z           = 0
  elem' x n k (S stopper) = if canDivideByPower x n k && canDivideByPower x n (S k) then k else elem' x n (S k) stopper where
    canDivideByPower x n k  = canDivide x $ power (prime n x) k
-- 7
len : GNat -> GNat
len x = len' x Z (x + 1) where
  len' _ _ Z           = 0
  len' x k (S stopper) = if 0 < prime k x && 0 == prime (k + 1) x then k else len' x (S k) stopper
-- 8
comb : GNat -> GNat -> GNat
comb x y = comb' x y Z (m8 x y + 1) where
  m8 : GNat -> GNat -> GNat
  m8 x y = power (pri (len x + len y)) (plus x y)
  comb' : GNat -> GNat -> GNat -> GNat -> GNat
  comb' _ _ _ Z           = 0
  comb' x y z (S stopper) =
    if combSub1 Z (len x + 1) /= 0 then 
      if combSub2 Z (len y + 1) /= 0 then z else comb' x y (S z) stopper
    else comb' x y (S z) stopper where
      combSub1 _ Z           = 0
      combSub1 m (S stopper) = if m < len x + 1 && 0 < m && elem z m == elem x m then 1 else combSub1 (S m) stopper
      combSub2 _ Z           = 0
      combSub2 n (S stopper) = if n < len y + 1 && 0 < n && elem z (len x + n) == elem y n then 1 else combSub2 (S n) stopper
-- 9
seq : GNat -> GNat
seq = power 2 
-- 10
paren : GNat -> GNat
paren x = seq 左かっこ * x * seq 右かっこ
-- 10.8.4 変数・記号・論理式



