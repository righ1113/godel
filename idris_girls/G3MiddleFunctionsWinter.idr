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
p : GNat -> GNat
p Z     = 0
p (S n) = p' n Z ((factorial $ p n) + 1 + 1) where
  p' _ _  Z           = 0
  p' n pp (S stopper) = if p n < pp && isPrime pp then pp else p' n (S pp) stopper 
-- 10.8.3 列
-- 6
elem : GNat -> GNat -> GNat
elem x n = elem' x n Z (x + 1) where
  elem' _ _ _ Z           = 0
  elem' x n k (S stopper) = if canDivideByPower x n k && canDivideByPower x n (S k) then k else elem' x n (S k) stopper where
    canDivideByPower x n k  = canDivide x $ power (prime n x) k



