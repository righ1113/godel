module G3MiddleFunctionsWinter

import G4LowerFormalPSpring

%access public export
%default total


-- 【後から気づいた】形式的体系P の関数を使って実装する必要は無い、原始再帰的であれば良い
-- 本での「述語」は「特性関数（Bool値を返す）」にする
-- 10.8.2 整数論
-- 1
canDivide : Nat -> Nat -> Bool
canDivide x d = canDivide' x d x where
  canDivide' x d Z     = False
  canDivide' x d (S n) = if x == d * (S n) then True else canDivide' x d n
-- 2
isPrime : Nat -> Bool
isPrime Z         = False
isPrime (S Z)     = False
isPrime (S (S x)) = isPrime' (S (S x)) (S (S x)) where
  isPrime' x Z     = True
  isPrime' x (S d) = if not ((S d) == 1) && not ((S d) == x) && canDivide x (S d) then False else isPrime' x d
-- 3
prime : Nat -> Nat -> Nat
prime Z     _ = 0
prime (S n) x = prime' n x Z x where
  prime' _ _ _ Z           = 0
  prime' n x p (S stopper) = if p == x + 1 then 0 else if prime n x < p && canDivide x p && isPrime p then p else prime' n x (S p) stopper
-- 4
factorial : Nat -> Nat
factorial Z     = 1
factorial (S n) = (S n) * factorial n
-- 5
pri : Nat -> Nat
pri Z     = 0
pri (S n) = pri' n Z ((factorial $ pri n) + 1 + 1) where
  pri' _ _  Z           = 0
  pri' n pp (S stopper) = if pri n < pp && isPrime pp then pp else pri' n (S pp) stopper
-- 10.8.3 列
-- 6
elem : Nat -> Nat -> Nat
elem x n = elem' x n Z (x + 1) where
  elem' _ _ _ Z           = 0
  elem' x n k (S stopper) = if canDivideByPower x n k && canDivideByPower x n (S k) then k else elem' x n (S k) stopper where
    canDivideByPower x n k  = canDivide x $ power (prime n x) k
-- 7
len : Nat -> Nat
len x = len' x Z (x + 1) where
  len' _ _ Z           = 0
  len' x k (S stopper) = if 0 < prime k x && 0 == prime (k + 1) x then k else len' x (S k) stopper
-- 8
m8 : Nat -> Nat -> Nat
m8 x y = power (pri (len x + len y)) (plus x y)
comb : Nat -> Nat -> Nat
comb x y = comb' x y Z (m8 x y + 1) where
  comb' : Nat -> Nat -> Nat -> Nat -> Nat
  comb' _ _ _ Z           = 0
  comb' x y z (S stopper) =
    if combSub1 Z (len x + 1) /= 0 then
      if combSub2 Z (len y + 1) /= 0 then z else comb' x y (S z) stopper
    else comb' x y (S z) stopper where
      combSub1 _ Z           = 0
      combSub1 m (S stopper) = if m < len x + 1 && 0 < m && elem z m           == elem x m then 1 else combSub1 (S m) stopper
      combSub2 _ Z           = 0
      combSub2 n (S stopper) = if n < len y + 1 && 0 < n && elem z (len x + n) == elem y n then 1 else combSub2 (S n) stopper
-- 9
seq : Nat -> Nat
seq = power 2
-- 10
paren : Nat -> Nat
paren x = seq 左かっこ * x * seq 右かっこ
-- 10.8.4 変数・記号・論理式
-- 11
isVarType : Nat -> Nat -> Bool
isVarType x n = n >= 1 && isVarType' x x where
  isVarType' x Z     = False
  isVarType' x (S p) = if (isVarBase (S p)) && x == power (S p) n then True else isVarType' x p where
    isVarBase p = p > 右かっこ && isPrime p
-- 12
isVar : Nat -> Bool
isVar x = isVar' x x where
  isVar' x Z     = False
  isVar' x (S n) = isVarType x (S n)
-- 13[to use]
postulate not : Nat -> Nat -- not2 を上で使ったら落ちる
not2 : Nat -> Nat
not2 x = seq 否定 * paren x
-- 14
or : Nat -> Nat -> Nat
or x y = paren x * seq または * paren y
-- 15[to use]
postulate forall : Nat -> Nat -> Nat
forall2 : Nat -> Nat -> Nat
forall2 x a = seq 全ての * seq x * paren a
-- 16
succ : Nat -> Nat -> Nat
succ Z     x = x
succ (S n) x = seq ｆ * succ n x
-- 17
nBar : Nat -> Nat
nBar n = succ n $ seq Ｏ
-- 18
isNumberType : Nat -> Bool
isNumberType x = isNumberType' x x where
  isNumberType' x Z     = False
  isNumberType' x (S m) = isNumberType'' x (S m) x || isNumberType' x m where
    isNumberType'' x m Z     = False
    isNumberType'' x m (S n) = ((m == Ｏ || isVarType m 1) && x == succ n (seq m)) || isNumberType'' x m n
-- 19
isNthType : Nat -> Nat -> Bool
isNthType x n = n == 1 && isNumberType x || n > 1 && isNthType' x n x where
  isNthType' x n Z     = False
  isNthType' x n (S v) = isVarType (S v) n && x == seq (S v) || isNthType' x n v
-- 20
isElementForm : Nat -> Bool
isElementForm x = isElementForm' x x where
  isElementForm' x Z     = False
  isElementForm' x (S n) = isElementForm'' x (S n) x || isElementForm' x n where
    isElementForm'' x n Z     = False
    isElementForm'' x n (S b) = isElementForm''' x n (S b) x || isElementForm'' x n b where
      isElementForm''' x n b Z     = False
      isElementForm''' x n b (S a) = (isNthType (S a) (n + 1) && isNthType b n && x == (S a) * paren b)
        || isElementForm''' x n b a
-- 21
isOp : Nat -> Nat -> Nat -> Bool
isOp x a b = isNotOp x a || isOrOp x a b || isForallOp x a where
  isNotOp x a    = x == not a
  isOrOp x a b   = x == or a b
  isForallOp x a = isForallOp' x x a where
    isForallOp' x Z     a = False
    isForallOp' x (S v) a = isVar (S v) && x == forall (S v) a || isForallOp' x v a
-- 22
isFormSeq : Nat -> Bool
isFormSeq x = len x > 0 && isFormSeq' x (len x) where
  isFormSeq' x Z     = True
  isFormSeq' x (S n) = isElementForm (elem x n) || isFormSeq'' x (S n) n || isFormSeq' x n where
    isFormSeq'' x n Z     = False
    isFormSeq'' x n (S p) = isFormSeq''' x n (S p) (Nat.pred n) || isFormSeq'' x n p where
      isFormSeq''' x n p Z     = False
      isFormSeq''' x n p (S q) = isOp (elem x n) (elem x p) (elem x (S q)) || isFormSeq''' x n p q

-- 23
m23 : Nat -> Nat
m23 x = power (pri (power (len x) 2)) (x * (power (len x) 2))
isEndedWith : Nat -> Nat -> Bool
isEndedWith n x = n * elem n (len n) == x
isForm : Nat -> Bool
isForm x = isForm' x (m23 x) where
  isForm' x Z     = False
  isForm' x (S n) = isFormSeq (S n) && isEndedWith (S n) x || isForm' x n

-- 45[to use]
postulate proves : Nat -> Nat -> Bool



