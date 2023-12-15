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
postulate myNot : Nat -> Nat -- myNot2 を上で使ったら落ちる
myNot2 : Nat -> Nat
myNot2 x = seq 否定 * paren x
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
  isNotOp x a    = x == myNot2 a
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
-- 24
isBoundAt : Nat -> Nat -> Nat -> Bool
isBoundAt v n x = isVar v && isForm x && isBoundAt' v n x x where
  isBoundAt' v n x Z     = False
  isBoundAt' v n x (S a) = isBoundAt'' v n x (S a) x || isBoundAt' v n x a where
    isBoundAt'' v n x a Z     = False
    isBoundAt'' v n x a (S b) = isBoundAt''' v n x a (S b) x || isBoundAt'' v n x a b where
      isBoundAt''' v n x a b Z     = False
      isBoundAt''' v n x a b (S c) = x == a * forall2 v b * (S c)
        && isForm b && len a + 1 <= n && n <= len a + len (forall2 v b)
          || isBoundAt''' v n x a b c
-- 25
isFreeAt : Nat -> Nat -> Nat -> Bool
isFreeAt v n x = isVar v && isForm x && v == elem x n && n <= len x && not (isBoundAt v n x)
-- 26
isFree : Nat -> Nat -> Bool
isFree v x = isFree' v x (len x) where
  isFree' v x Z     = False
  isFree' v x (S n) = isFreeAt v (S n) x || isFree' v x n
-- 27
substAtWith : Nat -> Nat -> Nat -> Nat
substAtWith x n c = substAtWith' x n c (m8 x c) (m8 x c) where
  substAtWith' x n c Z     stoc = stoc
  substAtWith' x n c (S z) stoc = substAtWith' x n c z (min (substAtWith'' x n c (S z) stoc x) stoc) where
    substAtWith'' x n c z stoc Z     = stoc
    substAtWith'' x n c z stoc (S a) = min (substAtWith''' x n c z stoc (S a) x) (substAtWith'' x n c z stoc a) where
      substAtWith''' x n c z stoc a Z = stoc
      substAtWith''' x n c z stoc a (S b) = substAtWith''' x n c z choice a b where
        choice = if z < stoc && n == len a + 1 && x == a * seq (elem x n) * (S b) && z == a * c * (S b) then z else stoc
-- 28
freepos : Nat -> Nat -> Nat -> Nat
freepos Z v x = freepos' v x (len x) (len x) where
  freepos' v x Z     stoc = stoc
  freepos' v x (S n) stoc = freepos' v x n choice where
    choice = if isFreeAt v n x && freeposB v x n (len x) then n else stoc where
      freeposB v x n Z     = False
      freeposB v x n (S p) = n >= (S p) || not (isFreeAt v (S p) x) || freeposB v x n p
freepos (S k) v x = freepos' v x (freepos k v x) (freepos k v x) where
  freepos' v x Z     stoc = stoc
  freepos' v x (S n) stoc = freepos' v x n choice where
    choice = if isFreeAt v n x && freeposB v x n (freepos k v x) then n else stoc where
      freeposB v x n Z     = False
      freeposB v x n (S p) = n >= (S p) || not (isFreeAt v (S p) x) || freeposB v x n p
-- 29
freenum : Nat -> Nat -> Nat
freenum v x = freenum' v x (len x) (len x) where
  freenum' v x Z stoc = stoc
  freenum' v x (S n) stoc = freenum' v x n choice where
    choice = if freepos (S n) v x == 0 then stoc else stoc + 1
-- 30
substSome : Nat -> Nat -> Nat -> Nat -> Nat
substSome Z     x v c = x
substSome (S k) x v c = substAtWith (substSome k x v c) (freepos k v x) c
-- 31
subst : Nat -> Nat -> Nat -> Nat
subst a v = substSome (freenum v a) a v
-- 32
implies : Nat -> Nat -> Nat
implies a = or (myNot2 a)
and : Nat -> Nat -> Nat
and a b = myNot2 $ or (myNot2 a) (myNot2 b)
equiv : Nat -> Nat -> Nat
equiv a b = and (implies a b) (implies b a)
exists : Nat -> Nat -> Nat
exists x a = myNot2 (forall2 x (myNot2 a))
-- 33
typeLift : Nat -> Nat -> Nat
typeLift n x = typeLift' n x (power x (power x n)) (power x (power x n)) where
  typeLift' n x Z acc = acc
  typeLift' n x (S y) acc = typeLift' n x y choice where
    choice = if typeLift'' n x y (len x) then (S y) else acc where
      typeLift'' n x y Z     = True
      typeLift'' n x y (S k) =
        ((not (isVar (elem x (S k))) && elem y (S k) == elem x (S k))
          || ((isVar (elem x (S k))) && elem y (S k) == elem x (S k) * power (prime 1 (elem x (S k))) 2))
            && typeLift'' n x y k
-- 10.8.5 公理・定理・形式的証明
-- 34
isAxiomI : Nat -> Bool
isAxiomI x = x == α１ || x == α２ || x == α３
-- 35
isSchemaII1 : Nat -> Bool
isSchemaII1 x = isSchemaII1' x x where
  isSchemaII1' x Z     =  isForm Z     && x == implies (or Z     Z)     Z
  isSchemaII1' x (S p) = (isForm (S p) && x == implies (or (S p) (S p)) (S p)) || isSchemaII1' x p
isSchemaII2 : Nat -> Bool
isSchemaII2 x = isSchemaII2' x x where
  isSchemaII2' x Z     = False
  isSchemaII2' x (S p) = isSchemaII2'' x (S p) x || isSchemaII2' x p where
    isSchemaII2'' x p Z     =  isForm p && isForm Z     && x == implies p (or p Z)
    isSchemaII2'' x p (S q) = (isForm p && isForm (S q) && x == implies p (or p (S q)) ) || isSchemaII2'' x p q
isSchemaII3 : Nat -> Bool
isSchemaII3 x = isSchemaII3' x x where
  isSchemaII3' x Z     = False
  isSchemaII3' x (S p) = isSchemaII3'' x (S p) x || isSchemaII3' x p where
    isSchemaII3'' x p Z     =  isForm p && isForm Z     && x == implies (or p Z)     (or Z p)
    isSchemaII3'' x p (S q) = (isForm p && isForm (S q) && x == implies (or p (S q)) (or (S q) p) ) || isSchemaII3'' x p q
isSchemaII4''' : Nat -> Nat -> Nat -> Nat -> Bool
isSchemaII4''' x p q Z     =  isForm p && isForm q && isForm Z     && x == implies (implies p q) (implies (or Z p)     (or Z     q))
isSchemaII4''' x p q (S r) = (isForm p && isForm q && isForm (S r) && x == implies (implies p q) (implies (or (S r) p) (or (S r) q)) ) || isSchemaII4''' x p q r
isSchemaII4 : Nat -> Bool
isSchemaII4 x = isSchemaII4' x x where
  isSchemaII4' x Z     = False
  isSchemaII4' x (S p) = isSchemaII4'' x (S p) x || isSchemaII4' x p where
    isSchemaII4'' x p Z     = False
    isSchemaII4'' x p (S q) = isSchemaII4''' x p (S q) x || isSchemaII4'' x p q
-- 36
isSchemaII : Nat -> Bool
isSchemaII x = isSchemaII1 x || isSchemaII2 x || isSchemaII3 x || isSchemaII4 x
-- 37
isNotBoundIn : Nat -> Nat -> Nat -> Bool
isNotBoundIn z y v = not $ isNotBoundIn' (len y) where
  isNotBoundIn' Z     = False
  isNotBoundIn' (S n) = isNotBoundIn'' (S n) (len z) || isNotBoundIn' n where
    isNotBoundIn'' n Z     = False
    isNotBoundIn'' n (S m) = isNotBoundIn''' n (S m) z || isNotBoundIn'' n m where
      isNotBoundIn''' n m Z     = False
      isNotBoundIn''' n m (S w) = (S w) == elem z m && isBoundAt (S w) n y && isFreeAt v n y || isNotBoundIn''' n m w
-- 38
isSchemaIII1 : Nat -> Bool
isSchemaIII1 x = isSchemaIII1' x where
  isSchemaIII1' Z     = False
  isSchemaIII1' (S v) = isSchemaIII1'' (S v) x || isSchemaIII1' v where
    isSchemaIII1'' v Z     = False
    isSchemaIII1'' v (S y) = isSchemaIII1''' v (S y) x || isSchemaIII1'' v y where
      isSchemaIII1''' v y Z     = False
      isSchemaIII1''' v y (S z) = isSchemaIII1'''' v y (S z) x || isSchemaIII1''' v y z where
        isSchemaIII1'''' v y z Z     = isVarType v Z     && isNthType z Z     && isForm y && isNotBoundIn z y v && x == implies (forall2 v y) (subst y v z)
        isSchemaIII1'''' v y z (S n) = isVarType v (S n) && isNthType z (S n) && isForm y && isNotBoundIn z y v && x == implies (forall2 v y) (subst y v z)
          || isSchemaIII1'''' v y z n
-- 39
isSchemaIII2''' : Nat -> Nat -> Nat -> Nat -> Bool
isSchemaIII2''' x v q Z     = isVar v && isForm Z     && (not (isFree v Z))     && isForm q && x == implies (forall2 v (or Z     q)) (or Z     (forall2 v q))
isSchemaIII2''' x v q (S p) = isVar v && isForm (S p) && (not (isFree v (S p))) && isForm q && x == implies (forall2 v (or (S p) q)) (or (S p) (forall2 v q))
  || isSchemaIII2''' x v q p
isSchemaIII2 : Nat -> Bool
isSchemaIII2 x = isSchemaIII2' x where
  isSchemaIII2' Z = False
  isSchemaIII2' (S v) = isSchemaIII2'' (S v) x || isSchemaIII2' v where
    isSchemaIII2'' v Z     = False
    isSchemaIII2'' v (S q) = isSchemaIII2''' x v (S q) x || isSchemaIII2'' v q
-- 40
isAxiomIV : Nat -> Bool
isAxiomIV x = isAxiomIV' x where
  isAxiomIV' Z     = False
  isAxiomIV' (S u) = isAxiomIV'' (S u) x || isAxiomIV' u where
    isAxiomIV'' u Z     = False
    isAxiomIV'' u (S v) = isAxiomIV''' u (S v) x || isAxiomIV'' u v where
      isAxiomIV''' u v Z     = False
      isAxiomIV''' u v (S y) = isAxiomIV'''' u v (S y) x || isAxiomIV''' u v y where
        isAxiomIV'''' u v y Z     = isVarType u      1  && isVarType v Z && isFree u y && isForm y && x == exists u (forall2 v (equiv (m8 (seq u) (paren (seq v))) y))
        isAxiomIV'''' u v y (S n) = isVarType u (n + 1) && isVarType v n && isFree u y && isForm y && x == exists u (forall2 v (equiv (m8 (seq u) (paren (seq v))) y))
          || isAxiomIV'''' u v y n

-- 45[to use]
postulate proves : Nat -> Nat -> Bool



