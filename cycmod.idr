import Decidable.Equality

%default total

data Inspect : a -> Type where
  wi : {A : Type} -> (x : A) -> (y : A) -> (eq: x = y) -> Inspect x
  
inspect : {A : Type} -> (x : A) -> Inspect x
inspect x = wi x _ refl

match : {A : Type} -> {x : A} -> (y : A) -> {eq : x = y} -> Inspect x
match y {eq} = wi _ y eq

succNotLTEZ : (n : Nat) -> LTE (S n) Z -> _|_
succNotLTEZ n lteZero impossible 

decEqNatRefl : (a : Nat) -> decEq a a = Yes refl {a}
decEqNatRefl Z = refl
decEqNatRefl (S a) = let ih = decEqNatRefl a in ?deceqnatrefl

data Cyc : Nat -> Type where
  mkCyc : (r : Nat) -> Cyc (S n)

getR : Cyc n -> Nat
getR (mkCyc r) = r

rotate : Cyc n -> Cyc n
rotate (mkCyc r) = mkCyc (S r)

cycPlus : Cyc (S n) -> Cyc (S n) -> Cyc (S n)
cycPlus (mkCyc left) (mkCyc right) = mkCyc (left + right)

cycPlusRightZeroNeutral : (c : Cyc (S n)) -> cycPlus c (mkCyc Z) = c
cycPlusRightZeroNeutral (mkCyc c) = ?cprznprf

cycPlusAssociative : (left : Cyc (S n)) -> (middle : Cyc (S n)) -> (right : Cyc (S n)) -> cycPlus left (cycPlus middle right) = cycPlus (cycPlus left middle) right
cycPlusAssociative (mkCyc l) (mkCyc m) (mkCyc r) = ?cycassociativeprf

cycPlusCommutative : (left : Cyc (S n)) -> (right : Cyc (S n)) -> cycPlus left right = cycPlus right left
cycPlusCommutative (mkCyc l) (mkCyc r) = ?cyccommutativeprf

reduce' : Nat -> Nat -> Nat -> Nat
reduce' n c Z = c
reduce' n c (S r) with (decEq n (S c))
  | (Yes p) = reduce' n Z r
  | (No p) = reduce' n (S c) r

decEqInv : (n : Nat) -> (c : Nat) -> (prf: n = c -> _|_) -> (prf' : n = c -> _|_ ** decEq n c = No prf')
decEqInv n c prf with (decEq n c)
  | (Yes p) = FalseElim (prf p)
  | (No p) = (p ** refl)

advPlusPrf : (n, c, k : Nat) -> n = c + (S (S k)) -> n = (S c) + (S k)
advPlusPrf n c k prf = ?appprf

natNotEqPlusSucc : (c,k : Nat) -> c = plus c (S k) -> _|_
natNotEqPlusSucc c k refl impossible

reduceOneZero : (c : Nat) -> reduce' (S Z) Z c = Z
reduceOneZero Z = refl
reduceOneZero (S k) = let ih = reduceOneZero k in ?rozprf_2

reduceElimg : (n,c,r : Nat) -> (prf: (S n) = c + (S r)) -> reduce' (S n) c (S r) = Z
reduceElimg n c Z prf = ?prf_1
reduceElimg n c (S k) prf with (decEq n c)
  | (Yes p) = FalseElim ?reduceelimf
  | (No p)= let ih = reduceElimg n (S c) k (advPlusPrf (S n) c k prf) in ?reduceelimprf

reduceElim : (n : Nat) -> mkCyc {n=n} (reduce' (S n) Z (S n)) = mkCyc {n = n} Z
reduceElim n = ?remprf

unsuccInEq : (c : Nat) -> (n : Nat) -> ((S n = S c) -> _|_) -> ((n = c) -> _|_)
unsuccInEq c n prf prf' = ?usieprf

lteAdvance : (c : Nat) -> (n : Nat) -> (l: LTE c n) -> ((n = c) -> _|_) -> LTE (S c) n
lteAdvance Z Z l prf = FalseElim ?lteadvelim
lteAdvance Z (S n) l prf = ?lteadvprf_1
lteAdvance (S c) Z l prf = FalseElim $ succNotLTEZ c l
lteAdvance (S c) (S n) (lteSucc l) prf = let ih = lteAdvance c n l (unsuccInEq c n prf) in ?lteadvprf_2

lteSuccTrans : (c : Nat) -> (n : Nat) -> LTE (S c) n -> LTE 1 n
lteSuccTrans c Z prf = FalseElim ?lstelim
lteSuccTrans c (S k) prf = ?lstprf_2

reducel : (n : Nat) -> (c : Nat ** LT c n) -> (r : Nat) -> (out : Nat ** LT out n)
reducel n c Z = c
reducel n (c ** prf) (S r) with (decEq n (S c))
  | (Yes p) = reducel n (Z ** (lteSuccTrans c n prf)) r
  | (No p) = reducel n (S c ** ?reducelprf) r

reduce : Cyc (S n) -> Cyc (S n)
reduce (mkCyc r) {n=n} = mkCyc $ reduce' (S n) Z r

reduceP : (n: Nat) -> Cyc (S n) -> (r : Nat ** LT r (S n))
reduceP Z (mkCyc c) = (Z ** (lteSucc lteZero))
reduceP (S n) (mkCyc c) = reducel (S (S n)) (Z ** (lteSucc lteZero)) c

cycInverse' : Nat -> Nat -> Nat -> Nat
cycInverse' Z _ _ = Z 
cycInverse' n c Z = c
cycInverse' (S n) Z (S r) = cycInverse' (S n) n r
cycInverse' n (S c) (S r) = cycInverse' n c r

minusElim : (n : Nat) -> (r : Nat) -> LT r n -> plus r (minus n r) = n
minusElim n Z prf = ?minusElimPrfz
minusElim Z (S r) prf = FalseElim ?wrongo
minusElim (S n) (S r) (lteSucc prf) = let ih = minusElim n r prf in ?minusElimPrf

cycInverse : (c : Cyc (S n)) -> (i : Cyc (S n) ** (reduce (cycPlus (mkCyc (getWitness $ reduceP n c)) i)) = mkCyc {n = n} 0)
cycInverse {n = Z} (mkCyc c) = (mkCyc Z ** refl)
cycInverse {n = S n} c with (reduceP (S n) c)
  | (Z ** prf) = ((mkCyc Z) ** refl)
  | ((S r) ** (lteSucc prf)) with (decEq n 0)
    | (Yes prf') = (mkCyc ((S (S n)) - (S r)) ** ?invsyprf)
    | (No prf') = (mkCyc ((S (S n)) - (S r)) ** ?invsnprf)

-- New inverse function if (reduce Z+c = 0 then Z else if reduce (S Z + c] = 0...

---------- Proofs ----------


Main.rozprf_2 = proof
  intros
  exact ih


Main.remprf = proof
  compute
  intros
  let prf = reduceElimg n Z n refl
  rewrite sym prf
  trivial


Main.reduceelimf = proof
  compute
  intro n,c,p,k
  rewrite sym p
  rewrite (plusSuccRightSucc c (S k))
  intro
  let prf' = succInjective c (plus c (S k)) prf
  exact (natNotEqPlusSucc c k prf')


Main.reduceelimprf = proof
  compute
  intros
  let deq = decEqInv n c p
  rewrite sym (getProof deq)
  compute
  rewrite sym ih
  refine refl


Main.appprf = proof
  compute
  intros
  rewrite sym (plusSuccRightSucc c (S k))
  exact prf


Main.prf_1 = proof
  intro n,c
  compute
  rewrite (plusCommutative 1 c)
  intro
  let prfa = succInjective n c prf
  rewrite prfa
  rewrite sym (decEqNatRefl n)
  compute
  trivial


Main.invsnprf = proof
  compute
  intros
  rewrite sym (minusElim (S n) r prf)
  rewrite (reduceElim (S n))
  compute
  trivial


Main.invsyprf = proof
  compute
  intros
  rewrite sym (minusElim (S n) r prf)
  compute
  rewrite sym prf'
  compute
  trivial


Main.lstelim = proof
  intros
  exact (succNotLTEZ c prf)


Main.lstprf_2 = proof
  compute
  intros
  refine lteSucc
  exact lteZero


Main.reducelprf = proof
  compute
  intros
  exact (lteAdvance (S c) n prf p)


Main.lteadvelim = proof
  compute
  intros
  exact (prf refl)


Main.lteadvprf_2 = proof
  compute
  intros
  refine lteSucc
  exact ih


Main.usieprf = proof
  compute
  intros
  exact (prf (cong prf'))


Main.lteadvprf_1 = proof
  compute
  intros
  refine lteSucc
  exact lteZero 


Main.wrongo = proof
  compute
  intros
  exact (succNotLTEZ (S r) prf)


Main.minusElimPrf = proof
  compute
  intros
  rewrite sym ih
  trivial


Main.minusElimPrfz = proof
  intros
  rewrite sym (minusZeroRight n)
  trivial

Main.cprznprf = proof
  intros
  rewrite (plusZeroRightNeutral c)
  trivial


Main.cyccommutativeprf = proof
  intros
  rewrite (plusCommutative l r)
  trivial


Main.cycassociativeprf = proof
  intros
  rewrite (plusAssociative l m r)
  trivial


Main.deceqnatrefl = proof
  compute
  intros
  rewrite sym ih
  compute
  trivial
