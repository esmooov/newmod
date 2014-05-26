%default total

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

reduceElim'' : (n : Nat) -> mkCyc {n=n} (reduce' (S n) Z (S n)) = mkCyc {n = n} Z
reduceElim'' Z = refl
reduceElim'' (S k) 

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

reducePMk : Cyc (S n) -> Cyc (S n)
reducePMk {n=n} c with (reduceP n c)
  | (r ** prf) = mkCyc r

reduceSZEqZ : (r : Nat) -> reduce' (S Z) Z r = Z
reduceSZEqZ Z = refl
reduceSZEqZ (S r) = let ih = reduceSZEqZ r in ?rszezprf

cycInverse' : Nat -> Nat -> Nat -> Nat
cycInverse' Z _ _ = Z 
cycInverse' n c Z = c
cycInverse' (S n) Z (S r) = cycInverse' (S n) n r
cycInverse' n (S c) (S r) = cycInverse' n c r

minusElim : (n : Nat) -> (r : Nat) -> LT r n -> plus r (minus n r) = n
minusElim n Z prf = ?minusElimPrfz
minusElim Z (S r) prf = FalseElim ?wrongo
minusElim (S n) (S r) (lteSucc prf) = let ih = minusElim n r prf in ?minusElimPrf

decEqNo : (n : Nat) ->  (prf: (n = Z) -> _|_) -> decEq n Z = No prf
decEqNo n prf with (decEq n Z)
  | (Yes p) = ?a
  | (No prf) = ?b

cycInverse : (c : Cyc (S n)) -> (i : Cyc (S n) ** (reduce (cycPlus (mkCyc (getWitness $ reduceP n c)) i)) = mkCyc {n = n} 0)
cycInverse {n = Z} (mkCyc c) = (mkCyc Z ** refl)
cycInverse {n = S n} c with (reduceP (S n) c)
  | (Z ** prf) = ((mkCyc Z) ** refl)
  | ((S r) ** (lteSucc prf)) with (decEq n 0)
    | (Yes prf') = (mkCyc ((S (S n)) - (S r)) ** ?invsyprf)
    | (No prf') = (mkCyc ((S (S n)) - (S r)) ** ?invsnprf)

---------- Proofs ----------

Main.invsnprf = proof
  compute
  intros
  rewrite sym (minusElim (S n) r prf)
  rewrite (reduceElim'' (S n))
  compute
  refine refl


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



Main.rszezprf = proof
  intros
  exact ih


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
