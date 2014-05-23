%default total

data Cyc : Nat -> Type where
  mkCyc : (r : Nat) -> Cyc (S n)

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

reduce : Cyc (S n) -> Cyc (S n)
reduce (mkCyc r) {n=n} = mkCyc $ reduce' (S n) Z r

reduceSZEqZ : (r : Nat) -> reduce' (S Z) Z r = Z
reduceSZEqZ Z = refl
reduceSZEqZ (S r) = let ih = reduceSZEqZ r in ?rszezprf

cycInverse : (c : Cyc (S n)) -> (i : Cyc (S n) ** (reduce (cycPlus (reduce c) i)) = mkCyc {n = n} 0)
cycInverse {n = Z} (mkCyc c) = (mkCyc Z ** ?invsprfz)
cycInverse {n = (S n)} c with (reduce c)
  | (mkCyc Z) = ((mkCyc Z) ** refl)
  | (mkCyc (S r)) = (mkCyc ((S n) - r) ** ?invsprf)

---------- Proofs ----------

Main.invsprfz = proof
  compute
  intros
  rewrite sym (reduceSZEqZ c)
  compute
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


