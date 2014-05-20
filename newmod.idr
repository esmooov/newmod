%default total

data Mod : (n : Nat) -> Type where
  mkMod : (i : Nat) -> (l : Nat ** (n : Nat ** (n = S(i + l)))) -> Mod n

succZeroN : (n : Nat) -> (S n) = (S (plus 0 n))
succZeroN n = refl

succZeroN' : (n : Nat) -> (S n) = (S (plus n 0))
succZeroN' n = rewrite sym (plusZeroRightNeutral n) in refl

makeModZ : (n : Nat) -> Mod (S n)
makeModZ n = mkMod 0 (n ** ((S n) ** succZeroN n))

makeModLast : (n : Nat) -> Mod (S n)
makeModLast n = mkMod n (Z ** ((S n) ** succZeroN' n))

rotate : Mod n -> Mod n
rotate (mkMod i (Z ** (n ** prf))) = mkMod Z (i ** (n ** ?rzprf))
rotate (mkMod i ((S l) ** (n ** prf))) = mkMod (S i) (l ** (n ** ?rsprf))

zeroNotSucc : (n : Nat) -> Z = S n -> _|_
zeroNotSucc Z refl impossible
zeroNotSucc (S k) refl impossible

succNotLTEZ : (n : Nat) -> LTE (S n) Z -> _|_
succNotLTEZ n lteZero impossible 

modplus' : Nat -> Mod n -> Mod n
modplus' Z m' = m'
modplus' {n=n} (S i) m' with (decEq n (S i))
  | Yes p = m'
  | No p = modplus' i (rotate m')

modplus : Mod (S n) -> Mod (S n) -> Mod (S n)
modplus {n=n} (mkMod i _) (mkMod i' _) = modplus' (i + i') (makeModZ n)

modplusCommutative : (a : Mod (S n)) -> (b : Mod (S n)) -> modplus a b = modplus b a
modplusCommutative (mkMod i _) (mkMod i' _) = ?mpluscomutative

natPlusMinusInverse : (j : Nat) -> (n : Nat) -> LT j n -> plus j (n-j) = n
natPlusMinusInverse Z n lt = minusZeroRight n
natPlusMinusInverse j Z lt = FalseElim (succNotLTEZ j lt)
natPlusMinusInverse (S j) (S n) (lteSucc lt) = let ih = natPlusMinusInverse j n lt in ?npmiprf

modFill : (j : Nat) -> (n : Nat) -> LT j n -> Mod (S n)
modFill Z Z lt = mkMod Z (Z ** (S Z ** refl))
modFill Z n lt = mkMod Z (n-Z ** (S n ** ?modfillz))
modFill j Z lt = FalseElim $ succNotLTEZ j lt
modFill (S k) n ltp = mkMod (S k) (n-(S k) ** (S n ** ?modfill))

--modplusReduce : (j : Nat) -> (k : Nat) -> (n : Nat) -> (LT j (S n)) -> (p : k = n - j) -> (prf : S n = S(j + k)) -> modplus' {n = S n} j (mkMod 0 (n ** (S n ** refl))) = mkMod {n = S n} j (k ** (S n ** refl))
--modplusReduce Z k n lt p prf = ?mprprf_1
--modplusReduce (S j) k n lt p prf = ?mprprf_2

--modplusInjection : (i : Nat) -> (k : Nat) -> (j : Nat) -> (n : Nat) -> (prf: S n = S (i+k)) -> modplus {n=n} (mkMod i (k ** (S n ** prf))) (modplus' j (mkMod 0 (n ** (S n ** refl)))) = modplus' {n = S n} (i + j) (mkMod 0 (n ** (S n ** refl)))
--modplusInjection i k j n prf with (modplus' {n = S n} j (mkMod 0 (n ** (S n ** refl))))
  --| (mkMod o r) = ?mpiprf

modplusAssociative : (a : Mod (S n)) -> (b : Mod (S n)) -> (c : Mod (S n)) -> modplus a (modplus b c) = modplus (modplus a b) c
modplusAssociative (mkMod i x) (mkMod k y) (mkMod j z) = ?prf_1

succPlusInvert : (a : Nat) -> (b : Nat) -> (S a) + b = (S b) + a
succPlusInvert Z b = rewrite plusCommutative Z b in refl
succPlusInvert (S a) b = ?succplusprf

invertPrf : (a : Nat) -> (b : Nat) -> (n : Nat) -> n = S (plus (S a) b) -> n = S (plus (S b) a)
invertPrf a b n prf = ?invertprf

decEqNatRefl : (a : Nat) -> decEq a a = Yes refl {a}
decEqNatRefl Z = refl
decEqNatRefl (S a) = let ih = decEqNatRefl a in ?deceqnatrefl

inverseM : (m : Mod (S n)) -> (inv : Mod (S n) ** (modplus m inv = makeModZ n))
inverseM {n = n} (mkMod Z (l ** (n ** prf))) = (makeModZ n ** refl)
inverseM (mkMod (S i) (l ** (Z ** prf))) = FalseElim $ zeroNotSucc (plus (S i) l) prf
inverseM {n = n} (mkMod (S k) (l ** (S n ** prf))) = (mkMod (S l) (k ** (S n ** invertPrf k l (S n) prf)) ** ?imprf)

---------- Proofs ----------

Main.modfill = proof
  intros
  compute
  rewrite sym (natPlusMinusInverse (S k) n ltp)
  trivial


Main.npmiprf = proof
  compute
  intros
  refine cong
  exact ih



Main.modfillz = proof
  compute
  intros
  rewrite sym (minusZeroRight n)
  trivial



Main.imprf = proof
  compute
  intros
  let prf' = succInjective n (S (plus k l)) prf
  rewrite (plusSuccRightSucc k l)
  rewrite prf'
  rewrite sym (decEqNatRefl n)
  compute
  trivial

Main.deceqnatrefl = proof
  compute
  intros
  rewrite sym ih
  compute
  trivial

Main.mpluscomutative = proof
  compute
  intros
  rewrite (plusCommutative i i')
  trivial

Main.invertprf = proof
  intros
  rewrite (succPlusInvert a b)
  exact prf

Main.rsprf = proof
  compute
  intros
  rewrite sym (plusSuccRightSucc i l)
  exact prf

Main.rzprf = proof
  compute
  intros
  rewrite sym prf
  rewrite sym (plusZeroRightNeutral i)
  refine refl

Main.succplusprf = proof
  intros
  rewrite (plusSuccRightSucc b a)
  rewrite (plusCommutative a b)
  trivial
