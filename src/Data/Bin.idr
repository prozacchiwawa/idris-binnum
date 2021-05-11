module Data.Bin

import Decidable.Equality

%default total

decAsBool : Dec p -> Bool
decAsBool (Yes _) = True
decAsBool (No _)  = False

public export
less : Nat -> Nat -> Nat
less Z _ = Z
less a Z = a
less (S a) (S b) = less a b

public export
lessThan : Nat -> Nat -> Bool
lessThan Z (S a) = True
lessThan _ Z = False
lessThan (S a) (S b) = lessThan a b

sNotZ : {a : Nat} -> (S a = 0) -> Void
sNotZ Refl impossible

zNotS : {a : Nat} -> (0 = S a) -> Void
zNotS Refl impossible

-- Thanks: https://stackoverflow.com/questions/46507712/how-can-i-have-idris-automatically-prove-that-two-values-are-not-equal
fromFalse : (d : Dec p) -> {auto isFalse : decAsBool d = False} -> Not p
fromFalse (Yes _) {isFalse = Refl} impossible
fromFalse (No contra) = contra

data NotEq : a -> a -> Type where
    MkNotEq : {a : t} -> {b : t} -> Not (a = b) -> NotEq a b

public export data Bin = O Nat Bin | BNil

-- Thanks: https://www.reddit.com/r/Idris/comments/8yv5fn/using_deceq_in_proofs_extracting_and_applying_the/e2e8a6l/?context=3
O_injective : (O a v = O b w) -> (a = b, v = w)
O_injective Refl = (Refl, Refl)

total bnilNotO : (a : Nat) -> (b : Bin) -> (BNil = O a v) -> Void
bnilNotO a b p impossible

total notOBNil : (a : Nat) -> (b : Bin) -> (O a v = BNil) -> Void
notOBNil a b p impossible

total aNEBMeansNotEqual : (a : Nat) -> (b : Nat) -> (v : Bin) -> Dec (a = b) -> Dec (O a v = O b v)
aNEBMeansNotEqual a b v (Yes prf) = rewrite prf in Yes Refl
aNEBMeansNotEqual a b v (No contra) =
  No $ \prf =>
    let (ojAB, _) = O_injective prf in
    contra ojAB

total vNEWMeansNotEqual : (v : Bin) -> (w : Bin) -> Dec (v = w) -> Dec (O Z v = O Z w)
vNEWMeansNotEqual v w (Yes prf) = rewrite prf in Yes Refl
vNEWMeansNotEqual v w (No contra) = 
  No $ \prf =>
    let (_, ojVW) = O_injective prf in
    contra ojVW

avNEBWMeansNotEqual : (a : Nat) -> (v : Bin) -> (b : Nat) -> (w : Bin) -> Dec (a = b) -> Dec (v = w) -> Dec (O a v = O b w)
avNEBWMeansNotEqual a v b w (Yes prfAB) (Yes prfVW) = 
  rewrite prfAB in
  rewrite prfVW in
  Yes Refl
avNEBWMeansNotEqual a v b w (Yes prfAB) (No contraVW) = 
  No $ \prf => 
    let (_, ojVW) = O_injective prf in contraVW ojVW
avNEBWMeansNotEqual a v b w (No contraAB) _ = 
  No $ \prf =>
    let (ojAV, _) = O_injective prf in contraAB ojAV

eq0BNil : (O 0 BNil = O 0 BNil)
eq0BNil = Refl

doDecEqInner : (x1 : Bin) -> (x2 : Bin) -> Dec (x1 = x2)
doDecEqInner BNil                BNil              = Yes Refl
doDecEqInner BNil                (O b     w      ) = 
  No (bnilNotO {a=b} {b=w})
doDecEqInner (O a     v        ) BNil              = 
  No (notOBNil {a=a} {b=v})
doDecEqInner (O a     v        ) (O b     w      ) =
  avNEBWMeansNotEqual a v b w (decEq a b) (doDecEqInner v w)

DecEq Bin where
  decEq = doDecEqInner

binIsZero : Bin -> Bool
binIsZero BNil = True
binIsZero (O _ _) = False

public export
oneMore : Bin -> Bin
oneMore BNil = BNil
oneMore (O a x) = O (S a) x

oneMoreZeroIsZero : oneMore BNil = BNil
oneMoreZeroIsZero = Refl

public export
flipFromLeft : Bin -> Bin
flipFromLeft BNil = O Z BNil
flipFromLeft (O (S a) x) = O Z (O a x)
flipFromLeft (O Z x) = assert_total (oneMore (flipFromLeft x))

public export
binInc : Bin -> Bin
binInc BNil = O Z BNil
binInc (O Z BNil) = O (S Z) BNil
binInc (O a v) = flipFromLeft (O a v)

binDec : Bin -> Bin
binDec BNil = BNil
binDec (O Z BNil) = BNil
binDec (O Z (O a b)) = (O (S a) b)
{-
  0001 -- -> 1110
-}
binDec (O (S a) b) = 
  assert_total (O Z (binDec (O a b)))

public export
nat2Bin : Nat -> Bin
nat2Bin Z = BNil
nat2Bin (S a) = binInc (nat2Bin a)

nat2BinZIsBNil : nat2Bin Z = BNil
nat2BinZIsBNil = Refl

public export
bin2Nat : Bin -> Nat
bin2Nat BNil = Z
bin2Nat (O Z v) = 
  let m1 = assert_total (bin2Nat v) in
  let m2 = plus m1 m1 in
  S m2
bin2Nat (O (S a) v) =
  let m1 = assert_total (bin2Nat (O a v)) in
  plus m1 m1

bin2NatBNilIsZ : bin2Nat BNil = Z
bin2NatBNilIsZ = Refl

public export
binAdd : Bin -> Bin -> Bin
binAdd a b = nat2Bin (plus (bin2Nat a) (bin2Nat b))

azPlus : (a : Nat) -> (plus a Z = a)
azPlus Z = Refl
azPlus (S a1) = rewrite azPlus {a=a1} in Refl

zaPlus : (a : Nat) -> (plus Z a = a)
zaPlus Z = Refl
zaPlus (S a1) = Refl

testPlusA0 : (n : Nat) -> n = plus n 0
testPlusA0 Z = Refl
testPlusA0 (S k) =
  let rec = testPlusA0 {n=k} in
  rewrite rec in
  rewrite azPlus k in
  rewrite azPlus k in
  Refl

plusS1Eq2 : (n : Nat) -> plus n (S Z) = S n
plusS1Eq2 Z = Refl
plusS1Eq2 (S a) =
  let rec = plusS1Eq2 {n=a} in
  rewrite rec in Refl

add2NEqNP2 : (n : Nat) -> (a : Nat) -> S (plus n a) = plus n (S a)
add2NEqNP2 Z Z = Refl
add2NEqNP2 Z (S a) = Refl
add2NEqNP2 n Z =
  rewrite sym (testPlusA0 n) in
  rewrite (plusS1Eq2 n) in Refl

add2NEqNP2 (S n) (S a) =
  rewrite (add2NEqNP2 n (S a)) in
  Refl

moveSInPlus2 : (a : Nat) -> S (plus a a) = plus a (S a)
moveSInPlus2 Z = Refl
moveSInPlus2 a1 =
  rewrite sym (add2NEqNP2 a1 a1) in Refl

moveSInPlus3 : (a : Nat) -> S (plus a a) = plus (S a) a
moveSInPlus3 Z = Refl
moveSInPlus3 a1 = Refl

moveSInPlus4 : (a : Nat) -> plus (S a) a = S (plus a a)
moveSInPlus4 Z = Refl
moveSInPlus4 a1 = Refl

oneMoreIsTwiceAsMuch : (v : Bin) -> (plus (plus (bin2Nat v) (bin2Nat v)) (plus (bin2Nat v) (bin2Nat v))) = (bin2Nat (oneMore (oneMore v)))
oneMoreIsTwiceAsMuch BNil = Refl
oneMoreIsTwiceAsMuch (O Z v) = Refl
oneMoreIsTwiceAsMuch (O (S a) v) = Refl

oneMoreXIs2X : (b : Bin) -> bin2Nat (oneMore b) = plus (bin2Nat b) (bin2Nat b)
oneMoreXIs2X BNil = Refl
oneMoreXIs2X (O n a) = Refl

plusAZ : (a : Nat) -> (a = plus a Z)
plusAZ Z = Refl
plusAZ (S a) =
  rewrite plusAZ a in
  rewrite azPlus a in
  rewrite azPlus a in
  Refl

plusZA : (a : Nat) -> (a = plus Z a)
plusZA Z = Refl
plusZA (S a1) = Refl

plus00B0 : Z = plus Z Z
plus00B0 = Refl

saEqSb : (a : Nat) -> (b : Nat) -> Dec (S a = S b) -> Dec (a = b)
saEqSb Z Z (Yes prf) = Yes Refl
saEqSb a Z (Yes prf) =
  case decEq a Z of
    Yes prf1 =>
      rewrite prf1 in Yes Refl
    No contra => No contra
saEqSb a (S b) (Yes prf) =
  case decEq a (S b) of
    Yes prf1 => rewrite prf1 in Yes Refl
    No contra => No contra
saEqSb a b (No contra) =
  case decEq a b of
    Yes prf1 => rewrite prf1 in Yes Refl
    No contra => No contra

ssaNe1 : {a : Nat} -> (S (S a) = 1) -> Void
ssaNe1 Refl impossible

ssbNe1 : {b : Nat} -> (1 = S (S b)) -> Void
ssbNe1 Refl impossible

bEq0MeansSbEq1 : (b : Nat) -> Dec (0 = b) -> Dec (1 = S b)
bEq0MeansSbEq1 Z _ = Yes Refl
bEq0MeansSbEq1 (S b) _ = No $ \prfx => ssbNe1 prfx

saEqSb2 : (a : Nat) -> (b : Nat) -> (rw : Dec (a = b)) -> Dec (S a = S b)
saEqSb2 Z Z (Yes prf) = Yes Refl
saEqSb2 a Z (Yes prf) =
  case decEq a Z of
    Yes prf1 => rewrite prf1 in Yes Refl
    No contra => No $ \prfx => contra prf
saEqSb2 (S a) Z (No contra) =
  case decEq (S a) Z of
    Yes prf1 => rewrite prf1 in Yes Refl
    No contra1 => No ssaNe1
saEqSb2 a (S b) (Yes prf) =
  case decEq a (S b) of
    Yes prf1 => rewrite prf1 in Yes Refl
    No contra => No $ \prfx => contra prf
saEqSb2 Z (S b) (No contra) = No ssbNe1
saEqSb2 a b (No contra) =
  saEqSb (S a) (S b) (decEq (S (S a)) (S (S b)))

saEqSb3 : (a : Nat) -> (b : Nat) -> Dec (plus a 0 = plus b 0) -> Dec (a = b)
saEqSb3 a b prf =
  rewrite plusAZ a in
  rewrite plusAZ b in
  prf

oneIsNotTwo : (S Z) = (S (S Z)) -> Void
oneIsNotTwo p impossible

twoIsNotAPlus3 : {a : Nat} -> (S (S Z) = S (S (S a))) -> Void
twoIsNotAPlus3 Refl impossible

sPs : (a : Nat) -> (b : Nat) -> (a = b) -> (S a = S b)
sPs Z Z p = Refl
sPs Z (S b) p = absurd (zNotS {a = b} p)
sPs (S a) Z p = absurd (sNotZ {a = a} p)
sPs (S a) (S b) p with (saEqSb2 (S a) (S b) (Yes p))
  sPs (S a1) (S b1) p | Yes pe = pe
  sPs (S Z) (S Z) p | No contra = Refl
  sPs (S Z) (S (S b1)) p | No contra impossible
  sPs (S (S a1)) (S Z) p | No contra impossible
  sPs (S (S a1)) (S (S b1)) p | No contra with (saEqSb2 (S (S a1)) (S (S b1)) (Yes p))
    sPs (S (S a1)) (S (S b1)) p | No contra | Yes p1 = absurd (contra p1)
    sPs (S (S a1)) (S (S b1)) p | No contra | No q1 =
      let
        iwant = sPs (S (S a1)) (S (S b1)) p
      in
      absurd (assert_total (contra iwant))

eqs : (a : Nat) -> (b : Nat) -> (S a = S b) -> (a = b)
eqs Z Z p = Refl
eqs Z (S b) p with (decEq b Z)
  eqs Z (S Z) p | Yes zp = absurd (oneIsNotTwo p)
  eqs Z (S b1) p | No c impossible
eqs (S a) Z p impossible
eqs (S a1) (S b1) p with (decEq a1 b1)
  eqs (S a1) (S b1) p | Yes p1 =
    rewrite p1 in
    Refl
  eqs (S Z) (S Z) p | No c1 = Refl
  eqs (S Z) (S (S b1)) p | No c1 impossible
  eqs (S (S a1)) (S Z) p | No c1 impossible
  eqs (S (S a1)) (S (S b1)) p | No c1 with (saEqSb a1 b1 (No c1))
    eqs (S (S a1)) (S (S b1)) p | No c1 | Yes ppp =
      let
        cproof : (S a1 = S b1)
        cproof = sPs a1 b1 ppp
      in
      absurd (c1 cproof)
    eqs (S (S a1)) (S (S b1)) p | No c1 | No qqq =
      let
        cproof = eqs (S (S a1)) (S (S b1)) p
        dproof = eqs (S a1) (S b1) cproof
        subp = eqs a1 b1 (assert_total dproof)
      in
      absurd (qqq subp)

plusA0EqPlusB0 : (a : Nat) -> (b : Nat) -> (rw : Dec (plus a 1 = plus b 1)) -> Dec (plus a 0 = plus b 0)
plusA0EqPlusB0 Z Z (Yes prf) = Yes Refl
plusA0EqPlusB0 a Z (Yes prf) =
  rewrite azPlus a in
  case decEq a Z of
    Yes prf1 => Yes prf1
    No contra => No contra
plusA0EqPlusB0 (S a1) (S b1) (Yes prf) =
  rewrite add2NEqNP2 a1 0 in
  rewrite add2NEqNP2 b1 0 in
  rewrite plusS1Eq2 a1 in
  rewrite plusS1Eq2 b1 in
  saEqSb2 a1 b1 (decEq a1 b1)
plusA0EqPlusB0 (S a1) (S b1) (No contra) =
  rewrite add2NEqNP2 a1 0 in
  rewrite add2NEqNP2 b1 0 in
  rewrite plusS1Eq2 a1 in
  rewrite plusS1Eq2 b1 in
  saEqSb2 a1 b1 (decEq a1 b1)
plusA0EqPlusB0 Z Z (No contra) = absurd (contra Refl)
plusA0EqPlusB0 Z (S b1) (Yes p) with (decEq Z (S b1))
  plusA0EqPlusB0 Z (S b1) (Yes p) | Yes p2 =
    rewrite sym (plusAZ b1) in
    Yes p2
  plusA0EqPlusB0 Z (S b1) (Yes p) | No c2 =
    rewrite sym (plusAZ b1) in
    No c2
plusA0EqPlusB0 Z (S b1) (No contra) with (decEq Z (S b1))
  plusA0EqPlusB0 Z (S b1) (No contra) | Yes p2 =
    rewrite sym (plusAZ b1) in
    Yes p2
  plusA0EqPlusB0 Z (S b1) (No contra) | No c2 =
    rewrite sym (plusAZ b1) in
    No c2
plusA0EqPlusB0 (S a1) Z (No contra) =
  let
    res = saEqSb (plus a1 1) Z (No contra)
  in
  rewrite add2NEqNP2 a1 Z in
  res

plusA1EqPlusB1 : (a : Nat) -> (b : Nat) -> Dec (a = b) -> Dec (plus a 1 = plus b 1)
plusA1EqPlusB1 a b (Yes prf) =
  rewrite prf in Yes Refl
plusA1EqPlusB1 a b (No contra) =
  let re = plusA0EqPlusB0 a b (decEq (plus a 1) (plus b 1)) in
  rewrite plusS1Eq2 a in
  rewrite plusS1Eq2 b in
  saEqSb2 a b (No contra)

removeOneS : (a : Nat) -> (b : Nat) -> Dec (a = b) -> Dec (S a = S b)
removeOneS a b (Yes prf) =
  rewrite prf in Yes Refl
removeOneS a b (No contra) =
  rewrite plusAZ a in
  rewrite plusAZ b in
  saEqSb2 (plus a 0) (plus b 0) (decEq (plus a 0) (plus b 0))

twoTimesAIsZeroIfAIs2 : (a : Nat) -> Dec (plus a a = 0) -> Dec (a = 0)
twoTimesAIsZeroIfAIs2 a prf =
  saEqSb3 a 0 (decEq (plus a 0) 0)

twoTimesAIsZeroIfAIs : (a : Nat) -> Dec (a = 0) -> Dec (plus a a = 0)
twoTimesAIsZeroIfAIs a (Yes prf) = rewrite prf in Yes Refl
twoTimesAIsZeroIfAIs Z _ = Yes Refl
twoTimesAIsZeroIfAIs (S a) (No contra) =
  rewrite sym (add2NEqNP2 a a) in
  No $ \prf =>
    sNotZ {a=S (plus a a)} prf

fourIsNotZero : (S (S (S (S Z))) = 0) -> Void
fourIsNotZero Refl impossible

fourIsNotTwo : (S (S (S (S Z))) = S (S Z)) -> Void
fourIsNotTwo Refl impossible

sixIsNotZero : (S (S (S (S (S (S Z))))) = plus 0 0) -> Void
sixIsNotZero Refl impossible

sixIsNotTwo : (S (S (S (S (S (S Z))))) = plus 1 1) -> Void
sixIsNotTwo Refl impossible

sixIsNotFour : (S (S (S (S (S (S Z))))) = plus 2 2) -> Void
sixIsNotFour Refl impossible

fourIsNotAPlus6 : {a : Nat} -> (S (S (S (S Z))) = S (S (S (S (S (S (plus a a))))))) -> Void
fourIsNotAPlus6 Refl impossible

eightIsNotZero : (S (S (S (S (S (S (S (S Z))))))) = 0) -> Void
eightIsNotZero Refl impossible

eightIsNotTwo : (S (S (S (S (S (S (S (S Z))))))) = (S (S Z))) -> Void
eightIsNotTwo Refl impossible

eightIsNotFour : (S (S (S (S (S (S (S (S Z))))))) = (S (S (S (S Z))))) -> Void
eightIsNotFour Refl impossible

eightIsNotSix : (S (S (S (S (S (S (S (S Z))))))) = (S (S (S (S (S (S Z))))))) -> Void
eightIsNotSix Refl impossible

sixIsNotAPlus8 : {a : Nat} -> (S (S (S (S (S (S Z))))) = S (S (S (S (S (S (S (S (plus a a))))))))) -> Void
sixIsNotAPlus8 Refl impossible

eightIsNotAPlus10 : {a : Nat} -> (S (S (S (S (S (S (S (S Z))))))) = S (S (S (S (S (S (S (S (S (S (plus a a))))))))))) -> Void
eightIsNotAPlus10 Refl impossible

tenIsNotZero : (S (S (S (S (S (S (S (S (S (S Z))))))))) = plus 0 0) -> Void
tenIsNotZero Refl impossible

tenIsNotTwo : (S (S (S (S (S (S (S (S (S (S Z))))))))) = plus (S Z) (S Z)) -> Void
tenIsNotTwo Refl impossible

tenIsNotFour : (S (S (S (S (S (S (S (S (S (S Z))))))))) = plus (S (S Z)) (S (S Z))) -> Void
tenIsNotFour Refl impossible

tenIsNotSix : (S (S (S (S (S (S (S (S (S (S Z))))))))) = plus (S (S (S Z))) (S (S (S Z)))) -> Void
tenIsNotSix Refl impossible

tenIsNotEight : (S (S (S (S (S (S (S (S (S (S Z))))))))) = plus (S (S (S (S Z)))) (S (S (S (S Z))))) -> Void
tenIsNotEight Refl impossible

tenIsNotAPlus12 : {a : Nat} -> (S (S (S (S (S (S (S (S (S (S Z))))))))) = S (S (S (S (S (S (S (S (S (S (S (S (plus a a))))))))))))) -> Void
tenIsNotAPlus12 Refl impossible

fourPlusAIsNot0 : {a : Nat} -> (S (S (S (S a))) = 0) -> Void
fourPlusAIsNot0 Refl impossible

fourPlusAIsNot2 : {a : Nat} -> (S (S (S (S a))) = 2) -> Void
fourPlusAIsNot2 Refl impossible

a2Pa4 : (a : Nat) -> Dec (2 = a) -> Dec (4 = plus a a)
a2Pa4 (S (S Z)) _ = Yes Refl
a2Pa4 a (Yes r) =
  rewrite r in
  rewrite sym r in Yes Refl
a2Pa4 Z (No contra) = No fourIsNotZero
a2Pa4 (S Z) _ = No fourIsNotTwo
a2Pa4 (S (S (S a))) (No contra) =
  rewrite sym (add2NEqNP2 a (S (S a))) in
  rewrite sym (add2NEqNP2 a (S a)) in
  rewrite sym (add2NEqNP2 a a) in
  No fourIsNotAPlus6

plusZZPlus4N : {n : Nat} -> (S (S (S (S (plus n n)))) = plus 0 0) -> Void
plusZZPlus4N Refl impossible

plus2NEq0 : {n : Nat} -> (S (S n) = 0) -> Void
plus2NEq0 Refl impossible

plus2NEq1 : {n : Nat} -> (S (S n) = 1) -> Void
plus2NEq1 Refl impossible

plus4NNEqPlus2APlus2A : (n : Nat) -> (S (S (S (S (plus n n)))) = plus (S (S n)) (S (S n)))
plus4NNEqPlus2APlus2A n =
  rewrite sym (add2NEqNP2 n (S n)) in
  rewrite sym (add2NEqNP2 n n) in
  Refl

a4Pa2 : (n : Nat) -> (a : Nat) -> Dec (S (S (S (S (plus n n)))) = plus a a) -> Dec (S (S n) = a)
a4Pa2 n Z prf = No plus2NEq0
a4Pa2 n (S Z) prf = No plus2NEq1
a4Pa2 Z (S (S Z)) p = Yes Refl
a4Pa2 Z (S (S (S a))) p = No twoIsNotAPlus3
a4Pa2 n (S (S a)) p = decEq (S (S n)) (S (S a))

a3Pa6 : (a : Nat) -> Dec (3 = a) -> Dec (6 = plus a a)
a3Pa6 (S (S (S Z))) _ = Yes Refl
a3Pa6 a (Yes r) =
  rewrite r in
  rewrite sym r in Yes Refl
a3Pa6 Z (No contra) = No sixIsNotZero
a3Pa6 (S Z) _ = No sixIsNotTwo
a3Pa6 (S (S Z)) _ = No sixIsNotFour
a3Pa6 (S (S (S (S a)))) (No contra) =
  rewrite sym (add2NEqNP2 a (S (S (S a)))) in
  rewrite sym (add2NEqNP2 a (S (S a))) in
  rewrite sym (add2NEqNP2 a (S a)) in
  rewrite sym (add2NEqNP2 a a) in
  No sixIsNotAPlus8

a4Pa8 : (a : Nat) -> Dec (4 = a) -> Dec (8 = plus a a)
a4Pa8 (S (S (S (S Z)))) _ = Yes Refl
a4Pa8 a (Yes r) =
  rewrite r in
  rewrite sym r in Yes Refl
a4Pa8 Z (No contra) = No eightIsNotZero
a4Pa8 (S Z) _ = No eightIsNotTwo
a4Pa8 (S (S Z)) _ = No eightIsNotFour
a4Pa8 (S (S (S Z))) _ = No eightIsNotSix
a4Pa8 (S (S (S (S (S a))))) (No contra) =
  rewrite sym (add2NEqNP2 a (S (S (S (S a))))) in
  rewrite sym (add2NEqNP2 a (S (S (S a)))) in
  rewrite sym (add2NEqNP2 a (S (S a))) in
  rewrite sym (add2NEqNP2 a (S a)) in
  rewrite sym (add2NEqNP2 a a) in
  No eightIsNotAPlus10

fourPlusNNEqPlusN2N2 : (n : Nat) -> (S (S (S (S (plus n n)))) = plus (S (S n)) (S (S n)))
fourPlusNNEqPlusN2N2 n =
  rewrite sym (add2NEqNP2 n (S n)) in
  rewrite sym (add2NEqNP2 n n) in
  Refl

threePlusAIsNot2 : {a : Nat} -> (S (S (S a)) = S (S Z)) -> Void
threePlusAIsNot2 Refl impossible

twoIsNotThreePlusA : {a : Nat} -> (S (S Z) = S (S (S a))) -> Void
twoIsNotThreePlusA Refl impossible

fivePlusAIsNotFour : {a : Nat} -> (S (S (S (S (S a)))) = S (S (S (S Z)))) -> Void
fivePlusAIsNotFour Refl impossible

ssNEqPlusAA : (n : Nat) -> (a : Nat) -> Dec (S (S n) = a) -> Dec (S (S (S (S (plus n n)))) = plus a a)
ssNEqPlusAA Z a p = a2Pa4 a p
ssNEqPlusAA (S Z) a p = a3Pa6 a p
ssNEqPlusAA (S (S Z)) a p = a4Pa8 a p
ssNEqPlusAA n a (Yes p) =
  rewrite sym p in
  rewrite fourPlusNNEqPlusN2N2 n in
  let ssres1 = saEqSb (S (S (S (S (plus n n))))) (S (S n)) in
  let ssres2 = saEqSb (S (S (S (plus n n)))) (S n) in
  Yes Refl
ssNEqPlusAA n Z (No contra) = No fourPlusAIsNot0
ssNEqPlusAA n (S Z) (No contra) = No fourPlusAIsNot2
ssNEqPlusAA (S n) (S (S Z)) (No contra) = No fivePlusAIsNotFour
ssNEqPlusAA n (S (S a)) (No contra) =
  rewrite fourPlusNNEqPlusN2N2 n in
  decEq (S (S (plus n (S (S n))))) (S (S (plus a (S (S a)))))

canHalveAdds4 : (n : Nat) -> (a : Nat) -> (S (S n) = plus a a) -> ((S (S (S (S (plus n n))))) = plus (plus a a) (plus a a))
canHalveAdds4 n a prf =
  rewrite sym prf in
  rewrite sym (moveSInPlus2 (S n)) in
  rewrite sym (moveSInPlus2 n) in Refl

fourSBackIn : (a : Nat) -> (S (S (S (S (plus (plus a a) (plus a a))))) = plus (plus (S a) (S a)) (plus (S a) (S a)))
fourSBackIn Z = Refl
fourSBackIn (S a) =
  rewrite sym (add2NEqNP2 a a) in
  rewrite sym (add2NEqNP2 a (S a)) in
  rewrite sym (add2NEqNP2 a a) in
  rewrite sym (add2NEqNP2 (plus a a) (S (plus a a))) in
  rewrite sym (add2NEqNP2 (plus a a) (plus a a)) in
  rewrite sym (add2NEqNP2 (plus a a) (S (S (S (plus a a))))) in
  rewrite sym (add2NEqNP2 (plus a a) (S (S (plus a a)))) in
  rewrite sym (add2NEqNP2 (plus a a) (S (plus a a))) in
  rewrite sym (add2NEqNP2 (plus a a) (plus a a)) in
  Refl

ssPlusAAEqPlusSaSa : (a : Nat) -> (S (S (plus a a)) = plus (S a) (S a))
ssPlusAAEqPlusSaSa Z = Refl
ssPlusAAEqPlusSaSa (S a) =
  rewrite moveSInPlus2 (S a) in
  Refl

oneMoreFlipFromNatEqSb2NOAV : (a : Nat) -> (v : Bin) -> (S (S (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) = bin2Nat (oneMore (flipFromLeft (O a v))))
oneMoreFlipFromNatEqSb2NOAV Z BNil = Refl
oneMoreFlipFromNatEqSb2NOAV (S a) v =
  rewrite sym (add2NEqNP2 (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) in
  Refl
oneMoreFlipFromNatEqSb2NOAV Z (O a1 v1) =
  rewrite sym (add2NEqNP2 (plus (bin2Nat (O a1 v1)) (bin2Nat (O a1 v1))) (plus (bin2Nat (O a1 v1)) (bin2Nat (O a1 v1)))) in
  rewrite oneMoreXIs2X (oneMore (flipFromLeft (O a1 v1))) in
  rewrite sym (oneMoreFlipFromNatEqSb2NOAV a1 v1) in
  rewrite sym (add2NEqNP2 (S (S (plus (bin2Nat (O a1 v1)) (bin2Nat (O a1 v1))))) (S (plus (bin2Nat (O a1 v1)) (bin2Nat (O a1 v1))))) in
  rewrite sym (add2NEqNP2 (S (S (plus (bin2Nat (O a1 v1)) (bin2Nat (O a1 v1))))) (plus (bin2Nat (O a1 v1)) (bin2Nat (O a1 v1)))) in
  Refl

ssBin2NatOneMoreVEqPlus2XBin2NatFLipFromLeftV : (v : Bin) -> (S (S (bin2Nat (oneMore v))) = (plus (bin2Nat (flipFromLeft v)) (bin2Nat (flipFromLeft v))))
ssBin2NatOneMoreVEqPlus2XBin2NatFLipFromLeftV BNil = Refl
ssBin2NatOneMoreVEqPlus2XBin2NatFLipFromLeftV (O Z BNil) = Refl
ssBin2NatOneMoreVEqPlus2XBin2NatFLipFromLeftV (O (S a) v) =
  rewrite moveSInPlus2 (plus (bin2Nat (O a v)) (bin2Nat (O a v))) in
  Refl
ssBin2NatOneMoreVEqPlus2XBin2NatFLipFromLeftV (O Z (O a v)) =
  rewrite sym (oneMoreFlipFromNatEqSb2NOAV a v) in
  rewrite sym (add2NEqNP2 (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) in
  rewrite sym (add2NEqNP2 (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (S (plus (bin2Nat (O a v)) (bin2Nat (O a v))))) in
  rewrite sym (add2NEqNP2 (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) in
  Refl

canHalveAdds4Start : (v : Bin) -> S (S (S (S (plus (bin2Nat (oneMore v)) (bin2Nat (oneMore v)))))) = plus (plus (bin2Nat (flipFromLeft v)) (bin2Nat (flipFromLeft v))) (plus (bin2Nat (flipFromLeft v)) (bin2Nat (flipFromLeft v)))
canHalveAdds4Start v =
  canHalveAdds4 (bin2Nat (oneMore v)) (bin2Nat (flipFromLeft v)) (ssBin2NatOneMoreVEqPlus2XBin2NatFLipFromLeftV v)

canHalveAdds8Start : (v : Bin) -> S (S (plus (bin2Nat v) (bin2Nat v))) = bin2Nat (oneMore (flipFromLeft v))
canHalveAdds8Start BNil = Refl
canHalveAdds8Start (O a v) =
  rewrite oneMoreFlipFromNatEqSb2NOAV a v in
  Refl

moveAllS1 : (x : Nat) -> S (S (S (S (plus (plus (plus x x) (plus x x)) (plus (plus x x) (plus x x)))))) = S (plus (plus (plus x x) (S (plus x x))) (S (plus (plus x x) (S (plus x x)))))
moveAllS1 Z = Refl
moveAllS1 (S a) =
  rewrite sym (add2NEqNP2 a a) in
  rewrite sym (add2NEqNP2 (S (plus a a)) (S (S (plus a a)))) in
  rewrite sym (add2NEqNP2 (S (plus a a)) (S (plus a a))) in
  rewrite sym (add2NEqNP2 (S (plus a a)) (plus a a)) in
  rewrite sym (add2NEqNP2 (plus a a) (S (S (plus a a)))) in
  rewrite sym (add2NEqNP2 (plus a a) (S (plus a a))) in
  rewrite sym (add2NEqNP2 (plus a a) (plus a a)) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (S (plus (plus a a) (plus a a)))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (plus (plus a a) (plus a a))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (plus (plus a a) (plus a a)))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (plus (plus a a) (plus a a))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (S (S (S (plus (plus a a) (plus a a)))))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (S (S (plus (plus a a) (plus a a))))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (S (plus (plus a a) (plus a a)))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (plus (plus a a) (plus a a))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (plus (plus a a) (plus a a)))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (plus (plus a a) (plus a a))) in
  Refl

moveAllS2 : (x : Nat) -> S (S (S (S (S (plus (plus (plus x x) (S (plus x x))) (S (plus (plus x x) (S (plus x x))))))))) = S (S (S (S (S (S (S (S (plus (plus (plus x x) (plus x x)) (plus (plus x x) (plus x x))))))))))
moveAllS2 Z = Refl
moveAllS2 (S a) =
  rewrite sym (add2NEqNP2 a a) in
  rewrite sym (add2NEqNP2 (S (plus a a)) (S (S (plus a a)))) in
  rewrite sym (add2NEqNP2 (S (plus a a)) (S (plus a a))) in
  rewrite sym (add2NEqNP2 (S (plus a a)) (plus a a)) in
  rewrite sym (add2NEqNP2 (plus a a) (S (S (plus a a)))) in
  rewrite sym (add2NEqNP2 (plus a a) (S (plus a a))) in
  rewrite sym (add2NEqNP2 (plus a a) (plus a a)) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (S (plus (plus a a) (plus a a)))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (plus (plus a a) (plus a a))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (plus (plus a a) (plus a a)))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (plus (plus a a) (plus a a))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (S (S (S (plus (plus a a) (plus a a)))))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (S (S (plus (plus a a) (plus a a))))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (S (plus (plus a a) (plus a a)))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (plus (plus a a) (plus a a))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (plus (plus a a) (plus a a)))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (plus (plus a a) (plus a a))) in
  Refl

prove2XBin2NatFlipFromLeftVEqBin2NatOneMoreV : (v : Bin) -> S (S (S (S (plus (bin2Nat (oneMore v)) (bin2Nat (oneMore v)))))) = plus (plus (bin2Nat (flipFromLeft v)) (bin2Nat (flipFromLeft v))) (plus (bin2Nat (flipFromLeft v)) (bin2Nat (flipFromLeft v)))
prove2XBin2NatFlipFromLeftVEqBin2NatOneMoreV BNil = Refl
prove2XBin2NatFlipFromLeftVEqBin2NatOneMoreV (O Z BNil) = Refl
prove2XBin2NatFlipFromLeftVEqBin2NatOneMoreV (O (S a) BNil) =
  rewrite moveAllS1 (bin2Nat (O a BNil)) in Refl
prove2XBin2NatFlipFromLeftVEqBin2NatOneMoreV (O (S a) (O b w)) =
  rewrite moveAllS1 (bin2Nat (O a (O b w))) in Refl
prove2XBin2NatFlipFromLeftVEqBin2NatOneMoreV (O Z (O a v)) =
  rewrite moveAllS2 (bin2Nat (O a v)) in
  rewrite sym (oneMoreFlipFromNatEqSb2NOAV a v) in
  rewrite sym (add2NEqNP2 (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (S (plus (bin2Nat (O a v)) (bin2Nat (O a v))))) in
  rewrite sym (add2NEqNP2 (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) in
  rewrite sym (add2NEqNP2 (plus (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) (S (S (S (plus (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))))))) in
  rewrite sym (add2NEqNP2 (plus (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) (S (S (plus (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v))))))) in
  rewrite sym (add2NEqNP2 (plus (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) (S (plus (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))))) in
  rewrite sym (add2NEqNP2 (plus (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) (plus (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v))))) in
  Refl

testBin2Nat : (b : Bin) -> S (bin2Nat b) = bin2Nat (binInc b)
testBin2Nat BNil = Refl
testBin2Nat (O Z BNil) = Refl
testBin2Nat (O Z (O Z v)) =
  rewrite sym (add2NEqNP2 (plus (bin2Nat v) (bin2Nat v)) (plus (bin2Nat v) (bin2Nat v))) in
  rewrite oneMoreIsTwiceAsMuch v in
  rewrite oneMoreXIs2X (oneMore (flipFromLeft v)) in
  rewrite oneMoreXIs2X (oneMore v) in
  rewrite oneMoreXIs2X (flipFromLeft v) in
  rewrite canHalveAdds4Start v in Refl
testBin2Nat (O Z (O (S a) v)) =
  rewrite (add2NEqNP2 (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) in Refl
testBin2Nat (O (S a) BNil) = Refl
testBin2Nat (O (S a) (O b v)) = Refl

sAISBin2NatBinIncNat2BinA : (a : Nat) -> S a = bin2Nat (binInc (nat2Bin a))
sAISBin2NatBinIncNat2BinA Z = Refl
sAISBin2NatBinIncNat2BinA (S a) =
  rewrite sym (testBin2Nat (binInc (nat2Bin a))) in
  rewrite sAISBin2NatBinIncNat2BinA a in
  Refl

bin2NatIsReflexiveWithNat2Bin : (a : Nat) -> a = (bin2Nat (nat2Bin a))
bin2NatIsReflexiveWithNat2Bin Z = Refl
bin2NatIsReflexiveWithNat2Bin (S a) = 
  rewrite sAISBin2NatBinIncNat2BinA a in
  Refl

showBinInternal : Bin -> String
showBinInternal BNil = ""
showBinInternal (O Z v) = (assert_total (showBinInternal v)) ++ "1"
showBinInternal (O (S a) v) = (assert_total (showBinInternal (O a v))) ++ "0"

showBin : Bin -> String
showBin BNil = "0"
showBin x = showBinInternal x

public export
implementation Show Bin where
  show = showBin

Cast Bin Nat where
  cast = bin2Nat

Cast Nat Bin where
  cast = nat2Bin

binEq : Bin -> Bin -> Bool
binEq BNil BNil = True
binEq BNil (O b y) = False
binEq (O a x) BNil = False
binEq (O Z x) (O Z y) = assert_total (binEq x y)
binEq (O Z x) (O (S b) y) = False
binEq (O (S a) x) (O Z y) = False
binEq (O (S a) x) (O (S b) y) = assert_total (binEq (O a x) (O b y))

natEq : Nat -> Nat -> Bool
natEq Z Z = True
natEq (S n) Z = False
natEq Z (S n) = False
natEq (S n) (S m) = natEq n m

binEqAA : (a : Bin) -> binEq a a = True
binEqAA BNil =
  Refl
binEqAA (O Z v) =
  rewrite assert_total (binEqAA v) in
  Refl
binEqAA (O (S a) BNil) =
  rewrite assert_total (binEqAA (O a BNil)) in
  Refl
binEqAA (O (S a) v) =
  rewrite assert_total (binEqAA (O a v)) in
  Refl

Eq Bin where
  (==) = binEq
