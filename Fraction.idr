module Fraction

import NatExtras
import Singleton

%default total


mutual
    data Fraction : Nat -> Type where
        QZ : Fraction (S n)
        QR : (f: Fraction (S n)) -> {auto ok : LT (remainder f) n} -> Fraction (S n)
        QS : (f: Fraction (S n)) -> {auto ok : remainder f = n} -> Fraction (S n)

    remainder : Fraction n -> Nat
    remainder QZ = Z
    remainder (QS _) = Z
    remainder (QR f) = S (remainder f)

remainderLessThanBound : (f : Fraction (S n)) -> LTE (remainder f) n
remainderLessThanBound QZ = LTEZero
remainderLessThanBound (QS _) = LTEZero
remainderLessThanBound {n=S _} (QR {ok} _) = ok

quotient : Fraction n -> Nat
quotient QZ = Z
quotient (QS f) = S (quotient f)
quotient (QR f) = quotient f

fractionToNat : Fraction n -> Nat
fractionToNat QZ = Z
fractionToNat (QR f) = S (fractionToNat f)
fractionToNat (QS f) = S (fractionToNat f)

isLast : (f : Fraction (S n)) -> Either (LT (remainder f) n) (remainder f = n)
isLast {n=Z} QZ = Right Refl
isLast {n=S _} QZ = Left $ LTESucc LTEZero
isLast {n=Z} (QS f) = Right Refl
isLast {n=S _} (QS f) = Left $ LTESucc LTEZero
isLast {n=S k} (QR {ok=LTESucc ok} f) with (isLTE (remainder (QR f)) k)
    | Yes prf = Left $ LTESucc prf
    | No contra = Right $ cong $ eqProof ok contra

fractionSucc : Fraction (S n) -> Fraction (S n)
fractionSucc {n=Z} QZ = QS QZ
fractionSucc {n=S _} QZ = QR QZ
fractionSucc {n=Z} (QS f) = QS (QS f)
fractionSucc {n=S k} (QS f) = QR (QS f)
fractionSucc (QR f) with (isLast (QR f))
    | Left _ = QR (QR f)
    | Right _ = QS (QR f)

divMod : (m, n : Nat) -> {auto ok : GT n Z} -> Fraction n
divMod Z (S n) = QZ
divMod (S m) (S n) = fractionSucc $ divMod m (S n)

Cast (Fraction (S n)) Nat where
    cast f = fractionToNat f

Cast Nat (Fraction (S n)) where
    cast {n} m = divMod m (S n)

fractionToNatProp : (f : Fraction (S n)) -> quotient f * (S n) + remainder f = fractionToNat f
fractionToNatProp QZ = Refl
fractionToNatProp {n=Z} (QS {ok} f) = cong $ trans
    (sym $ cong {f=plus (mult (quotient f) 1)} ok)
    (fractionToNatProp f)
fractionToNatProp {n=S k} (QS {ok} f) =
    rewrite plusZeroRightNeutral (k + quotient f * S (S k)) in
        rewrite plusCommutative k (quotient f * S (S k)) in
            rewrite plusSuccRightSucc (quotient f * S (S k)) k in
                cong $ trans (sym $ cong {f=plus (quotient f * S (S k))} ok) (fractionToNatProp f)
fractionToNatProp {n=S k} (QR {ok} f) =
    rewrite sym $ plusSuccRightSucc (quotient f * S (S k)) (remainder f) in
        cong (fractionToNatProp f)

fractionToNatSucc : (f : Fraction (S n)) -> fractionToNat (fractionSucc f) = S (fractionToNat f)
fractionToNatSucc {n=Z} QZ = Refl
fractionToNatSucc {n=S _} QZ = Refl
fractionToNatSucc {n=Z} (QS _) = Refl
fractionToNatSucc {n=S _} (QS _) = Refl
fractionToNatSucc {n=S k} (QR {ok=LTESucc _} f) with (isLTE (remainder (QR f)) k)
    | Yes _ = Refl
    | No _ = Refl

divModProp : fractionToNat (divMod m (S n)) = m
divModProp {m=Z} = Refl
divModProp {m=S m} {n} = trans (fractionToNatSucc (divMod m (S n))) (cong $ divModProp {m})

remainderOneIfZero : (f : Fraction 1) -> remainder f = Z
remainderOneIfZero QZ = Refl
remainderOneIfZero (QS _) = Refl
remainderOneIfZero (QR {ok} _) = absurd ok

fractionSuccOneIsQS : (f : Fraction 1) -> {auto ok : remainder f = Z} -> QS f {ok} = fractionSucc f
fractionSuccOneIsQS QZ {ok=Refl} = Refl
fractionSuccOneIsQS (QS _) {ok=Refl} = Refl
fractionSuccOneIsQS (QR {ok} _) = absurd ok

fractionSuccIsQS : (f : Fraction (S n)) -> {auto ok : remainder f = n} -> QS f = fractionSucc f
fractionSuccIsQS QZ {ok=Refl} = Refl
fractionSuccIsQS (QS _) {ok=Refl} = Refl
fractionSuccIsQS (QR f) {n} {ok} with (isLast (QR f))
    | Left prf = absurd $ replace {P=\x=>LTE (S x) n} ok prf
    | Right prf = rewrite singleton ok prf in Refl

fractionSuccIsQR : (f : Fraction (S n)) -> {auto ok : LT (remainder f) n} -> QR f = fractionSucc f
fractionSuccIsQR {n=Z} _ {ok} = absurd ok
fractionSuccIsQR {n=S _} QZ {ok=LTESucc LTEZero} = Refl
fractionSuccIsQR {n=S _} (QS _) {ok=LTESucc LTEZero} = Refl
fractionSuccIsQR (QR f) {n} {ok} with (isLast (QR f))
    | Left prf = rewrite singleton ok prf in Refl
    | Right prf = absurd $ replace {P=\x=>LTE (S x) n} prf ok

divModInjective : (f : Fraction (S n)) -> f = divMod (fractionToNat f) (S n)
divModInjective QZ = Refl
divModInjective {n=Z} (QS f) = trans (fractionSuccOneIsQS f) $ cong {f=fractionSucc} $ divModInjective f
divModInjective {n=S k} (QS {ok} f) with (isLast f)
    | Left (LTESucc prf) = absurd $ replace {P=\x=>LTE x k} ok prf
    | Right _ = trans (fractionSuccIsQS f) $ cong {f=fractionSucc} $ divModInjective f
divModInjective {n=S _} (QR {ok=LTESucc _} f) = trans (fractionSuccIsQR f) $ cong $ divModInjective f

remainderIsSucc : (f : Fraction (S n)) -> {auto ok : LT (remainder f) n} -> remainder (fractionSucc f) = S (remainder f)
remainderIsSucc f = sym $ cong {f=remainder} $ fractionSuccIsQR f

remainderDivOneIsZero : (n : Nat) -> remainder (divMod n 1) = Z
remainderDivOneIsZero n = lteZeroHenceZero $ remainderLessThanBound $ divMod n (S Z)

remainderDoubleIsSame : (f : Fraction (S n)) -> remainder (divMod (remainder f) (S n)) = remainder f
remainderDoubleIsSame QZ = Refl
remainderDoubleIsSame {n=Z} (QR {ok} _) = absurd ok
remainderDoubleIsSame {n=S n} (QR {ok=LTESucc ok} f) with (isLast f)
    | Left _ = let lte = replace {P=\x=>LTE x n} (sym $ remainderDoubleIsSame f) ok in
        trans (remainderIsSucc (divMod (remainder f) (S (S n))) {ok=LTESucc lte}) (cong $ remainderDoubleIsSame f)
    | Right prf = absurd $ replace {P=\x=>LTE x n} prf ok
remainderDoubleIsSame {n=Z} (QS _) = Refl
remainderDoubleIsSame {n=S _} (QS _) = Refl

div' : (m, n : Nat) -> {auto ok : GT n Z} -> Nat
div' m (S n) = quotient $ divMod m (S n)

mod' : (m, n : Nat) -> {auto ok : GT n Z} -> Nat
mod' m (S n) = remainder $ divMod m (S n)

divModSucc : divMod (S m) (S n) = fractionSucc (divMod m (S n))
divModSucc {n=Z} = Refl
divModSucc {n=S _} {m=Z} = Refl
divModSucc {n=S n} {m=S m} with (isLast (divMod m (S n)))
    | Left _ = Refl
    | Right _ = Refl

plus' : Fraction n -> Fraction n -> Fraction n
plus' QZ right = right
plus' (QR left) right = fractionSucc $ plus' left right
plus' (QS left) right = fractionSucc $ plus' left right

plusZeroRightNeutral' : (f : Fraction (S n)) -> f = plus' f QZ
plusZeroRightNeutral' QZ = Refl
plusZeroRightNeutral' {n=Z} (QR {ok} _) = absurd ok
plusZeroRightNeutral' {n=S _} (QR f) = trans
    (fractionSuccIsQR f)
    (cong {f=fractionSucc} $ plusZeroRightNeutral' f)
plusZeroRightNeutral' {n=Z} (QS f) = trans
    (fractionSuccIsQS f)
    (cong {f=fractionSucc} $ plusZeroRightNeutral' f)
plusZeroRightNeutral' {n=S _} (QS f) = trans
    (fractionSuccIsQS f)
    (cong {f=fractionSucc} $ plusZeroRightNeutral' f)

plusSuccRightSucc' : (left, right : Fraction (S n)) -> fractionSucc (plus' left right) = plus' left (fractionSucc right)
plusSuccRightSucc' QZ right = Refl
plusSuccRightSucc' (QR left) right = cong $ plusSuccRightSucc' left right
plusSuccRightSucc' (QS left) right = cong $ plusSuccRightSucc' left right

divModPlus : divMod (m1 + m2) (S n) = plus' (divMod m1 (S n)) (divMod m2 (S n))
divModPlus {m1=Z} {m2=Z} = Refl
divModPlus {m1=Z} {m2=S m} = Refl
divModPlus {n} {m1=S m} {m2=Z} = rewrite plusZeroRightNeutral m in
    plusZeroRightNeutral' $ fractionSucc $ divMod m (S n)
divModPlus {n} {m1=S m1} {m2=S m2} =
    rewrite sym (plusSuccRightSucc m1 m2) in trans
        (cong {f=fractionSucc} $ divModPlus {m1=S m1} {m2} {n})
        (plusSuccRightSucc' (fractionSucc (divMod m1 (S n))) (divMod m2 (S n)))

divPlusBoundSucc : div' (S n + m) (S n) = S (div' m (S n))

divMult : div' (S k * m) (S k * S n) = div' m (S n)
divMult {k=Z} {m} {n} =
    rewrite plusZeroRightNeutral m in
        rewrite plusZeroRightNeutral n in
            Refl
divMult {k=S k} {m=Z} = rewrite multZeroRightZero k in Refl
divMult {k=S k} {m=S m} {n} = ?h3

modPreservesSum : (m1, m2, n : Nat) -> mod' (mod' m1 (S n) + mod' m2 (S n)) (S n) = mod' (m1 + m2) (S n)
modPreservesSum m1 m2 Z =
    rewrite remainderDivOneIsZero m1 in
        rewrite remainderDivOneIsZero m2 in
            rewrite remainderDivOneIsZero (m1 + m2) in Refl
modPreservesSum Z Z (S n) = Refl
modPreservesSum (S m) Z (S n) = rewrite plusZeroRightNeutral m in
    rewrite plusZeroRightNeutral (remainder (fractionSucc (divMod m (S (S n))))) in
        remainderDoubleIsSame (fractionSucc (divMod m (S (S n))))
modPreservesSum Z (S m) (S n) = remainderDoubleIsSame (fractionSucc (divMod m (S (S n))))
modPreservesSum (S m1) (S m2) (S n) = ?h (modPreservesSum m1 (S m2) (S n))