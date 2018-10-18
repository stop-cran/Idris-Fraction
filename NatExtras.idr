module NatExtras

%default total
%access public export


eqProof : LTE n k -> Not (LTE (S n) k) -> n = k
eqProof {k=Z} LTEZero contra = Refl
eqProof {k=S _} LTEZero contra = void $ contra $ LTESucc LTEZero
eqProof {k=S _} (LTESucc lte) contra = cong $ eqProof lte $ contra . LTESucc

lteProof : LTE n k -> Not (n = k) -> LT n k
lteProof {k=Z} LTEZero contra = void $ contra Refl
lteProof {k=S _} LTEZero contra = LTESucc LTEZero
lteProof {k=S _} (LTESucc lte) contra = LTESucc $ lteProof lte $ contra . cong

lteDecidable : LTE n k -> Either (LT n k) (n = k)
lteDecidable {k=Z} LTEZero = Right Refl
lteDecidable {k=S k} LTEZero = Left $ LTESucc LTEZero
lteDecidable (LTESucc lte) with (lteDecidable lte)
        | Left prf = Left $ LTESucc prf
        | Right prf = Right $ cong prf

Uninhabited (LTE (S n) n) where
    uninhabited (LTESucc lte) = uninhabited lte
        
ltNot : LT n k -> Not (n = k)
ltNot {k=Z} lte = absurd lte
ltNot {k=S k} (LTESucc lte) = \eq => uninhabited $ replace {P=\x=>LTE x k} eq lte

notZeroHenceNotLteZero : Not (n = Z) -> Not (LTE n Z)
notZeroHenceNotLteZero {n=Z} contra = void $ contra $ Refl
notZeroHenceNotLteZero {n=S k} contra = succNotLTEzero

lteZeroHenceZero : LTE n Z -> n = Z
lteZeroHenceZero LTEZero = Refl
