module Proposition


%default total
%access public export

interface Proposition t where
    atMostOneValue : (x : t) -> (y : t) -> x = y

Proposition (x = y) where
    atMostOneValue Refl Refl = Refl

Proposition (LTE m n) where
    atMostOneValue {m=Z} LTEZero LTEZero = Refl
    atMostOneValue {m=S _} (LTESucc x) (LTESucc y) = cong $ atMostOneValue x y
