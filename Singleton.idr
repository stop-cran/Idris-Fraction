module Singleton


%default total
%access public export

interface Singleton t where
    singleton : (x : t) -> (y : t) -> x = y

Singleton (x = y) where
    singleton Refl Refl = Refl

Singleton (LTE m n) where
    singleton {m=Z} LTEZero LTEZero = Refl
    singleton {m=S _} (LTESucc x) (LTESucc y) = cong $ singleton x y
