module Incon

data T : Type where
  T0 : (X : Type) -> (f : X -> T) -> T

inside : T -> T -> Type
a `inside` (T0 t f) = (x : t ** a = f x)

notinside : T -> T -> Type
a `notinside` b = Not (a `inside` b) 

Russell : T
Russell = T0 (t : T ** t `notinside` t) fst

t_notin_russell : t `inside` Russell -> t `notinside` t
t_notin_russell ((_ ** ynotiny) ** Refl) = ynotiny

russell_notin_russell : Russell `notinside` Russell
russell_notin_russell rinr = t_notin_russell rinr rinr

t_notin_t : {t : T} -> t `notinside` t -> t `inside` Russell
t_notin_t {t} tnint = ((t ** tnint) ** Refl)

falso : Void
falso = russell_notin_russell (t_notin_t russell_notin_russell)
