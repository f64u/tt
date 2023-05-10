module Incon

data T : Type where
  T0 : (X : Type) -> (f : (x : X) -> T) -> T

phi : T
phi = T0 Void (\v => absurd v)

set_of_phi : T
set_of_phi = T0 () (\_ => phi)

V2 : T
V2 = T0 Bool (\x => if x then phi else set_of_phi)

inside : T -> T -> Type
a `inside` (T0 t f ) = (x : t ** a = f x)

notinside : T -> T -> Type
a `notinside` b = Not (a `inside` b) 

Russell : T
Russell = T0 (t : T ** t `notinside` t) fst

t_notin_russell : x `inside` Russell -> x `notinside` x
t_notin_russell ((y ** ynotiny) ** Refl) = ynotiny

russell_notin_russell : Russell `notinside` Russell
russell_notin_russell rinr = t_notin_russell rinr rinr

x_notin_x : {x : T} -> x `notinside` x -> x `inside` Russell
x_notin_x {x} xninx = ((x ** xninx) ** Refl)

falso : Void
falso = russell_notin_russell (x_notin_x russell_notin_russell)