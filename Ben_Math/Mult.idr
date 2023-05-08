module Mult

import Plus

%default total

public export
mult_comm : (x : Nat) -> (y : Nat) -> x * y = y * x

public export
mult_distr : (x : Nat) -> (y : Nat) -> (z : Nat) -> x * (y + z) = (x * y) + (x * z)
mult_distr 0 y z = Refl
mult_distr (S k) y z = 
    rewrite mult_distr k y z in
    rewrite sym (plus_assoc (y + z) (k * y) (k * z)) in
    Refl

public export
mult_assoc : (x : Nat) -> (y : Nat) -> (z : Nat) -> (x * y) * z = x * (y * z)
mult_assoc 0 y z = Refl
mult_assoc (S k) y z = 
    rewrite sym (mult_comm z (y + (k * y))) in 
    rewrite mult_distr z y (k * y) in 
    rewrite sym (mult_assoc k y z) in 
    rewrite mult_comm y z in
    rewrite mult_comm (k * y) z in
    Refl

public export
mult_comm_z : (x : Nat) -> mult x 0 = 0
mult_comm_z 0 = Refl
mult_comm_z (S k) = mult_comm_z k

public export
mult_one_id : (x : Nat) -> mult x 1 = x
mult_one_id 0 = Refl
mult_one_id (S k) = cong S (mult_one_id k)

mult_comm x 0 = mult_comm_z x
mult_comm x (S k) = 
    let add1 = suc_eq_plus_one k in 
    rewrite add1 in 
    let distr = mult_distr x k 1 in
    rewrite distr in 
    let add_comm = plus_comm x (k * x) in
    rewrite add_comm in 
    rewrite mult_one_id x in 
    rewrite mult_comm x k in
    Refl
