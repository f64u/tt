module Paradoxes

%default total

contradiction : True = False -> Void
contradiction prf = uninhabited prf

Set : Type

set_cons : Set

set_contains : (s : Set) -> (u : Type) -> u -> Bool

does_not_contain_itself : Set -> Type
does_not_contain_itself s = ((set_contains s Set s) = False)

does_not_contain_itself_cons : (s : Set) -> (does_not_contain_itself s)

set_of_sets_that_dont_contain_themselves : 
    (s : Set) -> 
    (a : Set) -> 
    (prf : (does_not_contain_itself a)) -> 
    Type
set_of_sets_that_dont_contain_themselves s a prf = ((set_contains s Set a) = True)

set_of_sets_that_dont_contain_themselves_cons : 
    (s : Set) -> 
    (a : Set) -> 
    (prf : (does_not_contain_itself a)) -> 
    set_of_sets_that_dont_contain_themselves s a prf

russell_lem : (s : Set) -> 
    set_contains s Set s = False -> 
    set_contains s Set s = True -> 
    Void
russell_lem s prf prf1 = contradiction 
    (rewrite sym (prf) in 
    sym (prf1))
    

russell : Void
russell = 
    let not_in_itself = (does_not_contain_itself_cons set_cons) in
    russell_lem 
        set_cons 
        not_in_itself 
        (set_of_sets_that_dont_contain_themselves_cons 
            set_cons set_cons not_in_itself)
