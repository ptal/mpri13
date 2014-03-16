mpri13
======

ML type inference in presence of type classes

Student
=======

Pierre Talbot

Project notes
=============

* Task 1 to 3 are done.
* Many tests are added.

* 2 tests failing:
  - elaboration/bad/typeclass_local_let_bound_and_overload.mle
  - elaboration/bad/typeclass_overload_and_let_bound.mle

* Example of a quite nasty case handled (file elaboration/good/typeclass_couple_eq.mle):

type ('a, 'b) couple = Couple of 'a * 'b

let (l1 : int list) = (Cons[int](9, Cons[int](1, Nil[int])))
let (l2 : int list) = (Cons[int](1, Cons[int](1, Nil[int])))

let (c1 : (int list, int list) couple) = (Couple[int list, int list](l1[], l1[]))
let (c2 : (int list, int list) couple) = (Couple[int list, int list](l1[], l2[]))

let (res1 : boolean) = equal[(int list, int list) couple] c1[] c1[]
let (res2 : boolean) = equal[(int list, int list) couple] c1[] c2[]

> val res1 : boolean = true
> val res2 : boolean = false
