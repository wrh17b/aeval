About
=====

A prototype of the synthsizer of relational invariants over list-based ADTs and Arrays.

Installation
============

Compiles with gcc-5 (on Linux) and clang-700 (on Mac). Assumes preinstalled Gmp and Boost (libboost-system1.55-dev) packages.

* `cd aeval ; mkdir build ; cd build`
* `cmake ../`
* `make` to build dependencies (Z3 and LLVM)
* `make` to build the core code

The binary can be found in `build/tools/sim/`.

Running Benchmarks:
==========

`# "stacks"`

`echo Benchmark 1`

`./tools/sim/sim ../bench_sim/src/stack_list.smt2 ../bench_sim/src/stack_arr.smt2`

`echo Benchmark 2`

`./tools/sim/sim ../bench_sim/src/stack_list.smt2 ../bench_sim/src/stack_arr_2.smt2`

`echo Benchmark 3`

`./tools/sim/sim ../bench_sim/src/stack_list_double.smt2 ../bench_sim/src/stack_arr_double.smt2`

`echo Benchmark 4`

`./tools/sim/sim ../bench_sim/src/stack_list_double_1.smt2 ../bench_sim/src/stack_arr_double_1.smt2`

`echo Benchmark 5`

`./tools/sim/sim ../bench_sim/src/stack_list_double_2.smt2 ../bench_sim/src/stack_arr_double_2.smt2`

`echo Benchmark 6`

`./tools/sim/sim ../bench_sim/src/stack_list_double_3.smt2 ../bench_sim/src/stack_arr_double_3.smt2`



`# "queues"`

`echo Benchmark 7`

`./tools/sim/sim ../bench_sim/src/queue_list.smt2 ../bench_sim/src/queue_arr.smt2`

`echo Benchmark 8`

`./tools/sim/sim ../bench_sim/src/queue_list.smt2 ../bench_sim/src/queue_arr_2.smt2`

`echo Benchmark 9`

`./tools/sim/sim ../bench_sim/src/queue_revlist.smt2 ../bench_sim/src/queue_arr.smt2`



`# "sets"`

`echo Benchmark 10`

`./tools/sim/sim ../bench_sim/src/set_list_2.smt2 ../bench_sim/src/set_arr.smt2`

`echo Benchmark 11`

`./tools/sim/sim ../bench_sim/src/set_list.smt2 ../bench_sim/src/set_arr.smt2`



`# "multisets"`

`echo Benchmark 12`

`./tools/sim/sim ../bench_sim/src/multiset_list.smt2 ../bench_sim/src/multiset_arr.smt2`

`echo Benchmark 13`

`./tools/sim/sim ../bench_sim/src/multiset_list_2.smt2 ../bench_sim/src/multiset_arr_2.smt2`



`# "maps"`

`echo Benchmark 14`

`./tools/sim/sim ../bench_sim/src/map_list.smt2 ../bench_sim/src/map_arr.smt2`

`echo Benchmark 15`

`./tools/sim/sim ../bench_sim/src/map_list_2.smt2 ../bench_sim/src/map_arr.smt2`





Synthesized Invariants:
==========



`Benchmark 1`

`(assert (forall ((n Int) (A (Array Int Elem))) (= (R nil n A) (= n 0))))`

`(assert (forall ((xs Lst) (in Elem) (n Int) (A (Array Int Elem))) (= (R (cons in xs) n A) (and (<= 0 n) (distinct n 0) (= in (select A (- n 1))) (R xs (- n 1) A)))))`

`Benchmark 2`

`(assert (forall ((n Int) (A (Array Int Elem))) (= (R nil n A) (= n 5))))`

`(assert (forall ((xs Lst) (in Elem) (n Int) (A (Array Int Elem))) (= (R (cons in xs) n A) (and (<= 5 n) (distinct n 5) (= in (select A (+ (- 2) n))) (R xs (+ (- 2) n) A)))))`

`Benchmark 3`

`(assert (forall ((n Int) (A (Array Int Elem))) (= (R nil n A) (= n 0))))`

`(assert (forall ((xs Lst) (in Elem) (n Int) (A (Array Int Elem))) (= (R (cons in xs) n A) (and (<= 0 n) (distinct n 0) (= in (select A (- n 1))) (R xs (- n 1) A)))))`

`Benchmark 4`

`(assert (forall ((n Int) (A (Array Int Elem))) (= (R nil n A) (= n 0))))`

`(assert (forall ((xs Lst) (in2 Elem) (n Int) (A (Array Int Elem))) (= (R (cons in2 xs) n A) (and (<= 0 n) (distinct n 0) (= in2 (select A (- n 1))) (R xs (- n 1) A)))))`

`Benchmark 5`

`(assert (forall ((n Int) (A (Array Int Elem))) (= (R nil n A) (= n 0))))`

`(assert (forall ((xs Lst) (in2 Elem) (n Int) (A (Array Int Elem))) (= (R (cons in2 xs) n A) (and (<= 0 n) (distinct n 0) (= in2 (select A (- n 1))) (R xs (- n 1) A)))))`

`Benchmark 6`

`(assert (forall ((n Int) (A (Array Int Elem))) (= (R nil n A) (= n 0))))`

`(assert (forall ((xs Lst) (in Elem) (n Int) (A (Array Int Elem))) (= (R (cons in xs) n A) (and (<= 0 n) (distinct n 0) (= in (select A (- n 1))) (R xs (- n 1) A)))))`



`Benchmark 7`

`(assert (forall ((n Int) (m Int) (A (Array Int Elem))) (= (R nil n m A) (= n m))))`

`(assert (forall ((xs Lst) (in Elem) (n Int) (m Int) (A (Array Int Elem))) (= (R (cons in xs) n m A) (and (<= m n) (distinct n m) (= in (select A (- n 1))) (R xs (- n 1) m A)))))`

`Benchmark 8`

`(assert (forall ((n Int) (m Int) (A (Array Int Elem))) (= (R nil n m A) (= n (+ m 1)))))`

`(assert (forall ((xs Lst) (in Elem) (n Int) (m Int) (A (Array Int Elem))) (= (R (cons in xs) n m A) (and (<= (+ m 1) n) (distinct n (+ m 1)) (= in (select A (+ (- 2) n))) (R xs (+ (- 2) n) m A)))))`

`Benchmark 9`

`(assert (forall ((n Int) (m Int) (A (Array Int Elem))) (= (R nil n m A) (= n m))))`

`(assert (forall ((xs Lst) (out Elem) (n Int) (m Int) (A (Array Int Elem))) (= (R (cons out xs) n m A) (and (= out (select A m)) (<= m n) (distinct n m) (R xs n (+ 1 m) A)))))`



`Benchmark 10`

`(assert (forall ((s (Array Elem Bool)) (a Elem)) (= (R nil s) (forall ((a Elem)) (not (select s a))))))`

`(assert (forall ((xs Lst) (in Elem) (s (Array Elem Bool))) (= (R (cons in xs) s) (and (select s in) (R xs (store s in false))))))`

`Benchmark 11`

`(assert (forall ((s (Array Elem Bool)) (a Elem)) (= (R nil s) (forall ((a Elem)) (not (select s a))))))`

`(assert (forall ((xs Lst) (in Elem) (s (Array Elem Bool))) (= (R (cons in xs) s) (and (select s in) (ite (contains in xs) (R xs s) (R xs (store s in false)))))))`



`Benchmark 12`

`(assert (forall ((s (Array Elem Int)) (a Elem)) (= (R nil s) (forall ((a Elem)) (= (select s a) 0)))))`

`(assert (forall ((xs Lst) (in Elem) (s (Array Elem Int))) (= (R (cons in xs) s) (and (R xs (store s in (+ (- 1) (select s in)))) (= (select s in) (+ (num in xs) 1))))))`

`Benchmark 13`

`(assert (forall ((s (Array Elem Int)) (a Elem)) (= (R nil s) (forall ((a Elem)) (= (select s a) 0)))))`

`(assert (forall ((xs Lst) (in Elem) (s (Array Elem Int))) (= (R (cons in xs) s) (and (R xs (store s in (+ (- 1) (select s in)))) (= (select s in) (+ (num in xs) 1))))))`



`Benchmark 14`

`(assert (forall ((s (Array Key Value)) (a Key)) (= (R nil s) (forall ((a Key)) (= (empty 0) (select s a))))))`

`(assert (forall ((xs Lst) (in Key) (s (Array Key Value)) (_x_2 Value)) (= (R (cons (pair in _x_2) xs) s) (and (R xs (store s in (empty 0))) (= (select s in) _x_2)))))`

`Benchmark 15`

`(assert (forall ((s (Array Key Value)) (a Key)) (= (R nil s) (forall ((a Key)) (= (empty 0) (select s a))))))`

`(assert (forall ((xs Lst) (in Key) (inv Value) (s (Array Key Value))) (= (R (cons (pair in inv) xs) s) (and (R xs (store s in (get in xs))) (= (select s in) inv)))))`
