# Tools for the &rho;-property of combinators

A combinator, higher-order function given by a closed &lambda;-term,
is said to have the &rho;-property if the combinator X satisfies
X<sub>m</sub> and X<sub>n</sub> are &beta;&eta;-equivalent for distinct m and n,
where X<sub>n</sub> is defined by X<sub>1</sub> = X
and X<sub>n</sub> = X<sub>n-1</sub> X for n > 1.

Two programs `rho` and `bfast` are available here.

## Requirement and how to build

OCaml (&ge; 4.00) is required for building the programs.
Both can be built just by `make`.

## Program `rho`

The program `rho` checks the &rho;-property of arbitrary combinators.
For example, the &rho;-property of B, B<sub>10</sub> = B<sub>6</sub>, is
checked by
```
$ rho B
```
where `$` denotes the command prompt.
To check B(B B), run
```
$ rho 'B(B B)'
```
simply.
Available combinators can be seen by
```
$ rho -l
```
where `\x[...]` represents &lambda;-abstraction.
This syntax of &lambda;-abstraction can be used for combinators given by users.
Use the `-q` option for the quiet mode.
Although the program only checks first 65535 terms by default,
add the `-m` option for keeping on trying to find the cycle.
Using the `-fx` option,
the Floyd's (also called tortoise-and-hare) semi-algorithm is used
for finding cycles with constant memory usage.
Run
```
$ rho -h
```
for details of command line options.

## Program `bfast`

The program `bfast` checks the &rho;-property of B-terms
which has the form B<sup>n</sup> B
where f<sup>n</sup> means the n-fold composition of f.
The implementation is based on the normal form of B-terms
in the list representation,
B<sup>m<sub>1</sub></sup> B o
B<sup>m<sub>2</sub></sup> B o ... o
B<sup>m<sub>k</sub></sup> B,
with m<sub>1</sub> &ge; m<sub>2</sub> &ge;...&ge; m<sub>k</sub> &ge; 0.
This command also uses Floyd's cycle-finding algorithm.
To check the &rho;-property of B<sup>2</sup> B,
run
```
$ bfast 2
```
which results in (B<sup>2</sup> B)<sub>294</sub> = (B<sup>2</sup> B)<sub>258</sub>
with the history of computation over the list representation.
Command line options similar to those of `rho` are available.
It is better to use the `-fx` option for larger n.
Run
```
$ bfast -h
```
for details of command line options.


