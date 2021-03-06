# Tools for the &rho;-property of combinators

A combinator, higher-order function given by a closed &lambda;-term,
is said to have the _&rho;-property_ if the combinator X satisfies
X<sub>m</sub> and X<sub>n</sub> are &beta;&eta;-equivalent for distinct m and n,
where X<sub>n</sub> is defined by X<sub>1</sub> = X
and X<sub>n</sub> = X<sub>n-1</sub> X for n > 1.

Three programs `rho`, `bpoly` and `bmono` are available here.

## Requirement and how to build

Each program can be built by `make` with the name of the target program,
e.g., `make rho`.
You may build all programs just by `make` as far as requirements are satisfied.

- For `rho`,
OCaml (&ge; 4.08) and CamlP5 are required 
- For `bpoly`,
OCaml (&ge; 4.08), CamlP5 and [Zarith](https://github.com/ocaml/Zarith) are required.
- For `bmono`,
a standard C compiler is required.


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
add the `-u` option for keeping on trying to find the cycle.
Using the `-f` option,
Floyd's (also called tortoise-and-hare) semi-algorithm is used
for finding cycles with constant memory usage.
Run
```
$ rho -h
```
for details of command line options.

## Program `bpoly`

The program `bpoly` checks the &rho;-property of a B-term.
The implementation is based on the normal form of B-terms
in the 'decreasing polynomial' representation
&#91;[1](#fscd18)&#93; of the form
(B<sup>m<sub>1</sub></sup> B) o
(B<sup>m<sub>2</sub></sup> B) o ... o
(B<sup>m<sub>k</sub></sup> B),
with m<sub>1</sub> &ge; m<sub>2</sub> &ge;...&ge; m<sub>k</sub> &ge; 0
where B<sup>n</sup> stands fold n-fold composition of B,
e.g., (B<sup>3</sup> B) stands B(B(B B)).
To check the &rho;-property of B<sup>2</sup> B,
run
```
$ bpoly 2
```
which results in (B<sup>2</sup> B)<sub>294</sub> = (B<sup>2</sup> B)<sub>258</sub>
with the history of computation over decreasing polynomials.
To check the &rho;-property of
(B<sup>2</sup> B) o (B<sup>2</sup> B) o (B<sup>1</sup> B) o
(B<sup>1</sup> B) o (B<sup>0</sup> B) o (B<sup>0</sup> B),
run
```
$ bpoly 2 2 1 1 0 0
```
which does not terminate up to the given limit of repetition (65535 by default)
because it does not have the &rho;-property as shown our paper &#91;[1](#fscd18)&#93;.
Command line options similar to those of `rho` are available.
It is better to add the `-f` or `-b` option for larger n so as to use Floyd's or Brent's cycle-finding algorithm.
Run
```
$ bpoly -h
```
for details of command line options.

## Program `bmono`

The program `bmono` checks the &rho;-property of a monomial B-term
of the form B<sup>m</sup> B where m is given as an argument.
To check the &rho;-property of B<sup>2</sup> B,
run
```
$ bmono 2
```
in a similar way to `bpoly`.
The program `bmono` is written in C and specialized for checking monomial B-terms,
so it may run faster than `bpoly`.
The program `bpoly` should be used for observing the divergence of repetitive right application of non-monomial B-terms
because only monomial B-terms have the &rho;-property
as conjectured below.

# Conjecture

Keisuke Nakano conjectured in 2008 &#91;[2](#trs08)&#93; that

> a B-term has the &rho;-property if and only if it is equivalent to B<sup>n</sup> B with some n.

in which if-part and only-if-part are both still open.

## if-part
For every n &le; 6, it is known that B<sup>n</sup> B has the &rho;-property.
- (B<sup>0</sup> B)<sub>10</sub> = (B<sup>0</sup> B)<sub>6</sub>
- (B<sup>1</sup> B)<sub>52</sub> = (B<sup>1</sup> B)<sub>32</sub>
- (B<sup>2</sup> B)<sub>294</sub> = (B<sup>2</sup> B)<sub>258</sub>
- (B<sup>3</sup> B)<sub>10036</sub> = (B<sup>3</sup> B)<sub>4240</sub>
- (B<sup>4</sup> B)<sub>622659</sub> = (B<sup>4</sup> B)<sub>191206</sub>
- (B<sup>5</sup> B)<sub>1000685878</sub> = (B<sup>5</sup> B)<sub>766241307</sub>
- (B<sup>6</sup> B)<sub>2980054085040</sub> = (B<sup>6</sup> B)<sub>2641033883877</sub>

All of the above can be confirmed by running the `bpoly` program.
It took 8 days to check the &rho;-property of the case n=6.

## only-if-part
It is shown that the following B-terms do not have the &rho;-property.
- (B<sup>k</sup> B)<sup>(k+2)n</sup> with k&ge;0 and n&gt;0
- (B<sup>2</sup> B)<sup>2</sup> o (B<sup>1</sup> B)<sup>2</sup> o (B<sup>0</sup> B)<sup>2</sup>
- (B<sup>1</sup> B)<sup>3</sup> o (B<sup>0</sup> B)<sup>3</sup>

The proofs are found in &#91;[1](#fscd18)&#93; and &#91;[3](#lmcs20)&#93;.

---
<a name="fscd18">&#91;1&#93;</a> Mirai Ikebuchi and Keisuke Nakano. [On Repetitive Right Application of B-terms](https://doi.org/10.4230/LIPIcs.FSCD.2018.18), _In the proceedings of [the 3rd International Conference on Formal Structures for Computation and Deduction (FSCD 2018)](https://www.cs.le.ac.uk/events/fscd2018/)_, pp.18:1-18:15, Oxford, UK, July 2018.

<a name="trs08">&#91;2&#93;</a> Keisuke Nakano. &rho;-Property of Combinators, _[29th TRS Meeting](http://www.jaist.ac.jp/~hirokawa/trs-meeting/original/29.html)_, Tokyo, 2008.

<a name="lmcs20">&#91;3&#93;</a> Mirai Ikebuchi and Keisuke Nakano. [On Properties of B-terms](https://doi.org/10.23638/LMCS-16(2:8)2020), _[Logical Methods in Computer Science (LMCS)](https://lmcs.episciences.org)_, Volume 16, Issue 2, June 2020.
