# Testify
Testify is a syntactic extension that features type driven code
generation to automatically generate test for your programs. It allows
you to attach a property to a given type, as in the following example:

```OCaml
type p_int = int [@@satisfying (fun x -> x > 0)]
```

Which is to be understood as the type of *positive integers*. Of
course, OCaml's type system cannot type-check this kind of property,
however we can test them!  To do so, Testify uses the explicit type
annotations of your program to generate tests for the values whose
return type is ```p_int```, as in the following example.

```OCaml
let abs (x:int) : p_int = if x < 0 then -x else x
```
is now rewritten into:

```OCaml
let abs (x:int) : p_int = if x < 0 then -x else x

let _ = QCheck.Test.make (QCheck.make QCheck.Gen.int) (fun x1 -> ((<) 0) (abs x1))
```

As you noticed, a test has been added after the declaration of
```abs``` to check that its return values are indeed positive
integers. As you also noticed, Testify uses the wonderful
[QCheck](https://github.com/c-cube/qcheck) library do the tests. Other
examples are available in the examples directory.

### Usage
Testify is defined following the inline-test backend facility of
[dune](https://dune.readthedocs.io/en/stable/tests.html#defining-your-own-inline-test-backend),
thus you can simply add the following to your stanza in your dune file

```
(preprocess (pps ppx_testify))
(inline_tests (backend ppx_testify))
```

and run the generated tests by doing `dune runtest`.  You might need
to add the `--no-buffer` option in case dune messes with the colored
output. You can see examples of utilisation in the examples directory.

Also, Testify accepts the `-nb` option to change the number of runs per generated test, which you can pass through dune by doing:

```
(preprocess (pps ppx_testify -- -nb 42))
```

or using shell environment variables with dune's syntax :

```
(preprocess (pps ppx_testify -- -nb %{env:NB=42}))
```

which sets the number of runs to `$(NB)` if the variable `NB` is defined, and to `42` otherwise.
You can then do for example `NB=100 dune runtest`

#### Complete list of options:
- `-nb x` Sets the number of runs per test to `x`
- `-log`  Ouputs a pre-processing report
- `-seed s` Sets the random seedto `s`

### Why a PPX for test generations?
- because no one likes writing tests;
- because having access to the source code during test generation is good;
- because of the 0 runtime overhead, as the *real* program and the tested one can be compiled separately.

## How is it done?
Testify features an automatic derivation of QCheck’s generators for
[most](#derivation) basic types and uses those to randomly generates
inputs for each function whose return type was attached a validity property.
It then applies the function to the obtained inputs and checks the
ouput against the specified property. Note that we also provide a
```[@gen t]``` annotation that allows the programmer to explicitly
associate a generator to a type as below:

```OCaml
let[@gen p_int] spawn = QCheck.Gen.pint
```

### *Such that* annotation
For record types, we use the fact that fields are already named in the
type definition to provide the convenient writing:

```OCaml
type itv = {inf:int; sup:int} [@@s.t inf <= sup]
```
which is syntactic sugar for:

```OCaml
type itv = {inf:int; sup:int} [@@satisfying (fun {inf;sup} -> inf <= sup)]
```

### Derivation
Automatic derivation of generators is made for the following *Non-inductive* types:
- for basic types (unit, bool, char, int, float)
- for tuples
- for records
- for sum types
- for types who are attached a ```[@@satisying pred]``` annotation, we
  proceed to a rejection sampling using
  ```QCheck.find_example```. However, this can be avoided by
  specifying a generator to the given type **t** using the ```[@gen
  t]``` annotation.

When one or more generator can not be derived for a given function, no
test is generated.

### Current
Testify is still at a very (very) early stage of developpement and is
still very (very) unstable.

##### Things that are yet to be done
- handling of parametric types
- handling of module path for type annotations (e.g : `Int.t`)
- provide the user with a *standard library* of predifined types (positive integers, non-empty lists ...)
- define a way of tagging a function as partial or total
