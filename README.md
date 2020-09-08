# Testify
Testify is a syntactic extension that features type driven code
generation to automatically generate test for your programs. It allows
you to attach a property to a given type, as in the following example:

```OCaml
type p_int = int [@satisfying (fun x -> x > 0)]
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
integers. As you also noticed, Testify uses the wonderful QCheck
library do the tests. Other examples are available in the examples
directory.

### Why a PPX for test generations?
- because no one likes writting tests.
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

### derivation
Automatic derivation of generators is made for the following types:
- for basic types (unit, bool, char, int, float)
- for tuples
- for types who are attached a ```[@satisying pred]``` annotation, we
  proceed to a rejection sampling using
  ```QCheck.find_example```. However, this can be avoided by
  specifying a generator to the given type **t** using the ```[@gen
  t]``` annotation.

### Current
Testify is still at a very (very) early stage of developpement and is
still very (very) unstable.

##### Things that are yet to be done
- replace the current (generator + printer) implementation with QCheck's arbitrary
- handling of parametric types
- provide the user with a *standard library* of predifined types (positive integers, non-empty lists ...)
