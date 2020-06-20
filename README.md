# Wideopen

[![Build Status](https://travis-ci.com/ghilesZ/ppx_wideopen.svg?branch=master)](https://travis-ci.com/ghilesZ/ppx_wideopen)

## Why?
The shadowing trick allows the users to overwrite the usual arithmetic
operators ````(+, -, ...)```` with their own by simply doing ````let
open My_module in ...````. However the litterals in the program are
still interpreted as integer or floats by OCaml's parser which forces
the programmers to write boilerplate code to handle these cases.

Wideopen is a syntax-extension that allows you to use a custom parsing
utility for OCaml's litterals using by default the `of_string`
function of the specified module.

For example, the following piece of code (which uses the Zarith
library) computes the number of solutions of a quadratic equation:

````OCaml
  let nb_solutions a b c =
    let open[@parse.int] Z in
    let delta = b * b - 4 * a * c in
    if delta > 0 then 2
    else if delta = 0 then 1
    else 0
````

Which is syntactic sugar for:

````OCaml
  let nb_solutions a b c =
    let open Z in
    let delta = (b * b) - (of_string "4") * a * c in
    if delta > (of_string "0")
    then of_string "2"
    else if delta = (of_string "0") then of_string "1" else of_string "0"
````

## How it works?
Whenever an ````[@parse.]```` annotation is met, the litterals
````l```` appearing in the sub-expression are replaced with
````(of_string l)````. Also, note that as this extension works on the
Parsetree of OCaml, we are able to handle litterals of arbitrary size
(e.g. greater than 2^64), given that the parsing function being used
accepts it.

## The different annotations:
Wideopen provides three different annotation:

- ````[@parse.int]```` which replaces only the integer litterals (the ````Pconst_integers```` constructor of OCaml's ````Parsetree````)
  
- ````[@parse.float]```` which replaces only the float litterals (the ````Pconst_float```` constructor of OCaml's ````Parsetree````)

- ````[@parse.all]```` which replaces both float and integer litterals.

Note that the latter annotation allows you in particular to manipulate
"integers" and "floats" indiferently as a "bigger type" (Zarith's
rationals using the ````Q```` module for example) without having to
care about int-float conversion and operators.

## Customizing the parsing utility:
By default, Wideopen uses the ````of_string```` of the specified
module. However, to avoid having to define such a function within our
modules, we can specify the name of the function to be used for the
parsing as in the following example:

````OCaml
let open[@parse.all using parse] Mymodule in ...
````

Which parses both integers and floats using the ````parse```` function
of the module ````Mymodule````
