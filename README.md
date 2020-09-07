# Testify
Testify is a syntactic extension that features type driven code
generation to automatically generate test for your programs. It
allows you to attach a property to a given type **t** and use the explicit
type annotations of your program to generate tests for the values whose 
return type is  **t**,  as in the following example.

```OCaml
type itv = int * int [@satisfying (fun (x,y) -> x <= y)]

let neg ((low,high):itv) : itv = -high,-low

let add ((low1,high1):itv) ((low2,high2):itv) : itv =
  (low1 + low2), (high1 + high2)
```

which is rewritten into:


```OCaml
type itv = (((int * int))[@satisfying fun (x, y) -> x <= y])

let neg ((low, high) : itv) = (((- high), (- low)) : itv)

(QCheck.Test.make ~count:1000
        ~name:"neg does not respect the prediate (fun (x, y) -> x <= y) for some input"
        (QCheck.make
           (QCheck.find_example ~f:(fun (x, y) -> x <= y)
              (QCheck.Gen.pair QCheck.Gen.int QCheck.Gen.int)))
        (fun x1 -> (fun (x, y) -> x <= y) (neg x1)))
        
let add ((low1, high1) : itv) ((low2, high2) : itv) =
  (((low1 + low2), (high1 + high2)) : itv)
  
let _ = 
    (QCheck.Test.make ~count:1000
        ~name:"add does not respect the prediate (fun (x, y) -> x <= y) for some input"
        (QCheck.make
           (QCheck.Gen.pair
              (QCheck.find_example ~f:(fun (x, y) -> x <= y)
                 (QCheck.Gen.pair QCheck.Gen.int QCheck.Gen.int))
              (QCheck.find_example ~f:(fun (x, y) -> x <= y)
                 (QCheck.Gen.pair QCheck.Gen.int QCheck.Gen.int))))
        (fun (x1, x2) -> (fun (x, y) -> x <= y) (add x1 x2)))
```

As you noticed, Testify uses the wonderful QCheck library do the
tests.

## How is it done?
Testifies features an automatic derivation of QCheck’s generators for
most basic types and uses those to randomly generates inputs for each
function whose return type was attached a generator.  It the applies
the function to the obtained inputs and checks the ouput against the
specified property.

### Generator derivation
- for basic types (unit, bool, char, int, float)
- for tuples
- for types who are attached a predicate, we proceed to a rejection
  sampling using ```QCheck.find_example```. However, this can be
  avoided by specifying a generator to the given type **t** using the
  ```[@gen t]``` annotation.
