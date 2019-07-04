

# type-driven

## some concepts

1. reference transparency :  An expression (such as a func-
tion call) in a function is referentially transparent if it can be replaced with its result
without changing the behavior of the function. If functions produce only results, with
no side effects, this property is clearly true.

2.  A total function is guaranteed to produce a
result, meaning that it will return a value in a finite time for every possible well-typed
input, and it’s guaranteed not to throw any exceptions.

3.  A partial function, on the
other hand, might not return a result for some inputs. 
