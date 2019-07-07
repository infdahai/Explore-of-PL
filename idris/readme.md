

# type-driven

## comment

I use the binary file to execute idris program in windows 10 pro.
 
## some concepts

1. reference transparency :  An expression (such as a func-
tion call) in a function is referentially transparent if it can be replaced with its result
without changing the behavior of the function.   If functions produce only results, with
no side effects, this property is clearly true.

2.  A total function is guaranteed to produce a
result, meaning that it will return a value in a finite time for every possible well-typed
input, and it’s guaranteed not to throw any exceptions.

3.  A partial function, on the
other hand, might not return a result for some inputs. 

4.  Idris provides several basic numeric types, including the following:

     Int —A fixed-width signed integer type. It’s guaranteed to be at least 31 bits wide,
    but the exact width is system dependent.

     Integer —An unbounded signed integer type. Unlike Int , there’s no limit to the
    size of the numbers that can be represented, other than your machine’s mem-
    ory, but this type is more expensive in terms of performance and memory
    usage.

     Nat —An unbounded unsigned integer type. This is very often used for sizes and
    indexing of data structures, because they can never be negative. You’ll see
    much more of Nat later.
    
     Double —A double-precision floating-point type.
  
  
5.  partial application : 
    When a function has more than one argument, you can create a specialized version of
the function by omitting the later arguments. 

```idris
add : Int -> Int -> Int
add x y = x + y

:let addTwo = add 2
```

6.  type constraints : Constraints on generic types can be user-defined using
interface
    two other constraints provided by
    Idris:
    
     Eq states that the type must support the equality and inequality operators, ==
    and /= .
    
     Ord states that the type must support the comparison operators < , <= , > , and >= 
    
     example
    
    ```idris
        test: Num a => a -> a
        test x = double (double x)
    ```
