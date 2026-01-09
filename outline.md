Advanced Functional Programming
------

0. Strongly typed programming

1. Data types and recursion schemes

2. Functors and applicatives

3. Monads and algebraic effects

4. Algebraic theories

Assignment:

Prove these two versions of gcd equivalent.

```
    public static int gcd(int n, int m) {
        while (n != m) {
            if (n > m) {
                n = n - m;
            } else {
                m = m - n;
            }
        }
        return n;
    }

    public static int gcd2(int n, int m) {
        if (n == m) {
            return n;
        } else {
            if (n > m) {
                return gcd2(n-m, m);
            } else {
                return gcd2(n, m-n);
            }
        }
    }
```

5. Case: multi-phased type checking

6. Programming and proving with dependent types

- Curry-Howard

7. Performance and engineering

- Tail recursion
- Fusion
- Meta-programming
- Functional data structures
- QuickCheck

8-9. Project: Build and Verify XX

- Banking application with a lossy network

  + Three processes: customer, banking application, banking back-end
  
  + Challenges: modeling concurrency and communication
  
  + Handling communication failure

- Chat application with database logging

  + Many users, single chat server
  
  + Chat server logs messages and retrieves n most recent ones 

- A simple build system [what effects?]

- Write a closure-conversion pass for a language, using the free monad as an IR

10. Guest lecture: IOG

11. 


Project ideas:
---

Develop a type safe DSL for code transformation

Implement a typed nanopass compiler

Prove the correctness of tail-recursion elimination for a monadic language with fixed-points and jumps

Breadth-first traversal of a data structure

Implement an automatic CPS conversion function

Implement a closure conversion pass of a compiler




# Slogan

Everything is data

data-modeling with sums and products

