# ToyPythonCompiler
For IU Compiler course

Maintained by: Hongbo Chen, Sandy Wheeler, Louis Labuzienski

## Resources

The framework of this repo is from [IUCompilerCourse/python-student-support-code](https://github.com/IUCompilerCourse/python-student-support-code).

- [Course website](https://iucompilercourse.github.io/IU-Fall-2021/)
- [Racket Version Book](https://www.dropbox.com/s/ktdw8j0adcc44r0/book.pdf?dl=1)
- [Python Version Book](https://www.dropbox.com/s/mfxtojk4yif3toj/python-book.pdf?dl=1)
- [Python `ast` doc](https://docs.python.org/3.10/library/ast.html#ast.parse)

## Environment

I use `pyenv` to manage Python environment. Since `match` clause is just introduced in Python 3.10, which is still an `rc` version and not stable yet, it can be installed using `pyenv` and related packages can also be managed in a clean fashion.

## python-student-support-code

Support code for students (Python version).

The runtime.c file needs to be compiled by doing the following

```sh
   gcc -c -g -std=c99 runtime.c
```
This will produce a file named runtime.o. The -g flag is to tell the compiler to produce debug information that you may need to use the gdb (or lldb) debugger.

## Test

Please use `run-tests.py` to check our test cases for lambda.
use `python run-tests.py <chapter>`
Where chapter is one of the chapters we've covered in the course:
var, conditional, loop, tuple, function, lambda, bug

Use keyword all to run them all except for bug

To test our lambda functionality run `python run-tests.py lambda`
To test all functionality run `python run-testes.py all`

To compile and run all tests at the same time `gcc -c -g -std=c99 runtime.c & python run-tests.py all`


Note: Certain passes cannot be checked (select instructions and onward), but just pay attention to the overall output of the program. Also, a detailed output (tracing) can be toggled on or off by commenting line enable_tracing(). 

Note2: There are two test cases in the tests/bug directory that fail during run-tests.py. We are not certain as to why this is, but when we compile these test cases outside of run-tests.py there is no issue. 

## Final Project

For the final project we implemented Chapter 8: Lexically Scoped Functions. This means we added Uniquify, Assignment Conversion, and Closure Conversion to our compiler. 