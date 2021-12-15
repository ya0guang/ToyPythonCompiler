# ToyPythonCompiler
For IU Compiler course

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

Please use `run-tests.py` to check our test cases for lambda. Note: Certain passes cannot be checked and it will show that they are not successful (starting at select instructions), but just pay attention to the overall output of the program. Also, we have toggled on detailed output. To remove this change `util.py` set tracing = False

## Final Project

For the final project we implemented Chapter 8: Lexically Scoped Functions. This means we added Uniquify, Assignment Conversion, and Closure Conversion to our compiler. 