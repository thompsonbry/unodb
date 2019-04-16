# unodb

## Introduction

Unodb is an key-value store library. The main-memory component is ART
Trie. The licence is AGPLv3.

## Dependencies
*   git
*   a C++17 compiler, currently tested with clang 7.0 and GCC 8.0
*   CMake, at least 3.12
*   Guidelines Support Library for gsl::span, imported as a git
    submodule.
*   Boost.Container library. Version 1.69 gives UBSan errors
    ([bug report 1][boostub1], [bug report 2][boostub2]). Currently it
    is being tested with 1.60.
*   clang-format, at least 8.0
*   Google Test for tests, imported as a git submodule.
*   (optional) lcov
*   (optional) clang-tidy
*   (optional) cppcheck
*   (optional) cpplint
*   (optional) include-what-you-use
*   (optional) [DeepState][deepstate] for fuzzing

## Development

Source code is formatted with [Google C++ style][gc++style]. Automatic
code formatting is configured through git clean/fuzz filters. To
enable it, do `git config --local include.path ../.gitconfig`. If for
any reason you need to disable it temporarily, do `git config --local
--unset include.path`

clang-tidy, cppcheck, and cpplint will be invoked automatically during
build if found. Currently the diagnostic level for them as well as for
compiler warnings is set very high, and can be relaxed, especially for
clang-tidy, as need arises.

To enable Address, Leak, and Undefined Behavior sanitizers, add
`-DSANITIZE=ON` CMake option.

To invoke include-what-you-use, add `-DIWYU=ON` CMake option.

To enable inconclusive cppcheck diagnostics, add
`-DCPPCHECK_AGGRESSIVE=ON` CMake option.

To generate coverage reports using lcov, add `-DCOVERAGE=ON` CMake
option.

Google Test and DeepState are used for testing. There will be no unit
tests for each private implementation class. For DeepState, both
LLVM libfuzzer and built-in fuzzer are supported.

## Literature

*ART Trie*: V. Leis, A. Kemper and T. Neumann, "The adaptive radix tree:
ARTful indexing for main-memory databases," 2013 29th IEEE
International Conference on Data Engineering (ICDE 2013)(ICDE),
Brisbane, QLD, 2013, pp. 38-49.
doi:10.1109/ICDE.2013.6544812

[boostub1]: https://gcc.gnu.org/bugzilla/show_bug.cgi?id=80963

[boostub2]: https://bugs.llvm.org/show_bug.cgi?id=39191

[gc++style]: https://google.github.io/styleguide/cppguide.html "Google C++ Style Guide"

[deepstate]: https://github.com/trailofbits/deepstate "DeepState on GitHub"
