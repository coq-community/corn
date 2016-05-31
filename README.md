# C-CoRN
> The Coq Constructive Repository at Nijmegen.

## Install with OPAM
Make sure that you added the [Coq repository](http://coq.io/opam/):

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-corn

## Install from source
### Prerequisites
This version of C-CoRN should follow Coq trunk and requires
* SCons 1.2 or make

### Git checkout and submodules
C-CoRN depends on [Math Classes](https://github.com/math-classes/math-classes), which is a library of abstract interfaces for
mathematical structures that is heavily based on Coq's new type classes.

### Building C-CoRN
C-CoRN uses [SCons](http://www.scons.org/) for its build infrastructure. SCons is a modern
Python-based Make-replacement.

To build C-CoRN with SCons say `scons` to build the whole library, or
`scons some/module.vo` to just build `some/module.vo` (and its dependencies).

In addition to common Make options like `-j N` and `-k`, SCons
supports some useful options of its own, such as `--debug=time`, which
displays the time spent executing individual build commands.

    scons -c replaces Make clean

For more information, see the [SCons documentation](http://www.scons.org/). Make is still supported.

### Building documentation
To build CoqDoc documentation, say `scons coqdoc`.
