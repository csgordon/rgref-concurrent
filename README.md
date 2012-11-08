Rely-Guarantee References for Program Verification
==================================================
This repository contains the source code for RGref, a shallow Coq embedding of the rely-guarantee
reference approach to program verification.  The core ideas of the approach are to associate a
rely relation and a guarantee relation with each reference.  The guarantee limits the actions
(side effects) that may be performed using that reference, and thus generalizes a family of type
systems called reference immutability, where a mutability restriction is associated with each
reference.  The rely summarizes the guarantees of all possible aliases.

These relations grant us two useful things:

1. The guarantee provides fine-grained control over what mutation a function may perform on its arguments.
2. The rely permits us to add to a reference a refinement predicate (logical
formula) that must hold of a reference's referent. If a predicate is preserved by the rely
relation (i.e. if it is true in one state, and there is another state related to the first by the
rely relation, then it is true in the second state as well), then it is safe to assume that
predicate holds in general because the actions possible through any other alias are subsumed by
the rely.

This is not the primary documentation; more information is available upon request.

Compiling
---------
Building this development requires Coq 8.4.  For the first build, run compile.sh.  Subsequent builds
should work fine just running make.  If you add a file, add it to the list of .v files in
compile.sh, and rerun that script.

It should be possible to make it work under Coq 8.3 with a small amount of effort.  The initial
development was done under 8.3, until I discovered that 8.4's typeclass resolution mechanism
automatically finds many typeclass instances I had to provide manually in 8.3.

ProofGeneral Configuration
--------------------------
Because the development is split across multiple files and uses impredicative Set, ProofGeneral
requires a bit of additional configuration.  I use the following in my .emacs in addition to loading
the ProofGeneral scripts:

    (custom-set-variables
     '(coq-prog-args (quote ("-R" "RGref" "RGref" "-impredicative-set" "-I" "/path/to/rgref/checkout")))
     '(coq-load-path (quote ("/path/to/rgref/checkout")))
     )

Unicode
-------
The source files use Unicode characters (e.g. \tau, \Gamma), so your editor must support them.  On
Windows, Emacs occasionally opens a file with the incorrect encoding, which can be fixed with

    M-x revert-buffer-with-coding-system UTF-8
